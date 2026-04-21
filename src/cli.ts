// src/cli.ts — FuturLang command-line interface

import * as fs from 'fs';
import * as path from 'path';
import * as readline from 'readline';
import { spawn } from 'child_process';
import { parseFL, parseFLFile, expandFLFile } from './parser/formal';
import { lexFL } from './parser/lexer';
import { parseLinesToAST } from './parser/parser';
import { generateJSFromAST } from './codegen';
import { runtimePreamble } from './codegen/runtime';
import { checkFile, createMutableContext, evaluateIncrementalStep, deriveConclusions } from './checker/checker';
import { createReactApp } from './react/transpiler';
import { generateRustFromAST, generateCargoToml } from './codegen/rust';
import { startLspServer } from './lsp-server';
import { CHAIN_CARGO_TOML, CHAIN_SRC, CHAIN_SOURCE_HASH } from './codegen/chain-runtime';
import { buildFirebaseServerRuntime } from './codegen/firebase-server-runtime';

const rawArgs = process.argv.slice(2);
const strict = rawArgs.includes('--strict');
const noLaunch = rawArgs.includes('--no-launch');
const args = rawArgs.filter(arg => arg !== '--strict' && arg !== '--no-launch');

async function main() {
  if (args.length === 0) { printUsage(); return; }

  const command = args[0];

  if (command === 'check') {
    const file = args[1];
    if (!file) { console.error('Usage: fl check <file.fl>'); process.exit(1); }
    runCheck(file); return;
  }

  if (command === 'derive') {
    const file = args[1];
    if (!file) { console.error('Usage: fl derive <file.fl>'); process.exit(1); }
    runDerive(file); return;
  }

  if (command === 'web') {
    const file = args[1];
    const outDir = args[2] ?? 'generated/futurlang-webapp';
    if (!file) { console.error('Usage: fl web <file.fl> [out-dir]'); process.exit(1); }
    runWeb(file, outDir); return;
  }

  if (command === 'create-app') {
    const name = args[1];
    if (!name) { console.error('Usage: fl create-app <name>'); process.exit(1); }
    runCreateApp(name); return;
  }

  if (command === 'create-server') {
    const name = args[1];
    if (!name) { console.error('Usage: fl create-server <name>'); process.exit(1); }
    runCreateServer(name); return;
  }

  if (command === 'install') {
    await runInstall(); return;
  }

  if (command === 'start') {
    // Project-mode: fl start (no args, reads fl.json)
    if (!args[1] || args[1].endsWith('.fl') === false) {
      await runProjectStart(); return;
    }
    // Legacy: fl start <file.fl> [out-dir]
    const file = args[1];
    const outDir = args[2] ?? 'generated/futurlang-webapp';
    runStart(file, outDir); return;
  }

  if (command === 'server') {
    const file = args[1];
    if (!file) { console.error('Usage: fl server <file.fl>'); process.exit(1); }
    runServer(file); return;
  }

  if (command === 'build') {
    const file = args[1];
    if (!file) { console.error('Usage: fl build <file.fl> [-o output]'); process.exit(1); }
    const outFlag = args.indexOf('-o');
    const outName = outFlag >= 0 ? args[outFlag + 1] : null;
    await runBuild(file, outName); return;
  }

  if (command === 'rust') {
    const file = args[1];
    if (!file) { console.error('Usage: fl rust <file.fl> [out.rs]'); process.exit(1); }
    const outFile = args[2] ?? null;
    runRust(file, outFile); return;
  }

  if (command === 'repl') {
    runRepl(rawArgs.includes('--json')); return;
  }

  if (command === 'lsp-server') {
    const portArg = args.indexOf('--port');
    const port = portArg >= 0 ? parseInt(args[portArg + 1], 10) : 3001;
    await startLspServer(port);
    // Keep alive — never resolves so the process stays up
    await new Promise(() => {});
    return;
  }

  if (command === 'chain') {
    await runChain(args.slice(1)); return;
  }

  // Default: evaluate FL via TypeScript runtime
  const file = command;
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }
  runEval(file);
}

async function runExecute(file: string) {
  const source = expandFLFile(file);
  const nodes = parseLinesToAST(lexFL(source), { desugarFns: true });

  // Always show proof check output first
  if (isProofStyleProgram(nodes)) {
    const report = checkFile(nodes, { strict });
    printCheckReport(file, report, false);
    if (report.state !== 'PROVED') { process.exitCode = 1; return; }
  }

  // Compile to Rust in a hidden temp dir, run the binary, then clean up
  const rustNodes = parseLinesToAST(lexFL(source), { desugarFns: false });
  const rustSrc = generateRustFromAST(rustNodes, path.basename(file));
  const programName = path.basename(file, '.fl');
  const isAnchor = rustNodes.some(n => n.type === 'Program');

  if (isAnchor) {
    // On-chain programs can't be run directly — just check and report
    console.log(`\n${programName}: on-chain program (use fl build to compile for deployment)`);
    return;
  }

  const cargoToml = generateCargoToml(programName, false);
  const tmpDir = path.join(require('os').tmpdir(), `fl-run-${Date.now()}`);
  const srcDir = path.join(tmpDir, 'src');
  fs.mkdirSync(srcDir, { recursive: true });
  fs.writeFileSync(path.join(tmpDir, 'Cargo.toml'), cargoToml, 'utf8');
  fs.writeFileSync(path.join(srcDir, 'main.rs'), rustSrc, 'utf8');

  try {
    // Build silently
    await new Promise<void>((resolve, reject) => {
      const child = spawn('cargo', ['build', '--release', '--quiet'], {
        cwd: tmpDir, stdio: ['ignore', 'ignore', 'pipe'],
        shell: process.platform === 'win32',
      });
      let stderr = '';
      child.stderr?.on('data', (d: Buffer) => { stderr += d.toString(); });
      child.on('exit', code => code === 0 ? resolve() : reject(new Error(stderr)));
    });

    // Run the binary — stdio inherits so the program talks directly to the terminal
    const binary = path.join(tmpDir, 'target', 'release', programName);
    await new Promise<void>((resolve) => {
      const child = spawn(binary, [], { stdio: 'inherit' });
      child.on('exit', code => { process.exitCode = code ?? 0; resolve(); });
    });
  } catch (e: any) {
    console.error(`Compile error:\n${e.message}`);
    process.exitCode = 1;
  } finally {
    fs.rmSync(tmpDir, { recursive: true, force: true });
  }
}

function runEval(file: string) {
  const source = expandFLFile(file);
  const ast = parseLinesToAST(lexFL(source), { desugarFns: false });
  if (isProofStyleProgram(ast)) {
    console.log(`\n${path.basename(file)}: proof + runtime mode\n`);
    const proofAst = parseLinesToAST(lexFL(source), { desugarFns: true });
    const report = checkFile(proofAst, { strict });
    printCheckReport(file, report, false);
    if (report.state !== 'PROVED') {
      process.exitCode = 1;
    }
    console.log(`\nExecuting ${path.basename(file)}\n`);
  }
  const js = parseFLFile(file);
  try { eval(js); }
  catch (e: any) { console.error(e.message); process.exit(1); }
}

function runServer(file: string, extraRuntime = '') {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }
  // Compile FL to JS in-memory — no file ever written to disk (same as fl <file.fl>)
  const source = expandFLFile(file);
  const ast = parseLinesToAST(lexFL(source), { desugarFns: false });
  const js = generateJSFromAST(ast, runtimePreamble + (extraRuntime ? '\n' + extraRuntime : ''));
  try { eval(js); }
  catch (e: any) { console.error(e.message); process.exit(1); }
}

function runStart(file: string, outDir: string) {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }
  const source = fs.readFileSync(file, 'utf8');
  if (isServerProgram(source)) {
    runServer(file);
    return;
  }
  runWeb(file, outDir);
  if (noLaunch) {
    console.log('Skipping frontend launch because --no-launch was provided');
    return;
  }
  launchFrontend(outDir);
}

async function runBuild(file: string, outName: string | null) {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }

  const source = expandFLFile(file);
  const nodes = parseLinesToAST(lexFL(source), { desugarFns: false });
  const rustSrc = generateRustFromAST(nodes, path.basename(file));

  const isAnchor = nodes.some(n => n.type === 'Program');
  const programName = outName ?? path.basename(file, '.fl');
  const cargoToml = generateCargoToml(programName, isAnchor);

  // Write to a hidden temp directory — Rust source is never exposed to the user
  const tmpDir = path.join(require('os').tmpdir(), `fl-build-${Date.now()}`);
  const srcDir = path.join(tmpDir, 'src');
  fs.mkdirSync(srcDir, { recursive: true });
  fs.writeFileSync(path.join(tmpDir, 'Cargo.toml'), cargoToml, 'utf8');

  const entryFile = isAnchor ? 'lib.rs' : 'main.rs';
  fs.writeFileSync(path.join(srcDir, entryFile), rustSrc, 'utf8');

  console.log(`Building ${path.basename(file)}...`);

  const buildCmd = isAnchor ? 'cargo build-sbf' : 'cargo build --release';
  const [cmd, ...buildArgs] = buildCmd.split(' ');

  await new Promise<void>((resolve, reject) => {
    const child = spawn(cmd, buildArgs, {
      cwd: tmpDir,
      stdio: ['ignore', 'pipe', 'pipe'],
      shell: process.platform === 'win32',
    });
    let stderr = '';
    child.stderr?.on('data', (d: Buffer) => { stderr += d.toString(); });
    child.on('exit', (code) => {
      if (code === 0) resolve();
      else reject(new Error(`Build failed:\n${stderr}`));
    });
  }).then(() => {
    // Copy output artifact to cwd, then clean up temp dir
    const outDir = isAnchor
      ? path.join(tmpDir, 'target', 'deploy')
      : path.join(tmpDir, 'target', 'release');
    const artifactName = isAnchor ? `${programName.replace(/-/g, '_')}.so` : programName;
    const artifactSrc = path.join(outDir, artifactName);
    const artifactDst = path.join(process.cwd(), artifactName);
    if (fs.existsSync(artifactSrc)) {
      fs.copyFileSync(artifactSrc, artifactDst);
      console.log(`\n✓ Built: ${artifactName}`);
    } else {
      console.log(`\n✓ Build succeeded (artifact in ${outDir})`);
    }
  }).catch((e: Error) => {
    console.error(e.message);
    process.exitCode = 1;
  }).finally(() => {
    // Always remove temp dir — Rust source stays hidden
    fs.rmSync(tmpDir, { recursive: true, force: true });
  });
}

function runRust(file: string, outFile: string | null) {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }
  const source = expandFLFile(file);
  const nodes = parseLinesToAST(lexFL(source), { desugarFns: false });
  const rust = generateRustFromAST(nodes, path.basename(file));
  if (outFile) {
    fs.writeFileSync(outFile, rust, 'utf8');
    console.log(`Rust source written to ${outFile}`);
  } else {
    process.stdout.write(rust);
  }
}

function runCheck(file: string) {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }

  const source = expandFLFile(file);
  const report = checkFile(parseLinesToAST(lexFL(source), { desugarFns: true }), { strict });
  printCheckReport(file, report);
}

function runDerive(file: string) {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }

  const source = expandFLFile(file);
  const nodes = parseLinesToAST(lexFL(source), { desugarFns: true });

  console.log(`\nForward-chaining derivation: ${path.basename(file)}\n`);

  // Run checkFile to get premises in string form (already resolved by the kernel)
  const report = checkFile(nodes, { strict });

  let anyPrinted = false;
  for (const r of report.reports) {
    if (r.premises.length === 0) continue;
    anyPrinted = true;
    console.log(`  ${r.name}:`);
    console.log(`    premises: ${r.premises.join(' ; ')}`);

    const ctx = createMutableContext(r.premises, null);
    const t0 = Date.now();
    const conclusions = deriveConclusions(ctx);
    const elapsed = Date.now() - t0;

    if (conclusions.length === 0) {
      console.log(`    → no new conclusions reachable`);
    } else {
      console.log(`    → ${conclusions.length} conclusion(s) in ${elapsed}ms:`);
      for (const c of conclusions) {
        console.log(`       ${c}`);
      }
    }
    console.log('');
  }

  if (!anyPrinted) {
    console.log('  No theorem/lemma premises found in this file.');
  }
}

function runRepl(jsonMode: boolean) {
  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    terminal: !jsonMode,
  });

  if (!jsonMode) {
    console.log('FuturLang Interactive Agent REPL');
    console.log('Type a valid proof step (e.g. "assert(A ⊆ B)") or "exit".\\n');
  }

  // Interactive session without initial premises
  let ctx = createMutableContext([], null);

  if (!jsonMode) {
    rl.setPrompt('fl> ');
    rl.prompt();
  }

  rl.on('line', (line) => {
    line = line.trim();
    if (line === 'exit' || line === 'quit') {
      process.exit(0);
    }
    if (!line) {
      if (!jsonMode) rl.prompt();
      return;
    }

    try {
      const astNodes = parseLinesToAST(lexFL(line), { desugarFns: true });
      if (astNodes.length === 0) {
        if (!jsonMode) rl.prompt();
        return;
      }
      for (const node of astNodes) {
        const result = evaluateIncrementalStep(ctx, node);
        if (jsonMode) {
          console.log(JSON.stringify({ status: 'ok', trace: result }));
        } else {
          if (result) {
            const icon = result.state === 'PROVED' ? '✓' : result.state === 'PENDING' ? '~' : result.state === 'UNVERIFIED' ? '?' : '✗';
            console.log(` ${icon} ${result.rule} => ${result.state}`);
            if (result.message) console.log(`    ${result.message}`);
            if (result.causalError) console.dir(result.causalError, { depth: null, colors: true });
          }
        }
      }
    } catch (e: any) {
      if (jsonMode) {
        console.log(JSON.stringify({ status: 'error', error: e.message }));
      } else {
        console.error(` ✗ Parser/eval error: ${e.message}`);
      }
    }

    if (!jsonMode) rl.prompt();
  }).on('close', () => {
    process.exit(0);
  });
}

function printCheckReport(file: string, report: ReturnType<typeof checkFile>, exitOnFailure = true) {
  console.log(`\nChecking ${path.basename(file)}\n`);
  const declarationOnly = report.theoremCount > 0 && report.pairedCount === 0;

  for (const r of report.reports) {
    const status = r.state === 'PROVED' ? '✓' : r.state === 'PENDING' ? '~' : r.state === 'UNVERIFIED' ? '?' : '✗';
    const statusSuffix = r.pendingCount > 0
      ? ` (${r.provedCount} classical, ${r.pendingCount} pending)`
      : r.provedCount > 0 ? ` (${r.provedCount} classical)` : '';
    console.log(`  ${status} ${r.name}  ${r.state}${statusSuffix}`);
    if (r.premises.length > 0) {
      console.log(`      premises: ${r.premises.join(' ; ')}`);
    }
    if (r.goal) {
      console.log(`      goal: ${r.goal}`);
    }
    if (r.derivedConclusion) {
      console.log(`      final: ${r.derivedConclusion}`);
    }
    for (const step of r.proofSteps) {
      const stepIcon = step.state === 'PROVED' ? '✓' : step.state === 'PENDING' ? '~' : step.state === 'UNVERIFIED' ? '?' : '✗';
      console.log(`      ${stepIcon} step ${step.step} [${step.rule}] ${step.kind} ${step.claim}`);
      if (step.uses && step.uses.length > 0) {
        console.log(`        uses: ${step.uses.join(' ; ')}`);
      }
      if (step.imports && step.imports.length > 0) {
        console.log(`        imports: ${step.imports.join(' ; ')}`);
      }
    }
    for (const d of r.diagnostics) {
      if (d.severity === 'error') {
        console.log(`      ✗ ${d.message}`);
        if (d.hint) console.log(`        hint: ${d.hint}`);
      } else if (d.severity === 'warning') {
        console.log(`      ⚠ ${d.message}`);
      } else if (d.severity === 'info' && d.rule) {
        console.log(`      ℹ ${d.message}`);
      }
    }
  }

  for (const d of report.diagnostics) {
    if (declarationOnly && d.message.includes('have no proof')) continue;
    console.log(`  ${d.severity === 'error' ? '✗' : 'ℹ'} ${d.message}`);
  }

  if (declarationOnly) {
    console.log(`\n  Declaration-only proof program`);
    console.log(`  Theorems: ${report.theoremCount}`);
    console.log(report.state === 'FAILED' ? '\n✗ Structural errors found' : '\n~ Declarations parsed without paired derivations');
  } else {
    console.log(`\n  Theorems: ${report.theoremCount}  Paired: ${report.pairedCount}  Result: ${report.state}`);
    if (report.state === 'PROVED') {
      console.log('\n✓ All proofs reduced to classical morphism paths');
    } else if (report.state === 'PENDING') {
      console.log('\n~ At least one derivation is structurally valid but still blocked behind ω and Ra');
    } else if (report.state === 'UNVERIFIED') {
      console.log('\n? At least one derivation was accepted only as structurally unverified');
    } else {
      console.log('\n✗ Structural errors found');
    }
  }
  if (exitOnFailure && report.state !== 'PROVED') process.exit(1);
}

function isProofStyleProgram(ast: ReturnType<typeof parseLinesToAST>): boolean {
  return ast.some(node =>
    node.type === 'Theorem' ||
    node.type === 'Proof' ||
    node.type === 'Lemma'
  );
}

function runWeb(file: string, outDir: string) {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }
  const source = fs.readFileSync(file, 'utf8');
  const ast = parseLinesToAST(lexFL(source), { desugarFns: false });
  createReactApp(ast, outDir);
  console.log(`Generated React app in ${outDir}`);
}

function launchFrontend(outDir: string) {
  if (!fs.existsSync(path.join(outDir, 'package.json'))) {
    console.error(`Frontend app is missing package.json in ${outDir}`);
    process.exit(1);
  }
  if (!fs.existsSync(path.join(outDir, 'node_modules'))) {
    console.error(`Frontend dependencies are missing in ${outDir}. Run npm install there or use the default generated app directory.`);
    process.exit(1);
  }
  console.log(`Starting React dev server in ${outDir}`);
  const child = spawn('npm', ['run', 'dev', '--', '--host', '127.0.0.1', '--port', '5173'], {
    cwd: outDir,
    stdio: 'inherit',
    shell: process.platform === 'win32',
  });
  child.on('exit', (code) => {
    process.exit(code ?? 0);
  });
}

function isServerProgram(source: string): boolean {
  return /\bserve\s*\(/.test(source);
}

interface FlManifest {
  name: string;
  type: 'web' | 'server';
  main: string;
  /** Web: path to generated React output (default: generated/frontend) */
  generated?: string;
  /** Server: optional Firebase config for injecting Firestore helpers */
  firebase?: { projectId: string };
}

function readManifest(): FlManifest {
  // Support both package.flson (preferred) and fl.json (legacy)
  const candidates = ['package.flson', 'fl.json'];
  for (const name of candidates) {
    const p = path.join(process.cwd(), name);
    if (fs.existsSync(p)) return JSON.parse(fs.readFileSync(p, 'utf8')) as FlManifest;
  }
  console.error('No package.flson found. Run fl create-app <name> or fl create-server <name> to scaffold a project.');
  process.exit(1);
}

function runCreateApp(name: string) {
  const appDir = path.resolve(name);
  if (fs.existsSync(appDir)) { console.error(`Directory already exists: ${appDir}`); process.exit(1); }

  const generatedDir = 'generated/frontend';
  const mainFile = 'app.fl';

  const starterFl = `fn double(n ∈ Nat) -> Nat {
  conclude(n + n)
} →

fn clamp(x ∈ Real, lo ∈ Real, hi ∈ Real) -> Real {
  assume(lo <= hi) →
  conclude(max(lo, min(x, hi)))
} →

theorem DoubleIsPositive() {
  let n = 4 →
  let result = double(n) →
  assert(result > 0)
} →

proof DoubleIsPositive() {
  let n = 4 →
  let result = double(n) →
  conclude(result > 0)
}
`;

  const manifest: FlManifest = { name, type: 'web', main: mainFile, generated: generatedDir };

  fs.mkdirSync(appDir, { recursive: true });
  fs.writeFileSync(path.join(appDir, mainFile), starterFl, 'utf8');
  fs.writeFileSync(path.join(appDir, 'package.flson'), JSON.stringify(manifest, null, 2) + '\n', 'utf8');
  fs.writeFileSync(path.join(appDir, '.gitignore'), 'generated/\n', 'utf8');

  const outDir = path.join(appDir, generatedDir);
  const ast = parseLinesToAST(lexFL(starterFl), { desugarFns: false });
  createReactApp(ast, outDir);

  console.log(`\nCreated FL web app: ${name}/`);
  console.log(`  ${name}/${mainFile}            ← your FL source (edit this)`);
  console.log(`  ${name}/package.flson          ← project manifest`);
  console.log(`  ${name}/generated/frontend/    ← generated React (hidden, gitignored)`);
  console.log(`\nNext steps:`);
  console.log(`  cd ${name} && fl install && fl start`);
}

function runCreateServer(name: string) {
  const serverDir = path.resolve(name);
  if (fs.existsSync(serverDir)) { console.error(`Directory already exists: ${serverDir}`); process.exit(1); }

  const mainFile = 'server.fl';

  const starterFl = `// ${name} — FL server
// fl start  ←  compiles and runs in memory (no generated files)

fn cors(req ∈ Request) -> Response {
  conclude(json({ ok: true }, 200, {
    "Access-Control-Allow-Origin": "*",
    "Access-Control-Allow-Headers": "Content-Type, Authorization",
    "Access-Control-Allow-Methods": "GET, POST, PUT, DELETE, OPTIONS"
  }))
} →

fn health(req ∈ Request) -> Response {
  conclude(json({ status: "ok", service: "${name}", version: "1.0.0" }, 200, {
    "Access-Control-Allow-Origin": "*"
  }))
} →

fn notFound(req ∈ Request) -> Response {
  conclude(json({ error: "not found" }, 404, {
    "Access-Control-Allow-Origin": "*"
  }))
} →

let app = router([
  route("OPTIONS", "*", cors),
  route("GET", "/api/health", health)
], notFound) →

let server = serve(3001, app)
`;

  const manifest: FlManifest = { name, type: 'server', main: mainFile };

  fs.mkdirSync(serverDir, { recursive: true });
  fs.writeFileSync(path.join(serverDir, mainFile), starterFl, 'utf8');
  fs.writeFileSync(path.join(serverDir, 'package.flson'), JSON.stringify(manifest, null, 2) + '\n', 'utf8');
  fs.writeFileSync(path.join(serverDir, '.gitignore'), '.env\n', 'utf8');

  console.log(`\nCreated FL server: ${name}/`);
  console.log(`  ${name}/${mainFile}     ← your FL source (edit this)`);
  console.log(`  ${name}/package.flson  ← project manifest`);
  console.log(`\nNext steps:`);
  console.log(`  cd ${name} && fl start`);
}

async function runInstall() {
  const manifest = readManifest();
  if (manifest.type === 'server') {
    console.log('Server projects have no npm dependencies to install (runs in-memory).');
    return;
  }
  const generatedDir = path.resolve(manifest.generated ?? 'generated/frontend');
  if (!fs.existsSync(generatedDir)) {
    console.error(`Generated directory not found: ${generatedDir}. Run fl start to generate it first.`);
    process.exit(1);
  }
  console.log(`Installing dependencies in ${path.relative(process.cwd(), generatedDir)}/...`);
  await npmInstall(generatedDir);
  console.log('\nDone. Run fl start to launch your app.');
}

async function npmInstall(dir: string) {
  return new Promise<void>((resolve, reject) => {
    const child = spawn('npm', ['install'], {
      cwd: dir, stdio: 'inherit', shell: process.platform === 'win32',
    });
    child.on('exit', code => code === 0 ? resolve() : reject(new Error(`npm install exited with code ${code}`)));
  });
}

async function runProjectStart() {
  const manifest = readManifest();
  const mainFile = path.resolve(manifest.main);

  if (!fs.existsSync(mainFile)) {
    console.error(`Main file not found: ${manifest.main}`);
    process.exit(1);
  }

  if (manifest.type === 'server') {
    // ── Server: compile FL and eval in-memory — no files written ──────────────
    console.log(`Starting FL server from ${manifest.main}...`);
    let extraRuntime = '';
    if (manifest.firebase?.projectId) {
      extraRuntime = buildFirebaseServerRuntime(manifest.firebase.projectId);
    }
    runServer(mainFile, extraRuntime);
    return;
  }

  // ── Web: generate React into generated/frontend/, install if needed, launch ──
  const generatedDir = path.resolve(manifest.generated ?? 'generated/frontend');
  const source = fs.readFileSync(mainFile, 'utf8');
  const ast = parseLinesToAST(lexFL(source), { desugarFns: false });
  createReactApp(ast, generatedDir);
  console.log(`Generated React app from ${manifest.main}`);

  if (!fs.existsSync(path.join(generatedDir, 'node_modules'))) {
    console.log('node_modules not found — running npm install...');
    await npmInstall(generatedDir);
  }

  if (noLaunch) {
    console.log('Skipping frontend launch (--no-launch)');
    return;
  }
  launchFrontend(generatedDir);
}

async function runChain(extraArgs: string[]) {
  const os = require('os') as typeof import('os');
  const cacheDir = path.join(os.homedir(), '.futurlang', 'chain');
  const srcDir   = path.join(cacheDir, 'src');
  const binary   = path.join(cacheDir, 'target', 'release', 'futurchain');
  const hashFile = path.join(cacheDir, '.source-hash');

  // Check if a rebuild is needed
  const needsBuild = (() => {
    if (!fs.existsSync(binary)) return true;
    try { return fs.readFileSync(hashFile, 'utf8').trim() !== CHAIN_SOURCE_HASH; }
    catch { return true; }
  })();

  if (needsBuild) {
    console.log('Building FuturChain from FL source...');
    fs.mkdirSync(srcDir, { recursive: true });
    fs.writeFileSync(path.join(cacheDir, 'Cargo.toml'), CHAIN_CARGO_TOML, 'utf8');
    for (const [name, content] of Object.entries(CHAIN_SRC)) {
      fs.writeFileSync(path.join(srcDir, name), content, 'utf8');
    }

    await new Promise<void>((resolve, reject) => {
      const child = spawn('cargo', ['build', '--release'], {
        cwd: cacheDir,
        stdio: ['ignore', 'inherit', 'inherit'],
        shell: process.platform === 'win32',
      });
      child.on('exit', code => code === 0 ? resolve() : reject(new Error(`Build failed (exit ${code})`)));
    });

    fs.writeFileSync(hashFile, CHAIN_SOURCE_HASH, 'utf8');
    console.log('Build complete.\n');
  }

  const child = spawn(binary, extraArgs, { stdio: 'inherit' });
  child.on('exit', (code: number | null) => process.exit(code ?? 0));
  for (const sig of ['SIGINT', 'SIGTERM'] as const) {
    process.on(sig, () => child.kill(sig));
  }
}

function printUsage() {
  console.log(`
FuturLang — formal proof language

Usage:
  fl [--strict] <file.fl>           Execute a file; proof-shaped files also show checker output
  fl check [--strict] <file.fl>     Check proof structure with the categorical kernel
  fl derive <file.fl>               Forward-chain all derivable conclusions from premises
  fl build <file.fl> [-o name]      Compile to binary via Rust (source stays hidden)
  fl server <file.fl>               Run a server-style FL file

FuturChain:
  fl chain                          Start a FuturChain node (RPC on :8899, 400ms slots)
  fl chain --port 9000              Custom RPC port
  fl chain --slot-ms 1000           Custom slot duration (ms)
  fl chain --genesis-supply 1000    Custom genesis token supply

App workflow (recommended):
  fl create-app <name>              Scaffold a new FL web app (React generated into generated/frontend/)
  fl create-server <name>           Scaffold a new FL server (runs in-memory, no generated files)
  fl install                        Install frontend dependencies (web apps only; run inside app dir)
  fl start                          Start the project: web apps launch Vite, servers run in-memory

Legacy / single-file:
  fl start <file.fl> [out-dir]      Generate and launch a React app from a single FL file
  fl web <file.fl> [out-dir]        Generate a React app without launching it
  fl lsp-server [--port 3001]       Start the Language API Server (parse/check/hover/rust endpoints)
  fl repl [--json]                  Run the interactive agent REPL (for programmatic IO)

Notes:
  --strict                          Reserved for future kernel tightening
  --no-launch                       Generate frontend output without starting Vite

VS Code Extension (syntax highlighting, hover docs, completions):
  https://marketplace.visualstudio.com/items?itemName=WenitteApiou.futurlang
`);
}

main().catch(e => { console.error(e.message); process.exit(1); });
