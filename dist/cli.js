"use strict";
// src/cli.ts — FuturLang command-line interface
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const readline = __importStar(require("readline"));
const child_process_1 = require("child_process");
const formal_1 = require("./parser/formal");
const lexer_1 = require("./parser/lexer");
const parser_1 = require("./parser/parser");
const checker_1 = require("./checker/checker");
const transpiler_1 = require("./react/transpiler");
const rust_1 = require("./codegen/rust");
const lsp_server_1 = require("./lsp-server");
const rawArgs = process.argv.slice(2);
const strict = rawArgs.includes('--strict');
const noLaunch = rawArgs.includes('--no-launch');
const args = rawArgs.filter(arg => arg !== '--strict' && arg !== '--no-launch');
async function main() {
    if (args.length === 0) {
        printUsage();
        return;
    }
    const command = args[0];
    if (command === 'check') {
        const file = args[1];
        if (!file) {
            console.error('Usage: fl check <file.fl>');
            process.exit(1);
        }
        runCheck(file);
        return;
    }
    if (command === 'derive') {
        const file = args[1];
        if (!file) {
            console.error('Usage: fl derive <file.fl>');
            process.exit(1);
        }
        runDerive(file);
        return;
    }
    if (command === 'web') {
        const file = args[1];
        const outDir = args[2] ?? 'generated/futurlang-webapp';
        if (!file) {
            console.error('Usage: fl web <file.fl> [out-dir]');
            process.exit(1);
        }
        runWeb(file, outDir);
        return;
    }
    if (command === 'create-app') {
        const name = args[1];
        if (!name) {
            console.error('Usage: fl create-app <name>');
            process.exit(1);
        }
        runCreateApp(name);
        return;
    }
    if (command === 'install') {
        await runInstall();
        return;
    }
    if (command === 'start') {
        // Project-mode: fl start (no args, reads fl.json)
        if (!args[1] || args[1].endsWith('.fl') === false) {
            await runProjectStart();
            return;
        }
        // Legacy: fl start <file.fl> [out-dir]
        const file = args[1];
        const outDir = args[2] ?? 'generated/futurlang-webapp';
        runStart(file, outDir);
        return;
    }
    if (command === 'server') {
        const file = args[1];
        if (!file) {
            console.error('Usage: fl server <file.fl>');
            process.exit(1);
        }
        runServer(file);
        return;
    }
    if (command === 'build') {
        const file = args[1];
        if (!file) {
            console.error('Usage: fl build <file.fl> [-o output]');
            process.exit(1);
        }
        const outFlag = args.indexOf('-o');
        const outName = outFlag >= 0 ? args[outFlag + 1] : null;
        await runBuild(file, outName);
        return;
    }
    if (command === 'rust') {
        const file = args[1];
        if (!file) {
            console.error('Usage: fl rust <file.fl> [out.rs]');
            process.exit(1);
        }
        const outFile = args[2] ?? null;
        runRust(file, outFile);
        return;
    }
    if (command === 'repl') {
        runRepl(rawArgs.includes('--json'));
        return;
    }
    if (command === 'lsp-server') {
        const portArg = args.indexOf('--port');
        const port = portArg >= 0 ? parseInt(args[portArg + 1], 10) : 3001;
        await (0, lsp_server_1.startLspServer)(port);
        // Keep alive — never resolves so the process stays up
        await new Promise(() => { });
        return;
    }
    // Default: evaluate
    const file = command;
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    runEval(file);
}
function runEval(file) {
    const source = (0, formal_1.expandFLFile)(file);
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: false });
    if (isProofStyleProgram(ast)) {
        console.log(`\n${path.basename(file)}: proof + runtime mode\n`);
        const proofAst = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: true });
        const report = (0, checker_1.checkFile)(proofAst, { strict });
        printCheckReport(file, report, false);
        if (report.state !== 'PROVED') {
            process.exitCode = 1;
        }
        console.log(`\nExecuting ${path.basename(file)}\n`);
    }
    const js = (0, formal_1.parseFLFile)(file);
    try {
        eval(js);
    }
    catch (e) {
        console.error(e.message);
        process.exit(1);
    }
}
function runServer(file) {
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    const js = (0, formal_1.parseFLFile)(file);
    try {
        eval(js);
    }
    catch (e) {
        console.error(e.message);
        process.exit(1);
    }
}
function runStart(file, outDir) {
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
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
async function runBuild(file, outName) {
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    const source = (0, formal_1.expandFLFile)(file);
    const nodes = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: false });
    const rustSrc = (0, rust_1.generateRustFromAST)(nodes, path.basename(file));
    const isAnchor = nodes.some(n => n.type === 'Program');
    const programName = outName ?? path.basename(file, '.fl');
    const cargoToml = (0, rust_1.generateCargoToml)(programName, isAnchor);
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
    await new Promise((resolve, reject) => {
        const child = (0, child_process_1.spawn)(cmd, buildArgs, {
            cwd: tmpDir,
            stdio: ['ignore', 'pipe', 'pipe'],
            shell: process.platform === 'win32',
        });
        let stderr = '';
        child.stderr?.on('data', (d) => { stderr += d.toString(); });
        child.on('exit', (code) => {
            if (code === 0)
                resolve();
            else
                reject(new Error(`Build failed:\n${stderr}`));
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
        }
        else {
            console.log(`\n✓ Build succeeded (artifact in ${outDir})`);
        }
    }).catch((e) => {
        console.error(e.message);
        process.exitCode = 1;
    }).finally(() => {
        // Always remove temp dir — Rust source stays hidden
        fs.rmSync(tmpDir, { recursive: true, force: true });
    });
}
function runRust(file, outFile) {
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    const source = (0, formal_1.expandFLFile)(file);
    const nodes = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: false });
    const rust = (0, rust_1.generateRustFromAST)(nodes, path.basename(file));
    if (outFile) {
        fs.writeFileSync(outFile, rust, 'utf8');
        console.log(`Rust source written to ${outFile}`);
    }
    else {
        process.stdout.write(rust);
    }
}
function runCheck(file) {
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    const source = (0, formal_1.expandFLFile)(file);
    const report = (0, checker_1.checkFile)((0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: true }), { strict });
    printCheckReport(file, report);
}
function runDerive(file) {
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    const source = (0, formal_1.expandFLFile)(file);
    const nodes = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: true });
    console.log(`\nForward-chaining derivation: ${path.basename(file)}\n`);
    // Run checkFile to get premises in string form (already resolved by the kernel)
    const report = (0, checker_1.checkFile)(nodes, { strict });
    let anyPrinted = false;
    for (const r of report.reports) {
        if (r.premises.length === 0)
            continue;
        anyPrinted = true;
        console.log(`  ${r.name}:`);
        console.log(`    premises: ${r.premises.join(' ; ')}`);
        const ctx = (0, checker_1.createMutableContext)(r.premises, null);
        const t0 = Date.now();
        const conclusions = (0, checker_1.deriveConclusions)(ctx);
        const elapsed = Date.now() - t0;
        if (conclusions.length === 0) {
            console.log(`    → no new conclusions reachable`);
        }
        else {
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
function runRepl(jsonMode) {
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
    let ctx = (0, checker_1.createMutableContext)([], null);
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
            if (!jsonMode)
                rl.prompt();
            return;
        }
        try {
            const astNodes = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(line), { desugarFns: true });
            if (astNodes.length === 0) {
                if (!jsonMode)
                    rl.prompt();
                return;
            }
            for (const node of astNodes) {
                const result = (0, checker_1.evaluateIncrementalStep)(ctx, node);
                if (jsonMode) {
                    console.log(JSON.stringify({ status: 'ok', trace: result }));
                }
                else {
                    if (result) {
                        const icon = result.state === 'PROVED' ? '✓' : result.state === 'PENDING' ? '~' : result.state === 'UNVERIFIED' ? '?' : '✗';
                        console.log(` ${icon} ${result.rule} => ${result.state}`);
                        if (result.message)
                            console.log(`    ${result.message}`);
                        if (result.causalError)
                            console.dir(result.causalError, { depth: null, colors: true });
                    }
                }
            }
        }
        catch (e) {
            if (jsonMode) {
                console.log(JSON.stringify({ status: 'error', error: e.message }));
            }
            else {
                console.error(` ✗ Parser/eval error: ${e.message}`);
            }
        }
        if (!jsonMode)
            rl.prompt();
    }).on('close', () => {
        process.exit(0);
    });
}
function printCheckReport(file, report, exitOnFailure = true) {
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
                if (d.hint)
                    console.log(`        hint: ${d.hint}`);
            }
            else if (d.severity === 'warning') {
                console.log(`      ⚠ ${d.message}`);
            }
            else if (d.severity === 'info' && d.rule) {
                console.log(`      ℹ ${d.message}`);
            }
        }
    }
    for (const d of report.diagnostics) {
        if (declarationOnly && d.message.includes('have no proof'))
            continue;
        console.log(`  ${d.severity === 'error' ? '✗' : 'ℹ'} ${d.message}`);
    }
    if (declarationOnly) {
        console.log(`\n  Declaration-only proof program`);
        console.log(`  Theorems: ${report.theoremCount}`);
        console.log(report.state === 'FAILED' ? '\n✗ Structural errors found' : '\n~ Declarations parsed without paired derivations');
    }
    else {
        console.log(`\n  Theorems: ${report.theoremCount}  Paired: ${report.pairedCount}  Result: ${report.state}`);
        if (report.state === 'PROVED') {
            console.log('\n✓ All proofs reduced to classical morphism paths');
        }
        else if (report.state === 'PENDING') {
            console.log('\n~ At least one derivation is structurally valid but still blocked behind ω and Ra');
        }
        else if (report.state === 'UNVERIFIED') {
            console.log('\n? At least one derivation was accepted only as structurally unverified');
        }
        else {
            console.log('\n✗ Structural errors found');
        }
    }
    if (exitOnFailure && report.state !== 'PROVED')
        process.exit(1);
}
function isProofStyleProgram(ast) {
    return ast.some(node => node.type === 'Theorem' ||
        node.type === 'Proof' ||
        node.type === 'Lemma');
}
function runWeb(file, outDir) {
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    const source = fs.readFileSync(file, 'utf8');
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: false });
    (0, transpiler_1.createReactApp)(ast, outDir);
    console.log(`Generated React app in ${outDir}`);
}
function launchFrontend(outDir) {
    if (!fs.existsSync(path.join(outDir, 'package.json'))) {
        console.error(`Frontend app is missing package.json in ${outDir}`);
        process.exit(1);
    }
    if (!fs.existsSync(path.join(outDir, 'node_modules'))) {
        console.error(`Frontend dependencies are missing in ${outDir}. Run npm install there or use the default generated app directory.`);
        process.exit(1);
    }
    console.log(`Starting React dev server in ${outDir}`);
    const child = (0, child_process_1.spawn)('npm', ['run', 'dev', '--', '--host', '127.0.0.1', '--port', '5173'], {
        cwd: outDir,
        stdio: 'inherit',
        shell: process.platform === 'win32',
    });
    child.on('exit', (code) => {
        process.exit(code ?? 0);
    });
}
function isServerProgram(source) {
    return /\bserve\s*\(/.test(source);
}
function readManifest() {
    const manifestPath = path.join(process.cwd(), 'fl.json');
    if (!fs.existsSync(manifestPath)) {
        console.error('No fl.json found. Run fl create-app <name> to scaffold a new app, or run fl start <file.fl> to use a specific file.');
        process.exit(1);
    }
    return JSON.parse(fs.readFileSync(manifestPath, 'utf8'));
}
function runCreateApp(name) {
    const appDir = path.resolve(name);
    if (fs.existsSync(appDir)) {
        console.error(`Directory already exists: ${appDir}`);
        process.exit(1);
    }
    const backendDir = path.join(appDir, '_react');
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
    const manifest = { name, main: mainFile, backend: '_react' };
    fs.mkdirSync(appDir, { recursive: true });
    fs.writeFileSync(path.join(appDir, mainFile), starterFl, 'utf8');
    fs.writeFileSync(path.join(appDir, 'fl.json'), JSON.stringify(manifest, null, 2) + '\n', 'utf8');
    fs.writeFileSync(path.join(appDir, '.gitignore'), '_react/node_modules\n', 'utf8');
    const source = fs.readFileSync(path.join(appDir, mainFile), 'utf8');
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: false });
    (0, transpiler_1.createReactApp)(ast, backendDir);
    console.log(`Created app: ${name}/`);
    console.log(`  ${name}/${mainFile}   ← your FL source`);
    console.log(`  ${name}/fl.json       ← project manifest`);
    console.log(`  ${name}/_react/       ← generated React backend`);
    console.log(`\nNext steps:`);
    console.log(`  cd ${name}`);
    console.log(`  fl install`);
    console.log(`  fl start`);
}
async function runInstall() {
    const manifest = readManifest();
    const backendDir = path.resolve(manifest.backend);
    if (!fs.existsSync(backendDir)) {
        console.error(`Backend directory not found: ${backendDir}. Re-run fl create-app or fl start to regenerate it.`);
        process.exit(1);
    }
    console.log(`Installing dependencies in ${manifest.backend}/...`);
    await new Promise((resolve, reject) => {
        const child = (0, child_process_1.spawn)('npm', ['install'], {
            cwd: backendDir,
            stdio: 'inherit',
            shell: process.platform === 'win32',
        });
        child.on('exit', (code) => {
            if (code === 0)
                resolve();
            else
                reject(new Error(`npm install exited with code ${code}`));
        });
    });
    console.log('\nDone. Run fl start to launch your app.');
}
async function runProjectStart() {
    const manifest = readManifest();
    const mainFile = path.resolve(manifest.main);
    const backendDir = path.resolve(manifest.backend);
    if (!fs.existsSync(mainFile)) {
        console.error(`Main file not found: ${manifest.main}`);
        process.exit(1);
    }
    // Regenerate React app from current FL source
    const source = fs.readFileSync(mainFile, 'utf8');
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: false });
    (0, transpiler_1.createReactApp)(ast, backendDir);
    console.log(`Generated React app from ${manifest.main}`);
    // Auto-install if node_modules is missing
    if (!fs.existsSync(path.join(backendDir, 'node_modules'))) {
        console.log('node_modules not found — running npm install...');
        await new Promise((resolve, reject) => {
            const child = (0, child_process_1.spawn)('npm', ['install'], {
                cwd: backendDir,
                stdio: 'inherit',
                shell: process.platform === 'win32',
            });
            child.on('exit', (code) => {
                if (code === 0)
                    resolve();
                else
                    reject(new Error(`npm install exited with code ${code}`));
            });
        });
    }
    launchFrontend(backendDir);
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

App workflow (recommended):
  fl create-app <name>              Scaffold a new FL app with a React backend
  fl install                        Install React backend dependencies (run inside app dir)
  fl start                          Regenerate React app and launch dev server (run inside app dir)

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
