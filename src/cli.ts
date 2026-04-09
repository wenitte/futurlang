// src/cli.ts — FuturLang command-line interface

import * as fs from 'fs';
import * as path from 'path';
import { parseFL } from './parser/formal';
import { lexFL } from './parser/lexer';
import { parseLinesToAST } from './parser/parser';
import { checkFile } from './checker/checker';
import { createReactApp } from './react/transpiler';

const rawArgs = process.argv.slice(2);
const strict = rawArgs.includes('--strict');
const args = rawArgs.filter(arg => arg !== '--strict');

async function main() {
  if (args.length === 0) { printUsage(); return; }

  const command = args[0];

  if (command === 'check') {
    const file = args[1];
    if (!file) { console.error('Usage: fl check <file.fl>'); process.exit(1); }
    runCheck(file); return;
  }

  if (command === 'web') {
    const file = args[1];
    const outDir = args[2] ?? 'generated/futurlang-webapp';
    if (!file) { console.error('Usage: fl web <file.fl> [out-dir]'); process.exit(1); }
    runWeb(file, outDir); return;
  }

  // Default: evaluate
  const file = command;
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }
  runEval(file);
}

function runEval(file: string) {
  const source = fs.readFileSync(file, 'utf8');
  const ast = parseLinesToAST(lexFL(source));
  if (isProofStyleProgram(ast)) {
    console.log(`\n${path.basename(file)}: theorem-prover mode\n`);
    printCheckReport(file, checkFile(ast, { strict }));
    return;
  }
  const js = parseFL(source);
  try { eval(js); }
  catch (e: any) { console.error(e.message); process.exit(1); }
}

function runCheck(file: string) {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }

  const source = fs.readFileSync(file, 'utf8');
  const report = checkFile(parseLinesToAST(lexFL(source)), { strict });
  printCheckReport(file, report);
}

function printCheckReport(file: string, report: ReturnType<typeof checkFile>) {
  console.log(`\nChecking ${path.basename(file)}\n`);
  const declarationOnly = report.theoremCount > 0 && report.pairedCount === 0;

  for (const r of report.reports) {
    const status = r.state === 'PROVED' ? '✓' : r.state === 'PENDING' ? '~' : '✗';
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
      const stepIcon = step.state === 'PROVED' ? '✓' : step.state === 'PENDING' ? '~' : '✗';
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
    } else {
      console.log('\n✗ Structural errors found');
    }
  }
  if (report.state !== 'PROVED') process.exit(1);
}

function isProofStyleProgram(ast: ReturnType<typeof parseLinesToAST>): boolean {
  return ast.some(node =>
    node.type === 'Theorem' ||
    node.type === 'Proof' ||
    node.type === 'Lemma' ||
    node.type === 'Given' ||
    node.type === 'Assume' ||
    node.type === 'Conclude' ||
    node.type === 'Apply'
  );
}

function runWeb(file: string, outDir: string) {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }
  const source = fs.readFileSync(file, 'utf8');
  const ast = parseLinesToAST(lexFL(source));
  createReactApp(ast, outDir);
  console.log(`Generated React app in ${outDir}`);
}

function printUsage() {
  console.log(`
FuturLang — formal proof language

Usage:
  fl [--strict] <file.fl>           Auto-runs check mode for proof-shaped files, otherwise evaluates
  fl check [--strict] <file.fl>     Check proof structure with the categorical kernel
  fl web <file.fl>                  Generate a React app from the program truth chain

Notes:
  --strict                          Reserved for future kernel tightening
`);
}

main().catch(e => { console.error(e.message); process.exit(1); });
