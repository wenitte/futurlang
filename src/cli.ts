// src/cli.ts — FuturLang command-line interface

import * as fs from 'fs';
import * as path from 'path';
import { parseFL } from './parser/formal';
import { lexFL } from './parser/lexer';
import { parseLinesToAST } from './parser/parser';
import { checkFile } from './checker/checker';
import { setup, isSetupComplete } from './lean/setup';
import { verify } from './lean/verifier';
import { createReactApp } from './react/transpiler';

const args = process.argv.slice(2);

async function main() {
  if (args.length === 0) { printUsage(); return; }

  const command = args[0];

  if (command === 'setup') {
    try { await setup(msg => console.log(msg)); }
    catch (e: any) { console.error('Setup failed:', e.message); process.exit(1); }
    return;
  }

  if (command === 'check') {
    const file = args[1];
    if (!file) { console.error('Usage: fl check <file.fl>'); process.exit(1); }
    runCheck(file); return;
  }

  if (command === 'verify') {
    const file = args[1];
    if (!file) { console.error('Usage: fl verify <file.fl>'); process.exit(1); }
    runVerify(file); return;
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
  const js = parseFL(source);
  try { eval(js); }
  catch (e: any) { console.error(e.message); process.exit(1); }
}

function runCheck(file: string) {
  if (!fs.existsSync(file)) { console.error(`File not found: ${file}`); process.exit(1); }

  const source = fs.readFileSync(file, 'utf8');
  const report = checkFile(parseLinesToAST(lexFL(source)));

  console.log(`\nChecking ${path.basename(file)}\n`);

  for (const r of report.reports) {
    const icon   = r.valid ? '✓' : '✗';
    const method = r.method !== 'unknown' ? ` [${r.method}]` : '';
    console.log(`  ${icon} ${r.name}${method}  (${r.stepCount} steps, depth ${r.metrics.dependencyDepth})`);
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
      const stepIcon = step.valid ? '✓' : '✗';
      console.log(`      ${stepIcon} step ${step.step} [${step.rule}] ${step.kind} ${step.claim}`);
      if (step.uses && step.uses.length > 0) {
        console.log(`        uses: ${step.uses.join(' ; ')}`);
      }
      if (step.imports && step.imports.length > 0) {
        console.log(`        imports: ${step.imports.join(' ; ')}`);
      }
      if (step.establishesAs) {
        console.log(`        establishes-as: ${step.establishesAs}`);
      }
    }
    for (const d of r.diagnostics) {
      if (d.severity === 'error') {
        console.log(`      ✗ ${d.message}`);
        if (d.hint) console.log(`        hint: ${d.hint}`);
      } else if (d.severity === 'warning') {
        console.log(`      ⚠ ${d.message}`);
      } else if (d.severity === 'info' && d.rule && d.rule !== 'THEOREM_PROOF') {
        console.log(`      ℹ ${d.message}`);
      }
    }
  }

  for (const d of report.diagnostics) {
    console.log(`  ${d.severity === 'error' ? '✗' : 'ℹ'} ${d.message}`);
  }

  console.log(`\n  Theorems: ${report.theoremCount}  Paired: ${report.pairedCount}  Score: ${report.score}/100`);
  console.log(report.valid ? '\n✓ All proofs structurally valid' : '\n✗ Structural errors found');
  if (!report.valid) process.exit(1);
}

function runVerify(file: string) {
  if (!isSetupComplete()) {
    console.error('Lean backend not installed. Run: fl setup'); process.exit(1);
  }
  const source      = fs.readFileSync(file, 'utf8');
  const sourceLines = source.split('\n');
  const ast         = parseLinesToAST(lexFL(source));

  console.log(`Verifying ${path.basename(file)}...`);
  const result = verify(ast, sourceLines);

  for (const thm of result.theorems) {
    console.log(`  ${thm.verified ? '✓' : '✗'} ${thm.name}`);
  }
  if (result.errors.length > 0) {
    console.log('');
    for (const err of result.errors) {
      if (!err.message.toLowerCase().includes('sorry')) {
        const loc = err.flLine ? ` (line ${err.flLine})` : '';
        console.error(`  ✗${loc} ${err.message}`);
      }
    }
  }
  const realErrors = result.errors.filter(e => !e.message.toLowerCase().includes('sorry'));
  if (realErrors.length > 0) {
    console.log('\n✗ Verification failed'); process.exit(1);
  } else if (!result.success) {
    console.log('\n~ Proof structure verified (some steps use sorry placeholders)');
  } else {
    console.log('\n✓ Proof verified');
  }
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
  fl <file.fl>           Evaluate a proof program
  fl check <file.fl>     Check proof structure (natural deduction)
  fl verify <file.fl>    Verify proof against Lean 4 / Mathlib
  fl web <file.fl>       Generate a React app from the program truth chain
  fl setup               Install verification backend (one-time, ~4GB)
`);
}

main().catch(e => { console.error(e.message); process.exit(1); });
