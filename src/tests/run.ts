import { strict as assert } from 'assert';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { lexFL } from '../parser/lexer';
import { parseExpr } from '../parser/expr';
import { parseLinesToAST } from '../parser/parser';
import { checkFile } from '../checker/checker';
import { parseFL } from '../parser/formal';
import { transpileToLean } from '../lean/transpiler';
import { createReactApp } from '../react/transpiler';

function runTest(name: string, fn: () => void) {
  try {
    fn();
    console.log(`✓ ${name}`);
  } catch (error) {
    console.error(`✗ ${name}`);
    throw error;
  }
}

runTest('parseExpr marks quoted claims as string atoms', () => {
  const expr = parseExpr('"hello world"');
  assert.equal(expr.type, 'Atom');
  assert.equal(expr.atomKind, 'string');
});

runTest('parseExpr builds logical AST for supported expressions', () => {
  const expr = parseExpr('(p && q) -> r');
  assert.equal(expr.type, 'Implies');
});

runTest('parser preserves malformed expressions as opaque atoms', () => {
  const ast = parseLinesToAST(lexFL(`
theorem Broken() {
  assert(p && && q);
}
`));
  const theorem = ast[0];
  assert.equal(theorem.type, 'Theorem');
  const claim = theorem.body[0];
  assert.equal(claim.type, 'Assert');
  assert.equal(claim.expr.type, 'Atom');
  assert.equal(claim.expr.atomKind, 'opaque');
});

runTest('checker validates a paired theorem and proof', () => {
  const ast = parseLinesToAST(lexFL(`
theorem Identity() {
  assert(p -> p)
} ↔

proof Identity() {
  assume(p) →
  conclude(p)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.pairedCount, 1);
  assert.equal(report.reports[0].goal, 'p → p');
  assert.equal(report.reports[0].derivedConclusion, 'p');
});

runTest('checker rejects proofs that do not establish theorem goal', () => {
  const ast = parseLinesToAST(lexFL(`
theorem Identity() {
  assert(p -> p)
} ↔

proof Identity() {
  assume(p) →
  conclude(q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  assert.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal/);
});

runTest('checker accepts conjunction goals when both parts are established', () => {
  const ast = parseLinesToAST(lexFL(`
theorem Pair() {
  assert(p && q)
} ↔

proof Pair() {
  assume(p) →
  assert(q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
});

runTest('eval backend rejects unsupported mathematical notation', () => {
  assert.throws(
    () => {
      const js = parseFL(`
theorem AdvancedMath() {
  assert(∀(n: ℕ) ⇒ n = n)
}
`);
      eval(js);
    },
    /Use 'fl verify'/,
  );
});

runTest('Lean transpiler retains advanced mathematical claims', () => {
  const ast = parseLinesToAST(lexFL(`
theorem AdvancedMath() {
  assert(∀(n: ℕ) ⇒ n = n)
}
`));
  const output = transpileToLean(ast);
  assert.match(output.source, /theorem AdvancedMath/);
  assert.match(output.source, /∀ n : ℕ,/);
  assert.match(output.source, /n = n/);
});

runTest('React backend generates a webapp scaffold', () => {
  const ast = parseLinesToAST(lexFL(`
theorem Hello() {
  assert(true)
}
`));
  const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'futurlang-web-'));
  createReactApp(ast, outDir);
  assert.equal(fs.existsSync(path.join(outDir, 'package.json')), true);
  assert.equal(fs.existsSync(path.join(outDir, 'src', 'App.tsx')), true);
  assert.equal(fs.existsSync(path.join(outDir, 'src', 'styles.css')), true);
});

console.log('All unit tests passed.');
