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
  assert.equal(report.reports[0].proofSteps[0].rule, 'ASSUMPTION');
  assert.equal(report.reports[0].proofSteps[1].rule, 'IMPLIES_INTRO');
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
  assert(q) →
  conclude(p && q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.reports[0].proofSteps[2].rule, 'AND_INTRO');
});

runTest('checker accepts modus ponens style derivations', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ModusPonens() {
  given(p -> q)
  assert(q)
} ↔

proof ModusPonens() {
  assume(p) →
  conclude(q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.reports[0].premises[0], 'p → q');
  assert.equal(report.reports[0].proofSteps[1].rule, 'IMPLIES_ELIM');
});

runTest('checker accepts conjunction elimination derivations', () => {
  const ast = parseLinesToAST(lexFL(`
theorem LeftProjection() {
  assert((p && q) -> p)
} ↔

proof LeftProjection() {
  assume(p && q) →
  conclude(p)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.reports[0].proofSteps[1].rule, 'AND_ELIM');
});

runTest('checker enforces lemma hypotheses before apply', () => {
  const ast = parseLinesToAST(lexFL(`
lemma NeedsP() {
  given(p)
  assert(q)
} ↔

proof NeedsP() {
  conclude(q)
} →

theorem UsesLemma() {
  assert(q)
} ↔

proof UsesLemma() {
  apply(NeedsP)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  assert.match(report.reports.map(r => r.diagnostics.map(d => d.message).join('\n')).join('\n'), /missing hypotheses p/);
});

runTest('checker accepts chained lemma application with satisfied hypotheses', () => {
  const ast = parseLinesToAST(lexFL(`
lemma ForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof ForwardStep() {
  assume(p) →
  conclude(q)
} →

theorem UsesForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof UsesForwardStep() {
  assume(p) →
  apply(ForwardStep)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports.find(r => r.name === 'UsesForwardStep');
  assert.ok(theoremReport);
  assert.equal(theoremReport!.proofSteps[1].rule, 'BY_LEMMA');
  assert.equal(theoremReport!.proofSteps[1].uses?.[0], 'p → q');
  assert.equal(theoremReport!.proofSteps[1].imports?.[0], 'q');
  const importedFact = theoremReport!.proofObjects.find(object => object.source === 'lemma_application' && object.claim === 'q');
  assert.ok(importedFact);
  assert.equal(importedFact!.dependsOn[0], 'p → q');
  assert.equal(importedFact!.imports?.[0], 'q');
});

runTest('checker accepts chained multi-premise implication demo', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ChainImplication() {
  given(p -> q) →
  given(q -> r) →
  assert(r)
} ↔

proof ChainImplication() {
  assume(p) →
  assert(q) →
  conclude(r)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
});

runTest('checker accepts chained conjunction premise demo', () => {
  const ast = parseLinesToAST(lexFL(`
theorem RightProjection() {
  given(p && q) →
  assert(q)
} ↔

proof RightProjection() {
  conclude(q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
});

runTest('checker accepts contradiction discharge in the current demo subset', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExplosionDemo() {
  given(p) →
  given(¬p) →
  assert(q)
} ↔

proof ExplosionDemo() {
  assume(¬q) →
  contradiction() →
  conclude(q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.method, 'contradiction');
  assert.equal(theoremReport.proofSteps[1].rule, 'CONTRADICTION');
  assert.equal(theoremReport.proofSteps[2].rule, 'CONTRADICTION');
  const contradictionFact = theoremReport.proofObjects.find(object => object.claim === 'contradiction');
  assert.ok(contradictionFact);
  assert.match(contradictionFact!.dependsOn.join(' '), /p/);
  assert.match(contradictionFact!.dependsOn.join(' '), /¬p/);
});

runTest('checker records implication proof objects for derived facts', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ModusPonens() {
  given(p -> q) →
  assert(q)
} ↔

proof ModusPonens() {
  assume(p) →
  conclude(q)
}
`));
  const report = checkFile(ast);
  const theoremReport = report.reports[0];
  const conclusionObject = theoremReport.proofObjects.find(object => object.source === 'conclusion' && object.claim === 'q');
  assert.ok(conclusionObject);
  assert.equal(conclusionObject!.rule, 'IMPLIES_ELIM');
  assert.equal(conclusionObject!.dependsOn.length, 2);
  assert.match(conclusionObject!.dependsOn.join(' '), /p/);
  assert.match(conclusionObject!.dependsOn.join(' '), /q/);
});

runTest('parser rejects missing connective between top-level blocks', () => {
  assert.throws(
    () => parseLinesToAST(lexFL(`
lemma ForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof ForwardStep() {
  assume(p) →
  conclude(q)
}

theorem UsesForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof UsesForwardStep() {
  assume(p) →
  apply(ForwardStep)
}
`)),
    /Missing connective between top-level blocks/,
  );
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
