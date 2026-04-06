import { strict as assert } from 'assert';
import { execFileSync } from 'child_process';
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

runTest('parseExpr accepts MI-style implication and biconditional symbols', () => {
  const impliesExpr = parseExpr('(x ∈ A) ⇒ (x ∈ A)');
  assert.equal(impliesExpr.type, 'Implies');
  const iffExpr = parseExpr('(x ≤ y) ⇔ (x ≤ y)');
  assert.equal(iffExpr.type, 'Iff');
  const subsetExpr = parseExpr('(x ∈ A) ⇒ (A ⊆ B)');
  assert.equal(subsetExpr.type, 'Implies');
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
  assert.match(claim.expr.parseError ?? '', /Unexpected token|Unexpected token after expression|Expected/);
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
  assert.equal(report.reports[0].derivedConclusion, 'p → p');
  assert.equal(report.reports[0].proofSteps[0].rule, 'ASSUMPTION');
  assert.equal(report.reports[0].proofSteps[1].rule, 'IMPLIES_INTRO');
  assert.equal(report.reports[0].proofObjects[0].rule, 'ASSUMPTION');
  assert.equal(report.reports[0].proofObjects[0].dependsOnIds.length, 0);
  assert.equal(report.reports[0].derivations.length, 1);
  assert.equal(report.reports[0].derivations[0].rule, 'IMPLIES_INTRO');
  const implicationObject = report.reports[0].proofObjects.find(object => object.rule === 'IMPLIES_INTRO');
  assert.ok(implicationObject);
  assert.equal(implicationObject!.claim, 'p → p');
  assert.equal(report.reports[0].baseFactIds.length, 1);
  assert.equal(report.reports[0].derivedFactIds.length, 1);
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

runTest('checker surfaces parser fallback diagnostics for malformed rich mathematical notation', () => {
  const ast = parseLinesToAST(lexFL(`
theorem QuantifiedIdentity() {
  assert(∀(n: ℕ) ⇒)
} ↔

proof QuantifiedIdentity() {
  assert(∀(n: ℕ) ⇒)
}
`));
  const report = checkFile(ast);
  const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
  assert.match(messages, /outside the current parser\/checker subset/i);
  assert.match(messages, /opaque symbolic claim/i);
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
  const conjunctionObject = report.reports[0].proofObjects.find(object => object.claim === 'p ∧ q');
  assert.ok(conjunctionObject);
  assert.equal(conjunctionObject!.rule, 'AND_INTRO');
  assert.equal(conjunctionObject!.dependsOn.length, 2);
  assert.equal(conjunctionObject!.dependsOnIds.length, 2);
  const conjunctionDerivation = report.reports[0].derivations.find(node => node.rule === 'AND_INTRO');
  assert.ok(conjunctionDerivation);
  assert.equal(conjunctionDerivation!.inputIds.length, 2);
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
  assert.equal(report.reports[0].proofObjects[0].rule, 'PREMISE');
  assert.equal(report.reports[0].proofObjects[0].dependsOnIds.length, 0);
  const modusPonensDerivation = report.reports[0].derivations.find(node => node.rule === 'IMPLIES_ELIM');
  assert.ok(modusPonensDerivation);
  assert.equal(modusPonensDerivation!.inputIds.length, 2);
  assert.equal(report.reports[0].baseFactIds.length, 2);
  assert.equal(report.reports[0].derivedFactIds.length, 1);
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

runTest('checker accepts MI-style symbolic identity demos', () => {
  const ast = parseLinesToAST(lexFL(`
theorem MembershipIdentity() {
  assert((x ∈ A) ⇒ (x ∈ A))
} ↔

proof MembershipIdentity() {
  assume(x ∈ A) →
  conclude(x ∈ A)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.reports[0].derivedConclusion, 'x ∈ A → x ∈ A');
});

runTest('checker validates set-theoretic subset transport', () => {
  const ast = parseLinesToAST(lexFL(`
theorem SubsetTransport() {
  given(x ∈ A) →
  given(A ⊆ B) →
  assert(x ∈ B)
} ↔

proof SubsetTransport() {
  conclude(x ∈ B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'SUBSET_ELIM');
  assert.equal(theoremReport.derivedConclusion, 'x ∈ B');
  const subsetDerivation = theoremReport.derivations.find(node => node.rule === 'SUBSET_ELIM');
  assert.ok(subsetDerivation);
  assert.equal(subsetDerivation!.inputIds.length, 2);
});

runTest('checker validates chained set-theoretic subset transport', () => {
  const ast = parseLinesToAST(lexFL(`
theorem SubsetChain() {
  given(x ∈ A) →
  given(A ⊆ B) →
  given(B ⊆ C) →
  assert(x ∈ C)
} ↔

proof SubsetChain() {
  assert(x ∈ B) →
  conclude(x ∈ C)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'SUBSET_ELIM');
  assert.equal(theoremReport.proofSteps[1].rule, 'SUBSET_ELIM');
  assert.equal(theoremReport.derivedConclusion, 'x ∈ C');
  assert.equal(theoremReport.derivations.filter(node => node.rule === 'SUBSET_ELIM').length, 2);
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
  assert.equal(importedFact!.dependsOnIds.length, 1);
  const lemmaDerivation = theoremReport!.derivations.find(node => node.rule === 'BY_LEMMA');
  assert.ok(lemmaDerivation);
  assert.equal(lemmaDerivation!.inputIds.length, 1);
  assert.equal(theoremReport!.derivedFactIds.length, 1);
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
  assert.equal(contradictionFact!.dependsOnIds.length, 2);
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
  assert.equal(conclusionObject!.dependsOnIds.length, 2);
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

runTest('default fl command auto-runs checker for proof-shaped files', () => {
  const output = execFileSync('node', ['fl.js', 'examples/demo/identity.fl'], {
    cwd: process.cwd(),
    encoding: 'utf8',
  });
  assert.match(output, /theorem-prover mode/i);
  assert.match(output, /Checking identity\.fl/);
  assert.match(output, /final: p → p/);
});

runTest('default fl command presents standalone theorem files as declarations', () => {
  const output = execFileSync('node', ['fl.js', 'test/connectives.fl'], {
    cwd: process.cwd(),
    encoding: 'utf8',
  });
  assert.match(output, /Declaration-only proof program/);
  assert.match(output, /Theorems: 9/);
  assert.doesNotMatch(output, /Score: 0\/100/);
  assert.doesNotMatch(output, /have no proof/);
});

console.log('All unit tests passed.');
