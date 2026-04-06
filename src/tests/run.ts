import { strict as assert } from 'assert';
import { execFileSync } from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { lexFL } from '../parser/lexer';
import { parseExpr } from '../parser/expr';
import { parseLinesToAST } from '../parser/parser';
import { checkFile } from '../checker/checker';
import { exprToProp } from '../checker/propositions';
import { parseFL } from '../parser/formal';
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

runTest('parseExpr normalizes word equivalents for set notation and bounded quantifiers', () => {
  const unionExpr = parseExpr('(x in A) implies (x in A union B)');
  assert.equal(exprToProp(unionExpr), 'x ∈ A → x ∈ A ∪ B');

  const quantified = parseExpr('forall x in A, exists y in B');
  assert.equal(quantified.type, 'Atom');
  assert.equal(quantified.atomKind, 'expression');
  assert.equal(quantified.condition, '∀ x ∈ A, ∃ y ∈ B');
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

runTest('checker diagnoses unsupported quantified binder forms with a specific missing-rule hint', () => {
  const ast = parseLinesToAST(lexFL(`
theorem BoundedQuantifierDemo() {
  assert(forall x, x in A)
} ↔

proof BoundedQuantifierDemo() {
  assert(forall x, x in A)
}
`));
  const report = checkFile(ast);
  const messages = report.reports.flatMap(r => r.diagnostics.map(d => `${d.message}\n${d.hint ?? ''}`)).join('\n');
  assert.match(messages, /FORALL_BINDER/);
  assert.match(messages, /kernel/i);
});

runTest('checker accepts conjunction goals when both parts are established', () => {
  const ast = parseLinesToAST(lexFL(`
theorem Pair() {
  assert(p && q)
} ↔

proof Pair() {
  assume(p) →
  assume(q) →
  conclude(p && q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.reports[0].proofSteps[2].rule, 'AND_INTRO');
  const conjunctionObject = report.reports[0].proofObjects.find(object => object.claim === 'p ∧ q');
  assert.ok(conjunctionObject);
  assert.equal(conjunctionObject!.rule, 'AND_INTRO');
  assert.equal(conjunctionObject!.status, 'PROVED');
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

runTest('checker validates subset transitivity', () => {
  const ast = parseLinesToAST(lexFL(`
theorem SubsetTransitivity() {
  given(A subset B) →
  given(B subset C) →
  assert(A subset C)
} ↔

proof SubsetTransitivity() {
  conclude(A subset C)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'SUBSET_TRANS');
  assert.equal(theoremReport.derivedConclusion, 'A ⊆ C');
});

runTest('checker validates equality substitution on membership claims', () => {
  const ast = parseLinesToAST(lexFL(`
theorem EqualitySubstitution() {
  given(x = y) →
  given(x in A) →
  assert(y in A)
} ↔

proof EqualitySubstitution() {
  conclude(y in A)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'EQUALITY_SUBST');
  assert.equal(theoremReport.derivedConclusion, 'y ∈ A');
});

runTest('checker validates union introduction from word-form notation', () => {
  const ast = parseLinesToAST(lexFL(`
theorem UnionIntro() {
  given(x in A) →
  assert(x in A union B)
} ↔

proof UnionIntro() {
  conclude(x in A union B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.reports[0].proofSteps[0].rule, 'UNION_INTRO');
  assert.equal(report.reports[0].derivedConclusion, 'x ∈ A ∪ B');
});

runTest('checker validates intersection introduction and elimination', () => {
  const introAst = parseLinesToAST(lexFL(`
theorem IntersectionIntro() {
  given(x in A) →
  given(x in B) →
  assert(x in A intersection B)
} ↔

proof IntersectionIntro() {
  conclude(x in A intersection B)
}
`));
  const introReport = checkFile(introAst);
  assert.equal(introReport.valid, true);
  assert.equal(introReport.reports[0].proofSteps[0].rule, 'INTERSECTION_INTRO');
  assert.equal(introReport.reports[0].derivedConclusion, 'x ∈ A ∩ B');

  const elimAst = parseLinesToAST(lexFL(`
theorem IntersectionRight() {
  given(x in A intersection B) →
  assert(x in B)
} ↔

proof IntersectionRight() {
  conclude(x in B)
}
`));
  const elimReport = checkFile(elimAst);
  assert.equal(elimReport.valid, true);
  assert.equal(elimReport.reports[0].proofSteps[0].rule, 'INTERSECTION_ELIM');
  assert.equal(elimReport.reports[0].derivedConclusion, 'x ∈ B');
});

runTest('checker validates bounded universal elimination', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ForallInElim() {
  given(forall x in A, x in B) →
  given(a in A) →
  assert(a in B)
} ↔

proof ForallInElim() {
  conclude(a in B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'FORALL_IN_ELIM');
  assert.equal(theoremReport.derivedConclusion, 'a ∈ B');
});

runTest('checker validates bounded universal introduction with explicit witness scope', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ForallInIntro() {
  given(A subset B) →
  assert(forall x in A, x in B)
} ↔

proof ForallInIntro() {
  setVar(a) →
  assume(a in A) →
  assert(a in B) →
  conclude(forall x in A, x in B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[3].rule, 'FORALL_IN_INTRO');
  assert.equal(theoremReport.derivedConclusion, '∀ x ∈ A, x ∈ B');
});

runTest('checker rejects bounded universal introduction when the witness is reused as the binder', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ForallInIntroNotFresh() {
  given(A subset B) →
  assert(forall a in A, a in B)
} ↔

proof ForallInIntroNotFresh() {
  setVar(a) →
  assume(a in A) →
  assert(a in B) →
  conclude(forall a in A, a in B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  assert.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal|not yet derived/);
});

runTest('checker validates bounded existential introduction', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsInIntro() {
  given(a in A) →
  given(a in B) →
  assert(exists x in A, x in B)
} ↔

proof ExistsInIntro() {
  conclude(exists x in A, x in B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'EXISTS_IN_INTRO');
  assert.equal(theoremReport.derivedConclusion, '∃ x ∈ A, x ∈ B');
});

runTest('checker validates bounded existential elimination with explicit witness scope', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsInElim() {
  given(exists x in A, x in B) →
  assert(q)
} ↔

proof ExistsInElim() {
  setVar(a) →
  assume(a in A) →
  assume(a in B) →
  conclude(q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[3].rule, 'EXISTS_IN_ELIM');
  assert.equal(theoremReport.derivedConclusion, 'q');
});

runTest('checker rejects existential elimination when the witness leaks into the conclusion', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsInElimLeak() {
  given(exists x in A, x in B) →
  assert(a in C)
} ↔

proof ExistsInElimLeak() {
  setVar(a) →
  assume(a in A) →
  assume(a in B) →
  conclude(a in C)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  assert.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal|not yet derived/);
});

runTest('checker prevents witness facts from leaking after bounded universal introduction discharge', () => {
  const ast = parseLinesToAST(lexFL(`
theorem WitnessDoesNotLeak() {
  assert(a in B)
} ↔

proof WitnessDoesNotLeak() {
  setVar(a) →
  assume(a in A) →
  assert(a in B) →
  conclude(forall x in A, x in B) →
  conclude(a in B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  assert.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal|not yet derived|scope error/i);
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

// ── Phase 4: New propositional rules ─────────────────────────────────────────

runTest('checker accepts OR_INTRO_LEFT (have p, conclude p ∨ q)', () => {
  const ast = parseLinesToAST(lexFL(`
theorem OrIntroLeft() {
  assert(p -> p || q)
} ↔

proof OrIntroLeft() {
  assume(p) →
  conclude(p || q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const step = report.reports[0].proofSteps.find(s => s.rule === 'OR_INTRO_LEFT' || s.rule === 'IMPLIES_INTRO');
  assert.ok(step);
});

runTest('checker accepts OR_INTRO_RIGHT (have q, conclude p ∨ q)', () => {
  const ast = parseLinesToAST(lexFL(`
theorem OrIntroRight() {
  assert(q -> p || q)
} ↔

proof OrIntroRight() {
  assume(q) →
  conclude(p || q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
});

runTest('checker rejects OR_INTRO when neither side is established', () => {
  const ast = parseLinesToAST(lexFL(`
theorem OrIntroFail() {
  assert(p || q)
} ↔

proof OrIntroFail() {
  conclude(p || q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
});

runTest('checker accepts OR_ELIM (have p ∨ q, p → r, q → r → conclude r)', () => {
  const ast = parseLinesToAST(lexFL(`
theorem OrElim() {
  given(p || q) →
  given(p -> r) →
  given(q -> r) →
  assert(r)
} ↔

proof OrElim() {
  conclude(r)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const step = report.reports[0].proofSteps.find(s => s.rule === 'OR_ELIM');
  assert.ok(step);
});

runTest('checker accepts NOT_ELIM (double negation: ¬¬p → p)', () => {
  const ast = parseLinesToAST(lexFL(`
theorem NotElim() {
  given(¬¬p) →
  assert(p)
} ↔

proof NotElim() {
  conclude(p)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const step = report.reports[0].proofSteps.find(s => s.rule === 'NOT_ELIM');
  assert.ok(step);
});

runTest('checker accepts EX_FALSO (from ⊥ conclude anything)', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExFalso() {
  given(p) →
  given(¬p) →
  assert(q)
} ↔

proof ExFalso() {
  assume(¬q) →
  contradiction() →
  conclude(q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
});

// ── Phase 2: Sort errors ──────────────────────────────────────────────────────

runTest('checker rejects x ∈ x (both sides Element — sort error)', () => {
  const ast = parseLinesToAST(lexFL(`
theorem SortError() {
  assert(x ∈ x)
} ↔

proof SortError() {
  conclude(x ∈ x)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
  assert.match(messages, /sort error/i);
});

runTest('checker rejects A ⊆ x (right side Element in subset — sort error)', () => {
  const ast = parseLinesToAST(lexFL(`
theorem SortError2() {
  given(A ⊆ x) →
  assert(A ⊆ x)
} ↔

proof SortError2() {
  conclude(A ⊆ x)
}
`));
  const report = checkFile(ast);
  // sort error from the given/assume — should be flagged
  const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n') +
                   report.diagnostics.map(d => d.message).join('\n');
  assert.match(messages, /sort error/i);
});

// ── Phase 5: UNVERIFIED vs PROVED distinction ─────────────────────────────────

runTest('checker marks structurally-accepted assertions as UNVERIFIED', () => {
  const ast = parseLinesToAST(lexFL(`
theorem Unverified() {
  assert(p)
} ↔

proof Unverified() {
  assert(p)
}
`));
  const report = checkFile(ast);
  const unverifiedObj = report.reports[0].proofObjects.find(o => o.status === 'UNVERIFIED');
  assert.ok(unverifiedObj, 'Expected at least one UNVERIFIED proof object');
  assert.ok(report.reports[0].unverifiedCount > 0);
});

runTest('checker marks properly derived facts as PROVED', () => {
  const ast = parseLinesToAST(lexFL(`
theorem Proved() {
  assert(p -> p)
} ↔

proof Proved() {
  assume(p) →
  conclude(p)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.reports[0].unverifiedCount, 0);
  assert.ok(report.reports[0].provedCount > 0);
  const allProved = report.reports[0].proofObjects.every(o => o.status === 'PROVED');
  assert.equal(allProved, true);
});

runTest('checker rejects use of UNVERIFIED claim as derivation input', () => {
  const ast = parseLinesToAST(lexFL(`
theorem UnverifiedInput() {
  assert(p && q)
} ↔

proof UnverifiedInput() {
  assume(p) →
  assert(q) →
  conclude(p && q)
}
`));
  // q is asserted without derivation → UNVERIFIED → AND_INTRO fails
  const report = checkFile(ast);
  assert.equal(report.valid, false);
});

// ── Phase 3: Scope errors ─────────────────────────────────────────────────────

runTest('checker rejects set-theoretic conclusion with variable not in scope', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ScopeError() {
  assert(z ∈ C)
} ↔

proof ScopeError() {
  conclude(z ∈ C)
}
`));
  // z and C are never introduced via given/assume/setVar
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
  assert.match(messages, /scope error/i);
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
