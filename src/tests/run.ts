import { strict as assert } from 'assert';
import { execFileSync } from 'child_process';
import * as fs from 'fs';
import * as os from 'os';
import * as path from 'path';
import { lexFL } from '../parser/lexer';
import { parseExpr } from '../parser/expr';
import { parseLinesToAST } from '../parser/parser';
import { checkFile } from '../checker/checker';
import {
  canonicalizeProp,
  exprToProp,
  isSetBuilderLikeCanonical,
  parseBoundedQuantifierCanonical,
  parseCanonicalExpr,
  parseIndexedUnionCanonical,
  parseSetBuilderCanonical,
  parseStandaloneTypedQuantifierCanonical,
  parseTypedQuantifierCanonical,
  sameProp,
} from '../checker/propositions';
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
  assert.equal(quantified.type, 'Quantified');
  assert.equal(quantified.quantifier, 'forall');
  assert.equal(quantified.binderStyle, 'bounded');
  assert.equal(quantified.variable, 'x');
  assert.equal(quantified.domain, 'A');
  assert.equal(exprToProp(quantified), '∀ x ∈ A, ∃ y ∈ B');
});

runTest('parseExpr normalizes typed quantified binders into canonical atom form', () => {
  const quantified = parseExpr('∀(x y: G.carrier) ⇒ ∃(z: H) ⇒ x = z');
  assert.equal(quantified.type, 'Quantified');
  assert.equal(quantified.quantifier, 'forall');
  assert.equal(quantified.binderStyle, 'typed');
  assert.equal(quantified.variable, 'x');
  assert.equal(quantified.domain, 'G.carrier');
  assert.equal(exprToProp(quantified), '∀ x: G.carrier, ∀ y: G.carrier, ∃ z: H, x = z');
});

runTest('proposition normalization canonicalizes alternate surface syntax', () => {
  assert.equal(canonicalizeProp('(x in A) implies (x in A union B)'), 'x ∈ A → x ∈ A ∪ B');
  assert.equal(canonicalizeProp('forall x in A, exists y in B'), '∀ x ∈ A, ∃ y ∈ B');
  assert.equal(sameProp('(p -> q)', 'p → q'), true);
  assert.equal(sameProp('(x in A) implies (x in A union B)', 'x ∈ A → x ∈ A ∪ B'), true);
});

runTest('proposition normalization builds structured canonical atoms for kernel relations', () => {
  const membership = parseCanonicalExpr('x in A');
  assert.equal('kind' in membership ? membership.kind : '', 'membership');
  if ('kind' in membership && membership.kind === 'membership') {
    assert.equal(membership.element, 'x');
    assert.equal(membership.set, 'A');
  }

  const subset = parseCanonicalExpr('A subseteq B');
  assert.equal('kind' in subset ? subset.kind : '', 'subset');
  if ('kind' in subset && subset.kind === 'subset') {
    assert.equal(subset.left, 'A');
    assert.equal(subset.right, 'B');
    assert.equal(subset.strict, false);
  }

  const equality = parseCanonicalExpr('x=y');
  assert.equal('kind' in equality ? equality.kind : '', 'equality');
  if ('kind' in equality && equality.kind === 'equality') {
    assert.equal(equality.left, 'x');
    assert.equal(equality.right, 'y');
  }

  const typed = parseCanonicalExpr('a: Nat');
  assert.equal('kind' in typed ? typed.kind : '', 'typed_variable');
  if ('kind' in typed && typed.kind === 'typed_variable') {
    assert.equal(typed.variable, 'a');
    assert.equal(typed.domain, 'ℕ');
  }
});

runTest('proposition normalization parses set-builder and indexed-union terms structurally', () => {
  const builder = parseSetBuilderCanonical('{xH | x ∈ G.carrier}');
  assert.ok(builder);
  assert.equal(builder!.elementTemplate, 'xH');
  assert.equal(builder!.variable, 'x');
  assert.equal(builder!.domain, 'G.carrier');

  const indexedUnion = parseIndexedUnionCanonical('∪{xH | x ∈ G.carrier}');
  assert.ok(indexedUnion);
  assert.equal(indexedUnion!.elementTemplate, 'xH');
  assert.equal(indexedUnion!.variable, 'x');
  assert.equal(indexedUnion!.domain, 'G.carrier');

  assert.equal(isSetBuilderLikeCanonical('{xH | x ∈ G.carrier}'), true);
  assert.equal(isSetBuilderLikeCanonical('∪{xH | x ∈ G.carrier}'), true);
  assert.equal(isSetBuilderLikeCanonical('x ∈ A'), false);
});

runTest('proposition normalization parses bounded and typed quantifiers structurally', () => {
  const bounded = parseBoundedQuantifierCanonical('forall x in A, x in B', 'forall');
  assert.ok(bounded);
  assert.equal(bounded!.variable, 'x');
  assert.equal(bounded!.set, 'A');
  assert.equal(bounded!.body, 'x ∈ B');

  const typed = parseTypedQuantifierCanonical('∀(x: Nat) ⇒ P(x)', 'forall');
  assert.ok(typed);
  assert.equal(typed!.variable, 'x');
  assert.equal(typed!.domain, 'ℕ');
  assert.equal(typed!.body, 'P(x)');

  const standalone = parseStandaloneTypedQuantifierCanonical('∃!(xH: Set)', 'exists_unique');
  assert.ok(standalone);
  assert.equal(standalone!.variable, 'xH');
  assert.equal(standalone!.domain, 'Set');
});

runTest('parseExpr accepts standalone existential-unique binders', () => {
  const quantified = parseExpr('∃!(xH: Set)');
  assert.equal(quantified.type, 'Quantified');
  assert.equal(quantified.quantifier, 'exists_unique');
  assert.equal(quantified.binderStyle, 'typed');
  assert.equal(quantified.variable, 'xH');
  assert.equal(quantified.domain, 'Set');
  assert.equal(quantified.body, null);
  assert.equal(exprToProp(quantified), '∃! xH: Set');
});

runTest('parseExpr preserves set-builder and indexed-union syntax structurally', () => {
  const builder = parseExpr('{xH | x ∈ G.carrier}');
  assert.equal(builder.type, 'SetBuilder');
  assert.equal(builder.element, 'xH');
  assert.equal(builder.variable, 'x');
  assert.equal(builder.domain, 'G.carrier');
  assert.equal(exprToProp(builder), '{xH | x ∈ G.carrier}');

  const indexedUnion = parseExpr('∪{xH | x ∈ G.carrier}');
  assert.equal(indexedUnion.type, 'IndexedUnion');
  assert.equal(indexedUnion.builder.element, 'xH');
  assert.equal(indexedUnion.builder.variable, 'x');
  assert.equal(indexedUnion.builder.domain, 'G.carrier');
  assert.equal(exprToProp(indexedUnion), '∪{xH | x ∈ G.carrier}');
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

runTest('checker classifies typed quantified binders as kernel gaps, not parser fallbacks', () => {
  const ast = parseLinesToAST(lexFL(`
theorem TypedQuantifierDemo() {
  assert(∀(n: ℕ) ⇒ n = n)
} ↔

proof TypedQuantifierDemo() {
  assert(∀(n: ℕ) ⇒ n = n)
}
`));
  const report = checkFile(ast);
  const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
  assert.doesNotMatch(messages, /opaque symbolic claim/i);
  assert.match(messages, /does not establish theorem goal/i);
});

runTest('checker preserves standalone existential-unique binders inside larger expressions', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsUniqueShorthand() {
  assert(∀(x: G.carrier) ⇒ (∃!(xH: Set) ∧ DisjointCosets(G, H)))
} ↔

proof ExistsUniqueShorthand() {
  assert(∀(x: G.carrier) ⇒ (∃!(xH: Set) ∧ DisjointCosets(G, H)))
}
`));
  const report = checkFile(ast);
  const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
  assert.doesNotMatch(messages, /opaque symbolic claim/i);
  assert.match(messages, /EXISTS_UNIQUE|outside the current kernel subset/i);
});

runTest('checker classifies indexed-union set-builder equalities as set reasoning, not arithmetic fallback', () => {
  const ast = parseLinesToAST(lexFL(`
theorem IndexedUnionDemo() {
  assert(∪{xH | x ∈ G.carrier} = G.carrier)
} ↔

proof IndexedUnionDemo() {
  assert(∪{xH | x ∈ G.carrier} = G.carrier)
}
`));
  const report = checkFile(ast);
  const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
  assert.doesNotMatch(messages, /opaque symbolic claim/i);
  assert.doesNotMatch(messages, /ARITHMETIC_REASONING/);
  assert.match(messages, /SET_OPERATOR_REASONING|outside the current kernel subset/i);
});

runTest('checker preserves indexed-union equalities as structured expressions in theorem goals', () => {
  const ast = parseLinesToAST(lexFL(`
theorem IndexedUnionStructured() {
  assert(∪{xH | x ∈ G.carrier} = G.carrier)
}
`));
  const theorem = ast[0];
  assert.equal(theorem.type, 'Theorem');
  const claim = theorem.body[0];
  assert.equal(claim.type, 'Assert');
  assert.equal(claim.expr.type, 'Atom');
  assert.equal(claim.expr.atomKind, 'expression');
});

runTest('checker derives set-builder membership from a witness membership', () => {
  const ast = parseLinesToAST(lexFL(`
theorem SetBuilderIntro() {
  given(x ∈ A) →
  assert(xH ∈ {xH | x ∈ A})
} ↔

proof SetBuilderIntro() {
  conclude(xH ∈ {xH | x ∈ A})
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'SET_BUILDER_INTRO');
  assert.equal(theoremReport.derivedConclusion, 'xH ∈ {xH | x ∈ A}');
});

runTest('checker derives indexed-union membership from witness and body membership', () => {
  const ast = parseLinesToAST(lexFL(`
theorem IndexedUnionIntro() {
  given(x ∈ G.carrier) →
  given(g ∈ xH) →
  assert(g ∈ ∪{xH | x ∈ G.carrier})
} ↔

proof IndexedUnionIntro() {
  conclude(g ∈ ∪{xH | x ∈ G.carrier})
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'INDEXED_UNION_INTRO');
  assert.equal(theoremReport.derivedConclusion, 'g ∈ ∪{xH | x ∈ G.carrier}');
});

runTest('checker eliminates indexed-union membership with an explicit witness scope', () => {
  const ast = parseLinesToAST(lexFL(`
theorem IndexedUnionElim() {
  given(g ∈ ∪{xH | x ∈ G.carrier}) →
  assert(q)
} ↔

proof IndexedUnionElim() {
  setVar(a) →
  assume(a ∈ G.carrier) →
  assume(g ∈ aH) →
  conclude(q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[3].rule, 'INDEXED_UNION_ELIM');
  assert.equal(theoremReport.derivedConclusion, 'q');
});

runTest('checker rejects indexed-union elimination when the witness leaks into the conclusion', () => {
  const ast = parseLinesToAST(lexFL(`
theorem IndexedUnionElimLeak() {
  given(g ∈ ∪{xH | x ∈ G.carrier}) →
  assert(a ∈ B)
} ↔

proof IndexedUnionElimLeak() {
  setVar(a) →
  assume(a ∈ G.carrier) →
  assume(g ∈ aH) →
  conclude(a ∈ B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  assert.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal|not yet derived/);
});

runTest('checker derives indexed-union equality from matching membership quantifiers', () => {
  const ast = parseLinesToAST(lexFL(`
theorem IndexedUnionEquality() {
  given(∀ x ∈ ∪{y | y ∈ A}, x ∈ B) →
  given(∀ y ∈ B, y ∈ ∪{x | x ∈ A}) →
  assert(∪{x | x ∈ A} = B)
} ↔

proof IndexedUnionEquality() {
  conclude(∪{x | x ∈ A} = B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'SET_MEMBERSHIP_EQ');
  assert.equal(theoremReport.derivedConclusion, '∪{x | x ∈ A} = B');
});

runTest('checker rejects set equality when only one membership quantifier is present', () => {
  const ast = parseLinesToAST(lexFL(`
theorem IndexedUnionEqualityFail() {
  given(∀ x ∈ ∪{y | y ∈ A}, x ∈ B) →
  assert(∪{x | x ∈ A} = B)
} ↔

proof IndexedUnionEqualityFail() {
  conclude(∪{x | x ∈ A} = B)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'STRUCTURAL');
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

runTest('checker validates direct equality reflexivity and symmetry', () => {
  const reflAst = parseLinesToAST(lexFL(`
theorem EqualityRefl() {
  assert(x = x)
} ↔

proof EqualityRefl() {
  conclude(x = x)
}
`));
  const reflReport = checkFile(reflAst);
  assert.equal(reflReport.valid, true);
  assert.equal(reflReport.reports[0].proofSteps[0].rule, 'EQUALITY_REFL');

  const symmAst = parseLinesToAST(lexFL(`
theorem EqualitySymm() {
  given(x = y) →
  assert(y = x)
} ↔

proof EqualitySymm() {
  conclude(y = x)
}
`));
  const symmReport = checkFile(symmAst);
  assert.equal(symmReport.valid, true);
  assert.equal(symmReport.reports[0].proofSteps[0].rule, 'EQUALITY_SYMM');
});

runTest('checker validates equality transitivity', () => {
  const ast = parseLinesToAST(lexFL(`
theorem EqualityTrans() {
  given(x = y) →
  given(y = z) →
  assert(x = z)
} ↔

proof EqualityTrans() {
  conclude(x = z)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.reports[0].proofSteps[0].rule, 'EQUALITY_TRANS');
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

runTest('checker validates typed universal elimination', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ForallTypedElim() {
  given(∀ x: Nat, P(x)) →
  assert(P(a))
} ↔

proof ForallTypedElim() {
  setVar(a: Nat) →
  conclude(P(a))
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[1].rule, 'FORALL_TYPED_ELIM');
  assert.equal(theoremReport.derivedConclusion, 'P(a)');
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

runTest('checker validates typed universal introduction with explicit typed witness scope', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ForallTypedIntro() {
  given(∀ x: Nat, P(x)) →
  assert(∀ y: Nat, P(y))
} ↔

proof ForallTypedIntro() {
  setVar(a: Nat) →
  conclude(P(a)) →
  conclude(∀ y: Nat, P(y))
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[1].rule, 'FORALL_TYPED_ELIM');
  assert.equal(theoremReport.proofSteps[2].rule, 'FORALL_TYPED_INTRO');
  assert.equal(theoremReport.derivedConclusion, '∀ y: ℕ, P(y)');
});

runTest('checker satisfies nested typed universal theorem goals recursively', () => {
  const ast = parseLinesToAST(lexFL(`
theorem NestedForallGoal() {
  given(∀ x: Nat, ∀ y: Nat, Q(x, y)) →
  assert(∀ u: Nat, ∀ v: Nat, Q(u, v))
} ↔

proof NestedForallGoal() {
  setVar(a: Nat) →
  setVar(b: Nat) →
  conclude(Q(a, b))
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
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

runTest('checker validates typed existential introduction', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsTypedIntro() {
  given(P(a)) →
  assert(∃ x: Nat, P(x))
} ↔

proof ExistsTypedIntro() {
  setVar(a: Nat) →
  conclude(∃ x: Nat, P(x))
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[1].rule, 'EXISTS_TYPED_INTRO');
  assert.equal(theoremReport.derivedConclusion, '∃ x: ℕ, P(x)');
});

runTest('checker validates typed existential introduction from arithmetic witness equality', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsTypedArithmeticIntro() {
  given(n = m · r) →
  assert(∃ k: Nat, n = m · k)
} ↔

proof ExistsTypedArithmeticIntro() {
  setVar(r: Nat) →
  conclude(∃ k: Nat, n = m · k)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  assert.equal(report.reports[0].proofSteps[1].rule, 'EXISTS_TYPED_INTRO');
});

runTest('checker rewrites multiplicative equality by arithmetic commutativity', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ArithmeticComm() {
  given(n = r · m) →
  assert(n = m · r)
} ↔

proof ArithmeticComm() {
  conclude(n = m · r)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'ARITHMETIC_COMM');
  assert.equal(theoremReport.derivedConclusion, 'n = m · r');
});

runTest('checker validates typed existential introduction from commuted arithmetic witness equality', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsTypedArithmeticIntroComm() {
  given(n = r · m) →
  assert(∃ k: Nat, n = m · k)
} ↔

proof ExistsTypedArithmeticIntroComm() {
  setVar(r: Nat) →
  conclude(∃ k: Nat, n = m · k)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[1].rule, 'EXISTS_TYPED_INTRO');
  assert.equal(theoremReport.derivedConclusion, '∃ k: ℕ, n = m · k');
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

runTest('checker validates typed existential elimination with explicit witness scope', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsTypedElim() {
  given(∃ x: Nat, P(x)) →
  assert(q)
} ↔

proof ExistsTypedElim() {
  setVar(a: Nat) →
  assume(P(a)) →
  conclude(q)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[2].rule, 'EXISTS_TYPED_ELIM');
  assert.equal(theoremReport.derivedConclusion, 'q');
});

runTest('checker validates unique existence introduction from existence and uniqueness', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsUniqueIntro() {
  given(∃ x: Nat, P(x)) →
  given(∀ y: Nat, ∀ z: Nat, (P(y) && P(z)) -> y = z) →
  assert(∃! x: Nat, P(x))
} ↔

proof ExistsUniqueIntro() {
  conclude(∃! x: Nat, P(x))
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'EXISTS_UNIQUE_INTRO');
  assert.equal(theoremReport.derivedConclusion, '∃! x: ℕ, P(x)');
});

runTest('checker derives existence from a unique existence premise', () => {
  const ast = parseLinesToAST(lexFL(`
theorem ExistsUniqueElimExistence() {
  given(∃! x: Nat, P(x)) →
  assert(∃ x: Nat, P(x))
} ↔

proof ExistsUniqueElimExistence() {
  conclude(∃ x: Nat, P(x))
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'EXISTS_UNIQUE_ELIM');
  assert.equal(theoremReport.derivedConclusion, '∃ x: ℕ, P(x)');
});

runTest('checker derives divisibility from multiplicative equality', () => {
  const ast = parseLinesToAST(lexFL(`
theorem DividesIntro() {
  given(n = m · r) →
  assert(m divides n)
} ↔

proof DividesIntro() {
  conclude(m divides n)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'DIVIDES_INTRO');
  assert.equal(theoremReport.derivedConclusion, 'm divides n');
});

runTest('checker rewrites cardinality-index equalities by arithmetic commutativity', () => {
  const ast = parseLinesToAST(lexFL(`
theorem CardinalityComm() {
  given(|G| = [G:H] · |H|) →
  assert(|G| = |H| · [G:H])
} ↔

proof CardinalityComm() {
  conclude(|G| = |H| · [G:H])
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'ARITHMETIC_COMM');
  assert.equal(theoremReport.derivedConclusion, '|G| = |H| · [G:H]');
});

runTest('checker derives divisibility from cardinality-index equality', () => {
  const ast = parseLinesToAST(lexFL(`
theorem CardinalityDivides() {
  given(|G| = |H| · [G:H]) →
  assert(|H| divides |G|)
} ↔

proof CardinalityDivides() {
  conclude(|H| divides |G|)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].rule, 'DIVIDES_INTRO');
  assert.equal(theoremReport.derivedConclusion, '|H| divides |G|');
});

runTest('checker accepts arithmetic conjunctions and implications as kernel-checkable goals', () => {
  const ast = parseLinesToAST(lexFL(`
theorem CardinalityImplication() {
  given(|G| = |H| · [G:H]) →
  assert((r = [G:H] && |H| = m) -> |H| divides |G|)
} ↔

proof CardinalityImplication() {
  assume(r = [G:H] && |H| = m) →
  conclude(|H| divides |G|)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, true);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[1].rule, 'DIVIDES_INTRO');
  assert.equal(theoremReport.derivedConclusion, '|H| divides |G|');
  assert.equal(theoremReport.diagnostics.some(d => d.message.includes('ARITHMETIC_REASONING')), false);
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

runTest('checker marks external lemma application as UNVERIFIED and non-trusted', () => {
  const ast = parseLinesToAST(lexFL(`
theorem UsesExternalLemma() {
  assert(q)
} ↔

proof UsesExternalLemma() {
  apply(ForwardStep)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  const theoremReport = report.reports[0];
  assert.equal(theoremReport.proofSteps[0].status, 'UNVERIFIED');
  const importedFact = theoremReport.proofObjects.find(object => object.source === 'lemma_application');
  assert.ok(importedFact);
  assert.equal(importedFact!.status, 'UNVERIFIED');
  assert.match(theoremReport.diagnostics.map(d => d.message).join('\n'), /UNVERIFIED because 'ForwardStep' is not defined in this file/i);
  assert.match(theoremReport.diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal/i);
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
  assert.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /UNVERIFIED and does not advance the trusted proof state/i);
});

runTest('checker does not let UNVERIFIED assertions satisfy theorem goals', () => {
  const ast = parseLinesToAST(lexFL(`
theorem UnverifiedGoal() {
  assert(p)
} ↔

proof UnverifiedGoal() {
  assert(p)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  const messages = report.reports[0].diagnostics.map(d => d.message).join('\n');
  assert.match(messages, /does not establish theorem goal/i);
  assert.match(messages, /UNVERIFIED and does not advance the trusted proof state/i);
});

runTest('checker does not let UNVERIFIED conclusions satisfy theorem goals', () => {
  const ast = parseLinesToAST(lexFL(`
theorem UnverifiedConclusionGoal() {
  assert(p)
} ↔

proof UnverifiedConclusionGoal() {
  conclude(p)
}
`));
  const report = checkFile(ast);
  assert.equal(report.valid, false);
  const messages = report.reports[0].diagnostics.map(d => d.message).join('\n');
  assert.match(messages, /does not establish theorem goal/i);
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

runTest('checker strict mode rejects UNVERIFIED assertions', () => {
  const ast = parseLinesToAST(lexFL(`
theorem UnverifiedStrict() {
  assert(p)
} ↔

proof UnverifiedStrict() {
  assert(p)
}
`));
  const report = checkFile(ast, { strict: true });
  assert.equal(report.valid, false);
  const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
  assert.match(messages, /Strict mode rejects/i);
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

runTest('fl check --strict exits non-zero on UNVERIFIED proofs', () => {
  const file = path.join(os.tmpdir(), `strict-${Date.now()}.fl`);
  fs.writeFileSync(file, `
theorem StrictCli() {
  assert(p)
} ↔

proof StrictCli() {
  assert(p)
}
`);
  let stderr = '';
  try {
    execFileSync('node', ['fl.js', 'check', '--strict', file], {
      cwd: process.cwd(),
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    assert.fail('Expected strict CLI invocation to fail');
  } catch (error: any) {
    stderr = String(error.stdout ?? '') + String(error.stderr ?? '');
  }
  assert.match(stderr, /Strict mode rejects/);
});

console.log('All unit tests passed.');
