"use strict";
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
const assert_1 = require("assert");
const child_process_1 = require("child_process");
const fs = __importStar(require("fs"));
const os = __importStar(require("os"));
const path = __importStar(require("path"));
const lexer_1 = require("../parser/lexer");
const expr_1 = require("../parser/expr");
const parser_1 = require("../parser/parser");
const checker_1 = require("../checker/checker");
const propositions_1 = require("../checker/propositions");
const formal_1 = require("../parser/formal");
const transpiler_1 = require("../react/transpiler");
function runTest(name, fn) {
    try {
        fn();
        console.log(`✓ ${name}`);
    }
    catch (error) {
        console.error(`✗ ${name}`);
        throw error;
    }
}
runTest('parseExpr marks quoted claims as string atoms', () => {
    const expr = (0, expr_1.parseExpr)('"hello world"');
    assert_1.strict.equal(expr.type, 'Atom');
    assert_1.strict.equal(expr.atomKind, 'string');
});
runTest('parseExpr builds logical AST for supported expressions', () => {
    const expr = (0, expr_1.parseExpr)('(p && q) -> r');
    assert_1.strict.equal(expr.type, 'Implies');
});
runTest('parseExpr accepts MI-style implication and biconditional symbols', () => {
    const impliesExpr = (0, expr_1.parseExpr)('(x ∈ A) ⇒ (x ∈ A)');
    assert_1.strict.equal(impliesExpr.type, 'Implies');
    const iffExpr = (0, expr_1.parseExpr)('(x ≤ y) ⇔ (x ≤ y)');
    assert_1.strict.equal(iffExpr.type, 'Iff');
    const subsetExpr = (0, expr_1.parseExpr)('(x ∈ A) ⇒ (A ⊆ B)');
    assert_1.strict.equal(subsetExpr.type, 'Implies');
});
runTest('parseExpr normalizes word equivalents for set notation and bounded quantifiers', () => {
    const unionExpr = (0, expr_1.parseExpr)('(x in A) implies (x in A union B)');
    assert_1.strict.equal((0, propositions_1.exprToProp)(unionExpr), 'x ∈ A → x ∈ A ∪ B');
    const quantified = (0, expr_1.parseExpr)('forall x in A, exists y in B');
    assert_1.strict.equal(quantified.type, 'Quantified');
    assert_1.strict.equal(quantified.quantifier, 'forall');
    assert_1.strict.equal(quantified.binderStyle, 'bounded');
    assert_1.strict.equal(quantified.variable, 'x');
    assert_1.strict.equal(quantified.domain, 'A');
    assert_1.strict.equal((0, propositions_1.exprToProp)(quantified), '∀ x ∈ A, ∃ y ∈ B');
});
runTest('parseExpr normalizes typed quantified binders into canonical atom form', () => {
    const quantified = (0, expr_1.parseExpr)('∀(x y: G.carrier) ⇒ ∃(z: H) ⇒ x = z');
    assert_1.strict.equal(quantified.type, 'Quantified');
    assert_1.strict.equal(quantified.quantifier, 'forall');
    assert_1.strict.equal(quantified.binderStyle, 'typed');
    assert_1.strict.equal(quantified.variable, 'x');
    assert_1.strict.equal(quantified.domain, 'G.carrier');
    assert_1.strict.equal((0, propositions_1.exprToProp)(quantified), '∀ x: G.carrier, ∀ y: G.carrier, ∃ z: H, x = z');
});
runTest('parseExpr accepts standalone existential-unique binders', () => {
    const quantified = (0, expr_1.parseExpr)('∃!(xH: Set)');
    assert_1.strict.equal(quantified.type, 'Quantified');
    assert_1.strict.equal(quantified.quantifier, 'exists_unique');
    assert_1.strict.equal(quantified.binderStyle, 'typed');
    assert_1.strict.equal(quantified.variable, 'xH');
    assert_1.strict.equal(quantified.domain, 'Set');
    assert_1.strict.equal(quantified.body, null);
    assert_1.strict.equal((0, propositions_1.exprToProp)(quantified), '∃! xH: Set');
});
runTest('parser preserves malformed expressions as opaque atoms', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Broken() {
  assert(p && && q);
}
`));
    const theorem = ast[0];
    assert_1.strict.equal(theorem.type, 'Theorem');
    const claim = theorem.body[0];
    assert_1.strict.equal(claim.type, 'Assert');
    assert_1.strict.equal(claim.expr.type, 'Atom');
    assert_1.strict.equal(claim.expr.atomKind, 'opaque');
    assert_1.strict.match(claim.expr.parseError ?? '', /Unexpected token|Unexpected token after expression|Expected/);
});
runTest('checker validates a paired theorem and proof', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Identity() {
  assert(p -> p)
} ↔

proof Identity() {
  assume(p) →
  conclude(p)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.pairedCount, 1);
    assert_1.strict.equal(report.reports[0].goal, 'p → p');
    assert_1.strict.equal(report.reports[0].derivedConclusion, 'p → p');
    assert_1.strict.equal(report.reports[0].proofSteps[0].rule, 'ASSUMPTION');
    assert_1.strict.equal(report.reports[0].proofSteps[1].rule, 'IMPLIES_INTRO');
    assert_1.strict.equal(report.reports[0].proofObjects[0].rule, 'ASSUMPTION');
    assert_1.strict.equal(report.reports[0].proofObjects[0].dependsOnIds.length, 0);
    assert_1.strict.equal(report.reports[0].derivations.length, 1);
    assert_1.strict.equal(report.reports[0].derivations[0].rule, 'IMPLIES_INTRO');
    const implicationObject = report.reports[0].proofObjects.find(object => object.rule === 'IMPLIES_INTRO');
    assert_1.strict.ok(implicationObject);
    assert_1.strict.equal(implicationObject.claim, 'p → p');
    assert_1.strict.equal(report.reports[0].baseFactIds.length, 1);
    assert_1.strict.equal(report.reports[0].derivedFactIds.length, 1);
});
runTest('checker rejects proofs that do not establish theorem goal', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Identity() {
  assert(p -> p)
} ↔

proof Identity() {
  assume(p) →
  conclude(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
    assert_1.strict.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal/);
});
runTest('checker surfaces parser fallback diagnostics for malformed rich mathematical notation', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem QuantifiedIdentity() {
  assert(∀(n: ℕ) ⇒)
} ↔

proof QuantifiedIdentity() {
  assert(∀(n: ℕ) ⇒)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
    assert_1.strict.match(messages, /outside the current parser\/checker subset/i);
    assert_1.strict.match(messages, /opaque symbolic claim/i);
});
runTest('checker diagnoses unsupported quantified binder forms with a specific missing-rule hint', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem BoundedQuantifierDemo() {
  assert(forall x, x in A)
} ↔

proof BoundedQuantifierDemo() {
  assert(forall x, x in A)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    const messages = report.reports.flatMap(r => r.diagnostics.map(d => `${d.message}\n${d.hint ?? ''}`)).join('\n');
    assert_1.strict.match(messages, /FORALL_BINDER/);
    assert_1.strict.match(messages, /kernel/i);
});
runTest('checker classifies typed quantified binders as kernel gaps, not parser fallbacks', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem TypedQuantifierDemo() {
  assert(∀(n: ℕ) ⇒ n = n)
} ↔

proof TypedQuantifierDemo() {
  assert(∀(n: ℕ) ⇒ n = n)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
    assert_1.strict.doesNotMatch(messages, /opaque symbolic claim/i);
    assert_1.strict.match(messages, /does not establish theorem goal/i);
});
runTest('checker preserves standalone existential-unique binders inside larger expressions', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ExistsUniqueShorthand() {
  assert(∀(x: G.carrier) ⇒ (∃!(xH: Set) ∧ DisjointCosets(G, H)))
} ↔

proof ExistsUniqueShorthand() {
  assert(∀(x: G.carrier) ⇒ (∃!(xH: Set) ∧ DisjointCosets(G, H)))
}
`));
    const report = (0, checker_1.checkFile)(ast);
    const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
    assert_1.strict.doesNotMatch(messages, /opaque symbolic claim/i);
    assert_1.strict.match(messages, /FORALL_BINDER|outside the current kernel subset/i);
});
runTest('checker accepts conjunction goals when both parts are established', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Pair() {
  assert(p && q)
} ↔

proof Pair() {
  assume(p) →
  assume(q) →
  conclude(p && q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].proofSteps[2].rule, 'AND_INTRO');
    const conjunctionObject = report.reports[0].proofObjects.find(object => object.claim === 'p ∧ q');
    assert_1.strict.ok(conjunctionObject);
    assert_1.strict.equal(conjunctionObject.rule, 'AND_INTRO');
    assert_1.strict.equal(conjunctionObject.status, 'PROVED');
    assert_1.strict.equal(conjunctionObject.dependsOn.length, 2);
    assert_1.strict.equal(conjunctionObject.dependsOnIds.length, 2);
    const conjunctionDerivation = report.reports[0].derivations.find(node => node.rule === 'AND_INTRO');
    assert_1.strict.ok(conjunctionDerivation);
    assert_1.strict.equal(conjunctionDerivation.inputIds.length, 2);
});
runTest('checker accepts modus ponens style derivations', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ModusPonens() {
  given(p -> q)
  assert(q)
} ↔

proof ModusPonens() {
  assume(p) →
  conclude(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].premises[0], 'p → q');
    assert_1.strict.equal(report.reports[0].proofSteps[1].rule, 'IMPLIES_ELIM');
    assert_1.strict.equal(report.reports[0].proofObjects[0].rule, 'PREMISE');
    assert_1.strict.equal(report.reports[0].proofObjects[0].dependsOnIds.length, 0);
    const modusPonensDerivation = report.reports[0].derivations.find(node => node.rule === 'IMPLIES_ELIM');
    assert_1.strict.ok(modusPonensDerivation);
    assert_1.strict.equal(modusPonensDerivation.inputIds.length, 2);
    assert_1.strict.equal(report.reports[0].baseFactIds.length, 2);
    assert_1.strict.equal(report.reports[0].derivedFactIds.length, 1);
});
runTest('checker accepts conjunction elimination derivations', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem LeftProjection() {
  assert((p && q) -> p)
} ↔

proof LeftProjection() {
  assume(p && q) →
  conclude(p)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].proofSteps[1].rule, 'AND_ELIM');
});
runTest('checker accepts MI-style symbolic identity demos', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem MembershipIdentity() {
  assert((x ∈ A) ⇒ (x ∈ A))
} ↔

proof MembershipIdentity() {
  assume(x ∈ A) →
  conclude(x ∈ A)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].derivedConclusion, 'x ∈ A → x ∈ A');
});
runTest('checker validates set-theoretic subset transport', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem SubsetTransport() {
  given(x ∈ A) →
  given(A ⊆ B) →
  assert(x ∈ B)
} ↔

proof SubsetTransport() {
  conclude(x ∈ B)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[0].rule, 'SUBSET_ELIM');
    assert_1.strict.equal(theoremReport.derivedConclusion, 'x ∈ B');
    const subsetDerivation = theoremReport.derivations.find(node => node.rule === 'SUBSET_ELIM');
    assert_1.strict.ok(subsetDerivation);
    assert_1.strict.equal(subsetDerivation.inputIds.length, 2);
});
runTest('checker validates chained set-theoretic subset transport', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[0].rule, 'SUBSET_ELIM');
    assert_1.strict.equal(theoremReport.proofSteps[1].rule, 'SUBSET_ELIM');
    assert_1.strict.equal(theoremReport.derivedConclusion, 'x ∈ C');
    assert_1.strict.equal(theoremReport.derivations.filter(node => node.rule === 'SUBSET_ELIM').length, 2);
});
runTest('checker validates subset transitivity', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem SubsetTransitivity() {
  given(A subset B) →
  given(B subset C) →
  assert(A subset C)
} ↔

proof SubsetTransitivity() {
  conclude(A subset C)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[0].rule, 'SUBSET_TRANS');
    assert_1.strict.equal(theoremReport.derivedConclusion, 'A ⊆ C');
});
runTest('checker validates equality substitution on membership claims', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem EqualitySubstitution() {
  given(x = y) →
  given(x in A) →
  assert(y in A)
} ↔

proof EqualitySubstitution() {
  conclude(y in A)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[0].rule, 'EQUALITY_SUBST');
    assert_1.strict.equal(theoremReport.derivedConclusion, 'y ∈ A');
});
runTest('checker validates direct equality reflexivity and symmetry', () => {
    const reflAst = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem EqualityRefl() {
  assert(x = x)
} ↔

proof EqualityRefl() {
  conclude(x = x)
}
`));
    const reflReport = (0, checker_1.checkFile)(reflAst);
    assert_1.strict.equal(reflReport.valid, true);
    assert_1.strict.equal(reflReport.reports[0].proofSteps[0].rule, 'EQUALITY_REFL');
    const symmAst = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem EqualitySymm() {
  given(x = y) →
  assert(y = x)
} ↔

proof EqualitySymm() {
  conclude(y = x)
}
`));
    const symmReport = (0, checker_1.checkFile)(symmAst);
    assert_1.strict.equal(symmReport.valid, true);
    assert_1.strict.equal(symmReport.reports[0].proofSteps[0].rule, 'EQUALITY_SYMM');
});
runTest('checker validates equality transitivity', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem EqualityTrans() {
  given(x = y) →
  given(y = z) →
  assert(x = z)
} ↔

proof EqualityTrans() {
  conclude(x = z)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].proofSteps[0].rule, 'EQUALITY_TRANS');
});
runTest('checker validates union introduction from word-form notation', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem UnionIntro() {
  given(x in A) →
  assert(x in A union B)
} ↔

proof UnionIntro() {
  conclude(x in A union B)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].proofSteps[0].rule, 'UNION_INTRO');
    assert_1.strict.equal(report.reports[0].derivedConclusion, 'x ∈ A ∪ B');
});
runTest('checker validates intersection introduction and elimination', () => {
    const introAst = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem IntersectionIntro() {
  given(x in A) →
  given(x in B) →
  assert(x in A intersection B)
} ↔

proof IntersectionIntro() {
  conclude(x in A intersection B)
}
`));
    const introReport = (0, checker_1.checkFile)(introAst);
    assert_1.strict.equal(introReport.valid, true);
    assert_1.strict.equal(introReport.reports[0].proofSteps[0].rule, 'INTERSECTION_INTRO');
    assert_1.strict.equal(introReport.reports[0].derivedConclusion, 'x ∈ A ∩ B');
    const elimAst = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem IntersectionRight() {
  given(x in A intersection B) →
  assert(x in B)
} ↔

proof IntersectionRight() {
  conclude(x in B)
}
`));
    const elimReport = (0, checker_1.checkFile)(elimAst);
    assert_1.strict.equal(elimReport.valid, true);
    assert_1.strict.equal(elimReport.reports[0].proofSteps[0].rule, 'INTERSECTION_ELIM');
    assert_1.strict.equal(elimReport.reports[0].derivedConclusion, 'x ∈ B');
});
runTest('checker validates bounded universal elimination', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ForallInElim() {
  given(forall x in A, x in B) →
  given(a in A) →
  assert(a in B)
} ↔

proof ForallInElim() {
  conclude(a in B)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[0].rule, 'FORALL_IN_ELIM');
    assert_1.strict.equal(theoremReport.derivedConclusion, 'a ∈ B');
});
runTest('checker validates typed universal elimination', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ForallTypedElim() {
  given(∀ x: Nat, P(x)) →
  assert(P(a))
} ↔

proof ForallTypedElim() {
  setVar(a: Nat) →
  conclude(P(a))
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[1].rule, 'FORALL_TYPED_ELIM');
    assert_1.strict.equal(theoremReport.derivedConclusion, 'P(a)');
});
runTest('checker validates bounded universal introduction with explicit witness scope', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[3].rule, 'FORALL_IN_INTRO');
    assert_1.strict.equal(theoremReport.derivedConclusion, '∀ x ∈ A, x ∈ B');
});
runTest('checker validates typed universal introduction with explicit typed witness scope', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[1].rule, 'FORALL_TYPED_ELIM');
    assert_1.strict.equal(theoremReport.proofSteps[2].rule, 'FORALL_TYPED_INTRO');
    assert_1.strict.equal(theoremReport.derivedConclusion, '∀ y: ℕ, P(y)');
});
runTest('checker satisfies nested typed universal theorem goals recursively', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
});
runTest('checker rejects bounded universal introduction when the witness is reused as the binder', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
    assert_1.strict.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal|not yet derived/);
});
runTest('checker validates bounded existential introduction', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ExistsInIntro() {
  given(a in A) →
  given(a in B) →
  assert(exists x in A, x in B)
} ↔

proof ExistsInIntro() {
  conclude(exists x in A, x in B)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[0].rule, 'EXISTS_IN_INTRO');
    assert_1.strict.equal(theoremReport.derivedConclusion, '∃ x ∈ A, x ∈ B');
});
runTest('checker validates typed existential introduction', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ExistsTypedIntro() {
  given(P(a)) →
  assert(∃ x: Nat, P(x))
} ↔

proof ExistsTypedIntro() {
  setVar(a: Nat) →
  conclude(∃ x: Nat, P(x))
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[1].rule, 'EXISTS_TYPED_INTRO');
    assert_1.strict.equal(theoremReport.derivedConclusion, '∃ x: ℕ, P(x)');
});
runTest('checker validates bounded existential elimination with explicit witness scope', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[3].rule, 'EXISTS_IN_ELIM');
    assert_1.strict.equal(theoremReport.derivedConclusion, 'q');
});
runTest('checker validates typed existential elimination with explicit witness scope', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[2].rule, 'EXISTS_TYPED_ELIM');
    assert_1.strict.equal(theoremReport.derivedConclusion, 'q');
});
runTest('checker validates unique existence introduction from existence and uniqueness', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ExistsUniqueIntro() {
  given(∃ x: Nat, P(x)) →
  given(∀ y: Nat, ∀ z: Nat, (P(y) && P(z)) -> y = z) →
  assert(∃! x: Nat, P(x))
} ↔

proof ExistsUniqueIntro() {
  conclude(∃! x: Nat, P(x))
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[0].rule, 'EXISTS_UNIQUE_INTRO');
    assert_1.strict.equal(theoremReport.derivedConclusion, '∃! x: ℕ, P(x)');
});
runTest('checker derives existence from a unique existence premise', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ExistsUniqueElimExistence() {
  given(∃! x: Nat, P(x)) →
  assert(∃ x: Nat, P(x))
} ↔

proof ExistsUniqueElimExistence() {
  conclude(∃ x: Nat, P(x))
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.proofSteps[0].rule, 'EXISTS_UNIQUE_ELIM');
    assert_1.strict.equal(theoremReport.derivedConclusion, '∃ x: ℕ, P(x)');
});
runTest('checker rejects existential elimination when the witness leaks into the conclusion', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
    assert_1.strict.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal|not yet derived/);
});
runTest('checker prevents witness facts from leaking after bounded universal introduction discharge', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
    assert_1.strict.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal|not yet derived|scope error/i);
});
runTest('checker enforces lemma hypotheses before apply', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
    assert_1.strict.match(report.reports.map(r => r.diagnostics.map(d => d.message).join('\n')).join('\n'), /missing hypotheses p/);
});
runTest('checker accepts chained lemma application with satisfied hypotheses', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports.find(r => r.name === 'UsesForwardStep');
    assert_1.strict.ok(theoremReport);
    assert_1.strict.equal(theoremReport.proofSteps[1].rule, 'BY_LEMMA');
    assert_1.strict.equal(theoremReport.proofSteps[1].uses?.[0], 'p → q');
    assert_1.strict.equal(theoremReport.proofSteps[1].imports?.[0], 'q');
    const importedFact = theoremReport.proofObjects.find(object => object.source === 'lemma_application' && object.claim === 'q');
    assert_1.strict.ok(importedFact);
    assert_1.strict.equal(importedFact.dependsOn[0], 'p → q');
    assert_1.strict.equal(importedFact.imports?.[0], 'q');
    assert_1.strict.equal(importedFact.dependsOnIds.length, 1);
    const lemmaDerivation = theoremReport.derivations.find(node => node.rule === 'BY_LEMMA');
    assert_1.strict.ok(lemmaDerivation);
    assert_1.strict.equal(lemmaDerivation.inputIds.length, 1);
    assert_1.strict.equal(theoremReport.derivedFactIds.length, 1);
});
runTest('checker accepts chained multi-premise implication demo', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
});
runTest('checker accepts chained conjunction premise demo', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem RightProjection() {
  given(p && q) →
  assert(q)
} ↔

proof RightProjection() {
  conclude(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
});
runTest('checker accepts contradiction discharge in the current demo subset', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.method, 'contradiction');
    assert_1.strict.equal(theoremReport.proofSteps[1].rule, 'CONTRADICTION');
    assert_1.strict.equal(theoremReport.proofSteps[2].rule, 'CONTRADICTION');
    const contradictionFact = theoremReport.proofObjects.find(object => object.claim === 'contradiction');
    assert_1.strict.ok(contradictionFact);
    assert_1.strict.match(contradictionFact.dependsOn.join(' '), /p/);
    assert_1.strict.match(contradictionFact.dependsOn.join(' '), /¬p/);
    assert_1.strict.equal(contradictionFact.dependsOnIds.length, 2);
});
runTest('checker records implication proof objects for derived facts', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ModusPonens() {
  given(p -> q) →
  assert(q)
} ↔

proof ModusPonens() {
  assume(p) →
  conclude(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    const theoremReport = report.reports[0];
    const conclusionObject = theoremReport.proofObjects.find(object => object.source === 'conclusion' && object.claim === 'q');
    assert_1.strict.ok(conclusionObject);
    assert_1.strict.equal(conclusionObject.rule, 'IMPLIES_ELIM');
    assert_1.strict.equal(conclusionObject.dependsOn.length, 2);
    assert_1.strict.equal(conclusionObject.dependsOnIds.length, 2);
    assert_1.strict.match(conclusionObject.dependsOn.join(' '), /p/);
    assert_1.strict.match(conclusionObject.dependsOn.join(' '), /q/);
});
runTest('parser rejects missing connective between top-level blocks', () => {
    assert_1.strict.throws(() => (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
`)), /Missing connective between top-level blocks/);
});
runTest('eval backend rejects unsupported mathematical notation', () => {
    assert_1.strict.throws(() => {
        const js = (0, formal_1.parseFL)(`
theorem AdvancedMath() {
  assert(∀(n: ℕ) ⇒ n = n)
}
`);
        eval(js);
    }, /Use 'fl verify'/);
});
// ── Phase 4: New propositional rules ─────────────────────────────────────────
runTest('checker accepts OR_INTRO_LEFT (have p, conclude p ∨ q)', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem OrIntroLeft() {
  assert(p -> p || q)
} ↔

proof OrIntroLeft() {
  assume(p) →
  conclude(p || q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const step = report.reports[0].proofSteps.find(s => s.rule === 'OR_INTRO_LEFT' || s.rule === 'IMPLIES_INTRO');
    assert_1.strict.ok(step);
});
runTest('checker accepts OR_INTRO_RIGHT (have q, conclude p ∨ q)', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem OrIntroRight() {
  assert(q -> p || q)
} ↔

proof OrIntroRight() {
  assume(q) →
  conclude(p || q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
});
runTest('checker rejects OR_INTRO when neither side is established', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem OrIntroFail() {
  assert(p || q)
} ↔

proof OrIntroFail() {
  conclude(p || q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
});
runTest('checker accepts OR_ELIM (have p ∨ q, p → r, q → r → conclude r)', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const step = report.reports[0].proofSteps.find(s => s.rule === 'OR_ELIM');
    assert_1.strict.ok(step);
});
runTest('checker accepts NOT_ELIM (double negation: ¬¬p → p)', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem NotElim() {
  given(¬¬p) →
  assert(p)
} ↔

proof NotElim() {
  conclude(p)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const step = report.reports[0].proofSteps.find(s => s.rule === 'NOT_ELIM');
    assert_1.strict.ok(step);
});
runTest('checker accepts EX_FALSO (from ⊥ conclude anything)', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
});
// ── Phase 2: Sort errors ──────────────────────────────────────────────────────
runTest('checker rejects x ∈ x (both sides Element — sort error)', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem SortError() {
  assert(x ∈ x)
} ↔

proof SortError() {
  conclude(x ∈ x)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
    const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
    assert_1.strict.match(messages, /sort error/i);
});
runTest('checker rejects A ⊆ x (right side Element in subset — sort error)', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem SortError2() {
  given(A ⊆ x) →
  assert(A ⊆ x)
} ↔

proof SortError2() {
  conclude(A ⊆ x)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    // sort error from the given/assume — should be flagged
    const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n') +
        report.diagnostics.map(d => d.message).join('\n');
    assert_1.strict.match(messages, /sort error/i);
});
// ── Phase 5: UNVERIFIED vs PROVED distinction ─────────────────────────────────
runTest('checker marks structurally-accepted assertions as UNVERIFIED', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Unverified() {
  assert(p)
} ↔

proof Unverified() {
  assert(p)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    const unverifiedObj = report.reports[0].proofObjects.find(o => o.status === 'UNVERIFIED');
    assert_1.strict.ok(unverifiedObj, 'Expected at least one UNVERIFIED proof object');
    assert_1.strict.ok(report.reports[0].unverifiedCount > 0);
});
runTest('checker marks properly derived facts as PROVED', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Proved() {
  assert(p -> p)
} ↔

proof Proved() {
  assume(p) →
  conclude(p)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].unverifiedCount, 0);
    assert_1.strict.ok(report.reports[0].provedCount > 0);
    const allProved = report.reports[0].proofObjects.every(o => o.status === 'PROVED');
    assert_1.strict.equal(allProved, true);
});
runTest('checker rejects use of UNVERIFIED claim as derivation input', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
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
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
});
runTest('checker strict mode rejects UNVERIFIED assertions', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem UnverifiedStrict() {
  assert(p)
} ↔

proof UnverifiedStrict() {
  assert(p)
}
`));
    const report = (0, checker_1.checkFile)(ast, { strict: true });
    assert_1.strict.equal(report.valid, false);
    const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
    assert_1.strict.match(messages, /Strict mode rejects/i);
});
// ── Phase 3: Scope errors ─────────────────────────────────────────────────────
runTest('checker rejects set-theoretic conclusion with variable not in scope', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ScopeError() {
  assert(z ∈ C)
} ↔

proof ScopeError() {
  conclude(z ∈ C)
}
`));
    // z and C are never introduced via given/assume/setVar
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
    const messages = report.reports.flatMap(r => r.diagnostics.map(d => d.message)).join('\n');
    assert_1.strict.match(messages, /scope error/i);
});
runTest('React backend generates a webapp scaffold', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Hello() {
  assert(true)
}
`));
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'futurlang-web-'));
    (0, transpiler_1.createReactApp)(ast, outDir);
    assert_1.strict.equal(fs.existsSync(path.join(outDir, 'package.json')), true);
    assert_1.strict.equal(fs.existsSync(path.join(outDir, 'src', 'App.tsx')), true);
    assert_1.strict.equal(fs.existsSync(path.join(outDir, 'src', 'styles.css')), true);
});
runTest('default fl command auto-runs checker for proof-shaped files', () => {
    const output = (0, child_process_1.execFileSync)('node', ['fl.js', 'examples/demo/identity.fl'], {
        cwd: process.cwd(),
        encoding: 'utf8',
    });
    assert_1.strict.match(output, /theorem-prover mode/i);
    assert_1.strict.match(output, /Checking identity\.fl/);
    assert_1.strict.match(output, /final: p → p/);
});
runTest('default fl command presents standalone theorem files as declarations', () => {
    const output = (0, child_process_1.execFileSync)('node', ['fl.js', 'test/connectives.fl'], {
        cwd: process.cwd(),
        encoding: 'utf8',
    });
    assert_1.strict.match(output, /Declaration-only proof program/);
    assert_1.strict.match(output, /Theorems: 9/);
    assert_1.strict.doesNotMatch(output, /Score: 0\/100/);
    assert_1.strict.doesNotMatch(output, /have no proof/);
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
        (0, child_process_1.execFileSync)('node', ['fl.js', 'check', '--strict', file], {
            cwd: process.cwd(),
            encoding: 'utf8',
            stdio: ['ignore', 'pipe', 'pipe'],
        });
        assert_1.strict.fail('Expected strict CLI invocation to fail');
    }
    catch (error) {
        stderr = String(error.stdout ?? '') + String(error.stderr ?? '');
    }
    assert_1.strict.match(stderr, /Strict mode rejects/);
});
console.log('All unit tests passed.');
