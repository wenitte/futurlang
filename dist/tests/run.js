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
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const checker_1 = require("../checker/checker");
const parser_1 = require("../parser/parser");
const lexer_1 = require("../parser/lexer");
const expr_1 = require("../parser/expr");
const propositions_1 = require("../checker/propositions");
const category_1 = require("../kernel/category");
const revelation_1 = require("../kernel/revelation");
const quantifiers_1 = require("../kernel/quantifiers");
const values_1 = require("../kernel/values");
const category_diagrams_1 = require("../kernel/category-diagrams");
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
function parseProgram(source) {
    return (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source));
}
function assertTruthTable(label, op, expected) {
    runTest(label, () => {
        const values = ['0', '1', 'ω'];
        for (const left of values) {
            for (const right of values) {
                assert_1.strict.equal(op(left, right), expected[left][right], `${label}(${left}, ${right})`);
            }
        }
    });
}
runTest('parseExpr preserves FuturLang connective syntax', () => {
    const expr = (0, expr_1.parseExpr)('(x ∈ A) ⇒ (x ∈ B)');
    assert_1.strict.equal((0, propositions_1.exprToProp)(expr), 'x ∈ A → x ∈ B');
});
runTest('parseExpr recognizes fold and sigma sugar', () => {
    const fold = (0, expr_1.parseExpr)('fold(xs, 0, +)');
    assert_1.strict.equal((0, propositions_1.exprToProp)(fold), 'fold(xs, 0, +)');
    const sigma = (0, expr_1.parseExpr)('Σ(i, 0, n)');
    assert_1.strict.equal((0, propositions_1.exprToProp)(sigma), 'fold([0..n], 0, +)');
});
runTest('parser desugars fn declarations into theorem/proof pairs before checking', () => {
    const ast = parseProgram(`
fn double(n ∈ Nat) -> Nat {
  conclude(n + n)
}
`);
    assert_1.strict.equal(ast.length, 2);
    assert_1.strict.equal(ast[0].type, 'Theorem');
    assert_1.strict.equal(ast[1].type, 'Proof');
    if (ast[0].type !== 'Theorem' || ast[1].type !== 'Proof') {
        throw new Error('fn did not desugar to theorem/proof');
    }
    assert_1.strict.equal(ast[0].name, 'double');
    assert_1.strict.equal(ast[1].name, 'double');
    assert_1.strict.equal(ast[0].body[0].type, 'Given');
    assert_1.strict.equal(ast[0].body[ast[0].body.length - 1].type, 'Assert');
    assert_1.strict.equal(ast[1].body[0].type, 'Assume');
    assert_1.strict.equal(ast[1].body[1].type, 'Conclude');
});
runTest('parser captures struct field declarations as typed fields', () => {
    const ast = parseProgram(`
struct Point {
  x ∈ Real,
  y ∈ Real
}
`);
    assert_1.strict.equal(ast.length, 1);
    assert_1.strict.equal(ast[0].type, 'Struct');
    if (ast[0].type !== 'Struct') {
        throw new Error('struct did not parse');
    }
    assert_1.strict.equal(ast[0].name, 'Point');
    assert_1.strict.deepEqual(ast[0].fields, [
        { name: 'x', type: 'ℝ' },
        { name: 'y', type: 'ℝ' },
    ]);
});
runTest('parser captures type variants and match cases', () => {
    const ast = parseProgram(`
type Shape =
  | Circle(r ∈ Real)
  | Rectangle(w ∈ Real, h ∈ Real)
} →

theorem ShapeCase() {
  given(s ∈ Shape) →
  assert(s ∈ Shape)
} ↔

proof ShapeCase() {
  match s {
    case Circle(r) => conclude(s ∈ Shape)
    case Rectangle(w, h) => conclude(s ∈ Shape)
  }
}
`);
    assert_1.strict.equal(ast[0].type, 'TypeDecl');
    if (ast[0].type !== 'TypeDecl') {
        throw new Error('type did not parse');
    }
    assert_1.strict.equal(ast[0].variants.length, 2);
    assert_1.strict.equal(ast[2].type, 'Proof');
    if (ast[2].type !== 'Proof') {
        throw new Error('proof missing');
    }
    assert_1.strict.equal(ast[2].body[0].type, 'Match');
});
runTest('category proposition parsing recognizes morphisms and composites', () => {
    const morphism = (0, propositions_1.parseMorphismDeclarationCanonical)('f : A → B');
    assert_1.strict.ok(morphism);
    assert_1.strict.equal(morphism.label, 'f');
    assert_1.strict.equal(morphism.domain, 'A');
    assert_1.strict.equal(morphism.codomain, 'B');
    const equality = (0, propositions_1.parseCategoricalEqualityCanonical)('g ∘ f = h');
    assert_1.strict.ok(equality);
    assert_1.strict.equal((0, propositions_1.parseMorphismExprCanonical)('g ∘ f')?.kind, 'compose');
});
runTest('Wenittain negation matches WL-WL-001', () => {
    assert_1.strict.equal((0, values_1.neg)('1'), '0');
    assert_1.strict.equal((0, values_1.neg)('0'), '1');
    assert_1.strict.equal((0, values_1.neg)('ω'), 'ω');
});
assertTruthTable('Wenittain conjunction matches WL-WL-001', values_1.and, {
    '0': { '0': '0', '1': '0', 'ω': '0' },
    '1': { '0': '0', '1': '1', 'ω': 'ω' },
    'ω': { '0': '0', '1': 'ω', 'ω': 'ω' },
});
assertTruthTable('Wenittain disjunction matches WL-WL-001', values_1.or, {
    '0': { '0': '0', '1': '1', 'ω': 'ω' },
    '1': { '0': '1', '1': '1', 'ω': '1' },
    'ω': { '0': 'ω', '1': '1', 'ω': 'ω' },
});
assertTruthTable('Wenittain implication matches WL-WL-001', values_1.implies, {
    '0': { '0': '1', '1': '1', 'ω': '1' },
    '1': { '0': '0', '1': '1', 'ω': 'ω' },
    'ω': { '0': 'ω', '1': '1', 'ω': 'ω' },
});
runTest('quantifier asymmetry keeps exists independent from not-forall-not', () => {
    const frame = { denotingValues: ['0'], unresolvedCount: 1 };
    assert_1.strict.equal((0, quantifiers_1.evaluateNotForAllNot)(frame), '0');
    assert_1.strict.equal((0, quantifiers_1.evaluateExists)(frame), 'ω');
    assert_1.strict.equal((0, quantifiers_1.evaluateForAll)({ denotingValues: ['1'], unresolvedCount: 1 }), 'ω');
});
runTest('ω-Barrier rejects pending morphisms in classical composition', () => {
    const category = new category_1.WenittainCategory();
    const top = category.createObject('⊤');
    const p = category.createObject('p');
    const q = category.createObject('q');
    const pending = category.createMorphism({
        proposition: 'p',
        domain: top.id,
        codomain: p.id,
        tau: 'ω',
        rule: 'STRUCTURAL',
        unresolvedTerms: ['u'],
    });
    const arrow = category.createMorphism({
        proposition: 'p → q',
        domain: p.id,
        codomain: q.id,
        tau: '1',
        rule: 'IMPLIES_ELIM',
    });
    assert_1.strict.throws(() => category.compose(pending, arrow, 'q', 'IMPLIES_ELIM'), (error) => error instanceof category_1.KernelError && /ω-Barrier/.test(error.message));
});
runTest('Ra rejects partial witnesses and resolves pending morphisms with total witnesses', () => {
    const category = new category_1.WenittainCategory();
    const pending = category.createMorphism({
        proposition: 'm',
        domain: '⊤',
        codomain: 'obj:m',
        tau: 'ω',
        rule: 'STRUCTURAL',
        unresolvedTerms: ['u', 'v'],
    });
    assert_1.strict.throws(() => (0, revelation_1.applyRevelation)(category, pending, new Map([['u', '1']])), (error) => error instanceof revelation_1.RevelationError && /total witness/.test(error.message));
    const resolved = (0, revelation_1.applyRevelation)(category, pending, new Map([
        ['u', '1'],
        ['v', '1'],
    ]));
    assert_1.strict.equal(resolved.tau, '1');
    assert_1.strict.equal(resolved.pending, false);
});
runTest('category kernel validates and rejects composition correctly', () => {
    const diagrams = new category_diagrams_1.CategoryDiagramKernel();
    diagrams.registerClaim('f : A → B');
    diagrams.registerClaim('g : B → C');
    const composite = diagrams.resolveMorphismExpr((0, propositions_1.parseMorphismExprCanonical)('g ∘ f'));
    assert_1.strict.equal(diagrams.objectById(composite.domain).label, 'A');
    assert_1.strict.equal(diagrams.objectById(composite.codomain).label, 'C');
    diagrams.registerClaim('h : D → E');
    assert_1.strict.throws(() => diagrams.resolveMorphismExpr((0, propositions_1.parseMorphismExprCanonical)('h ∘ f')), (error) => error instanceof category_diagrams_1.CategoryDiagramError && /do not compose/.test(error.message));
});
runTest('checker returns PROVED for classical implication derivations', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
theorem Identity() {
  assert(p -> p)
} ↔

proof Identity() {
  assume(p) →
  conclude(p)
}
`));
    assert_1.strict.equal(report.state, 'PROVED');
    assert_1.strict.equal(report.reports[0].state, 'PROVED');
});
runTest('checker returns PENDING for structurally present but unsupported derivations', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
theorem PendingWitness() {
  assert(∃ x ∈ A, P(x))
} ↔

proof PendingWitness() {
  assert(∃ x ∈ A, P(x))
}
`));
    assert_1.strict.equal(report.state, 'PENDING');
    assert_1.strict.equal(report.reports[0].state, 'PENDING');
});
runTest('checker returns FAILED for invalid proof paths', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
theorem BadIdentity() {
  assert(p -> p)
} ↔

proof BadIdentity() {
  assume(p) →
  conclude(q)
}
`));
    assert_1.strict.equal(report.state, 'FAILED');
    assert_1.strict.equal(report.reports[0].state, 'FAILED');
});
runTest('checker imports proved lemmas as morphisms', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
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
    assert_1.strict.equal(report.state, 'PROVED');
    assert_1.strict.equal(report.reports[1].state, 'PROVED');
});
runTest('checker proves categorical identity laws', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
theorem IdentityLaw() {
  given(f : A → B) →
  assert(f ∘ id_A = f)
} ↔

proof IdentityLaw() {
  conclude(f ∘ id_A = f)
}
`));
    assert_1.strict.equal(report.state, 'PROVED');
});
runTest('checker rejects invalid categorical composition', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
theorem BadCompose() {
  given(f : A → B) →
  given(g : C → D) →
  assert(g ∘ f = h)
} ↔

proof BadCompose() {
  conclude(g ∘ f = h)
}
`));
    assert_1.strict.equal(report.state, 'FAILED');
    assert_1.strict.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /do not compose/);
});
runTest('checker proves explicit isomorphisms', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
theorem IsoWitness() {
  given(f : A → B) →
  given(g : B → A) →
  given(g ∘ f = id_A) →
  given(f ∘ g = id_B) →
  assert(Iso(f))
} ↔

proof IsoWitness() {
  conclude(Iso(f))
}
`));
    assert_1.strict.equal(report.state, 'PROVED');
});
runTest('checker proves product mediators and pullbacks', () => {
    const productReport = (0, checker_1.checkFile)(parseProgram(`
theorem ProductWitness() {
  given(pi1 : P → A) →
  given(pi2 : P → B) →
  given(f : X → A) →
  given(g : X → B) →
  given(m : X → P) →
  given(pi1 ∘ m = f) →
  given(pi2 ∘ m = g) →
  assert(ProductMediator(m, f, g, pi1, pi2))
} ↔

proof ProductWitness() {
  conclude(ProductMediator(m, f, g, pi1, pi2))
}
`));
    assert_1.strict.equal(productReport.state, 'PROVED');
    const pullbackReport = (0, checker_1.checkFile)(parseProgram(`
theorem PullbackSquare() {
  given(p1 : P → X) →
  given(p2 : P → Y) →
  given(f : X → Z) →
  given(g : Y → Z) →
  given(f ∘ p1 = g ∘ p2) →
  assert(Pullback(P, p1, p2, f, g))
} ↔

proof PullbackSquare() {
  conclude(Pullback(P, p1, p2, f, g))
}
`));
    assert_1.strict.equal(pullbackReport.state, 'PROVED');
});
runTest('checker proves functor composition preservation', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
theorem FunctorCompose() {
  given(Category(C)) →
  given(Category(D)) →
  given(Morphism(C, f, A, B)) →
  given(Morphism(C, g, B, C0)) →
  given(Functor(F, C, D)) →
  assert(F(g ∘ f) = F(g) ∘ F(f))
} ↔

proof FunctorCompose() {
  conclude(F(g ∘ f) = F(g) ∘ F(f))
}
`));
    assert_1.strict.equal(report.state, 'PROVED');
});
runTest('checker proves fold as a trusted kernel primitive', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
theorem FoldSum() {
  assert(fold([0..n], 0, +))
} ↔

proof FoldSum() {
  conclude(fold([0..n], 0, +))
}
`));
    assert_1.strict.equal(report.state, 'PROVED');
    assert_1.strict.equal(report.reports[0].proofSteps[0].rule, 'FOLD_ELIM');
});
runTest('checker desugars induction onto the fold kernel path', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
theorem InductionSum() {
  assert(SumTo(n))
} ↔

proof InductionSum() {
  induction(n) {
    base: SumTo(0)
    step: given(SumTo(k)) → conclude(SumTo(k+1))
  }
}
`));
    assert_1.strict.equal(report.state, 'PROVED');
    assert_1.strict.equal(report.reports[0].proofSteps[0].rule, 'FOLD_ELIM');
});
runTest('checker projects struct fields from struct membership', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
struct Point {
  x ∈ Real,
  y ∈ Real
} →

theorem PointProjection() {
  given(p ∈ Point) →
  assert(p.x ∈ Real)
} ↔

proof PointProjection() {
  conclude(p.x ∈ Real)
}
`));
    assert_1.strict.equal(report.state, 'PROVED');
    assert_1.strict.equal(report.reports[0].proofSteps[0].rule, 'STRUCT_ELIM');
});
runTest('checker introduces struct membership from field memberships', () => {
    const report = (0, checker_1.checkFile)(parseProgram(`
struct Point {
  x ∈ Real,
  y ∈ Real
} →

theorem PointIntro() {
  given(p.x ∈ Real) →
  given(p.y ∈ Real) →
  assert(p ∈ Point)
} ↔

proof PointIntro() {
  conclude(p ∈ Point)
}
`));
    assert_1.strict.equal(report.state, 'PROVED');
    assert_1.strict.equal(report.reports[0].proofSteps[0].rule, 'STRUCT_INTRO');
});
runTest('checker validates exhaustive match and rejects incomplete coverage', () => {
    const proved = (0, checker_1.checkFile)(parseProgram(`
type Shape =
  | Circle(r ∈ Real)
  | Rectangle(w ∈ Real, h ∈ Real)
} →

theorem ShapeCovered() {
  given(s ∈ Shape) →
  assert(s ∈ Shape)
} ↔

proof ShapeCovered() {
  match s {
    case Circle(r) => conclude(s ∈ Shape)
    case Rectangle(w, h) => conclude(s ∈ Shape)
  }
}
`));
    assert_1.strict.equal(proved.state, 'PROVED');
    assert_1.strict.equal(proved.reports[0].proofSteps[0].rule, 'MATCH_EXHAUSTIVE');
    const failed = (0, checker_1.checkFile)(parseProgram(`
type Shape =
  | Circle(r ∈ Real)
  | Rectangle(w ∈ Real, h ∈ Real)
} →

theorem ShapeMiss() {
  given(s ∈ Shape) →
  assert(s ∈ Shape)
} ↔

proof ShapeMiss() {
  match s {
    case Circle(r) => conclude(s ∈ Shape)
  }
}
`));
    assert_1.strict.equal(failed.state, 'FAILED');
});
runTest('demo examples all reduce to PROVED with no pending morphisms', () => {
    const demoDir = path.resolve(__dirname, '../../examples/demo');
    const files = collectDemoFiles(demoDir);
    const expectedStates = new Map([
        ['match-exhaustive-fail.fl', 'FAILED'],
    ]);
    for (const file of files) {
        const source = fs.readFileSync(file, 'utf8');
        const report = (0, checker_1.checkFile)(parseProgram(source));
        const label = path.relative(demoDir, file);
        const expected = expectedStates.get(label) ?? 'PROVED';
        assert_1.strict.equal(report.state, expected, label);
        if (expected !== 'PROVED')
            continue;
        for (const theoremReport of report.reports) {
            assert_1.strict.equal(theoremReport.state, 'PROVED', `${label}:${theoremReport.name}`);
            assert_1.strict.equal(theoremReport.pendingCount, 0, `${label}:${theoremReport.name}`);
        }
    }
});
function collectDemoFiles(dir) {
    const entries = fs.readdirSync(dir, { withFileTypes: true });
    const files = [];
    for (const entry of entries) {
        if (entry.name.startsWith('.'))
            continue;
        const absolute = path.join(dir, entry.name);
        if (entry.isDirectory()) {
            files.push(...collectDemoFiles(absolute));
        }
        else if (entry.name.endsWith('.fl')) {
            files.push(absolute);
        }
    }
    return files.sort();
}
