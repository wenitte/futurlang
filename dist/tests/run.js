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
runTest('demo examples all reduce to PROVED with no pending morphisms', () => {
    const demoDir = path.resolve(__dirname, '../../examples/demo');
    const files = fs.readdirSync(demoDir).filter(file => file.endsWith('.fl'));
    for (const file of files) {
        const source = fs.readFileSync(path.join(demoDir, file), 'utf8');
        const report = (0, checker_1.checkFile)(parseProgram(source));
        assert_1.strict.equal(report.state, 'PROVED', file);
        for (const theoremReport of report.reports) {
            assert_1.strict.equal(theoremReport.state, 'PROVED', `${file}:${theoremReport.name}`);
            assert_1.strict.equal(theoremReport.pendingCount, 0, `${file}:${theoremReport.name}`);
        }
    }
});
