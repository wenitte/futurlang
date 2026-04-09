import { strict as assert } from 'assert';
import * as fs from 'fs';
import * as path from 'path';
import { checkFile } from '../checker/checker';
import { parseLinesToAST } from '../parser/parser';
import { lexFL } from '../parser/lexer';
import { parseExpr } from '../parser/expr';
import { exprToProp } from '../checker/propositions';
import { WenittainCategory, KernelError } from '../kernel/category';
import { applyRevelation, RevelationError } from '../kernel/revelation';
import { evaluateExists, evaluateForAll, evaluateNotForAllNot } from '../kernel/quantifiers';
import { and, implies, neg, or, WenittainValue } from '../kernel/values';

function runTest(name: string, fn: () => void) {
  try {
    fn();
    console.log(`✓ ${name}`);
  } catch (error) {
    console.error(`✗ ${name}`);
    throw error;
  }
}

function parseProgram(source: string) {
  return parseLinesToAST(lexFL(source));
}

function assertTruthTable(
  label: string,
  op: (left: WenittainValue, right: WenittainValue) => WenittainValue,
  expected: Record<WenittainValue, Record<WenittainValue, WenittainValue>>,
) {
  runTest(label, () => {
    const values: WenittainValue[] = ['0', '1', 'ω'];
    for (const left of values) {
      for (const right of values) {
        assert.equal(op(left, right), expected[left][right], `${label}(${left}, ${right})`);
      }
    }
  });
}

runTest('parseExpr preserves FuturLang connective syntax', () => {
  const expr = parseExpr('(x ∈ A) ⇒ (x ∈ B)');
  assert.equal(exprToProp(expr), 'x ∈ A → x ∈ B');
});

runTest('Wenittain negation matches WL-WL-001', () => {
  assert.equal(neg('1'), '0');
  assert.equal(neg('0'), '1');
  assert.equal(neg('ω'), 'ω');
});

assertTruthTable('Wenittain conjunction matches WL-WL-001', and, {
  '0': { '0': '0', '1': '0', 'ω': '0' },
  '1': { '0': '0', '1': '1', 'ω': 'ω' },
  'ω': { '0': '0', '1': 'ω', 'ω': 'ω' },
});

assertTruthTable('Wenittain disjunction matches WL-WL-001', or, {
  '0': { '0': '0', '1': '1', 'ω': 'ω' },
  '1': { '0': '1', '1': '1', 'ω': '1' },
  'ω': { '0': 'ω', '1': '1', 'ω': 'ω' },
});

assertTruthTable('Wenittain implication matches WL-WL-001', implies, {
  '0': { '0': '1', '1': '1', 'ω': '1' },
  '1': { '0': '0', '1': '1', 'ω': 'ω' },
  'ω': { '0': 'ω', '1': '1', 'ω': 'ω' },
});

runTest('quantifier asymmetry keeps exists independent from not-forall-not', () => {
  const frame = { denotingValues: ['0'] as WenittainValue[], unresolvedCount: 1 };
  assert.equal(evaluateNotForAllNot(frame), '0');
  assert.equal(evaluateExists(frame), 'ω');
  assert.equal(evaluateForAll({ denotingValues: ['1'], unresolvedCount: 1 }), 'ω');
});

runTest('ω-Barrier rejects pending morphisms in classical composition', () => {
  const category = new WenittainCategory();
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
  assert.throws(
    () => category.compose(pending, arrow, 'q', 'IMPLIES_ELIM'),
    (error: unknown) => error instanceof KernelError && /ω-Barrier/.test(error.message),
  );
});

runTest('Ra rejects partial witnesses and resolves pending morphisms with total witnesses', () => {
  const category = new WenittainCategory();
  const pending = category.createMorphism({
    proposition: 'm',
    domain: '⊤',
    codomain: 'obj:m',
    tau: 'ω',
    rule: 'STRUCTURAL',
    unresolvedTerms: ['u', 'v'],
  });
  assert.throws(
    () => applyRevelation(category, pending, new Map([['u', '1']])),
    (error: unknown) => error instanceof RevelationError && /total witness/.test(error.message),
  );
  const resolved = applyRevelation(category, pending, new Map([
    ['u', '1'],
    ['v', '1'],
  ]));
  assert.equal(resolved.tau, '1');
  assert.equal(resolved.pending, false);
});

runTest('checker returns PROVED for classical implication derivations', () => {
  const report = checkFile(parseProgram(`
theorem Identity() {
  assert(p -> p)
} ↔

proof Identity() {
  assume(p) →
  conclude(p)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].state, 'PROVED');
});

runTest('checker returns PENDING for structurally present but unsupported derivations', () => {
  const report = checkFile(parseProgram(`
theorem PendingWitness() {
  assert(∃ x ∈ A, P(x))
} ↔

proof PendingWitness() {
  assert(∃ x ∈ A, P(x))
}
`));
  assert.equal(report.state, 'PENDING');
  assert.equal(report.reports[0].state, 'PENDING');
});

runTest('checker returns FAILED for invalid proof paths', () => {
  const report = checkFile(parseProgram(`
theorem BadIdentity() {
  assert(p -> p)
} ↔

proof BadIdentity() {
  assume(p) →
  conclude(q)
}
`));
  assert.equal(report.state, 'FAILED');
  assert.equal(report.reports[0].state, 'FAILED');
});

runTest('checker imports proved lemmas as morphisms', () => {
  const report = checkFile(parseProgram(`
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
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[1].state, 'PROVED');
});

runTest('demo examples all reduce to PROVED with no pending morphisms', () => {
  const demoDir = path.resolve(__dirname, '../../examples/demo');
  const files = fs.readdirSync(demoDir).filter(file => file.endsWith('.fl'));
  for (const file of files) {
    const source = fs.readFileSync(path.join(demoDir, file), 'utf8');
    const report = checkFile(parseProgram(source));
    assert.equal(report.state, 'PROVED', file);
    for (const theoremReport of report.reports) {
      assert.equal(theoremReport.state, 'PROVED', `${file}:${theoremReport.name}`);
      assert.equal(theoremReport.pendingCount, 0, `${file}:${theoremReport.name}`);
    }
  }
});
