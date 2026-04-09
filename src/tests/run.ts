import { strict as assert } from 'assert';
import * as fs from 'fs';
import * as path from 'path';
import { checkFile } from '../checker/checker';
import { parseLinesToAST } from '../parser/parser';
import { lexFL } from '../parser/lexer';
import { parseExpr } from '../parser/expr';
import { exprToProp, parseCategoricalEqualityCanonical, parseMorphismDeclarationCanonical, parseMorphismExprCanonical } from '../checker/propositions';
import { WenittainCategory, KernelError } from '../kernel/category';
import { applyRevelation, RevelationError } from '../kernel/revelation';
import { evaluateExists, evaluateForAll, evaluateNotForAllNot } from '../kernel/quantifiers';
import { and, implies, neg, or, WenittainValue } from '../kernel/values';
import { CategoryDiagramKernel, CategoryDiagramError } from '../kernel/category-diagrams';

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

runTest('category proposition parsing recognizes morphisms and composites', () => {
  const morphism = parseMorphismDeclarationCanonical('f : A → B');
  assert.ok(morphism);
  assert.equal(morphism!.label, 'f');
  assert.equal(morphism!.domain, 'A');
  assert.equal(morphism!.codomain, 'B');

  const equality = parseCategoricalEqualityCanonical('g ∘ f = h');
  assert.ok(equality);
  assert.equal(parseMorphismExprCanonical('g ∘ f')?.kind, 'compose');
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

runTest('category kernel validates and rejects composition correctly', () => {
  const diagrams = new CategoryDiagramKernel();
  diagrams.registerClaim('f : A → B');
  diagrams.registerClaim('g : B → C');
  const composite = diagrams.resolveMorphismExpr(parseMorphismExprCanonical('g ∘ f')!);
  assert.equal(diagrams.objectById(composite.domain).label, 'A');
  assert.equal(diagrams.objectById(composite.codomain).label, 'C');

  diagrams.registerClaim('h : D → E');
  assert.throws(
    () => diagrams.resolveMorphismExpr(parseMorphismExprCanonical('h ∘ f')!),
    (error: unknown) => error instanceof CategoryDiagramError && /do not compose/.test(error.message),
  );
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

runTest('checker proves categorical identity laws', () => {
  const report = checkFile(parseProgram(`
theorem IdentityLaw() {
  given(f : A → B) →
  assert(f ∘ id_A = f)
} ↔

proof IdentityLaw() {
  conclude(f ∘ id_A = f)
}
`));
  assert.equal(report.state, 'PROVED');
});

runTest('checker rejects invalid categorical composition', () => {
  const report = checkFile(parseProgram(`
theorem BadCompose() {
  given(f : A → B) →
  given(g : C → D) →
  assert(g ∘ f = h)
} ↔

proof BadCompose() {
  conclude(g ∘ f = h)
}
`));
  assert.equal(report.state, 'FAILED');
  assert.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /do not compose/);
});

runTest('checker proves explicit isomorphisms', () => {
  const report = checkFile(parseProgram(`
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
  assert.equal(report.state, 'PROVED');
});

runTest('checker proves product mediators and pullbacks', () => {
  const productReport = checkFile(parseProgram(`
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
  assert.equal(productReport.state, 'PROVED');

  const pullbackReport = checkFile(parseProgram(`
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
  assert.equal(pullbackReport.state, 'PROVED');
});

runTest('checker proves functor composition preservation', () => {
  const report = checkFile(parseProgram(`
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
  assert.equal(report.state, 'PROVED');
});

runTest('demo examples all reduce to PROVED with no pending morphisms', () => {
  const demoDir = path.resolve(__dirname, '../../examples/demo');
  const files = collectDemoFiles(demoDir);
  for (const file of files) {
    const source = fs.readFileSync(file, 'utf8');
    const report = checkFile(parseProgram(source));
    const label = path.relative(demoDir, file);
    assert.equal(report.state, 'PROVED', label);
    for (const theoremReport of report.reports) {
      assert.equal(theoremReport.state, 'PROVED', `${label}:${theoremReport.name}`);
      assert.equal(theoremReport.pendingCount, 0, `${label}:${theoremReport.name}`);
    }
  }
});

function collectDemoFiles(dir: string): string[] {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  const files: string[] = [];
  for (const entry of entries) {
    if (entry.name.startsWith('.')) continue;
    const absolute = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files.push(...collectDemoFiles(absolute));
    } else if (entry.name.endsWith('.fl')) {
      files.push(absolute);
    }
  }
  return files.sort();
}
