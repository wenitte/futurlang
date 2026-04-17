import { strict as assert } from 'assert';
import * as fs from 'fs';
import * as path from 'path';
import * as vm from 'vm';
import { spawnSync } from 'child_process';
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
import { generateJSFromAST } from '../codegen';
import { runtimePreamble } from '../codegen/runtime';
import { parseFLFile } from '../parser/formal';

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

function parseExecutableProgram(source: string) {
  return parseLinesToAST(lexFL(source), { desugarFns: false });
}

function runExecutable(source: string) {
  const ast = parseExecutableProgram(source);
  const js = generateJSFromAST(ast, runtimePreamble);
  const context: Record<string, unknown> = {
    console: { log: () => {} },
    globalThis: {} as Record<string, unknown>,
    require,
    Buffer,
    URL,
  };
  context.globalThis = context;
  vm.runInNewContext(js, context);
  return context;
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

runTest('parseExpr recognizes fold and sigma sugar', () => {
  const fold = parseExpr('fold(xs, 0, +)');
  assert.equal(exprToProp(fold), 'fold(xs, 0, +)');
  const sigma = parseExpr('Σ(i, 0, n)');
  assert.equal(exprToProp(sigma), 'fold([0..n], 0, +)');
});

runTest('parseExpr recognizes executable if, let-in, and lambda syntax', () => {
  assert.equal(
    exprToProp(parseExpr('if true then 1 else 0')),
    'if true then 1 else 0',
  );
  assert.equal(
    exprToProp(parseExpr('let x = 1 in x + 1')),
    'let x = 1 in x + 1',
  );
  assert.equal(
    exprToProp(parseExpr('fn(x: Nat) => x + 1')),
    'fn(x: Nat) => x + 1',
  );
});

runTest('parser desugars fn declarations into theorem/proof pairs before checking', () => {
  const ast = parseProgram(`
fn double(n ∈ Nat) -> Nat {
  conclude(n + n)
}
`);
  assert.equal(ast.length, 2);
  assert.equal(ast[0].type, 'Theorem');
  assert.equal(ast[1].type, 'Proof');
  if (ast[0].type !== 'Theorem' || ast[1].type !== 'Proof') {
    throw new Error('fn did not desugar to theorem/proof');
  }
  assert.equal(ast[0].name, 'double');
  assert.equal(ast[1].name, 'double');
  assert.equal(ast[0].body[0].type, 'Given');
  assert.equal(ast[0].body[ast[0].body.length - 1].type, 'Assert');
  assert.equal(ast[1].body[0].type, 'Assume');
  assert.equal(ast[1].body[1].type, 'Conclude');
});

runTest('parser captures struct field declarations as typed fields', () => {
  const ast = parseProgram(`
struct Point {
  x ∈ Real,
  y ∈ Real
}
`);
  assert.equal(ast.length, 1);
  assert.equal(ast[0].type, 'Struct');
  if (ast[0].type !== 'Struct') {
    throw new Error('struct did not parse');
  }
  assert.equal(ast[0].name, 'Point');
  assert.deepEqual(ast[0].fields, [
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
  assume(s ∈ Shape) →
  declareToProve(s ∈ Shape)
} ↔

proof ShapeCase() {
  match s {
    case Circle(r) => conclude(s ∈ Shape)
    case Rectangle(w, h) => conclude(s ∈ Shape)
  }
}
`);
  assert.equal(ast[0].type, 'TypeDecl');
  if (ast[0].type !== 'TypeDecl') {
    throw new Error('type did not parse');
  }
  assert.equal(ast[0].variants.length, 2);
  assert.equal(ast[2].type, 'Proof');
  if (ast[2].type !== 'Proof') {
    throw new Error('proof missing');
  }
  assert.equal(ast[2].body[0].type, 'Match');
});

runTest('parser captures kernel list patterns and multi-line case bodies', () => {
  const ast = parseProgram(`
fn length(xs ∈ List(Nat)) -> Nat {
  match xs {
    case [] =>
      conclude(0)
    case [x, ...rest] =>
      match x {
        case _ => conclude(1 + length(rest))
      }
  }
}
`);
  assert.equal(ast.length, 2);
  assert.equal(ast[1].type, 'Proof');
  if (ast[1].type !== 'Proof') {
    throw new Error('proof missing');
  }
  assert.deepEqual(ast[1].fnMeta, {
    params: [{ name: 'xs', type: 'List(ℕ)' }],
    returnType: 'ℕ',
  });
  const topMatch = ast[1].body[0];
  assert.equal(topMatch.type, 'Match');
  if (topMatch.type !== 'Match') {
    throw new Error('top-level match missing');
  }
  assert.equal(topMatch.cases.length, 2);
  assert.deepEqual(topMatch.cases[0].pattern, { kind: 'list_nil' });
  assert.deepEqual(topMatch.cases[1].pattern, { kind: 'list_cons', head: 'x', tail: 'rest' });
  assert.equal(topMatch.cases[1].body[0].type, 'Match');
});

runTest('server-style executable files are not misclassified as proof programs', () => {
  const ast = parseExecutableProgram(`
fn home(req ∈ Request) -> Response {
  conclude(text("home"))
} →

let app = router([
  route("GET", "/", home)
]) →

let server = serve(3000, app)
`);
  assert.equal(ast[0].type, 'FnDecl');
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
  declareToProve(p → p)
} ↔

proof Identity() {
  assume(p) →
  conclude(p)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].state, 'PROVED');
});

runTest('checker returns FAILED for unresolvable existential without witness', () => {
  const report = checkFile(parseProgram(`
theorem PendingWitness() {
  declareToProve(∃ x ∈ A, P(x))
} ↔

proof PendingWitness() {
  prove(∃ x ∈ A, P(x))
}
`));
  assert.equal(report.state, 'FAILED');
  assert.equal(report.reports[0].state, 'FAILED');
});

runTest('checker returns FAILED for invalid proof paths', () => {
  const report = checkFile(parseProgram(`
theorem BadIdentity() {
  declareToProve(p → p)
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
  assume(p → q) →
  declareToProve(q)
} ↔

proof ForwardStep() {
  assume(p) →
  conclude(q)
} →

theorem UsesForwardStep() {
  assume(p → q) →
  declareToProve(q)
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
  assume(f : A → B) →
  declareToProve(f ∘ id_A = f)
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
  assume(f : A → B ∧ g : C → D) →
  declareToProve(g ∘ f = h)
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
  assume(f : A → B ∧ g : B → A ∧ g ∘ f = id_A ∧ f ∘ g = id_B) →
  declareToProve(Iso(f))
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
  assume(pi1 : P → A ∧ pi2 : P → B ∧ f : X → A ∧ g : X → B ∧ m : X → P ∧ pi1 ∘ m = f ∧ pi2 ∘ m = g) →
  declareToProve(ProductMediator(m, f, g, pi1, pi2))
} ↔

proof ProductWitness() {
  conclude(ProductMediator(m, f, g, pi1, pi2))
}
`));
  assert.equal(productReport.state, 'PROVED');

  const pullbackReport = checkFile(parseProgram(`
theorem PullbackSquare() {
  assume(p1 : P → X ∧ p2 : P → Y ∧ f : X → Z ∧ g : Y → Z ∧ f ∘ p1 = g ∘ p2) →
  declareToProve(Pullback(P, p1, p2, f, g))
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
  assume(Category(C) ∧ Category(D) ∧ Morphism(C, f, A, B) ∧ Morphism(C, g, B, C0) ∧ Functor(F, C, D)) →
  declareToProve(F(g ∘ f) = F(g) ∘ F(f))
} ↔

proof FunctorCompose() {
  conclude(F(g ∘ f) = F(g) ∘ F(f))
}
`));
  assert.equal(report.state, 'PROVED');
});

runTest('checker proves fold as a trusted kernel primitive', () => {
  const report = checkFile(parseProgram(`
theorem FoldSum() {
  declareToProve(fold([0..n], 0, +))
} ↔

proof FoldSum() {
  conclude(fold([0..n], 0, +))
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].proofSteps[0].rule, 'FOLD_ELIM');
});

runTest('checker desugars induction onto the fold kernel path', () => {
  const report = checkFile(parseProgram(`
theorem InductionSum() {
  declareToProve(SumTo(n))
} ↔

proof InductionSum() {
  induction(n) {
    base: SumTo(0)
    step: assume(SumTo(k)) → conclude(SumTo(k+1))
  }
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].proofSteps[0].rule, 'FOLD_ELIM');
});

runTest('checker projects struct fields from struct membership', () => {
  const report = checkFile(parseProgram(`
struct Point {
  x ∈ Real,
  y ∈ Real
} →

theorem PointProjection() {
  assume(p ∈ Point) →
  declareToProve(p.x ∈ Real)
} ↔

proof PointProjection() {
  conclude(p.x ∈ Real)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].proofSteps[0].rule, 'STRUCT_ELIM');
});

runTest('checker introduces struct membership from field memberships', () => {
  const report = checkFile(parseProgram(`
struct Point {
  x ∈ Real,
  y ∈ Real
} →

theorem PointIntro() {
  assume(p.x ∈ Real ∧ p.y ∈ Real) →
  declareToProve(p ∈ Point)
} ↔

proof PointIntro() {
  conclude(p ∈ Point)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].proofSteps[0].rule, 'STRUCT_INTRO');
});

runTest('checker validates exhaustive match and rejects incomplete coverage', () => {
  const proved = checkFile(parseProgram(`
type Shape =
  | Circle(r ∈ Real)
  | Rectangle(w ∈ Real, h ∈ Real)
} →

theorem ShapeCovered() {
  assume(s ∈ Shape) →
  declareToProve(s ∈ Shape)
} ↔

proof ShapeCovered() {
  match s {
    case Circle(r) => conclude(s ∈ Shape)
    case Rectangle(w, h) => conclude(s ∈ Shape)
  }
}
`));
  assert.equal(proved.state, 'PROVED');
  assert.equal(proved.reports[0].proofSteps[0].rule, 'MATCH_EXHAUSTIVE');

  const failed = checkFile(parseProgram(`
type Shape =
  | Circle(r ∈ Real)
  | Rectangle(w ∈ Real, h ∈ Real)
} →

theorem ShapeMiss() {
  assume(s ∈ Shape) →
  declareToProve(s ∈ Shape)
} ↔

proof ShapeMiss() {
  match s {
    case Circle(r) => conclude(s ∈ Shape)
  }
}
`));
  assert.equal(failed.state, 'FAILED');
});

runTest('checker proves list recursion on the tail and rejects non-structural recursion', () => {
  const proved = checkFile(parseProgram(`
fn length(xs ∈ List(Nat)) -> Nat {
  match xs {
    case [] => conclude(0)
    case [_, ...rest] => conclude(1 + length(rest))
  }
}
`));
  assert.equal(proved.state, 'PROVED');
  assert.equal(proved.reports[0].state, 'PROVED');

  const unverified = checkFile(parseProgram(`
fn bad(xs ∈ List(Nat)) -> Nat {
  match xs {
    case [] => conclude(0)
    case [x, ...rest] => conclude(1 + bad(xs))
  }
}
`));
  assert.equal(unverified.state, 'FAILED');
  assert.equal(unverified.reports[0].state, 'FAILED');
});

runTest('eval mode preserves executable fn declarations and runs list recursion', () => {
  const runtime = runExecutable(`
fn length(xs ∈ List(Nat)) -> Nat {
  match xs {
    case [] => conclude(0)
    case [_, ...rest] => conclude(1 + length(rest))
  }
} →

let answer = length([1, 2, 3]) →
assert(answer == 3)
`);
  assert.equal(runtime.answer, 3);
});

runTest('eval mode supports Result constructors, match, if, let-in, lambda, and fold', () => {
  const runtime = runExecutable(`
type Result =
  | Ok(value ∈ Nat)
  | Err(message ∈ String)
} →

fn unwrapOrZero(result ∈ Result) -> Nat {
  match result {
    case Ok(value) => conclude(value)
    case Err(_) => conclude(0)
  }
} →

let add1 = fn(x: Nat) => x + 1 →
let picked = if true then Ok(4) else Err("nope") →
let total = let base = unwrapOrZero(picked) in fold([1, 2], base, fn(acc: Nat, x: Nat) => acc + x) →
assert(add1(total) == 8)
`);
  assert.equal(typeof runtime.add1, 'function');
  assert.equal(runtime.total, 7);
});

runTest('eval mode expands imports before parsing', () => {
  const tempDir = fs.mkdtempSync(path.join(process.cwd(), 'tmp-import-'));
  const libFile = path.join(tempDir, 'lib.fl');
  const mainFile = path.join(tempDir, 'main.fl');
  fs.writeFileSync(libFile, `
fn inc(x ∈ Nat) -> Nat {
  conclude(x + 1)
}
`);
  fs.writeFileSync(mainFile, `
import "./lib.fl"

let answer = inc(4) →
assert(answer == 5)
`);
  const js = parseFLFile(mainFile);
  const context: Record<string, unknown> = {
    console: { log: () => {} },
    globalThis: {} as Record<string, unknown>,
    require,
    Buffer,
    URL,
  };
  context.globalThis = context;
  vm.runInNewContext(js, context);
  assert.equal(context.answer, 5);
  fs.rmSync(tempDir, { recursive: true, force: true });
});

runTest('eval mode supports Node-style web server routing helpers', () => {
  const runtime = runExecutable(`
type Result =
  | Ok(value ∈ Nat)
  | Err(message ∈ String)
} →

fn homeHandler(req ∈ Request) -> Response {
  conclude(text("home"))
} →

fn apiHandler(req ∈ Request) -> Response {
  conclude(json(Ok(7)))
} →

let app = router([
  route("GET", "/", homeHandler),
  route("GET", "/api", apiHandler)
]) →
let home = dispatch(app, request("GET", "/")) →
let api = dispatch(app, request("GET", "/api")) →
let miss = dispatch(app, request("GET", "/missing")) →
assert(home.status == 200) →
assert(home.body == "home") →
assert(api.status == 200) →
assert(api.headers["content-type"] == "application/json; charset=utf-8") →
assert(api.body.indexOf("Ok") >= 0) →
assert(api.body.indexOf("7") >= 0) →
assert(miss.status == 404)
`);
  assert.equal((runtime.home as any).body, 'home');
  assert.equal((runtime.api as any).status, 200);
  assert.equal((runtime.miss as any).status, 404);
});

runTest('cli executes proof-shaped files and still prints checker output', () => {
  const tempDir = fs.mkdtempSync(path.join(process.cwd(), 'tmp-cli-proof-'));
  const file = path.join(tempDir, 'proof-and-run.fl');
  fs.writeFileSync(file, `
theorem Identity() {
  assume(p) →
  declareToProve(p)
} ↔

proof Identity() {
  assume(p) →
  conclude(p)
} →

let answer = if true then 1 else 0 →
assert(answer == 1)
`);
  const result = spawnSync('node', ['dist/cli.js', file], {
    cwd: process.cwd(),
    encoding: 'utf8',
  });
  assert.equal(result.status, 0, result.stderr || result.stdout);
  assert.match(result.stdout, /proof \+ runtime mode/);
  assert.match(result.stdout, /Checking/);
  assert.match(result.stdout, /Executing/);
  assert.match(result.stdout, /Program holds/);
  fs.rmSync(tempDir, { recursive: true, force: true });
});

runTest('cli auto-detects server files as executable runtime without theorem mode', () => {
  const result = spawnSync('node', ['dist/cli.js', 'start', 'examples/server/hello-http.fl'], {
    cwd: process.cwd(),
    encoding: 'utf8',
  });
  assert.match(result.stdout + result.stderr, /server .*starting/);
  assert.doesNotMatch(result.stdout + result.stderr, /theorem-prover mode/);
});

runTest('fl web generates a buildable React app for executable files', () => {
  const outDir = path.join(process.cwd(), 'generated', 'futurlang-webapp');
  const generate = spawnSync('node', ['dist/cli.js', 'web', 'examples/demo/fn-double.fl', outDir], {
    cwd: process.cwd(),
    encoding: 'utf8',
  });
  assert.equal(generate.status, 0, generate.stderr || generate.stdout);
  assert.match(generate.stdout, /Generated React app/);

  const build = spawnSync('npm', ['run', 'build'], {
    cwd: outDir,
    encoding: 'utf8',
  });
  assert.equal(build.status, 0, build.stderr || build.stdout);
});

runTest('fl start generates frontend output without launching when --no-launch is set', () => {
  const outDir = path.join(process.cwd(), 'generated', 'futurlang-webapp');
  const result = spawnSync('node', ['dist/cli.js', '--no-launch', 'start', 'examples/demo/fn-double.fl', outDir], {
    cwd: process.cwd(),
    encoding: 'utf8',
  });
  assert.equal(result.status, 0, result.stderr || result.stdout);
  assert.match(result.stdout, /Generated React app/);
  assert.match(result.stdout, /Skipping frontend launch/);
});

runTest('obtain destructures existential into membership and body assumptions', () => {
  const report = checkFile(parseProgram(`
theorem ObtainTest() {
  given(∃ x ∈ S, x ∈ T) →
  assert(∃ y ∈ T, y ∈ S)
} ↔
proof ObtainTest() {
  obtain(a, ∃ x ∈ S, x ∈ T) →
  conclude(∃ y ∈ T, y ∈ S)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].state, 'PROVED');
});

runTest('intro on forall goal adds domain membership to context', () => {
  // intro(x) on ∀ x ∈ ℕ, P(x) must add "x ∈ ℕ" to context, not bare "x".
  const report = checkFile(parseProgram(`
theorem ForallDomain() {
  given(A ⊆ B) →
  assert(∀ x ∈ A, x ∈ B)
} ↔
proof ForallDomain() {
  intro(x) →
  conclude(x ∈ B)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].state, 'PROVED');
});

runTest('apply reduces goal via backward implication from context hypothesis', () => {
  const report = checkFile(parseProgram(`
theorem ApplyBack() {
  given(p → q) →
  given(p) →
  assert(q)
} ↔
proof ApplyBack() {
  apply(p → q) →
  conclude(p)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].state, 'PROVED');
});

runTest('apply chained backward through two implications', () => {
  const report = checkFile(parseProgram(`
theorem ApplyChain() {
  given(p → q) →
  given(q → r) →
  given(p) →
  assert(r)
} ↔
proof ApplyChain() {
  apply(q → r) →
  apply(p → q) →
  conclude(p)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].state, 'PROVED');
});

runTest('rewrite substitutes structurally, not by raw string', () => {
  // "ab" contains "a" as a substring — string splitting would corrupt it,
  // but term-based rewrite should leave it untouched.
  const report = checkFile(parseProgram(`
theorem RewriteStructural() {
  given(a = b) →
  given(a ∈ S) →
  assert(b ∈ S)
} ↔
proof RewriteStructural() {
  rewrite(a = b) →
  conclude(b ∈ S)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].state, 'PROVED');
});

runTest('intro strips implication antecedent and updates goal', () => {
  const report = checkFile(parseProgram(`
theorem IntroImp() {
  assert(p → q → p)
} ↔
proof IntroImp() {
  intro(hp) →
  intro(hq) →
  exact(p)
}
`));
  assert.equal(report.state, 'PROVED');
  assert.equal(report.reports[0].state, 'PROVED');
});

// ── Inter-block connective validation ─────────────────────────────────────

runTest('inter-block → between independent blocks causes FAILED', () => {
  const report = checkFile(parseProgram(`
lemma A() {
  declareToProve(1 = 1)
} ↔

proof A() {
  conclude(1 = 1)
} →

lemma B() {
  declareToProve(2 = 2)
} ↔

proof B() {
  conclude(2 = 2)
}
`));
  assert.equal(report.state, 'FAILED');
  const hasInterBlockError = report.diagnostics.some(d =>
    d.severity === 'error' && d.message.includes('inter-block connective')
  );
  assert.ok(hasInterBlockError, 'expected inter-block connective error');
});

runTest('inter-block ∧ before a block that applies the previous causes FAILED', () => {
  const report = checkFile(parseProgram(`
lemma A() {
  declareToProve(1 = 1)
} ↔

proof A() {
  conclude(1 = 1)
} ∧

lemma B() {
  assume(1 = 1) →
  declareToProve(1 = 1)
} ↔

proof B() {
  apply(A)
}
`));
  assert.equal(report.state, 'FAILED');
  const hasInterBlockError = report.diagnostics.some(d =>
    d.severity === 'error' && d.message.includes('inter-block connective')
  );
  assert.ok(hasInterBlockError, 'expected inter-block connective error');
});

runTest('inter-block → is accepted when next proof applies current block', () => {
  const report = checkFile(parseProgram(`
lemma A() {
  declareToProve(1 = 1)
} ↔

proof A() {
  conclude(1 = 1)
} →

lemma B() {
  assume(1 = 1) →
  declareToProve(1 = 1)
} ↔

proof B() {
  apply(A)
}
`));
  assert.equal(report.state, 'PROVED');
});

runTest('inter-block ∧ is accepted between independent blocks', () => {
  const report = checkFile(parseProgram(`
lemma A() {
  declareToProve(1 = 1)
} ↔

proof A() {
  conclude(1 = 1)
} ∧

lemma B() {
  declareToProve(2 = 2)
} ↔

proof B() {
  conclude(2 = 2)
}
`));
  assert.equal(report.state, 'PROVED');
});

// ── Proof-step connective validation ──────────────────────────────────────

runTest('proof-step → between independent derivations causes FAILED', () => {
  const report = checkFile(parseProgram(`
lemma StepArrowFail() {
  assume(x ∈ A ∩ B) →
  declareToProve(x ∈ A ∧ x ∈ B)
} ↔

proof StepArrowFail() {
  assume(x ∈ A ∩ B) →
  prove(x ∈ A) →
  prove(x ∈ B) →
  conclude(x ∈ A ∧ x ∈ B)
}
`));
  assert.equal(report.state, 'FAILED');
  const report0 = report.reports[0];
  const hasConnError = (report0.diagnostics ?? []).some(d =>
    d.severity === 'error' && d.message.includes('does not depend on')
  );
  assert.ok(hasConnError, 'expected connective error for independent steps joined with →');
});

runTest('proof-step ∧ between independent derivations is accepted', () => {
  const report = checkFile(parseProgram(`
lemma StepWedgePass() {
  assume(x ∈ A ∩ B) →
  declareToProve(x ∈ A ∧ x ∈ B)
} ↔

proof StepWedgePass() {
  assume(x ∈ A ∩ B) →
  prove(x ∈ A) ∧
  prove(x ∈ B) →
  conclude(x ∈ A ∧ x ∈ B)
}
`));
  assert.equal(report.state, 'PROVED');
});

runTest('declaration body: assume(p) ∧ assume(q) is accepted as independent hypotheses', () => {
  const report = checkFile(parseProgram(`
lemma TwoAssumes() {
  assume(P) ∧
  assume(Q) →
  declareToProve(P ∧ Q)
} ↔

proof TwoAssumes() {
  conclude(P ∧ Q)
}
`));
  assert.equal(report.state, 'PROVED');
});

runTest('declaration body: assume(p) → assume(q) is rejected (→ implies dependency between hypotheses)', () => {
  const report = checkFile(parseProgram(`
lemma BadTwoAssumes() {
  assume(P) →
  assume(Q) →
  declareToProve(P ∧ Q)
} ↔

proof BadTwoAssumes() {
  conclude(P ∧ Q)
}
`));
  assert.equal(report.state, 'FAILED');
  const hasConnError = (report.reports[0]?.diagnostics ?? []).some(d =>
    d.severity === 'error' && d.message.includes('independent')
  );
  assert.ok(hasConnError, 'expected connective error for assume() → assume()');
});

runTest('inter-block ∨ emits a warning but does not cause FAILED', () => {
  const report = checkFile(parseProgram(`
lemma OrLeft() {
  assume(P) →
  declareToProve(P ∨ Q)
} ↔

proof OrLeft() {
  conclude(P ∨ Q)
} ∨

lemma OrRight() {
  assume(Q) →
  declareToProve(P ∨ Q)
} ↔

proof OrRight() {
  conclude(P ∨ Q)
}
`));
  assert.notEqual(report.state, 'FAILED');
  const hasWarning = report.diagnostics?.some(d =>
    d.severity === 'warning' && d.message.includes('∨')
  );
  assert.ok(hasWarning, 'expected warning for unvalidated ∨ connective');
});

runTest('demo examples all reduce to PROVED with no pending morphisms', () => {
  const demoDir = path.resolve(__dirname, '../../examples/demo');
  const files = collectDemoFiles(demoDir);
  const expectedStates = new Map<string, 'PROVED' | 'FAILED'>([
    ['match-exhaustive-fail.fl', 'FAILED'],
    ['list-nonstructural-fail.fl', 'FAILED'],
  ]);
  for (const file of files) {
    const source = fs.readFileSync(file, 'utf8');
    const report = checkFile(parseProgram(source));
    const label = path.relative(demoDir, file);
    const expected = expectedStates.get(label) ?? 'PROVED';
    assert.equal(report.state, expected, label);
    if (expected !== 'PROVED') continue;
    for (const theoremReport of report.reports) {
      assert.equal(theoremReport.state, 'PROVED', `${label}:${theoremReport.name}`);
      assert.equal(theoremReport.pendingCount, 0, `${label}:${theoremReport.name}`);
    }
  }
});

runTest('default fl command executes the full demo corpus with only intentional failures', () => {
  const demoDir = path.resolve(__dirname, '../../examples/demo');
  const files = collectDemoFiles(demoDir);
  const expectedExit = new Map<string, number>([
    ['match-exhaustive-fail.fl', 1],
  ]);

  for (const file of files) {
    const label = path.relative(demoDir, file);
    const result = spawnSync('node', ['dist/cli.js', file], {
      cwd: process.cwd(),
      encoding: 'utf8',
    });
    const expected = expectedExit.get(label) ?? 0;
    assert.equal(
      result.status,
      expected,
      `${label}\n${result.stdout}\n${result.stderr}`,
    );
    if (expected === 0) {
      assert.match(result.stdout, /Program holds|server .*starting|proof \+ runtime mode|fn /);
    } else {
      assert.match(result.stdout + result.stderr, /FAILED|non-exhaustive/i);
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
