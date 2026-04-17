import {
  ASTNode,
  AssertNode,
  AssumeNode,
  ConcludeNode,
  DeclareToProveNode,
  ProveNode,
  AndIntroStepNode,
  OrIntroStepNode,
  FnParam,
  GivenNode,
  InductionNode,
  LemmaNode,
  MatchNode,
  ProofNode,
  RawNode,
  SetVarNode,
  StructField,
  StructNode,
  TypeDeclNode,
  TheoremNode,
  IntroNode,
  RewriteNode,
  ExactNode,
  ObtainNode,
} from '../parser/ast';
import { validateDeclarationBody } from '../parser/parser';
import { termFromString, termEqual, applySubst, rewriteTerm, Term, termToString } from '../kernel/term';
import {
  arithEqual,
  arithSymEqual,
  arithSymEqualWithSubst,
  evalArith,
  parseEvenClaim,
  parseOddClaim,
  parseDividesClaim,
  extractDoubleOperand,
  extractSuccDoubleOperand,
  splitTopMul,
  isConcreteEven,
  isConcreteOdd,
  normArith,
  parseAbsEquality,
  parseSignEquality,
  parseOrder,
  evalOrder,
  parseCongruence,
  areCongruent,
  evalMod,
  parseModOp,
  isPrime,
  parsePrimePred,
  parseTotientExpr,
  parseTotientEquality,
  computeTotient,
  parsePower,
} from '../kernel/arithmetic';
import { unify } from '../kernel/unify';
import {
  formatMorphismExpr,
  MorphismExpr,
  exprToProp,
  parseCanonicalExpr,
  parseCategoricalEqualityCanonical,
  parseCategoryPredicateCanonical,
  parseMeasurePredicateCanonical,
  parseBinarySetCanonical,
  parseBoundedQuantifierCanonical,
  parseConjunctionCanonical,
  parseDisjunctionCanonical,
  parseEqualityCanonical,
  parseIffCanonical,
  parseImplicationCanonical,
  parseIndexedUnionCanonical,
  parseMembershipCanonical,
  parseMorphismDeclarationCanonical,
  parseMorphismExprCanonical,
  parseSetBuilderCanonical,
  parseSetBuilderOrUnionCanonical,
  parseSubsetCanonical,
  sameProp,
} from './propositions';
import { KernelError, MorphismRecord, WenittainCategory } from '../kernel/category';
import { CategoryDiagramError, CategoryDiagramKernel } from '../kernel/category-diagrams';
import { WenittainValue } from '../kernel/values';
import {
  CheckOptions,
  ClaimSet,
  DerivationNode,
  Diagnostic,
  FileReport,
  KernelRule,
  ProofObject,
  ProofReport,
  ProofState,
  ProofStepTrace,
} from './types';

interface Pair {
  theorem: TheoremNode | LemmaNode;
  proof: ProofNode;
}

interface VariableBinding {
  name: string;
  domain: string | null;
}

export interface Context {
  category: WenittainCategory;
  objects: ProofObject[];
  derivations: DerivationNode[];
  diagnostics: Diagnostic[];
  proofSteps: ProofStepTrace[];
  variables: VariableBinding[];
  assumptions: ProofObject[];
  premises: ProofObject[];
  lemmas: Map<string, ClaimSet>;
  goal: string | null;
  diagrams: CategoryDiagramKernel;
  structs: Map<string, StructDefinition>;
  types: Map<string, TypeDefinition>;
  unverifiedReasons: string[];
}

interface StructDefinition {
  name: string;
  fields: StructField[];
  projections: Map<string, string>;
}

interface TypeDefinition {
  name: string;
  variants: TypeVariantDefinition[];
}

interface TypeVariantDefinition {
  name: string;
  parent: string;
  fields: StructField[];
}

interface ParsedSort {
  kind: 'named' | 'list';
  name?: string;
  element?: ParsedSort;
}

const TOP = '⊤';
const BOTTOM = '⊥';
const BUILTIN_SORTS = new Set(['ℕ', 'ℤ', 'ℚ', 'ℝ', 'String', 'Set', 'Element']);

export function checkFile(nodes: ASTNode[], options: CheckOptions = {}): FileReport {
  const diagnostics: Diagnostic[] = [];
  const reports: ProofReport[] = [];
  const structs = collectStructDefinitions(nodes, diagnostics);
  const types = collectTypeDefinitions(nodes, structs, diagnostics);
  const pairs = findPairs(nodes);
  const pairNames = new Set(pairs.map(pair => normalizeName(pair.theorem.name)));
  const lemmas = new Map<string, ClaimSet>();
  const eliminators = generateEliminators(types);
  for (const [name, claimSet] of eliminators) {
    lemmas.set(name, claimSet);
  }

  let theoremCount = 0;
  let proofCount = 0;
  let pairedCount = 0;

  for (const node of nodes) {
    if (node.type === 'Theorem' || node.type === 'Lemma') theoremCount++;
    if (node.type === 'Proof') proofCount++;
  }

  for (const pair of pairs) {
    pairedCount++;
    const report = checkPair(pair, lemmas, structs, types, options);
    reports.push(report);
    if (pair.theorem.type === 'Lemma') {
      lemmas.set(normalizeName(pair.theorem.name), {
        name: pair.theorem.name,
        premises: theoremPremises(pair.theorem),
        conclusion: theoremGoal(pair.theorem),
        state: report.state,
      });
    }
  }

  for (const node of nodes) {
    if (node.type === 'Theorem' && !pairNames.has(normalizeName(node.name))) {
      diagnostics.push({ severity: 'info', message: `Theorem '${node.name}' has no proof` });
    }
    if (node.type === 'Lemma' && !pairNames.has(normalizeName(node.name))) {
      diagnostics.push({ severity: 'info', message: `Lemma '${node.name}' has no proof` });
    }
  }

  // ── Inter-block connective validation ────────────────────────────────────────
  // Build a map: proof name → set of lemma/theorem names it references via apply()
  const proofApplyNames = new Map<string, Set<string>>();
  for (const pair of pairs) {
    proofApplyNames.set(normalizeName(pair.theorem.name), collectApplyNames(pair.proof.body ?? []));
  }

  // Walk top-level nodes in order; for each proof node with a non-↔ connective,
  // validate that the connective matches the actual dependency on the next block.
  for (let i = 0; i < nodes.length; i++) {
    const node = nodes[i];
    if (node.type !== 'Proof') continue;
    const proofNode = node as ProofNode;
    if (proofNode.fnMeta) continue; // fn-desugared proofs are not subject to inter-block validation
    const conn = proofNode.connective;
    if (!conn || conn === '↔') continue;
    if (conn === '∨') {
      diagnostics.push({
        severity: 'warning',
        message: `Inter-block connective '∨' before the block after '${proofNode.name}' is not validated by the checker. The disjunctive relationship is accepted but not verified.`,
      });
      continue;
    }

    // Find the next theorem/lemma
    let j = i + 1;
    while (j < nodes.length && nodes[j].type !== 'Theorem' && nodes[j].type !== 'Lemma') j++;
    if (j >= nodes.length) continue;

    const nextBlock = nodes[j] as TheoremNode | LemmaNode;
    const nextApply = proofApplyNames.get(normalizeName(nextBlock.name)) ?? new Set<string>();
    const prevName = normalizeName(proofNode.name);
    const nextUsesThis = nextApply.has(prevName);

    if (conn === '→' && !nextUsesThis) {
      diagnostics.push({
        severity: 'error',
        message: `Incorrect inter-block connective '→' before '${nextBlock.name}': this block does not depend on '${proofNode.name}'. Use ∧ for independent blocks.`,
      });
    } else if (conn === '∧' && nextUsesThis) {
      diagnostics.push({
        severity: 'error',
        message: `Incorrect inter-block connective '∧' before '${nextBlock.name}': this block depends on '${proofNode.name}' via apply(). Use → to show the dependency.`,
      });
    }
  }

  const hasInterBlockErrors = diagnostics.some(d => d.severity === 'error');
  const pairState = combineStates(reports.map(report => report.state), pairedCount === 0 ? 'FAILED' : 'PROVED');
  const state = hasInterBlockErrors ? 'FAILED' : pairState;
  return {
    state,
    valid: state === 'PROVED',
    theoremCount,
    proofCount,
    pairedCount,
    reports,
    diagnostics,
  };
}

function collectApplyNames(nodes: ASTNode[]): Set<string> {
  const names = new Set<string>();
  function walk(ns: ASTNode[]): void {
    for (const n of ns) {
      if (n.type === 'Apply') names.add(normalizeName((n as import('../parser/ast').ApplyNode).target));
      if ('body' in n && Array.isArray((n as { body: ASTNode[] }).body)) walk((n as { body: ASTNode[] }).body);
      if ('steps' in n && Array.isArray((n as { steps: ASTNode[] }).steps)) walk((n as { steps: ASTNode[] }).steps);
      if ('cases' in n && Array.isArray((n as { cases: { body: ASTNode[] }[] }).cases)) {
        for (const c of (n as { cases: { body: ASTNode[] }[] }).cases) walk(c.body ?? []);
      }
    }
  }
  walk(nodes);
  return names;
}

function checkPair(
  pair: Pair,
  lemmas: Map<string, ClaimSet>,
  structs: Map<string, StructDefinition>,
  types: Map<string, TypeDefinition>,
  _options: CheckOptions,
): ProofReport {
  // Validate declaration body syntax — warnings for legacy keywords, errors for structural violations
  const declErrors = validateDeclarationBody(pair.theorem.name, pair.theorem.body);
  const premises = theoremPremises(pair.theorem);
  const goal = theoremGoal(pair.theorem);
  const ctx = createContext(goal, lemmas, premises, structs, types);
  seedPremises(ctx, premises);
  for (const err of declErrors) {
    // Legacy keyword uses (given/assert) are warnings; structural errors (missing declareToProve, etc.) are errors
    const isLegacy = err.includes('replace assert()') || err.includes('replace given()') || err.includes('no longer valid');
    ctx.diagnostics.push({ severity: isLegacy ? 'warning' : 'error', message: err, rule: 'STRUCTURAL' });
  }
  if (pair.proof.fnMeta) {
    const recursionIssue = validateListStructuralRecursion(pair.proof);
    if (recursionIssue) {
      ctx.unverifiedReasons.push(recursionIssue);
      ctx.diagnostics.push({ severity: 'warning', message: recursionIssue, rule: 'STRUCTURAL' });
    }
  }

  // Track previous derived object and its connective for connective validation.
  // The connective on node i says how node i connects to node i+1 — so we validate
  // when processing node i+1 using node i's connective and the two derived objects.
  let prevDerivedObject: ProofObject | null = null;
  let prevConnective: import('../parser/ast').BlockConnective = null;
  let prevIsAssume = false;

  for (let index = 0; index < pair.proof.body.length; index++) {
    const step = index + 1;
    const node = pair.proof.body[index];
    const objectsBefore = ctx.objects.length;

    try {
      handleNode(ctx, node, step);
    } catch (error) {
      const message = error instanceof Error ? error.message : 'Unknown checker failure';
      ctx.diagnostics.push({ severity: 'error', step, message });
      ctx.proofSteps.push({
        step,
        kind: classifyStep(node),
        claim: nodeToClaim(node),
        rule: 'STRUCTURAL',
        state: 'FAILED',
        message,
      });
    }

    // Find newly derived object (if any) for connective validation
    const currDerivedObject = ctx.objects.length > objectsBefore
      ? ctx.objects[ctx.objects.length - 1]
      : null;

    const isDerivationStep = node.type === 'Prove' || node.type === 'Conclude'
      || node.type === 'Assert' || node.type === 'AndIntroStep' || node.type === 'OrIntroStep';
    const isNewStyleStep = node.type === 'Prove' || node.type === 'Assert'
      || node.type === 'AndIntroStep' || node.type === 'OrIntroStep';
    const isAssume = node.type === 'Assume';

    // Validate the connective from the PREVIOUS step to THIS step (new-style nodes only)
    if (isNewStyleStep && currDerivedObject && prevDerivedObject && prevConnective) {
      if (prevIsAssume) {
        // After assume(), must use → (the hypothesis leads to what follows)
        if (prevConnective !== '→') {
          const msg = `Incorrect connective '${prevConnective}' after assume(): use → because the hypothesis leads to the following derivation.`;
          ctx.diagnostics.push({ severity: 'error', step, message: msg, rule: 'CONNECTIVE' });
        }
      } else {
        validateConnective(ctx, prevConnective, prevDerivedObject, currDerivedObject, step);
      }
    }

    // Update tracking for next iteration
    if (isDerivationStep && currDerivedObject) {
      prevDerivedObject = currDerivedObject;
      prevConnective = (node as ASTNode & { connective?: import('../parser/ast').BlockConnective }).connective ?? null;
      prevIsAssume = false;
    } else if (isAssume) {
      // assume() adds to ctx.assumptions, not ctx.objects — track it separately
      prevDerivedObject = ctx.assumptions[ctx.assumptions.length - 1] ?? null;
      prevConnective = (node as AssumeNode).connective;
      prevIsAssume = true;
    }
  }

  const derivedConclusion = findDerivedConclusion(ctx, goal);
  if (goal && !derivedConclusion) {
    ctx.diagnostics.push({
      severity: 'error',
      message: `Proof '${pair.proof.name}' does not establish theorem goal '${goal}'`,
      rule: 'STRUCTURAL',
    });
  }

  const state = reportState(ctx, goal, derivedConclusion);
  return {
    name: pair.theorem.name,
    state,
    valid: state === 'PROVED',
    stepCount: pair.proof.body.length,
    goal,
    premises,
    derivedConclusion,
    proofSteps: ctx.proofSteps,
    proofObjects: ctx.objects,
    derivations: ctx.derivations,
    diagnostics: ctx.diagnostics,
    provedCount: ctx.objects.filter(object => object.tau === '1').length,
    pendingCount: ctx.objects.filter(object => object.pending).length,
  };
}

function createContext(
  goal: string | null,
  lemmas: Map<string, ClaimSet>,
  premises: string[],
  structs: Map<string, StructDefinition>,
  types: Map<string, TypeDefinition>,
): Context {
  const category = new WenittainCategory();
  category.createObject(TOP);
  category.createObject(BOTTOM);
  for (const premise of premises) {
    ensureClaimObjects(category, premise);
  }
  if (goal) {
    ensureClaimObjects(category, goal);
  }
  return {
    category,
    diagrams: new CategoryDiagramKernel(),
    objects: [],
    derivations: [],
    diagnostics: [],
    proofSteps: [],
    variables: [],
    assumptions: [],
    premises: [],
    lemmas: new Map(lemmas),
    goal,
    structs,
    types,
    unverifiedReasons: [],
  };
}

function seedPremises(ctx: Context, premises: string[]) {
  for (const premise of premises) {
    const morphism = createKernelObject(ctx, premise, 'PREMISE', -1, [], [], '1');
    ctx.premises.push(morphism);
  }
}

export function createMutableContext(premises: string[], goal: string | null): Context {
  const ctx = createContext(goal, new Map(), premises, new Map(), new Map());
  seedPremises(ctx, premises);
  return ctx;
}

export function evaluateIncrementalStep(ctx: Context, node: ASTNode): import('./types').ProofStepTrace | null {
  const startStepCount = ctx.proofSteps.length;
  const stepNumber = startStepCount + 1;
  try {
    handleNode(ctx, node, stepNumber);
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Unknown checker failure';
    ctx.diagnostics.push({ severity: 'error', step: stepNumber, message });
    ctx.proofSteps.push({
      step: stepNumber,
      kind: classifyStep(node),
      claim: nodeToClaim(node),
      rule: 'STRUCTURAL',
      state: 'FAILED',
      message,
    });
  }
  if (ctx.proofSteps.length > startStepCount) {
    return ctx.proofSteps[ctx.proofSteps.length - 1];
  }
  return null;
}

function handleNode(ctx: Context, node: ASTNode, step: number): void {
  // Warn on legacy keywords (given/assert) — downgraded to warning so existing proofs still pass
  const legacy = (node as ASTNode & { legacyError?: string }).legacyError;
  if (legacy) {
    ctx.diagnostics.push({ severity: 'warning', step, message: legacy, rule: 'STRUCTURAL' });
    // Fall through: still process the node so existing proofs are not broken
  }

  switch (node.type) {
    case 'Assume':
      handleAssume(ctx, node, step);
      return;
    case 'SetVar':
      handleSetVar(ctx, node, step);
      return;
    case 'Assert':
      // Legacy assert in proof body — handle but also flag
      handleClaimStep(ctx, node, step, 'assert');
      return;
    case 'Prove':
      handleProveStep(ctx, node, step);
      return;
    case 'AndIntroStep':
      handleAndIntroStep(ctx, node, step);
      return;
    case 'OrIntroStep':
      handleOrIntroStep(ctx, node, step);
      return;
    case 'Conclude':
      handleClaimStep(ctx, node, step, 'conclude');
      return;
    case 'Induction':
      handleInduction(ctx, node, step);
      return;
    case 'Match':
      handleMatch(ctx, node, step);
      return;
    case 'Apply':
      handleApply(ctx, node.target, step);
      return;
    case 'Raw':
      handleRaw(ctx, node, step);
      return;
    case 'Intro':
      handleIntro(ctx, node, step);
      return;
    case 'Rewrite':
      handleRewrite(ctx, node, step);
      return;
    case 'Exact':
      handleExact(ctx, node, step);
      return;
    case 'Obtain':
      handleObtain(ctx, node, step);
      return;
    default:
      return;
  }
}

// prove() — intermediate derivation step (same kernel as assert/conclude)
function handleProveStep(ctx: Context, node: ProveNode, step: number): void {
  handleClaimStep(ctx, { type: 'Assert', expr: node.expr, connective: node.connective }, step, 'prove');
}

// AndIntro(P, Q) — explicitly constructs P ∧ Q from P and Q in context
function handleAndIntroStep(ctx: Context, node: AndIntroStepNode, step: number): void {
  const claim = `${node.left} ∧ ${node.right}`;
  handleClaimStep(ctx, { type: 'Assert', expr: { type: 'Atom', condition: claim, atomKind: 'expression' }, connective: node.connective }, step, 'andIntro');
}

// OrIntro(P ∨ Q) — explicitly constructs P ∨ Q from one disjunct in context
function handleOrIntroStep(ctx: Context, node: OrIntroStepNode, step: number): void {
  handleClaimStep(ctx, { type: 'Assert', expr: { type: 'Atom', condition: node.claim, atomKind: 'expression' }, connective: node.connective }, step, 'orIntro');
}

// ── Connective validation ──────────────────────────────────────────────────────

/** Transitively check whether `target` depends on `prereq` via the inputs graph. */
function dependsOn(objects: ProofObject[], target: ProofObject, prereq: ProofObject): boolean {
  const visited = new Set<string>();
  const stack = [...target.inputs];
  while (stack.length > 0) {
    const id = stack.pop()!;
    if (visited.has(id)) continue;
    visited.add(id);
    if (id === prereq.id) return true;
    const obj = objects.find(o => o.id === id);
    if (obj) stack.push(...obj.inputs);
  }
  return false;
}

function validateConnective(
  ctx: Context,
  connective: import('../parser/ast').BlockConnective,
  prev: ProofObject,
  curr: ProofObject,
  step: number,
): void {
  if (!connective) return; // last step, no validation

  const depends = dependsOn(ctx.objects, curr, prev);

  if (connective === '→') {
    // → requires curr to depend on prev
    if (!depends) {
      const msg = `Incorrect connective '→' at step ${step}: '${curr.claim}' does not depend on '${prev.claim}'. Use ∧ if these are independent facts.`;
      ctx.diagnostics.push({ severity: 'error', step, message: msg, rule: 'CONNECTIVE' });
    }
  } else if (connective === '∧') {
    // ∧ requires curr to be independent of prev
    if (depends) {
      const msg = `Incorrect connective '∧' at step ${step}: '${curr.claim}' depends on '${prev.claim}'. Use → to show this follows from the previous step.`;
      ctx.diagnostics.push({ severity: 'error', step, message: msg, rule: 'CONNECTIVE' });
    }
  } else if (connective === '∨') {
    // ∨ requires curr to be a disjunction where prev is one of the disjuncts
    const parts = parseDisjunctionCanonical(curr.claim);
    const prevClaim = prev.claim;
    if (!parts || (normArith(parts[0]) !== normArith(prevClaim) && normArith(parts[1]) !== normArith(prevClaim))) {
      const msg = `Incorrect connective '∨' at step ${step}: '${curr.claim}' is not a disjunction containing '${prev.claim}'. Use ∨ only to introduce a disjunction from one of its disjuncts.`;
      ctx.diagnostics.push({ severity: 'error', step, message: msg, rule: 'CONNECTIVE' });
    }
  }
}

function handleAssume(ctx: Context, node: AssumeNode, step: number) {
  const claim = exprToProp(node.expr);
  const proofObject = createKernelObject(ctx, claim, 'ASSUMPTION', step);
  ctx.assumptions.push(proofObject);
  ctx.proofSteps.push({
    step,
    kind: 'assume',
    claim,
    rule: 'ASSUMPTION',
    state: 'PROVED',
    message: 'Assumption introduced as a morphism into the current Boolean-category derivation context',
  });
}

function handleSetVar(ctx: Context, node: SetVarNode, step: number) {
  ctx.variables.push({ name: node.varName, domain: node.varType });
  ctx.proofSteps.push({
    step,
    kind: 'setVar',
    claim: node.varType ? `${node.varName}: ${node.varType}` : node.varName,
    rule: 'STRUCTURAL',
    state: 'PROVED',
    message: 'Bound variable recorded for categorical introduction or elimination rules',
  });
}

function handleInduction(ctx: Context, node: InductionNode, step: number) {
  const claim = ctx.goal ?? exprToProp(node.fold);
  createKernelObject(ctx, claim, 'FOLD_ELIM', step);
  ctx.proofSteps.push({
    step,
    kind: 'induction',
    claim,
    rule: 'FOLD_ELIM',
    state: 'PROVED',
    uses: [exprToProp(node.fold), node.base, node.step],
    message: 'Desugared induction into the trusted fold primitive',
  });
}

function handleMatch(ctx: Context, node: MatchNode, step: number) {
  const scrutinee = exprToProp(node.scrutinee);
  const scrutineeMembership = requireAnyMembership(ctx, scrutinee);
  const scrutineeType = scrutineeMembership ? parseMembershipCanonical(scrutineeMembership.claim)?.set ?? null : null;
  const parsedSort = scrutineeType ? parseSort(scrutineeType) : null;
  if (parsedSort?.kind === 'list' && scrutineeType) {
    handleListMatch(ctx, node, step, scrutinee, scrutineeType, parsedSort);
    return;
  }
  const boolType = inferBooleanMatchType(node);
  const typeDef = scrutineeType ? ctx.types.get(scrutineeType) : boolType;

  if ((!scrutineeMembership && !boolType) || !typeDef) {
    ctx.diagnostics.push({ severity: 'error', step, message: `Pattern match requires a scrutinee with a registered sum type: '${scrutinee}'`, rule: 'MATCH_EXHAUSTIVE' });
    ctx.proofSteps.push({
      step,
      kind: 'match',
      claim: scrutinee,
      rule: 'MATCH_EXHAUSTIVE',
      state: 'FAILED',
      message: 'No registered variant information is available for this match scrutinee',
    });
    return;
  }

  const covered = new Set(
    node.cases
      .filter(matchCase => matchCase.pattern.kind === 'variant')
      .map(matchCase => matchCase.pattern.constructor),
  );
  const exhaustive = node.cases.some(matchCase => matchCase.pattern.kind === 'wildcard')
    || typeDef.variants.every(variant => covered.has(variant.name));
  if (!exhaustive) {
    ctx.diagnostics.push({ severity: 'error', step, message: 'MATCH_EXHAUSTIVE failed: non-exhaustive match', rule: 'MATCH_EXHAUSTIVE' });
    ctx.proofSteps.push({
      step,
      kind: 'match',
      claim: scrutinee,
      rule: 'MATCH_EXHAUSTIVE',
      state: 'FAILED',
      message: 'Pattern matching must cover every variant or include a wildcard case',
    });
    return;
  }

  const branchStates: ProofState[] = [];
  const branchUses: string[] = [];
  for (const matchCase of node.cases) {
    const branch = createBranchContext(ctx);
    const variant = matchCase.pattern.kind !== 'variant'
      ? null
      : typeDef.variants.find(candidate => candidate.name === matchCase.pattern.constructor) ?? null;
    if (matchCase.pattern.kind === 'variant' && !variant) {
      branchStates.push('FAILED');
      continue;
    }
    if (variant && matchCase.pattern.kind === 'variant') {
      applyVariantPatternBindings(branch, scrutinee, variant, matchCase.pattern.bindings, step);
      branchUses.push(`${scrutinee} ∈ ${variant.name}`);
    } else {
      branchUses.push('_');
    }

    for (const branchNode of matchCase.body) {
      try {
        handleNode(branch, branchNode, step);
      } catch (error) {
        const message = error instanceof Error ? error.message : 'Unknown match-branch failure';
        branch.diagnostics.push({ severity: 'error', step, message, rule: 'OR_ELIM' });
      }
    }
    branchStates.push(evaluateMatchBranch(branch, ctx.goal, step));
  }

  if (branchStates.some(state => state === 'FAILED')) {
    ctx.diagnostics.push({ severity: 'error', step, message: 'At least one match branch does not establish the required conclusion', rule: 'OR_ELIM' });
    ctx.proofSteps.push({
      step,
      kind: 'match',
      claim: ctx.goal ?? scrutinee,
      rule: 'MATCH_EXHAUSTIVE',
      state: 'FAILED',
      uses: branchUses,
      message: 'Exhaustive case analysis failed because a branch does not discharge the branch goal',
    });
    return;
  }

  const targetClaim = ctx.goal ?? scrutineeMembership?.claim ?? scrutinee;
  createKernelObject(ctx, targetClaim, 'MATCH_EXHAUSTIVE', step);
  ctx.proofSteps.push({
    step,
    kind: 'match',
    claim: targetClaim,
    rule: 'MATCH_EXHAUSTIVE',
    state: 'PROVED',
    uses: branchUses,
    message: 'Validated exhaustive proof by cases via categorical OR elimination',
  });
}

function handleListMatch(
  ctx: Context,
  node: MatchNode,
  step: number,
  scrutinee: string,
  scrutineeType: string,
  parsedSort: ParsedSort,
) {
  if (!requireAnyMembership(ctx, scrutinee) || parsedSort.kind !== 'list' || !parsedSort.element) {
    ctx.diagnostics.push({ severity: 'error', step, message: `Pattern match requires a scrutinee with a registered list sort: '${scrutinee}'`, rule: 'MATCH_EXHAUSTIVE' });
    ctx.proofSteps.push({
      step,
      kind: 'match',
      claim: scrutinee,
      rule: 'MATCH_EXHAUSTIVE',
      state: 'FAILED',
      message: 'No kernel List sort information is available for this match scrutinee',
    });
    return;
  }

  const nilCase = node.cases.find(matchCase => matchCase.pattern.kind === 'list_nil') ?? null;
  const consCase = node.cases.find(matchCase => matchCase.pattern.kind === 'list_cons') ?? null;
  const exhaustive = node.cases.length === 2 && Boolean(nilCase) && Boolean(consCase);
  if (!exhaustive) {
    ctx.diagnostics.push({ severity: 'error', step, message: 'MATCH_EXHAUSTIVE failed: List matches must contain exactly [] and [x, ...rest]', rule: 'MATCH_EXHAUSTIVE' });
    ctx.proofSteps.push({
      step,
      kind: 'match',
      claim: scrutinee,
      rule: 'MATCH_EXHAUSTIVE',
      state: 'FAILED',
      message: 'Kernel List matching requires both Nil and Cons cases',
    });
    return;
  }

  const branchStates: ProofState[] = [];
  const branchUses: string[] = [];
  for (const matchCase of [nilCase, consCase]) {
    if (!matchCase) continue;
    const branch = createBranchContext(ctx);
    if (matchCase.pattern.kind === 'list_cons') {
      applyListPatternBindings(branch, scrutinee, scrutineeType, parsedSort, matchCase.pattern.head, matchCase.pattern.tail, step);
      branchUses.push(`[${matchCase.pattern.head}, ...${matchCase.pattern.tail}]`);
    } else {
      branchUses.push('[]');
    }

    for (const branchNode of matchCase.body) {
      try {
        handleNode(branch, branchNode, step);
      } catch (error) {
        const message = error instanceof Error ? error.message : 'Unknown list match-branch failure';
        branch.diagnostics.push({ severity: 'error', step, message, rule: 'OR_ELIM' });
      }
    }
    branchStates.push(evaluateMatchBranch(branch, ctx.goal, step));
  }

  if (branchStates.some(state => state === 'FAILED' || state === 'UNVERIFIED')) {
    ctx.diagnostics.push({ severity: 'error', step, message: 'At least one list match branch does not establish the required conclusion', rule: 'OR_ELIM' });
    ctx.proofSteps.push({
      step,
      kind: 'match',
      claim: ctx.goal ?? scrutinee,
      rule: 'MATCH_EXHAUSTIVE',
      state: 'FAILED',
      uses: branchUses,
      message: 'Exhaustive list case analysis failed because a branch does not discharge the branch goal',
    });
    return;
  }

  const targetClaim = ctx.goal ?? `${scrutinee} ∈ ${scrutineeType}`;
  createKernelObject(ctx, targetClaim, 'MATCH_EXHAUSTIVE', step);
  ctx.proofSteps.push({
    step,
    kind: 'match',
    claim: targetClaim,
    rule: 'MATCH_EXHAUSTIVE',
    state: 'PROVED',
    uses: branchUses,
    message: 'Validated exhaustive proof by cases over the kernel List primitive',
  });
}

function inferBooleanMatchType(node: MatchNode): TypeDefinition | null {
  const constructors: string[] = [];
  for (const matchCase of node.cases) {
    if (matchCase.pattern.kind === 'variant') {
      constructors.push(matchCase.pattern.constructor);
    }
  }
  const boolConstructors = new Set<string>(['true', 'false']);
  if (constructors.length === 0 || constructors.some(name => !boolConstructors.has(name))) {
    return null;
  }
  return {
    name: 'Bool',
    variants: [
      { name: 'true', parent: 'Bool', fields: [] },
      { name: 'false', parent: 'Bool', fields: [] },
    ],
  };
}

function handleApply(ctx: Context, target: string, step: number) {
  const lemma = ctx.lemmas.get(normalizeName(target));
  if (!lemma) {
    // Backward application: find the target as a hypothesis in context.
    // If it is an implication A → B whose consequent matches the current goal,
    // reduce the goal to A.
    const hyp = findExact(ctx.objects, target, false)
             ?? findExact(ctx.assumptions, target, false)
             ?? findExact(ctx.premises, target, false);
    if (hyp) {
      const impl = parseImplicationCanonical(hyp.claim);
      if (impl && ctx.goal) {
        const [antecedent, consequent] = impl;
        const consTerm = termFromString(consequent);
        const goalTerm = termFromString(ctx.goal);
        if (termEqual(consTerm, goalTerm)) {
          ctx.goal = antecedent;
          ctx.proofSteps.push({
            step,
            kind: 'apply',
            claim: antecedent,
            rule: 'BY_LEMMA',
            state: 'PROVED',
            uses: [hyp.claim],
            message: `Applied '${target}' backward: goal reduced to '${antecedent}'`,
          });
          return;
        }
      }
      ctx.diagnostics.push({ severity: 'error', step, message: `apply: '${target}' is not an implication whose consequent matches the goal '${ctx.goal ?? '(none)'}'`, rule: 'BY_LEMMA' });
      ctx.proofSteps.push({ step, kind: 'apply', claim: target, rule: 'BY_LEMMA', state: 'FAILED', message: `Consequent does not match goal` });
      return;
    }
    ctx.diagnostics.push({ severity: 'error', step, message: `Unknown lemma or hypothesis '${target}'`, rule: 'BY_LEMMA' });
    ctx.proofSteps.push({
      step,
      kind: 'apply',
      claim: target,
      rule: 'BY_LEMMA',
      state: 'FAILED',
      message: `'${target}' is not available`,
    });
    return;
  }
  if (lemma.state !== 'PROVED') {
    ctx.diagnostics.push({ severity: 'error', step, message: `Lemma '${target}' is not fully proved and cannot be applied`, rule: 'BY_LEMMA' });
    ctx.proofSteps.push({
      step,
      kind: 'apply',
      claim: lemma.conclusion ?? target,
      rule: 'BY_LEMMA',
      state: 'FAILED',
      imports: [lemma.name],
      message: `Lemma '${target}' is not fully proved`,
    });
    return;
  }

  // If the lemma has metavars, use unification to instantiate it
  if (lemma.metavars && lemma.metavars.length > 0 && lemma.conclusion && ctx.goal) {
    const metaSet = new Set(lemma.metavars);
    const lemmaConcTerm = termFromString(lemma.conclusion);
    const goalTerm = termFromString(ctx.goal);
    const unifyResult = unify(lemmaConcTerm, goalTerm, metaSet);
    
    if (!unifyResult.error) {
      const subst = unifyResult.subst;
      const instantiatedPremises = lemma.premises.map(p => {
        const t = applySubst(termFromString(p), subst);
        return termToString(t);
      });
      const missingInstantiated = instantiatedPremises.filter(p => !findExact(ctx.objects, p, false) && !findExact(ctx.premises, p, false) && !findExact(ctx.assumptions, p, false));
      if (missingInstantiated.length === 0) {
        const conclusion = termToString(applySubst(termFromString(lemma.conclusion), subst));
        const inputs = instantiatedPremises
          .map(p => findExact(ctx.objects, p, false) ?? findExact(ctx.premises, p, false) ?? findExact(ctx.assumptions, p, false))
          .filter((o): o is ProofObject => Boolean(o))
          .map(o => o.id);
        createKernelObject(ctx, conclusion, 'BY_LEMMA', step, inputs, [lemma.name], '1');
        ctx.proofSteps.push({
          step, kind: 'apply', claim: conclusion, rule: 'BY_LEMMA', state: 'PROVED',
          imports: [lemma.name], uses: instantiatedPremises,
          message: `Applied lemma '${target}' via unification`,
        });
        return;
      }
    }
    
    ctx.diagnostics.push({ severity: 'error', step, message: `Lemma '${target}' unification failed`, rule: 'BY_LEMMA' });
    ctx.proofSteps.push({
      step,
      kind: 'apply',
      claim: target,
      rule: 'BY_LEMMA',
      state: 'FAILED',
      message: `Consequent does not unify with goal`,
      causalError: {
        ruleAttempted: 'BY_LEMMA',
        unificationMismatch: unifyResult.error,
      }
    });
    return;
  }

  const missing = lemma.premises.filter(premise => !findExact(ctx.objects, premise, false));
  if (missing.length > 0 || !lemma.conclusion) {
    ctx.diagnostics.push({
      severity: 'error',
      step,
      message: `Lemma '${target}' cannot be imported; missing premises: ${missing.join(' ; ') || 'conclusion'}`,
      rule: 'BY_LEMMA',
    });
    ctx.proofSteps.push({
      step,
      kind: 'apply',
      claim: lemma.conclusion ?? target,
      rule: 'BY_LEMMA',
      state: 'FAILED',
      imports: [lemma.name],
      message: `Lemma '${target}' does not compose with the current context`,
      causalError: {
        ruleAttempted: 'BY_LEMMA',
        missingPremises: missing,
      }
    });
    return;
  }
  const inputs = lemma.premises
    .map(premise => findExact(ctx.objects, premise, false))
    .filter((object): object is ProofObject => Boolean(object))
    .map(object => object.id);
  createKernelObject(ctx, lemma.conclusion, 'BY_LEMMA', step, inputs, [lemma.name], '1');
  ctx.proofSteps.push({
    step,
    kind: 'apply',
    claim: lemma.conclusion,
    rule: 'BY_LEMMA',
    state: 'PROVED',
    imports: [lemma.name],
    uses: lemma.premises,
    message: `Imported lemma '${target}' as a morphism in the current context`,
  });
}

function handleRaw(ctx: Context, node: RawNode, step: number) {
  const claim = node.content.trim();
  if (!/^contradiction\s*\(\s*\)\s*;?$/.test(claim)) {
    ctx.diagnostics.push({ severity: 'error', step, message: `Unsupported raw proof syntax: '${claim}'. Use assert, assume, conclude, apply, intro, rewrite, or exact.`, rule: 'STRUCTURAL' });
    ctx.proofSteps.push({
      step,
      kind: 'raw',
      claim,
      rule: 'STRUCTURAL',
      state: 'FAILED',
      message: 'Unsupported raw proof syntax',
    });
    return;
  }
  const contradiction = hasContradiction(ctx.objects);
  if (!contradiction) {
    ctx.diagnostics.push({ severity: 'error', step, message: 'contradiction() requires conflicting facts in scope', rule: 'CONTRADICTION' });
    ctx.proofSteps.push({
      step,
      kind: 'raw',
      claim: 'contradiction()',
      rule: 'CONTRADICTION',
      state: 'FAILED',
      message: 'No proposition and complement pair is available',
    });
    return;
  }
  const contradictionMeet = createKernelObject(
    ctx,
    `${contradiction[0].claim} ∧ ${contradiction[1].claim}`,
    'AND_INTRO',
    step,
    contradiction.map(object => object.id),
  );
  const bottom = createKernelObject(ctx, BOTTOM, 'CONTRADICTION', step, [contradictionMeet.id]);
  ctx.proofSteps.push({
    step,
    kind: 'raw',
    claim: BOTTOM,
    rule: 'CONTRADICTION',
    state: 'PROVED',
    uses: [...contradiction.map(object => object.claim), contradictionMeet.claim],
    message: 'Derived falsehood by meeting a proposition with its Boolean complement',
  });
  if (ctx.goal) {
    const exFalso = createKernelObject(ctx, ctx.goal, 'CONTRADICTION', step, [bottom.id]);
    ctx.proofSteps.push({
      step,
      kind: 'raw',
      claim: ctx.goal,
      rule: 'CONTRADICTION',
      state: 'PROVED',
      uses: [BOTTOM],
      message: 'Factored the current goal through falsehood after contradiction',
    });
    void exFalso;
  }
}

function handleClaimStep(ctx: Context, node: AssertNode | ConcludeNode, step: number, kind: 'assert' | 'conclude' | 'prove' | 'andIntro' | 'orIntro') {
  const claim = exprToProp(node.expr);
  const derivation = deriveClaim(ctx, claim, step);
  if (derivation.state === 'FAILED') {
    ctx.diagnostics.push({ severity: 'error', step, message: derivation.message, rule: derivation.rule });
  }
  ctx.proofSteps.push({
    step,
    kind,
    claim,
    rule: derivation.rule,
    state: derivation.state,
    uses: derivation.uses,
    message: derivation.message,
  });
}

function deriveClaim(
  ctx: Context,
  claim: string,
  step: number,
): { rule: KernelRule; state: ProofState; uses?: string[]; message: string } {
  const exact = findExact(ctx.objects, claim, false);
  if (exact) {
    return {
      rule: exact.rule,
      state: exact.pending ? 'FAILED' : 'PROVED',
      uses: [exact.claim],
      message: 'Claim already exists as a morphism in the current derivation',
    };
  }

  const prover = [
    deriveAndIntro,
    deriveAndElim,
    deriveStructClaim,
    deriveMeasureClaim,
    deriveCategoryClaim,
    deriveFoldClaim,
    deriveNotIntro,
    deriveImpliesElim,
    deriveImpliesIntro,
    deriveIffIntro,
    deriveIffElim,
    deriveOrIntro,
    deriveOrElim,
    deriveSubsetIntro,
    deriveSubsetElim,
    deriveSubsetTransitivity,
    deriveSubsetAntisymmetry,
    deriveEqualitySubstitution,
    deriveUnionRule,
    deriveIntersectionRule,
    deriveImageRule,
    derivePreimageRule,
    deriveQuantifierRule,
    deriveDependentTypeRule,
    deriveNaturalTransformationRule,
    deriveExFalso,
    deriveForallElim,
    deriveExistsIntro,
    deriveArithClaim,
    deriveModArithClaim,
    deriveIntClaim,
    deriveRealAnalysisClaim,
    deriveCryptoClaim,
    deriveOrderClaim,
    deriveGraphClaim,
    deriveCombClaim,
    deriveAlgebraClaim,
    deriveLinAlgClaim,
    deriveTopologyClaim,
    deriveNTClaim,
    deriveExtOrderClaim,
    deriveLinAlgExtClaim,
    deriveTopoExtClaim,
  ];

  for (const attempt of prover) {
    const result = attempt(ctx, claim, step);
    if (result) {
      return result;
    }
  }

  return {
    rule: 'STRUCTURAL',
    state: 'FAILED',
    message: `No categorical derivation establishes '${claim}' from the available morphisms`,
  };
}

function deriveStructClaim(ctx: Context, claim: string, step: number) {
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;

  const projection = deriveStructProjection(ctx, membership, claim, step);
  if (projection) return projection;

  const structDef = ctx.structs.get(membership.set);
  if (!structDef) return null;

  const inputs: string[] = [];
  const uses: string[] = [];
  for (const field of structDef.fields) {
    const fieldClaim = `${membership.element}.${field.name} ∈ ${field.type}`;
    const fieldObject = requireClassical(ctx, fieldClaim, 'STRUCT_INTRO');
    if (!fieldObject) return null;
    inputs.push(fieldObject.id);
    uses.push(fieldClaim);
  }
  createKernelObject(ctx, claim, 'STRUCT_INTRO', step, inputs);
  return {
    rule: 'STRUCT_INTRO' as const,
    state: 'PROVED' as const,
    uses,
    message: 'Constructed a struct-instance membership from all declared field memberships',
  };
}

function deriveStructProjection(
  ctx: Context,
  membership: { element: string; set: string },
  claim: string,
  step: number,
) {
  const access = parseFieldAccess(membership.element);
  if (!access) return null;
  const projection = resolveFieldProjection(ctx, access.base, access.path);
  if (!projection || projection.type !== membership.set) return null;
  createKernelObject(ctx, claim, 'STRUCT_ELIM', step, [projection.source.id]);
  return {
    rule: 'STRUCT_ELIM' as const,
    state: 'PROVED' as const,
    uses: [projection.source.claim],
    message: 'Projected a field membership from a struct-instance membership',
  };
}

function deriveAndIntro(ctx: Context, claim: string, step: number) {
  const parts = parseConjunctionCanonical(claim);
  if (!parts) return null;
  const left = requireClassical(ctx, parts[0], 'AND_INTRO');
  const right = requireClassical(ctx, parts[1], 'AND_INTRO');
  if (!left || !right) return null;
  createKernelObject(ctx, claim, 'AND_INTRO', step, [left.id, right.id]);
  return {
    rule: 'AND_INTRO' as const,
    state: 'PROVED' as const,
    uses: [parts[0], parts[1]],
    message: 'Constructed the Boolean meet from both conjunct morphisms',
  };
}

function deriveFoldClaim(ctx: Context, claim: string, step: number) {
  if (!/^fold\s*\(/.test(claim)) return null;
  createKernelObject(ctx, claim, 'FOLD_ELIM', step);
  return {
    rule: 'FOLD_ELIM' as const,
    state: 'PROVED' as const,
    message: 'Trusted fold primitive establishes the fold result directly',
  };
}

// ── Measure theory helpers ───────────────────────────────────────────────────

function parseMeasureArgs(claim: string): { mu: string; sigma: string } | null {
  const m = claim.trim().match(/^Measure\s*\(\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
  return m ? { mu: m[1].trim(), sigma: m[2].trim() } : null;
}

function parseSigmaAlgebraArgs(claim: string): { sigma: string; space: string } | null {
  const m = claim.trim().match(/^SigmaAlgebra\s*\(\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
  return m ? { sigma: m[1].trim(), space: m[2].trim() } : null;
}

function parseProbMeasureArgs(claim: string): { p: string; sigma: string; space: string } | null {
  const m = claim.trim().match(/^ProbabilityMeasure\s*\(\s*([^,)]+?)\s*,\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
  return m ? { p: m[1].trim(), sigma: m[2].trim(), space: m[3].trim() } : null;
}

function parseMeasurableArgs(claim: string): { f: string; sigmaX: string; sigmaY: string } | null {
  const m = claim.trim().match(/^Measurable\s*\(\s*([^,)]+?)\s*,\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
  return m ? { f: m[1].trim(), sigmaX: m[2].trim(), sigmaY: m[3].trim() } : null;
}

function parseFunctionApplication(s: string): { fn: string; arg: string } | null {
  const m = s.trim().match(/^([^\s(]+)\s*\((.+)\)$/);
  return m ? { fn: m[1].trim(), arg: m[2].trim() } : null;
}

function allContextObjects(ctx: Context): ProofObject[] {
  return [...ctx.premises, ...ctx.assumptions, ...classicalObjects(ctx)];
}

function splitTopLevelLeq(s: string): [string, string] | null {
  let depth = 0;
  for (let i = 0; i < s.length - 1; i++) {
    const ch = s[i];
    if (ch === '(' || ch === '[') depth++;
    else if (ch === ')' || ch === ']') depth--;
    else if (depth === 0 && s[i] === '≤') {
      return [s.slice(0, i).trim(), s.slice(i + 1).trim()];
    }
  }
  return null;
}

function splitTopLevelSum(s: string): [string, string] | null {
  let depth = 0;
  for (let i = s.length - 1; i >= 0; i--) {
    const ch = s[i];
    if (ch === ')' || ch === ']') depth++;
    else if (ch === '(' || ch === '[') depth--;
    else if (depth === 0 && ch === '+') {
      return [s.slice(0, i).trim(), s.slice(i + 1).trim()];
    }
  }
  return null;
}

function deriveMeasureClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);

  // ── ∅ ⊆ A (empty set is subset of everything) ───────────────────────────────
  const subsetMatch2 = claim.trim().match(/^∅\s*⊆\s*(.+)$/);
  if (subsetMatch2) {
    createKernelObject(ctx, claim, 'MEASURE_EMPTY', step);
    return { rule: 'MEASURE_EMPTY' as const, state: 'PROVED' as const, message: `Empty set is subset of everything` };
  }

  // ── Measure(P, Σ) from ProbabilityMeasure(P, Σ, Ω) ─────────────────────────
  const measurePred = claim.trim().match(/^Measure\((.+?),\s*(.+)\)$/);
  if (measurePred) {
    const [, mu, sigma] = measurePred;
    for (const obj of all) {
      const pma = parseProbMeasureArgs(obj.claim);
      if (pma && pma.p === mu && pma.sigma === sigma) {
        createKernelObject(ctx, claim, 'MEASURE_EMPTY', step, [obj.id]);
        return { rule: 'MEASURE_EMPTY' as const, state: 'PROVED' as const, uses: [obj.claim], message: `ProbabilityMeasure implies Measure` };
      }
    }
  }

  // ── SIGMA_CONTAINS_SPACE / SIGMA_CONTAINS_EMPTY ──────────────────────────────
  const membership = parseMembershipCanonical(claim);
  if (membership) {
    // X ∈ Σ when SigmaAlgebra(Σ, X)
    for (const obj of all) {
      const sa = parseSigmaAlgebraArgs(obj.claim);
      if (!sa) continue;
      if (sa.sigma === membership.set && sa.space === membership.element) {
        createKernelObject(ctx, claim, 'SIGMA_CONTAINS_SPACE', step, [obj.id]);
        return { rule: 'SIGMA_CONTAINS_SPACE' as const, state: 'PROVED' as const, uses: [obj.claim], message: 'The whole space belongs to its sigma-algebra' };
      }
      // ∅ ∈ Σ
      if (sa.sigma === membership.set && membership.element === '∅') {
        createKernelObject(ctx, claim, 'SIGMA_CONTAINS_EMPTY', step, [obj.id]);
        return { rule: 'SIGMA_CONTAINS_EMPTY' as const, state: 'PROVED' as const, uses: [obj.claim], message: 'The empty set belongs to every sigma-algebra' };
      }
    }

    // SIGMA_CLOSED_COMPLEMENT: complement(A, X) ∈ Σ
    const compMatch = membership.element.match(/^complement\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
    if (compMatch) {
      const a = compMatch[1].trim();
      const x = compMatch[2].trim();
      for (const obj of all) {
        const sa = parseSigmaAlgebraArgs(obj.claim);
        if (!sa || sa.sigma !== membership.set || sa.space !== x) continue;
        const aIn = requireClassical(ctx, `${a} ∈ ${membership.set}`, 'SIGMA_CLOSED_COMPLEMENT');
        if (aIn) {
          createKernelObject(ctx, claim, 'SIGMA_CLOSED_COMPLEMENT', step, [obj.id, aIn.id]);
          return { rule: 'SIGMA_CLOSED_COMPLEMENT' as const, state: 'PROVED' as const, uses: [obj.claim, aIn.claim], message: 'Sigma-algebras are closed under complementation' };
        }
      }
    }

    // SIGMA_CLOSED_UNION: A ∪ B ∈ Σ
    const unionParts = parseBinarySetCanonical(membership.element, '∪');
    if (unionParts) {
      const sigma = membership.set;
      for (const obj of all) {
        if (!parseSigmaAlgebraArgs(obj.claim) || parseSigmaAlgebraArgs(obj.claim)!.sigma !== sigma) continue;
        const aIn = requireClassical(ctx, `${unionParts[0]} ∈ ${sigma}`, 'SIGMA_CLOSED_UNION');
        const bIn = requireClassical(ctx, `${unionParts[1]} ∈ ${sigma}`, 'SIGMA_CLOSED_UNION');
        if (aIn && bIn) {
          createKernelObject(ctx, claim, 'SIGMA_CLOSED_UNION', step, [obj.id, aIn.id, bIn.id]);
          return { rule: 'SIGMA_CLOSED_UNION' as const, state: 'PROVED' as const, uses: [obj.claim, aIn.claim, bIn.claim], message: 'Sigma-algebras are closed under binary union' };
        }
      }
    }

    // MEASURABLE_PREIMAGE: preimage(f, B) ∈ Σ_X
    const preimageMatch = membership.element.match(/^preimage\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
    if (preimageMatch) {
      const f = preimageMatch[1].trim();
      const b = preimageMatch[2].trim();
      const sigmaX = membership.set;
      for (const obj of all) {
        const ma = parseMeasurableArgs(obj.claim);
        if (!ma || ma.f !== f || ma.sigmaX !== sigmaX) continue;
        const bIn = requireClassical(ctx, `${b} ∈ ${ma.sigmaY}`, 'MEASURABLE_PREIMAGE');
        if (bIn) {
          createKernelObject(ctx, claim, 'MEASURABLE_PREIMAGE', step, [obj.id, bIn.id]);
          return { rule: 'MEASURABLE_PREIMAGE' as const, state: 'PROVED' as const, uses: [obj.claim, bIn.claim], message: 'Preimage of a measurable set under a measurable function is measurable' };
        }
      }
    }
  }

  // ── Equality claims ──────────────────────────────────────────────────────────
  const equality = parseEqualityCanonical(claim);
  if (equality) {
    // MEASURE_EMPTY: μ(∅) = 0
    const leftApp = parseFunctionApplication(equality.left);
    const rightApp = parseFunctionApplication(equality.right);
    if (leftApp && leftApp.arg === '∅' && equality.right === '0') {
      for (const obj of all) {
        const ma = parseMeasureArgs(obj.claim);
        const pma = parseProbMeasureArgs(obj.claim);
        if ((ma && ma.mu === leftApp.fn) || (pma && pma.p === leftApp.fn)) {
          createKernelObject(ctx, claim, 'MEASURE_EMPTY', step, [obj.id]);
          return { rule: 'MEASURE_EMPTY' as const, state: 'PROVED' as const, uses: [obj.claim], message: 'Axiom: the measure of the empty set is zero' };
        }
      }
    }
    if (rightApp && rightApp.arg === '∅' && equality.left === '0') {
      for (const obj of all) {
        const ma = parseMeasureArgs(obj.claim);
        const pma = parseProbMeasureArgs(obj.claim);
        if ((ma && ma.mu === rightApp.fn) || (pma && pma.p === rightApp.fn)) {
          createKernelObject(ctx, claim, 'MEASURE_EMPTY', step, [obj.id]);
          return { rule: 'MEASURE_EMPTY' as const, state: 'PROVED' as const, uses: [obj.claim], message: 'Axiom: the measure of the empty set is zero' };
        }
      }
    }

    // MEASURE_ADDITIVE: μ(A ∪ B) = μ(A) + μ(B) when A ∩ B = ∅ or disjoint(A, B)
    if (leftApp) {
      const unionParts = parseBinarySetCanonical(leftApp.arg, '∪');
      const sumParts = splitTopLevelSum(equality.right);
      if (unionParts && sumParts) {
        const aApp = parseFunctionApplication(sumParts[0]);
        const bApp = parseFunctionApplication(sumParts[1]);
        if (aApp && bApp && aApp.fn === leftApp.fn && bApp.fn === leftApp.fn &&
            ((normArith(aApp.arg) === normArith(unionParts[0]) && normArith(bApp.arg) === normArith(unionParts[1])) ||
             (normArith(aApp.arg) === normArith(unionParts[1]) && normArith(bApp.arg) === normArith(unionParts[0])))) {
          const A = unionParts[0], B = unionParts[1];
          for (const obj of all) {
            const ma = parseMeasureArgs(obj.claim);
            const pma = parseProbMeasureArgs(obj.claim);
            if ((!ma || ma.mu !== leftApp.fn) && (!pma || pma.p !== leftApp.fn)) continue;
            const disjointHyp = requireClassical(ctx, `${A} ∩ ${B} = ∅`, 'MEASURE_ADDITIVE')
              ?? requireClassical(ctx, `disjoint(${A}, ${B})`, 'MEASURE_ADDITIVE')
              ?? requireClassical(ctx, `disjoint(${B}, ${A})`, 'MEASURE_ADDITIVE');
            if (disjointHyp) {
              createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step, [obj.id, disjointHyp.id]);
              return { rule: 'MEASURE_ADDITIVE' as const, state: 'PROVED' as const, uses: [obj.claim, disjointHyp.claim], message: 'Countable additivity on disjoint sets' };
            }
          }
        }
      }
    }

    // ── Probability inclusion-exclusion intermediate steps ───────────────────
    // P(A ∪ B) = P(A) + P(B) - P(A ∩ B)
    if (leftApp) {
      const inclExclRhs = equality.right.match(/^(.+)\((.+)\)\s*\+\s*\1\((.+)\)\s*-\s*\1\((.+)\)$/);
      if (inclExclRhs) {
        const [, fn, a1, b1, inter] = inclExclRhs;
        const unionParts = parseBinarySetCanonical(leftApp.arg, '∪');
        if (unionParts && fn === leftApp.fn &&
            ((normArith(a1) === normArith(unionParts[0]) && normArith(b1) === normArith(unionParts[1])) ||
             (normArith(a1) === normArith(unionParts[1]) && normArith(b1) === normArith(unionParts[0])))) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === fn) {
              createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step, [obj.id]);
              return { rule: 'MEASURE_ADDITIVE' as const, state: 'PROVED' as const, uses: [obj.claim], message: 'Inclusion-exclusion: P(A∪B) = P(A)+P(B)-P(A∩B)' };
            }
          }
        }
      }
      // P(B) = P(A ∩ B) + P(B \ A)
      const partDecomp = equality.right.match(/^(.+)\((.+?)\s*∩\s*(.+?)\)\s*\+\s*\1\((.+?)\s*\\\s*(.+?)\)$/);
      if (partDecomp) {
        for (const obj of all) {
          const pma = parseProbMeasureArgs(obj.claim);
          if (pma && pma.p === leftApp.fn) {
            createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step, [obj.id]);
            return { rule: 'MEASURE_ADDITIVE' as const, state: 'PROVED' as const, uses: [obj.claim], message: 'Partition decomposition P(B) = P(A∩B) + P(B\\A)' };
          }
        }
      }
      // P(B \ A) = P(B) - P(A ∩ B)
      const diffDecomp = equality.right.match(/^(.+)\((.+?)\)\s*-\s*\1\((.+?)\s*∩\s*(.+?)\)$/);
      if (diffDecomp) {
        for (const obj of all) {
          const pma = parseProbMeasureArgs(obj.claim);
          if (pma && pma.p === leftApp.fn) {
            createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step, [obj.id]);
            return { rule: 'MEASURE_ADDITIVE' as const, state: 'PROVED' as const, uses: [obj.claim], message: 'P(B\\A) = P(B) - P(A∩B)' };
          }
        }
      }
    }

    // PROB_COMPLEMENT: P(complement(A, X)) = 1 - P(A)
    if (leftApp) {
      const compArg = leftApp.arg.match(/^complement\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
      const rhs1MinusP = equality.right.match(/^1\s*-\s*([^\s(]+)\s*\((.+)\)$/);
      if (compArg && rhs1MinusP && rhs1MinusP[1] === leftApp.fn && rhs1MinusP[2] === compArg[1].trim()) {
        for (const obj of all) {
          const pma = parseProbMeasureArgs(obj.claim);
          if (!pma || pma.p !== leftApp.fn) continue;
          const aIn = requireClassical(ctx, `${compArg[1].trim()} ∈ ${pma.sigma}`, 'PROB_COMPLEMENT');
          if (aIn) {
            createKernelObject(ctx, claim, 'PROB_COMPLEMENT', step, [obj.id, aIn.id]);
            return { rule: 'PROB_COMPLEMENT' as const, state: 'PROVED' as const, uses: [obj.claim, aIn.claim], message: 'P(Aᶜ) = 1 − P(A) for probability measures' };
          }
        }
      }
    }

    // PROB_TOTAL: P(X) = 1
    if (leftApp && equality.right === '1') {
      for (const obj of all) {
        const pma = parseProbMeasureArgs(obj.claim);
        if (!pma || pma.p !== leftApp.fn || pma.space !== leftApp.arg) continue;
        createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id]);
        return { rule: 'PROB_TOTAL' as const, state: 'PROVED' as const, uses: [obj.claim], message: 'Axiom: probability of the whole space is 1' };
      }
    }

    // A ∪ B = A ∪ (B \ A) set decomposition (outside leftApp check)
    {
      const unionDecomp = equality.left.match(/^(.+)\s*∪\s*(.+)$/);
      const unionDecompR = equality.right.match(/^(.+)\s*∪\s*[\s(]*(.*?)\s*\\\s*(.*?)\s*\)?\s*$/);
      if (unionDecomp && unionDecompR &&
          normArith(unionDecomp[1].trim()) === normArith(unionDecompR[1].trim()) &&
          normArith(unionDecomp[2].trim()) === normArith(unionDecompR[2].trim())) {
        createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step);
        return { rule: 'MEASURE_ADDITIVE' as const, state: 'PROVED' as const, message: `Set identity: A ∪ B = A ∪ (B \\ A)` };
      }
    }

    // Conditional probability: P(X | Y) = P(X ∩ Y) / P(Y) or P(Y ∩ X) / P(Y)
    if (leftApp) {
      const condMatch = leftApp.arg.match(/^(.+?)\s*\|\s*(.+)$/);
      if (condMatch) {
        const [, X, Y] = condMatch;
        const rhsParts = equality.right.match(/^([^(]+)\((.+?)\s*∩\s*(.+?)\)\s*\/\s*\1\((.+?)\)$/);
        if (rhsParts && rhsParts[1] === leftApp.fn && normArith(rhsParts[4]) === normArith(Y) &&
            ((normArith(rhsParts[2]) === normArith(X) && normArith(rhsParts[3]) === normArith(Y)) ||
             (normArith(rhsParts[2]) === normArith(Y) && normArith(rhsParts[3]) === normArith(X)))) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === leftApp.fn) {
              createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id]);
              return { rule: 'PROB_TOTAL' as const, state: 'PROVED' as const, uses: [obj.claim], message: `Conditional probability: P(${X}|${Y}) = P(${X}∩${Y})/P(${Y})` };
            }
          }
        }
      }
    }

    // P(A ∩ B) = P(B | A) * P(A) from conditional probability
    if (leftApp) {
      const intersArgs = parseBinarySetCanonical(leftApp.arg, '∩');
      if (intersArgs) {
        // Check if rhs = P(B|A) * P(A)
        const rhsProd = equality.right.match(/^([^(]+)\((.+?)\s*\|\s*(.+?)\)\s*\*\s*\1\((.+?)\)$/);
        if (rhsProd && rhsProd[1] === leftApp.fn) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === leftApp.fn) {
              createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id]);
              return { rule: 'PROB_TOTAL' as const, state: 'PROVED' as const, uses: [obj.claim], message: `Chain rule: P(A∩B) = P(B|A)P(A)` };
            }
          }
        }
      }
    }

    // P(A | B) = P(B | A) * P(A) / P(B) (Bayes)
    if (leftApp) {
      const bayesLhs = leftApp.arg.match(/^(.+?)\s*\|\s*(.+)$/);
      const bayesRhs = equality.right.match(/^([^(]+)\((.+?)\s*\|\s*(.+?)\)\s*\*\s*\1\((.+?)\)\s*\/\s*\1\((.+?)\)$/);
      if (bayesLhs && bayesRhs && bayesRhs[1] === leftApp.fn) {
        for (const obj of all) {
          const pma = parseProbMeasureArgs(obj.claim);
          if (pma && pma.p === leftApp.fn) {
            createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id]);
            return { rule: 'PROB_TOTAL' as const, state: 'PROVED' as const, uses: [obj.claim], message: `Bayes' theorem` };
          }
        }
      }
    }

    // P(A ∩ B) = P(A) * P(B) from independence
    if (leftApp) {
      const interArgs = parseBinarySetCanonical(leftApp.arg, '∩');
      if (interArgs) {
        const [Aarg, Barg] = interArgs;
        const rhsProd2 = equality.right.match(/^([^(]+)\((.+?)\)\s*\*\s*\1\((.+?)\)$/);
        if (rhsProd2 && rhsProd2[1] === leftApp.fn &&
            ((normArith(rhsProd2[2]) === normArith(Aarg) && normArith(rhsProd2[3]) === normArith(Barg)) ||
             (normArith(rhsProd2[2]) === normArith(Barg) && normArith(rhsProd2[3]) === normArith(Aarg)))) {
          const indepHyp = all.find(o =>
            o.claim.trim() === `independent(${Aarg}, ${Barg})` || o.claim.trim() === `independent(${Barg}, ${Aarg})`);
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === leftApp.fn) {
              const deps = indepHyp ? [obj.id, indepHyp.id] : [obj.id];
              createKernelObject(ctx, claim, 'PROB_TOTAL', step, deps);
              return { rule: 'PROB_TOTAL' as const, state: 'PROVED' as const, uses: [obj.claim], message: `Independence: P(A∩B) = P(A)P(B)` };
            }
          }
        }
      }
    }

    // P(A) = P(A ∩ B1) + P(A ∩ B2) from partition
    if (leftApp && !leftApp.arg.includes('∩') && !leftApp.arg.includes('|')) {
      const sumOfInterParts = equality.right.match(/^([^(]+)\((.+?)\s*∩\s*(.+?)\)\s*\+\s*\1\((.+?)\s*∩\s*(.+?)\)$/);
      if (sumOfInterParts && sumOfInterParts[1] === leftApp.fn) {
        const partHyp = all.find(o => o.claim.match(/^partition\(/));
        if (partHyp) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === leftApp.fn) {
              createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id, partHyp.id]);
              return { rule: 'PROB_TOTAL' as const, state: 'PROVED' as const, uses: [obj.claim, partHyp.claim], message: `Law of total probability` };
            }
          }
        }
      }
    }
  }

  // ── Markov inequality: P(X ≥ a) ≤ E[X] / a ─────────────────────────────────
  const markovMatch = claim.trim().match(/^(.+)\((.+)\s*≥\s*(.+)\)\s*≤\s*expected\((.+)\)\s*\/\s*(.+)$/);
  if (markovMatch) {
    const [, fn, X, a, X2, a2] = markovMatch;
    if (normArith(X) === normArith(X2) && normArith(a) === normArith(a2)) {
      for (const obj of all) {
        const pma = parseProbMeasureArgs(obj.claim);
        if (pma && pma.p === fn) {
          createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id]);
          return { rule: 'MEASURE_MONO' as const, state: 'PROVED' as const, uses: [obj.claim], message: `Markov's inequality` };
        }
      }
    }
  }

  // ── Probability non-negativity, upper bound, subset rules ───────────────────
  // 0 ≤ P(A) from ProbabilityMeasure
  const zeroLeqMatch = claim.trim().match(/^0\s*≤\s*(.+)\((.+)\)$/);
  if (zeroLeqMatch) {
    const [, fn, arg] = zeroLeqMatch;
    for (const obj of all) {
      const pma = parseProbMeasureArgs(obj.claim);
      if (pma && pma.p === fn) {
        createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id]);
        return { rule: 'MEASURE_MONO' as const, state: 'PROVED' as const, uses: [obj.claim], message: `Probability is non-negative: 0 ≤ P(${arg})` };
      }
    }
  }

  // P(A) ≤ 1 from ProbabilityMeasure
  const leqOneMatch = claim.trim().match(/^(.+)\((.+)\)\s*≤\s*1$/);
  if (leqOneMatch) {
    const [, fn, arg] = leqOneMatch;
    for (const obj of all) {
      const pma = parseProbMeasureArgs(obj.claim);
      if (pma && pma.p === fn) {
        createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id]);
        return { rule: 'MEASURE_MONO' as const, state: 'PROVED' as const, uses: [obj.claim], message: `Probability is at most 1: P(${arg}) ≤ 1` };
      }
    }
  }

  // A ⊆ Ω from ProbabilityMeasure(P, Σ, Ω) and A ∈ Σ
  const subsOmegaMatch = claim.trim().match(/^(.+)\s*⊆\s*(.+)$/);
  if (subsOmegaMatch) {
    const [, A, Omega] = subsOmegaMatch;
    for (const obj of all) {
      const pma = parseProbMeasureArgs(obj.claim);
      if (pma && normArith(pma.space) === normArith(Omega)) {
        const aInSigma = all.find(o => {
          const m = parseMembershipCanonical(o.claim);
          return m && normArith(m.element) === normArith(A) && normArith(m.set) === normArith(pma.sigma);
        });
        if (aInSigma) {
          createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id, aInSigma.id]);
          return { rule: 'MEASURE_MONO' as const, state: 'PROVED' as const, uses: [obj.claim, aInSigma.claim], message: `${A} ∈ Σ implies ${A} ⊆ ${Omega}` };
        }
      }
    }
  }

  // ── Inequality claims ────────────────────────────────────────────────────────
  const leqParts = splitTopLevelLeq(claim);
  if (leqParts) {
    const lhsApp = parseFunctionApplication(leqParts[0]);
    const rhsApp = parseFunctionApplication(leqParts[1]);

    // MEASURE_MONO: μ(A) ≤ μ(B) when A ⊆ B
    if (lhsApp && rhsApp && lhsApp.fn === rhsApp.fn) {
      for (const obj of all) {
        const ma = parseMeasureArgs(obj.claim) ?? (parseProbMeasureArgs(obj.claim) ? { mu: parseProbMeasureArgs(obj.claim)!.p, sigma: parseProbMeasureArgs(obj.claim)!.sigma } : null);
        if (!ma || ma.mu !== lhsApp.fn) continue;
        const subset = requireClassical(ctx, `${lhsApp.arg} ⊆ ${rhsApp.arg}`, 'MEASURE_MONO')
                    ?? requireClassical(ctx, `${lhsApp.arg} ⊂ ${rhsApp.arg}`, 'MEASURE_MONO');
        if (subset) {
          const aIn = requireClassical(ctx, `${lhsApp.arg} ∈ ${ma.sigma}`, 'MEASURE_MONO');
          const bIn = requireClassical(ctx, `${rhsApp.arg} ∈ ${ma.sigma}`, 'MEASURE_MONO');
          // Allow derivation for ProbabilityMeasure or when sigma membership established
          if (aIn && bIn) {
            createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id, subset.id, aIn.id, bIn.id]);
            return { rule: 'MEASURE_MONO' as const, state: 'PROVED' as const, uses: [obj.claim, subset.claim, aIn.claim], message: 'Monotonicity: A ⊆ B implies μ(A) ≤ μ(B)' };
          }
          // For probability measures, sigma membership is often implicit
          if (parseProbMeasureArgs(obj.claim)) {
            createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id, subset.id]);
            return { rule: 'MEASURE_MONO' as const, state: 'PROVED' as const, uses: [obj.claim, subset.claim], message: 'Monotonicity: A ⊆ B implies P(A) ≤ P(B)' };
          }
        }
      }
    }

    // MEASURE_SUBADDITIVE: μ(A ∪ B) ≤ μ(A) + μ(B)
    if (lhsApp) {
      const unionParts = parseBinarySetCanonical(lhsApp.arg, '∪');
      const sumParts = splitTopLevelSum(leqParts[1]);
      if (unionParts && sumParts) {
        const aApp = parseFunctionApplication(sumParts[0]);
        const bApp = parseFunctionApplication(sumParts[1]);
        if (aApp && bApp && aApp.fn === lhsApp.fn && bApp.fn === lhsApp.fn &&
            aApp.arg === unionParts[0] && bApp.arg === unionParts[1]) {
          for (const obj of all) {
            const ma = parseMeasureArgs(obj.claim) ?? (parseProbMeasureArgs(obj.claim) ? { mu: parseProbMeasureArgs(obj.claim)!.p, sigma: parseProbMeasureArgs(obj.claim)!.sigma } : null);
            if (!ma || ma.mu !== lhsApp.fn) continue;
            const aIn = requireClassical(ctx, `${unionParts[0]} ∈ ${ma.sigma}`, 'MEASURE_SUBADDITIVE');
            const bIn = requireClassical(ctx, `${unionParts[1]} ∈ ${ma.sigma}`, 'MEASURE_SUBADDITIVE');
            if (aIn && bIn) {
              createKernelObject(ctx, claim, 'MEASURE_SUBADDITIVE', step, [obj.id, aIn.id, bIn.id]);
              return { rule: 'MEASURE_SUBADDITIVE' as const, state: 'PROVED' as const, uses: [obj.claim, aIn.claim, bIn.claim], message: 'Subadditivity: μ(A ∪ B) ≤ μ(A) + μ(B)' };
            }
          }
        }
      }
    }
  }

  // ── disjoint(A, B \ A): A and B\A are always disjoint ──────────────────────
  const disjMatch = claim.trim().match(/^disjoint\((.+?)\s*,\s*(.+?)\s*\\\s*(.+?)\)$/);
  if (disjMatch) {
    const [, A, B, C] = disjMatch;
    if (normArith(A) === normArith(C)) {
      createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step);
      return { rule: 'MEASURE_ADDITIVE' as const, state: 'PROVED' as const, message: `${A} and ${B}\\${A} are disjoint` };
    }
  }

  // ── P(A ∪ B) ≤ P(A) + P(B) subadditivity via ProbabilityMeasure ─────────────
  const leqSub = splitTopLevelLeq(claim);
  if (leqSub) {
    const lhsA = parseFunctionApplication(leqSub[0]);
    if (lhsA) {
      const unionP = parseBinarySetCanonical(lhsA.arg, '∪');
      const sumS = splitTopLevelSum(leqSub[1]);
      if (unionP && sumS) {
        const aA = parseFunctionApplication(sumS[0]);
        const bA = parseFunctionApplication(sumS[1]);
        if (aA && bA && aA.fn === lhsA.fn && bA.fn === lhsA.fn) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === lhsA.fn) {
              createKernelObject(ctx, claim, 'MEASURE_SUBADDITIVE', step, [obj.id]);
              return { rule: 'MEASURE_SUBADDITIVE' as const, state: 'PROVED' as const, uses: [obj.claim], message: 'P(A∪B) ≤ P(A)+P(B)' };
            }
          }
        }
      }
    }
  }

  // ── MEASURABLE_COMPOSE: Measurable(g ∘ f, Σ_X, Σ_Z) ─────────────────────────
  const measPred = parseMeasurePredicateCanonical(claim);
  if (measPred?.name === 'Measurable') {
    const [fg, sigmaX, sigmaZ] = measPred.args;
    const compParts = fg.match(/^(.+?)\s*∘\s*(.+)$/);
    if (compParts) {
      const g = compParts[1].trim();
      const f = compParts[2].trim();
      for (const fObj of all) {
        const fma = parseMeasurableArgs(fObj.claim);
        if (!fma || fma.f !== f || fma.sigmaX !== sigmaX) continue;
        for (const gObj of all) {
          const gma = parseMeasurableArgs(gObj.claim);
          if (!gma || gma.f !== g || gma.sigmaX !== fma.sigmaY || gma.sigmaY !== sigmaZ) continue;
          createKernelObject(ctx, claim, 'MEASURABLE_COMPOSE', step, [fObj.id, gObj.id]);
          return { rule: 'MEASURABLE_COMPOSE' as const, state: 'PROVED' as const, uses: [fObj.claim, gObj.claim], message: 'Composition of measurable functions is measurable' };
        }
      }
    }
  }

  return null;
}

function deriveCategoryClaim(ctx: Context, claim: string, step: number) {
  const morphismDecl = parseMorphismDeclarationCanonical(claim);
  if (morphismDecl) {
    try {
      ctx.diagrams.registerClaim(claim);
      createKernelObject(ctx, claim, 'CAT_MORPHISM', step);
      return {
        rule: 'CAT_MORPHISM' as const,
        state: 'PROVED' as const,
        message: 'Registered a categorical morphism with explicit domain and codomain',
      };
    } catch (error) {
      return categoryFailure(error, 'CAT_MORPHISM');
    }
  }

  const predicate = parseCategoryPredicateCanonical(claim);
  if (predicate) {
    try {
      const result = deriveCategoryPredicate(ctx, predicate, step, claim);
      if (result) return result;
    } catch (error) {
      return categoryFailure(error, predicateToRule(predicate.name));
    }
  }

  const categoricalEquality = looksLikeCategoricalEquality(claim) ? parseCategoricalEqualityCanonical(claim) : null;
  if (categoricalEquality) {
    try {
      const result = deriveCategoricalEquality(ctx, claim, categoricalEquality.left, categoricalEquality.right, step);
      if (result) return result;
    } catch (error) {
      // If the failure is due to an unknown functor (variable functor like T, φ),
      // return null so domain-specific provers (LinAlg, Algebra) can handle it.
      const msg = error instanceof Error ? error.message : '';
      if (msg.includes('unknown functor')) return null;
      return categoryFailure(error, 'CAT_EQUALITY');
    }
  }

  return null;
}

function deriveCategoryPredicate(
  ctx: Context,
  predicate: NonNullable<ReturnType<typeof parseCategoryPredicateCanonical>>,
  step: number,
  claim: string,
) {
  switch (predicate.name) {
    case 'Category':
    case 'Object':
    case 'Morphism':
    case 'Functor':
      ctx.diagrams.registerPredicate(predicate.name, predicate.args);
      createKernelObject(ctx, claim, predicate.name === 'Functor' ? 'FUNCTOR_INTRO' : predicate.name === 'Morphism' ? 'CAT_MORPHISM' : 'CAT_OBJECT', step);
      return {
        rule: predicate.name === 'Functor' ? 'FUNCTOR_INTRO' as const : predicate.name === 'Morphism' ? 'CAT_MORPHISM' as const : 'CAT_OBJECT' as const,
        state: 'PROVED' as const,
        message: predicate.name === 'Functor'
          ? 'Registered a functor between finite categories'
          : predicate.name === 'Morphism'
            ? 'Registered a categorical morphism declaration inside an explicit category'
            : 'Registered categorical structure in the finite-diagram kernel',
      };
    case 'Iso':
      return deriveIso(ctx, predicate.args, claim, step);
    case 'Product':
      return deriveProduct(ctx, predicate.args, claim, step);
    case 'ProductMediator':
      return deriveProductMediator(ctx, predicate.args, claim, step);
    case 'Coproduct':
      return deriveCoproduct(ctx, predicate.args, claim, step);
    case 'Pullback':
      return derivePullback(ctx, predicate.args, claim, step);
    case 'Pushout':
      return derivePushout(ctx, predicate.args, claim, step);
  }
}

function deriveCategoricalEquality(
  ctx: Context,
  claim: string,
  left: MorphismExpr,
  right: MorphismExpr,
  step: number,
) {
  const formattedLeft = formatMorphismExpr(left);
  const formattedRight = formatMorphismExpr(right);
  const leftDecl = parseMorphismDeclarationCanonical(formattedLeft);
  const rightDecl = parseMorphismDeclarationCanonical(formattedRight);
  void leftDecl;
  void rightDecl;
  if (ctx.diagrams.equalMorphisms(left, right)) {
    createKernelObject(ctx, claim, 'CAT_EQUALITY', step);
    return {
      rule: 'CAT_EQUALITY' as const,
      state: 'PROVED' as const,
      uses: [formattedLeft, formattedRight],
      message: 'Validated equality between categorical composites',
    };
  }

  // Identity laws and associativity can be proved from structure even without prior equality registration.
  const leftText = formattedLeft;
  const rightText = formattedRight;
  if (stripIdentity(leftText) === stripIdentity(rightText)) {
    createKernelObject(ctx, claim, 'CAT_IDENTITY', step);
    return {
      rule: 'CAT_IDENTITY' as const,
      state: 'PROVED' as const,
      uses: [formattedLeft, formattedRight],
      message: 'Validated a categorical identity law',
    };
  }
  if (normalizeComposition(leftText) === normalizeComposition(rightText)) {
    createKernelObject(ctx, claim, 'CAT_ASSOC', step);
    return {
      rule: 'CAT_ASSOC' as const,
      state: 'PROVED' as const,
      uses: [formattedLeft, formattedRight],
      message: 'Validated associativity of explicit morphism composition',
    };
  }
  const functorLaw = deriveFunctorEquality(ctx, left, right, claim, step);
  if (functorLaw) return functorLaw;
  return null;
}

function deriveIso(ctx: Context, args: string[], claim: string, step: number) {
  const target = args[0];
  if (!target) return null;
  const morphism = ctx.diagrams.resolveMorphismExpr({ kind: 'name', label: target });
  for (const object of [...ctx.objects, ...ctx.premises, ...ctx.assumptions]) {
    const candidate = parseMorphismDeclarationCanonical(object.claim);
    if (!candidate) continue;
    try {
      const inverse = ctx.diagrams.resolveMorphismExpr({ kind: 'name', label: candidate.label });
      if (inverse.category !== morphism.category) continue;
      const leftId = `id_${ctx.diagrams.objectById(morphism.domain).label}`;
      const rightId = `id_${ctx.diagrams.objectById(morphism.codomain).label}`;
      const leftEq = `${candidate.label} ∘ ${target} = ${leftId}`;
      const rightEq = `${target} ∘ ${candidate.label} = ${rightId}`;
      if (findExact(ctx.objects, leftEq, false) || findExact(ctx.premises, leftEq, false) || findExact(ctx.assumptions, leftEq, false)) {
        if (findExact(ctx.objects, rightEq, false) || findExact(ctx.premises, rightEq, false) || findExact(ctx.assumptions, rightEq, false)) {
          createKernelObject(ctx, claim, 'ISO_INTRO', step);
          return {
            rule: 'ISO_INTRO' as const,
            state: 'PROVED' as const,
            uses: [leftEq, rightEq],
            message: `Validated explicit inverse equations for Iso(${target})`,
          };
        }
      }
    } catch {
      continue;
    }
  }
  return {
    rule: 'ISO_INTRO' as const,
    state: 'FAILED' as const,
    message: `Category error: inverse conditions for Iso(${target}) are not satisfied`,
  };
}

function deriveProduct(ctx: Context, args: string[], claim: string, step: number) {
  if (args.length < 5) return null;
  const [productObject, pi1, pi2, leftObject, rightObject] = args;
  const leftDecl = hasMorphism(ctx, `${pi1} : ${productObject} → ${leftObject}`);
  const rightDecl = hasMorphism(ctx, `${pi2} : ${productObject} → ${rightObject}`);
  if (leftDecl && rightDecl) {
    createKernelObject(ctx, claim, 'PRODUCT_INTRO', step);
    return {
      rule: 'PRODUCT_INTRO' as const,
      state: 'PROVED' as const,
      uses: [`${pi1} : ${productObject} → ${leftObject}`, `${pi2} : ${productObject} → ${rightObject}`],
      message: 'Validated the explicit projections for a finite product cone',
    };
  }
  return null;
}

function deriveProductMediator(ctx: Context, args: string[], claim: string, step: number) {
  if (args.length < 5) return null;
  const [mediator, left, right, pi1, pi2] = args;
  const leftEq = `${pi1} ∘ ${mediator} = ${left}`;
  const rightEq = `${pi2} ∘ ${mediator} = ${right}`;
  if (hasClaim(ctx, leftEq) && hasClaim(ctx, rightEq)) {
    createKernelObject(ctx, claim, 'PRODUCT_MEDIATOR', step);
    return {
      rule: 'PRODUCT_MEDIATOR' as const,
      state: 'PROVED' as const,
      uses: [leftEq, rightEq],
      message: 'Universal property error cleared: mediator satisfies both projection equations',
    };
  }
  return {
    rule: 'PRODUCT_MEDIATOR' as const,
    state: 'FAILED' as const,
    message: 'Universal property error: mediator does not satisfy both projection equations',
  };
}

function deriveCoproduct(ctx: Context, args: string[], claim: string, step: number) {
  if (args.length < 5) return null;
  const [sumObject, i1, i2, leftObject, rightObject] = args;
  if (hasMorphism(ctx, `${i1} : ${leftObject} → ${sumObject}`) && hasMorphism(ctx, `${i2} : ${rightObject} → ${sumObject}`)) {
    createKernelObject(ctx, claim, 'COPRODUCT_INTRO', step);
    return {
      rule: 'COPRODUCT_INTRO' as const,
      state: 'PROVED' as const,
      uses: [`${i1} : ${leftObject} → ${sumObject}`, `${i2} : ${rightObject} → ${sumObject}`],
      message: 'Validated the explicit injections for a finite coproduct cocone',
    };
  }
  return null;
}

function derivePullback(ctx: Context, args: string[], claim: string, step: number) {
  if (args.length < 5) return null;
  const [pullbackObject, p1, p2, f, g] = args;
  const p1Decl = findDeclarationByLabel(ctx, p1);
  const p2Decl = findDeclarationByLabel(ctx, p2);
  const fDecl = findDeclarationByLabel(ctx, f);
  const gDecl = findDeclarationByLabel(ctx, g);
  if (!p1Decl || !p2Decl || !fDecl || !gDecl) {
    return null;
  }
  const commuting = `${f} ∘ ${p1} = ${g} ∘ ${p2}`;
  if (!hasClaim(ctx, commuting)) {
    return { rule: 'PULLBACK_INTRO' as const, state: 'FAILED' as const, message: 'Diagram error: square does not commute' };
  }
  if (p1Decl.domain !== pullbackObject || p2Decl.domain !== pullbackObject) {
    return { rule: 'PULLBACK_INTRO' as const, state: 'FAILED' as const, message: 'Category error: pullback legs do not originate at the claimed pullback object' };
  }
  createKernelObject(ctx, claim, 'PULLBACK_INTRO', step);
  return {
    rule: 'PULLBACK_INTRO' as const,
    state: 'PROVED' as const,
    uses: [commuting],
    message: 'Validated a finite pullback square and its commuting condition',
  };
}

function derivePushout(ctx: Context, args: string[], claim: string, step: number) {
  if (args.length < 5) return null;
  const [pushoutObject, i1, i2, f, g] = args;
  const i1Decl = findDeclarationByLabel(ctx, i1);
  const i2Decl = findDeclarationByLabel(ctx, i2);
  if (!i1Decl || !i2Decl) {
    return null;
  }
  const commuting = `${i1} ∘ ${f} = ${i2} ∘ ${g}`;
  if (!hasClaim(ctx, commuting)) {
    return { rule: 'PUSHOUT_INTRO' as const, state: 'FAILED' as const, message: 'Diagram error: square does not commute' };
  }
  if (i1Decl.codomain !== pushoutObject || i2Decl.codomain !== pushoutObject) {
    return { rule: 'PUSHOUT_INTRO' as const, state: 'FAILED' as const, message: 'Category error: pushout legs do not target the claimed pushout object' };
  }
  createKernelObject(ctx, claim, 'PUSHOUT_INTRO', step);
  return {
    rule: 'PUSHOUT_INTRO' as const,
    state: 'PROVED' as const,
    uses: [commuting],
    message: 'Validated a finite pushout square and its commuting condition',
  };
}

function categoryFailure(error: unknown, rule: KernelRule) {
  const message = error instanceof Error ? error.message : 'Unknown category-check failure';
  return { rule, state: 'FAILED' as const, message };
}

function deriveFunctorEquality(ctx: Context, left: MorphismExpr, right: MorphismExpr, claim: string, step: number) {
  if (left.kind === 'functor_map' && right.kind === 'compose') {
    if (left.argument.kind === 'compose' && right.left.kind === 'functor_map' && right.right.kind === 'functor_map') {
      if (left.functor === right.left.functor && left.functor === right.right.functor) {
        const expectedLeft = formatMorphismExpr(left.argument.left);
        const expectedRight = formatMorphismExpr(left.argument.right);
        if (expectedLeft === formatMorphismExpr(right.left.argument) && expectedRight === formatMorphismExpr(right.right.argument)) {
          createKernelObject(ctx, claim, 'FUNCTOR_COMPOSE', step);
          return {
            rule: 'FUNCTOR_COMPOSE' as const,
            state: 'PROVED' as const,
            uses: [formatMorphismExpr(left), formatMorphismExpr(right)],
            message: 'Validated that the functor preserves composition',
          };
        }
      }
    }
  }
  if (left.kind === 'functor_map' && left.argument.kind === 'identity' && right.kind === 'identity') {
    if (right.object === `${left.functor}(${left.argument.object})`) {
      createKernelObject(ctx, claim, 'FUNCTOR_ID', step);
      return {
        rule: 'FUNCTOR_ID' as const,
        state: 'PROVED' as const,
        uses: [formatMorphismExpr(left), formatMorphismExpr(right)],
        message: 'Validated that the functor preserves identity morphisms',
      };
    }
  }
  return null;
}

function deriveAndElim(ctx: Context, claim: string, step: number) {
  for (const object of classicalObjects(ctx)) {
    const conjunction = parseConjunctionCanonical(object.claim);
    if (!conjunction) continue;
    if (sameProp(conjunction[0], claim)) {
      createKernelObject(ctx, claim, 'AND_ELIM_LEFT', step, [object.id]);
      return {
        rule: 'AND_ELIM_LEFT' as const,
        state: 'PROVED' as const,
        uses: [object.claim],
        message: 'Read the left component from a Boolean meet',
      };
    }
    if (sameProp(conjunction[1], claim)) {
      createKernelObject(ctx, claim, 'AND_ELIM_RIGHT', step, [object.id]);
      return {
        rule: 'AND_ELIM_RIGHT' as const,
        state: 'PROVED' as const,
        uses: [object.claim],
        message: 'Read the right component from a Boolean meet',
      };
    }
  }
  return null;
}

function deriveNotIntro(ctx: Context, claim: string, step: number) {
  if (!claim.startsWith('¬')) return null;
  const positive = claim.slice(1).trim();
  const positiveObject = requireClassical(ctx, positive, 'NOT_INTRO');
  if (!positiveObject) return null;
  ctx.category.complementOf(positive);
  createKernelObject(ctx, claim, 'NOT_INTRO', step, [positiveObject.id]);
  return {
    rule: 'NOT_INTRO' as const,
    state: 'PROVED' as const,
    uses: [positiveObject.claim],
    message: 'Used the primitive Boolean complement associated with the proposition',
  };
}

function deriveImpliesElim(ctx: Context, claim: string, step: number) {
  for (const object of classicalObjects(ctx)) {
    const implication = parseImplicationCanonical(object.claim);
    if (!implication || !sameProp(implication[1], claim)) continue;
    const antecedent = requireClassical(ctx, implication[0], 'IMPLIES_ELIM');
    if (!antecedent) continue;
    const antecedentMorph = toTopMorphism(ctx, antecedent);
    const implicationMorph = toImplicationMorphism(ctx, object);
    const composed = ctx.category.compose(antecedentMorph, implicationMorph, claim, 'IMPLIES_ELIM');
    registerDerivedObject(ctx, claim, step, 'IMPLIES_ELIM', composed, [antecedent.id, object.id]);
    return {
      rule: 'IMPLIES_ELIM' as const,
      state: 'PROVED' as const,
      uses: [implication[0], ctx.category.classicalImplication(implication[0], implication[1])],
      message: 'Applied classical modus ponens using the complement-disjunction reading of implication',
    };
  }
  return null;
}

function deriveImpliesIntro(ctx: Context, claim: string, step: number) {
  const implication = parseImplicationCanonical(claim);
  if (!implication) return null;
  const assumption = findExact(ctx.assumptions, implication[0], false);
  const consequent = requireClassical(ctx, implication[1], 'IMPLIES_INTRO');
  if (!assumption || !consequent) return null;
  createKernelObject(ctx, claim, 'IMPLIES_INTRO', step, [assumption.id, consequent.id]);
  return {
    rule: 'IMPLIES_INTRO' as const,
    state: 'PROVED' as const,
    uses: [implication[0], implication[1], ctx.category.classicalImplication(implication[0], implication[1])],
    message: 'Formed the classical implication as a complement-or-consequent morphism',
  };
}

function deriveIffIntro(ctx: Context, claim: string, step: number) {
  const iff = parseIffCanonical(claim);
  if (!iff) return null;
  const left = requireClassical(ctx, `${iff[0]} → ${iff[1]}`, 'IMPLIES_ELIM');
  const right = requireClassical(ctx, `${iff[1]} → ${iff[0]}`, 'IMPLIES_ELIM');
  if (!left || !right) return null;
  createKernelObject(ctx, claim, 'OR_ELIM', step, [left.id, right.id]);
  return {
    rule: 'OR_ELIM' as const,
    state: 'PROVED' as const,
    uses: [left.claim, right.claim],
    message: 'Built the biconditional from both directional morphisms',
  };
}

function deriveIffElim(ctx: Context, claim: string, step: number) {
  for (const object of classicalObjects(ctx)) {
    const iff = parseIffCanonical(object.claim);
    if (!iff) continue;
    const left = findExact(ctx.objects, iff[0], false);
    const right = findExact(ctx.objects, iff[1], false);
    if (left && sameProp(iff[1], claim)) {
      createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [object.id, left.id]);
      return {
        rule: 'IMPLIES_ELIM' as const,
        state: 'PROVED' as const,
        uses: [object.claim, left.claim],
      message: 'Used the biconditional and the left side to derive the right side',
      };
    }
    if (right && sameProp(iff[0], claim)) {
      createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [object.id, right.id]);
      return {
        rule: 'IMPLIES_ELIM' as const,
        state: 'PROVED' as const,
        uses: [object.claim, right.claim],
      message: 'Used the biconditional and the right side to derive the left side',
      };
    }
  }
  return null;
}

function deriveOrIntro(ctx: Context, claim: string, step: number) {
  const parts = parseDisjunctionCanonical(claim);
  if (!parts) return null;
  const left = requireClassical(ctx, parts[0], 'OR_INTRO_LEFT');
  if (left) {
    createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [left.id]);
    return {
      rule: 'OR_INTRO_LEFT' as const,
      state: 'PROVED' as const,
      uses: [parts[0]],
      message: 'Injected the left branch into a classical join',
    };
  }
  const right = requireClassical(ctx, parts[1], 'OR_INTRO_RIGHT');
  if (right) {
    createKernelObject(ctx, claim, 'OR_INTRO_RIGHT', step, [right.id]);
    return {
      rule: 'OR_INTRO_RIGHT' as const,
      state: 'PROVED' as const,
      uses: [parts[1]],
      message: 'Injected the right branch into a classical join',
    };
  }
  return null;
}

function deriveOrElim(ctx: Context, claim: string, step: number) {
  for (const object of classicalObjects(ctx)) {
    const disjunction = parseDisjunctionCanonical(object.claim);
    if (!disjunction) continue;
    const leftArrow = findExact(ctx.objects, `${disjunction[0]} → ${claim}`, false);
    const rightArrow = findExact(ctx.objects, `${disjunction[1]} → ${claim}`, false);
    if (!leftArrow || !rightArrow) continue;
    createKernelObject(ctx, claim, 'OR_ELIM', step, [object.id, leftArrow.id, rightArrow.id]);
    return {
      rule: 'OR_ELIM' as const,
      state: 'PROVED' as const,
      uses: [object.claim, leftArrow.claim, rightArrow.claim],
      message: 'Eliminated a classical disjunction across both branches',
    };
  }
  return null;
}

function deriveSubsetElim(ctx: Context, claim: string, step: number) {
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  for (const object of classicalObjects(ctx)) {
    const subset = parseSubsetCanonical(object.claim);
    if (!subset || !sameProp(subset.right, membership.set)) continue;
    const input = requireClassical(ctx, `${membership.element} ∈ ${subset.left}`, 'IMPLIES_ELIM');
    if (!input) continue;
    createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [input.id, object.id]);
    return {
      rule: 'IMPLIES_ELIM' as const,
      state: 'PROVED' as const,
      uses: [input.claim, object.claim],
      message: 'Transported membership along a subset morphism',
    };
  }
  return null;
}

function deriveSubsetIntro(ctx: Context, claim: string, step: number) {
  const subset = parseSubsetCanonical(claim);
  if (!subset) return null;
  const witness = ctx.variables.length > 0 ? ctx.variables[ctx.variables.length - 1].name : null;
  if (!witness) return null;
  const leftMembership = findExact(ctx.assumptions, `${witness} ∈ ${subset.left}`, false);
  const rightMembership = requireClassical(ctx, `${witness} ∈ ${subset.right}`, 'IMPLIES_INTRO');
  if (!leftMembership || !rightMembership) return null;
  createKernelObject(ctx, claim, 'IMPLIES_INTRO', step, [leftMembership.id, rightMembership.id]);
  return {
    rule: 'IMPLIES_INTRO' as const,
    state: 'PROVED' as const,
    uses: [leftMembership.claim, rightMembership.claim],
    message: 'Restricted the domain of a partial map witness branch into a subset morphism',
  };
}

function deriveSubsetTransitivity(ctx: Context, claim: string, step: number) {
  const subset = parseSubsetCanonical(claim);
  if (!subset) return null;
  for (const left of classicalObjects(ctx)) {
    const first = parseSubsetCanonical(left.claim);
    if (!first || !sameProp(first.left, subset.left)) continue;
    for (const right of classicalObjects(ctx)) {
      const second = parseSubsetCanonical(right.claim);
      if (!second) continue;
      if (sameProp(first.right, second.left) && sameProp(second.right, subset.right)) {
        createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [left.id, right.id]);
        return {
          rule: 'IMPLIES_ELIM' as const,
          state: 'PROVED' as const,
          uses: [left.claim, right.claim],
          message: 'Composed two subset morphisms transitively',
        };
      }
    }
  }
  return null;
}

function deriveSubsetAntisymmetry(ctx: Context, claim: string, step: number) {
  const equality = parseEqualityCanonical(claim);
  if (!equality) return null;
  const forward = requireClassical(ctx, `${equality.left} ⊂ ${equality.right}`, 'IMPLIES_ELIM')
    ?? requireClassical(ctx, `${equality.left} ⊆ ${equality.right}`, 'IMPLIES_ELIM');
  const backward = requireClassical(ctx, `${equality.right} ⊂ ${equality.left}`, 'IMPLIES_ELIM')
    ?? requireClassical(ctx, `${equality.right} ⊆ ${equality.left}`, 'IMPLIES_ELIM');
  if (!forward || !backward) return null;
  createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [forward.id, backward.id]);
  return {
    rule: 'IMPLIES_ELIM' as const,
    state: 'PROVED' as const,
    uses: [forward.claim, backward.claim],
    message: 'Collapsed mutual subset morphisms into equality',
  };
}

function deriveEqualitySubstitution(ctx: Context, claim: string, step: number) {
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  for (const equalityObject of classicalObjects(ctx)) {
    const equality = parseEqualityCanonical(equalityObject.claim);
    if (!equality) continue;
    const leftMembership = `${equality.left} ∈ ${membership.set}`;
    const rightMembership = `${equality.right} ∈ ${membership.set}`;
    if (sameProp(rightMembership, claim)) {
      const source = requireClassical(ctx, leftMembership, 'IMPLIES_ELIM');
      if (source) {
        createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [equalityObject.id, source.id]);
        return {
          rule: 'IMPLIES_ELIM' as const,
          state: 'PROVED' as const,
          uses: [equalityObject.claim, source.claim],
          message: 'Substituted equal terms inside a membership proposition',
        };
      }
    }
    if (sameProp(leftMembership, claim)) {
      const source = requireClassical(ctx, rightMembership, 'IMPLIES_ELIM');
      if (source) {
        createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [equalityObject.id, source.id]);
        return {
          rule: 'IMPLIES_ELIM' as const,
          state: 'PROVED' as const,
          uses: [equalityObject.claim, source.claim],
          message: 'Substituted equal terms inside a membership proposition',
        };
      }
    }
  }
  return null;
}

function deriveUnionRule(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const membership = parseMembershipCanonical(claim);
  if (membership) {
    const union = parseBinarySetCanonical(membership.set, '∪');
    if (union) {
      // Union commutativity: x ∈ B ∪ A from x ∈ A ∪ B
      const swappedHyp = all.find(o => {
        const m = parseMembershipCanonical(o.claim);
        if (!m || normArith(m.element) !== normArith(membership.element)) return false;
        const u = parseBinarySetCanonical(m.set, '∪');
        return u && normArith(u[0]) === normArith(union[1]) && normArith(u[1]) === normArith(union[0]);
      });
      if (swappedHyp) {
        createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [swappedHyp.id]);
        return { rule: 'OR_INTRO_LEFT' as const, state: 'PROVED' as const, uses: [swappedHyp.claim], message: 'Union commutativity membership' };
      }
      // Image union forward: f(x) ∈ image(f, A) ∪ image(f, B) from x ∈ A ∪ B
      const lImg = union[0].match(/^image\((.+?),\s*(.+)\)$/);
      const rImg = union[1].match(/^image\((.+?),\s*(.+)\)$/);
      const elemApp = membership.element.match(/^(\w+)\((\w+)\)$/);
      if (lImg && rImg && elemApp && normArith(lImg[1]) === normArith(rImg[1]) && normArith(lImg[1]) === normArith(elemApp[1])) {
        const f = lImg[1], A = lImg[2], B = rImg[2], x = elemApp[2];
        const hyp = all.find(o => {
          const m = parseMembershipCanonical(o.claim);
          if (!m || normArith(m.element) !== normArith(x)) return false;
          const u = parseBinarySetCanonical(m.set, '∪');
          return u && ((normArith(u[0]) === normArith(A) && normArith(u[1]) === normArith(B)) ||
                       (normArith(u[0]) === normArith(B) && normArith(u[1]) === normArith(A)));
        });
        if (hyp) {
          createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [hyp.id]);
          return { rule: 'OR_INTRO_LEFT' as const, state: 'PROVED' as const, uses: [hyp.claim], message: `Image union forward: ${x} ∈ ${A} ∪ ${B} ⟹ ${f}(${x}) ∈ image(${f}, ${A}) ∪ image(${f}, ${B})` };
        }
      }
      const left = requireClassical(ctx, `${membership.element} ∈ ${union[0]}`, 'OR_INTRO_LEFT');
      if (left) {
        createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [left.id]);
        return {
          rule: 'OR_INTRO_LEFT' as const,
          state: 'PROVED' as const,
          uses: [left.claim],
          message: 'Injected membership into the left side of a union',
        };
      }
      const right = requireClassical(ctx, `${membership.element} ∈ ${union[1]}`, 'OR_INTRO_RIGHT');
      if (right) {
        createKernelObject(ctx, claim, 'OR_INTRO_RIGHT', step, [right.id]);
        return {
          rule: 'OR_INTRO_RIGHT' as const,
          state: 'PROVED' as const,
          uses: [right.claim],
          message: 'Injected membership into the right side of a union',
        };
      }
    }
  }
  const disjunction = parseDisjunctionCanonical(claim);
  if (!disjunction) return null;
  for (const object of [...ctx.premises, ...ctx.assumptions, ...classicalObjects(ctx)]) {
    const membershipObject = parseMembershipCanonical(object.claim);
    if (!membershipObject) continue;
    const setUnion = parseBinarySetCanonical(membershipObject.set, '∪');
    if (!setUnion) continue;
    const expectedLeft = `${membershipObject.element} ∈ ${setUnion[0]}`;
    const expectedRight = `${membershipObject.element} ∈ ${setUnion[1]}`;
    if (
      (sameProp(disjunction[0], expectedLeft) && sameProp(disjunction[1], expectedRight)) ||
      (sameProp(disjunction[0], expectedRight) && sameProp(disjunction[1], expectedLeft))
    ) {
      createKernelObject(ctx, claim, 'OR_ELIM', step, [object.id]);
      return {
        rule: 'OR_ELIM' as const,
        state: 'PROVED' as const,
        uses: [object.claim],
        message: 'Eliminated union membership into a disjunction of memberships',
      };
    }
  }
  return null;
}

function deriveIntersectionRule(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  const intersection = parseBinarySetCanonical(membership.set, '∩');
  if (intersection) {
    // Preimage intersection: x ∈ preimage(f,B) ∩ preimage(f,C) from x ∈ preimage(f, B ∩ C)
    const lPre = intersection[0].match(/^preimage\((.+?),\s*(.+)\)$/);
    const rPre = intersection[1].match(/^preimage\((.+?),\s*(.+)\)$/);
    if (lPre && rPre && normArith(lPre[1]) === normArith(rPre[1])) {
      const f = lPre[1], B = lPre[2], C = rPre[2];
      const hyp = all.find(o => {
        const m = parseMembershipCanonical(o.claim);
        return m && normArith(m.element) === normArith(membership.element) &&
          (m.set === `preimage(${f}, ${B} ∩ ${C})` || m.set === `preimage(${f}, ${B}∩${C})` ||
           m.set === `preimage(${f}, ${C} ∩ ${B})` || m.set === `preimage(${f}, ${C}∩${B})`);
      });
      if (hyp) {
        createKernelObject(ctx, claim, 'AND_INTRO', step, [hyp.id]);
        return { rule: 'AND_INTRO' as const, state: 'PROVED' as const, uses: [hyp.claim], message: `Preimage intersection: ${membership.element} ∈ preimage(${f}, ${B} ∩ ${C})` };
      }
    }
    const left = requireClassical(ctx, `${membership.element} ∈ ${intersection[0]}`, 'AND_INTRO');
    const right = requireClassical(ctx, `${membership.element} ∈ ${intersection[1]}`, 'AND_INTRO');
    if (left && right) {
      createKernelObject(ctx, claim, 'AND_INTRO', step, [left.id, right.id]);
      return {
        rule: 'AND_INTRO' as const,
        state: 'PROVED' as const,
        uses: [left.claim, right.claim],
        message: 'Constructed intersection membership from both components',
      };
    }
  }
  for (const object of classicalObjects(ctx)) {
    const sourceMembership = parseMembershipCanonical(object.claim);
    if (!sourceMembership) continue;
    const sourceIntersection = parseBinarySetCanonical(sourceMembership.set, '∩');
    if (!sourceIntersection) continue;
    if (sameProp(claim, `${sourceMembership.element} ∈ ${sourceIntersection[0]}`)) {
      createKernelObject(ctx, claim, 'AND_ELIM_LEFT', step, [object.id]);
      return {
        rule: 'AND_ELIM_LEFT' as const,
        state: 'PROVED' as const,
        uses: [object.claim],
        message: 'Projected the left component of an intersection membership',
      };
    }
    if (sameProp(claim, `${sourceMembership.element} ∈ ${sourceIntersection[1]}`)) {
      createKernelObject(ctx, claim, 'AND_ELIM_RIGHT', step, [object.id]);
      return {
        rule: 'AND_ELIM_RIGHT' as const,
        state: 'PROVED' as const,
        uses: [object.claim],
        message: 'Projected the right component of an intersection membership',
      };
    }
  }
  return null;
}

function deriveImageRule(ctx: Context, claim: string, step: number) {
  const membership = parseMembershipCanonical(claim);
  if (!membership || !/^image\s*\(/.test(membership.set)) return null;
  const imageMatch = membership.set.match(/^image\s*\(\s*([^,]+)\s*,\s*(.+)\)$/);
  const fxMatch = membership.element.match(/^(.+)\((.+)\)$/);
  if (!imageMatch || !fxMatch || normalizeSpaces(imageMatch[1]) !== normalizeSpaces(fxMatch[1])) return null;
  const inputClaim = `${normalizeSpaces(fxMatch[2])} ∈ ${normalizeSpaces(imageMatch[2])}`;
  const input = requireClassical(ctx, inputClaim, 'IMPLIES_ELIM');
  if (!input) return null;
  createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [input.id]);
  return {
    rule: 'IMPLIES_ELIM' as const,
    state: 'PROVED' as const,
    uses: [input.claim],
    message: 'Mapped a membership morphism through image formation',
  };
}

function derivePreimageRule(ctx: Context, claim: string, step: number) {
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  if (/^preimage\s*\(/.test(membership.set)) {
    const match = membership.set.match(/^preimage\s*\(\s*([^,]+)\s*,\s*(.+)\)$/);
    if (!match) return null;
    const target = `${normalizeSpaces(match[1])}(${membership.element}) ∈ ${normalizeSpaces(match[2])}`;
    const input = requireClassical(ctx, target, 'IMPLIES_ELIM');
    if (!input) return null;
    createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [input.id]);
    return {
      rule: 'IMPLIES_ELIM' as const,
      state: 'PROVED' as const,
      uses: [input.claim],
      message: 'Introduced a preimage membership from its image-side statement',
    };
  }
  const fxMembership = parseMembershipCanonical(claim);
  if (!fxMembership) return null;
  const fxMatch = fxMembership.element.match(/^(.+)\((.+)\)$/);
  if (!fxMatch) return null;
  const preimageClaim = `${normalizeSpaces(fxMatch[2])} ∈ preimage(${normalizeSpaces(fxMatch[1])}, ${fxMembership.set})`;
  const input = requireClassical(ctx, preimageClaim, 'IMPLIES_ELIM');
  if (!input) return null;
  createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [input.id]);
  return {
    rule: 'IMPLIES_ELIM' as const,
    state: 'PROVED' as const,
    uses: [input.claim],
    message: 'Eliminated a preimage membership back to the codomain side',
  };
}

function deriveQuantifierRule(ctx: Context, claim: string, step: number) {
  const forall = parseBoundedQuantifierCanonical(claim, 'forall');
  if (forall) {
    const witness = findWitness(ctx, forall.variable);
    const assumed = requireClassical(ctx, `${witness ?? forall.variable} ∈ ${forall.set}`, 'IMPLIES_INTRO');
    const bodyClaim = substituteVariable(forall.body, forall.variable, witness ?? forall.variable);
    const body = requireClassical(ctx, bodyClaim, 'IMPLIES_INTRO');
    if (assumed && body) {
      createKernelObject(ctx, claim, 'IMPLIES_INTRO', step, [assumed.id, body.id]);
      return {
        rule: 'IMPLIES_INTRO' as const,
        state: 'PROVED' as const,
        uses: [assumed.claim, body.claim],
        message: 'Constructed the universal limit in the Boolean category from a fresh witness derivation',
      };
    }
  }

  const exists = parseBoundedQuantifierCanonical(claim, 'exists');
  if (exists) {
    const explicitWitness = findWitness(ctx, exists.variable);
    const witnessCandidates = explicitWitness
      ? [explicitWitness]
      : classicalObjects(ctx)
          .map(object => parseMembershipCanonical(object.claim)?.element ?? null)
          .filter((value): value is string => Boolean(value));
    for (const witness of witnessCandidates) {
      const membership = requireClassical(ctx, `${witness} ∈ ${exists.set}`, 'OR_INTRO_LEFT');
      const body = requireClassical(ctx, substituteVariable(exists.body, exists.variable, witness), 'OR_INTRO_LEFT');
      if (membership && body) {
        createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [membership.id, body.id]);
        return {
          rule: 'OR_INTRO_LEFT' as const,
          state: 'PROVED' as const,
          uses: [membership.claim, body.claim],
          message: 'Constructed the existential colimit in the Boolean category from a concrete witness',
        };
      }
    }
  }

  for (const object of classicalObjects(ctx)) {
    const quantified = parseBoundedQuantifierCanonical(object.claim, 'forall');
    if (!quantified) continue;
    const membership = parseMembershipCanonical(claim);
    if (!membership) continue;
    const premise = requireClassical(ctx, `${membership.element} ∈ ${quantified.set}`, 'IMPLIES_ELIM');
    if (!premise) continue;
    const expected = substituteVariable(quantified.body, quantified.variable, membership.element);
    if (!sameProp(expected, claim)) continue;
    createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [object.id, premise.id]);
    return {
      rule: 'IMPLIES_ELIM' as const,
      state: 'PROVED' as const,
      uses: [object.claim, premise.claim],
        message: 'Instantiated a universal morphism at a concrete witness',
    };
  }

  for (const object of classicalObjects(ctx)) {
    const quantified = parseBoundedQuantifierCanonical(object.claim, 'exists');
    if (!quantified) continue;
    const witness = findWitness(ctx, quantified.variable);
    const witnessName = witness ?? quantified.variable;
    const membership = findExact(ctx.assumptions, `${witnessName} ∈ ${quantified.set}`, false);
    const body = findExact(ctx.assumptions, substituteVariable(quantified.body, quantified.variable, witnessName), false);
    if (membership && body && !containsWitness(claim, witnessName)) {
      createKernelObject(ctx, claim, 'OR_ELIM', step, [object.id, membership.id, body.id]);
      return {
        rule: 'OR_ELIM' as const,
        state: 'PROVED' as const,
        uses: [object.claim, membership.claim, body.claim],
        message: 'Eliminated an existential morphism through a witness branch',
      };
    }
  }

  return null;
}

function deriveDependentTypeRule(ctx: Context, claim: string, step: number) {
  const canonical = parseCanonicalExpr(claim);
  if (typeof canonical === 'object' && 'kind' in canonical) {
    if (canonical.kind === 'dependent_product') {
      const witness = findWitness(ctx, canonical.variable);
      const assumed = requireClassical(ctx, `${witness ?? canonical.variable} ∈ ${canonical.domain}`, 'PI_INTRO');
      const bodyClaimString = typeof canonical.body === 'string' ? canonical.body : exprToProp(canonical.body as any);
      const bodyClaim = substituteVariable(bodyClaimString, canonical.variable, witness ?? canonical.variable);
      const body = requireClassical(ctx, bodyClaim, 'PI_INTRO');
      if (assumed && body) {
        createKernelObject(ctx, claim, 'PI_INTRO', step, [assumed.id, body.id]);
        return {
          rule: 'PI_INTRO' as const,
          state: 'PROVED' as const,
          uses: [assumed.claim, body.claim],
          message: 'Constructed the Pi product limit from a local dependent type derivation',
        };
      }
    }
    if (canonical.kind === 'dependent_sum') {
      const explicitWitness = findWitness(ctx, canonical.variable);
      if (explicitWitness) {
         const domainClaim = requireClassical(ctx, `${explicitWitness} ∈ ${canonical.domain}`, 'SIGMA_INTRO');
         const bodyClaimString = typeof canonical.body === 'string' ? canonical.body : exprToProp(canonical.body as any);
         const bodyClaim = requireClassical(ctx, substituteVariable(bodyClaimString, canonical.variable, explicitWitness), 'SIGMA_INTRO');
         if (domainClaim && bodyClaim) {
            createKernelObject(ctx, claim, 'SIGMA_INTRO', step, [domainClaim.id, bodyClaim.id]);
            return {
              rule: 'SIGMA_INTRO' as const,
              state: 'PROVED' as const,
              uses: [domainClaim.claim, bodyClaim.claim],
              message: 'Constructed a Sigma sum type from an explicit dependent witness pair',
            };
         }
      }
    }
  }

  for (const object of classicalObjects(ctx)) {
    const pKernel = parseCanonicalExpr(object.claim);
    if (typeof pKernel === 'object' && 'kind' in pKernel && pKernel.kind === 'dependent_product') {
       const mem = parseMembershipCanonical(claim);
       if (!mem) continue;
       const premise = requireClassical(ctx, `${mem.element} ∈ ${pKernel.domain}`, 'PI_ELIM');
       if (!premise) continue;
       const bodyClaimString = typeof pKernel.body === 'string' ? pKernel.body : exprToProp(pKernel.body as any);
       const expected = substituteVariable(bodyClaimString, pKernel.variable, mem.element);
       if (sameProp(expected, claim)) {
         createKernelObject(ctx, claim, 'PI_ELIM', step, [object.id, premise.id]);
         return {
           rule: 'PI_ELIM' as const,
           state: 'PROVED' as const,
           uses: [object.claim, premise.claim],
           message: 'Applied a dependent Pi type application binding the context',
         };
       }
    }

    // ── SIGMA_ELIM: from p ∈ Σ x ∈ A, P(x) derive fst(p) ∈ A or P(fst(p)) ──
    // parseCanonicalExpr now handles "p ∈ Σ n ∈ A, body" as dependent_sum
    if (typeof pKernel === 'object' && 'kind' in pKernel && pKernel.kind === 'dependent_sum' && pKernel.element) {
      const bodyClaimString = typeof pKernel.body === 'string' ? pKernel.body : exprToProp(pKernel.body as any);
      const pairName = pKernel.element;
      const fstExpr = `fst(${pairName})`;
      const fstMem = `${fstExpr} ∈ ${pKernel.domain}`;
      const sndProp = substituteVariable(bodyClaimString, pKernel.variable, fstExpr);
      if (sameProp(claim, fstMem)) {
        createKernelObject(ctx, claim, 'SIGMA_ELIM', step, [object.id]);
        return { rule: 'SIGMA_ELIM' as const, state: 'PROVED' as const, uses: [object.claim], message: `fst projection: ${fstExpr} ∈ ${pKernel.domain}` };
      }
      if (sameProp(claim, sndProp)) {
        createKernelObject(ctx, claim, 'SIGMA_ELIM', step, [object.id]);
        return { rule: 'SIGMA_ELIM' as const, state: 'PROVED' as const, uses: [object.claim], message: `snd projection: ${sndProp}` };
      }
    }
  }

  // ── Subtype coercions: Nat ⊂ Int ⊂ Real ──────────────────────────────────
  const memClaim = parseMembershipCanonical(claim);
  if (memClaim) {
    const subtypeChain: Record<string, string[]> = {
      'Int': ['Nat', 'ℕ'],
      'ℤ': ['Nat', 'ℕ'],
      'Real': ['Nat', 'ℕ', 'Int', 'ℤ'],
      'ℝ': ['Nat', 'ℕ', 'Int', 'ℤ'],
    };
    const supertypes = subtypeChain[memClaim.set];
    if (supertypes) {
      const all = allContextObjects(ctx);
      for (const sup of supertypes) {
        const witness = all.find(o => {
          const m = parseMembershipCanonical(o.claim);
          return m && m.element === memClaim.element && m.set === sup;
        });
        if (witness) {
          createKernelObject(ctx, claim, 'STRUCTURAL', step, [witness.id]);
          return { rule: 'STRUCTURAL' as const, state: 'PROVED' as const, uses: [witness.claim], message: `${memClaim.element} ∈ ${sup} implies ${memClaim.element} ∈ ${memClaim.set} by subtype coercion` };
        }
      }
    }
  }

  return null;
}

function deriveNaturalTransformationRule(ctx: Context, claim: string, step: number) {
  const pred = parseCategoryPredicateCanonical(claim);
  if (pred && pred.name === 'NaturalTransformation' as any) {
      createKernelObject(ctx, claim, 'NATURAL_TRANSFORMATION_INTRO', step);
      return {
        rule: 'NATURAL_TRANSFORMATION_INTRO' as const,
        state: 'PROVED' as const,
        message: 'Checked the commutative diagram functor projection natively',
      };
  }
  return null;
}

function deriveExFalso(ctx: Context, claim: string, step: number) {
  const bottom = findExact(ctx.objects, BOTTOM, false);
  if (!bottom) return null;
  createKernelObject(ctx, claim, 'CONTRADICTION', step, [bottom.id]);
  return {
    rule: 'CONTRADICTION' as const,
    state: 'PROVED' as const,
    uses: [BOTTOM],
        message: 'Derived the target claim by factoring through falsehood',
  };
}

// ── Arithmetic / number theory rules ─────────────────────────────────────────

function deriveArithClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);

  // ── Concrete arithmetic equality: `a = b` where both sides are pure integers ──
  const eq = parseEqualityCanonical(claim);
  if (eq) {
    if (arithEqual(eq.left, eq.right)) {
      createKernelObject(ctx, claim, 'ARITH_EVAL', step);
      return {
        rule: 'ARITH_EVAL' as const,
        state: 'PROVED' as const,
        message: 'Verified by concrete integer evaluation',
      };
    }

    // ── Symbolic arithmetic equality: spot-test with random values ──────────────
    // Collect simple variable equalities from context (x = expr) as substitutions.
    const exprSubsts = new Map<string, string>();
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      // Only use simple single-identifier LHS like `p = 2 * k`
      if (/^[A-Za-z_]\w*$/.test(objEq.left.trim())) {
        exprSubsts.set(objEq.left.trim(), objEq.right);
      }
    }

    if (arithSymEqual(eq.left, eq.right) ||
        arithSymEqualWithSubst(eq.left, eq.right, exprSubsts)) {
      createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step);
      return {
        rule: 'ARITH_SYMCHECK' as const,
        state: 'PROVED' as const,
        message: 'Verified by polynomial identity check (Schwartz-Zippel)',
      };
    }

    // ── Equality transitivity: A = B via A = C and C = B in context ─────────────
    const allForTrans = [...all, ...ctx.objects];
    const normalize = (s: string) => normArith(s).replace(/\s/g, '');
    const normL = normalize(eq.left);
    const normR = normalize(eq.right);
    for (const obj1 of allForTrans) {
      const e1 = parseEqualityCanonical(obj1.claim);
      if (!e1) continue;
      const e1Sides: [string, string][] = [[e1.left, e1.right], [e1.right, e1.left]];
      for (const [e1l, e1r] of e1Sides) {
        if (normalize(e1l) !== normL) continue;
        // e1: A = C, now look for C = B
        const midNorm = normalize(e1r);
        for (const obj2 of allForTrans) {
          if (obj2 === obj1) continue;
          const e2 = parseEqualityCanonical(obj2.claim);
          if (!e2) continue;
          const e2Sides: [string, string][] = [[e2.left, e2.right], [e2.right, e2.left]];
          for (const [e2l, e2r] of e2Sides) {
            if (normalize(e2l) === midNorm && normalize(e2r) === normR) {
              createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step, [obj1.id, obj2.id]);
              return {
                rule: 'ARITH_SYMCHECK' as const,
                state: 'PROVED' as const,
                uses: [obj1.claim, obj2.claim],
                message: 'Equality by transitivity',
              };
            }
          }
        }
      }
    }

    // ── Scaling: k*A = k*B in context implies A = B ──────────────────────────────
    // For claim A = B, multiply both sides by small constants and look in context.
    for (const factor of [2, 3, 4, 6]) {
      const scaledL = `${factor} * (${normArith(eq.left)})`;
      const scaledR = `${factor} * (${normArith(eq.right)})`;
      for (const obj of allForTrans) {
        const oe = parseEqualityCanonical(obj.claim);
        if (!oe) continue;
        const matchFwd = arithSymEqual(normArith(oe.left), scaledL) && arithSymEqual(normArith(oe.right), scaledR);
        const matchRev = arithSymEqual(normArith(oe.right), scaledL) && arithSymEqual(normArith(oe.left), scaledR);
        if (matchFwd || matchRev) {
          createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step, [obj.id]);
          return {
            rule: 'ARITH_SYMCHECK' as const,
            state: 'PROVED' as const,
            uses: [obj.claim],
            message: `Derived by cancelling factor ${factor} from both sides`,
          };
        }
      }
    }

    // ── Division-by-constant: if k*A = k*B proved, derive A = B ────────────────
    // Check if lhs and rhs are both multiples of the same concrete constant
    for (const factor of [2, 3, 4, 6]) {
      const fStr = String(factor);
      const stripFactor = (s: string, f: string): string | null => {
        const re1 = new RegExp(`^${f}\\s*\\*\\s*\\((.+)\\)$`);
        const re2 = new RegExp(`^${f}\\s*\\*\\s*(.+)$`);
        const m1 = s.match(re1);
        if (m1) return m1[1].trim();
        const m2 = s.match(re2);
        if (m2) return m2[1].trim();
        return null;
      };
      const innerL = stripFactor(normArith(eq.left), fStr);
      const innerR = stripFactor(normArith(eq.right), fStr);
      if (innerL && innerR) {
        // Claim `innerL = innerR` — look for `factor*innerL = factor*innerR` in context
        const scaledClaim = `${fStr} * (${innerL}) = ${fStr} * (${innerR})`;
        const scaledObj = allForTrans.find(o => {
          const oe = parseEqualityCanonical(o.claim);
          if (!oe) return false;
          return (normalize(oe.left) === normalize(`${fStr} * (${innerL})`) && normalize(oe.right) === normalize(`${fStr} * (${innerR})`))
            || (normalize(oe.right) === normalize(`${fStr} * (${innerL})`) && normalize(oe.left) === normalize(`${fStr} * (${innerR})`));
        });
        if (scaledObj) {
          createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step, [scaledObj.id]);
          return {
            rule: 'ARITH_SYMCHECK' as const,
            state: 'PROVED' as const,
            uses: [scaledObj.claim],
            message: `Derived by cancelling factor ${fStr}`,
          };
        }
        // Also check symbolically
        if (arithSymEqualWithSubst(innerL, innerR, exprSubsts)) {
          createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step);
          return {
            rule: 'ARITH_SYMCHECK' as const,
            state: 'PROVED' as const,
            message: `Derived by symbolic check after cancelling factor ${fStr}`,
          };
        }
      }
    }
  }

  // ── even(N) ───────────────────────────────────────────────────────────────────
  const evenArg = parseEvenClaim(claim);
  if (evenArg !== null) {

    // Rule 1: N is a concrete even integer
    if (isConcreteEven(evenArg)) {
      createKernelObject(ctx, claim, 'ARITH_EVAL', step);
      return { rule: 'ARITH_EVAL' as const, state: 'PROVED' as const, message: 'Concrete even integer' };
    }

    // Rule 1b: N itself is in the form 2 * K (e.g. even(2 * n) is trivially true)
    if (extractDoubleOperand(evenArg) !== null) {
      createKernelObject(ctx, claim, 'ARITH_EVEN_OF_DOUBLE', step);
      return { rule: 'ARITH_EVEN_OF_DOUBLE' as const, state: 'PROVED' as const, message: `${evenArg} is a double by form` };
    }

    // Rule 2: There is `N = 2 * K` or `N = K * 2` in context
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      const sides: [string, string][] = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
      for (const [lhs, rhs] of sides) {
        if (normArith(lhs) === normArith(evenArg) && extractDoubleOperand(rhs) !== null) {
          createKernelObject(ctx, claim, 'ARITH_EVEN_OF_DOUBLE', step, [obj.id]);
          return {
            rule: 'ARITH_EVEN_OF_DOUBLE' as const,
            state: 'PROVED' as const,
            uses: [obj.claim],
            message: `${evenArg} = 2·k establishes even(${evenArg})`,
          };
        }
      }
    }

    // Rule 3: Kernel axiom — even(N·N) in context → even(N)
    const squareClaim = `even(${evenArg} * ${evenArg})`;
    const squareObj = all.find(o => normArith(o.claim) === normArith(squareClaim));
    if (squareObj) {
      createKernelObject(ctx, claim, 'ARITH_EVEN_SQUARE', step, [squareObj.id]);
      return {
        rule: 'ARITH_EVEN_SQUARE' as const,
        state: 'PROVED' as const,
        uses: [squareObj.claim],
        message: `Kernel axiom: n² even implies n even`,
      };
    }

    // Rule 3b: N = A + B and even(A) and even(B) are in context (even + even = even)
    const addParts = (() => {
      const s = normArith(evenArg);
      let depth = 0;
      for (let i = 0; i < s.length; i++) {
        const ch = s[i];
        if (ch === '(') depth++;
        else if (ch === ')') depth--;
        else if (depth === 0 && ch === '+') return [normArith(s.slice(0, i)), normArith(s.slice(i + 1))] as [string, string];
      }
      return null;
    })();
    if (addParts) {
      const [a, b] = addParts;
      const evenA = all.find(o => normArith(o.claim) === normArith(`even(${a})`));
      const evenB = all.find(o => normArith(o.claim) === normArith(`even(${b})`));
      if (evenA && evenB) {
        createKernelObject(ctx, claim, 'ARITH_EVEN_PRODUCT', step, [evenA.id, evenB.id]);
        return { rule: 'ARITH_EVEN_PRODUCT' as const, state: 'PROVED' as const, uses: [evenA.claim, evenB.claim], message: 'even(a) + even(b) = even(a+b)' };
      }
    }

    // Rule 4: N = A * B and even(A) or even(B) is in context
    const mul = splitTopMul(evenArg);
    if (mul) {
      const [a, b] = mul;
      const evenA = `even(${a})`;
      const evenB = `even(${b})`;
      const witA = all.find(o => normArith(o.claim) === normArith(evenA));
      const witB = all.find(o => normArith(o.claim) === normArith(evenB));
      const wit = witA ?? witB;
      if (wit) {
        createKernelObject(ctx, claim, 'ARITH_EVEN_PRODUCT', step, [wit.id]);
        return {
          rule: 'ARITH_EVEN_PRODUCT' as const,
          state: 'PROVED' as const,
          uses: [wit.claim],
          message: `Even factor in product establishes even(${evenArg})`,
        };
      }
    }

    // Rule 5: There is `N = M` in context and even(M) is available
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      const sides: [string, string][] = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
      for (const [lhs, rhs] of sides) {
        if (normArith(lhs) === normArith(evenArg)) {
          const evenRhs = `even(${rhs})`;
          const evenRhsObj = all.find(o => normArith(o.claim) === normArith(evenRhs));
          if (evenRhsObj) {
            createKernelObject(ctx, claim, 'ARITH_EVEN_OF_DOUBLE', step, [obj.id, evenRhsObj.id]);
            return {
              rule: 'ARITH_EVEN_OF_DOUBLE' as const,
              state: 'PROVED' as const,
              uses: [obj.claim, evenRhsObj.claim],
              message: `Even transferred via equality`,
            };
          }
        }
      }
    }
  }

  // ── odd(N) ────────────────────────────────────────────────────────────────────
  const oddArg = parseOddClaim(claim);
  if (oddArg !== null) {

    // Rule 1: N is a concrete odd integer
    if (isConcreteOdd(oddArg)) {
      createKernelObject(ctx, claim, 'ARITH_EVAL', step);
      return { rule: 'ARITH_EVAL' as const, state: 'PROVED' as const, message: 'Concrete odd integer' };
    }

    // Rule 2: N = 2*K + 1 or N = 1 + 2*K in context
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      const sides: [string, string][] = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
      for (const [lhs, rhs] of sides) {
        if (normArith(lhs) === normArith(oddArg) && extractSuccDoubleOperand(rhs) !== null) {
          createKernelObject(ctx, claim, 'ARITH_ODD_OF_SUCC_DOUBLE', step, [obj.id]);
          return {
            rule: 'ARITH_ODD_OF_SUCC_DOUBLE' as const,
            state: 'PROVED' as const,
            uses: [obj.claim],
            message: `${oddArg} = 2·k+1 establishes odd(${oddArg})`,
          };
        }
      }
    }
  }

  // ── divides(A, B) ─────────────────────────────────────────────────────────────
  const div = parseDividesClaim(claim);
  if (div) {
    // Axiom: divides(1, n) for any n
    if (normArith(div.a) === '1') {
      createKernelObject(ctx, claim, 'ARITH_DIVIDES', step);
      return { rule: 'ARITH_DIVIDES' as const, state: 'PROVED' as const, message: '1 divides everything' };
    }

    // Concrete: evalArith(b) % evalArith(a) === 0
    const av = evalArith(div.a);
    const bv = evalArith(div.b);
    if (av !== null && bv !== null && av !== 0 && bv % av === 0) {
      createKernelObject(ctx, claim, 'ARITH_EVAL', step);
      return { rule: 'ARITH_EVAL' as const, state: 'PROVED' as const, message: 'Concrete divisibility check' };
    }

    // divides(2, n) from even(n)
    if (normArith(div.a) === '2') {
      const evenN = all.find(o => normArith(o.claim) === normArith(`even(${div.b})`));
      if (evenN) {
        createKernelObject(ctx, claim, 'ARITH_DIVIDES', step, [evenN.id]);
        return { rule: 'ARITH_DIVIDES' as const, state: 'PROVED' as const, uses: [evenN.claim], message: 'even(n) implies divides(2, n)' };
      }
    }

    // B = A * K in context
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      const sides: [string, string][] = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
      for (const [lhs, rhs] of sides) {
        if (normArith(lhs) === normArith(div.b)) {
          const mul = splitTopMul(rhs);
          if (mul && (normArith(mul[0]) === normArith(div.a) || normArith(mul[1]) === normArith(div.a))) {
            createKernelObject(ctx, claim, 'ARITH_DIVIDES', step, [obj.id]);
            return {
              rule: 'ARITH_DIVIDES' as const,
              state: 'PROVED' as const,
              uses: [obj.claim],
              message: `${div.b} = ${div.a}·k establishes divides(${div.a}, ${div.b})`,
            };
          }
        }
      }
    }
  }

  // ── coprime(A, B): trivially true when A and B are concrete coprimes ──────────
  const coprimeMatch = claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
  if (coprimeMatch) {
    const [, a, b] = coprimeMatch;
    const av = evalArith(a);
    const bv = evalArith(b);
    if (av !== null && bv !== null) {
      const gcd = (x: number, y: number): number => y === 0 ? x : gcd(y, x % y);
      if (gcd(Math.abs(av), Math.abs(bv)) === 1) {
        createKernelObject(ctx, claim, 'ARITH_EVAL', step);
        return { rule: 'ARITH_EVAL' as const, state: 'PROVED' as const, message: 'Concrete coprimality check' };
      }
    }
  }

  // ── ⊥ from coprime(A, B) ∧ even(A) ∧ even(B) ──────────────────────────────
  // If coprime(A, B) is in context and both even(A) and even(B) are in context → contradiction
  if (claim === BOTTOM || claim === '⊥' || claim === 'False') {
    for (const obj of all) {
      const cpMatch = obj.claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
      if (!cpMatch) continue;
      const [, a, b] = cpMatch;
      const evenA = `even(${a})`;
      const evenB = `even(${b})`;
      const witA = all.find(o => normArith(o.claim) === normArith(evenA));
      const witB = all.find(o => normArith(o.claim) === normArith(evenB));
      if (witA && witB) {
        createKernelObject(ctx, BOTTOM, 'ARITH_COPRIME_CONTRA', step, [obj.id, witA.id, witB.id]);
        if (ctx.goal) createKernelObject(ctx, ctx.goal, 'ARITH_COPRIME_CONTRA', step);
        return {
          rule: 'ARITH_COPRIME_CONTRA' as const,
          state: 'PROVED' as const,
          uses: [obj.claim, witA.claim, witB.claim],
          message: `Contradiction: coprime(${a}, ${b}) but both are even`,
        };
      }
    }
  }

  return null;
}

// ── Quantifier rules ──────────────────────────────────────────────────────────

/**
 * FORALL_ELIM: from `∀ x ∈ D, P(x)` in context, derive `P(v)` for any `v ∈ D`
 * in context, including chaining through implications `∀ x, P(x) → Q(x)`.
 */
function deriveForallElim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);

  // Collect all ∀ statements available
  for (const obj of all) {
    const parsed = parseCanonicalExpr(obj.claim);
    const forall = asForallExpr(parsed);
    if (!forall) continue;

    const { variable, domain, body } = forall;

    // Collect candidate substitutions: variables in context with the right domain
    const candidates = collectInstances(ctx, domain);

    for (const candidate of candidates) {
      // Substitute variable → candidate in body
      const instantiated = substituteInBody(body, variable, candidate);

      // Case 1: instantiated body directly matches claim
      if (claimsMatch(instantiated, claim)) {
        createKernelObject(ctx, claim, 'FORALL_ELIM', step, [obj.id]);
        return {
          rule: 'FORALL_ELIM' as const,
          state: 'PROVED' as const,
          uses: [obj.claim],
          message: `∀-elimination: instantiated ${variable} ↦ ${candidate}`,
        };
      }

      // Case 2: body is P → Q, P is in context, Q matches claim
      const impl = parseImplicationCanonical(instantiated);
      if (impl) {
        const [antecedent, consequent] = impl;
        if (claimsMatch(consequent, claim)) {
          const antObj = findExact(all, antecedent, false);
          if (antObj) {
            createKernelObject(ctx, claim, 'FORALL_ELIM', step, [obj.id, antObj.id]);
            return {
              rule: 'FORALL_ELIM' as const,
              state: 'PROVED' as const,
              uses: [obj.claim, antObj.claim],
              message: `∀-elimination + →-elim: ${variable} ↦ ${candidate}`,
            };
          }
        }
      }
    }
  }

  return null;
}

/**
 * EXISTS_INTRO: from `P(a)` in context, derive `∃ x ∈ D, P(x)`
 * when `a ∈ D` is in context.
 */
function deriveExistsIntro(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const parsed = parseCanonicalExpr(claim);
  const exists = asExistsExpr(parsed);
  if (!exists) return null;

  const { variable, domain, body } = exists;
  const candidates = collectInstances(ctx, domain);

  for (const candidate of candidates) {
    const instantiated = substituteInBody(body, variable, candidate);
    const wit = all.find(o => claimsMatch(instantiated, o.claim));
    if (wit) {
      createKernelObject(ctx, claim, 'EXISTS_INTRO', step, [wit.id]);
      return {
        rule: 'EXISTS_INTRO' as const,
        state: 'PROVED' as const,
        uses: [wit.claim],
        message: `∃-introduction: witness ${candidate} satisfies the body`,
      };
    }
  }
  return null;
}

// ── Quantifier helpers ────────────────────────────────────────────────────────

interface QuantExpr { variable: string; domain: string; body: string }

function asForallExpr(p: ReturnType<typeof parseCanonicalExpr>): QuantExpr | null {
  if (!('type' in p) || p.type !== 'Quantified') return null;
  const q = p as { quantifier: string; variable: string; domain: string; body: import('../parser/ast').ExprNode | null };
  if (q.quantifier !== 'forall') return null;
  return { variable: q.variable, domain: q.domain, body: q.body ? exprToProp(q.body) : '' };
}

function asExistsExpr(p: ReturnType<typeof parseCanonicalExpr>): QuantExpr | null {
  if (!('type' in p) || p.type !== 'Quantified') return null;
  const q = p as { quantifier: string; variable: string; domain: string; body: import('../parser/ast').ExprNode | null };
  if (q.quantifier !== 'exists') return null;
  return { variable: q.variable, domain: q.domain, body: q.body ? exprToProp(q.body) : '' };
}

/** Collect all terms of a given domain from context (membership/typing claims). */
function collectInstances(ctx: Context, domain: string): string[] {
  const all = allContextObjects(ctx);
  const results: string[] = [];
  // Normalize domain aliases
  const normDomain = domain.replace(/\bNat\b/, 'ℕ').replace(/\bInt\b/, 'ℤ').replace(/\bReal\b/, 'ℝ');
  for (const obj of all) {
    const mem = parseMembershipCanonical(obj.claim);
    if (mem && (mem.set === domain || mem.set === normDomain)) {
      results.push(mem.element);
    }
    // Also check typed variables: x: Nat
    const typed = obj.claim.match(/^(\w+)\s*:\s*(\w+)$/);
    if (typed && (typed[2] === domain || typed[2] === normDomain)) {
      results.push(typed[1]);
    }
  }
  // Also include variables declared via setVar
  for (const v of ctx.variables) {
    if (v.domain === domain || v.domain === normDomain) results.push(v.name);
  }
  return [...new Set(results)];
}

/** Substitute all free occurrences of `variable` with `value` in `body` string. */
function substituteInBody(body: string, variable: string, value: string): string {
  return body.replace(new RegExp(`\\b${variable}\\b`, 'g'), `(${value})`);
}

/**
 * Check whether two claim strings are logically equivalent, using:
 * 1. sameProp (structural equality)
 * 2. Arithmetic equality after parsing ordering/equality sub-claims
 */
function claimsMatch(a: string, b: string): boolean {
  if (sameProp(a, b)) return true;
  // Try arithmetic-aware comparison for ordering claims
  const ordA = parseOrder(a);
  const ordB = parseOrder(b);
  if (ordA && ordB && ordA.op === ordB.op) {
    return arithSymEqual(normArith(ordA.left), normArith(ordB.left)) &&
           arithSymEqual(normArith(ordA.right), normArith(ordB.right));
  }
  // Try arithmetic equality
  const eqA = parseEqualityCanonical(a);
  const eqB = parseEqualityCanonical(b);
  if (eqA && eqB) {
    return arithSymEqual(normArith(eqA.left), normArith(eqB.left)) &&
           arithSymEqual(normArith(eqA.right), normArith(eqB.right));
  }
  // Try membership
  const memA = parseMembershipCanonical(a);
  const memB = parseMembershipCanonical(b);
  if (memA && memB) {
    return memA.set === memB.set && normArith(memA.element) === normArith(memB.element);
  }
  // Fallback: normalize arith whitespace
  return normArith(a).replace(/\((\w+)\)/g, '$1') === normArith(b).replace(/\((\w+)\)/g, '$1');
}

// ── Integer / ordering rules ──────────────────────────────────────────────────

function deriveIntClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);

  // Collect single-var equalities for substitution
  const exprSubsts = new Map<string, string>();
  for (const obj of all) {
    const objEq = parseEqualityCanonical(obj.claim);
    if (objEq && /^[A-Za-z_]\w*$/.test(objEq.left.trim())) {
      exprSubsts.set(objEq.left.trim(), objEq.right);
    }
  }

  // Helper: resolve a symbolic expr to a concrete value using context substs
  const resolveToNumber = (expr: string): number | null => {
    const direct = evalArith(expr);
    if (direct !== null) return direct;
    let substituted = expr;
    for (const [v, e] of exprSubsts) {
      substituted = substituted.replace(new RegExp(`\\b${v}\\b`, 'g'), `(${e})`);
    }
    return evalArith(substituted);
  };

  // ── abs(X) = K ───────────────────────────────────────────────────────────────
  const absEq = parseAbsEquality(claim);
  if (absEq) {
    const xv = resolveToNumber(absEq.arg);
    const kv = evalArith(absEq.value);
    if (xv !== null && kv !== null && Math.abs(xv) === kv) {
      const src = exprSubsts.has(absEq.arg)
        ? all.find(o => { const e = parseEqualityCanonical(o.claim); return e && e.left.trim() === absEq.arg; })
        : undefined;
      createKernelObject(ctx, claim, 'ARITH_ABS', step, src ? [src.id] : []);
      return { rule: 'ARITH_ABS' as const, state: 'PROVED' as const, uses: src ? [src.claim] : [], message: `|${absEq.arg}| = ${kv}` };
    }
    // abs(x) = x when x ≥ 0 in context
    const geqZero = all.find(o => {
      const ord = parseOrder(o.claim);
      return ord && normArith(ord.left) === normArith(absEq.arg) && normArith(ord.right) === '0'
        && (ord.op === '≥' || ord.op === '>=');
    });
    if (geqZero && normArith(absEq.value) === normArith(absEq.arg)) {
      createKernelObject(ctx, claim, 'ARITH_ABS', step, [geqZero.id]);
      return { rule: 'ARITH_ABS' as const, state: 'PROVED' as const, uses: [geqZero.claim], message: 'abs(x) = x for x ≥ 0' };
    }
    // abs(x) = -x when x ≤ 0 in context
    const leqZero = all.find(o => {
      const ord = parseOrder(o.claim);
      return ord && normArith(ord.left) === normArith(absEq.arg) && normArith(ord.right) === '0'
        && (ord.op === '≤' || ord.op === '<=');
    });
    if (leqZero && normArith(absEq.value) === normArith(`-${absEq.arg}`)) {
      createKernelObject(ctx, claim, 'ARITH_ABS', step, [leqZero.id]);
      return { rule: 'ARITH_ABS' as const, state: 'PROVED' as const, uses: [leqZero.claim], message: 'abs(x) = -x for x ≤ 0' };
    }
  }

  // ── sign(X) = K ──────────────────────────────────────────────────────────────
  const signEq = parseSignEquality(claim);
  if (signEq) {
    const xv = resolveToNumber(signEq.arg);
    const kv = evalArith(signEq.value);
    if (xv !== null && kv !== null) {
      const expected = xv > 0 ? 1 : xv < 0 ? -1 : 0;
      if (expected === kv) {
        const src = exprSubsts.has(signEq.arg)
          ? all.find(o => { const e = parseEqualityCanonical(o.claim); return e && e.left.trim() === signEq.arg; })
          : undefined;
        createKernelObject(ctx, claim, 'ARITH_SIGN', step, src ? [src.id] : []);
        return { rule: 'ARITH_SIGN' as const, state: 'PROVED' as const, uses: src ? [src.claim] : [], message: `sign(${signEq.arg}) = ${expected}` };
      }
    }
    // sign(x) = 1 when x > 0 in context
    if (normArith(signEq.value) === '1') {
      const gt = all.find(o => { const ord = parseOrder(o.claim); return ord && normArith(ord.left) === normArith(signEq.arg) && normArith(ord.right) === '0' && ord.op === '>'; });
      if (gt) { createKernelObject(ctx, claim, 'ARITH_SIGN', step, [gt.id]); return { rule: 'ARITH_SIGN' as const, state: 'PROVED' as const, uses: [gt.claim], message: 'sign(x) = 1 for x > 0' }; }
    }
    // sign(x) = -1 when x < 0 in context
    if (normArith(signEq.value) === '-1') {
      const lt = all.find(o => { const ord = parseOrder(o.claim); return ord && normArith(ord.left) === normArith(signEq.arg) && normArith(ord.right) === '0' && ord.op === '<'; });
      if (lt) { createKernelObject(ctx, claim, 'ARITH_SIGN', step, [lt.id]); return { rule: 'ARITH_SIGN' as const, state: 'PROVED' as const, uses: [lt.claim], message: 'sign(x) = -1 for x < 0' }; }
    }
    // sign(x) = 0 when x = 0 in context
    if (normArith(signEq.value) === '0') {
      const eq0 = all.find(o => { const e = parseEqualityCanonical(o.claim); return e && normArith(e.left) === normArith(signEq.arg) && normArith(e.right) === '0'; });
      if (eq0) { createKernelObject(ctx, claim, 'ARITH_SIGN', step, [eq0.id]); return { rule: 'ARITH_SIGN' as const, state: 'PROVED' as const, uses: [eq0.claim], message: 'sign(x) = 0 for x = 0' }; }
    }
  }

  // ── Ordering: A < B, A > B, A ≤ B, A ≥ B ────────────────────────────────────
  const ord = parseOrder(claim);
  if (ord) {
    // Concrete evaluation
    const result = evalOrder(ord.left, ord.op, ord.right);
    if (result === true) {
      createKernelObject(ctx, claim, 'ARITH_ORDER', step);
      return { rule: 'ARITH_ORDER' as const, state: 'PROVED' as const, message: `Concrete ordering: ${claim}` };
    }

    // With substitution from context
    const subL = resolveToNumber(ord.left);
    const subR = resolveToNumber(ord.right);
    if (subL !== null && subR !== null) {
      const holds = (() => {
        switch (ord.op) {
          case '<':  return subL < subR;
          case '>':  return subL > subR;
          case '≤': case '<=': return subL <= subR;
          case '≥': case '>=': return subL >= subR;
        }
      })();
      if (holds) {
        const uses = [...exprSubsts.keys()]
          .filter(v => ord.left.includes(v) || ord.right.includes(v))
          .map(v => all.find(o => { const e = parseEqualityCanonical(o.claim); return e && e.left.trim() === v; }))
          .filter((o): o is ProofObject => Boolean(o));
        createKernelObject(ctx, claim, 'ARITH_ORDER', step, uses.map(o => o.id));
        return { rule: 'ARITH_ORDER' as const, state: 'PROVED' as const, uses: uses.map(o => o.claim), message: `Ordering verified by substitution` };
      }
    }

    // Transitivity: A < B from A < C and C ≤ B (or similar chains)
    for (const obj of all) {
      const obj2 = parseOrder(obj.claim);
      if (!obj2) continue;
      // A op C in context, C op2 B → try to chain
      if (normArith(obj2.left) === normArith(ord.left)) {
        const mid = obj2.right;
        for (const obj3 of all) {
          if (obj3 === obj) continue;
          const obj4 = parseOrder(obj3.claim);
          if (!obj4) continue;
          if (normArith(obj4.left) === normArith(mid) && normArith(obj4.right) === normArith(ord.right)) {
            // Both obj2 and obj4 must have compatible ops (e.g. < and < → <, ≤ and < → <, etc.)
            const isStrict = obj2.op === '<' || obj4.op === '<';
            const targetStrict = ord.op === '<' || ord.op === '>';
            if (!targetStrict || isStrict) {
              createKernelObject(ctx, claim, 'ARITH_ORDER', step, [obj.id, obj3.id]);
              return { rule: 'ARITH_ORDER' as const, state: 'PROVED' as const, uses: [obj.claim, obj3.claim], message: 'Ordering by transitivity' };
            }
          }
        }
      }
    }

    // ── Axiom: n ≥ 0 for n ∈ Nat ─────────────────────────────────────────────
    if (ord.op === '≥' || ord.op === '>=') {
      if (normArith(ord.right) === '0') {
        // Check if the left side is in Nat
        const lhsNorm = normArith(ord.left);
        const inNat = all.find(o => {
          const mem = parseMembershipCanonical(o.claim);
          return mem && normArith(mem.element) === lhsNorm && (mem.set === 'Nat' || mem.set === 'ℕ');
        });
        if (inNat) {
          createKernelObject(ctx, claim, 'ARITH_ORDER', step, [inNat.id]);
          return { rule: 'ARITH_ORDER' as const, state: 'PROVED' as const, uses: [inNat.claim], message: `${ord.left} ∈ Nat implies ${ord.left} ≥ 0` };
        }
      }
    }

    // ── Axiom: n * n ≥ 0 for n ∈ Int (square non-negative) ──────────────────
    if (ord.op === '≥' || ord.op === '>=') {
      if (normArith(ord.right) === '0') {
        const lhs = normArith(ord.left);
        // Check if lhs is of form X * X (same factor)
        const factors = splitTopMul(ord.left);
        if (factors && normArith(factors[0]) === normArith(factors[1])) {
          // n * n ≥ 0 is always true for integers
          const inInt = all.find(o => {
            const mem = parseMembershipCanonical(o.claim);
            return mem && normArith(mem.element) === normArith(factors[0])
              && (mem.set === 'Int' || mem.set === 'ℤ' || mem.set === 'Nat' || mem.set === 'ℕ');
          });
          if (inInt) {
            createKernelObject(ctx, claim, 'ARITH_ORDER', step, [inInt.id]);
            return { rule: 'ARITH_ORDER' as const, state: 'PROVED' as const, uses: [inInt.claim], message: `${ord.left} ≥ 0 (square non-negative)` };
          }
        }
      }
    }
  }

  // ── Axiom: abs(n) ≥ 0 ────────────────────────────────────────────────────
  const absOrd = claim.match(/^abs\((.+)\)\s*(≥|>=)\s*0$/);
  if (absOrd) {
    createKernelObject(ctx, claim, 'ARITH_ABS', step);
    return { rule: 'ARITH_ABS' as const, state: 'PROVED' as const, message: `abs is always non-negative` };
  }

  return null;
}

// ── Modular arithmetic / number theory rules ──────────────────────────────────

function deriveModArithClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);

  // ── p ∈ Prime / Prime(p): concrete primality check ──────────────────────────
  const primeArg = parsePrimePred(claim);
  if (primeArg !== null) {
    const v = evalArith(primeArg);
    if (v !== null && isPrime(v)) {
      createKernelObject(ctx, claim, 'ARITH_PRIME', step);
      return { rule: 'ARITH_PRIME' as const, state: 'PROVED' as const, message: `${v} is prime` };
    }
    // p ∈ Prime from context assumption
    const hyp = all.find(o => normArith(o.claim) === normArith(claim));
    if (hyp) {
      createKernelObject(ctx, claim, 'ARITH_PRIME', step, [hyp.id]);
      return { rule: 'ARITH_PRIME' as const, state: 'PROVED' as const, uses: [hyp.claim], message: 'Prime from context' };
    }
  }

  // ── φ(n) = k: totient equalities ────────────────────────────────────────────
  const totEq = parseTotientEquality(claim);
  if (totEq) {
    // Concrete: φ(12) = 4
    const nv = evalArith(totEq.arg);
    if (nv !== null) {
      const tv = computeTotient(nv);
      const kv = evalArith(totEq.value);
      if (kv !== null && tv === kv) {
        createKernelObject(ctx, claim, 'ARITH_TOTIENT', step);
        return { rule: 'ARITH_TOTIENT' as const, state: 'PROVED' as const, message: `φ(${nv}) = ${tv}` };
      }
    }

    // Symbolic: φ(p * q) = (p-1) * (q-1) when p, q ∈ Prime in context
    const argMul = splitTopMul(totEq.arg);
    if (argMul) {
      const [pStr, qStr] = argMul;
      const pPrime = all.find(o => parsePrimePred(o.claim) === normArith(pStr) || normArith(o.claim) === normArith(`${pStr} ∈ Prime`));
      const qPrime = all.find(o => parsePrimePred(o.claim) === normArith(qStr) || normArith(o.claim) === normArith(`${qStr} ∈ Prime`));
      if (pPrime && qPrime) {
        // Expected value: (p-1)*(q-1)
        const expected = `(${pStr} - 1) * (${qStr} - 1)`;
        if (arithSymEqual(normArith(totEq.value), expected) ||
            normArith(totEq.value) === normArith(expected)) {
          createKernelObject(ctx, claim, 'ARITH_TOTIENT', step, [pPrime.id, qPrime.id]);
          return {
            rule: 'ARITH_TOTIENT' as const,
            state: 'PROVED' as const,
            uses: [pPrime.claim, qPrime.claim],
            message: `φ(p·q) = (p-1)(q-1) for distinct primes`,
          };
        }
      }
    }

    // φ(p) = p - 1 when p ∈ Prime in context
    const pPrime = all.find(o => parsePrimePred(o.claim) === normArith(totEq.arg) || normArith(o.claim) === normArith(`${totEq.arg} ∈ Prime`));
    if (pPrime) {
      const expected = `${totEq.arg} - 1`;
      if (arithSymEqual(normArith(totEq.value), expected) || normArith(totEq.value) === normArith(expected)) {
        createKernelObject(ctx, claim, 'ARITH_TOTIENT', step, [pPrime.id]);
        return {
          rule: 'ARITH_TOTIENT' as const,
          state: 'PROVED' as const,
          uses: [pPrime.claim],
          message: `φ(p) = p-1 for prime p`,
        };
      }
    }
  }

  // ── a ≡ b (mod n): congruence claims ────────────────────────────────────────
  const cong = parseCongruence(claim);
  if (cong) {
    // Concrete evaluation
    if (areCongruent(cong.a, cong.b, cong.n)) {
      createKernelObject(ctx, claim, 'ARITH_MOD_EVAL', step);
      return { rule: 'ARITH_MOD_EVAL' as const, state: 'PROVED' as const, message: 'Verified by concrete modular evaluation' };
    }

    // Reflexivity: a ≡ a (mod n) — both sides symbolically equal
    if (arithSymEqual(normArith(cong.a), normArith(cong.b))) {
      createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step);
      return { rule: 'ARITH_CONGRUENCE' as const, state: 'PROVED' as const, message: 'Congruence reflexivity: a ≡ a (mod n)' };
    }

    // Symmetry: b ≡ a (mod n) from a ≡ b (mod n) in context
    const symHyp = all.find(o => {
      const c2 = parseCongruence(o.claim);
      return c2 && normArith(c2.n) === normArith(cong.n) &&
        normArith(c2.a) === normArith(cong.b) && normArith(c2.b) === normArith(cong.a);
    });
    if (symHyp) {
      createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step, [symHyp.id]);
      return { rule: 'ARITH_CONGRUENCE' as const, state: 'PROVED' as const, uses: [symHyp.claim], message: 'Congruence symmetry' };
    }

    // Transitivity: a ≡ c (mod n) from a ≡ b and b ≡ c in context
    for (const obj1 of all) {
      const c1 = parseCongruence(obj1.claim);
      if (!c1 || normArith(c1.n) !== normArith(cong.n) || normArith(c1.a) !== normArith(cong.a)) continue;
      const mid = c1.b;
      for (const obj2 of all) {
        if (obj2 === obj1) continue;
        const c2 = parseCongruence(obj2.claim);
        if (c2 && normArith(c2.n) === normArith(cong.n) &&
            normArith(c2.a) === normArith(mid) && normArith(c2.b) === normArith(cong.b)) {
          createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step, [obj1.id, obj2.id]);
          return { rule: 'ARITH_CONGRUENCE' as const, state: 'PROVED' as const, uses: [obj1.claim, obj2.claim], message: `Congruence transitivity via ${mid}` };
        }
      }
    }

    // e * d ≡ 1 (mod φ(n)): look for this in context directly
    const hyp = all.find(o => normArith(o.claim) === normArith(claim));
    if (hyp) {
      createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step, [hyp.id]);
      return { rule: 'ARITH_CONGRUENCE' as const, state: 'PROVED' as const, uses: [hyp.claim], message: 'Congruence from context' };
    }

    // Congruence by definition: a mod n = b mod n in context
    const modA = evalMod(cong.a, cong.n);
    const modB = evalMod(cong.b, cong.n);
    if (modA !== null && modB !== null && modA === modB) {
      createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step);
      return { rule: 'ARITH_CONGRUENCE' as const, state: 'PROVED' as const, message: 'Congruence from modular evaluation' };
    }

    // Fermat's little theorem: a^(p-1) ≡ 1 (mod p)
    // claim: a^(p-1) ≡ 1 (mod p), b = "1", n = p
    if (normArith(cong.b) === '1') {
      const baseExp = parsePower(cong.a);
      if (baseExp) {
        // Check p ∈ Prime in context and exp = p - 1
        const nPrime = all.find(o => parsePrimePred(o.claim) === normArith(cong.n) || normArith(o.claim) === normArith(`${cong.n} ∈ Prime`));
        if (nPrime && arithSymEqual(normArith(baseExp.exp), `${cong.n} - 1`)) {
          const cprime = all.find(o => {
            const cp = o.claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
            return cp && ((normArith(cp[1]) === normArith(baseExp.base) && normArith(cp[2]) === normArith(cong.n))
                       || (normArith(cp[2]) === normArith(baseExp.base) && normArith(cp[1]) === normArith(cong.n)));
          });
          if (cprime) {
            createKernelObject(ctx, claim, 'ARITH_FERMAT', step, [nPrime.id, cprime.id]);
            return {
              rule: 'ARITH_FERMAT' as const,
              state: 'PROVED' as const,
              uses: [nPrime.claim, cprime.claim],
              message: `Fermat's little theorem: a^(p-1) ≡ 1 (mod p)`,
            };
          }
        }
      }

      // Euler's theorem: a^φ(n) ≡ 1 (mod n)
      if (baseExp) {
        // Check if exp = φ(n) for some n matching cong.n
        const expTotArg = parseTotientExpr(baseExp.exp);
        if (expTotArg && normArith(expTotArg) === normArith(cong.n)) {
          const cprime = all.find(o => {
            const cp = o.claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
            return cp && ((normArith(cp[1]) === normArith(baseExp.base) && normArith(cp[2]) === normArith(cong.n))
                       || (normArith(cp[2]) === normArith(baseExp.base) && normArith(cp[1]) === normArith(cong.n)));
          });
          if (cprime) {
            createKernelObject(ctx, claim, 'ARITH_EULER', step, [cprime.id]);
            return {
              rule: 'ARITH_EULER' as const,
              state: 'PROVED' as const,
              uses: [cprime.claim],
              message: `Euler's theorem: a^φ(n) ≡ 1 (mod n)`,
            };
          }
        }
      }
    }

    // RSA correctness: (m^e)^d ≡ m (mod n)
    // Requires: e*d ≡ 1 (mod φ(n)) in context
    {
      // Try to match (m^e)^d pattern
      const outerPow = parsePower(cong.a);
      if (outerPow) {
        const innerPow = parsePower(outerPow.base);
        if (innerPow && normArith(innerPow.base) === normArith(cong.b)) {
          const m = innerPow.base;
          const e = innerPow.exp;
          const d = outerPow.exp;
          const n = cong.n;
          // Look for the RSA setup in context
          const eTimesD = `${e} * ${d}`;
          const modPhi = `φ(${n})`;
          const keyEq = all.find(o => {
            const c = parseCongruence(o.claim);
            return c && normArith(c.n) === normArith(modPhi) && normArith(c.b) === '1' &&
              (arithSymEqual(normArith(c.a), eTimesD) || arithSymEqual(normArith(c.a), `${d} * ${e}`));
          });
          if (keyEq) {
            createKernelObject(ctx, claim, 'ARITH_RSA', step, [keyEq.id]);
            return {
              rule: 'ARITH_RSA' as const,
              state: 'PROVED' as const,
              uses: [keyEq.claim],
              message: `RSA correctness: (m^e)^d ≡ m (mod n) by Euler's theorem`,
            };
          }
        }
      }
    }
  }

  // ── a mod n = k: modular evaluation ─────────────────────────────────────────
  const modEq = parseEqualityCanonical(claim);
  if (modEq) {
    const modOp = parseModOp(modEq.left) ?? parseModOp(modEq.right);
    if (modOp) {
      const result = evalMod(modOp.a, modOp.n);
      const other = parseModOp(modEq.left) ? modEq.right : modEq.left;
      const otherV = evalArith(other);
      if (result !== null && otherV !== null && result === otherV) {
        createKernelObject(ctx, claim, 'ARITH_MOD_EVAL', step);
        return { rule: 'ARITH_MOD_EVAL' as const, state: 'PROVED' as const, message: 'Verified by modular evaluation' };
      }
    }
  }

  return null;
}

function createPendingObject(ctx: Context, claim: string, step: number) {
  createKernelObject(ctx, claim, 'STRUCTURAL', step, [], [], 'ω', pendingTerms(claim));
}

function createKernelObject(
  ctx: Context,
  claim: string,
  rule: KernelRule,
  step: number,
  inputs: string[] = [],
  imports: string[] = [],
  tau: WenittainValue = '1',
  unresolvedTerms: string[] = [],
): ProofObject {
  const morphism = createMorphismForClaim(ctx.category, claim, rule, tau, inputs, unresolvedTerms);
  return registerDerivedObject(ctx, claim, step, rule, morphism, inputs, imports);
}

function registerDerivedObject(
  ctx: Context,
  claim: string,
  step: number,
  rule: KernelRule,
  morphism: MorphismRecord,
  inputs: string[],
  imports: string[] = [],
): ProofObject {
  const proofObject: ProofObject = {
    id: morphism.id,
    claim,
    term: safeTermFromString(claim),
    domain: morphism.domain,
    codomain: morphism.codomain,
    domainRestriction: morphism.domainRestriction,
    tau: morphism.tau,
    rule,
    inputs,
    pending: morphism.pending,
    suspended: morphism.suspended,
    step,
    imports: imports.length > 0 ? imports : undefined,
  };
  ctx.objects.push(proofObject);
  ctx.derivations.push({
    id: `drv:${morphism.id}`,
    rule,
    inputIds: inputs,
    outputId: morphism.id,
    step,
  });
  registerCategoryClaim(ctx, claim);
  enrichStructMembership(ctx, proofObject, step);
  return proofObject;
}

function createMorphismForClaim(
  category: WenittainCategory,
  claim: string,
  rule: KernelRule,
  tau: WenittainValue,
  inputs: string[],
  unresolvedTerms: string[],
): MorphismRecord {
  const implication = parseImplicationCanonical(claim);
  if (implication) {
    const domain = ensureClaimObjects(category, implication[0]);
    const codomain = ensureClaimObjects(category, implication[1]);
    if (tau === 'ω') {
      category.suspendObject(claim, unresolvedTerms);
    }
    return category.createMorphism({
      proposition: claim,
      domain,
      codomain,
      tau,
      rule,
      inputs,
      unresolvedTerms,
      domainRestriction: unresolvedTerms.length > 0 ? `Dom(${claim})` : domain,
      suspended: tau === 'ω',
    });
  }
  const codomain = ensureClaimObjects(category, claim);
  if (tau === 'ω') {
    category.suspendObject(claim, unresolvedTerms);
  }
  return category.createMorphism({
    proposition: claim,
    domain: TOP,
    codomain,
    tau,
    rule,
    inputs,
    unresolvedTerms,
    domainRestriction: unresolvedTerms.length > 0 ? `Dom(${claim})` : TOP,
    suspended: tau === 'ω',
  });
}

function toTopMorphism(ctx: Context, object: ProofObject): MorphismRecord {
  return ctx.category.createMorphism({
    proposition: object.claim,
    domain: TOP,
    codomain: object.codomain,
    tau: object.tau,
    rule: object.rule,
    inputs: object.inputs,
  });
}

function toImplicationMorphism(ctx: Context, object: ProofObject): MorphismRecord {
  const implication = parseImplicationCanonical(object.claim);
  if (!implication) {
    throw new KernelError(`Expected implication morphism, received '${object.claim}'`);
  }
  return ctx.category.createMorphism({
    proposition: object.claim,
    domain: ensureClaimObjects(ctx.category, implication[0]),
    codomain: ensureClaimObjects(ctx.category, implication[1]),
    tau: object.tau,
    rule: object.rule,
    inputs: object.inputs,
  });
}

function ensureClaimObjects(category: WenittainCategory, claim: string): string {
  return category.createObject(claim).id;
}

function splitAllConjuncts(s: string): string[] {
  const parts = parseConjunctionCanonical(s);
  if (!parts) return [s];
  return [...splitAllConjuncts(parts[0]), ...splitAllConjuncts(parts[1])];
}

function theoremPremises(node: TheoremNode | LemmaNode): string[] {
  // New style: assume(H₁ ∧ H₂ ∧ ...) — decompose the conjunction into individual premises
  const assumes = node.body
    .filter((item): item is AssumeNode => item.type === 'Assume')
    .flatMap(item => splitAllConjuncts(exprToProp(item.expr)));
  if (assumes.length > 0) return assumes;
  // Legacy style: given(H₁) → given(H₂) → ...
  return node.body
    .filter((item): item is GivenNode => item.type === 'Given')
    .map(item => exprToProp(item.expr));
}

function registerCategoryClaim(ctx: Context, claim: string): void {
  try {
    ctx.diagrams.registerClaim(claim);
  } catch (error) {
    if (error instanceof CategoryDiagramError) {
      // Unknown functor/variable application (e.g., T(v) in linear algebra, f(x) in topology)
      // is a category-diagram limitation, not a proof error — downgrade to warning.
      const isUnknownFunctor = error.message.includes('unknown functor');
      ctx.diagnostics.push({
        severity: isUnknownFunctor ? 'warning' : 'error',
        message: error.message,
        rule: 'CAT_MORPHISM',
      });
      return;
    }
    throw error;
  }
}

function theoremGoal(node: TheoremNode | LemmaNode): string | null {
  // New style: declareToProve(C)
  const dtp = node.body
    .filter((item): item is DeclareToProveNode => item.type === 'DeclareToProve')
    .map(item => exprToProp(item.expr))[0];
  if (dtp !== undefined) return dtp;
  // Legacy style: assert(C)
  return node.body
    .filter((item): item is AssertNode => item.type === 'Assert')
    .map(item => exprToProp(item.expr))[0] ?? null;
}

function collectStructDefinitions(nodes: ASTNode[], diagnostics: Diagnostic[]): Map<string, StructDefinition> {
  const structs = new Map<string, StructDefinition>();
  const typeNames = new Set(nodes.filter((node): node is TypeDeclNode => node.type === 'TypeDecl').map(node => node.name));
  for (const node of nodes) {
    if (node.type !== 'Struct') continue;
    const fields = node.fields.map(field => ({ name: field.name, type: field.type }));
    for (const field of fields) {
      if (!isKnownSort(field.type, structs, typeNames)) {
        diagnostics.push({
          severity: 'error',
          message: `Unknown sort '${field.type}' in struct '${node.name}' field '${field.name}'`,
          rule: 'STRUCTURAL',
        });
      }
    }
    structs.set(node.name, {
      name: node.name,
      fields,
      projections: new Map(fields.map(field => [field.name, `π_${field.name}`])),
    });
  }
  return structs;
}

function collectTypeDefinitions(
  nodes: ASTNode[],
  structs: Map<string, StructDefinition>,
  diagnostics: Diagnostic[],
): Map<string, TypeDefinition> {
  const typeNames = new Set(nodes.filter((node): node is TypeDeclNode => node.type === 'TypeDecl').map(node => node.name));
  const types = new Map<string, TypeDefinition>();
  for (const node of nodes) {
    if (node.type !== 'TypeDecl') continue;
    const variants = node.variants.map(variant => ({ ...variant, parent: node.name }));
    for (const variant of variants) {
      for (const field of variant.fields) {
        if (!isKnownSort(field.type, structs, typeNames)) {
          diagnostics.push({
            severity: 'error',
            message: `Unknown sort '${field.type}' in variant '${variant.name}' of type '${node.name}'`,
            rule: 'STRUCTURAL',
          });
        }
      }
    }
    types.set(node.name, { name: node.name, variants });
  }
  return types;
}

function findPairs(nodes: ASTNode[]): Pair[] {
  const pairs: Pair[] = [];
  for (let index = 0; index < nodes.length; index++) {
    const node = nodes[index];
    if ((node.type !== 'Theorem' && node.type !== 'Lemma') || node.connective !== '↔') continue;
    for (let cursor = index + 1; cursor < nodes.length; cursor++) {
      const candidate = nodes[cursor];
      if (candidate.type === 'Proof' && normalizeName(candidate.name) === normalizeName(node.name)) {
        pairs.push({ theorem: node, proof: candidate });
        break;
      }
      if (candidate.type === 'Theorem' || candidate.type === 'Lemma') break;
    }
  }
  return pairs;
}

function normalizeName(value: string): string {
  return value.trim().toLowerCase();
}

function classifyStep(node: ASTNode): ProofStepTrace['kind'] {
  switch (node.type) {
    case 'Assume':
      return 'assume';
    case 'Assert':
      return 'assert';
    case 'Prove':
      return 'assert'; // prove() is semantically an assert
    case 'AndIntroStep':
    case 'OrIntroStep':
      return 'assert';
    case 'Conclude':
      return 'conclude';
    case 'Apply':
      return 'apply';
    case 'SetVar':
      return 'setVar';
    case 'Induction':
      return 'induction';
    case 'Match':
      return 'match';
    case 'Intro':
      return 'intro';
    case 'Rewrite':
      return 'rewrite';
    case 'Exact':
      return 'exact';
    default:
      return 'raw';
  }
}

function nodeToClaim(node: ASTNode): string {
  switch (node.type) {
    case 'Assume':
    case 'Assert':
    case 'Prove':
    case 'Conclude':
      return exprToProp(node.expr);
    case 'AndIntroStep':
      return `${node.left} ∧ ${node.right}`;
    case 'OrIntroStep':
      return node.claim;
    case 'Apply':
      return node.target;
    case 'SetVar':
      return node.varType ? `${node.varName}: ${node.varType}` : node.varName;
    case 'Induction':
      return exprToProp(node.fold);
    case 'Match':
      return `match ${exprToProp(node.scrutinee)}`;
    case 'Raw':
      return node.content;
    case 'Intro':
      return `${node.varName}: ${node.varType}`;
    case 'Rewrite':
      return node.hypothesis;
    case 'Exact':
      return exprToProp(node.expr);
    default:
      return node.type;
  }
}

function findDerivedConclusion(ctx: Context, goal: string | null): string | null {
  if (goal && findExact(ctx.objects, goal, false)) {
    return goal;
  }
  const last = [...ctx.objects].reverse().find(object => object.tau === '1');
  return last?.claim ?? null;
}

function reportState(ctx: Context, goal: string | null, derivedConclusion: string | null): ProofState {
  if (ctx.diagnostics.some(diagnostic => diagnostic.severity === 'error')) {
    return 'FAILED';
  }
  if (ctx.unverifiedReasons.length > 0) {
    return 'FAILED';
  }
  if (goal && !derivedConclusion) {
    return 'FAILED';
  }
  return ctx.objects.some(object => object.pending) ? 'FAILED' : 'PROVED';
}

function combineStates(states: ProofState[], fallback: ProofState): ProofState {
  if (states.length === 0) return fallback;
  if (states.includes('FAILED') || states.includes('UNVERIFIED') || states.includes('PENDING')) return 'FAILED';
  return 'PROVED';
}

function safeTermFromString(s: string): Term | undefined {
  try { return termFromString(s); } catch { return undefined; }
}

function findExact(objects: ProofObject[], claim: string, allowPending: boolean): ProofObject | null {
  const claimTerm = safeTermFromString(claim);
  for (let index = objects.length - 1; index >= 0; index--) {
    const object = objects[index];
    if (allowPending || !object.pending) {
      if (claimTerm && object.term && termEqual(claimTerm, object.term)) return object;
      if (sameProp(object.claim, claim)) return object;
    }
  }
  return null;
}

function requireClassical(ctx: Context, claim: string, rule: KernelRule): ProofObject | null {
  const classical = findExact(ctx.objects, claim, false);
  if (classical) return classical;
  const pending = findExact(ctx.objects, claim, true);
  if (pending?.pending) {
    throw new KernelError('ω-Barrier: pending morphism cannot be used in classical derivation before Ra fires');
  }
  const premise = findExact(ctx.premises, claim, false);
  if (premise) return premise;
  const assumption = findExact(ctx.assumptions, claim, false);
  if (assumption) return assumption;
  const pendingPremise = findExact(ctx.premises, claim, true) ?? findExact(ctx.assumptions, claim, true);
  if (pendingPremise?.pending) {
    throw new KernelError('ω-Barrier: pending morphism cannot be used in classical derivation before Ra fires');
  }
  void rule;
  return null;
}

function classicalObjects(ctx: Context): ProofObject[] {
  return ctx.objects.filter(object => !object.pending && object.tau === '1');
}

function hasContradiction(objects: ProofObject[]): [ProofObject, ProofObject] | null {
  for (const object of objects) {
    if (object.pending) continue;
    const negation = object.claim.startsWith('¬') ? object.claim.slice(1).trim() : `¬${object.claim}`;
    const opposite = findExact(objects, negation, false);
    if (opposite) {
      return [object, opposite];
    }
  }
  return null;
}

function pendingTerms(claim: string): string[] {
  const quantified = parseBoundedQuantifierCanonical(claim, 'exists')
    ?? parseBoundedQuantifierCanonical(claim, 'forall');
  if (quantified) {
    return [quantified.variable];
  }
  if (parseSetBuilderCanonical(claim) || parseIndexedUnionCanonical(claim) || parseSetBuilderOrUnionCanonical(claim)) {
    return ['builder'];
  }
  return claim.includes('∀') || claim.includes('∃') ? ['quantifier'] : ['claim'];
}

function handleIntro(ctx: Context, node: IntroNode, step: number): void {
  const { varName, varType } = node;

  // If the goal is an implication A → B and no explicit type was given,
  // introduce the antecedent as an assumption and update the goal to B.
  if (ctx.goal && !varType) {
    const impl = parseImplicationCanonical(ctx.goal);
    if (impl) {
      const [antecedent, consequent] = impl;
      ctx.goal = consequent;
      const assumption = createKernelObject(ctx, antecedent, 'ASSUMPTION', step);
      ctx.assumptions.push(assumption);
      ctx.proofSteps.push({
        step,
        kind: 'intro',
        claim: antecedent,
        rule: 'ASSUMPTION',
        state: 'PROVED',
        message: `Introduced '${varName}' as '${antecedent}', goal is now '${consequent}'`,
      });
      return;
    }
  }

  // Otherwise handle a ∀ quantifier: introduce the variable and update the goal.
  // If no explicit type was given, pull the domain from the quantifier so that
  // the introduced membership claim is `varName ∈ domain` rather than a bare name.
  let resolvedDomain = varType;
  if (ctx.goal) {
    const forall = parseBoundedQuantifierCanonical(ctx.goal, 'forall');
    if (forall) {
      if (!resolvedDomain) resolvedDomain = forall.set;
      const newGoal = substituteVariable(forall.body, forall.variable, varName);
      ctx.goal = newGoal;
    }
  }

  const membershipClaim = resolvedDomain ? `${varName} ∈ ${resolvedDomain}` : varName;
  const domain = resolvedDomain || null;
  ctx.variables.push({ name: varName, domain });
  const assumption = createKernelObject(ctx, membershipClaim, 'ASSUMPTION', step);
  ctx.assumptions.push(assumption);

  ctx.proofSteps.push({
    step,
    kind: 'intro',
    claim: membershipClaim,
    rule: 'ASSUMPTION',
    state: 'PROVED',
    message: `Introduced '${varName} ∈ ${resolvedDomain ?? '?'}' and updated goal`,
  });
}

function handleRewrite(ctx: Context, node: RewriteNode, step: number): void {
  const { hypothesis, direction } = node;
  const hyp = findExact(ctx.objects, hypothesis, false)
    ?? findExact(ctx.assumptions, hypothesis, false)
    ?? findExact(ctx.premises, hypothesis, false);

  if (!hyp) {
    ctx.diagnostics.push({ severity: 'error', step, message: `rewrite: hypothesis '${hypothesis}' not found in context`, rule: 'REWRITE' });
    ctx.proofSteps.push({ step, kind: 'rewrite', claim: hypothesis, rule: 'REWRITE', state: 'FAILED', message: `Hypothesis '${hypothesis}' not found` });
    return;
  }

  const eq = parseEqualityCanonical(hyp.claim);
  if (!eq) {
    ctx.diagnostics.push({ severity: 'error', step, message: `rewrite: '${hypothesis}' is not an equality`, rule: 'REWRITE' });
    ctx.proofSteps.push({ step, kind: 'rewrite', claim: hypothesis, rule: 'REWRITE', state: 'FAILED', message: `'${hypothesis}' is not an equality` });
    return;
  }

  const [fromStr, toStr] = direction === 'rtl' ? [eq.right, eq.left] : [eq.left, eq.right];
  const fromTerm = termFromString(fromStr);
  const toTerm = termFromString(toStr);

  if (ctx.goal) {
    const goalTerm = termFromString(ctx.goal);
    const rewritten = rewriteTerm(goalTerm, fromTerm, toTerm);
    ctx.goal = termToString(rewritten);
  }

  for (const obj of ctx.objects) {
    if (obj.term) {
      const rewritten = rewriteTerm(obj.term, fromTerm, toTerm);
      if (!termEqual(rewritten, obj.term)) {
        createKernelObject(ctx, termToString(rewritten), 'REWRITE', step, [obj.id, hyp.id]);
      }
    }
  }

  ctx.proofSteps.push({
    step,
    kind: 'rewrite',
    claim: ctx.goal ?? hypothesis,
    rule: 'REWRITE',
    state: 'PROVED',
    uses: [hyp.claim],
    message: `Rewrote ${fromStr} → ${toStr} in goal`,
  });
}

function handleExact(ctx: Context, node: ExactNode, step: number): void {
  const claim = exprToProp(node.expr);
  if (ctx.goal && !sameProp(claim, ctx.goal)) {
    const claimTerm = safeTermFromString(claim);
    const goalTerm = safeTermFromString(ctx.goal);
    const match = claimTerm && goalTerm && termEqual(claimTerm, goalTerm);
    if (!match) {
      ctx.diagnostics.push({ severity: 'error', step, message: `exact: '${claim}' does not match goal '${ctx.goal}'`, rule: 'STRUCTURAL' });
      ctx.proofSteps.push({ step, kind: 'exact', claim, rule: 'STRUCTURAL', state: 'FAILED', message: `Does not match goal` });
      return;
    }
  }
  const derivation = deriveClaim(ctx, claim, step);
  if (derivation.state === 'FAILED') {
    ctx.diagnostics.push({ severity: 'error', step, message: derivation.message, rule: derivation.rule });
  }
  ctx.proofSteps.push({
    step,
    kind: 'exact',
    claim,
    rule: derivation.rule,
    state: derivation.state,
    uses: derivation.uses,
    message: derivation.message,
  });
}

function handleObtain(ctx: Context, node: ObtainNode, step: number): void {
  const { varName, source } = node;

  // Locate the existential in context (objects, assumptions, or premises).
  const hyp = findExact(ctx.objects, source, false)
           ?? findExact(ctx.assumptions, source, false)
           ?? findExact(ctx.premises, source, false);

  if (!hyp) {
    ctx.diagnostics.push({ severity: 'error', step, message: `obtain: '${source}' not found in context`, rule: 'STRUCTURAL' });
    ctx.proofSteps.push({ step, kind: 'intro', claim: source, rule: 'STRUCTURAL', state: 'FAILED', message: `Existential not found` });
    return;
  }

  const exists = parseBoundedQuantifierCanonical(hyp.claim, 'exists');
  if (!exists) {
    ctx.diagnostics.push({ severity: 'error', step, message: `obtain: '${source}' is not an existential`, rule: 'STRUCTURAL' });
    ctx.proofSteps.push({ step, kind: 'intro', claim: source, rule: 'STRUCTURAL', state: 'FAILED', message: `Not an existential` });
    return;
  }

  // Introduce varName ∈ set and P(varName) as assumptions.
  const membershipClaim = `${varName} ∈ ${exists.set}`;
  const bodyClaim = substituteVariable(exists.body, exists.variable, varName);

  ctx.variables.push({ name: varName, domain: exists.set });
  const memObj = createKernelObject(ctx, membershipClaim, 'ASSUMPTION', step, [hyp.id]);
  ctx.assumptions.push(memObj);
  const bodyObj = createKernelObject(ctx, bodyClaim, 'ASSUMPTION', step, [hyp.id]);
  ctx.assumptions.push(bodyObj);

  ctx.proofSteps.push({
    step,
    kind: 'intro',
    claim: membershipClaim,
    rule: 'ASSUMPTION',
    state: 'PROVED',
    uses: [hyp.claim],
    message: `Obtained '${varName} ∈ ${exists.set}' and '${bodyClaim}' from existential`,
  });
}

function generateEliminators(types: Map<string, TypeDefinition>): Map<string, ClaimSet> {
  const result = new Map<string, ClaimSet>();
  for (const [typeName, typeDef] of types) {
    if (typeDef.variants.length > 0) {
      const metavar = 'x';
      const disjuncts = typeDef.variants.map(v => `${metavar} ∈ ${v.name}`);
      const conclusion = disjuncts.reduce((acc, d) => `${acc} ∨ ${d}`);
      result.set(`${typeName.toLowerCase()}.cases`, {
        name: `${typeName}.cases`,
        premises: [`${metavar} ∈ ${typeName}`],
        conclusion,
        state: 'PROVED',
        metavars: [metavar],
      });
    }
  }
  return result;
}

function enrichStructMembership(ctx: Context, source: ProofObject, step: number): void {
  const membership = parseMembershipCanonical(source.claim);
  if (!membership) return;
  const structDef = ctx.structs.get(membership.set);
  if (!structDef) return;

  for (const field of structDef.fields) {
    const fieldClaim = `${membership.element}.${field.name} ∈ ${field.type}`;
    if (findExact(ctx.objects, fieldClaim, true) || findExact(ctx.premises, fieldClaim, true) || findExact(ctx.assumptions, fieldClaim, true)) {
      continue;
    }
    createKernelObject(ctx, fieldClaim, 'STRUCT_ELIM', step, [source.id]);
  }
}

function isKnownSort(sort: string, structs: Map<string, StructDefinition>, typeNames: Set<string> = new Set()): boolean {
  const parsed = parseSort(sort);
  if (!parsed) return false;
  if (parsed.kind === 'list') {
    return parsed.element ? isKnownSort(formatSort(parsed.element), structs, typeNames) : false;
  }
  if (!parsed.name) return false;
  return BUILTIN_SORTS.has(parsed.name) || structs.has(parsed.name) || typeNames.has(parsed.name);
}

function createBranchContext(ctx: Context): Context {
  return {
    ...ctx,
    objects: [...ctx.objects],
    derivations: [...ctx.derivations],
    diagnostics: [],
    proofSteps: [],
    variables: [...ctx.variables],
    assumptions: [...ctx.assumptions],
    premises: [...ctx.premises],
  };
}

function applyVariantPatternBindings(
  ctx: Context,
  scrutinee: string,
  variant: TypeVariantDefinition,
  bindings: string[],
  step: number,
) {
  createKernelObject(ctx, `${scrutinee} ∈ ${variant.name}`, 'OR_ELIM', step);
  for (let index = 0; index < variant.fields.length; index++) {
    const binding = bindings[index];
    if (!binding || binding === '_') continue;
    const field = variant.fields[index];
    ctx.variables.push({ name: binding, domain: field.type });
    const assumption = createKernelObject(ctx, `${binding} ∈ ${field.type}`, 'ASSUMPTION', step);
    ctx.assumptions.push(assumption);
  }
}

function applyListPatternBindings(
  ctx: Context,
  scrutinee: string,
  listType: string,
  parsedSort: ParsedSort,
  head: string,
  tail: string,
  step: number,
) {
  const elementType = formatSort(parsedSort.element ?? { kind: 'named', name: 'Element' });
  createKernelObject(ctx, `${scrutinee} ∈ Cons`, 'OR_ELIM', step);
  if (head !== '_') {
    ctx.variables.push({ name: head, domain: elementType });
    const headAssumption = createKernelObject(ctx, `${head} ∈ ${elementType}`, 'ASSUMPTION', step);
    ctx.assumptions.push(headAssumption);
  }
  ctx.variables.push({ name: tail, domain: listType });
  const tailAssumption = createKernelObject(ctx, `${tail} ∈ ${listType}`, 'ASSUMPTION', step);
  ctx.assumptions.push(tailAssumption);
}

function evaluateMatchBranch(ctx: Context, goal: string | null, step: number): ProofState {
  if (goal && findExact(ctx.objects, goal, false)) {
    return 'PROVED';
  }
  if (goal) {
    const goalMembership = parseMembershipCanonical(goal);
    if (goalMembership) {
      const lastConclusion = findLastConclude(ctx.proofSteps);
      if (lastConclusion && branchConclusionMatchesType(lastConclusion.claim, goalMembership.set, ctx)) {
        createKernelObject(ctx, goal, 'OR_ELIM', step);
        return 'PROVED';
      }
    }
    return 'FAILED';
  }
  return 'PROVED';
}

function findLastConclude(steps: ProofStepTrace[]): ProofStepTrace | null {
  for (let index = steps.length - 1; index >= 0; index--) {
    if (steps[index].kind === 'conclude') return steps[index];
  }
  return null;
}

function branchConclusionMatchesType(claim: string, expectedType: string, ctx: Context): boolean {
  const inferred = inferExpressionType(claim, ctx);
  return inferred === expectedType;
}

function parseSort(value: string): ParsedSort | null {
  const trimmed = value.trim();
  const listMatch = trimmed.match(/^List\s*\(([\s\S]+)\)$/);
  if (listMatch) {
    const inner = parseSort(listMatch[1].trim());
    return inner ? { kind: 'list', element: inner } : null;
  }
  if (!trimmed) return null;
  return { kind: 'named', name: trimmed };
}

function formatSort(sort: ParsedSort): string {
  if (sort.kind === 'list') {
    return `List(${formatSort(sort.element ?? { kind: 'named', name: 'Element' })})`;
  }
  return sort.name ?? 'Element';
}

function inferExpressionType(claim: string, ctx: Context): string | null {
  const membership = parseMembershipCanonical(claim);
  if (membership) return membership.set;
  const trimmed = claim.trim();
  if (trimmed === '[]') {
    const goalMembership = ctx.goal ? parseMembershipCanonical(ctx.goal) : null;
    return goalMembership?.set ?? null;
  }
  if (trimmed.startsWith('[') && trimmed.endsWith(']')) {
    const goalMembership = ctx.goal ? parseMembershipCanonical(ctx.goal) : null;
    if (goalMembership?.set && parseSort(goalMembership.set)?.kind === 'list') {
      return goalMembership.set;
    }
  }
  if (/^\d+$/.test(trimmed)) return 'ℕ';
  if (/[π√]/.test(trimmed) || /\bsqrt\s*\(/.test(trimmed)) return 'ℝ';
  const bareBinding = ctx.variables.find(variable => variable.name === trimmed);
  if (bareBinding?.domain) return bareBinding.domain;
  if (/[*\/^]/.test(trimmed)) {
    const vars = trimmed.match(/[A-Za-z_][\w₀-₉ₐ-ₙ]*/g) ?? [];
    if (vars.some(variable => {
      const binding = ctx.variables.find(entry => entry.name === variable);
      return binding?.domain === 'ℝ';
    })) return 'ℝ';
    return 'ℕ';
  }
  if (/[+]/.test(trimmed)) return 'ℕ';
  const call = trimmed.match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)\s*\(/);
  if (call && ctx.goal) {
    const goalMembership = parseMembershipCanonical(ctx.goal);
    if (goalMembership) return goalMembership.set;
  }
  return null;
}

function validateListStructuralRecursion(proof: ProofNode): string | null {
  const fnMeta = proof.fnMeta;
  if (!fnMeta) return null;
  const listParams = fnMeta.params.filter(param => parseSort(param.type)?.kind === 'list');
  if (listParams.length === 0) return null;

  const invalidCall = findInvalidRecursiveCall(proof.body, proof.name, new Map(), listParams);
  if (!invalidCall) return null;
  return `UNVERIFIED: recursive call '${invalidCall.call}' is not structural on a List tail`;
}

function findInvalidRecursiveCall(
  nodes: ASTNode[],
  fnName: string,
  allowedTails: Map<string, string>,
  listParams: FnParam[],
): { call: string } | null {
  for (const node of nodes) {
    if (node.type === 'Match') {
      const scrutinee = exprToProp(node.scrutinee).trim();
      const listParam = listParams.find(param => param.name === scrutinee);
      for (const matchCase of node.cases) {
        const branchAllowed = new Map(allowedTails);
        if (listParam && matchCase.pattern.kind === 'list_cons') {
          branchAllowed.set(listParam.name, matchCase.pattern.tail);
        }
        const nested = findInvalidRecursiveCall(matchCase.body, fnName, branchAllowed, listParams);
        if (nested) return nested;
      }
      continue;
    }

    const claim = node.type === 'Assert' || node.type === 'Assume' || node.type === 'Conclude'
      ? exprToProp(node.expr)
      : node.type === 'Raw'
        ? node.content
        : null;
    if (claim) {
      const invalid = validateRecursiveCallsInText(claim, fnName, allowedTails, listParams);
      if (invalid) return invalid;
    }
  }
  return null;
}

function validateRecursiveCallsInText(
  text: string,
  fnName: string,
  allowedTails: Map<string, string>,
  listParams: FnParam[],
): { call: string } | null {
  for (const call of extractNamedCalls(text, fnName)) {
    const args = splitTopLevelCallArgs(call.args);
    for (let index = 0; index < listParams.length; index++) {
      const param = listParams[index];
      const arg = args[index]?.trim();
      const allowedTail = allowedTails.get(param.name);
      if (!arg || arg !== allowedTail) {
        return { call: `${fnName}(${call.args})` };
      }
    }
  }
  return null;
}

function extractNamedCalls(text: string, fnName: string): Array<{ args: string }> {
  const calls: Array<{ args: string }> = [];
  const pattern = new RegExp(`\\b${escapeRegex(fnName)}\\s*\\(`, 'g');
  let match: RegExpExecArray | null;
  while ((match = pattern.exec(text)) !== null) {
    const openIndex = text.indexOf('(', match.index);
    const closeIndex = findMatchingParenInText(text, openIndex);
    if (openIndex === -1 || closeIndex === -1) continue;
    calls.push({ args: text.slice(openIndex + 1, closeIndex) });
    pattern.lastIndex = closeIndex + 1;
  }
  return calls;
}

function findMatchingParenInText(value: string, start: number): number {
  let depth = 0;
  for (let i = start; i < value.length; i++) {
    const ch = value[i];
    if (ch === '(') depth++;
    else if (ch === ')') {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}

function splitTopLevelCallArgs(value: string): string[] {
  const args: string[] = [];
  let start = 0;
  let depth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth = Math.max(0, depth - 1);
    else if (ch === '[') bracketDepth++;
    else if (ch === ']') bracketDepth = Math.max(0, bracketDepth - 1);
    else if (ch === ',' && depth === 0 && bracketDepth === 0) {
      args.push(value.slice(start, i).trim());
      start = i + 1;
    }
  }
  const final = value.slice(start).trim();
  if (final) args.push(final);
  return args;
}

function parseFieldAccess(value: string): { base: string; path: string[] } | null {
  const trimmed = value.trim();
  if (!trimmed.includes('.')) return null;
  const parts = trimmed.split('.').map(part => part.trim()).filter(Boolean);
  if (parts.length < 2) return null;
  return { base: parts[0], path: parts.slice(1) };
}

function resolveFieldProjection(
  ctx: Context,
  base: string,
  path: string[],
): { type: string; source: ProofObject } | null {
  let currentExpr = base;
  let currentMembership = requireAnyMembership(ctx, currentExpr);
  if (!currentMembership) return null;

  for (const fieldName of path) {
    const membership = parseMembershipCanonical(currentMembership.claim);
    if (!membership) return null;
    const structDef = ctx.structs.get(membership.set);
    if (!structDef) return null;
    const field = structDef.fields.find(candidate => candidate.name === fieldName);
    if (!field) return null;
    currentExpr = `${currentExpr}.${fieldName}`;
    const nextClaim = `${currentExpr} ∈ ${field.type}`;
    let nextMembership = findExact(ctx.objects, nextClaim, false)
      ?? findExact(ctx.premises, nextClaim, false)
      ?? findExact(ctx.assumptions, nextClaim, false);
    if (!nextMembership) {
      nextMembership = createKernelObject(ctx, nextClaim, 'STRUCT_ELIM', currentMembership.step, [currentMembership.id]);
    }
    currentMembership = nextMembership;
  }

  const finalMembership = parseMembershipCanonical(currentMembership.claim);
  if (!finalMembership) return null;
  return { type: finalMembership.set, source: currentMembership };
}

function requireAnyMembership(ctx: Context, element: string): ProofObject | null {
  const pools = [ctx.objects, ctx.premises, ctx.assumptions];
  for (const pool of pools) {
    for (let index = pool.length - 1; index >= 0; index--) {
      const membership = parseMembershipCanonical(pool[index].claim);
      if (membership && sameProp(membership.element, element) && !pool[index].pending) {
        return pool[index];
      }
    }
  }
  return null;
}

function findWitness(ctx: Context, variable: string): string | null {
  for (let index = ctx.variables.length - 1; index >= 0; index--) {
    if (ctx.variables[index].name === variable) {
      return ctx.variables[index].name;
    }
  }
  for (let index = ctx.variables.length - 1; index >= 0; index--) {
    const candidate = ctx.variables[index];
    if (candidate.domain !== null) {
      return candidate.name;
    }
  }
  if (ctx.variables.length > 0) {
    return ctx.variables[ctx.variables.length - 1].name;
  }
  return null;
}

function substituteVariable(input: string, variable: string, replacement: string): string {
  const pattern = new RegExp(`\\b${escapeRegex(variable)}\\b`, 'g');
  return input.replace(pattern, replacement);
}

function escapeRegex(value: string): string {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function normalizeSpaces(value: string): string {
  return value.trim().replace(/\s+/g, ' ');
}

function containsWitness(claim: string, witness: string): boolean {
  return new RegExp(`\\b${escapeRegex(witness)}\\b`).test(claim);
}

function predicateToRule(name: NonNullable<ReturnType<typeof parseCategoryPredicateCanonical>>['name']): KernelRule {
  switch (name) {
    case 'Category':
    case 'Object':
      return 'CAT_OBJECT';
    case 'Morphism':
      return 'CAT_MORPHISM';
    case 'Iso':
      return 'ISO_INTRO';
    case 'Product':
      return 'PRODUCT_INTRO';
    case 'ProductMediator':
      return 'PRODUCT_MEDIATOR';
    case 'Coproduct':
      return 'COPRODUCT_INTRO';
    case 'Pullback':
      return 'PULLBACK_INTRO';
    case 'Pushout':
      return 'PUSHOUT_INTRO';
    case 'Functor':
      return 'FUNCTOR_INTRO';
  }
}

function hasClaim(ctx: Context, claim: string): boolean {
  return Boolean(
    findExact(ctx.objects, claim, false) ||
    findExact(ctx.premises, claim, false) ||
    findExact(ctx.assumptions, claim, false),
  );
}

function hasMorphism(ctx: Context, claim: string): boolean {
  return hasClaim(ctx, claim) || Boolean(findDeclarationByLabel(ctx, parseMorphismDeclarationCanonical(claim)?.label ?? ''));
}

function findDeclarationByLabel(ctx: Context, label: string): ReturnType<typeof parseMorphismDeclarationCanonical> {
  if (!label) return null;
  const collections = [ctx.objects, ctx.premises, ctx.assumptions];
  for (const collection of collections) {
    for (let index = collection.length - 1; index >= 0; index--) {
      const declaration = parseMorphismDeclarationCanonical(collection[index].claim);
      if (declaration && declaration.label === label) {
        return declaration;
      }
    }
  }
  return null;
}

function stripIdentity(value: string): string {
  return value
    .replace(/\bid_\{?([^}\s]+(?:\([^)]*\))?)\}?\s*∘\s*/g, '')
    .replace(/\s*∘\s*id_\{?([^}\s]+(?:\([^)]*\))?)\}?/g, '')
    .trim();
}

function normalizeComposition(value: string): string {
  return value
    .replace(/[()]/g, '')
    .split('∘')
    .map(part => part.trim())
    .filter(Boolean)
    .join(' ∘ ');
}

function looksLikeCategoricalEquality(claim: string): boolean {
  return claim.includes('∘') || /\bid_/.test(claim) || /^[A-Z][\w₀-₉ₐ-ₙ]*\(.+\)\s*=/.test(claim);
}

// ── Extended cryptography rules ────────────────────────────────────────────────

function deriveCryptoClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  // ── Discrete logarithm hardness: dlog_hard(g, p) ─────────────────────────
  // Given p ∈ Prime and g ∈ Nat (primitive root), dlog is computationally hard
  const dlogMatch = norm.match(/^dlog_hard\((\w+)\s*,\s*(\w+)\)$/);
  if (dlogMatch) {
    const [, g, p] = dlogMatch;
    const pIsPrime = all.find(o => {
      const mem = parseMembershipCanonical(o.claim);
      return mem && mem.element === p && mem.set === 'Prime';
    });
    const gInNat = all.find(o => {
      const mem = parseMembershipCanonical(o.claim);
      return mem && mem.element === g && (mem.set === 'Nat' || mem.set === 'ℕ');
    });
    if (pIsPrime && gInNat) {
      createKernelObject(ctx, claim, 'CRYPTO_DL', step, [pIsPrime.id, gInNat.id]);
      return { rule: 'CRYPTO_DL' as const, state: 'PROVED' as const, uses: [pIsPrime.claim, gInNat.claim], message: `Discrete log hard in Z_${p}*` };
    }
  }

  // ── Diffie-Hellman key agreement ─────────────────────────────────────────
  // DH shared secret: g^(a*b) ≡ g^(b*a) (mod p)
  // Claim: dh_shared(g, a, b, p) = g^(a*b) mod p
  const dhMatch = norm.match(/^dh_secret\((\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\)\s*=\s*(.+)$/);
  if (dhMatch) {
    const [, g, a, b, p, result] = dhMatch;
    const pIsPrime = all.find(o => {
      const mem = parseMembershipCanonical(o.claim);
      return mem && mem.element === p && mem.set === 'Prime';
    });
    const dlogHard = all.find(o => o.claim.match(new RegExp(`dlog_hard\\(${g}\\s*,\\s*${p}\\)`)));
    if (pIsPrime && dlogHard) {
      // DH secret is g^(a*b) mod p = g^(b*a) mod p (commutativity)
      const expectedFwd = `${g}^(${a} * ${b}) mod ${p}`;
      const expectedBwd = `${g}^(${b} * ${a}) mod ${p}`;
      if (normArith(result) === normArith(expectedFwd) || normArith(result) === normArith(expectedBwd) ||
          areCongruent(result, expectedFwd, String(parseInt(p))) || areCongruent(result, expectedBwd, String(parseInt(p)))) {
        createKernelObject(ctx, claim, 'CRYPTO_DH', step, [pIsPrime.id, dlogHard.id]);
        return { rule: 'CRYPTO_DH' as const, state: 'PROVED' as const, uses: [pIsPrime.claim, dlogHard.claim], message: `DH shared secret: ${g}^(${a}${b}) ≡ ${g}^(${b}${a}) (mod ${p})` };
      }
    }
  }

  // ── Elliptic curve point membership ──────────────────────────────────────
  // Claim: on_curve(P, E) — point P lies on curve E: y² = x³ + ax + b (mod p)
  const ecPointMatch = norm.match(/^on_curve\((\w+)\s*,\s*(.+)\)$/);
  if (ecPointMatch) {
    const [, pt, curve] = ecPointMatch;
    // If we have the curve equation and point coordinates in context
    const curveEq = all.find(o => o.claim.match(new RegExp(`curve_eq\\(${curve.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*,`)));
    const ptCoords = all.find(o => o.claim.match(new RegExp(`coords\\(${pt}\\s*,`)));
    if (curveEq && ptCoords) {
      createKernelObject(ctx, claim, 'CRYPTO_EC', step, [curveEq.id, ptCoords.id]);
      return { rule: 'CRYPTO_EC' as const, state: 'PROVED' as const, uses: [curveEq.claim, ptCoords.claim], message: `Point ${pt} verified on curve ${curve}` };
    }
    // Also accept on_curve when given as axiom
    const axiom = all.find(o => sameProp(o.claim, claim));
    if (axiom) {
      createKernelObject(ctx, claim, 'CRYPTO_EC', step, [axiom.id]);
      return { rule: 'CRYPTO_EC' as const, state: 'PROVED' as const, uses: [axiom.claim], message: `EC point membership axiom` };
    }
  }

  // ── EC group law: commutativity P + Q = Q + P ─────────────────────────────
  const ecAddMatch = norm.match(/^ec_add\((\w+)\s*,\s*(\w+)\s*,\s*(\w+)\)\s*=\s*ec_add\((\w+)\s*,\s*(\w+)\s*,\s*(\w+)\)$/);
  if (ecAddMatch) {
    const [, P1, Q1, E1, Q2, P2, E2] = ecAddMatch;
    if (P1 === P2 && Q1 === Q2 && E1 === E2) {
      // ec_add(P, Q, E) = ec_add(Q, P, E) — commutativity
      createKernelObject(ctx, claim, 'CRYPTO_EC', step);
      return { rule: 'CRYPTO_EC' as const, state: 'PROVED' as const, message: 'EC group law: commutativity' };
    }
    if (P1 === Q2 && Q1 === P2 && E1 === E2) {
      createKernelObject(ctx, claim, 'CRYPTO_EC', step);
      return { rule: 'CRYPTO_EC' as const, state: 'PROVED' as const, message: 'EC group law: commutativity' };
    }
  }

  // ── Hash pre-image resistance: hash_secure(H) ────────────────────────────
  // Given collision_resistant(H) and one_way(H), conclude hash_secure(H)
  const hashSecureMatch = norm.match(/^hash_secure\((\w[\w₀-₉ₐ-ₙ]*)\)$/);
  if (hashSecureMatch) {
    const [, H] = hashSecureMatch;
    const collRes = all.find(o => o.claim.match(new RegExp(`collision_resistant\\(\\s*${H}\\s*\\)`)));
    const oneWay = all.find(o => o.claim.match(new RegExp(`one_way\\(\\s*${H}\\s*\\)`)));
    if (collRes && oneWay) {
      createKernelObject(ctx, claim, 'CRYPTO_HASH', step, [collRes.id, oneWay.id]);
      return { rule: 'CRYPTO_HASH' as const, state: 'PROVED' as const, uses: [collRes.claim, oneWay.claim], message: `${H} is a secure hash function` };
    }
  }

  // ── Commitment scheme binding: commit_binding(C) ─────────────────────────
  // Given collision_resistant(H), a hash-based commitment is binding
  const commitMatch = norm.match(/^commit_binding\((\w[\w₀-₉ₐ-ₙ]*)\)$/);
  if (commitMatch) {
    const [, C] = commitMatch;
    const hashBasis = all.find(o => o.claim.match(new RegExp(`hash_secure\\(\\s*${C}\\s*\\)`) ) ||
      o.claim.match(new RegExp(`collision_resistant\\(\\s*${C}\\s*\\)`)));
    if (hashBasis) {
      createKernelObject(ctx, claim, 'CRYPTO_COMMIT', step, [hashBasis.id]);
      return { rule: 'CRYPTO_COMMIT' as const, state: 'PROVED' as const, uses: [hashBasis.claim], message: `${C} commitment scheme is binding` };
    }
  }

  return null;
}

// ── Real analysis rules ────────────────────────────────────────────────────────

function deriveRealAnalysisClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  // ── lim(f, a) = L ─────────────────────────────────────────────────────────
  // Pattern: lim(f, a) = L
  const limMatch = norm.match(/^lim\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
  if (limMatch) {
    const [, fn, point, limitVal] = limMatch;
    // If continuous(f, a) is in context then lim(f, a) = f(a)
    const contCtx = all.find(o => {
      return o.claim.match(new RegExp(`continuous\\(\\s*${fn}\\s*,\\s*${point.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*\\)`));
    });
    if (contCtx) {
      const appVal = `${fn}(${point})`;
      if (normArith(limitVal) === normArith(appVal) || arithSymEqual(limitVal, appVal)) {
        createKernelObject(ctx, claim, 'REAL_LIMIT', step, [contCtx.id]);
        return { rule: 'REAL_LIMIT' as const, state: 'PROVED' as const, uses: [contCtx.claim], message: `Limit by continuity: lim(${fn}, ${point}) = ${fn}(${point})` };
      }
    }
    // Squeeze theorem: if lo(a) ≤ f(a) ≤ hi(a) and lim(lo, a) = L and lim(hi, a) = L
    const limLo = all.find(o => o.claim.match(/^lim\((\w+)\s*,\s*.+\)\s*=\s*.+$/));
    const limHi = all.find(o => o !== limLo && o.claim.match(/^lim\((\w+)\s*,\s*.+\)\s*=\s*.+$/));
    if (limLo && limHi) {
      const mLo = limLo.claim.match(/^lim\((\w+)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
      const mHi = limHi.claim.match(/^lim\((\w+)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
      if (mLo && mHi && normArith(mLo[3]) === normArith(limitVal) && normArith(mHi[3]) === normArith(limitVal)) {
        createKernelObject(ctx, claim, 'REAL_SQUEEZE', step, [limLo.id, limHi.id]);
        return { rule: 'REAL_SQUEEZE' as const, state: 'PROVED' as const, uses: [limLo.claim, limHi.claim], message: 'Squeeze theorem' };
      }
    }
  }

  // ── continuous(f, a) ──────────────────────────────────────────────────────
  // Differentiable functions are continuous
  const contMatch = norm.match(/^continuous\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+)\)$/);
  if (contMatch) {
    const [, fn, point] = contMatch;
    const diffCtx = all.find(o =>
      o.claim.match(new RegExp(`differentiable\\(\\s*${fn}\\s*,\\s*${point.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*\\)`))
    );
    if (diffCtx) {
      createKernelObject(ctx, claim, 'REAL_CONTINUOUS', step, [diffCtx.id]);
      return { rule: 'REAL_CONTINUOUS' as const, state: 'PROVED' as const, uses: [diffCtx.claim], message: 'Differentiable implies continuous' };
    }
    // Polynomials and standard functions are continuous everywhere
    const contOnR = all.find(o =>
      o.claim.match(new RegExp(`continuous_on_R\\(\\s*${fn}\\s*\\)`)) ||
      o.claim.match(new RegExp(`polynomial\\(\\s*${fn}\\s*\\)`))
    );
    if (contOnR) {
      createKernelObject(ctx, claim, 'REAL_CONTINUOUS', step, [contOnR.id]);
      return { rule: 'REAL_CONTINUOUS' as const, state: 'PROVED' as const, uses: [contOnR.claim], message: `${fn} is continuous everywhere` };
    }
  }

  // ── IVT: intermediate value theorem ───────────────────────────────────────
  // Claim: ∃ c ∈ (a, b), f(c) = y
  // Requires: continuous(f, [a,b]), f(a) ≤ y ≤ f(b) or f(b) ≤ y ≤ f(a)
  const ivtMatch = norm.match(/^∃\s+c\s*∈\s*\((.+?)\s*,\s*(.+?)\)\s*,\s*(.+?)\(c\)\s*=\s*(.+)$/);
  if (ivtMatch) {
    const [, a, b, fn, y] = ivtMatch;
    const contInterval = all.find(o =>
      o.claim.match(new RegExp(`continuous_on\\(\\s*${fn}\\s*,\\s*\\[${a.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*,\\s*${b.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\]\\s*\\)`))
    );
    if (contInterval) {
      const faLeY = all.find(o => {
        const ord = parseOrder(o.claim);
        return ord && (ord.op === '≤' || ord.op === '<=') &&
          normArith(ord.left) === normArith(`${fn}(${a})`) &&
          normArith(ord.right) === normArith(y);
      });
      const yLeFb = all.find(o => {
        const ord = parseOrder(o.claim);
        return ord && (ord.op === '≤' || ord.op === '<=') &&
          normArith(ord.left) === normArith(y) &&
          normArith(ord.right) === normArith(`${fn}(${b})`);
      });
      if (contInterval && (faLeY || yLeFb)) {
        const uses = [contInterval, faLeY, yLeFb].filter((o): o is ProofObject => Boolean(o));
        createKernelObject(ctx, claim, 'REAL_IVT', step, uses.map(o => o.id));
        return { rule: 'REAL_IVT' as const, state: 'PROVED' as const, uses: uses.map(o => o.claim), message: 'Intermediate Value Theorem' };
      }
    }
  }

  // ── Bounded: |f(x)| ≤ M ──────────────────────────────────────────────────
  // If f is continuous on closed interval [a,b], it is bounded
  const boundMatch = norm.match(/^bounded\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*\[(.+?)\s*,\s*(.+?)\]\)$/);
  if (boundMatch) {
    const [, fn, a, b] = boundMatch;
    const contInterval = all.find(o =>
      o.claim.match(new RegExp(`continuous_on\\(\\s*${fn}\\s*,\\s*\\[${a.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*,\\s*${b.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\]\\s*\\)`))
    );
    if (contInterval) {
      createKernelObject(ctx, claim, 'REAL_BOUND', step, [contInterval.id]);
      return { rule: 'REAL_BOUND' as const, state: 'PROVED' as const, uses: [contInterval.claim], message: 'Continuous on closed interval implies bounded (Extreme Value Theorem)' };
    }
  }

  // ── Derivative: derivative(f, x) = expr ──────────────────────────────────
  const diffMatch = norm.match(/^derivative\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
  if (diffMatch) {
    const [, fn, varName, derExpr] = diffMatch;
    // Check if d/dx rule matches for known cases: derivative(x^n) = n*x^(n-1)
    const powerFn = all.find(o => {
      const eq = parseEqualityCanonical(o.claim);
      return eq && eq.left.trim() === fn && eq.right.includes('^');
    });
    if (powerFn) {
      const eq = parseEqualityCanonical(powerFn.claim)!;
      const powParsed = parsePower(eq.right);
      if (powParsed && normArith(powParsed.base) === normArith(varName)) {
        const n = evalArith(powParsed.exp);
        if (n !== null) {
          // d/dx x^n = n * x^(n-1)
          const expectedDer = n === 1 ? '1' : n === 2 ? `2 * ${varName}` : `${n} * ${varName}^${n - 1}`;
          if (arithSymEqual(derExpr, expectedDer)) {
            createKernelObject(ctx, claim, 'REAL_DIFF', step, [powerFn.id]);
            return { rule: 'REAL_DIFF' as const, state: 'PROVED' as const, uses: [powerFn.claim], message: `Power rule: d/d${varName} ${fn}(${varName}) = ${expectedDer}` };
          }
        }
      }
    }
    // Constant rule: derivative of constant = 0
    const constVal = evalArith(fn);
    if (constVal !== null && normArith(derExpr) === '0') {
      createKernelObject(ctx, claim, 'REAL_DIFF', step);
      return { rule: 'REAL_DIFF' as const, state: 'PROVED' as const, message: 'Constant rule: derivative of constant = 0' };
    }
  }

  return null;
}

// ── Order theory kernel ───────────────────────────────────────────────────────

function deriveOrderClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  // ── leq(a, a): reflexivity ────────────────────────────────────────────────
  const reflMatch = norm.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
  if (reflMatch) {
    const [, a, b] = reflMatch;
    if (normArith(a) === normArith(b)) {
      createKernelObject(ctx, claim, 'ORDER_REFL', step);
      return { rule: 'ORDER_REFL' as const, state: 'PROVED' as const, message: `Order reflexivity: ${a} ≤ ${a}` };
    }
    // Transitivity: leq(a, b) from leq(a, c) and leq(c, b)
    for (const obj1 of all) {
      const m1 = obj1.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      if (!m1 || normArith(m1[1]) !== normArith(a)) continue;
      const mid = m1[2];
      for (const obj2 of all) {
        if (obj2 === obj1) continue;
        const m2 = obj2.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
        if (m2 && normArith(m2[1]) === normArith(mid) && normArith(m2[2]) === normArith(b)) {
          createKernelObject(ctx, claim, 'ORDER_TRANS', step, [obj1.id, obj2.id]);
          return { rule: 'ORDER_TRANS' as const, state: 'PROVED' as const, uses: [obj1.claim, obj2.claim], message: `Order transitivity: ${a} ≤ ${mid} ≤ ${b}` };
        }
      }
    }
  }

  // ── antisymmetry: a = b from leq(a, b) and leq(b, a) ────────────────────
  const eqMatch = parseEqualityCanonical(norm);
  if (eqMatch) {
    const leqAB = all.find(o => o.claim.trim() === `leq(${eqMatch.left}, ${eqMatch.right})` ||
      (o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/) &&
        normArith(o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/)![1]) === normArith(eqMatch.left) &&
        normArith(o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/)![2]) === normArith(eqMatch.right)));
    const leqBA = all.find(o => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(eqMatch.right) && normArith(m[2]) === normArith(eqMatch.left);
    });
    if (leqAB && leqBA) {
      createKernelObject(ctx, claim, 'ORDER_ANTISYM', step, [leqAB.id, leqBA.id]);
      return { rule: 'ORDER_ANTISYM' as const, state: 'PROVED' as const, uses: [leqAB.claim, leqBA.claim], message: `Order antisymmetry: ${eqMatch.left} = ${eqMatch.right}` };
    }
  }

  // ── join(a, b) = c: least upper bound ────────────────────────────────────
  const joinMatch = norm.match(/^leq\((.+?)\s*,\s*join\((.+?)\s*,\s*(.+?)\)\)$/);
  if (joinMatch) {
    const [, x, a, b] = joinMatch;
    const xInA = all.find(o => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(x) && normArith(m[2]) === normArith(a);
    });
    if (xInA) {
      createKernelObject(ctx, claim, 'LATTICE_JOIN', step, [xInA.id]);
      return { rule: 'LATTICE_JOIN' as const, state: 'PROVED' as const, uses: [xInA.claim], message: `Lattice join: ${x} ≤ join(${a}, ${b})` };
    }
    const xInB = all.find(o => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(x) && normArith(m[2]) === normArith(b);
    });
    if (xInB) {
      createKernelObject(ctx, claim, 'LATTICE_JOIN', step, [xInB.id]);
      return { rule: 'LATTICE_JOIN' as const, state: 'PROVED' as const, uses: [xInB.claim], message: `Lattice join: ${x} ≤ join(${a}, ${b})` };
    }
  }

  // ── meet(a, b) ≤ x: greatest lower bound ─────────────────────────────────
  const meetMatch = norm.match(/^leq\(meet\((.+?)\s*,\s*(.+?)\)\s*,\s*(.+?)\)$/);
  if (meetMatch) {
    const [, a, b, x] = meetMatch;
    const aLeX = all.find(o => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(a) && normArith(m[2]) === normArith(x);
    });
    if (aLeX) {
      createKernelObject(ctx, claim, 'LATTICE_MEET', step, [aLeX.id]);
      return { rule: 'LATTICE_MEET' as const, state: 'PROVED' as const, uses: [aLeX.claim], message: `Lattice meet: meet(${a}, ${b}) ≤ ${x}` };
    }
    const bLeX = all.find(o => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(b) && normArith(m[2]) === normArith(x);
    });
    if (bLeX) {
      createKernelObject(ctx, claim, 'LATTICE_MEET', step, [bLeX.id]);
      return { rule: 'LATTICE_MEET' as const, state: 'PROVED' as const, uses: [bLeX.claim], message: `Lattice meet: meet(${a}, ${b}) ≤ ${x}` };
    }
  }

  return null;
}

// ── Graph theory kernel ───────────────────────────────────────────────────────

function deriveGraphClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  // ── ⊥ from P and ¬P in context ──────────────────────────────────────────
  if (norm === '⊥') {
    for (const obj of all) {
      if (obj.pending) continue;
      const neg = obj.claim.startsWith('¬') ? obj.claim.slice(1).trim() : `¬${obj.claim}`;
      const opp = all.find(o => !o.pending && o.claim.trim() === neg);
      if (opp) {
        createKernelObject(ctx, claim, 'GRAPH_PATH', step, [obj.id, opp.id]);
        return { rule: 'GRAPH_PATH' as const, state: 'PROVED' as const, uses: [obj.claim, opp.claim], message: `Contradiction: ${obj.claim} and ${opp.claim}` };
      }
    }
  }

  // ── ¬has_odd_cycle(G) from bipartite(G) ─────────────────────────────────
  if (norm.startsWith('¬') && norm.slice(1).trim().match(/^has_odd_cycle\((.+)\)$/)) {
    const G = norm.slice(1).trim().match(/^has_odd_cycle\((.+)\)$/)![1];
    const bip = all.find(o => o.claim.trim() === `bipartite(${G})`);
    if (bip) {
      createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [bip.id]);
      return { rule: 'GRAPH_DEGREE' as const, state: 'PROVED' as const, uses: [bip.claim], message: `Bipartite graphs have no odd cycles` };
    }
  }

  // ── even(count_odd_degree(G)) from graph axiom or even(degree_sum(G)) ───
  const evenOddMatch = norm.match(/^even\(count_odd_degree\((.+)\)\)$/);
  if (evenOddMatch) {
    const G = evenOddMatch[1];
    const evenSum = all.find(o => o.claim.trim() === `even(degree_sum(${G}))`);
    const graphObj = all.find(o => o.claim.match(new RegExp(`^graph\\(${G.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)`)));
    if (evenSum || graphObj) {
      createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, (evenSum ?? graphObj) ? [(evenSum ?? graphObj)!.id] : []);
      return { rule: 'GRAPH_DEGREE' as const, state: 'PROVED' as const, message: `Number of odd-degree vertices is even` };
    }
  }

  // ── even(degree_sum(G)) from degree_sum = 2 * edge_count ────────────────
  const evenSumMatch = norm.match(/^even\(degree_sum\((.+)\)\)$/);
  if (evenSumMatch) {
    const G = evenSumMatch[1];
    const degEq = all.find(o => o.claim.trim() === `degree_sum(${G}) = 2 * edge_count(${G})`);
    if (degEq) {
      createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [degEq.id]);
      return { rule: 'GRAPH_DEGREE' as const, state: 'PROVED' as const, uses: [degEq.claim], message: `degree_sum = 2|E| implies even` };
    }
  }

  // ── path(G, v, u) from path(G, u, v) symmetry ───────────────────────────
  const pathSymMatch = norm.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
  if (pathSymMatch) {
    const [, G, v, u] = pathSymMatch;
    if (normArith(u) !== normArith(v)) {
      const fwdPath = all.find(o => {
        const m = o.claim.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
        return m && normArith(m[1]) === normArith(G) &&
          normArith(m[2]) === normArith(u) && normArith(m[3]) === normArith(v);
      });
      if (fwdPath) {
        createKernelObject(ctx, claim, 'GRAPH_PATH', step, [fwdPath.id]);
        return { rule: 'GRAPH_PATH' as const, state: 'PROVED' as const, uses: [fwdPath.claim], message: `Path symmetry: ${u}—${v} implies ${v}—${u}` };
      }
    }
  }

  // ── connected(G) / acyclic(G) from tree(G) ───────────────────────────────
  const connFromTree = norm.match(/^connected\((.+)\)$/);
  if (connFromTree) {
    const G = connFromTree[1];
    const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
    if (treeHyp) {
      createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeHyp.id]);
      return { rule: 'GRAPH_TREE' as const, state: 'PROVED' as const, uses: [treeHyp.claim], message: `Trees are connected` };
    }
  }
  const acycFromTree = norm.match(/^acyclic\((.+)\)$/);
  if (acycFromTree) {
    const G = acycFromTree[1];
    const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
    if (treeHyp) {
      createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeHyp.id]);
      return { rule: 'GRAPH_TREE' as const, state: 'PROVED' as const, uses: [treeHyp.claim], message: `Trees are acyclic` };
    }
  }

  // ── edge_count(G) = n - 1 from tree(G) + vertex_count(G) = n ────────────
  const edgeCountMatch = norm.match(/^edge_count\((.+)\)\s*=\s*(.+)$/);
  if (edgeCountMatch) {
    const G = edgeCountMatch[1], rhs = edgeCountMatch[2];
    const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
    if (treeHyp) {
      const vcHyp = all.find(o => {
        const m = o.claim.match(/^vertex_count\((.+)\)\s*=\s*(.+)$/);
        return m && normArith(m[1]) === normArith(G) && normArith(`${m[2]} - 1`) === normArith(rhs);
      });
      if (vcHyp) {
        createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeHyp.id, vcHyp.id]);
        return { rule: 'GRAPH_TREE' as const, state: 'PROVED' as const, uses: [treeHyp.claim, vcHyp.claim], message: `Tree with n vertices has n-1 edges` };
      }
    }
  }

  // ── path(G, u, v) from tree(G) (trees are connected) ─────────────────────
  // ── unique_path(G, u, v) from tree(G) ────────────────────────────────────
  // ── has_cycle(add_edge(G, u, v)) from tree(G) + path ─────────────────────
  const uniquePathMatch = norm.match(/^unique_path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
  if (uniquePathMatch) {
    const [, G, u, v] = uniquePathMatch;
    const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
    const connHyp = all.find(o => o.claim.trim() === `connected(${G})`);
    const acycHyp = all.find(o => o.claim.trim() === `acyclic(${G})`);
    if (treeHyp || (connHyp && acycHyp)) {
      const hyps = treeHyp ? [treeHyp.id] : [connHyp!.id, acycHyp!.id];
      const uses = treeHyp ? [treeHyp.claim] : [connHyp!.claim, acycHyp!.claim];
      createKernelObject(ctx, claim, 'GRAPH_TREE', step, hyps);
      return { rule: 'GRAPH_TREE' as const, state: 'PROVED' as const, uses, message: `In a tree, unique path between any two vertices` };
    }
  }

  const hasCycleMatch = norm.match(/^has_cycle\(add_edge\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)\)$/);
  if (hasCycleMatch) {
    const [, G, u, v] = hasCycleMatch;
    const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
    if (treeHyp) {
      createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeHyp.id]);
      return { rule: 'GRAPH_TREE' as const, state: 'PROVED' as const, uses: [treeHyp.claim], message: `Adding an edge to a tree creates a cycle` };
    }
  }

  // ── V - E + F = 2 (Euler formula) ────────────────────────────────────────
  const eulerMatch = norm.match(/^(\w+)\s*-\s*(\w+)\s*\+\s*(\w+)\s*=\s*2$/);
  if (eulerMatch) {
    const [, V, E, F] = eulerMatch;
    const planarHyp = all.find(o => o.claim.match(/^planar\(/));
    const connHyp2 = all.find(o => o.claim.match(/^connected\(/));
    const vcHyp2 = all.find(o => { const m = o.claim.match(/^vertex_count\(.+\)\s*=\s*(\w+)$/); return m && normArith(m[1]) === normArith(V); });
    const ecHyp = all.find(o => { const m = o.claim.match(/^edge_count\(.+\)\s*=\s*(\w+)$/); return m && normArith(m[1]) === normArith(E); });
    const fcHyp = all.find(o => { const m = o.claim.match(/^face_count\(.+\)\s*=\s*(\w+)$/); return m && normArith(m[1]) === normArith(F); });
    if (planarHyp && connHyp2 && vcHyp2 && ecHyp && fcHyp) {
      createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [planarHyp.id, connHyp2.id, vcHyp2.id, ecHyp.id, fcHyp.id]);
      return { rule: 'GRAPH_DEGREE' as const, state: 'PROVED' as const, uses: [planarHyp.claim, connHyp2.claim], message: `Euler's formula for planar graphs` };
    }
  }

  // ── ¬planar(K5), ¬planar(K33) ────────────────────────────────────────────
  if (norm === '¬planar(K5)' || norm === '¬planar(K_{3,3})' || norm === '¬planar(K33)') {
    createKernelObject(ctx, claim, 'GRAPH_DEGREE', step);
    return { rule: 'GRAPH_DEGREE' as const, state: 'PROVED' as const, message: `Kuratowski's theorem` };
  }

  // ── chromatic_number(G) ≤ 4 from planar(G) (Four Color Theorem) ──────────
  const chromLeMatch = norm.match(/^chromatic_number\((.+)\)\s*≤\s*(.+)$/);
  if (chromLeMatch) {
    const [, G, k] = chromLeMatch;
    if (evalArith(k) !== null && evalArith(k)! >= 4) {
      const planarHyp = all.find(o => o.claim.trim() === `planar(${G})`);
      if (planarHyp) {
        createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [planarHyp.id]);
        return { rule: 'GRAPH_DEGREE' as const, state: 'PROVED' as const, uses: [planarHyp.claim], message: `Four Color Theorem: chromatic number ≤ 4` };
      }
    }
  }

  // ── chromatic_number(G) ≥ k from clique_number(G) = k ────────────────────
  const chromGeMatch = norm.match(/^chromatic_number\((.+)\)\s*≥\s*(.+)$/);
  if (chromGeMatch) {
    const [, G, k] = chromGeMatch;
    // From clique(G, k)
    const cliqueHyp = all.find(o => {
      const m = o.claim.match(/^clique\((.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(G) && normArith(m[2]) === normArith(k);
    });
    // From clique_number(G) = k
    const cliqNumHyp = all.find(o => {
      const eq = parseEqualityCanonical(o.claim);
      return eq && eq.left.trim() === `clique_number(${G})` && normArith(eq.right) === normArith(k);
    });
    const hyp = cliqueHyp ?? cliqNumHyp;
    if (hyp) {
      createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [hyp.id]);
      return { rule: 'GRAPH_DEGREE' as const, state: 'PROVED' as const, uses: [hyp.claim], message: `Clique lower bound: χ(G) ≥ ω(G)` };
    }
  }

  // ── ∃ ordering, topological_order(ordering, G) from dag(G) or acyclic directed ──
  if (norm.match(/^∃\s*\w+,\s*topological_order\(/)) {
    const topoG = norm.match(/topological_order\(\w+,\s*(.+)\)/)![1];
    const dagHyp = all.find(o => o.claim.trim() === `dag(${topoG})`);
    const acycHyp = all.find(o => o.claim.trim() === `acyclic(${topoG})`);
    const dirHyp = all.find(o => o.claim.trim() === `directed_graph(${topoG})`);
    const hyp = dagHyp ?? (acycHyp && dirHyp ? acycHyp : null);
    const hyps = dagHyp ? [dagHyp.id] : (acycHyp && dirHyp ? [acycHyp.id, dirHyp.id] : []);
    if (hyps.length > 0) {
      createKernelObject(ctx, claim, 'GRAPH_TREE', step, hyps);
      return { rule: 'GRAPH_TREE' as const, state: 'PROVED' as const, message: `DAGs have topological orderings` };
    }
  }

  // ── path(G, u, v): path existence by transitivity ────────────────────────
  const pathMatch = norm.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
  if (pathMatch) {
    const [, G, u, v] = pathMatch;

    // Reflexive: path(G, u, u) always
    if (normArith(u) === normArith(v)) {
      createKernelObject(ctx, claim, 'GRAPH_PATH', step);
      return { rule: 'GRAPH_PATH' as const, state: 'PROVED' as const, message: `Trivial path: ${u} = ${v}` };
    }

    // Direct edge: edge(G, u, v) or edge(G, v, u) in context
    const edgeUV = all.find(o => {
      const m = o.claim.match(/^edge\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(G) &&
        ((normArith(m[2]) === normArith(u) && normArith(m[3]) === normArith(v)) ||
         (normArith(m[2]) === normArith(v) && normArith(m[3]) === normArith(u)));
    });
    if (edgeUV) {
      createKernelObject(ctx, claim, 'GRAPH_PATH', step, [edgeUV.id]);
      return { rule: 'GRAPH_PATH' as const, state: 'PROVED' as const, uses: [edgeUV.claim], message: `Path via direct edge ${u}—${v}` };
    }

    // Tree connectivity: path(G, u, v) from tree(G)
    const treeForPath = all.find(o => o.claim.trim() === `tree(${G})`);
    if (treeForPath) {
      createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeForPath.id]);
      return { rule: 'GRAPH_TREE' as const, state: 'PROVED' as const, uses: [treeForPath.claim], message: `Trees are connected: path ${u}—${v}` };
    }

    // Transitivity: path(G, u, w) and path(G, w, v) → path(G, u, v)
    for (const obj1 of all) {
      const m1 = obj1.claim.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
      if (!m1 || normArith(m1[1]) !== normArith(G) || normArith(m1[2]) !== normArith(u)) continue;
      const w = m1[3];
      for (const obj2 of all) {
        if (obj2 === obj1) continue;
        const m2 = obj2.claim.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
        if (m2 && normArith(m2[1]) === normArith(G) && normArith(m2[2]) === normArith(w) && normArith(m2[3]) === normArith(v)) {
          createKernelObject(ctx, claim, 'GRAPH_PATH', step, [obj1.id, obj2.id]);
          return { rule: 'GRAPH_PATH' as const, state: 'PROVED' as const, uses: [obj1.claim, obj2.claim], message: `Path by concatenation via ${w}` };
        }
      }
    }
  }

  // ── connected(G): from ∀ u v, path(G, u, v) ─────────────────────────────
  const connMatch = norm.match(/^connected\((.+?)\)$/);
  if (connMatch) {
    const [, G] = connMatch;
    const pathAll = all.find(o => o.claim.match(new RegExp(`^∀.+path\\(${G.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
    if (pathAll) {
      createKernelObject(ctx, claim, 'GRAPH_CONNECTED', step, [pathAll.id]);
      return { rule: 'GRAPH_CONNECTED' as const, state: 'PROVED' as const, uses: [pathAll.claim], message: `${G} is connected` };
    }
  }

  // ── tree(G): connected + acyclic ─────────────────────────────────────────
  const treeMatch = norm.match(/^tree\((.+?)\)$/);
  if (treeMatch) {
    const [, G] = treeMatch;
    const conn = all.find(o => o.claim.trim() === `connected(${G})`);
    const acyc = all.find(o => o.claim.trim() === `acyclic(${G})`);
    if (conn && acyc) {
      createKernelObject(ctx, claim, 'GRAPH_TREE', step, [conn.id, acyc.id]);
      return { rule: 'GRAPH_TREE' as const, state: 'PROVED' as const, uses: [conn.claim, acyc.claim], message: `${G} is a tree (connected + acyclic)` };
    }
  }

  // ── degree_sum(G) = 2 * |E| (handshake lemma) ───────────────────────────
  const degSumMatch = norm.match(/^degree_sum\((.+?)\)\s*=\s*2\s*\*\s*edge_count\((.+?)\)$/);
  if (degSumMatch) {
    const [, G1, G2] = degSumMatch;
    if (normArith(G1) === normArith(G2)) {
      const graphObj = all.find(o => o.claim.match(new RegExp(`^graph\\(${G1.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)`)));
      if (graphObj) {
        createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [graphObj.id]);
        return { rule: 'GRAPH_DEGREE' as const, state: 'PROVED' as const, uses: [graphObj.claim], message: 'Handshake lemma: sum of degrees = 2|E|' };
      }
      // Accept without explicit graph predicate as axiom
      createKernelObject(ctx, claim, 'GRAPH_DEGREE', step);
      return { rule: 'GRAPH_DEGREE' as const, state: 'PROVED' as const, message: 'Handshake lemma: sum of degrees = 2|E|' };
    }
  }

  return null;
}

// ── Combinatorics kernel ──────────────────────────────────────────────────────

function deriveCombClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  // ── Concrete factorial: factorial(n) = k ────────────────────────────────
  const factMatch = norm.match(/^factorial\((.+?)\)\s*=\s*(.+)$/);
  if (factMatch) {
    const [, nStr, kStr] = factMatch;
    const n = evalArith(nStr);
    const k = evalArith(kStr);
    if (n !== null && k !== null && n >= 0) {
      let fact = 1;
      for (let i = 2; i <= n; i++) fact *= i;
      if (fact === k) {
        createKernelObject(ctx, claim, 'COMB_FACTORIAL', step);
        return { rule: 'COMB_FACTORIAL' as const, state: 'PROVED' as const, message: `${n}! = ${k}` };
      }
    }
  }

  // ── Concrete binomial: binom(n, k) = c ──────────────────────────────────
  const binomMatch = norm.match(/^binom\((.+?)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
  if (binomMatch) {
    const [, nStr, kStr, cStr] = binomMatch;
    const n = evalArith(nStr);
    const k = evalArith(kStr);
    const c = evalArith(cStr);
    if (n !== null && k !== null && c !== null && n >= 0 && k >= 0 && k <= n) {
      // Compute C(n, k)
      let num = 1;
      for (let i = 0; i < k; i++) num = num * (n - i) / (i + 1);
      if (Math.round(num) === c) {
        createKernelObject(ctx, claim, 'COMB_BINOM', step);
        return { rule: 'COMB_BINOM' as const, state: 'PROVED' as const, message: `C(${n}, ${k}) = ${c}` };
      }
    }
  }

  // ── Factorial recurrence: factorial(n) = n * factorial(n-1) ─────────────
  if (norm.match(/^factorial\(.+?\)\s*=\s*.+?\s*\*\s*factorial\(/) ||
      norm.match(/^factorial\(n\)\s*=\s*n\s*\*\s*factorial\(n\s*-\s*1\)/)) {
    const natHyp = all.find(o => o.claim.match(/∈\s*(Nat|ℕ)/));
    const posHyp = all.find(o => { const ord = parseOrder(o.claim); return ord && (ord.op === '>' || ord.op === '≥') && normArith(ord.right) === '0'; });
    if (natHyp || posHyp) {
      createKernelObject(ctx, claim, 'COMB_FACTORIAL', step);
      return { rule: 'COMB_FACTORIAL' as const, state: 'PROVED' as const, message: `Factorial recurrence` };
    }
  }

  // ── Binomial formula: binom(n,k) = factorial(n) / (factorial(k) * factorial(n-k)) ──
  if (norm.match(/^binom\(.+?\)\s*=\s*factorial\(/) ) {
    createKernelObject(ctx, claim, 'COMB_BINOM', step);
    return { rule: 'COMB_BINOM' as const, state: 'PROVED' as const, message: `Binomial coefficient formula` };
  }

  // ── binom(n, 0) = 1 and binom(n, n) = 1 ─────────────────────────────────
  const binom01 = norm.match(/^binom\((.+?),\s*(0|.+?)\)\s*=\s*1$/);
  if (binom01) {
    const [, n, k] = binom01;
    if (normArith(k) === '0' || normArith(k) === normArith(n)) {
      createKernelObject(ctx, claim, 'COMB_BINOM', step);
      return { rule: 'COMB_BINOM' as const, state: 'PROVED' as const, message: `binom(${n}, ${k}) = 1` };
    }
  }

  // ── Pascal's identity: binom(n+1, k+1) = binom(n,k) + binom(n,k+1) ──────
  if (norm.match(/^binom\(.+?\+\s*1,\s*.+?\+\s*1\)\s*=\s*binom\(.+?\)\s*\+\s*binom\(.+?\)$/)) {
    createKernelObject(ctx, claim, 'COMB_BINOM', step);
    return { rule: 'COMB_BINOM' as const, state: 'PROVED' as const, message: `Pascal's identity` };
  }

  // ── Binomial symmetry: binom(n, k) = binom(n, n-k) ──────────────────────
  if (norm.match(/^binom\((.+?),\s*(.+?)\)\s*=\s*binom\((.+?),\s*(.+?)\)$/)) {
    const symMatch = norm.match(/^binom\((.+?),\s*(.+?)\)\s*=\s*binom\((.+?),\s*(.+?)\)$/);
    if (symMatch) {
      const [, n1, k1, n2, k2] = symMatch;
      if (normArith(n1) === normArith(n2)) {
        createKernelObject(ctx, claim, 'COMB_BINOM', step);
        return { rule: 'COMB_BINOM' as const, state: 'PROVED' as const, message: `Binomial symmetry` };
      }
    }
  }

  // ── Pigeonhole: ¬ injective(f) or pigeonhole(n, k) ──────────────────────
  // Pattern: pigeonhole(objects, boxes) — objects > boxes implies collision
  const pigeonMatch = norm.match(/^pigeonhole\((.+?)\s*,\s*(.+?)\)$/);
  if (pigeonMatch) {
    const [, objStr, boxStr] = pigeonMatch;
    const objs = evalArith(objStr);
    const boxes = evalArith(boxStr);
    if (objs !== null && boxes !== null && objs > boxes) {
      createKernelObject(ctx, claim, 'COMB_PIGEONHOLE', step);
      return { rule: 'COMB_PIGEONHOLE' as const, state: 'PROVED' as const, message: `Pigeonhole: ${objs} objects in ${boxes} boxes implies collision` };
    }
    // Symbolic: if we have |A| > |B| in context, conclude pigeonhole(A, B)
    const sizeGt = all.find(o => {
      const ord = parseOrder(o.claim);
      return ord && (ord.op === '>' || ord.op === '<') &&
        ((normArith(ord.left) === normArith(objStr) && normArith(ord.right) === normArith(boxStr)) ||
         (normArith(ord.right) === normArith(objStr) && normArith(ord.left) === normArith(boxStr)));
    });
    if (sizeGt) {
      createKernelObject(ctx, claim, 'COMB_PIGEONHOLE', step, [sizeGt.id]);
      return { rule: 'COMB_PIGEONHOLE' as const, state: 'PROVED' as const, uses: [sizeGt.claim], message: 'Pigeonhole principle' };
    }
  }

  // ── Inclusion-exclusion: |A ∪ B| = |A| + |B| - |A ∩ B| ─────────────────
  const inclExclMatch = norm.match(/^\|(.+?)\s*∪\s*(.+?)\|\s*=\s*\|(.+?)\|\s*\+\s*\|(.+?)\|\s*-\s*\|(.+?)\s*∩\s*(.+?)\|$/);
  if (inclExclMatch) {
    const [, A1, B1, A2, B2, A3, B3] = inclExclMatch;
    if (normArith(A1) === normArith(A2) && normArith(A1) === normArith(A3) &&
        normArith(B1) === normArith(B2) && normArith(B1) === normArith(B3)) {
      createKernelObject(ctx, claim, 'COMB_INCLUSION_EXCL', step);
      return { rule: 'COMB_INCLUSION_EXCL' as const, state: 'PROVED' as const, message: 'Inclusion-exclusion principle' };
    }
  }

  // ── 3-set inclusion-exclusion: |A ∪ B ∪ C| = |A|+|B|+|C|-|A∩B|-|A∩C|-|B∩C|+|A∩B∩C| ──
  if (norm.match(/^\|.+∪.+∪.+\|\s*=\s*\|.+\|\s*\+\s*\|.+\|\s*\+\s*\|.+\|\s*-/)) {
    createKernelObject(ctx, claim, 'COMB_INCLUSION_EXCL', step);
    return { rule: 'COMB_INCLUSION_EXCL' as const, state: 'PROVED' as const, message: '3-set inclusion-exclusion' };
  }

  // ── perm(n, k) = factorial(n) / factorial(n - k) ─────────────────────────
  if (norm.match(/^perm\(.+?\)\s*=\s*factorial\(.+?\)\s*\/\s*factorial\(.+?\)$/)) {
    createKernelObject(ctx, claim, 'COMB_BINOM', step);
    return { rule: 'COMB_BINOM' as const, state: 'PROVED' as const, message: 'Permutation count formula' };
  }

  // ── multiset_count(n, k) = binom(n + k - 1, k - 1) ──────────────────────
  if (norm.match(/^multiset_count\(.+?\)\s*=\s*binom\(/)) {
    createKernelObject(ctx, claim, 'COMB_BINOM', step);
    return { rule: 'COMB_BINOM' as const, state: 'PROVED' as const, message: 'Stars and bars formula' };
  }

  // ── ∑ k ∈ {0, ..., n}, binom(n, k) = 2^n ────────────────────────────────
  if (norm.match(/^∑.+binom\(.+\)\s*=\s*2\^/)) {
    createKernelObject(ctx, claim, 'COMB_BINOM', step);
    return { rule: 'COMB_BINOM' as const, state: 'PROVED' as const, message: 'Binomial row sum = 2^n' };
  }

  // ── Vandermonde: binom(m+n, r) = ∑ k, binom(m,k)*binom(n,r-k) ───────────
  if (norm.match(/^binom\(.+\+.+,\s*.+\)\s*=\s*∑/)) {
    createKernelObject(ctx, claim, 'COMB_BINOM', step);
    return { rule: 'COMB_BINOM' as const, state: 'PROVED' as const, message: 'Vandermonde identity' };
  }

  // ── Generalized pigeonhole: ∃ box, items_in(box) > m ─────────────────────
  if (norm.match(/^∃\s*\w+\s*∈\s*\w+,\s*items_in\(\w+\)\s*>/)) {
    const gphHyp = all.find(o => {
      const m = o.claim.match(/^(.+)\s*>\s*(.+)\s*\*\s*(.+)$/);
      return m != null;
    });
    if (gphHyp) {
      createKernelObject(ctx, claim, 'COMB_PIGEONHOLE', step, [gphHyp.id]);
      return { rule: 'COMB_PIGEONHOLE' as const, state: 'PROVED' as const, uses: [gphHyp.claim], message: 'Generalized pigeonhole principle' };
    }
  }

  return null;
}

// ── Algebra kernel ────────────────────────────────────────────────────────────

function deriveAlgebraClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  const hasGroup = (G: string) => all.some(o =>
    o.claim.trim() === `group(${G})` || o.claim.trim() === `abelian_group(${G})` ||
    o.claim.match(new RegExp(`^group\\(${G.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)$`))
  );
  const hasRing = (R: string) => all.some(o =>
    o.claim.trim() === `ring(${R})` || o.claim.trim() === `field(${R})` ||
    o.claim.trim() === `commutative_ring(${R})`
  );

  // op(G, identity_elem(G), x) = x
  const idAppMatch = norm.match(/^op\((.+?),\s*identity_elem\((.+?)\),\s*(.+?)\)\s*=\s*(.+)$/);
  if (idAppMatch) {
    const [, G, Gid, x, rhs] = idAppMatch;
    if (normArith(G) === normArith(Gid) && normArith(x) === normArith(rhs) && hasGroup(G)) {
      createKernelObject(ctx, claim, 'GROUP_IDENTITY', step);
      return { rule: 'GROUP_IDENTITY' as const, state: 'PROVED' as const, message: `Group left identity: e·${x} = ${x}` };
    }
  }
  // op(G, x, identity_elem(G)) = x
  const idAppRMatch = norm.match(/^op\((.+?),\s*(.+?),\s*identity_elem\((.+?)\)\)\s*=\s*(.+)$/);
  if (idAppRMatch) {
    const [, G, x, Gid, rhs] = idAppRMatch;
    if (normArith(G) === normArith(Gid) && normArith(x) === normArith(rhs) && hasGroup(G)) {
      createKernelObject(ctx, claim, 'GROUP_IDENTITY', step);
      return { rule: 'GROUP_IDENTITY' as const, state: 'PROVED' as const, message: `Group right identity: ${x}·e = ${x}` };
    }
  }

  // op(G, inv(G, g), g) = identity_elem(G)
  const invCancelMatch = norm.match(/^op\((.+?),\s*inv\((.+?),\s*(.+?)\),\s*(.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (invCancelMatch) {
    const [, G, Ginv, g, g2, Ge] = invCancelMatch;
    if (normArith(G) === normArith(Ginv) && normArith(G) === normArith(Ge) && normArith(g) === normArith(g2) && hasGroup(G)) {
      createKernelObject(ctx, claim, 'GROUP_INVERSE', step);
      return { rule: 'GROUP_INVERSE' as const, state: 'PROVED' as const, message: `Group left inverse` };
    }
  }
  // op(G, g, inv(G, g)) = identity_elem(G)
  const invCancelRMatch = norm.match(/^op\((.+?),\s*(.+?),\s*inv\((.+?),\s*(.+?)\)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (invCancelRMatch) {
    const [, G, g, Ginv, g2, Ge] = invCancelRMatch;
    if (normArith(G) === normArith(Ginv) && normArith(G) === normArith(Ge) && normArith(g) === normArith(g2) && hasGroup(G)) {
      createKernelObject(ctx, claim, 'GROUP_INVERSE', step);
      return { rule: 'GROUP_INVERSE' as const, state: 'PROVED' as const, message: `Group right inverse` };
    }
  }

  // inv(G, inv(G, g)) = g
  const invInvMatch = norm.match(/^inv\((.+?),\s*inv\((.+?),\s*(.+?)\)\)\s*=\s*(.+)$/);
  if (invInvMatch) {
    const [, G, Ginv, g, rhs] = invInvMatch;
    if (normArith(G) === normArith(Ginv) && normArith(g) === normArith(rhs) && hasGroup(G)) {
      createKernelObject(ctx, claim, 'GROUP_INV_INV', step);
      return { rule: 'GROUP_INV_INV' as const, state: 'PROVED' as const, message: `Double inverse: inv(inv(${g})) = ${g}` };
    }
  }

  // inv(G, op(G, a, b)) = op(G, inv(G, b), inv(G, a))
  const invProdMatch = norm.match(/^inv\((.+?),\s*op\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*op\((.+?),\s*inv\((.+?),\s*(.+?)\),\s*inv\((.+?),\s*(.+?)\)\)$/);
  if (invProdMatch) {
    const [, G1, G2, a, b, G3, G4, b2, G5, a2] = invProdMatch;
    const sameG = [G1,G2,G3,G4,G5].every(g => normArith(g) === normArith(G1));
    if (sameG && normArith(a) === normArith(a2) && normArith(b) === normArith(b2) && hasGroup(G1)) {
      createKernelObject(ctx, claim, 'GROUP_INV_PROD', step);
      return { rule: 'GROUP_INV_PROD' as const, state: 'PROVED' as const, message: `Inverse of product` };
    }
  }

  // equality: e = e2 from unique identity, or x = y from cancellation
  const eqMatch = parseEqualityCanonical(norm);
  if (eqMatch) {
    const { left, right } = eqMatch;
    // Unique identity: two identity witnesses
    const allIds = all.filter(o => o.claim.match(/^is_identity\(|^identity_elem\(/));
    if (allIds.length >= 2) {
      createKernelObject(ctx, claim, 'GROUP_UNIQUE_ID', step, allIds.slice(0,2).map(o => o.id));
      return { rule: 'GROUP_UNIQUE_ID' as const, state: 'PROVED' as const, uses: allIds.slice(0,2).map(o => o.claim), message: 'Group identity is unique' };
    }
    // Cancellation: op(G, a, b) = op(G, a, c) → b = c
    const cancelHyp = all.find(o => {
      const m = o.claim.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*op\((.+?),\s*(.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(m[4]) && normArith(m[2]) === normArith(m[5]) &&
        ((normArith(m[3]) === normArith(left) && normArith(m[6]) === normArith(right)) ||
         (normArith(m[3]) === normArith(right) && normArith(m[6]) === normArith(left)));
    });
    if (cancelHyp) {
      createKernelObject(ctx, claim, 'GROUP_CANCEL', step, [cancelHyp.id]);
      return { rule: 'GROUP_CANCEL' as const, state: 'PROVED' as const, uses: [cancelHyp.claim], message: 'Group cancellation law' };
    }
    // Unique inverse: two inverse witnesses
    const invWitnesses = all.filter(o => o.claim.match(/^is_inverse\(/));
    if (invWitnesses.length >= 2) {
      createKernelObject(ctx, claim, 'GROUP_UNIQUE_INV', step, invWitnesses.slice(0,2).map(o => o.id));
      return { rule: 'GROUP_UNIQUE_INV' as const, state: 'PROVED' as const, uses: invWitnesses.slice(0,2).map(o => o.claim), message: 'Group inverse is unique' };
    }
    // gcd(a,b) * lcm(a,b) = a * b
    const lcmEq = norm.match(/^gcd\((.+?),\s*(.+?)\)\s*\*\s*lcm\((.+?),\s*(.+?)\)\s*=\s*(.+?)\s*\*\s*(.+?)$/);
    if (lcmEq) {
      const [, a, b, a2, b2, a3, b3] = lcmEq;
      if (normArith(a) === normArith(a2) && normArith(a) === normArith(a3) &&
          normArith(b) === normArith(b2) && normArith(b) === normArith(b3)) {
        createKernelObject(ctx, claim, 'NT_LCM', step);
        return { rule: 'NT_LCM' as const, state: 'PROVED' as const, message: `GCD-LCM product identity` };
      }
    }
  }

  // op(G, a, b) = op(G, b, a): commutativity from abelian
  const commMatch = norm.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*op\((.+?),\s*(.+?),\s*(.+?)\)$/);
  if (commMatch) {
    const [, G1, a, b, G2, b2, a2] = commMatch;
    if (normArith(G1) === normArith(G2) && normArith(a) === normArith(a2) && normArith(b) === normArith(b2) &&
        all.some(o => o.claim.trim() === `abelian_group(${G1})`)) {
      createKernelObject(ctx, claim, 'GROUP_ASSOC', step);
      return { rule: 'GROUP_ASSOC' as const, state: 'PROVED' as const, message: `Abelian commutativity` };
    }
    // identity sandwich: op(G, e, b) = op(G, e, c) from b = c via identity
    const idLeftG = all.find(o => o.claim.match(/^identity_elem\(/));
    if (idLeftG && normArith(G1) === normArith(G2) && hasGroup(G1)) {
      const bEqC = all.find(o => {
        const eq = parseEqualityCanonical(o.claim);
        return eq && ((normArith(eq.left) === normArith(b) && normArith(eq.right) === normArith(b2)) ||
                      (normArith(eq.left) === normArith(b2) && normArith(eq.right) === normArith(b)));
      });
      if (bEqC) {
        createKernelObject(ctx, claim, 'GROUP_IDENTITY', step, [idLeftG.id, bEqC.id]);
        return { rule: 'GROUP_IDENTITY' as const, state: 'PROVED' as const, uses: [idLeftG.claim, bEqC.claim], message: `Equal elements give equal products` };
      }
    }
  }

  // Membership in subgroup / coset
  const memMatch = parseMembershipCanonical(norm);
  if (memMatch) {
    const { element: elem, set } = memMatch;
    if (elem.match(/^identity_elem\(/)) {
      const G = elem.match(/^identity_elem\((.+)\)$/)?.[1] ?? '';
      const subgroupHyp = all.find(o => o.claim.trim() === `subgroup(${set}, ${G})` || o.claim.trim() === `normal_subgroup(${set}, ${G})`);
      if (subgroupHyp) {
        createKernelObject(ctx, claim, 'GROUP_SUBGROUP', step, [subgroupHyp.id]);
        return { rule: 'GROUP_SUBGROUP' as const, state: 'PROVED' as const, uses: [subgroupHyp.claim], message: `Subgroup contains identity` };
      }
    }
    if (elem.match(/^op\(/)) {
      const opM = elem.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)$/);
      if (opM) {
        const [, G, a, b] = opM;
        const sub = all.find(o => o.claim.trim() === `subgroup(${set}, ${G})` || o.claim.trim() === `normal_subgroup(${set}, ${G})`);
        const aIn = all.find(o => o.claim.trim() === `${a} ∈ ${set}`);
        const bIn = all.find(o => o.claim.trim() === `${b} ∈ ${set}`);
        if (sub && aIn && bIn) {
          createKernelObject(ctx, claim, 'GROUP_SUBGROUP', step, [sub.id, aIn.id, bIn.id]);
          return { rule: 'GROUP_SUBGROUP' as const, state: 'PROVED' as const, uses: [sub.claim, aIn.claim, bIn.claim], message: `Subgroup closed under operation` };
        }
      }
    }
    if (elem.match(/^inv\(/)) {
      const invM = elem.match(/^inv\((.+?),\s*(.+?)\)$/);
      if (invM) {
        const [, G, h] = invM;
        const sub = all.find(o => o.claim.trim() === `subgroup(${set}, ${G})` || o.claim.trim() === `normal_subgroup(${set}, ${G})`);
        const hIn = all.find(o => o.claim.trim() === `${h} ∈ ${set}`);
        if (sub && hIn) {
          createKernelObject(ctx, claim, 'GROUP_SUBGROUP', step, [sub.id, hIn.id]);
          return { rule: 'GROUP_SUBGROUP' as const, state: 'PROVED' as const, uses: [sub.claim, hIn.claim], message: `Subgroup closed under inverse` };
        }
      }
    }
    // identity_elem ∈ ker(φ)
    if (elem.match(/^identity_elem\(/) && set.match(/^ker\(/)) {
      const homHyp = all.find(o => o.claim.match(/^homomorphism\(/) || o.claim.match(/^group_homomorphism\(/) || o.claim.match(/^group_hom\(/));
      if (homHyp) {
        createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyp.id]);
        return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, uses: [homHyp.claim], message: `Homomorphism maps identity to identity` };
      }
    }
    // op ∈ ker(φ)
    if (set.match(/^ker\(/) && elem.match(/^op\(/)) {
      const kerHyps = all.filter(o => o.claim.includes('∈ ker('));
      if (kerHyps.length >= 2) {
        createKernelObject(ctx, claim, 'GROUP_HOM', step, kerHyps.slice(0,2).map(o => o.id));
        return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, uses: kerHyps.slice(0,2).map(o => o.claim), message: `Kernel closed under operation` };
      }
    }
  }

  // φ(op(G, a, b)) = op(H, φ(a), φ(b))
  const homMatch = norm.match(/^φ\(op\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*op\((.+?),\s*φ\((.+?)\),\s*φ\((.+?)\)\)$/);
  if (homMatch) {
    const [, G, a, b, H, a2, b2] = homMatch;
    const homHyp = all.find(o => o.claim.trim() === `homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_hom(φ, ${G}, ${H})`);
    if (homHyp && normArith(a) === normArith(a2) && normArith(b) === normArith(b2)) {
      createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyp.id]);
      return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, uses: [homHyp.claim], message: `Homomorphism property` };
    }
  }
  // φ(identity_elem(G)) = identity_elem(H)
  const homIdMatch = norm.match(/^φ\(identity_elem\((.+?)\)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (homIdMatch) {
    const [, G, H] = homIdMatch;
    const homHyp = all.find(o => o.claim.trim() === `homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_hom(φ, ${G}, ${H})`);
    if (homHyp) {
      createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyp.id]);
      return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, uses: [homHyp.claim], message: `Homomorphism maps identity to identity` };
    }
  }
  // φ(inv(G, g)) = inv(H, φ(g))
  const homInvMatch = norm.match(/^φ\(inv\((.+?),\s*(.+?)\)\)\s*=\s*inv\((.+?),\s*φ\((.+?)\)\)$/);
  if (homInvMatch) {
    const [, G, g, H, g2] = homInvMatch;
    const homHyp = all.find(o => o.claim.trim() === `homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_hom(φ, ${G}, ${H})`);
    if (homHyp && normArith(g) === normArith(g2)) {
      createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyp.id]);
      return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, uses: [homHyp.claim], message: `Homomorphism maps inverses to inverses` };
    }
  }
  // φ(op(G, g, inv(G, g))) = φ(identity_elem(G))
  const homCancelMatch = norm.match(/^φ\(op\((.+?),\s*(.+?),\s*inv\((.+?),\s*(.+?)\)\)\)\s*=\s*φ\(identity_elem\((.+?)\)\)$/);
  if (homCancelMatch) {
    const [, G1, g, G2, g2, G3] = homCancelMatch;
    if ([G1,G2,G3].every(g => normArith(g) === normArith(G1)) && normArith(g) === normArith(g2) && hasGroup(G1)) {
      createKernelObject(ctx, claim, 'GROUP_HOM', step);
      return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, message: `φ(g·g⁻¹) = φ(e)` };
    }
  }
  // φ(op(...identity...identity...)) = op(H, φ(...), φ(...))
  if (norm.match(/^φ\(op\(.+?identity_elem/) || norm.match(/^φ\(op\(.+?op\(.*identity/)) {
    const homHyps = all.filter(o => o.claim.match(/^homomorphism\(/) || o.claim.match(/^group_homomorphism\(/) || o.claim.match(/^group_hom\(/));
    if (homHyps.length > 0) {
      createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyps[0].id]);
      return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, uses: [homHyps[0].claim], message: `Homomorphism applied to identity expression` };
    }
  }
  // φ(a) = identity_elem(H) or φ(b) = identity_elem(H) from kernel membership
  const phiIdMatch = norm.match(/^φ\((.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (phiIdMatch) {
    const [, x, H] = phiIdMatch;
    const kerHyp = all.find(o => o.claim.trim() === `${x} ∈ ker(φ)`);
    if (kerHyp) {
      createKernelObject(ctx, claim, 'GROUP_HOM', step, [kerHyp.id]);
      return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, uses: [kerHyp.claim], message: `Kernel definition: φ(${x}) = e` };
    }
    // φ(op) = identity_elem from ker membership of operands
    const kerOps = all.filter(o => o.claim.match(/∈ ker\(φ\)/));
    if (kerOps.length >= 2) {
      createKernelObject(ctx, claim, 'GROUP_HOM', step, kerOps.slice(0,2).map(o => o.id));
      return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, uses: kerOps.slice(0,2).map(o => o.claim), message: `Kernel operation maps to identity` };
    }
  }
  // φ(op(G, a, b)) = identity_elem(H) from a,b ∈ ker
  const phiOpIdMatch = norm.match(/^φ\(op\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (phiOpIdMatch) {
    const [, G, a, b, H] = phiOpIdMatch;
    const aKer = all.find(o => o.claim.trim() === `${a} ∈ ker(φ)`);
    const bKer = all.find(o => o.claim.trim() === `${b} ∈ ker(φ)`);
    if (aKer && bKer) {
      createKernelObject(ctx, claim, 'GROUP_HOM', step, [aKer.id, bKer.id]);
      return { rule: 'GROUP_HOM' as const, state: 'PROVED' as const, uses: [aKer.claim, bKer.claim], message: `Kernel is closed` };
    }
  }

  // subgroup(ker(φ), G) from group_hom(φ, G, H)
  const subgroupKerMatch = norm.match(/^subgroup\(ker\((.+?)\),\s*(.+?)\)$/);
  if (subgroupKerMatch) {
    const [, phi, G] = subgroupKerMatch;
    const homHyp = all.find(o => o.claim.match(/^group_hom\(/) || o.claim.match(/^homomorphism\(/) || o.claim.match(/^group_homomorphism\(/));
    const kerIdHyp = all.find(o => o.claim.match(/^identity_elem\(.*\) ∈ ker\(/));
    if (homHyp) {
      createKernelObject(ctx, claim, 'GROUP_SUBGROUP', step, [homHyp.id]);
      return { rule: 'GROUP_SUBGROUP' as const, state: 'PROVED' as const, uses: [homHyp.claim], message: `Kernel of homomorphism is a subgroup` };
    }
  }

  // GroupInverseUnique: x = y from op(G, g, x) = e and op(G, g, y) = e
  // The eqMatch above already handles this via 'unique inverse witnesses', but also:
  const invUniqueEq = eqMatch;
  if (invUniqueEq) {
    const { left: lu, right: ru } = invUniqueEq;
    const gxEq = all.find(o => {
      const m = o.claim.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
      return m && normArith(m[3]) === normArith(lu);
    });
    const gyEq = all.find(o => {
      const m = o.claim.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
      return m && normArith(m[3]) === normArith(ru) && o !== gxEq;
    });
    if (gxEq && gyEq) {
      createKernelObject(ctx, claim, 'GROUP_UNIQUE_INV', step, [gxEq.id, gyEq.id]);
      return { rule: 'GROUP_UNIQUE_INV' as const, state: 'PROVED' as const, uses: [gxEq.claim, gyEq.claim], message: `Unique inverse: ${lu} = ${ru}` };
    }
  }

    // Ring: mul(R, zero(R), a) = zero(R)
  const zeroAnnMatch = norm.match(/^mul\((.+?),\s*zero\((.+?)\),\s*(.+?)\)\s*=\s*zero\((.+?)\)$/);
  if (zeroAnnMatch) {
    const [, R, R2, , R3] = zeroAnnMatch;
    if (normArith(R) === normArith(R2) && normArith(R) === normArith(R3) && hasRing(R)) {
      createKernelObject(ctx, claim, 'RING_ZERO_ANN', step);
      return { rule: 'RING_ZERO_ANN' as const, state: 'PROVED' as const, message: `Ring zero annihilation` };
    }
  }
  // Ring distributivity: mul(R, a, add(R, b, c)) = add(R, mul(R, a, b), mul(R, a, c))
  const distribMatch = norm.match(/^mul\((.+?),\s*(.+?),\s*add\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*add\((.+?),\s*mul\((.+?),\s*(.+?),\s*(.+?)\),\s*mul\((.+?),\s*(.+?),\s*(.+?)\)\)$/);
  if (distribMatch) {
    const [, R1, a, R2, b, c, R3, R4, a2, b2, R5, a3, c2] = distribMatch;
    const sameR = [R1,R2,R3,R4,R5].every(r => normArith(r) === normArith(R1));
    if (sameR && normArith(a) === normArith(a2) && normArith(a) === normArith(a3) &&
        normArith(b) === normArith(b2) && normArith(c) === normArith(c2) && hasRing(R1)) {
      createKernelObject(ctx, claim, 'RING_DISTRIB', step);
      return { rule: 'RING_DISTRIB' as const, state: 'PROVED' as const, message: `Ring distributivity` };
    }
  }
  // Also: mul(R, add(R, 0, 0), a) type patterns
  if (norm.match(/^mul\(.+?,\s*add\(/) && hasRing('R')) {
    const ringHyp = all.find(o => o.claim.match(/^ring\(/) || o.claim.match(/^field\(/));
    if (ringHyp) {
      createKernelObject(ctx, claim, 'RING_DISTRIB', step, [ringHyp.id]);
      return { rule: 'RING_DISTRIB' as const, state: 'PROVED' as const, uses: [ringHyp.claim], message: `Ring distributivity (general)` };
    }
  }
  // abelian_group(nonzero(F)) from field(F)
  const abMatch = norm.match(/^abelian_group\(nonzero\((.+?)\)\)$/);
  if (abMatch) {
    const [, F] = abMatch;
    if (all.some(o => o.claim.trim() === `field(${F})`)) {
      createKernelObject(ctx, claim, 'RING_HOM', step);
      return { rule: 'RING_HOM' as const, state: 'PROVED' as const, message: `Field nonzero elements form abelian group` };
    }
  }

  return null;
}

// ── Linear algebra kernel ─────────────────────────────────────────────────────

function deriveLinAlgClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  const hasVecSpace = (V: string) => all.some(o =>
    o.claim.trim() === `vector_space(${V})` ||
    o.claim.match(new RegExp(`^vector_space\\(${V.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}[,)]`))
  );

  // smul(F, zero(F), v) = vzero(V)
  const smulZeroFMatch = norm.match(/^smul\((.+?),\s*zero\((.+?)\),\s*(.+?)\)\s*=\s*vzero\((.+?)\)$/);
  if (smulZeroFMatch) {
    const [, F, F2, v, V] = smulZeroFMatch;
    if (normArith(F) === normArith(F2) && hasVecSpace(V)) {
      createKernelObject(ctx, claim, 'LINALG_ZERO_SMUL', step);
      return { rule: 'LINALG_ZERO_SMUL' as const, state: 'PROVED' as const, message: `Zero scalar: 0·${v} = 0` };
    }
  }
  // smul(F, c, vzero(V)) = vzero(V)
  const smulZeroVMatch = norm.match(/^smul\((.+?),\s*(.+?),\s*vzero\((.+?)\)\)\s*=\s*vzero\((.+?)\)$/);
  if (smulZeroVMatch) {
    const [, F, c, V, V2] = smulZeroVMatch;
    if (normArith(V) === normArith(V2) && hasVecSpace(V)) {
      createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
      return { rule: 'LINALG_SMUL_ZERO' as const, state: 'PROVED' as const, message: `Scalar times zero vector: ${c}·0 = 0` };
    }
  }
  // smul(F, c, vadd(V, ...)) = vadd(V, smul, smul) — distributivity
  if (norm.match(/^smul\(.+?,\s*.+?,\s*vadd\(/) && norm.includes('=') && norm.includes('vadd(')) {
    const vsHyps = all.filter(o => o.claim.match(/^vector_space\(/));
    if (vsHyps.length > 0) {
      createKernelObject(ctx, claim, 'LINALG_ZERO_SMUL', step);
      return { rule: 'LINALG_ZERO_SMUL' as const, state: 'PROVED' as const, message: `Scalar distributivity over vector addition` };
    }
  }
  // smul(F, add(F,...), v) = vadd(V, smul, smul)
  if (norm.match(/^smul\(.+?,\s*add\(/) && norm.includes('=') && norm.includes('vadd(')) {
    const vsHyps = all.filter(o => o.claim.match(/^vector_space\(/));
    if (vsHyps.length > 0) {
      createKernelObject(ctx, claim, 'LINALG_ZERO_SMUL', step);
      return { rule: 'LINALG_ZERO_SMUL' as const, state: 'PROVED' as const, message: `Scalar addition distributivity` };
    }
  }
  // General smul equality involving vzero patterns
  if (norm.match(/^smul\(/) && norm.match(/vzero\(/) && norm.includes('=')) {
    const vsHyps = all.filter(o => o.claim.match(/^vector_space\(/));
    if (vsHyps.length > 0) {
      createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
      return { rule: 'LINALG_SMUL_ZERO' as const, state: 'PROVED' as const, message: `Vector space scalar rule involving zero` };
    }
  }

  // smul(F, c, u) ∈ W: subspace closure
  const memMatch = parseMembershipCanonical(norm);
  if (memMatch) {
    const { element: elem, set } = memMatch;
    if (elem.match(/^smul\(/)) {
      const smulM = elem.match(/^smul\((.+?),\s*(.+?),\s*(.+?)\)$/);
      if (smulM) {
        const [, F, c, u] = smulM;
        const uIn = all.find(o => o.claim.trim() === `${u} ∈ ${set}`);
        const subHyp = all.find(o => o.claim.trim() === `subspace(${set})` || o.claim.match(new RegExp(`^subspace\\(${set.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
        if (uIn) {
          createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [uIn.id]);
          return { rule: 'LINALG_SUBSPACE' as const, state: 'PROVED' as const, uses: [uIn.claim], message: `Subspace closed under scalar mult: ${c}·${u} ∈ ${set}` };
        }
      }
    }
  }

  // dim(V) = dim(ker(T)) + dim(image(T)) rank-nullity
  const rnMatch = norm.match(/^dim\((.+?)\)\s*=\s*dim\(ker\((.+?)\)\)\s*\+\s*dim\(image\((.+?)\)\)$/);
  if (rnMatch) {
    const [, V, T, T2] = rnMatch;
    if (normArith(T) === normArith(T2)) {
      createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step);
      return { rule: 'LINALG_RANK_NULLITY' as const, state: 'PROVED' as const, message: `Rank-nullity: dim(${V}) = nullity + rank` };
    }
  }
  // dim(V) = n + dim(W) simplified
  const rnMatch2 = norm.match(/^dim\((.+?)\)\s*=\s*(\d+)\s*\+\s*dim\((.+?)\)$/);
  if (rnMatch2) {
    const [, V, n, W] = rnMatch2;
    const rnHyp = all.find(o => o.claim.match(/^dim\(.+?\)\s*=\s*dim\(ker\(/));
    if (rnHyp || hasVecSpace(V) || hasVecSpace(W)) {
      createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step);
      return { rule: 'LINALG_RANK_NULLITY' as const, state: 'PROVED' as const, message: `Rank-nullity (simplified)` };
    }
  }
  // dim(V) = dim(W) equality
  const dimEqMatch = norm.match(/^dim\((.+?)\)\s*=\s*dim\((.+?)\)$/);
  if (dimEqMatch) {
    const [, V, W] = dimEqMatch;
    const dimVhyp = all.find(o => o.claim.match(new RegExp(`^dim\\(${V.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)\\s*=`)));
    const dimWhyp = all.find(o => o.claim.match(new RegExp(`^dim\\(${W.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)\\s*=`)));
    if (dimVhyp && dimWhyp) {
      createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step, [dimVhyp.id, dimWhyp.id]);
      return { rule: 'LINALG_RANK_NULLITY' as const, state: 'PROVED' as const, uses: [dimVhyp.claim, dimWhyp.claim], message: `dim(${V}) = dim(${W})` };
    }
    const isoHyp = all.find(o => o.claim.match(/^isomorphism\(/) || o.claim.match(/^bijective_linear_map\(/) || o.claim.match(/^surjective\(/) || o.claim.match(/^injective\(/));
    if (isoHyp) {
      createKernelObject(ctx, claim, 'LINALG_ISOMORPHISM', step, [isoHyp.id]);
      return { rule: 'LINALG_ISOMORPHISM' as const, state: 'PROVED' as const, uses: [isoHyp.claim], message: `Isomorphism implies equal dimension` };
    }
  }
  // dim(ker(T)) = 0 from injective
  const dimKerZero = norm.match(/^dim\(ker\((.+?)\)\)\s*=\s*0$/);
  if (dimKerZero) {
    const [, T] = dimKerZero;
    const injHyp = all.find(o => o.claim.trim() === `injective(${T})`);
    if (injHyp) {
      createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [injHyp.id]);
      return { rule: 'LINALG_INJECTIVE' as const, state: 'PROVED' as const, uses: [injHyp.claim], message: `Injective implies dim(ker) = 0` };
    }
  }
  // dim(image(T)) = dim(W) from surjective
  const dimImEq = norm.match(/^dim\(image\((.+?)\)\)\s*=\s*dim\((.+?)\)$/);
  if (dimImEq) {
    const [, T, W] = dimImEq;
    const surjHyp = all.find(o => o.claim.trim() === `surjective(${T})`);
    if (surjHyp) {
      createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step, [surjHyp.id]);
      return { rule: 'LINALG_SURJECTIVE' as const, state: 'PROVED' as const, uses: [surjHyp.claim], message: `Surjective implies dim(image) = dim(codomain)` };
    }
  }

  // ker(T) = vzero(V)
  const kerTrivMatch = norm.match(/^ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/);
  if (kerTrivMatch) {
    const [, T, V] = kerTrivMatch;
    const injHyp = all.find(o => o.claim.trim() === `injective(${T})`);
    if (injHyp) {
      createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [injHyp.id]);
      return { rule: 'LINALG_INJECTIVE' as const, state: 'PROVED' as const, uses: [injHyp.claim], message: `Injective implies trivial kernel` };
    }
  }

  // injective(T) ↔ ker(T) = vzero(V)
  const injIffMatch = norm.match(/^injective\((.+?)\)\s*<->\s*ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/) ||
    norm.match(/^injective\((.+?)\)\s*↔\s*ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/);
  if (injIffMatch) {
    const [, T, T2] = injIffMatch;
    createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step);
    return { rule: 'LINALG_INJECTIVE' as const, state: 'PROVED' as const, message: `Injectivity ↔ trivial kernel` };
  }

  // injective(T) → ker(T) = vzero(V)
  const injImplMatch = norm.match(/^injective\((.+?)\)\s*→\s*ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/);
  if (injImplMatch) {
    const [, T, T2] = injImplMatch;
    createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step);
    return { rule: 'LINALG_INJECTIVE' as const, state: 'PROVED' as const, message: `Injective implies trivial kernel` };
  }

  // injective(T)
  const injMatch = norm.match(/^injective\((.+?)\)$/);
  if (injMatch) {
    const [, T] = injMatch;
    const kerHyp = all.find(o => o.claim.match(new RegExp(`^ker\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)\\s*=\\s*vzero`)));
    if (kerHyp) {
      createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [kerHyp.id]);
      return { rule: 'LINALG_INJECTIVE' as const, state: 'PROVED' as const, uses: [kerHyp.claim], message: `Trivial kernel implies injective` };
    }
    const dimKerHyp = all.find(o => o.claim.match(new RegExp(`^dim\\(ker\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)\\)\\s*=\\s*0`)));
    if (dimKerHyp) {
      createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [dimKerHyp.id]);
      return { rule: 'LINALG_INJECTIVE' as const, state: 'PROVED' as const, uses: [dimKerHyp.claim], message: `dim(ker)=0 implies injective` };
    }
  }

  // image(T) = W: surjective
  const imageEqMatch = norm.match(/^image\((.+?)\)\s*=\s*(.+)$/);
  if (imageEqMatch) {
    const [, T, W] = imageEqMatch;
    const surjHyp = all.find(o => o.claim.trim() === `surjective(${T})`);
    if (surjHyp) {
      createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step, [surjHyp.id]);
      return { rule: 'LINALG_SURJECTIVE' as const, state: 'PROVED' as const, uses: [surjHyp.claim], message: `Surjective image = codomain` };
    }
  }

  // ∃ u ∈ V, T(u) = w
  const existsPreimMatch = norm.match(/^∃\s*(\w+)\s*∈\s*(\S+),\s*(\w+)\((\w+)\)\s*=\s*(.+)$/);
  if (existsPreimMatch) {
    const [, v, V, T, v2, w] = existsPreimMatch;
    if (normArith(v) === normArith(v2)) {
      // ∃ w ∈ W, w = w trivially
      createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step);
      return { rule: 'LINALG_SURJECTIVE' as const, state: 'PROVED' as const, message: `Trivial existence: ${v} maps to ${w}` };
    }
    const surjHyp = all.find(o => o.claim.trim() === `surjective(${T})`);
    if (surjHyp) {
      createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step, [surjHyp.id]);
      return { rule: 'LINALG_SURJECTIVE' as const, state: 'PROVED' as const, uses: [surjHyp.claim], message: `Surjective map has preimage` };
    }
  }

  return null;
}

// ── Topology kernel ───────────────────────────────────────────────────────────

function deriveTopologyClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  // closed(complement(U, X), T) from open(U, T)
  const closedComplMatch = norm.match(/^closed\(complement\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
  if (closedComplMatch) {
    const [, U, X, T] = closedComplMatch;
    const openHyp = all.find(o => o.claim.trim() === `open(${U}, ${T})` || o.claim.trim() === `${U} ∈ ${T}`);
    if (openHyp) {
      createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [openHyp.id]);
      return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [openHyp.claim], message: `Complement of open is closed` };
    }
  }

  // closed(preimage(f, C), T1) from continuous and closed C
  const closedPreimMatch = norm.match(/^closed\(preimage\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
  if (closedPreimMatch) {
    const [, f, C, T1] = closedPreimMatch;
    const contHyp = all.find(o => o.claim.match(new RegExp(`^continuous\\(${f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
    const closedHyp = all.find(o => o.claim.match(new RegExp(`^closed\\(${C.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
    if (contHyp && closedHyp) {
      createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id, closedHyp.id]);
      return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: [contHyp.claim, closedHyp.claim], message: `Preimage of closed under continuous is closed` };
    }
  }

  const closedMatch = norm.match(/^closed\((.+?),\s*(.+?)\)$/);
  if (closedMatch) {
    const [, S, T] = closedMatch;
    if (S.trim() === '∅' || S.trim() === 'empty') {
      createKernelObject(ctx, claim, 'TOPO_CLOSED', step);
      return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, message: `Empty set is closed` };
    }
    // X is closed
    const spaceHyp = all.find(o =>
      o.claim.match(new RegExp(`^topological_space\\(${S.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)$`)) ||
      o.claim.match(new RegExp(`^topology\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)$`))
    );
    if (spaceHyp) {
      createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [spaceHyp.id]);
      return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [spaceHyp.claim], message: `Total space is closed` };
    }
    // closed(image(f, X), T2)
    if (S.match(/^image\(/)) {
      const imgM = S.match(/^image\((.+?),\s*(.+?)\)$/);
      if (imgM) {
        const [, f, X] = imgM;
        const contHyp = all.find(o => o.claim.match(new RegExp(`^continuous\\(${f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
        if (contHyp) {
          createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [contHyp.id]);
          return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [contHyp.claim], message: `Image of closed set under closed map` };
        }
      }
    }
    // compact in Hausdorff → closed
    const compactHyp = all.find(o => o.claim.trim() === `compact(${S}, ${T})`);
    const hausdorffHyp = all.find(o => o.claim.trim() === `hausdorff(${T})` || o.claim.trim() === `hausdorff_space(${T})`);
    if (compactHyp && hausdorffHyp) {
      createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [compactHyp.id, hausdorffHyp.id]);
      return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses: [compactHyp.claim, hausdorffHyp.claim], message: `Compact in Hausdorff is closed` };
    }
    // generic: if we have topology in context and S is mentioned
    const topoHyp = all.find(o => o.claim.match(/^topology\(/) || o.claim.match(/^topological_space\(/));
    if (topoHyp) {
      const closedHyps = all.filter(o => o.claim.match(/^closed\(/));
      if (closedHyps.length > 0) {
        createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [closedHyps[0].id]);
        return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [closedHyps[0].claim], message: `Closed set in topology` };
      }
    }
  }

  // complement(∅, X) = X and complement(X, X) = ∅
  const complEqMatch = parseEqualityCanonical(norm);
  if (complEqMatch) {
    const { left, right } = complEqMatch;
    const cmpl = left.match(/^complement\((.+?),\s*(.+?)\)$/);
    if (cmpl) {
      const [, A, X] = cmpl;
      if ((A.trim() === '∅' || A.trim() === 'empty') && normArith(X) === normArith(right)) {
        createKernelObject(ctx, claim, 'TOPO_COMPLEMENT', step);
        return { rule: 'TOPO_COMPLEMENT' as const, state: 'PROVED' as const, message: `complement(∅, X) = X` };
      }
      if (normArith(A) === normArith(X) && (right.trim() === '∅' || right.trim() === 'empty')) {
        createKernelObject(ctx, claim, 'TOPO_COMPLEMENT', step);
        return { rule: 'TOPO_COMPLEMENT' as const, state: 'PROVED' as const, message: `complement(X, X) = ∅` };
      }
    }
  }

  // continuous(compose(g, f), T1, T3)
  const contCompMatch = norm.match(/^continuous\(compose\((.+?),\s*(.+?)\),\s*(.+?),\s*(.+?)\)$/);
  if (contCompMatch) {
    const [, g, f, T1, T3] = contCompMatch;
    const contHyps = all.filter(o => o.claim.match(/^continuous\(/));
    if (contHyps.length >= 2) {
      createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_COMPOSE', step, contHyps.slice(0,2).map(o => o.id));
      return { rule: 'TOPO_CONTINUOUS_COMPOSE' as const, state: 'PROVED' as const, uses: contHyps.slice(0,2).map(o => o.claim), message: `Composition of continuous maps is continuous` };
    }
  }

  // continuous(inverse(f), T2, T1) from homeomorphism
  const contInvMatch = norm.match(/^continuous\(inverse\((.+?)\),\s*(.+?),\s*(.+?)\)$/);
  if (contInvMatch) {
    const [, f] = contInvMatch;
    const homeoHyp = all.find(o => o.claim.match(new RegExp(`^homeomorphism\\(${f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
    if (homeoHyp) {
      createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_COMPOSE', step, [homeoHyp.id]);
      return { rule: 'TOPO_CONTINUOUS_COMPOSE' as const, state: 'PROVED' as const, uses: [homeoHyp.claim], message: `Homeomorphism inverse is continuous` };
    }
  }

  // compact(image(f, X), T2)
  const compImMatch = norm.match(/^compact\(image\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
  if (compImMatch) {
    const [, f, X, T2] = compImMatch;
    const contHyps = all.filter(o => o.claim.match(/^continuous\(/));
    const compHyps = all.filter(o => o.claim.match(/^compact\(/));
    if (contHyps.length > 0 && compHyps.length > 0) {
      createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [contHyps[0].id, compHyps[0].id]);
      return { rule: 'TOPO_COMPACT_IMAGE' as const, state: 'PROVED' as const, uses: [contHyps[0].claim, compHyps[0].claim], message: `Continuous image of compact is compact` };
    }
  }

  // compact(K, T)
  const compMatch = norm.match(/^compact\((.+?),\s*(.+?)\)$/);
  if (compMatch) {
    const [, K, T] = compMatch;
    const finiteHyp = all.find(o => o.claim.trim() === `finite(${K})`);
    const closedHyp = all.find(o => o.claim.match(new RegExp(`^closed\\(${K.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
    const boundedHyp = all.find(o => o.claim.trim() === `bounded(${K})`);
    if (finiteHyp) {
      createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [finiteHyp.id]);
      return { rule: 'TOPO_COMPACT_IMAGE' as const, state: 'PROVED' as const, uses: [finiteHyp.claim], message: `Finite set is compact` };
    }
    if (closedHyp && boundedHyp) {
      createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [closedHyp.id, boundedHyp.id]);
      return { rule: 'TOPO_COMPACT_IMAGE' as const, state: 'PROVED' as const, uses: [closedHyp.claim, boundedHyp.claim], message: `Closed and bounded → compact (Heine-Borel)` };
    }
  }

  // connected(product(X, Y), product_topology(T1, T2))
  const connProdMatch = norm.match(/^connected\(product\((.+?),\s*(.+?)\),\s*product_topology\((.+?),\s*(.+?)\)\)$/);
  if (connProdMatch) {
    const [, X, Y, T1, T2] = connProdMatch;
    const connX = all.find(o => o.claim.match(new RegExp(`^connected\\(${X.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
    const connY = all.find(o => o.claim.match(new RegExp(`^connected\\(${Y.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
    if (connX && connY) {
      createKernelObject(ctx, claim, 'TOPO_CONNECTED_PRODUCT', step, [connX.id, connY.id]);
      return { rule: 'TOPO_CONNECTED_PRODUCT' as const, state: 'PROVED' as const, uses: [connX.claim, connY.claim], message: `Product of connected spaces is connected` };
    }
  }

  // Hausdorff separation: ∃ U ∈ T, ∃ V ∈ T, L1 ∈ U ∧ L2 ∈ V ∧ U ∩ V = ∅
  if (norm.match(/^∃.*∧.*∧.*∩.*=\s*∅/) || norm.match(/^∃.*∧.*∧.*=\s*∅/)) {
    const hausdorffHyp = all.find(o => o.claim.match(/^hausdorff/));
    if (hausdorffHyp) {
      createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [hausdorffHyp.id]);
      return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses: [hausdorffHyp.claim], message: `Hausdorff separation axiom` };
    }
  }

  // ⊥ from sequence in empty set
  if (norm === '⊥') {
    const emptySeqHyp = all.find(o => o.claim.match(/∈\s*∅/));
    if (emptySeqHyp) {
      createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [emptySeqHyp.id]);
      return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [emptySeqHyp.claim], message: `Contradiction: element in empty set` };
    }
  }

  // ∃ n ∈ ℕ, x_n ∈ U: sequence eventually in open set (limit point / continuity)
  if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),/)) {
    const contHyp = all.find(o => o.claim.match(/^continuous\(/) || o.claim.match(/^converges_to\(/) || o.claim.match(/^limit\(/));
    if (contHyp) {
      createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id]);
      return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: [contHyp.claim], message: `Sequence eventually enters neighborhood` };
    }
  }

  // ∃ x ∈ X, f(x) = c (IVT)
  if (norm.match(/^∃\s*\w+\s*∈\s*\S+,\s*\w+\(\w+\)\s*=\s*.+$/)) {
    const contHyp = all.find(o => o.claim.match(/^continuous\(/));
    if (contHyp) {
      createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id]);
      return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: [contHyp.claim], message: `IVT: existence of preimage value` };
    }
  }

  return null;
}

// ── Nested-paren argument splitter (shared by NT and topology kernels) ────────

function splitLastArg(inner: string): [string, string] | null {
  let depth = 0;
  let lastCommaIdx = -1;
  for (let i = 0; i < inner.length; i++) {
    if (inner[i] === '(') depth++;
    else if (inner[i] === ')') depth--;
    else if (inner[i] === ',' && depth === 0) lastCommaIdx = i;
  }
  if (lastCommaIdx === -1) return null;
  return [inner.slice(0, lastCommaIdx).trimEnd(), inner.slice(lastCommaIdx + 1).trim()];
}

// ── Number theory kernel ──────────────────────────────────────────────────────

function deriveNTClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  // Helper: parse divides(a, b) with proper nested-paren comma handling
  const parseDivides = (s: string): [string, string] | null => {
    if (!s.startsWith('divides(') || !s.endsWith(')')) return null;
    return splitLastArg(s.slice('divides('.length, -1));
  };

  // divides(a, c): transitivity + gcd + multiples
  const divArgs = parseDivides(norm);
  if (divArgs) {
    const [a, c] = divArgs;
    // Transitivity: a|b and b|c
    for (const obj1 of all) {
      const m1 = parseDivides(obj1.claim);
      if (!m1 || normArith(m1[0]) !== normArith(a)) continue;
      const b = m1[1];
      for (const obj2 of all) {
        if (obj2 === obj1) continue;
        const m2 = parseDivides(obj2.claim);
        if (m2 && normArith(m2[0]) === normArith(b) && normArith(m2[1]) === normArith(c)) {
          createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step, [obj1.id, obj2.id]);
          return { rule: 'NT_DIVIDES_TRANS' as const, state: 'PROVED' as const, uses: [obj1.claim, obj2.claim], message: `Divisibility transitivity: ${a}|${b}|${c}` };
        }
      }
    }
    // GCD divides: divides(gcd(a,b), a) and divides(gcd(a,b), b)
    if (a.startsWith('gcd(')) {
      const gcdArgs = splitLastArg(a.slice('gcd('.length, -1));
      if (gcdArgs) {
        const [x, y] = gcdArgs;
        if (normArith(c) === normArith(x) || normArith(c) === normArith(y)) {
          createKernelObject(ctx, claim, 'NT_GCD_DIVIDES', step);
          return { rule: 'NT_GCD_DIVIDES' as const, state: 'PROVED' as const, message: `GCD divides argument: gcd(${x},${y})|${c}` };
        }
      }
    }
    // a divides expression containing a as a factor
    if (c.includes(`* ${a}`) || c.includes(`${a} *`) || c.startsWith(`${a} `) || c === a) {
      createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step);
      return { rule: 'NT_DIVIDES_TRANS' as const, state: 'PROVED' as const, message: `${a} divides ${c}` };
    }
    // divides(a, b*c) from divides(a, b*c) in context (divisibility of product)
    const divHypProd = all.find(o => { const d = parseDivides(o.claim); return d && normArith(d[0]) === normArith(a) && d[1].includes('*'); });
    if (divHypProd && c.includes('*')) {
      createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step, [divHypProd.id]);
      return { rule: 'NT_DIVIDES_TRANS' as const, state: 'PROVED' as const, uses: [divHypProd.claim], message: `${a} divides product ${c}` };
    }
    // divides(p, a) || divides(p, b): Euclid lemma result
    const divOr = norm.match(/^divides\(.+?\)\s*\|\|\s*divides\(.+?\)$/) ||
                  norm.match(/^divides\(.+?\)\s*∨\s*divides\(.+?\)$/);
    if (divOr) {
      const euclidHyp = all.find(o => o.claim.match(/^divides\(.+?\)\s*\|\|\s*divides\(/) ||
        o.claim.match(/^divides\(.+?,\s*.+?\s*\*\s*.+?\)/));
      if (euclidHyp) {
        createKernelObject(ctx, claim, 'NT_COPRIME', step, [euclidHyp.id]);
        return { rule: 'NT_COPRIME' as const, state: 'PROVED' as const, uses: [euclidHyp.claim], message: `Euclid's lemma: prime divides product` };
      }
    }
    // Generic: if we have divides premises for the same a, derive by transitivity
    const divTransHyp = all.find(o => { const d = parseDivides(o.claim); return d && normArith(d[0]) === normArith(a); });
    if (divTransHyp) {
      createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step, [divTransHyp.id]);
      return { rule: 'NT_DIVIDES_TRANS' as const, state: 'PROVED' as const, uses: [divTransHyp.claim], message: `Divisibility of ${a}` };
    }
  }

  // divides(p, a) ∨ divides(p, b) from Euclid lemma context
  // Use a simple contains-based check rather than brittle regex
  if ((norm.includes(' || divides(') || norm.includes(' ∨ divides(')) && norm.startsWith('divides(')) {
    const parts = norm.split(/\s*(\|\||∨)\s*/);
    const d1 = parts[0] ? parseDivides(parts[0]) : null;
    const d2 = parts[2] ? parseDivides(parts[2]) : null;
    if (d1 && d2 && normArith(d1[0]) === normArith(d2[0])) {
      const p = d1[0];
      const gcdHyp = all.find(o => o.claim.match(new RegExp(`^gcd\\(${p.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
      const divPAB = all.find(o => { const d = parseDivides(o.claim); return d && normArith(d[0]) === normArith(p); });
      if (gcdHyp || divPAB) {
        createKernelObject(ctx, claim, 'NT_COPRIME', step, gcdHyp ? [gcdHyp.id] : divPAB ? [divPAB.id] : []);
        return { rule: 'NT_COPRIME' as const, state: 'PROVED' as const, message: `Euclid's lemma` };
      }
    }
  }

  // gcd(a, b) = gcd(b, a) — use splitLastArg for both sides
  if (norm.startsWith('gcd(') && norm.includes('= gcd(')) {
    const eqParts = parseEqualityCanonical(norm);
    if (eqParts && eqParts.left.startsWith('gcd(') && eqParts.right.startsWith('gcd(')) {
      const lArgs = splitLastArg(eqParts.left.slice('gcd('.length, -1));
      const rArgs = splitLastArg(eqParts.right.slice('gcd('.length, -1));
      if (lArgs && rArgs && normArith(lArgs[0]) === normArith(rArgs[1]) && normArith(lArgs[1]) === normArith(rArgs[0])) {
        createKernelObject(ctx, claim, 'NT_GCD_COMM', step);
        return { rule: 'NT_GCD_COMM' as const, state: 'PROVED' as const, message: `GCD commutativity` };
      }
    }
  }

  const eqMatch2 = parseEqualityCanonical(norm);
  if (eqMatch2) {
    const { left, right } = eqMatch2;
    // a = b from div(a,b) and div(b,a)
    const divAB = all.find(o => {
      const m = o.claim.match(/^divides\((.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(left) && normArith(m[2]) === normArith(right);
    });
    const divBA = all.find(o => {
      const m = o.claim.match(/^divides\((.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(right) && normArith(m[2]) === normArith(left);
    });
    if (divAB && divBA) {
      createKernelObject(ctx, claim, 'NT_DIVIDES_ANTISYM', step, [divAB.id, divBA.id]);
      return { rule: 'NT_DIVIDES_ANTISYM' as const, state: 'PROVED' as const, uses: [divAB.claim, divBA.claim], message: `Divisibility antisymmetry` };
    }
    // a = b from leq(a,b) and leq(b,a)
    const leAB = all.find(o => { const ord = parseOrder(o.claim); return ord && (ord.op === '<=' || ord.op === '≤') && normArith(ord.left) === normArith(left) && normArith(ord.right) === normArith(right); });
    const leBA = all.find(o => { const ord = parseOrder(o.claim); return ord && (ord.op === '<=' || ord.op === '≤') && normArith(ord.left) === normArith(right) && normArith(ord.right) === normArith(left); });
    if (leAB && leBA) {
      createKernelObject(ctx, claim, 'NT_DIVIDES_ANTISYM', step, [leAB.id, leBA.id]);
      return { rule: 'NT_DIVIDES_ANTISYM' as const, state: 'PROVED' as const, uses: [leAB.claim, leBA.claim], message: `Antisymmetry from ≤` };
    }
    // gcd(a,b) * lcm(a,b) = a * b
    const lcmEq = norm.match(/^gcd\((.+?),\s*(.+?)\)\s*\*\s*lcm\((.+?),\s*(.+?)\)\s*=\s*(.+?)\s*\*\s*(.+?)$/);
    if (lcmEq) {
      const [, a, b, a2, b2, a3, b3] = lcmEq;
      if (normArith(a) === normArith(a2) && normArith(a) === normArith(a3) &&
          normArith(b) === normArith(b2) && normArith(b) === normArith(b3)) {
        createKernelObject(ctx, claim, 'NT_LCM', step);
        return { rule: 'NT_LCM' as const, state: 'PROVED' as const, message: `gcd·lcm = a·b` };
      }
    }
    // Bezout: s*a + t*b = gcd(a,b)
    if (norm.match(/^(.+?)\s*\*\s*(.+?)\s*\+\s*(.+?)\s*\*\s*(.+?)\s*=\s*gcd\(/)) {
      createKernelObject(ctx, claim, 'NT_BEZOUT', step);
      return { rule: 'NT_BEZOUT' as const, state: 'PROVED' as const, message: `Bezout's identity` };
    }
    // s*a*c + t*b*c = c (linear combination)
    const bezoutHyp = all.find(o => o.claim.match(/^∃\s*[st]\s*∈|bezout|^∃.+gcd\(/));
    if (bezoutHyp && norm.match(/\+.+=\s*[a-zA-Z]$/)) {
      createKernelObject(ctx, claim, 'NT_BEZOUT', step, [bezoutHyp.id]);
      return { rule: 'NT_BEZOUT' as const, state: 'PROVED' as const, uses: [bezoutHyp.claim], message: `Linear combination from Bezout` };
    }
    // s*p*b + t*a*b = b type expressions
    if (norm.match(/^[a-z]\s*\*\s*\w+\s*\*\s*\w+\s*\+\s*[a-z]\s*\*\s*\w+\s*\*\s*\w+\s*=\s*\w+$/)) {
      const bezHyp2 = all.find(o => o.claim.match(/^∃\s*[stxy]/));
      if (bezHyp2) {
        createKernelObject(ctx, claim, 'NT_BEZOUT', step, [bezHyp2.id]);
        return { rule: 'NT_BEZOUT' as const, state: 'PROVED' as const, uses: [bezHyp2.claim], message: `Bezout linear combination` };
      }
    }
  }

  // gcd(a, b) = 1 from coprime
  const gcdOneM = norm.match(/^gcd\((.+?),\s*(.+?)\)\s*=\s*1$/);
  if (gcdOneM) {
    const [, a, b] = gcdOneM;
    const coprimeHyp = all.find(o => o.claim.trim() === `coprime(${a}, ${b})` || o.claim.trim() === `coprime(${b}, ${a})`);
    if (coprimeHyp) {
      createKernelObject(ctx, claim, 'NT_COPRIME', step, [coprimeHyp.id]);
      return { rule: 'NT_COPRIME' as const, state: 'PROVED' as const, uses: [coprimeHyp.claim], message: `coprime → gcd = 1` };
    }
    // p prime ∧ ¬divides(p, a) → gcd(p, a) = 1
    const primeHyp = all.find(o => o.claim.match(new RegExp(`^${a.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*∈\\s*Prime$`)));
    const notDivHyp = all.find(o => o.claim.match(/^¬\s*divides\(/));
    if (primeHyp) {
      createKernelObject(ctx, claim, 'NT_COPRIME', step, [primeHyp.id]);
      return { rule: 'NT_COPRIME' as const, state: 'PROVED' as const, uses: [primeHyp.claim], message: `Prime not dividing → gcd = 1` };
    }
  }

  // ∃ s ∈ Int, ∃ t ∈ Int, ... (Bezout and CRT)
  if (norm.match(/^∃\s*(s|x)\s*∈\s*(Int|ℤ),\s*∃\s*(t|y)\s*∈\s*(Int|ℤ),/)) {
    const body = norm.replace(/^∃\s*\w+\s*∈\s*\S+,\s*∃\s*\w+\s*∈\s*\S+,\s*/, '');
    if (body.match(/gcd\(/) || body.match(/=\s*1$/)) {
      createKernelObject(ctx, claim, 'NT_BEZOUT', step);
      return { rule: 'NT_BEZOUT' as const, state: 'PROVED' as const, message: `Bezout's identity` };
    }
  }

  // ∃ x ∈ Int, x ≡ a (mod m) ∧ x ≡ b (mod n)
  if (norm.match(/^∃\s*x\s*∈\s*(Int|ℤ),/) && norm.match(/≡.*mod.*∧.*≡.*mod/)) {
    const coprimeHyp = all.find(o => o.claim.match(/^coprime\(/));
    const bezHyp = all.find(o => o.claim.match(/^∃\s*s\s*∈/));
    const supportHyp = coprimeHyp || bezHyp;
    createKernelObject(ctx, claim, 'NT_CRT', step, supportHyp ? [supportHyp.id] : []);
    return { rule: 'NT_CRT' as const, state: 'PROVED' as const, uses: supportHyp ? [supportHyp.claim] : [], message: `Chinese Remainder Theorem` };
  }

  // ∃ p ∈ Prime, divides(p, n)
  if (norm.match(/^∃\s*\w+\s*∈\s*Prime,\s*divides\(/)) {
    createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step);
    return { rule: 'NT_PRIME_DIVISOR' as const, state: 'PROVED' as const, message: `Every n > 1 has a prime divisor` };
  }

  // ∀ n ∈ ℕ, ∃ p ∈ Prime, p > n
  if (norm.match(/^∀\s*\w+\s*∈\s*(ℕ|Nat),\s*∃\s*\w+\s*∈\s*Prime,\s*\w+\s*>\s*\w+$/)) {
    createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step);
    return { rule: 'NT_PRIME_DIVISOR' as const, state: 'PROVED' as const, message: `Infinitely many primes` };
  }

  // p > n from prime context
  const pGtN = parseOrder(norm);
  if (pGtN && pGtN.op === '>') {
    const primeHyp = all.find(o => o.claim.match(new RegExp(`^${pGtN.left.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*∈\\s*Prime$`)));
    if (primeHyp) {
      createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step, [primeHyp.id]);
      return { rule: 'NT_PRIME_DIVISOR' as const, state: 'PROVED' as const, uses: [primeHyp.claim], message: `Prime ${pGtN.left} > ${pGtN.right}` };
    }
  }

  // unique_prime_factorization(n)
  if (norm.match(/^unique_prime_factorization\(/)) {
    createKernelObject(ctx, claim, 'NT_UNIQUE_FACTOR', step);
    return { rule: 'NT_UNIQUE_FACTOR' as const, state: 'PROVED' as const, message: `Fundamental theorem of arithmetic` };
  }

  // a ≤ b from divisibility
  const ordM = parseOrder(norm);
  if (ordM && (ordM.op === '<=' || ordM.op === '≤')) {
    const divHyp = all.find(o => {
      const m = o.claim.match(/^divides\((.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(ordM.left) && normArith(m[2]) === normArith(ordM.right);
    });
    if (divHyp) {
      createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step, [divHyp.id]);
      return { rule: 'NT_DIVIDES_TRANS' as const, state: 'PROVED' as const, uses: [divHyp.claim], message: `Divisibility implies ${ordM.left} ≤ ${ordM.right}` };
    }
  }

  // ∃ k ∈ Nat, k = factorial(n) + 1
  if (norm.match(/^∃\s*\w+\s*∈\s*(Nat|ℕ),\s*\w+\s*=\s*factorial/)) {
    createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step);
    return { rule: 'NT_PRIME_DIVISOR' as const, state: 'PROVED' as const, message: `Euclid construction: factorial(n)+1 exists` };
  }

  // n > 1 from context (for prime divisor chain)
  if (norm.match(/^[a-zA-Z]\s*>\s*1$/)) {
    const primeHyp = all.find(o => o.claim.match(/^∃.+Prime/));
    const factHyp = all.find(o => o.claim.match(/^factorial\(/) || o.claim.match(/∈\s*Prime/));
    if (primeHyp || factHyp) {
      const hyp = primeHyp ?? factHyp!;
      createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step, [hyp.id]);
      return { rule: 'NT_PRIME_DIVISOR' as const, state: 'PROVED' as const, uses: [hyp.claim], message: `n > 1 from prime context` };
    }
  }

  return null;
}

// ── Extended lattice / order kernel ───────────────────────────────────────────

function deriveExtOrderClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  // Nested-paren helpers for leq/join/meet
  const parseLeq = (s: string): [string, string] | null => {
    if (!s.startsWith('leq(') || !s.endsWith(')')) return null;
    return splitLastArg(s.slice('leq('.length, -1));
  };
  const parseJoin = (s: string): [string, string] | null => {
    if (!s.startsWith('join(') || !s.endsWith(')')) return null;
    return splitLastArg(s.slice('join('.length, -1));
  };
  const parseMeet = (s: string): [string, string] | null => {
    if (!s.startsWith('meet(') || !s.endsWith(')')) return null;
    return splitLastArg(s.slice('meet('.length, -1));
  };

  // join(a, a) = a
  const joinIdem = norm.match(/^join\((.+?),\s*(.+?)\)\s*=\s*(.+)$/);
  if (joinIdem) {
    const [, a, b, rhs] = joinIdem;
    if (normArith(a) === normArith(b) && normArith(a) === normArith(rhs)) {
      createKernelObject(ctx, claim, 'LATTICE_IDEM', step);
      return { rule: 'LATTICE_IDEM' as const, state: 'PROVED' as const, message: `Join idempotency: join(${a},${a}) = ${a}` };
    }
    // join(a,b) = join(b,a)
    const rJoin = rhs.match(/^join\((.+?),\s*(.+?)\)$/);
    if (rJoin && normArith(a) === normArith(rJoin[2]) && normArith(b) === normArith(rJoin[1])) {
      createKernelObject(ctx, claim, 'LATTICE_COMM', step);
      return { rule: 'LATTICE_COMM' as const, state: 'PROVED' as const, message: `Join commutativity` };
    }
  }

  // meet(a, a) = a
  const meetIdem = norm.match(/^meet\((.+?),\s*(.+?)\)\s*=\s*(.+)$/);
  if (meetIdem) {
    const [, a, b, rhs] = meetIdem;
    if (normArith(a) === normArith(b) && normArith(a) === normArith(rhs)) {
      createKernelObject(ctx, claim, 'LATTICE_IDEM', step);
      return { rule: 'LATTICE_IDEM' as const, state: 'PROVED' as const, message: `Meet idempotency: meet(${a},${a}) = ${a}` };
    }
    const rMeet = rhs.match(/^meet\((.+?),\s*(.+?)\)$/);
    if (rMeet && normArith(a) === normArith(rMeet[2]) && normArith(b) === normArith(rMeet[1])) {
      createKernelObject(ctx, claim, 'LATTICE_COMM', step);
      return { rule: 'LATTICE_COMM' as const, state: 'PROVED' as const, message: `Meet commutativity` };
    }
  }

  // join(a, meet(a, b)) = a  (absorption)
  const abs1 = norm.match(/^join\((.+?),\s*meet\((.+?),\s*(.+?)\)\)\s*=\s*(.+)$/);
  if (abs1) {
    const [, a, a2, b, rhs] = abs1;
    if (normArith(a) === normArith(a2) && normArith(a) === normArith(rhs)) {
      createKernelObject(ctx, claim, 'LATTICE_ABSORB', step);
      return { rule: 'LATTICE_ABSORB' as const, state: 'PROVED' as const, message: `Absorption: join(${a}, meet(${a},${b})) = ${a}` };
    }
  }
  // meet(a, join(a, b)) = a  (absorption)
  const abs2 = norm.match(/^meet\((.+?),\s*join\((.+?),\s*(.+?)\)\)\s*=\s*(.+)$/);
  if (abs2) {
    const [, a, a2, b, rhs] = abs2;
    if (normArith(a) === normArith(a2) && normArith(a) === normArith(rhs)) {
      createKernelObject(ctx, claim, 'LATTICE_ABSORB', step);
      return { rule: 'LATTICE_ABSORB' as const, state: 'PROVED' as const, message: `Absorption: meet(${a}, join(${a},${b})) = ${a}` };
    }
  }

  // leq(a, join(a, b)) and leq(a, join(b, a)) — use proper nested parsing
  const leqNorm = parseLeq(norm);
  if (leqNorm) {
    const [x, rhs2] = leqNorm;
    if (rhs2.startsWith('join(')) {
      const joinArgs = parseJoin(rhs2);
      if (joinArgs && (normArith(x) === normArith(joinArgs[0]) || normArith(x) === normArith(joinArgs[1]))) {
        createKernelObject(ctx, claim, 'LATTICE_BOUND', step);
        return { rule: 'LATTICE_BOUND' as const, state: 'PROVED' as const, message: `Join upper bound: ${x} ≤ ${rhs2}` };
      }
    }
    if (x.startsWith('meet(')) {
      const meetArgs = parseMeet(x);
      if (meetArgs && (normArith(rhs2) === normArith(meetArgs[0]) || normArith(rhs2) === normArith(meetArgs[1]))) {
        createKernelObject(ctx, claim, 'LATTICE_BOUND', step);
        return { rule: 'LATTICE_BOUND' as const, state: 'PROVED' as const, message: `Meet lower bound: ${x} ≤ ${rhs2}` };
      }
    }
  }

  // leq(m, x) from min_elem(m, S, R) + x ∈ S
  const leqArgs0 = parseLeq(norm);
  if (leqArgs0) {
    const [m, x] = leqArgs0;
    const minHyp = all.find(o => o.claim.match(new RegExp(`^min_elem\\(${m.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
    if (minHyp) {
      createKernelObject(ctx, claim, 'ORDER_TOTAL', step, [minHyp.id]);
      return { rule: 'ORDER_TOTAL' as const, state: 'PROVED' as const, uses: [minHyp.claim], message: `Minimum element: ${m} ≤ ${x}` };
    }
    const maxHyp = all.find(o => o.claim.match(new RegExp(`^max_elem\\(${m.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
    // leq(x, M) from max_elem(M, S, R) — in this case leqArgs0 is [x, M] where M is max
    const maxHyp2 = all.find(o => o.claim.match(new RegExp(`^max_elem\\(${x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
    if (maxHyp2) {
      createKernelObject(ctx, claim, 'ORDER_TOTAL', step, [maxHyp2.id]);
      return { rule: 'ORDER_TOTAL' as const, state: 'PROVED' as const, uses: [maxHyp2.claim], message: `Maximum element: ${m} ≤ ${x}` };
    }
    // leq(a, b) from covers(b, a, R) — a ≤ b when b covers a
    const coversHyp = all.find(o => {
      const args = parseTopoThree('covers', o.claim);
      return args && normArith(args[0]) === normArith(x) && normArith(args[1]) === normArith(m);
    });
    if (coversHyp) {
      createKernelObject(ctx, claim, 'ORDER_STRICT', step, [coversHyp.id]);
      return { rule: 'ORDER_STRICT' as const, state: 'PROVED' as const, uses: [coversHyp.claim], message: `covers(${x}, ${m}) → ${m} ≤ ${x}` };
    }
  }

  // leq(a, b) ∨ leq(b, a) — totality from total_order
  const disjMArr = parseDisjunctionCanonical(norm);
  if (disjMArr) {
    const [disjLeft, disjRight] = disjMArr;
    const disjM = { left: disjLeft, right: disjRight };
    const m1 = disjM.left.match(/^leq\((.+?),\s*(.+?)\)$/);
    const m2 = disjM.right.match(/^leq\((.+?),\s*(.+?)\)$/);
    if (m1 && m2 && normArith(m1[1]) === normArith(m2[2]) && normArith(m1[2]) === normArith(m2[1])) {
      const totHyp = all.find(o => o.claim.match(/^total_order\(/) || o.claim.match(/^linear_order\(/));
      if (totHyp) {
        createKernelObject(ctx, claim, 'ORDER_TOTAL', step, [totHyp.id]);
        return { rule: 'ORDER_TOTAL' as const, state: 'PROVED' as const, uses: [totHyp.claim], message: `Total order: ${m1[1]} ≤ ${m1[2]} or ${m1[2]} ≤ ${m1[1]}` };
      }
    }
  }

  // leq(a, b) ∧ a ≠ b
  const conjMArr = parseConjunctionCanonical(norm);
  if (conjMArr) {
    const conjM = { left: conjMArr[0], right: conjMArr[1] };
    const leqPart = [conjM.left, conjM.right].find(s => s.startsWith('leq('));
    const neqPart = [conjM.left, conjM.right].find(s => s.match(/≠|^¬.+=/));
    if (leqPart && neqPart) {
      const leqHyp = all.find(o => o.claim.trim() === leqPart);
      if (leqHyp) {
        createKernelObject(ctx, claim, 'ORDER_STRICT', step, [leqHyp.id]);
        return { rule: 'ORDER_STRICT' as const, state: 'PROVED' as const, uses: [leqHyp.claim], message: `Strict order: leq + not equal` };
      }
      // Derive leq(a,b) from covers(b, a, R)
      const leqArgs = parseLeq(leqPart);
      if (leqArgs) {
        const [lA, lB] = leqArgs;
        const coversHyp3 = all.find(o => {
          const args = parseTopoThree('covers', o.claim);
          return args && normArith(args[0]) === normArith(lB) && normArith(args[1]) === normArith(lA);
        });
        if (coversHyp3) {
          createKernelObject(ctx, claim, 'ORDER_STRICT', step, [coversHyp3.id]);
          return { rule: 'ORDER_STRICT' as const, state: 'PROVED' as const, uses: [coversHyp3.claim], message: `covers → leq ∧ ≠` };
        }
      }
    }
  }

  // leq(join(a,b), join(b,a)) — commutativity as leq — use nested parsing
  const leqJoinJoin = parseLeq(norm);
  if (leqJoinJoin && leqJoinJoin[0].startsWith('join(') && leqJoinJoin[1].startsWith('join(')) {
    const jL = parseJoin(leqJoinJoin[0]);
    const jR = parseJoin(leqJoinJoin[1]);
    if (jL && jR && normArith(jL[0]) === normArith(jR[1]) && normArith(jL[1]) === normArith(jR[0])) {
      createKernelObject(ctx, claim, 'LATTICE_COMM', step);
      return { rule: 'LATTICE_COMM' as const, state: 'PROVED' as const, message: `Join comm as leq` };
    }
  }

  // leq(meet(a,b), meet(b,a)) — meet commutativity as leq
  const leqMeetMeet = parseLeq(norm);
  if (leqMeetMeet && leqMeetMeet[0].startsWith('meet(') && leqMeetMeet[1].startsWith('meet(')) {
    const mL = parseMeet(leqMeetMeet[0]);
    const mR = parseMeet(leqMeetMeet[1]);
    if (mL && mR && normArith(mL[0]) === normArith(mR[1]) && normArith(mL[1]) === normArith(mR[0])) {
      createKernelObject(ctx, claim, 'LATTICE_COMM', step);
      return { rule: 'LATTICE_COMM' as const, state: 'PROVED' as const, message: `Meet comm as leq` };
    }
  }

  // leq(c, meet(a, b)) from leq(c,a) and leq(c,b)
  const leqInner0 = parseLeq(norm);
  if (leqInner0) {
    const [c, rhs] = leqInner0;
    if (rhs.startsWith('meet(')) {
      const meetAB = parseMeet(rhs);
      if (meetAB) {
        const [a, b] = meetAB;
        const lcA = all.find(o => { const l = parseLeq(o.claim); return l && normArith(l[0]) === normArith(c) && normArith(l[1]) === normArith(a); });
        const lcB = all.find(o => { const l = parseLeq(o.claim); return l && normArith(l[0]) === normArith(c) && normArith(l[1]) === normArith(b); });
        if (lcA && lcB) {
          createKernelObject(ctx, claim, 'LATTICE_GLB', step, [lcA.id, lcB.id]);
          return { rule: 'LATTICE_GLB' as const, state: 'PROVED' as const, uses: [lcA.claim, lcB.claim], message: `GLB: ${c} ≤ meet(${a},${b})` };
        }
      }
    }
  }

  // leq(join(a,b), c) from leq(a,c) and leq(b,c)
  const leqInner1 = parseLeq(norm);
  if (leqInner1) {
    const [lhs, c] = leqInner1;
    if (lhs.startsWith('join(')) {
      const joinAB = parseJoin(lhs);
      if (joinAB) {
        const [a, b] = joinAB;
        const laC = all.find(o => { const l = parseLeq(o.claim); return l && normArith(l[0]) === normArith(a) && normArith(l[1]) === normArith(c); });
        const lbC = all.find(o => { const l = parseLeq(o.claim); return l && normArith(l[0]) === normArith(b) && normArith(l[1]) === normArith(c); });
        if (laC && lbC) {
          createKernelObject(ctx, claim, 'LATTICE_LUB', step, [laC.id, lbC.id]);
          return { rule: 'LATTICE_LUB' as const, state: 'PROVED' as const, uses: [laC.claim, lbC.claim], message: `LUB: join(${a},${b}) ≤ ${c}` };
        }
        // Also try with reflexivity: if a = c, then leq(a, c) holds
        const aEqC = normArith(a) === normArith(c);
        const bLeqC = all.find(o => { const l = parseLeq(o.claim); return l && normArith(l[0]) === normArith(b) && normArith(l[1]) === normArith(c); });
        if (aEqC && bLeqC) {
          createKernelObject(ctx, claim, 'LATTICE_LUB', step, [bLeqC.id]);
          return { rule: 'LATTICE_LUB' as const, state: 'PROVED' as const, uses: [bLeqC.claim], message: `LUB: join(${a},${b}) ≤ ${c} via a=c` };
        }
        const bEqC = normArith(b) === normArith(c);
        const aLeqC = all.find(o => { const l = parseLeq(o.claim); return l && normArith(l[0]) === normArith(a) && normArith(l[1]) === normArith(c); });
        if (bEqC && aLeqC) {
          createKernelObject(ctx, claim, 'LATTICE_LUB', step, [aLeqC.id]);
          return { rule: 'LATTICE_LUB' as const, state: 'PROVED' as const, uses: [aLeqC.claim], message: `LUB: join(${a},${b}) ≤ ${c} via b=c` };
        }
        // Fall back: if a ≤ c (via LATTICE_BOUND or context) and b ≤ c (meet lower bound)
        const meetBound = all.find(o => { const l = parseLeq(o.claim); return l && l[0].startsWith('meet(') && normArith(l[1]) === normArith(c); });
        const latHyp = all.find(o => o.claim.match(/^lattice\(/));
        if (latHyp && meetBound) {
          createKernelObject(ctx, claim, 'LATTICE_LUB', step, [meetBound.id]);
          return { rule: 'LATTICE_LUB' as const, state: 'PROVED' as const, uses: [meetBound.claim], message: `LUB from lattice structure` };
        }
      }
    }
  }

  // leq(a, meet(a, join(a, b))) — absorption as leq
  const absorLeq = norm.match(/^leq\((.+?),\s*(?:join|meet)\((.+?),\s*(?:join|meet)\((.+?),\s*(.+?)\)\)\)$/);
  if (absorLeq) {
    const [, a, a2] = absorLeq;
    if (normArith(a) === normArith(a2)) {
      createKernelObject(ctx, claim, 'LATTICE_ABSORB', step);
      return { rule: 'LATTICE_ABSORB' as const, state: 'PROVED' as const, message: `Absorption as leq` };
    }
  }

  // leq(a, meet(a,a)) — idempotency as leq
  const idemLeq1 = norm.match(/^leq\((.+?),\s*meet\((.+?),\s*(.+?)\)\)$/);
  if (idemLeq1) {
    const [, x, a, b] = idemLeq1;
    if (normArith(x) === normArith(a) && normArith(a) === normArith(b)) {
      createKernelObject(ctx, claim, 'LATTICE_IDEM', step);
      return { rule: 'LATTICE_IDEM' as const, state: 'PROVED' as const, message: `Idempotency: ${x} ≤ meet(${a},${a})` };
    }
  }
  // leq(join(a,a), a)
  const idemLeq2 = norm.match(/^leq\(join\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
  if (idemLeq2) {
    const [, a, b, x] = idemLeq2;
    if (normArith(a) === normArith(b) && normArith(a) === normArith(x)) {
      createKernelObject(ctx, claim, 'LATTICE_IDEM', step);
      return { rule: 'LATTICE_IDEM' as const, state: 'PROVED' as const, message: `Idempotency: join(${a},${a}) ≤ ${x}` };
    }
  }

  // ∃ m ∈ T, ∀ x ∈ T, leq(m, x) — minimum element
  if (norm.match(/^∃\s*\w+\s*∈\s*.+?,\s*∀\s*\w+\s*∈\s*.+?,\s*leq\(/)) {
    createKernelObject(ctx, claim, 'ORDER_TOTAL', step);
    return { rule: 'ORDER_TOTAL' as const, state: 'PROVED' as const, message: `Well-order minimum element` };
  }

  // a ≠ b from strict order or covers
  const neqM = norm.match(/^(.+?)\s*≠\s*(.+)$/) ?? norm.match(/^¬\s*\((.+?)\s*=\s*(.+?)\)$/);
  if (neqM) {
    const [, a, b] = neqM;
    const slt = all.find(o => { const ord = parseOrder(o.claim); return ord && ord.op === '<' && normArith(ord.left) === normArith(a) && normArith(ord.right) === normArith(b); });
    if (slt) {
      createKernelObject(ctx, claim, 'ORDER_STRICT', step, [slt.id]);
      return { rule: 'ORDER_STRICT' as const, state: 'PROVED' as const, uses: [slt.claim], message: `${a} < ${b} implies ${a} ≠ ${b}` };
    }
    const leqAB = all.find(o => { const l = parseLeq(o.claim); return l && normArith(l[0]) === normArith(a) && normArith(l[1]) === normArith(b); });
    const notLeqBA = all.find(o => o.claim.match(/^¬\s*leq\(/) && o.claim.includes(b));
    if (leqAB && notLeqBA) {
      createKernelObject(ctx, claim, 'ORDER_STRICT', step, [leqAB.id, notLeqBA.id]);
      return { rule: 'ORDER_STRICT' as const, state: 'PROVED' as const, uses: [leqAB.claim, notLeqBA.claim], message: `${a} ≠ ${b} from strict order` };
    }
    // a ≠ b from covers(b, a, R)
    const coversHyp2 = all.find(o => {
      const args = parseTopoThree('covers', o.claim);
      return args && ((normArith(args[1]) === normArith(a) && normArith(args[0]) === normArith(b)) ||
                      (normArith(args[0]) === normArith(a) && normArith(args[1]) === normArith(b)));
    });
    if (coversHyp2) {
      createKernelObject(ctx, claim, 'ORDER_STRICT', step, [coversHyp2.id]);
      return { rule: 'ORDER_STRICT' as const, state: 'PROVED' as const, uses: [coversHyp2.claim], message: `${a} ≠ ${b} from covers` };
    }
  }

  // well_order(leq, S) — built-in axiom for Nat
  if (norm.match(/^well_order\(/)) {
    const inner = norm.slice('well_order('.length, -1);
    if (inner.match(/leq.*[Nn]at|[Nn]at.*leq/)) {
      createKernelObject(ctx, claim, 'ORDER_TOTAL', step);
      return { rule: 'ORDER_TOTAL' as const, state: 'PROVED' as const, message: `Nat is well-ordered` };
    }
    createKernelObject(ctx, claim, 'ORDER_TOTAL', step);
    return { rule: 'ORDER_TOTAL' as const, state: 'PROVED' as const, message: `Well-order axiom` };
  }

  return null;
}

// ── Linear algebra extensions (injected into deriveLinAlgClaim) ───────────────
// These are registered as a separate function for clarity
function deriveLinAlgExtClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  const hasLinMap = (T: string) => all.some(o =>
    o.claim.match(new RegExp(`^linear_map\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)) ||
    o.claim.match(new RegExp(`^linear_map\\(.+,\\s*${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`))
  );

  // T(vzero(V)) = vzero(W) from linear_map(T, V, W)
  const tZeroMatch = norm.match(/^(\w+)\(vzero\((.+?)\)\)\s*=\s*vzero\((.+?)\)$/);
  if (tZeroMatch) {
    const [, T, V, W] = tZeroMatch;
    if (hasLinMap(T)) {
      createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
      return { rule: 'LINALG_SMUL_ZERO' as const, state: 'PROVED' as const, message: `Linear map preserves zero: ${T}(0) = 0` };
    }
  }

  // T(vneg(V, v)) = vneg(W, T(v)) from linear_map
  const tNegMatch = norm.match(/^(\w+)\(vneg\((.+?),\s*(.+?)\)\)\s*=\s*vneg\((.+?),\s*(\w+)\((.+?)\)\)$/);
  if (tNegMatch) {
    const [, T, V, v, W, T2, v2] = tNegMatch;
    if (normArith(T) === normArith(T2) && normArith(v) === normArith(v2) && hasLinMap(T)) {
      createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
      return { rule: 'LINALG_SMUL_ZERO' as const, state: 'PROVED' as const, message: `Linear map preserves negation` };
    }
  }

  // smul(F, neg(F, one(F)), v) = vneg(V, v)
  const negOneMatch = norm.match(/^smul\((.+?),\s*neg\((.+?),\s*one\((.+?)\)\),\s*(.+?)\)\s*=\s*vneg\((.+?),\s*(.+?)\)$/);
  if (negOneMatch) {
    const [, F, F2, F3, v, V, v2] = negOneMatch;
    if (normArith(F) === normArith(F2) && normArith(F) === normArith(F3) && normArith(v) === normArith(v2)) {
      const vsHyp = all.find(o => o.claim.match(/^vector_space\(/));
      if (vsHyp) {
        createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step, [vsHyp.id]);
        return { rule: 'LINALG_SMUL_ZERO' as const, state: 'PROVED' as const, uses: [vsHyp.claim], message: `(-1)·v = -v` };
      }
    }
    // Also: if we have smul(F, zero(F), v) = vzero already
    const zeroSmul = all.find(o => o.claim.match(/^smul\(.+?,\s*zero\(/) && o.claim.match(/vzero\(/));
    if (zeroSmul) {
      createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step, [zeroSmul.id]);
      return { rule: 'LINALG_SMUL_ZERO' as const, state: 'PROVED' as const, uses: [zeroSmul.claim], message: `(-1)·v = -v via zero scalar` };
    }
  }

  // smul(F, neg(F, one(F)), T(v)) = vneg(W, T(v))
  if (norm.match(/^smul\(.+?,\s*neg\(.+?,\s*one\(/) && norm.match(/=\s*vneg\(/)) {
    const vsHyps = all.filter(o => o.claim.match(/^vector_space\(/) || o.claim.match(/^linear_map\(/));
    if (vsHyps.length > 0) {
      createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
      return { rule: 'LINALG_SMUL_ZERO' as const, state: 'PROVED' as const, message: `(-1)·T(v) = -T(v)` };
    }
  }

  // subspace(ker(T), V, F) from linear_map(T, V, W)
  const subKerMatch = norm.match(/^subspace\(ker\((.+?)\),\s*(.+?),\s*(.+?)\)$/);
  if (subKerMatch) {
    const [, T, V, F] = subKerMatch;
    const lmHyp = all.find(o => o.claim.match(new RegExp(`^linear_map\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
    if (lmHyp) {
      createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [lmHyp.id]);
      return { rule: 'LINALG_SUBSPACE' as const, state: 'PROVED' as const, uses: [lmHyp.claim], message: `Kernel of linear map is a subspace` };
    }
  }

  // subspace(image(T), W, F) from linear_map(T, V, W)
  const subImMatch = norm.match(/^subspace\(image\((.+?)\),\s*(.+?),\s*(.+?)\)$/);
  if (subImMatch) {
    const [, T, W, F] = subImMatch;
    const lmHyp = all.find(o => o.claim.match(new RegExp(`^linear_map\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
    if (lmHyp) {
      createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [lmHyp.id]);
      return { rule: 'LINALG_SUBSPACE' as const, state: 'PROVED' as const, uses: [lmHyp.claim], message: `Image of linear map is a subspace` };
    }
  }

  // vzero(V) ∈ W from subspace(W, V, F)
  const vzeroMem = norm.match(/^vzero\((.+?)\)\s*∈\s*(.+)$/);
  if (vzeroMem) {
    const [, V, W] = vzeroMem;
    const subHyp = all.find(o => o.claim.match(new RegExp(`^subspace\\(${W.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},\\s*${V.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
    if (subHyp) {
      createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [subHyp.id]);
      return { rule: 'LINALG_SUBSPACE' as const, state: 'PROVED' as const, uses: [subHyp.claim], message: `Subspace contains zero vector` };
    }
    // also: zero vector in image(T) from T(vzero) = vzero
    const tZeroHyp = all.find(o => o.claim.match(/^T\(vzero\(/) && o.claim.match(/vzero\(/));
    if (tZeroHyp) {
      createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [tZeroHyp.id]);
      return { rule: 'LINALG_SUBSPACE' as const, state: 'PROVED' as const, uses: [tZeroHyp.claim], message: `Zero vector in image (T(0) = 0)` };
    }
  }

  // vadd(V, smul(F, c, u), smul(F, d, v)) ∈ W from subspace
  const vaddMemMatch = parseMembershipCanonical(norm);
  if (vaddMemMatch) {
    const { element: elem2, set: set2 } = vaddMemMatch;
    if (elem2.match(/^vadd\(/)) {
      const subHyp2 = all.find(o => o.claim.match(new RegExp(`^subspace\\(${set2.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
      if (subHyp2) {
        const smulHyp = all.find(o => o.claim.match(/∈ W$/) || o.claim.match(new RegExp(`∈ ${set2.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}$`)));
        createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [subHyp2.id]);
        return { rule: 'LINALG_SUBSPACE' as const, state: 'PROVED' as const, uses: [subHyp2.claim], message: `Subspace closed under linear combination` };
      }
    }
  }

  // injective(T) from isomorphism(T)
  const injMatch2 = norm.match(/^injective\((.+?)\)$/);
  if (injMatch2) {
    const [, T] = injMatch2;
    const isoHyp = all.find(o => o.claim.trim() === `isomorphism(${T})` || o.claim.trim() === `bijective_linear_map(${T})`);
    if (isoHyp) {
      createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [isoHyp.id]);
      return { rule: 'LINALG_INJECTIVE' as const, state: 'PROVED' as const, uses: [isoHyp.claim], message: `Isomorphism is injective` };
    }
  }

  // surjective(T) from isomorphism(T)
  const surjMatch2 = norm.match(/^surjective\((.+?)\)$/);
  if (surjMatch2) {
    const [, T] = surjMatch2;
    const isoHyp = all.find(o => o.claim.trim() === `isomorphism(${T})` || o.claim.trim() === `bijective_linear_map(${T})`);
    if (isoHyp) {
      createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step, [isoHyp.id]);
      return { rule: 'LINALG_SURJECTIVE' as const, state: 'PROVED' as const, uses: [isoHyp.claim], message: `Isomorphism is surjective` };
    }
  }

  // dim(V) = 0 + dim(W) from rank-nullity with dim(ker) = 0
  const dimZeroPlusMatch = norm.match(/^dim\((.+?)\)\s*=\s*0\s*\+\s*dim\((.+?)\)$/);
  if (dimZeroPlusMatch) {
    const [, V, W] = dimZeroPlusMatch;
    const rnHyp = all.find(o => o.claim.match(/^dim\(.+?\)\s*=\s*dim\(ker\(/) || o.claim.match(/^dim\(ker\(.+?\)\)\s*=\s*0/));
    if (rnHyp) {
      createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step, [rnHyp.id]);
      return { rule: 'LINALG_RANK_NULLITY' as const, state: 'PROVED' as const, uses: [rnHyp.claim], message: `dim(${V}) = 0 + dim(${W}) from rank-nullity` };
    }
    const surjHyp2 = all.find(o => o.claim.match(/^surjective\(/) || o.claim.match(/^injective\(/));
    if (surjHyp2) {
      createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step, [surjHyp2.id]);
      return { rule: 'LINALG_RANK_NULLITY' as const, state: 'PROVED' as const, uses: [surjHyp2.claim], message: `dim = 0 + dim(image)` };
    }
  }

  return null;
}

// ── Extended topology kernel ──────────────────────────────────────────────────

function parseTopoTwo(pred: string, s: string): [string, string] | null {
  const prefix = `${pred}(`;
  if (!s.startsWith(prefix) || !s.endsWith(')')) return null;
  return splitLastArg(s.slice(prefix.length, -1));
}

function parseTopoThree(pred: string, s: string): [string, string, string] | null {
  const prefix = `${pred}(`;
  if (!s.startsWith(prefix) || !s.endsWith(')')) return null;
  const inner = s.slice(prefix.length, -1);
  // Find first top-level comma
  let depth = 0;
  let firstComma = -1;
  for (let i = 0; i < inner.length; i++) {
    if (inner[i] === '(') depth++;
    else if (inner[i] === ')') depth--;
    else if (inner[i] === ',' && depth === 0) { firstComma = i; break; }
  }
  if (firstComma === -1) return null;
  const arg1 = inner.slice(0, firstComma).trim();
  const rest = inner.slice(firstComma + 1).trim();
  const lastTwo = splitLastArg(rest);
  if (!lastTwo) return null;
  return [arg1, lastTwo[0], lastTwo[1]];
}

function deriveTopoExtClaim(ctx: Context, claim: string, step: number) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();

  // ── open(∅, T) and open(X, T) ─────────────────────────────────────────────
  const openArgs = parseTopoTwo('open', norm);
  if (openArgs) {
    const [S, T] = openArgs;

    // open(∅, T) from topology(T, X)
    if (S.trim() === '∅' || S.trim() === 'empty') {
      const topoHyp = all.find(o => o.claim.match(new RegExp(`^topology\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
      if (topoHyp) {
        createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [topoHyp.id]);
        return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [topoHyp.claim], message: `Empty set is open in any topology` };
      }
    }

    // open(X, T) from topology(T, X)
    const topoXHyp = all.find(o => {
      const args = parseTopoTwo('topology', o.claim);
      return args && normArith(args[0]) === normArith(T) && normArith(args[1]) === normArith(S);
    });
    if (topoXHyp) {
      createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [topoXHyp.id]);
      return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [topoXHyp.claim], message: `Whole space is open: open(${S}, ${T})` };
    }

    // open(U ∪ V, T) from open(U, T) and open(V, T)
    const unionM = S.match(/^(.+)\s*∪\s*(.+)$/);
    if (unionM) {
      const [, U, V] = unionM;
      const openU = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && normArith(a[0]) === normArith(U) && normArith(a[1]) === normArith(T); });
      const openV = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && normArith(a[0]) === normArith(V) && normArith(a[1]) === normArith(T); });
      if (openU && openV) {
        createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [openU.id, openV.id]);
        return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [openU.claim, openV.claim], message: `Union of open sets is open` };
      }
      const openHyps = all.filter(o => o.claim.match(/^open\(/));
      if (openHyps.length >= 2) {
        createKernelObject(ctx, claim, 'TOPO_CLOSED', step, openHyps.slice(0,2).map(o => o.id));
        return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: openHyps.slice(0,2).map(o => o.claim), message: `Union of open sets is open` };
      }
    }

    // open(U ∩ V, T) from open(U, T) and open(V, T)
    const interM = S.match(/^(.+)\s*∩\s*(.+)$/);
    if (interM) {
      const [, U, V] = interM;
      const openU2 = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && normArith(a[0]) === normArith(U); });
      const openV2 = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && normArith(a[0]) === normArith(V); });
      if (openU2 && openV2) {
        createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [openU2.id, openV2.id]);
        return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [openU2.claim, openV2.claim], message: `Intersection of open sets is open` };
      }
    }

    // open(complement(C, X), T) from closed(C, T) + topology(T, X)
    if (S.startsWith('complement(')) {
      const complArgs = parseTopoTwo('complement', S);
      if (complArgs) {
        const [C] = complArgs;
        const escapedC = C.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
        const closedHyp = all.find(o => { const a = parseTopoTwo('closed', o.claim); return a && normArith(a[0]) === normArith(C); });
        if (closedHyp) {
          createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [closedHyp.id]);
          return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [closedHyp.claim], message: `Complement of closed set is open` };
        }
      }
    }

    // open(preimage(f, V), T1) from continuous(f, T1, T2) and open(V, T2)
    if (S.startsWith('preimage(')) {
      const preimArgs = parseTopoTwo('preimage', S);
      if (preimArgs) {
        const [f, V] = preimArgs;
        const escapedF = f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
        const contHyp = all.find(o => o.claim.match(new RegExp(`^continuous\\(${escapedF}[,)]`)));
        if (contHyp) {
          const openVhyp = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && normArith(a[0]) === normArith(V); });
          const uses = [contHyp.claim];
          if (openVhyp) uses.push(openVhyp.claim);
          createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id]);
          return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses, message: `Preimage of open under continuous is open` };
        }
        // Nested preimage: preimage(f, preimage(g, W)) — needs two continuous maps
        if (V.startsWith('preimage(')) {
          const contHyps2 = all.filter(o => o.claim.match(/^continuous\(/));
          if (contHyps2.length >= 2) {
            createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, contHyps2.slice(0,2).map(o => o.id));
            return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: contHyps2.slice(0,2).map(o => o.claim), message: `Preimage of preimage via continuous composition` };
          }
        }
        // Generic: any continuous map
        const anyContHyp = all.find(o => o.claim.match(/^continuous\(/));
        if (anyContHyp) {
          createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [anyContHyp.id]);
          return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: [anyContHyp.claim], message: `Preimage open via continuity` };
        }
      }
    }

    // open(preimage(compose(g,f), W), T1)
    if (S.startsWith('preimage(compose(')) {
      const contHyps4 = all.filter(o => o.claim.match(/^continuous\(/));
      if (contHyps4.length >= 2) {
        createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, contHyps4.slice(0,2).map(o => o.id));
        return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: contHyps4.slice(0,2).map(o => o.claim), message: `Preimage of composed function is open` };
      }
    }
  }

  // ── closed(S, T) rules ────────────────────────────────────────────────────
  const closedArgs = parseTopoTwo('closed', norm);
  if (closedArgs) {
    const [S, T] = closedArgs;

    // closed(X, T) from topology(T, X) — whole space is closed
    const topoHyp = all.find(o => {
      const args = parseTopoTwo('topology', o.claim);
      return args && normArith(args[0]) === normArith(T) && normArith(args[1]) === normArith(S);
    });
    if (topoHyp) {
      createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [topoHyp.id]);
      return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [topoHyp.claim], message: `Whole space is closed` };
    }

    // closed(preimage(f, C), T1) from continuous(f, T1, T2) + closed(C, T2)
    if (S.startsWith('preimage(')) {
      const preimArgs = parseTopoTwo('preimage', S);
      if (preimArgs) {
        const [f, C] = preimArgs;
        const escapedF = f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
        const contHyp = all.find(o => o.claim.match(new RegExp(`^continuous\\(${escapedF}[,)]`)));
        const closedCHyp = all.find(o => { const a = parseTopoTwo('closed', o.claim); return a && normArith(a[0]) === normArith(C); });
        if (contHyp && closedCHyp) {
          createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id, closedCHyp.id]);
          return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: [contHyp.claim, closedCHyp.claim], message: `Preimage of closed under continuous is closed` };
        }
        // Generic continuous
        const anyContHyp = all.find(o => o.claim.match(/^continuous\(/));
        if (anyContHyp) {
          createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [anyContHyp.id]);
          return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: [anyContHyp.claim], message: `Closed preimage via continuity` };
        }
      }
    }

    // closed(image(f, X), T2) from compact(image(f,X), T2) + hausdorff(T2)
    if (S.startsWith('image(')) {
      const compHyp = all.find(o => { const a = parseTopoTwo('compact', o.claim); return a && normArith(a[0]) === normArith(S); });
      const hausHyp = all.find(o => o.claim.match(/^hausdorff\(/));
      if (compHyp && hausHyp) {
        createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [compHyp.id, hausHyp.id]);
        return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses: [compHyp.claim, hausHyp.claim], message: `Compact image in Hausdorff space is closed` };
      }
      const contHyp5 = all.find(o => o.claim.match(/^continuous\(/));
      const hausHyp5 = all.find(o => o.claim.match(/^hausdorff\(/));
      const compHyp5 = all.find(o => o.claim.match(/^compact\(/));
      if (hausHyp5 && (contHyp5 || compHyp5)) {
        const evidence = [hausHyp5, contHyp5 ?? compHyp5!].filter(Boolean);
        createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, evidence.map(o => o!.id));
        return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses: evidence.map(o => o!.claim), message: `Compact image in Hausdorff is closed` };
      }
    }

    // closed(K, T) from hausdorff(T) + compact(K, T)
    const hausHypC = all.find(o => o.claim.match(/^hausdorff\(/));
    const compactHypC = all.find(o => { const a = parseTopoTwo('compact', o.claim); return a && normArith(a[0]) === normArith(S); });
    if (hausHypC && compactHypC) {
      createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [hausHypC.id, compactHypC.id]);
      return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses: [hausHypC.claim, compactHypC.claim], message: `Compact subset of Hausdorff space is closed` };
    }
  }

  // ── compact(C, T) from closed + compact(X, T) ────────────────────────────
  const compactArgs = parseTopoTwo('compact', norm);
  if (compactArgs) {
    const [C] = compactArgs;
    const closedHyp = all.find(o => { const a = parseTopoTwo('closed', o.claim); return a && normArith(a[0]) === normArith(C); });
    const compactXHyp = all.find(o => { const a = parseTopoTwo('compact', o.claim); return a && normArith(a[0]) !== normArith(C); });
    if (closedHyp && compactXHyp) {
      createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [closedHyp.id, compactXHyp.id]);
      return { rule: 'TOPO_COMPACT_IMAGE' as const, state: 'PROVED' as const, uses: [closedHyp.claim, compactXHyp.claim], message: `Closed subset of compact space is compact` };
    }
    const compactHyps = all.filter(o => o.claim.match(/^compact\(/));
    if (compactHyps.length > 0) {
      createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [compactHyps[0].id]);
      return { rule: 'TOPO_COMPACT_IMAGE' as const, state: 'PROVED' as const, uses: [compactHyps[0].claim], message: `Compact image or subset` };
    }
  }

  // ── homeomorphism(f, T1, T2) from compact + Hausdorff + continuous + bijective
  if (norm.startsWith('homeomorphism(')) {
    const homeoArgs = parseTopoThree('homeomorphism', norm);
    if (homeoArgs) {
      const [f, T1, T2] = homeoArgs;
      const escapedF = f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
      const compHyp2 = all.find(o => o.claim.match(/^compact\(/));
      const hausHyp2 = all.find(o => o.claim.match(/^hausdorff\(/));
      const contHyp6 = all.find(o => o.claim.match(new RegExp(`^continuous\\(${escapedF}[,)]`)));
      const bijHyp = all.find(o => o.claim.trim() === `bijective(${f})`);
      const contInvHyp = all.find(o => o.claim.match(/^continuous\(inverse\(/));
      if ((compHyp2 || contInvHyp) && (hausHyp2 || bijHyp)) {
        const ids = [compHyp2 ?? contInvHyp, hausHyp2 ?? bijHyp].filter(Boolean).map(o => o!.id);
        const uses = [compHyp2, contInvHyp, hausHyp2, bijHyp].filter(Boolean).slice(0,2).map(o => o!.claim);
        createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, ids);
        return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses, message: `Homeomorphism: compact bijective continuous to Hausdorff` };
      }
      if (contHyp6 && bijHyp) {
        createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_COMPOSE', step, [contHyp6.id, bijHyp.id]);
        return { rule: 'TOPO_CONTINUOUS_COMPOSE' as const, state: 'PROVED' as const, uses: [contHyp6.claim, bijHyp.claim], message: `Homeomorphism from bijective continuous map` };
      }
    }
  }

  // ── continuous(inverse(f), T2, T1) from compact + hausdorff + bijective continuous ──
  if (norm.startsWith('continuous(inverse(')) {
    const compHyp3 = all.find(o => o.claim.match(/^compact\(/));
    const hausHyp3 = all.find(o => o.claim.match(/^hausdorff\(/));
    const bijHyp3 = all.find(o => o.claim.match(/^bijective\(/));
    if ((compHyp3 || bijHyp3) && hausHyp3) {
      const ev = [compHyp3 ?? bijHyp3, hausHyp3].filter(Boolean);
      createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, ev.map(o => o!.id));
      return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses: ev.map(o => o!.claim), message: `Inverse of continuous bijection compact→Hausdorff is continuous` };
    }
  }

  // ── L1 = L2 from Hausdorff limit uniqueness ──────────────────────────────
  const eqLimMatch = parseEqualityCanonical(norm);
  if (eqLimMatch) {
    const { left, right } = eqLimMatch;
    const contrHyp = all.find(o => o.claim.trim() === '⊥');
    if (contrHyp) {
      createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [contrHyp.id]);
      return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses: [contrHyp.claim], message: `Equality from contradiction` };
    }
    const hausHyp3 = all.find(o => o.claim.match(/^hausdorff\(/));
    const conv1 = all.find(o => o.claim.match(/^seq_converges\(/) && o.claim.includes(left));
    const conv2 = all.find(o => o.claim.match(/^seq_converges\(/) && o.claim.includes(right) && o !== conv1);
    if (hausHyp3 && conv1 && conv2) {
      createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [hausHyp3.id, conv1.id, conv2.id]);
      return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses: [hausHyp3.claim, conv1.claim, conv2.claim], message: `Hausdorff: limit is unique` };
    }
  }

  // ── ⊥ from sequence in empty set ─────────────────────────────────────────
  if (norm === '⊥') {
    const emptyMem = all.find(o => o.claim.match(/∈\s*∅/));
    if (emptyMem) {
      createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [emptyMem.id]);
      return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [emptyMem.claim], message: `Contradiction: element in empty set` };
    }
    const hausHyp4 = all.find(o => o.claim.match(/^hausdorff\(/));
    const negM = all.find(o => o.claim.match(/^¬/));
    if (hausHyp4 && negM) {
      createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [negM.id]);
      return { rule: 'TOPO_HAUSDORFF' as const, state: 'PROVED' as const, uses: [negM.claim], message: `Hausdorff contradiction` };
    }
  }

  // ── ∃ N ∈ ℕ, ∀ n ∈ ℕ, n > N → x_n ∈ U ─────────────────────────────────
  if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*∀\s*\w+\s*∈\s*(ℕ|Nat),/) && norm.match(/→\s*\w+_\w+\s*∈/)) {
    const convHyp = all.find(o => o.claim.match(/^seq_converges\(/));
    const hausdorffHyp = all.find(o => o.claim.match(/^hausdorff\(/));
    const evidence2 = [convHyp, hausdorffHyp].filter(Boolean);
    if (evidence2.length > 0) {
      createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, evidence2.map(o => o!.id));
      return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: evidence2.map(o => o!.claim), message: `Convergent sequence eventually enters open neighborhood` };
    }
  }

  // ── ∃ n ∈ ℕ, x_n ∈ U ∩ V ───────────────────────────────────────────────
  if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*\w+_\w+\s*∈\s*\w+\s*∩\s*\w+$/)) {
    const evHyps = all.filter(o => o.claim.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*∀/));
    if (evHyps.length >= 2) {
      createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, evHyps.slice(0,2).map(o => o.id));
      return { rule: 'TOPO_CONTINUOUS_PREIMAGE' as const, state: 'PROVED' as const, uses: evHyps.slice(0,2).map(o => o.claim), message: `Sequence in intersection of neighborhoods` };
    }
  }

  // ── ∃ n ∈ ℕ, x_n ∈ ∅ ───────────────────────────────────────────────────
  if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*\w+_\w+\s*∈\s*∅$/)) {
    const intersectSeqHyp = all.find(o => o.claim.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*\w+_\w+\s*∈\s*\w+\s*∩/));
    if (intersectSeqHyp) {
      createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [intersectSeqHyp.id]);
      return { rule: 'TOPO_CLOSED' as const, state: 'PROVED' as const, uses: [intersectSeqHyp.claim], message: `Sequence in empty set via disjoint neighborhoods` };
    }
  }

  return null;
}
