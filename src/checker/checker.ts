import {
  ASTNode,
  AssertNode,
  AssumeNode,
  ConcludeNode,
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
} from '../parser/ast';
import {
  formatMorphismExpr,
  MorphismExpr,
  exprToProp,
  parseCategoricalEqualityCanonical,
  parseCategoryPredicateCanonical,
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

interface Context {
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

  const state = combineStates(reports.map(report => report.state), pairedCount === 0 ? 'PENDING' : 'PROVED');
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

function checkPair(
  pair: Pair,
  lemmas: Map<string, ClaimSet>,
  structs: Map<string, StructDefinition>,
  types: Map<string, TypeDefinition>,
  _options: CheckOptions,
): ProofReport {
  const premises = theoremPremises(pair.theorem);
  const goal = theoremGoal(pair.theorem);
  const ctx = createContext(goal, lemmas, premises, structs, types);
  seedPremises(ctx, premises);
  if (pair.proof.fnMeta) {
    const recursionIssue = validateListStructuralRecursion(pair.proof);
    if (recursionIssue) {
      ctx.unverifiedReasons.push(recursionIssue);
      ctx.diagnostics.push({ severity: 'warning', message: recursionIssue, rule: 'STRUCTURAL' });
    }
  }

  for (let index = 0; index < pair.proof.body.length; index++) {
    const step = index + 1;
    const node = pair.proof.body[index];
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
  }

  const derivedConclusion = findDerivedConclusion(ctx, goal);
  if (goal && !derivedConclusion) {
    const pendingGoal = findExact(ctx.objects, goal, true);
    ctx.diagnostics.push({
      severity: pendingGoal ? 'warning' : 'error',
      message: pendingGoal
        ? `Goal '${goal}' remains pending until Ra resolves its ω-valued morphisms`
        : `Proof '${pair.proof.name}' does not establish theorem goal '${goal}'`,
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

function handleNode(ctx: Context, node: ASTNode, step: number): void {
  switch (node.type) {
    case 'Assume':
      handleAssume(ctx, node, step);
      return;
    case 'SetVar':
      handleSetVar(ctx, node, step);
      return;
    case 'Assert':
      handleClaimStep(ctx, node, step, 'assert');
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
    default:
      return;
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
    state: branchStates.some(state => state === 'PENDING') ? 'PENDING' : 'PROVED',
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
    state: branchStates.some(state => state === 'PENDING') ? 'PENDING' : 'PROVED',
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
    ctx.diagnostics.push({ severity: 'error', step, message: `Unknown lemma '${target}'`, rule: 'BY_LEMMA' });
    ctx.proofSteps.push({
      step,
      kind: 'apply',
      claim: target,
      rule: 'BY_LEMMA',
      state: 'FAILED',
      message: `Lemma '${target}' is not available`,
    });
    return;
  }
  if (lemma.state === 'PENDING') {
    const claim = lemma.conclusion ?? target;
    createKernelObject(ctx, claim, 'BY_LEMMA', step, [], [lemma.name], 'ω', ['lemma']);
    ctx.proofSteps.push({
      step,
      kind: 'apply',
      claim,
      rule: 'BY_LEMMA',
      state: 'PENDING',
      imports: [lemma.name],
      message: `Lemma '${target}' imports a pending morphism`,
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
    createPendingObject(ctx, claim, step);
    ctx.proofSteps.push({
      step,
      kind: 'raw',
      claim,
      rule: 'STRUCTURAL',
      state: 'PENDING',
      message: 'Unsupported raw proof syntax is preserved as a pending morphism',
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

function handleClaimStep(ctx: Context, node: AssertNode | ConcludeNode, step: number, kind: 'assert' | 'conclude') {
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
      state: exact.pending ? 'PENDING' : 'PROVED',
      uses: [exact.claim],
      message: 'Claim already exists as a morphism in the current derivation',
    };
  }

  const prover = [
    deriveAndIntro,
    deriveAndElim,
    deriveStructClaim,
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
    deriveExFalso,
  ];

  for (const attempt of prover) {
    const result = attempt(ctx, claim, step);
    if (result) {
      return result;
    }
  }

  if (shouldRemainPending(claim)) {
    createPendingObject(ctx, claim, step);
    return {
      rule: 'STRUCTURAL',
      state: 'PENDING',
      message: 'Claim is structurally present but remains pending until supported morphisms are supplied or Ra resolves it',
    };
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
  return {
    rule: 'PRODUCT_INTRO' as const,
    state: 'PENDING' as const,
    message: 'Universal property error: mediator or projection data for the product is incomplete',
  };
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
  return { rule: 'COPRODUCT_INTRO' as const, state: 'PENDING' as const, message: 'Universal property error: coproduct injections are incomplete' };
}

function derivePullback(ctx: Context, args: string[], claim: string, step: number) {
  if (args.length < 5) return null;
  const [pullbackObject, p1, p2, f, g] = args;
  const p1Decl = findDeclarationByLabel(ctx, p1);
  const p2Decl = findDeclarationByLabel(ctx, p2);
  const fDecl = findDeclarationByLabel(ctx, f);
  const gDecl = findDeclarationByLabel(ctx, g);
  if (!p1Decl || !p2Decl || !fDecl || !gDecl) {
    return { rule: 'PULLBACK_INTRO' as const, state: 'PENDING' as const, message: 'Universal property error: pullback data is incomplete' };
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
    return { rule: 'PUSHOUT_INTRO' as const, state: 'PENDING' as const, message: 'Universal property error: pushout data is incomplete' };
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
  const membership = parseMembershipCanonical(claim);
  if (membership) {
    const union = parseBinarySetCanonical(membership.set, '∪');
    if (union) {
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
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  const intersection = parseBinarySetCanonical(membership.set, '∩');
  if (intersection) {
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

function theoremPremises(node: TheoremNode | LemmaNode): string[] {
  return node.body
    .filter((item): item is GivenNode => item.type === 'Given')
    .map(item => exprToProp(item.expr));
}

function registerCategoryClaim(ctx: Context, claim: string): void {
  try {
    ctx.diagrams.registerClaim(claim);
  } catch (error) {
    if (error instanceof CategoryDiagramError) {
      ctx.diagnostics.push({ severity: 'error', message: error.message, rule: 'CAT_MORPHISM' });
      return;
    }
    throw error;
  }
}

function theoremGoal(node: TheoremNode | LemmaNode): string | null {
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
    default:
      return 'raw';
  }
}

function nodeToClaim(node: ASTNode): string {
  switch (node.type) {
    case 'Assume':
    case 'Assert':
    case 'Conclude':
      return exprToProp(node.expr);
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
    return 'UNVERIFIED';
  }
  if (goal && !derivedConclusion) {
    return findExact(ctx.objects, goal, true) ? 'PENDING' : 'FAILED';
  }
  return ctx.objects.some(object => object.pending) ? 'PENDING' : 'PROVED';
}

function combineStates(states: ProofState[], fallback: ProofState): ProofState {
  if (states.length === 0) return fallback;
  if (states.includes('FAILED')) return 'FAILED';
  if (states.includes('UNVERIFIED')) return 'UNVERIFIED';
  if (states.includes('PENDING')) return 'PENDING';
  return 'PROVED';
}

function findExact(objects: ProofObject[], claim: string, allowPending: boolean): ProofObject | null {
  for (let index = objects.length - 1; index >= 0; index--) {
    const object = objects[index];
    if (sameProp(object.claim, claim) && (allowPending || !object.pending)) {
      return object;
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

function shouldRemainPending(claim: string): boolean {
  return Boolean(
    parseBoundedQuantifierCanonical(claim, 'forall') ||
    parseBoundedQuantifierCanonical(claim, 'exists') ||
    parseSetBuilderCanonical(claim) ||
    parseIndexedUnionCanonical(claim) ||
    claim.includes('∀') ||
    claim.includes('∃')
  );
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
