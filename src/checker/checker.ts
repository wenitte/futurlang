// src/checker/checker.ts
// Main proof checker — walks the AST and applies inference rules

import {
  ASTNode, TheoremNode, ProofNode, LemmaNode, DefinitionNode,
  AssertNode, GivenNode, AssumeNode, ConcludeNode, ApplyNode, SetVarNode, RawNode,
  ExprNode, AtomNode,
} from '../parser/ast';
import {
  ProofContext, ProofReport, FileReport, Diagnostic,
  Claim, Variable, ClaimSet, ProofMethod, CheckResult, ProofStepTrace, ProofObject,
  DerivationNode,
} from './types';
import {
  checkAssumption, checkContradiction, checkLemmaApplication,
  checkTheoremProofPairing, checkInduction, checkAndIntro,
  checkAndElim, checkImpliesIntro, checkModusPonens, checkSubsetElim,
} from './rules';
import {
  exprToProp, sameProp, splitConjunction as splitGoalConjunction,
  splitImplication, splitIff,
} from './propositions';

// ── Public API ────────────────────────────────────────────────────────────────

export function checkFile(nodes: ASTNode[]): FileReport {
  const diagnostics: Diagnostic[] = [];
  const reports: ProofReport[] = [];
  const globalLemmas = new Map<string, ClaimSet>();

  // Pass 1: collect all theorem/lemma names into global scope
  collectLemmaNames(nodes, globalLemmas);

  // Pass 2: find and check theorem↔proof pairs
  const pairs = findPairs(nodes);
  const pairedNames = new Set(pairs.map(pair => normalizeName(pair.theorem.name)));

  let theoremCount = 0, proofCount = 0, pairedCount = 0;

  for (const node of nodes) {
    if (node.type === 'Theorem') theoremCount++;
    if (node.type === 'Proof')   proofCount++;
    if (node.type === 'Lemma')   {
      theoremCount++;
      if (!pairedNames.has(normalizeName(node.name))) {
        const report = checkProofBlock(node.name, node.body, globalLemmas, 'unknown');
        reports.push(report);
      }
    }
  }

  for (const pair of pairs) {
    pairedCount++;
    const report = checkPair(pair.theorem, pair.proof, globalLemmas);
    reports.push(report);
  }

  // File-level checks
  if (theoremCount === 0) {
    diagnostics.push({ severity: 'warning', message: 'File contains no theorems' });
  }
  if (pairedCount < theoremCount) {
    diagnostics.push({
      severity: 'info',
      message: `${theoremCount - pairedCount} theorem(s) have no proof`
    });
  }

  const allValid = reports.every(r => r.valid);
  const score = computeScore(reports, pairedCount, theoremCount);

  return { valid: allValid, theoremCount, proofCount, pairedCount, reports, diagnostics, score };
}

// ── Pair finding ──────────────────────────────────────────────────────────────

interface TheoremProofPair {
  theorem: TheoremNode | LemmaNode;
  proof:   ProofNode;
}

function findPairs(nodes: ASTNode[]): TheoremProofPair[] {
  const pairs: TheoremProofPair[] = [];
  for (let i = 0; i < nodes.length; i++) {
    const node = nodes[i];
    if ((node.type === 'Theorem' || node.type === 'Lemma') && node.connective === '↔') {
      // Look for matching proof
      for (let j = i + 1; j < nodes.length; j++) {
        if (nodes[j].type === 'Proof') {
          const proof = nodes[j] as ProofNode;
          if (normalizeName(proof.name) === normalizeName(node.name)) {
            pairs.push({ theorem: node, proof });
            break;
          }
        }
        // Stop looking if we hit another theorem
        if (nodes[j].type === 'Theorem') break;
      }
    }
  }
  return pairs;
}

// ── Check a theorem↔proof pair ────────────────────────────────────────────────

function checkPair(thm: TheoremNode | LemmaNode, proof: ProofNode, globalLemmas: Map<string, ClaimSet>): ProofReport {
  const diagnostics: Diagnostic[] = [];
  const theoremPremises = thm.body
    .filter((n): n is GivenNode => n.type === 'Given')
    .map(node => exprToProp(node.expr));
  const theoremGoalExpr = thm.body.find((n): n is AssertNode => n.type === 'Assert')?.expr ?? null;
  const theoremGoal = theoremGoalExpr ? exprToProp(theoremGoalExpr) : null;

  // Check the pairing itself
  const thmAsserts  = thm.body.filter(n => n.type === 'Assert');
  const pairingCheck = checkTheoremProofPairing(
    thm.name, proof.name,
    thmAsserts.length > 0,
    proof.body.length,
    proof.body.some(n => n.type === 'Conclude')
  );

  if (!pairingCheck.valid) {
    diagnostics.push({ severity: 'error', message: pairingCheck.message, hint: pairingCheck.hint, rule: pairingCheck.rule });
  }

  // Detect proof method
  const method = detectProofMethod(proof.body);

  // Check the proof body
  const proofReport = checkProofBlock(proof.name, proof.body, globalLemmas, method, theoremGoal, theoremPremises);
  diagnostics.push(...proofReport.diagnostics);

  if (theoremGoalExpr) {
    const goalParseDiagnostic = parseFallbackDiagnostic(theoremGoalExpr, `Theorem goal '${theoremGoal}'`);
    if (goalParseDiagnostic) diagnostics.push(goalParseDiagnostic);
    if (!isCheckableGoal(theoremGoalExpr)) {
      diagnostics.push({
        severity: 'info',
        message: `Goal '${theoremGoal}' is outside the current checker subset; use 'fl verify' for semantic verification`,
        rule: 'THEOREM_PROOF',
      });
    } else if (!goalSatisfied(theoremGoalExpr, proofReport, proof.body)) {
      diagnostics.push({
        severity: 'error',
        message: `Proof '${proof.name}' does not establish theorem goal '${theoremGoal}'`,
        hint: theoremGoalHint(theoremGoalExpr),
        rule: 'THEOREM_PROOF',
      });
    }
  }

  return {
    name: thm.name,
    valid: pairingCheck.valid && proofReport.valid && !diagnostics.some(d => d.severity === 'error'),
    method,
    stepCount: proof.body.length,
    goal: theoremGoal,
    premises: theoremPremises,
    derivedConclusion: proofReport.derivedConclusion,
    proofSteps: proofReport.proofSteps,
    proofObjects: proofReport.proofObjects,
    derivations: proofReport.derivations,
    baseFactIds: proofReport.baseFactIds,
    derivedFactIds: proofReport.derivedFactIds,
    diagnostics,
    metrics: proofReport.metrics,
  };
}

// ── Check a proof body ────────────────────────────────────────────────────────

function checkProofBlock(
  name: string,
  body: ASTNode[],
  globalLemmas: Map<string, ClaimSet>,
  method: ProofMethod,
  goal: string | null = null,
  premises: string[] = []
): ProofReport {
  const diagnostics: Diagnostic[] = [];
  const premiseClaims = premises.map((content, index) => ({
    content,
    source: 'premise' as const,
    step: -(index + 1),
    proofObjectId: makeProofObjectId(-(index + 1), 'premise', content),
  }));
  const ctx: ProofContext = {
    established: premiseClaims,
    proofObjects: premiseClaims.map(claim => ({
      id: claim.proofObjectId!,
      claim: claim.content,
      rule: 'PREMISE',
      source: claim.source,
      step: claim.step,
      dependsOn: [],
      dependsOnIds: [],
    })),
    derivations: [],
    variables: [],
    lemmas: new Map(globalLemmas),
    method,
    inContradiction: false,
    goal,
  };

  let step = 0;
  let assumptionCount = 0, assertionCount = 0, lemmaCount = 0;
  let hasConclusion = false, hasSorry = false;
  let maxDepth = 0, currentDepth = 0;
  const proofSteps: ProofStepTrace[] = [];

  for (const node of body) {
    step++;

    switch (node.type) {
      case 'Assume': {
        const n = node as AssumeNode;
        const claim = exprToString(n.expr);
        const parseDiagnostic = parseFallbackDiagnostic(n.expr, `Step ${step} assumption '${claim}'`);
        if (parseDiagnostic) diagnostics.push(parseDiagnostic);
        const result = checkAssumption(claim);
        if (!result.valid) {
          diagnostics.push({ severity: 'error', message: result.message, step, rule: result.rule });
        }
        registerAssumptionClaim(ctx, claim, step, result.rule);
        proofSteps.push({
          step,
          kind: 'assume',
          claim,
          rule: result.rule,
          valid: result.valid,
          message: result.message,
          establishesAs: 'assumption',
        });
        // If assumption is negated something, we're in contradiction mode
        if (claim.startsWith('¬') || claim.startsWith('not ') ||
            claim.includes('contradiction') || claim.toLowerCase().includes('bycontradiction')) {
          ctx.inContradiction = true;
        }
        assumptionCount++;
        currentDepth++;
        maxDepth = Math.max(maxDepth, currentDepth);
        break;
      }

      case 'Assert': {
        const n = node as AssertNode;
        const claim = exprToString(n.expr);
        const parseDiagnostic = parseFallbackDiagnostic(n.expr, `Step ${step} assertion '${claim}'`);
        if (parseDiagnostic) diagnostics.push(parseDiagnostic);

        // Check for sorry (explicit gap)
        if (claim.toLowerCase().includes('sorry')) {
          hasSorry = true;
          diagnostics.push({ severity: 'info', message: `Step ${step}: sorry placeholder`, rule: 'SORRY' });
          registerAssertionClaim(ctx, claim, step, 'SORRY');
          proofSteps.push({
            step,
            kind: 'assert',
            claim,
            rule: 'SORRY',
            valid: true,
            message: 'sorry placeholder',
          });
          break;
        }

        // Check and/intro: if claim is a conjunction, verify both sides
        let stepRule: CheckResult | null = null;
        if (isConjunction(n.expr)) {
          const [left, right] = splitConjunction(n.expr);
          const andResult = checkAndIntro(left, right, ctx);
          stepRule = andResult;
          if (!andResult.valid) {
            // Warning not error — the conjunction may be introducing new facts
            diagnostics.push({ severity: 'info', message: andResult.message, step, hint: andResult.hint });
          }
        } else {
          const premise = checkPremiseClaim(claim, ctx);
          if (premise) {
            stepRule = premise;
          } else {
            const derivation = checkDerivedClaim(claim, ctx);
            if (derivation?.valid) {
              stepRule = derivation;
            }
          }
        }

        const finalizedAssertion = registerDerivedClaim(ctx, {
          content: claim,
          source: 'assertion',
          step,
          derivation: stepRule,
        });
        if (!finalizedAssertion.result.valid && stepRule?.valid !== false) {
          diagnostics.push({
            severity: 'error',
            message: finalizedAssertion.result.message,
            step,
            hint: finalizedAssertion.result.hint,
            rule: finalizedAssertion.result.rule,
          });
        }
        proofSteps.push({
          step,
          kind: 'assert',
          claim,
          rule: finalizedAssertion.result.rule,
          valid: finalizedAssertion.result.valid,
          message: finalizedAssertion.result.message,
          establishesAs: 'assertion',
        });
        assertionCount++;

        // Each assert deepens the chain
        if (n.connective === '→') currentDepth++;
        maxDepth = Math.max(maxDepth, currentDepth);
        break;
      }

      case 'Conclude': {
        const n = node as ConcludeNode;
        const claim = exprToString(n.expr);
        const parseDiagnostic = parseFallbackDiagnostic(n.expr, `Step ${step} conclusion '${claim}'`);
        if (parseDiagnostic) diagnostics.push(parseDiagnostic);
        const contradictionDischarge = checkContradictionDischarge(claim, ctx);
        const derivation = isConjunction(n.expr)
          ? checkAndIntro(...splitConjunction(n.expr), ctx)
          : contradictionDischarge ?? checkDerivedClaim(claim, ctx) ?? checkImplicationGoalDischarge(claim, ctx);
        if (derivation && !derivation.valid) {
          diagnostics.push({ severity: 'error', message: derivation.message, step, hint: derivation.hint, rule: derivation.rule });
        }
        const finalizedConclusion = registerDerivedClaim(ctx, {
          content: claim,
          source: 'conclusion',
          step,
          derivation,
        });
        if (!finalizedConclusion.result.valid) {
          diagnostics.push({ severity: 'error', message: finalizedConclusion.result.message, step, hint: finalizedConclusion.result.hint, rule: finalizedConclusion.result.rule });
        }
        proofSteps.push({
          step,
          kind: 'conclude',
          claim,
          rule: finalizedConclusion.result.rule,
          valid: finalizedConclusion.result.valid,
          message: finalizedConclusion.result.message,
          establishesAs: 'conclusion',
        });
        hasConclusion = true;

        // If we're in a contradiction block, the contradiction result is valid
        if (claim.toLowerCase().includes('contradiction')) {
          const result = checkContradiction(ctx);
          if (!result.valid) {
            diagnostics.push({ severity: 'error', message: result.message, step, hint: result.hint });
          }
        }
        break;
      }

      case 'Apply': {
        const n = node as ApplyNode;
        const result = checkLemmaApplication(n.target, ctx);
        const lemma = ctx.lemmas.get(normalizeName(n.target));
        if (result.valid && lemma && lemma.conclusions.length > 0) {
          for (const conclusion of lemma.conclusions) {
            registerLemmaImportClaim(ctx, conclusion, step, lemma.hypotheses, lemma.conclusions);
          }
        } else if (result.valid) {
          registerLemmaImportClaim(ctx, `applied(${n.target})`, step, [], []);
        }
        if (!result.valid) {
          diagnostics.push({ severity: 'error', message: result.message, step, rule: result.rule, hint: result.hint });
        }
        proofSteps.push({
          step,
          kind: 'apply',
          claim: n.target,
          rule: result.rule,
          valid: result.valid,
          message: result.message,
          uses: result.valid && lemma ? lemma.hypotheses : [],
          imports: result.valid && lemma ? lemma.conclusions : [],
          establishesAs: 'lemma_application',
        });
        lemmaCount++;
        break;
      }

      case 'SetVar': {
        const n = node as SetVarNode;
        ctx.variables.push({ name: n.varName, type: n.varType, step });
        // Variables are always valid introductions
        if (n.varType) {
          registerVariableClaim(ctx, `${n.varName}: ${n.varType}`, step);
        }
        proofSteps.push({
          step,
          kind: 'setVar',
          claim: n.varType ? `${n.varName}: ${n.varType}` : n.varName,
          rule: 'VARIABLE',
          valid: true,
          message: 'Variable introduced into context',
          establishesAs: 'variable',
        });
        break;
      }

      case 'Raw': {
        const n = node as RawNode;
        const content = n.content.trim().toLowerCase();

        // Detect contradiction marker in raw content
        if (content === 'contradiction()' || content === 'contradiction') {
          const result = checkContradiction(ctx);
          if (!result.valid) {
            diagnostics.push({ severity: 'error', message: result.message, step, hint: result.hint });
          }
          registerContradictionClaim(ctx, step, result.rule);
          proofSteps.push({
            step,
            kind: 'raw',
            claim: 'contradiction',
            rule: result.rule,
            valid: result.valid,
            message: result.message,
            establishesAs: 'assertion',
          });
        } else {
          proofSteps.push({
            step,
            kind: 'raw',
            claim: n.content,
            rule: 'STRUCTURAL',
            valid: true,
            message: 'Raw proof step preserved',
          });
        }
        break;
      }

      case 'Lemma': {
        // Inline lemma — recurse
        const n = node as LemmaNode;
        const lemmaGoalExpr = n.body.find((child): child is AssertNode => child.type === 'Assert')?.expr ?? null;
        const innerReport = checkProofBlock(n.name, n.body, ctx.lemmas, 'unknown', lemmaGoalExpr ? exprToProp(lemmaGoalExpr) : null);
        ctx.lemmas.set(normalizeName(n.name), {
          hypotheses: [],
          conclusions: innerReport.derivedConclusion ? [innerReport.derivedConclusion] : [],
        });
        diagnostics.push(...innerReport.diagnostics.map(d => ({ ...d, message: `[${n.name}] ${d.message}` })));
        registerLemmaImportClaim(ctx, `lemma(${n.name})`, step, innerReport.derivedConclusion ? [innerReport.derivedConclusion] : [], []);
        proofSteps.push({
          step,
          kind: 'lemma',
          claim: n.name,
          rule: 'BY_LEMMA',
          valid: innerReport.valid,
          message: innerReport.valid ? 'Inline lemma checked' : 'Inline lemma has errors',
          establishesAs: 'lemma_application',
        });
        lemmaCount++;
        break;
      }
    }
  }

  // Induction-specific checks
  if (method === 'induction') {
    const content = body.map(n => nodeToString(n)).join(' ').toLowerCase();
    const result = checkInduction(
      content.includes('base_case') || content.includes('base case') || content.includes('n = 0') || content.includes('n = 1'),
      content.includes('inductive_step') || content.includes('inductive step') || content.includes('k + 1') || content.includes('n + 1'),
      content.includes('inductive hypothesis') || content.includes('induction hypothesis') || content.includes('inductive_hypothesis')
    );
    if (!result.valid) {
      diagnostics.push({ severity: 'error', message: result.message, hint: result.hint, rule: result.rule });
    }
  }

  // Final check: does the proof establish anything at all?
  const hasAnyProgress = ctx.established.length > 0;
  if (!hasAnyProgress) {
    diagnostics.push({ severity: 'error', message: `Proof '${name}' establishes nothing`, rule: 'STRUCTURAL' });
  }

  const valid = !diagnostics.some(d => d.severity === 'error');
  const derivedConclusion = findDerivedConclusion(ctx.established);
  const baseFactIds = collectBaseFactIds(ctx.proofObjects, ctx.derivations);
  const derivedFactIds = collectDerivedFactIds(ctx.derivations);
  diagnostics.push(...validateDerivationGraph({
    goal: ctx.goal,
    proofObjects: ctx.proofObjects,
    derivations: ctx.derivations,
  }));

  return {
    name,
    valid: !diagnostics.some(d => d.severity === 'error'),
    method,
    stepCount: step,
    goal: ctx.goal,
    premises,
    derivedConclusion,
    proofSteps,
    proofObjects: ctx.proofObjects,
    derivations: ctx.derivations,
    baseFactIds,
    derivedFactIds,
    diagnostics,
    metrics: {
      assumptionCount,
      assertionCount,
      lemmaApplicationCount: lemmaCount,
      hasConclusion,
      hasSorry,
      dependencyDepth: maxDepth,
    },
  };
}

// ── Helpers ───────────────────────────────────────────────────────────────────

function detectProofMethod(body: ASTNode[]): ProofMethod {
  const content = body.map(n => nodeToString(n)).join(' ').toLowerCase();
  if (content.includes('bycontradiction') || content.includes('by_contradiction') ||
      content.includes('contradiction') || content.includes('assume(¬') ||
      content.includes('assume(not ')) return 'contradiction';
  if (content.includes('induction') || content.includes('base_case') ||
      content.includes('inductive_step')) return 'induction';
  if (content.includes('construct') || content.includes('define(') ||
      content.includes('let ')) return 'construction';
  return 'direct';
}

function collectLemmaNames(nodes: ASTNode[], map: Map<string, ClaimSet>) {
  for (const node of nodes) {
    if (node.type === 'Lemma' || node.type === 'Theorem') {
      const key = normalizeName(node.name);
      const statement = node.body.find((child): child is AssertNode => child.type === 'Assert');
      const hypotheses = node.body
        .filter((child): child is GivenNode => child.type === 'Given')
        .map(child => exprToProp(child.expr));
      map.set(key, { name: node.name, hypotheses, conclusions: statement ? [exprToProp(statement.expr)] : [] });
    }
    if (node.type === 'Definition') {
      const key = normalizeName(node.name);
      map.set(key, { name: node.name, hypotheses: [], conclusions: ['defined'] });
    }
  }
}

function exprToString(expr: ExprNode): string {
  return exprToProp(expr);
}

function nodeToString(node: ASTNode): string {
  switch (node.type) {
    case 'Given':    return exprToString((node as GivenNode).expr);
    case 'Assert':   return exprToString((node as AssertNode).expr);
    case 'Assume':   return exprToString((node as AssumeNode).expr);
    case 'Conclude': return exprToString((node as ConcludeNode).expr);
    case 'Raw':      return (node as RawNode).content;
    case 'Apply':    return `apply(${(node as ApplyNode).target})`;
    default: return '';
  }
}

function isConjunction(expr: ExprNode): boolean {
  return expr.type === 'And';
}

function splitConjunction(expr: ExprNode): [string, string] {
  return splitGoalConjunction(expr) ?? ['', ''];
}

function normalizeName(s: string): string {
  return s.toLowerCase().replace(/[^a-z0-9]/g, '');
}

function computeScore(reports: ProofReport[], paired: number, total: number): number {
  if (total === 0) return 0;
  let score = 0;
  // 40 points for pairing ratio
  score += (paired / total) * 40;
  // 40 points for validity
  const validRatio = reports.filter(r => r.valid).length / Math.max(reports.length, 1);
  score += validRatio * 40;
  // 20 points for richness (has assumptions, conclusions, no sorry)
  const richRatio = reports.filter(r =>
    r.metrics.assumptionCount > 0 &&
    r.metrics.hasConclusion &&
    !r.metrics.hasSorry
  ).length / Math.max(reports.length, 1);
  score += richRatio * 20;
  return Math.round(score);
}

function goalSatisfied(goalExpr: ExprNode, report: ProofReport, body: ASTNode[]): boolean {
  const established = report.derivedConclusion;
  if (!established) return false;
  const goal = exprToProp(goalExpr);
  if (sameProp(established, goal)) return true;

  const implication = splitImplication(goalExpr);
  if (implication) {
    const [antecedent, consequent] = implication;
    const sawAssumption = body.some(
      node => node.type === 'Assume' && sameProp(exprToString((node as AssumeNode).expr), antecedent)
    );
    return sawAssumption && sameProp(established, consequent);
  }

  const conjunction = splitGoalConjunction(goalExpr);
  if (conjunction) {
    const [left, right] = conjunction;
    const establishedClaims = collectEstablishedClaims(body);
    return establishedClaims.some(claim => sameProp(claim, left))
      && establishedClaims.some(claim => sameProp(claim, right));
  }

  const iff = splitIff(goalExpr);
  if (iff) {
    const [left, right] = iff;
    const establishedClaims = collectEstablishedClaims(body);
    return establishedClaims.some(claim => sameProp(claim, `${left} → ${right}`))
      && establishedClaims.some(claim => sameProp(claim, `${right} → ${left}`));
  }

  return false;
}

function collectEstablishedClaims(body: ASTNode[]): string[] {
  const claims: string[] = [];
  for (const node of body) {
    if (node.type === 'Assert') claims.push(exprToString(node.expr));
    if (node.type === 'Assume') claims.push(exprToString(node.expr));
    if (node.type === 'Conclude') claims.push(exprToString(node.expr));
  }
  return claims;
}

function findDerivedConclusion(established: Claim[]): string | null {
  for (let i = established.length - 1; i >= 0; i--) {
    const claim = established[i];
    if (claim.source === 'conclusion' || claim.source === 'assertion' || claim.source === 'lemma_application') {
      return claim.content;
    }
  }
  return null;
}

function registerClaim(
  ctx: ProofContext,
  input: {
    content: string;
    source: Claim['source'];
    step: number;
    rule: CheckResult['rule'];
    dependsOn: string[];
    dependsOnIds?: string[];
    imports?: string[];
    emitDerivation?: boolean;
  }
): Claim {
  const proofObjectId = makeProofObjectId(input.step, input.source, input.content);
  const claim: Claim = {
    content: input.content,
    source: input.source,
    step: input.step,
    proofObjectId,
  };
  ctx.established.push(claim);
  ctx.proofObjects.push({
    id: proofObjectId,
    claim: input.content,
    rule: input.rule,
    source: input.source,
    step: input.step,
    dependsOn: uniqueProps(input.dependsOn),
    dependsOnIds: uniqueIds(input.dependsOnIds ?? resolveClaimIds(ctx, input.dependsOn)),
    imports: input.imports && input.imports.length > 0 ? uniqueProps(input.imports) : undefined,
  });
  if (input.emitDerivation !== false) {
    ctx.derivations.push(makeDerivationNode(input.step, input.rule, uniqueIds(input.dependsOnIds ?? resolveClaimIds(ctx, input.dependsOn)), proofObjectId));
  }
  return claim;
}

function registerAssumptionClaim(ctx: ProofContext, claim: string, step: number, rule: CheckResult['rule']): Claim {
  return registerClaim(ctx, {
    content: claim,
    source: 'assumption',
    step,
    rule,
    dependsOn: [],
    emitDerivation: false,
  });
}

function registerAssertionClaim(ctx: ProofContext, claim: string, step: number, rule: CheckResult['rule']): Claim {
  return registerClaim(ctx, {
    content: claim,
    source: 'assertion',
    step,
    rule,
    dependsOn: [],
    emitDerivation: false,
  });
}

function registerVariableClaim(ctx: ProofContext, claim: string, step: number): Claim {
  return registerClaim(ctx, {
    content: claim,
    source: 'variable',
    step,
    rule: 'VARIABLE',
    dependsOn: [],
    emitDerivation: false,
  });
}

function registerLemmaImportClaim(
  ctx: ProofContext,
  claim: string,
  step: number,
  hypotheses: string[],
  imports: string[],
): Claim {
  return registerClaim(ctx, {
    content: claim,
    source: 'lemma_application',
    step,
    rule: 'BY_LEMMA',
    dependsOn: hypotheses,
    dependsOnIds: resolveClaimIds(ctx, hypotheses),
    imports,
  });
}

function registerContradictionClaim(ctx: ProofContext, step: number, rule: CheckResult['rule']): Claim {
  const dependency = findContradictionDependency(ctx);
  return registerClaim(ctx, {
    content: 'contradiction',
    source: 'assertion',
    step,
    rule,
    dependsOn: dependency?.claims ?? [],
    dependsOnIds: dependency?.ids ?? [],
  });
}

function registerDerivedClaim(
  ctx: ProofContext,
  input: {
    content: string;
    source: 'assertion' | 'conclusion';
    step: number;
    derivation: CheckResult | null;
  }
): { claim: Claim; result: CheckResult } {
  const builder = buildProofObjectInput(input.content, input.source, input.step, input.derivation, ctx);
  const graphValidation = validateProofObjectInput(builder);
  const result = graphValidation ?? input.derivation ?? {
    valid: true as const,
    rule: builder.rule,
    message: builder.rule === 'STRUCTURAL' ? 'Assertion accepted' : `${builder.rule} accepted`,
  };
  const claim = registerClaim(ctx, {
    ...builder,
    emitDerivation: Boolean(input.derivation?.valid) && !graphValidation,
  });
  return { claim, result };
}

function makeProofObjectId(step: number, source: string, claim: string): string {
  return `${source}:${step}:${normalizeName(claim)}`;
}

function makeDerivationNode(step: number, rule: CheckResult['rule'], inputIds: string[], outputId: string): DerivationNode {
  return {
    id: `derivation:${step}:${normalizeName(outputId)}`,
    step,
    rule,
    inputIds,
    outputId,
  };
}

function collectBaseFactIds(proofObjects: ProofObject[], derivations: DerivationNode[]): string[] {
  const derived = new Set(derivations.map(node => node.outputId));
  return proofObjects.filter(object => !derived.has(object.id)).map(object => object.id);
}

function collectDerivedFactIds(derivations: DerivationNode[]): string[] {
  return [...new Set(derivations.map(node => node.outputId))];
}

function validateDerivationGraph(input: {
  goal: string | null;
  proofObjects: ProofObject[];
  derivations: DerivationNode[];
}): Diagnostic[] {
  const diagnostics: Diagnostic[] = [];
  const objectMap = new Map(input.proofObjects.map(object => [object.id, object]));

  for (const node of input.derivations) {
    const output = objectMap.get(node.outputId);
    if (!output) {
      diagnostics.push({
        severity: 'error',
        message: `Derivation '${node.id}' references missing output proof object '${node.outputId}'`,
        step: node.step,
        rule: node.rule,
      });
      continue;
    }

    const inputs = node.inputIds
      .map(id => objectMap.get(id))
      .filter((object): object is ProofObject => Boolean(object));

    if (inputs.length !== node.inputIds.length) {
      diagnostics.push({
        severity: 'error',
        message: `Derivation '${node.id}' references missing input proof objects`,
        step: node.step,
        rule: node.rule,
      });
      continue;
    }

    const error = validateDerivationNode(node, inputs, output, input.goal);
    if (error) diagnostics.push(error);
  }

  return diagnostics;
}

function validateDerivationNode(
  node: DerivationNode,
  inputs: ProofObject[],
  output: ProofObject,
  goal: string | null,
): Diagnostic | null {
  switch (node.rule) {
    case 'IMPLIES_ELIM':
      return validateImpliesElimNode(node, inputs, output);
    case 'AND_INTRO':
      return validateAndIntroNode(node, inputs, output);
    case 'AND_ELIM':
      return validateAndElimNode(node, inputs, output);
    case 'SUBSET_ELIM':
      return validateSubsetElimNode(node, inputs, output);
    case 'IMPLIES_INTRO':
      return validateImpliesIntroNode(node, inputs, output, goal);
    case 'CONTRADICTION':
      return validateContradictionNode(node, inputs);
    case 'BY_LEMMA':
      return inputs.length === 0 && output.dependsOnIds.length > 0
        ? {
            severity: 'error',
            message: `Lemma derivation '${node.id}' has no resolved inputs`,
            step: node.step,
            rule: node.rule,
          }
        : null;
    default:
      return null;
  }
}

function validateImpliesElimNode(node: DerivationNode, inputs: ProofObject[], output: ProofObject): Diagnostic | null {
  if (inputs.length !== 2) {
    return { severity: 'error', message: `IMPLIES_ELIM '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
  }
  const implication = inputs.find(input => parseImplicationProp(input.claim));
  const antecedent = inputs.find(input => !parseImplicationProp(input.claim));
  if (!implication || !antecedent) {
    return { severity: 'error', message: `IMPLIES_ELIM '${node.id}' must reference an implication and its antecedent`, step: node.step, rule: node.rule };
  }
  const pair = parseImplicationProp(implication.claim);
  if (!pair || !sameProp(pair[0], antecedent.claim) || !sameProp(pair[1], output.claim)) {
    return { severity: 'error', message: `IMPLIES_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
  }
  return null;
}

function validateAndIntroNode(node: DerivationNode, inputs: ProofObject[], output: ProofObject): Diagnostic | null {
  const conjunction = parseConjunctionProp(output.claim);
  if (!conjunction) {
    return { severity: 'error', message: `AND_INTRO '${node.id}' must produce a conjunction`, step: node.step, rule: node.rule };
  }
  if (inputs.length < 2) {
    return { severity: 'error', message: `AND_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
  }
  const leftOk = inputs.some(input => sameProp(input.claim, conjunction[0]));
  const rightOk = inputs.some(input => sameProp(input.claim, conjunction[1]));
  if (!leftOk || !rightOk) {
    return { severity: 'error', message: `AND_INTRO '${node.id}' inputs do not match '${output.claim}'`, step: node.step, rule: node.rule };
  }
  return null;
}

function validateAndElimNode(node: DerivationNode, inputs: ProofObject[], output: ProofObject): Diagnostic | null {
  if (inputs.length !== 1) {
    return { severity: 'error', message: `AND_ELIM '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
  }
  const conjunction = parseConjunctionProp(inputs[0].claim);
  if (!conjunction || (!sameProp(conjunction[0], output.claim) && !sameProp(conjunction[1], output.claim))) {
    return { severity: 'error', message: `AND_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
  }
  return null;
}

function validateSubsetElimNode(node: DerivationNode, inputs: ProofObject[], output: ProofObject): Diagnostic | null {
  if (inputs.length !== 2) {
    return { severity: 'error', message: `SUBSET_ELIM '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
  }
  const membership = inputs.find(input => parseMembershipProp(input.claim));
  const subset = inputs.find(input => parseSubsetProp(input.claim));
  if (!membership || !subset) {
    return { severity: 'error', message: `SUBSET_ELIM '${node.id}' must reference membership and subset inputs`, step: node.step, rule: node.rule };
  }
  const membershipParts = parseMembershipProp(membership.claim);
  const subsetParts = parseSubsetProp(subset.claim);
  const outputParts = parseMembershipProp(output.claim);
  if (!membershipParts || !subsetParts || !outputParts) {
    return { severity: 'error', message: `SUBSET_ELIM '${node.id}' has malformed set-theoretic inputs`, step: node.step, rule: node.rule };
  }
  if (!sameProp(membershipParts.element, outputParts.element) ||
      !sameProp(membershipParts.set, subsetParts.left) ||
      !sameProp(outputParts.set, subsetParts.right)) {
    return { severity: 'error', message: `SUBSET_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
  }
  return null;
}

function validateImpliesIntroNode(node: DerivationNode, inputs: ProofObject[], output: ProofObject, goal: string | null): Diagnostic | null {
  if (inputs.length < 1) {
    return { severity: 'error', message: `IMPLIES_INTRO '${node.id}' requires proof inputs`, step: node.step, rule: node.rule };
  }
  const implication = parseImplicationProp(output.claim) ?? (goal ? parseImplicationProp(goal) : null);
  if (!implication) {
    return { severity: 'error', message: `IMPLIES_INTRO '${node.id}' must produce an implication`, step: node.step, rule: node.rule };
  }
  const assumption = inputs.find(input => input.source === 'assumption' && sameProp(input.claim, implication[0]));
  const consequent = inputs.find(input => sameProp(input.claim, implication[1]));
  if (!assumption || !consequent) {
    return { severity: 'error', message: `IMPLIES_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
  }
  return null;
}

function validateContradictionNode(node: DerivationNode, inputs: ProofObject[]): Diagnostic | null {
  if (inputs.length < 2) {
    return { severity: 'error', message: `CONTRADICTION '${node.id}' requires conflicting inputs`, step: node.step, rule: node.rule };
  }
  const hasPair = inputs.some(input => inputs.some(other => input.id !== other.id && sameProp(negateProp(input.claim), other.claim)));
  if (!hasPair) {
    return { severity: 'error', message: `CONTRADICTION '${node.id}' has no contradictory input pair`, step: node.step, rule: node.rule };
  }
  return null;
}

function buildProofObjectInput(
  claim: string,
  source: 'assertion' | 'conclusion',
  step: number,
  derivation: CheckResult | null,
  ctx: ProofContext,
): {
  content: string;
  source: Claim['source'];
  step: number;
  rule: CheckResult['rule'];
  dependsOn: string[];
  dependsOnIds?: string[];
  imports?: string[];
} {
  if (!derivation?.valid) {
    return {
      content: claim,
      source,
      step,
      rule: derivation?.rule ?? 'STRUCTURAL',
      dependsOn: [],
    };
  }

  switch (derivation.rule) {
    case 'PREMISE':
      return buildPremiseProofObject(claim, source, step, ctx);
    case 'IMPLIES_ELIM':
      return buildImpliesElimProofObject(claim, source, step, ctx);
    case 'AND_INTRO':
      return buildAndIntroProofObject(claim, source, step, ctx);
    case 'AND_ELIM':
      return buildAndElimProofObject(claim, source, step, ctx);
    case 'SUBSET_ELIM':
      return buildSubsetElimProofObject(claim, source, step, ctx);
    case 'IMPLIES_INTRO':
      return buildImpliesIntroProofObject(claim, source, step, ctx);
    case 'CONTRADICTION':
      return buildContradictionDischargeProofObject(claim, source, step, ctx);
    default:
      return {
        content: claim,
        source,
        step,
        rule: derivation.rule,
        dependsOn: [],
      };
  }
}

function buildPremiseProofObject(claim: string, source: 'assertion' | 'conclusion', step: number, ctx: ProofContext) {
  const dependencyClaims = [claim];
  return {
    content: claim,
    source,
    step,
    rule: 'PREMISE' as const,
    dependsOn: dependencyClaims,
    dependsOnIds: resolveClaimIds(ctx, dependencyClaims),
  };
}

function implicationOutputClaim(claim: string, ctx: ProofContext): string {
  const implication = ctx.goal ? parseImplicationProp(ctx.goal) : parseImplicationProp(claim);
  if (!implication) return claim;
  return `${implication[0]} → ${implication[1]}`;
}

function buildImpliesElimProofObject(claim: string, source: 'assertion' | 'conclusion', step: number, ctx: ProofContext) {
  const dependency = findImplicationElimDependency(claim, ctx);
  return {
    content: claim,
    source,
    step,
    rule: 'IMPLIES_ELIM' as const,
    dependsOn: dependency?.claims ?? [],
    dependsOnIds: dependency?.ids ?? [],
  };
}

function buildAndIntroProofObject(claim: string, source: 'assertion' | 'conclusion', step: number, ctx: ProofContext) {
  const dependency = findAndIntroDependency(claim, ctx);
  return {
    content: claim,
    source,
    step,
    rule: 'AND_INTRO' as const,
    dependsOn: dependency?.claims ?? [],
    dependsOnIds: dependency?.ids ?? [],
  };
}

function buildAndElimProofObject(claim: string, source: 'assertion' | 'conclusion', step: number, ctx: ProofContext) {
  const dependency = findAndElimDependency(claim, ctx);
  return {
    content: claim,
    source,
    step,
    rule: 'AND_ELIM' as const,
    dependsOn: dependency?.claims ?? [],
    dependsOnIds: dependency?.ids ?? [],
  };
}

function buildSubsetElimProofObject(claim: string, source: 'assertion' | 'conclusion', step: number, ctx: ProofContext) {
  const dependency = findSubsetElimDependency(claim, ctx);
  return {
    content: claim,
    source,
    step,
    rule: 'SUBSET_ELIM' as const,
    dependsOn: dependency?.claims ?? [],
    dependsOnIds: dependency?.ids ?? [],
  };
}

function buildImpliesIntroProofObject(claim: string, source: 'assertion' | 'conclusion', step: number, ctx: ProofContext) {
  const dependency = findImplicationIntroDependency(claim, ctx);
  const outputClaim = implicationOutputClaim(claim, ctx);
  return {
    content: outputClaim,
    source,
    step,
    rule: 'IMPLIES_INTRO' as const,
    dependsOn: dependency?.claims ?? [],
    dependsOnIds: dependency?.ids ?? [],
  };
}

function buildContradictionDischargeProofObject(claim: string, source: 'assertion' | 'conclusion', step: number, ctx: ProofContext) {
  const dependency = findContradictionDependency(ctx);
  return {
    content: claim,
    source,
    step,
    rule: 'CONTRADICTION' as const,
    dependsOn: dependency?.claims ?? [],
    dependsOnIds: dependency?.ids ?? [],
  };
}

function findImplicationElimDependency(
  claim: string,
  ctx: ProofContext,
): { claims: string[]; ids: string[] } | null {
  for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
    const item = ctx.proofObjects[i];
    const implication = parseImplicationProp(item.claim);
    if (!implication) continue;
    const [antecedent, consequent] = implication;
    if (!sameProp(consequent, claim)) continue;
    const antecedentObject = findLatestProofObjectByClaim(ctx, antecedent);
    if (antecedentObject) {
      return {
        claims: [antecedent, item.claim],
        ids: [antecedentObject.id, item.id],
      };
    }
  }
  return null;
}

function findAndIntroDependency(
  claim: string,
  ctx: ProofContext,
): { claims: string[]; ids: string[] } | null {
  const conjunction = parseConjunctionProp(claim);
  if (!conjunction) return null;
  const left = findLatestProofObjectByClaim(ctx, conjunction[0]);
  const right = findLatestProofObjectByClaim(ctx, conjunction[1]);
  if (!left || !right) return null;
  return {
    claims: [conjunction[0], conjunction[1]],
    ids: uniqueIds([left.id, right.id]),
  };
}

function findAndElimDependency(
  claim: string,
  ctx: ProofContext,
): { claims: string[]; ids: string[] } | null {
  for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
    const item = ctx.proofObjects[i];
    const conjunction = parseConjunctionProp(item.claim);
    if (!conjunction) continue;
    const [left, right] = conjunction;
    if (sameProp(left, claim) || sameProp(right, claim)) {
      return { claims: [item.claim], ids: [item.id] };
    }
  }
  return null;
}

function findSubsetElimDependency(
  claim: string,
  ctx: ProofContext,
): { claims: string[]; ids: string[] } | null {
  const output = parseMembershipProp(claim);
  if (!output) return null;
  const subsetCandidate = findLatestProofObject(ctx, object => {
    const subset = parseSubsetProp(object.claim);
    return subset !== null && sameProp(subset.right, output.set);
  });
  if (!subsetCandidate) return null;
  const subset = parseSubsetProp(subsetCandidate.claim);
  if (!subset) return null;
  const membershipCandidate = findLatestProofObject(ctx, object => {
    const membership = parseMembershipProp(object.claim);
    return membership !== null &&
      sameProp(membership.element, output.element) &&
      sameProp(membership.set, subset.left);
  });
  if (!membershipCandidate) return null;
  return {
    claims: [membershipCandidate.claim, subsetCandidate.claim],
    ids: uniqueIds([membershipCandidate.id, subsetCandidate.id]),
  };
}

function findImplicationIntroDependency(
  claim: string,
  ctx: ProofContext,
): { claims: string[]; ids: string[] } | null {
  const implication = ctx.goal ? parseImplicationProp(ctx.goal) : parseImplicationProp(claim);
  if (!implication) return null;
  const antecedentObject = findLatestProofObjectByClaim(ctx, implication[0], object => object.source === 'assumption');
  const consequentObject = findLatestProofObjectByClaim(ctx, implication[1]);
  if (!antecedentObject || !consequentObject) return null;
  return {
    claims: [implication[0], implication[1]],
    ids: uniqueIds([antecedentObject.id, consequentObject.id]),
  };
}

function findContradictionDependency(ctx: ProofContext): { claims: string[]; ids: string[] } | null {
  const contradiction = findContradictionProofObjects(ctx);
  if (!contradiction) return null;
  return {
    claims: [contradiction.a.claim, contradiction.b.claim],
    ids: uniqueIds([contradiction.a.id, contradiction.b.id]),
  };
}

function findContradictionPair(established: Claim[]): { a: string; b: string } | null {
  for (const claim of established) {
    const negated = negateProp(claim.content);
    if (established.some(other => sameProp(other.content, negated))) {
      return { a: claim.content, b: negated };
    }
  }
  return null;
}

function findContradictionProofObjects(
  ctx: ProofContext,
): { a: ProofObject; b: ProofObject } | null {
  for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
    const candidate = ctx.proofObjects[i];
    const negated = negateProp(candidate.claim);
    const opposite = findLatestProofObjectByClaim(ctx, negated);
    if (opposite) {
      return { a: candidate, b: opposite };
    }
  }
  return null;
}

function negateProp(claim: string): string {
  const value = claim.trim();
  if (value.startsWith('¬')) return value.slice(1).trim();
  if (value.startsWith('not ')) return value.slice(4).trim();
  return `¬${value}`;
}

function uniqueProps(values: string[]): string[] {
  const unique: string[] = [];
  for (const value of values) {
    if (!unique.some(existing => sameProp(existing, value))) {
      unique.push(value);
    }
  }
  return unique;
}

function uniqueIds(values: string[]): string[] {
  return [...new Set(values.filter(Boolean))];
}

function resolveClaimIds(ctx: ProofContext, claims: string[]): string[] {
  const resolved: string[] = [];
  for (const claim of claims) {
    const matches = ctx.established.filter(item => sameProp(item.content, claim) && item.proofObjectId);
    if (matches.length > 0) {
      resolved.push(matches[matches.length - 1].proofObjectId!);
    }
  }
  return uniqueIds(resolved);
}

function findLatestProofObjectByClaim(
  ctx: ProofContext,
  claim: string,
  predicate?: (object: ProofObject) => boolean,
): ProofObject | null {
  for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
    const object = ctx.proofObjects[i];
    if (sameProp(object.claim, claim) && (!predicate || predicate(object))) {
      return object;
    }
  }
  return null;
}

function findLatestProofObject(
  ctx: ProofContext,
  predicate: (object: ProofObject) => boolean,
): ProofObject | null {
  for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
    const object = ctx.proofObjects[i];
    if (predicate(object)) return object;
  }
  return null;
}

function validateProofObjectInput(input: {
  content: string;
  rule: CheckResult['rule'];
  dependsOn: string[];
  dependsOnIds?: string[];
}): CheckResult | null {
  const dependsOnIds = input.dependsOnIds ?? [];
  const minimum = minimumDependencyCount(input.rule, input.dependsOn);
  if (dependsOnIds.length >= minimum) return null;
  if (minimum === 0) return null;
  return {
    valid: false,
    rule: input.rule,
    message: `Could not resolve proof-object references for '${input.content}' under ${input.rule}`,
    hint: `Expected ${minimum} dependency reference(s), resolved ${dependsOnIds.length}.`,
  };
}

function minimumDependencyCount(rule: CheckResult['rule'], dependsOn: string[]): number {
  switch (rule) {
    case 'PREMISE':
      return 1;
    case 'IMPLIES_ELIM':
      return uniqueProps(dependsOn).length;
    case 'AND_INTRO':
      return uniqueProps(dependsOn).length;
    case 'AND_ELIM':
      return 1;
    case 'SUBSET_ELIM':
      return uniqueProps(dependsOn).length;
    case 'IMPLIES_INTRO':
      return uniqueProps(dependsOn).length;
    case 'CONTRADICTION':
      return uniqueProps(dependsOn).length;
    case 'BY_LEMMA':
      return uniqueProps(dependsOn).length;
    default:
      return 0;
  }
}

function theoremGoalHint(goalExpr: ExprNode): string {
  const implication = splitImplication(goalExpr);
  if (implication) {
    const [antecedent, consequent] = implication;
    return `For a simple demo proof, start with assume(${antecedent}) and finish by concluding ${consequent}.`;
  }
  const conjunction = splitGoalConjunction(goalExpr);
  if (conjunction) {
    const [left, right] = conjunction;
    return `Establish both '${left}' and '${right}', then conclude the conjunction or leave both as derived steps.`;
  }
  return 'Finish the proof with conclude(<theorem claim>) or an equivalent final asserted result.';
}

function isCheckableGoal(expr: ExprNode): boolean {
  switch (expr.type) {
    case 'Atom':
      return expr.atomKind !== 'opaque';
    case 'And':
    case 'Or':
    case 'Implies':
    case 'Iff':
      return isCheckableGoal(expr.left) && isCheckableGoal(expr.right);
    case 'Not':
      return isCheckableGoal(expr.operand);
    default:
      return false;
  }
}

function parseFallbackDiagnostic(expr: ExprNode, label: string): Diagnostic | null {
  if (expr.type !== 'Atom' || expr.atomKind !== 'opaque') return null;
  const atom = expr as AtomNode;
  const reason = atom.parseError
    ? `The parser fell back to an opaque symbolic claim: ${atom.parseError}`
    : `The parser accepted this as an opaque symbolic claim.`;
  const mathHint = parserFallbackHint(atom.condition);
  return {
    severity: 'info',
    message: `${label} is outside the current parser/checker subset. ${reason}`,
    rule: 'STRUCTURAL',
    hint: mathHint,
  };
}

function containsMathNotation(value: string): boolean {
  return /[∀∃∈∉⊆⊂≤≥≠ℕℤℚℝ]/.test(value);
}

function parserFallbackHint(value: string): string {
  if (/[∀∃]/.test(value)) {
    return `This looks like quantified mathematics. Keep the MI-style notation if you want, but use 'fl verify' until quantifier semantics are part of the fast checker subset.`;
  }
  if (/[∈∉⊆⊂]/.test(value)) {
    return `This looks like set-theoretic notation. The fast checker currently verifies only a small set-theoretic subset such as membership identities and subset transport; otherwise use 'fl verify'.`;
  }
  if (/:\s*[\wℕℤℚℝ]/.test(value) || /→|⇒/.test(value)) {
    return `This looks like typed or function-style mathematical notation. Keep the MI-style syntax if you want, but use 'fl verify' outside the fast checker subset.`;
  }
  if (containsMathNotation(value)) {
    return `This looks like mathematical notation. Keep the MI-style syntax if you want, but use 'fl verify' for richer semantics outside the fast checker subset.`;
  }
  return `Rewrite the expression into the current fast checker subset or use 'fl verify'.`;
}

function checkDerivedClaim(claim: string, ctx: ProofContext): CheckResult | null {
  if (ctx.established.some(item => sameProp(item.content, claim))) {
    return null;
  }

  for (const item of ctx.established) {
    const implication = parseImplicationProp(item.content);
    if (!implication) continue;
    const [antecedent, consequent] = implication;
    if (!sameProp(consequent, claim)) continue;
    const result = checkModusPonens(antecedent, consequent, ctx);
    if (result.valid) return result;
  }

  for (const item of ctx.established) {
    const conjunction = parseConjunctionProp(item.content);
    if (!conjunction) continue;
    const [left, right] = conjunction;
    if (sameProp(left, claim) || sameProp(right, claim)) {
      const result = checkAndElim(claim, item.content, ctx);
      if (result.valid) return result;
    }
  }

  const subsetElim = checkSubsetDerivedClaim(claim, ctx);
  if (subsetElim?.valid) return subsetElim;

  if (ctx.goal && sameProp(ctx.goal, claim)) {
    return {
      valid: false as const,
      rule: 'STRUCTURAL',
      message: `Conclusion '${claim}' is not yet derived from the current context`,
      hint: `Add assumptions or intermediate proof steps that derive '${claim}' from earlier claims.`,
    };
  }

  return null;
}

function checkSubsetDerivedClaim(claim: string, ctx: ProofContext): CheckResult | null {
  const output = parseMembershipProp(claim);
  if (!output) return null;
  for (const item of ctx.established) {
    const subset = parseSubsetProp(item.content);
    if (!subset || !sameProp(subset.right, output.set)) continue;
    const membershipClaim = `${output.element} ∈ ${subset.left}`;
    const result = checkSubsetElim(membershipClaim, item.content, claim, ctx);
    if (result.valid) return result;
  }
  return null;
}

function checkImplicationGoalDischarge(claim: string, ctx: ProofContext): CheckResult | null {
  if (!ctx.goal) return null;
  const implication = parseImplicationProp(ctx.goal);
  if (!implication) return null;

  const [antecedent, consequent] = implication;
  if (!sameProp(consequent, claim)) return null;

  const antecedentAssumed = ctx.established.some(
    item => item.source === 'assumption' && sameProp(item.content, antecedent)
  );
  const consequentEstablished = ctx.established.some(item => sameProp(item.content, consequent));
  return checkImpliesIntro(antecedent, consequent, antecedentAssumed, consequentEstablished);
}

function checkContradictionDischarge(claim: string, ctx: ProofContext): CheckResult | null {
  const contradictionEstablished = ctx.established.some(item => sameProp(item.content, 'contradiction'));
  if (!contradictionEstablished) return null;
  const contradiction = checkContradiction(ctx);
  if (!contradiction.valid) return contradiction;
  return {
    valid: true,
    rule: 'CONTRADICTION',
    message: `Contradiction discharges the current goal: ${claim}`,
  };
}

function checkPremiseClaim(claim: string, ctx: ProofContext): CheckResult | null {
  if (!ctx.goal) return null;
  if (!sameProp(claim, ctx.goal) && !ctx.established.some(item => item.source === 'premise' && sameProp(item.content, claim))) {
    return null;
  }
  return {
    valid: true,
    rule: 'PREMISE',
    message: `Premise available in context: ${claim}`,
  };
}

function parseImplicationProp(prop: string): [string, string] | null {
  const parts = splitTopLevel(prop, '→');
  if (!parts) return null;
  return parts;
}

function parseConjunctionProp(prop: string): [string, string] | null {
  const parts = splitTopLevel(prop, '∧');
  if (!parts) return null;
  return parts;
}

function parseSubsetProp(prop: string): { left: string; right: string } | null {
  const match = stripParens(prop).match(/^(.+?)\s*(⊆|⊂)\s*(.+)$/);
  if (!match) return null;
  return { left: stripParens(match[1].trim()), right: stripParens(match[3].trim()) };
}

function parseMembershipProp(prop: string): { element: string; set: string } | null {
  const match = stripParens(prop).match(/^(.+?)\s*(∈|∉)\s*(.+)$/);
  if (!match) return null;
  return { element: stripParens(match[1].trim()), set: stripParens(match[3].trim()) };
}

function splitTopLevel(prop: string, operator: '→' | '∧'): [string, string] | null {
  let depth = 0;
  for (let i = 0; i < prop.length; i++) {
    const ch = prop[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth = Math.max(0, depth - 1);
    else if (depth === 0 && prop.slice(i, i + operator.length) === operator) {
      const left = stripParens(prop.slice(0, i).trim());
      const right = stripParens(prop.slice(i + operator.length).trim());
      if (left && right) return [left, right];
    }
  }
  return null;
}

function stripParens(value: string): string {
  let result = value.trim();
  while (result.startsWith('(') && result.endsWith(')')) {
    const inner = result.slice(1, -1).trim();
    if (!inner) break;
    if (!hasBalancedParens(inner)) break;
    result = inner;
  }
  return result;
}

function hasBalancedParens(value: string): boolean {
  let depth = 0;
  for (const ch of value) {
    if (ch === '(') depth++;
    else if (ch === ')') {
      depth--;
      if (depth < 0) return false;
    }
  }
  return depth === 0;
}
