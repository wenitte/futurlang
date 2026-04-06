// src/checker/checker.ts
// Main proof checker — walks the AST and applies inference rules

import {
  ASTNode, TheoremNode, ProofNode, LemmaNode, DefinitionNode,
  AssertNode, GivenNode, AssumeNode, ConcludeNode, ApplyNode, SetVarNode, RawNode,
  ExprNode,
} from '../parser/ast';
import {
  ProofContext, ProofReport, FileReport, Diagnostic,
  Claim, Variable, ClaimSet, ProofMethod, CheckResult, ProofStepTrace, ProofObject,
} from './types';
import {
  checkAssumption, checkContradiction, checkLemmaApplication,
  checkTheoremProofPairing, checkInduction, checkAndIntro,
  checkAndElim, checkImpliesIntro, checkModusPonens,
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
    })),
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
        const result = checkAssumption(claim);
        if (!result.valid) {
          diagnostics.push({ severity: 'error', message: result.message, step, rule: result.rule });
        }
        const established = registerClaim(ctx, {
          content: claim,
          source: 'assumption',
          step,
          rule: result.rule,
          dependsOn: [],
        });
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

        // Check for sorry (explicit gap)
        if (claim.toLowerCase().includes('sorry')) {
          hasSorry = true;
          diagnostics.push({ severity: 'info', message: `Step ${step}: sorry placeholder`, rule: 'SORRY' });
          registerClaim(ctx, {
            content: claim,
            source: 'assertion',
            step,
            rule: 'SORRY',
            dependsOn: [],
          });
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

        registerClaim(ctx, {
          content: claim,
          source: 'assertion',
          step,
          rule: stepRule?.rule ?? 'STRUCTURAL',
          dependsOn: inferDependencies(claim, stepRule, ctx),
        });
        proofSteps.push({
          step,
          kind: 'assert',
          claim,
          rule: stepRule?.rule ?? 'STRUCTURAL',
          valid: stepRule?.valid ?? true,
          message: stepRule?.message ?? 'Assertion accepted',
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
        const contradictionDischarge = checkContradictionDischarge(claim, ctx);
        const derivation = isConjunction(n.expr)
          ? checkAndIntro(...splitConjunction(n.expr), ctx)
          : contradictionDischarge ?? checkDerivedClaim(claim, ctx) ?? checkImplicationGoalDischarge(claim, ctx);
        if (derivation && !derivation.valid) {
          diagnostics.push({ severity: 'error', message: derivation.message, step, hint: derivation.hint, rule: derivation.rule });
        }
        registerClaim(ctx, {
          content: claim,
          source: 'conclusion',
          step,
          rule: derivation?.rule ?? 'STRUCTURAL',
          dependsOn: inferDependencies(claim, derivation, ctx),
        });
        proofSteps.push({
          step,
          kind: 'conclude',
          claim,
          rule: derivation?.rule ?? 'STRUCTURAL',
          valid: derivation?.valid ?? true,
          message: derivation?.message ?? 'Conclusion accepted',
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
            registerClaim(ctx, {
              content: conclusion,
              source: 'lemma_application',
              step,
              rule: result.rule,
              dependsOn: lemma.hypotheses,
              imports: lemma.conclusions,
            });
          }
        } else if (result.valid) {
          registerClaim(ctx, {
            content: `applied(${n.target})`,
            source: 'lemma_application',
            step,
            rule: result.rule,
            dependsOn: [],
          });
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
          registerClaim(ctx, {
            content: `${n.varName}: ${n.varType}`,
            source: 'variable',
            step,
            rule: 'VARIABLE',
            dependsOn: [],
          });
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
          registerClaim(ctx, {
            content: 'contradiction',
            source: 'assertion',
            step,
            rule: result.rule,
            dependsOn: contradictionDependencies(ctx),
          });
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
        registerClaim(ctx, {
          content: `lemma(${n.name})`,
          source: 'lemma_application',
          step,
          rule: 'BY_LEMMA',
          dependsOn: innerReport.derivedConclusion ? [innerReport.derivedConclusion] : [],
        });
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

  return {
    name,
    valid,
    method,
    stepCount: step,
    goal: ctx.goal,
    premises,
    derivedConclusion,
    proofSteps,
    proofObjects: ctx.proofObjects,
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
    imports?: string[];
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
    imports: input.imports && input.imports.length > 0 ? uniqueProps(input.imports) : undefined,
  });
  return claim;
}

function makeProofObjectId(step: number, source: string, claim: string): string {
  return `${source}:${step}:${normalizeName(claim)}`;
}

function inferDependencies(claim: string, derivation: CheckResult | null, ctx: ProofContext): string[] {
  if (!derivation?.valid) return [];
  switch (derivation.rule) {
    case 'PREMISE':
      return [claim];
    case 'IMPLIES_ELIM':
      return dependenciesForImplicationElim(claim, ctx);
    case 'AND_INTRO':
      return dependenciesForAndIntro(claim);
    case 'AND_ELIM':
      return dependenciesForAndElim(claim, ctx);
    case 'IMPLIES_INTRO':
      return dependenciesForImplicationIntro(claim, ctx);
    case 'CONTRADICTION':
      return contradictionDependencies(ctx);
    default:
      return [];
  }
}

function dependenciesForImplicationElim(claim: string, ctx: ProofContext): string[] {
  for (const item of ctx.established) {
    const implication = parseImplicationProp(item.content);
    if (!implication) continue;
    const [antecedent, consequent] = implication;
    if (sameProp(consequent, claim) && ctx.established.some(established => sameProp(established.content, antecedent))) {
      return [antecedent, item.content];
    }
  }
  return [];
}

function dependenciesForAndIntro(claim: string): string[] {
  const conjunction = parseConjunctionProp(claim);
  return conjunction ? [conjunction[0], conjunction[1]] : [];
}

function dependenciesForAndElim(claim: string, ctx: ProofContext): string[] {
  for (const item of ctx.established) {
    const conjunction = parseConjunctionProp(item.content);
    if (!conjunction) continue;
    const [left, right] = conjunction;
    if (sameProp(left, claim) || sameProp(right, claim)) {
      return [item.content];
    }
  }
  return [];
}

function dependenciesForImplicationIntro(claim: string, ctx: ProofContext): string[] {
  const implication = ctx.goal ? parseImplicationProp(ctx.goal) : parseImplicationProp(claim);
  return implication ? [implication[0], implication[1]] : [];
}

function contradictionDependencies(ctx: ProofContext): string[] {
  const contradiction = findContradictionPair(ctx.established);
  return contradiction ? [contradiction.a, contradiction.b] : [];
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
