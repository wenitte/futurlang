// src/checker/checker.ts
// Main proof checker — walks the AST and applies inference rules

import {
  ASTNode, TheoremNode, ProofNode, LemmaNode, DefinitionNode,
  AssertNode, AssumeNode, ConcludeNode, ApplyNode, SetVarNode, RawNode,
  ExprNode,
} from '../parser/ast';
import {
  ProofContext, ProofReport, FileReport, Diagnostic,
  Claim, Variable, ClaimSet, ProofMethod,
} from './types';
import {
  checkAssumption, checkContradiction, checkLemmaApplication,
  checkTheoremProofPairing, checkInduction, checkAndIntro,
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

  let theoremCount = 0, proofCount = 0, pairedCount = 0;

  for (const node of nodes) {
    if (node.type === 'Theorem') theoremCount++;
    if (node.type === 'Proof')   proofCount++;
    if (node.type === 'Lemma')   {
      theoremCount++;
      const report = checkProofBlock(node.name, node.body, globalLemmas, 'unknown');
      reports.push(report);
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
  theorem: TheoremNode;
  proof:   ProofNode;
}

function findPairs(nodes: ASTNode[]): TheoremProofPair[] {
  const pairs: TheoremProofPair[] = [];
  for (let i = 0; i < nodes.length; i++) {
    const node = nodes[i];
    if (node.type === 'Theorem' && node.connective === '↔') {
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

function checkPair(thm: TheoremNode, proof: ProofNode, globalLemmas: Map<string, ClaimSet>): ProofReport {
  const diagnostics: Diagnostic[] = [];
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
  const proofReport = checkProofBlock(proof.name, proof.body, globalLemmas, method, theoremGoal);
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
    derivedConclusion: proofReport.derivedConclusion,
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
  goal: string | null = null
): ProofReport {
  const diagnostics: Diagnostic[] = [];
  const ctx: ProofContext = {
    established: [],
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
        ctx.established.push({ content: claim, source: 'assumption', step });
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
          ctx.established.push({ content: claim, source: 'assertion', step });
          break;
        }

        // Check and/intro: if claim is a conjunction, verify both sides
        if (isConjunction(n.expr)) {
          const [left, right] = splitConjunction(n.expr);
          const andResult = checkAndIntro(left, right, ctx);
          if (!andResult.valid) {
            // Warning not error — the conjunction may be introducing new facts
            diagnostics.push({ severity: 'info', message: andResult.message, step, hint: andResult.hint });
          }
        }

        ctx.established.push({ content: claim, source: 'assertion', step });
        assertionCount++;

        // Each assert deepens the chain
        if (n.connective === '→') currentDepth++;
        maxDepth = Math.max(maxDepth, currentDepth);
        break;
      }

      case 'Conclude': {
        const n = node as ConcludeNode;
        const claim = exprToString(n.expr);
        ctx.established.push({ content: claim, source: 'conclusion', step });
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
        if (lemma && lemma.conclusions.length > 0) {
          for (const conclusion of lemma.conclusions) {
            ctx.established.push({ content: conclusion, source: 'lemma_application', step });
          }
        } else {
          ctx.established.push({ content: `applied(${n.target})`, source: 'lemma_application', step });
        }
        if (!result.valid) {
          diagnostics.push({ severity: 'warning', message: result.message, step, rule: result.rule });
        }
        lemmaCount++;
        break;
      }

      case 'SetVar': {
        const n = node as SetVarNode;
        ctx.variables.push({ name: n.varName, type: n.varType, step });
        // Variables are always valid introductions
        if (n.varType) {
          ctx.established.push({
            content: `${n.varName}: ${n.varType}`,
            source: 'variable', step
          });
        }
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
          ctx.established.push({ content: 'contradiction', source: 'assertion', step });
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
        ctx.established.push({ content: `lemma(${n.name})`, source: 'lemma_application', step });
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
    derivedConclusion,
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
      map.set(key, { hypotheses: [], conclusions: statement ? [exprToProp(statement.expr)] : [] });
    }
    if (node.type === 'Definition') {
      const key = normalizeName(node.name);
      map.set(key, { hypotheses: [], conclusions: ['defined'] });
    }
  }
}

function exprToString(expr: ExprNode): string {
  return exprToProp(expr);
}

function nodeToString(node: ASTNode): string {
  switch (node.type) {
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
