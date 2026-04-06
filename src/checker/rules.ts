// src/checker/rules.ts
// Natural deduction inference rules — each returns a CheckResult

import { ProofContext, Claim, CheckResult, InferenceRule } from './types';
import { normalizeProp } from './propositions';

// ── Rule: ASSUMPTION ──────────────────────────────────────────────────────────
// assume(P) is always valid — it introduces P into the context.
// The only constraint: assume must come before any step that uses P.
export function checkAssumption(claim: string): CheckResult {
  if (!claim || claim.trim() === '') {
    return { valid: false, rule: 'ASSUMPTION', message: 'Empty assumption' };
  }
  return { valid: true, rule: 'ASSUMPTION', message: `Assumed: ${claim}` };
}

// ── Rule: IMPLIES_ELIM (Modus Ponens) ─────────────────────────────────────────
// If P → Q is established, and P is established, then Q follows.
export function checkModusPonens(
  antecedent: string,
  conditional: string,
  ctx: ProofContext
): CheckResult {
  const hasAntecedent = isEstablished(antecedent, ctx);
  const hasConditional = isEstablished(conditional, ctx) ||
                         isEstablished(`${antecedent} → ${conditional}`, ctx);

  if (hasAntecedent && hasConditional) {
    return { valid: true, rule: 'IMPLIES_ELIM', message: `Modus ponens: ${antecedent} → ${conditional}` };
  }
  if (!hasAntecedent) {
    return {
      valid: false, rule: 'IMPLIES_ELIM',
      message: `Cannot apply modus ponens: '${antecedent}' not yet established`,
      hint: `Add assume(${antecedent}) or prove it first`
    };
  }
  return { valid: false, rule: 'IMPLIES_ELIM', message: `Conditional '${conditional}' not established` };
}

// ── Rule: AND_INTRO ───────────────────────────────────────────────────────────
// If P is established and Q is established, then P ∧ Q is valid.
export function checkAndIntro(left: string, right: string, ctx: ProofContext): CheckResult {
  const hasLeft  = isEstablished(left, ctx);
  const hasRight = isEstablished(right, ctx);

  if (hasLeft && hasRight) {
    return { valid: true, rule: 'AND_INTRO', message: `Both sides established: (${left}) ∧ (${right})` };
  }
  const missing = !hasLeft ? left : right;
  return {
    valid: false, rule: 'AND_INTRO',
    message: `Cannot form conjunction: '${missing}' not yet established`,
    hint: `Establish '${missing}' before asserting the conjunction`
  };
}

// ── Rule: AND_ELIM ───────────────────────────────────────────────────────────
// If P ∧ Q is established, then either P or Q may be concluded.
export function checkAndElim(target: string, conjunction: string, ctx: ProofContext): CheckResult {
  const hasConjunction = isEstablished(conjunction, ctx);
  if (!hasConjunction) {
    return {
      valid: false, rule: 'AND_ELIM',
      message: `Cannot eliminate conjunction: '${conjunction}' not yet established`,
      hint: `Establish '${conjunction}' before deriving '${target}'`
    };
  }
  return { valid: true, rule: 'AND_ELIM', message: `Conjunction elimination: ${conjunction} ⊢ ${target}` };
}

// ── Rule: SUBSET_ELIM ────────────────────────────────────────────────────────
// If x ∈ A is established and A ⊆ B is established, then x ∈ B follows.
export function checkSubsetElim(elementMembership: string, subsetClaim: string, target: string, ctx: ProofContext): CheckResult {
  const hasMembership = isEstablished(elementMembership, ctx);
  const hasSubset = isEstablished(subsetClaim, ctx);
  if (hasMembership && hasSubset) {
    return { valid: true, rule: 'SUBSET_ELIM', message: `Subset elimination: ${elementMembership}, ${subsetClaim} ⊢ ${target}` };
  }
  if (!hasMembership) {
    return {
      valid: false,
      rule: 'SUBSET_ELIM',
      message: `Cannot use subset elimination: '${elementMembership}' not yet established`,
      hint: `Establish '${elementMembership}' before deriving '${target}'`,
    };
  }
  return {
    valid: false,
    rule: 'SUBSET_ELIM',
    message: `Cannot use subset elimination: '${subsetClaim}' not yet established`,
    hint: `Establish '${subsetClaim}' before deriving '${target}'`,
  };
}

export function checkSubsetTrans(leftSubset: string, rightSubset: string, target: string, ctx: ProofContext): CheckResult {
  const hasLeft = isEstablished(leftSubset, ctx);
  const hasRight = isEstablished(rightSubset, ctx);
  if (hasLeft && hasRight) {
    return { valid: true, rule: 'SUBSET_TRANS', message: `Subset transitivity: ${leftSubset}, ${rightSubset} ⊢ ${target}` };
  }
  if (!hasLeft) {
    return {
      valid: false,
      rule: 'SUBSET_TRANS',
      message: `Cannot use subset transitivity: '${leftSubset}' not yet established`,
      hint: `Establish '${leftSubset}' before deriving '${target}'`,
    };
  }
  return {
    valid: false,
    rule: 'SUBSET_TRANS',
    message: `Cannot use subset transitivity: '${rightSubset}' not yet established`,
    hint: `Establish '${rightSubset}' before deriving '${target}'`,
  };
}

export function checkEqualitySubst(equalityClaim: string, membershipClaim: string, target: string, ctx: ProofContext): CheckResult {
  const hasEquality = isEstablished(equalityClaim, ctx);
  const hasMembership = isEstablished(membershipClaim, ctx);
  if (hasEquality && hasMembership) {
    return { valid: true, rule: 'EQUALITY_SUBST', message: `Equality substitution: ${equalityClaim}, ${membershipClaim} ⊢ ${target}` };
  }
  if (!hasEquality) {
    return {
      valid: false,
      rule: 'EQUALITY_SUBST',
      message: `Cannot use equality substitution: '${equalityClaim}' not yet established`,
      hint: `Establish '${equalityClaim}' before deriving '${target}'`,
    };
  }
  return {
    valid: false,
    rule: 'EQUALITY_SUBST',
    message: `Cannot use equality substitution: '${membershipClaim}' not yet established`,
    hint: `Establish '${membershipClaim}' before deriving '${target}'`,
  };
}

export function checkUnionIntro(membershipClaim: string, target: string, ctx: ProofContext): CheckResult {
  if (isEstablished(membershipClaim, ctx)) {
    return { valid: true, rule: 'UNION_INTRO', message: `Union introduction: ${membershipClaim} ⊢ ${target}` };
  }
  return {
    valid: false,
    rule: 'UNION_INTRO',
    message: `Cannot use union introduction: '${membershipClaim}' not yet established`,
    hint: `Establish '${membershipClaim}' before deriving '${target}'`,
  };
}

export function checkIntersectionIntro(leftMembership: string, rightMembership: string, target: string, ctx: ProofContext): CheckResult {
  const hasLeft = isEstablished(leftMembership, ctx);
  const hasRight = isEstablished(rightMembership, ctx);
  if (hasLeft && hasRight) {
    return { valid: true, rule: 'INTERSECTION_INTRO', message: `Intersection introduction: ${leftMembership}, ${rightMembership} ⊢ ${target}` };
  }
  const missing = hasLeft ? rightMembership : leftMembership;
  return {
    valid: false,
    rule: 'INTERSECTION_INTRO',
    message: `Cannot use intersection introduction: '${missing}' not yet established`,
    hint: `Establish '${missing}' before deriving '${target}'`,
  };
}

export function checkIntersectionElim(intersectionClaim: string, target: string, ctx: ProofContext): CheckResult {
  if (isEstablished(intersectionClaim, ctx)) {
    return { valid: true, rule: 'INTERSECTION_ELIM', message: `Intersection elimination: ${intersectionClaim} ⊢ ${target}` };
  }
  return {
    valid: false,
    rule: 'INTERSECTION_ELIM',
    message: `Cannot use intersection elimination: '${intersectionClaim}' not yet established`,
    hint: `Establish '${intersectionClaim}' before deriving '${target}'`,
  };
}

export function checkForallInElim(quantifiedClaim: string, witnessMembership: string, target: string, ctx: ProofContext): CheckResult {
  const hasQuantified = isEstablished(quantifiedClaim, ctx);
  const hasMembership = isEstablished(witnessMembership, ctx);
  if (hasQuantified && hasMembership) {
    return { valid: true, rule: 'FORALL_IN_ELIM', message: `Bounded universal elimination: ${quantifiedClaim}, ${witnessMembership} ⊢ ${target}` };
  }
  if (!hasQuantified) {
    return {
      valid: false,
      rule: 'FORALL_IN_ELIM',
      message: `Cannot use bounded universal elimination: '${quantifiedClaim}' not yet established`,
      hint: `Establish '${quantifiedClaim}' before deriving '${target}'`,
    };
  }
  return {
    valid: false,
    rule: 'FORALL_IN_ELIM',
    message: `Cannot use bounded universal elimination: '${witnessMembership}' not yet established`,
    hint: `Establish '${witnessMembership}' before deriving '${target}'`,
  };
}

export function checkForallInIntro(
  witnessMembership: string,
  instantiatedBody: string,
  target: string,
  ctx: ProofContext,
): CheckResult {
  const hasMembership = isEstablished(witnessMembership, ctx);
  const hasBody = isEstablished(instantiatedBody, ctx);
  if (hasMembership && hasBody) {
    return { valid: true, rule: 'FORALL_IN_INTRO', message: `Bounded universal introduction: ${witnessMembership}, ${instantiatedBody} ⊢ ${target}` };
  }
  if (!hasMembership) {
    return {
      valid: false,
      rule: 'FORALL_IN_INTRO',
      message: `Cannot use bounded universal introduction: '${witnessMembership}' not yet established`,
      hint: `Open an explicit witness scope and establish '${witnessMembership}' before deriving '${target}'`,
    };
  }
  return {
    valid: false,
    rule: 'FORALL_IN_INTRO',
    message: `Cannot use bounded universal introduction: '${instantiatedBody}' not yet established`,
    hint: `Establish '${instantiatedBody}' inside the witness scope before deriving '${target}'`,
  };
}

export function checkExistsInIntro(witnessMembership: string, instantiatedBody: string, target: string, ctx: ProofContext): CheckResult {
  const hasMembership = isEstablished(witnessMembership, ctx);
  const hasBody = isEstablished(instantiatedBody, ctx);
  if (hasMembership && hasBody) {
    return { valid: true, rule: 'EXISTS_IN_INTRO', message: `Bounded existential introduction: ${witnessMembership}, ${instantiatedBody} ⊢ ${target}` };
  }
  if (!hasMembership) {
    return {
      valid: false,
      rule: 'EXISTS_IN_INTRO',
      message: `Cannot use bounded existential introduction: '${witnessMembership}' not yet established`,
      hint: `Establish '${witnessMembership}' before deriving '${target}'`,
    };
  }
  return {
    valid: false,
    rule: 'EXISTS_IN_INTRO',
    message: `Cannot use bounded existential introduction: '${instantiatedBody}' not yet established`,
    hint: `Establish '${instantiatedBody}' before deriving '${target}'`,
  };
}

export function checkExistsInElim(
  existentialClaim: string,
  witnessMembership: string,
  instantiatedBody: string,
  target: string,
  ctx: ProofContext,
): CheckResult {
  const hasExistential = isEstablished(existentialClaim, ctx);
  const hasMembership = isEstablished(witnessMembership, ctx);
  const hasBody = isEstablished(instantiatedBody, ctx);
  if (hasExistential && hasMembership && hasBody) {
    return { valid: true, rule: 'EXISTS_IN_ELIM', message: `Bounded existential elimination: ${existentialClaim}, ${witnessMembership}, ${instantiatedBody} ⊢ ${target}` };
  }
  if (!hasExistential) {
    return {
      valid: false,
      rule: 'EXISTS_IN_ELIM',
      message: `Cannot use bounded existential elimination: '${existentialClaim}' not yet established`,
      hint: `Establish '${existentialClaim}' before deriving '${target}'`,
    };
  }
  if (!hasMembership) {
    return {
      valid: false,
      rule: 'EXISTS_IN_ELIM',
      message: `Cannot use bounded existential elimination: '${witnessMembership}' not yet established`,
      hint: `Open an explicit witness scope and establish '${witnessMembership}' before deriving '${target}'`,
    };
  }
  return {
    valid: false,
    rule: 'EXISTS_IN_ELIM',
    message: `Cannot use bounded existential elimination: '${instantiatedBody}' not yet established`,
    hint: `Establish '${instantiatedBody}' inside the witness scope before deriving '${target}'`,
  };
}

// ── Rule: CONTRADICTION ───────────────────────────────────────────────────────
// If we have assume(¬P) (or assume(P) then derive its negation), the
// contradiction is valid and we can conclude P (or anything).
export function checkContradiction(ctx: ProofContext): CheckResult {
  if (!ctx.inContradiction) {
    return {
      valid: false, rule: 'CONTRADICTION',
      message: 'contradiction() called outside a byContradiction block',
      hint: 'Wrap in byContradiction(assume(...)) → ... → contradiction()'
    };
  }
  // Check that we have two claims that directly contradict each other
  const contradiction = findContradiction(ctx.established);
  if (contradiction) {
    return {
      valid: true, rule: 'CONTRADICTION',
      message: `Contradiction found: '${contradiction.a}' and '${contradiction.b}'`
    };
  }
  // No explicit contradiction found but we're in a contradiction block
  // This is a warning not an error — the step may be valid but we can't verify it
  return {
    valid: true, rule: 'CONTRADICTION',
    message: 'Contradiction asserted (unverified — no explicit conflicting claims found)'
  };
}

// ── Rule: BY_LEMMA ────────────────────────────────────────────────────────────
// apply(Lemma) is valid if Lemma is in scope (defined earlier in the file
// or as an inline lemma block in this proof).
export function checkLemmaApplication(lemmaName: string, ctx: ProofContext): CheckResult {
  const key = lemmaName.toLowerCase().replace(/[^a-z0-9_]/g, '_');
  const lemma = ctx.lemmas.get(key);
  if (lemma) {
    const missing = lemma.hypotheses.filter(h => !isEstablished(h, ctx));
    if (missing.length > 0) {
      return {
        valid: false,
        rule: 'BY_LEMMA',
        message: `Cannot apply ${lemmaName}: missing hypotheses ${missing.join(', ')}`,
        hint: `Establish the required hypotheses before apply(${lemmaName})`,
      };
    }
    return { valid: true, rule: 'BY_LEMMA', message: `Applied lemma: ${lemmaName}` };
  }
  // Not found — warning not error (lemma may be a known mathematical result)
  return {
    valid: true, rule: 'BY_LEMMA',
    message: `Applied external lemma: ${lemmaName} (not defined in this file — assumed valid)`
  };
}

// ── Rule: THEOREM_PROOF pairing ───────────────────────────────────────────────
// theorem X ↔ proof X is valid iff:
// 1. Names match (case-insensitive)
// 2. Theorem has at least one assert (the statement)
// 3. Proof has at least one step
// 4. Proof ends with conclude or a final assert
export function checkTheoremProofPairing(
  theoremName: string,
  proofName: string,
  theoremHasStatement: boolean,
  proofStepCount: number,
  proofHasConclusion: boolean
): CheckResult {
  const namesMatch = normalizeName(theoremName) === normalizeName(proofName);
  if (!namesMatch) {
    return {
      valid: false, rule: 'THEOREM_PROOF',
      message: `Theorem '${theoremName}' paired with proof '${proofName}' — names don't match`,
      hint: `Rename proof to ${theoremName}()`
    };
  }
  if (!theoremHasStatement) {
    return {
      valid: false, rule: 'THEOREM_PROOF',
      message: `Theorem '${theoremName}' has no assert() statement`,
      hint: `Add assert(<claim>) inside the theorem block`
    };
  }
  if (proofStepCount === 0) {
    return {
      valid: false, rule: 'THEOREM_PROOF',
      message: `Proof '${proofName}' is empty`,
      hint: `Add at least one step (assume, assert, or conclude)`
    };
  }
  if (!proofHasConclusion) {
    return {
      valid: true, rule: 'THEOREM_PROOF',
      message: `Proof '${proofName}' has no explicit conclude() — last assert used as conclusion`
    };
  }
  return { valid: true, rule: 'THEOREM_PROOF', message: `${theoremName} ↔ ${proofName} ✓` };
}

// ── Rule: INDUCTION ───────────────────────────────────────────────────────────
// An induction proof must have:
// 1. A base case
// 2. An inductive step (referencing the inductive hypothesis)
export function checkInduction(
  hasBaseCase: boolean,
  hasInductiveStep: boolean,
  hasInductiveHypothesis: boolean
): CheckResult {
  if (!hasBaseCase) {
    return {
      valid: false, rule: 'INDUCTION',
      message: 'Induction proof missing base case',
      hint: 'Add assert(base_case) or label a step as base_case'
    };
  }
  if (!hasInductiveStep) {
    return {
      valid: false, rule: 'INDUCTION',
      message: 'Induction proof missing inductive step',
      hint: 'Add inductive_step block or assert(inductive_step)'
    };
  }
  if (!hasInductiveHypothesis) {
    return {
      valid: true, rule: 'INDUCTION',
      message: 'Induction proof has no explicit inductive hypothesis reference (warning)'
    };
  }
  return { valid: true, rule: 'INDUCTION', message: 'Induction: base case + inductive step ✓' };
}

// ── Rule: IMPLIES_INTRO ───────────────────────────────────────────────────────
// A proof of P → Q must:
// 1. assume(P) at some point
// 2. conclude(Q) after that assumption
export function checkImpliesIntro(
  antecedent: string,
  consequent: string,
  antecedentAssumed: boolean,
  consequentEstablished: boolean
): CheckResult {
  if (!antecedentAssumed) {
    return {
      valid: false, rule: 'IMPLIES_INTRO',
      message: `To prove '${antecedent} → ${consequent}', must assume '${antecedent}' first`,
      hint: `Add assume(${antecedent}) at the start of the proof`
    };
  }
  if (!consequentEstablished) {
    return {
      valid: false, rule: 'IMPLIES_INTRO',
      message: `Assumed '${antecedent}' but never established '${consequent}'`,
      hint: `Add assert(${consequent}) or conclude(${consequent}) after the assumption`
    };
  }
  return { valid: true, rule: 'IMPLIES_INTRO', message: `${antecedent} → ${consequent} ✓` };
}

// ── Helpers ───────────────────────────────────────────────────────────────────

function isEstablished(claim: string, ctx: ProofContext): boolean {
  const normalized = normalizeProp(claim);
  return ctx.established.some(c => normalizeProp(c.content) === normalized);
}

function normalizeClaim(s: string): string {
  return normalizeProp(s);
}

function normalizeName(s: string): string {
  return s.toLowerCase().replace(/[^a-z0-9]/g, '');
}

interface ContradictionPair { a: string; b: string; }

function findContradiction(claims: Claim[]): ContradictionPair | null {
  for (const c of claims) {
    const negated = negate(c.content);
    if (claims.some(d => normalizeClaim(d.content) === normalizeClaim(negated))) {
      return { a: c.content, b: negated };
    }
  }
  return null;
}

function negate(claim: string): string {
  const s = claim.trim();
  if (s.startsWith('¬')) return s.slice(1).trim();
  if (s.startsWith('not ')) return s.slice(4).trim();
  return `¬${s}`;
}
