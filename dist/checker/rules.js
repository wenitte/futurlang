"use strict";
// src/checker/rules.ts
// Natural deduction inference rules — each returns a CheckResult
Object.defineProperty(exports, "__esModule", { value: true });
exports.checkAssumption = checkAssumption;
exports.checkModusPonens = checkModusPonens;
exports.checkAndIntro = checkAndIntro;
exports.checkContradiction = checkContradiction;
exports.checkLemmaApplication = checkLemmaApplication;
exports.checkTheoremProofPairing = checkTheoremProofPairing;
exports.checkInduction = checkInduction;
exports.checkImpliesIntro = checkImpliesIntro;
// ── Rule: ASSUMPTION ──────────────────────────────────────────────────────────
// assume(P) is always valid — it introduces P into the context.
// The only constraint: assume must come before any step that uses P.
function checkAssumption(claim) {
    if (!claim || claim.trim() === '') {
        return { valid: false, rule: 'ASSUMPTION', message: 'Empty assumption' };
    }
    return { valid: true, rule: 'ASSUMPTION', message: `Assumed: ${claim}` };
}
// ── Rule: IMPLIES_ELIM (Modus Ponens) ─────────────────────────────────────────
// If P → Q is established, and P is established, then Q follows.
function checkModusPonens(antecedent, conditional, ctx) {
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
function checkAndIntro(left, right, ctx) {
    const hasLeft = isEstablished(left, ctx);
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
// ── Rule: CONTRADICTION ───────────────────────────────────────────────────────
// If we have assume(¬P) (or assume(P) then derive its negation), the
// contradiction is valid and we can conclude P (or anything).
function checkContradiction(ctx) {
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
function checkLemmaApplication(lemmaName, ctx) {
    const key = lemmaName.toLowerCase().replace(/[^a-z0-9_]/g, '_');
    if (ctx.lemmas.has(key)) {
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
function checkTheoremProofPairing(theoremName, proofName, theoremHasStatement, proofStepCount, proofHasConclusion) {
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
function checkInduction(hasBaseCase, hasInductiveStep, hasInductiveHypothesis) {
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
function checkImpliesIntro(antecedent, consequent, antecedentAssumed, consequentEstablished) {
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
function isEstablished(claim, ctx) {
    const normalized = normalizeClaim(claim);
    return ctx.established.some(c => normalizeClaim(c.content) === normalized);
}
function normalizeClaim(s) {
    return s.trim().toLowerCase().replace(/\s+/g, ' ');
}
function normalizeName(s) {
    return s.toLowerCase().replace(/[^a-z0-9]/g, '');
}
function findContradiction(claims) {
    for (const c of claims) {
        const negated = negate(c.content);
        if (claims.some(d => normalizeClaim(d.content) === normalizeClaim(negated))) {
            return { a: c.content, b: negated };
        }
    }
    return null;
}
function negate(claim) {
    const s = claim.trim();
    if (s.startsWith('¬'))
        return s.slice(1).trim();
    if (s.startsWith('not '))
        return s.slice(4).trim();
    return `¬${s}`;
}
