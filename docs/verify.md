# Verification

External verification via Lean 4 has been removed.

The FuturLang kernel is now self-contained. All proof checking is performed by the internal natural-deduction checker built into `fl check` (and auto-invoked by `fl` for proof-shaped files).

## What the kernel checks

- Propositional logic: IMPLIES_INTRO, IMPLIES_ELIM, AND_INTRO, AND_ELIM, OR_INTRO_LEFT, OR_INTRO_RIGHT, OR_ELIM, NOT_INTRO, NOT_ELIM (double negation), EX_FALSO, CONTRADICTION
- Set-theoretic rules: SUBSET_ELIM, SUBSET_TRANS, EQUALITY_SUBST, UNION_INTRO, INTERSECTION_INTRO, INTERSECTION_ELIM, FORALL_IN_ELIM, FORALL_IN_INTRO, EXISTS_IN_INTRO, EXISTS_IN_ELIM
- Sort checking: left-side of ∈ must be an Element sort; right-side must be Set; ⊆, ∪, ∩ operands must be Set
- Scope checking: set-theoretic variables must be introduced via given(), assume(), or setVar() before use in conclusions

## Proof object status

Every proof step is classified as one of:

- **PROVED**: a valid derivation chain backs this fact
- **UNVERIFIED**: the claim is in the proof source but no kernel rule can derive it; it is recorded but cannot be used as input to further derivation rules
- **FAILED**: the proof step produced an error-level diagnostic

`fl check` output uses `✓` for PROVED, `~` for UNVERIFIED, and `✗` for FAILED.
