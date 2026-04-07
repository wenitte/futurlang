# Roadmap

## Stage 1 — Complete (self-contained kernel)

The internal derivation kernel now covers full propositional logic and the set-theoretic subset.

- Sort system: two base sorts (Set and Element), enforced on ∈, ⊆, ∪, ∩
- Scope model: variables introduced by given/assume/setVar; conclusions scope-checked
- Full propositional rules: IMPLIES_INTRO/ELIM, AND_INTRO/ELIM, OR_INTRO_LEFT/RIGHT, OR_ELIM, NOT_INTRO, NOT_ELIM, EX_FALSO, CONTRADICTION
- Three-way status: PROVED / UNVERIFIED / FAILED
- UNVERIFIED claims are tracked but cannot be used as inputs to derivation rules
- Lean backend removed; kernel is self-contained

## Stage 2 — Build a sound core

- Eliminate remaining UNVERIFIED paths in the demos and examples
- Improve theorem-to-proof source mapping and diagnostics

## Stage 3 — Elaboration and richer libraries

- Equality, function application, and algebraic laws
- Expand the first named lemma libraries for common mathematical facts
- Bounded quantifier introduction with auto-witnessed proofs

## Stage 4 — Expressive mathematics

- Structural induction for natural numbers and lists
- Rich type annotations on setVar
- Towards a serious prover for undergraduate-level mathematics

Visible chaining is a language law. All extensions must preserve the single-chain source model.
