# Checker

`fl check` is the fast structural and judgment-level checker.

`fl <file.fl>` now routes to this checker automatically when the source is proof-shaped.

## What It Guarantees Today

- theorem/proof names match
- theorem and lemma premises declared with `given(...)` are carried into proof context
- each established fact in the current checker subset is recorded as an internal proof object with dependencies
- rich mathematical expressions that fall outside the fast checker subset now produce explicit parser/checker fallback diagnostics instead of silently disappearing into generic structure
- theorem blocks declare a claim
- proofs are non-empty
- simple paired proofs are checked against the theorem goal
- simple implication demos are accepted when the proof assumes the antecedent and derives the consequent
- simple conjunction demos are accepted when both sides are established
- set-theoretic subset transport is validated in the current kernel subset:
  from `x ∈ A` and `A ⊆ B`, the checker can derive `x ∈ B`
- subset transitivity is validated in the current kernel subset:
  from `A ⊆ B` and `B ⊆ C`, the checker can derive `A ⊆ C`
- equality substitution is validated for membership claims:
  from `x = y` and `x ∈ A`, the checker can derive `y ∈ A`
- union membership introduction is validated:
  from `x ∈ A`, the checker can derive `x ∈ A ∪ B`
- intersection membership introduction and elimination are validated:
  from `x ∈ A` and `x ∈ B`, the checker can derive `x ∈ A ∩ B`
  from `x ∈ A ∩ B`, the checker can derive either component membership
- bounded universal elimination is validated:
  from `∀x ∈ A, P(x)` and `a ∈ A`, the checker can derive `P(a)`
- bounded universal introduction is validated in a narrow witness-scope form:
  from `setVar(a)`, `a ∈ A`, and an explicit derived `P(a)`, the checker can derive `∀x ∈ A, P(x)` when the witness is used as a fresh scoped stand-in
- bounded existential introduction is validated:
  from `a ∈ A` and `P(a)`, the checker can derive `∃x ∈ A, P(x)`
- bounded existential elimination is validated in a narrow witness-scope form:
  from `∃x ∈ A, P(x)`, plus explicit assumptions `a ∈ A` and `P(a)` for a `setVar(a)` witness, the checker can discharge a conclusion that does not mention `a`
- chained set-membership transport proofs are accepted when each step is justified by prior membership and subset facts
- lemma application checks required hypotheses before adding lemma conclusions
- `apply(...)` traces show both consumed lemma hypotheses and imported conclusions
- simple contradiction demos are accepted when the proof explicitly enters contradiction mode, records `contradiction()`, and then discharges the goal
- omitted top-level connectives are rejected before proof checking starts
- parsed-but-unsupported notation now says which kernel rule is missing and tells you when to use `fl verify`

## What It Does Not Guarantee Yet

- full semantic proof soundness
- dependent typing
- definitional equality
- normalization
- rich binder elaboration beyond bounded `∀x ∈ A` elimination and bounded `∃x ∈ A` introduction
- full quantified scope discipline beyond the current narrow `EXISTS_IN_ELIM` witness-shape check
- complete lemma application semantics
- a trusted contradiction kernel

## Demo Guidance

For demos today, prefer proofs like:

- `p -> p`
- `p && q`
- `x ∈ A`, `A ⊆ B` therefore `x ∈ B`
- `(x ∈ A) ∧ (x ∈ B)` therefore `x ∈ A`
- theorem plus matching proof with `given`, `assume`, `assert`, and `conclude`
- chained contradiction demos with an explicit `contradiction()` step
