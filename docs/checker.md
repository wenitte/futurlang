# Checker

`fl check` is the fast structural and judgment-level checker.

## What It Guarantees Today

- theorem/proof names match
- theorem and lemma premises declared with `given(...)` are carried into proof context
- each established fact in the current checker subset is recorded as an internal proof object with dependencies
- theorem blocks declare a claim
- proofs are non-empty
- simple paired proofs are checked against the theorem goal
- simple implication demos are accepted when the proof assumes the antecedent and derives the consequent
- simple conjunction demos are accepted when both sides are established
- lemma application checks required hypotheses before adding lemma conclusions
- `apply(...)` traces show both consumed lemma hypotheses and imported conclusions
- simple contradiction demos are accepted when the proof explicitly enters contradiction mode, records `contradiction()`, and then discharges the goal
- omitted top-level connectives are rejected before proof checking starts

## What It Does Not Guarantee Yet

- full semantic proof soundness
- dependent typing
- definitional equality
- normalization
- rich binder elaboration
- complete lemma application semantics
- a trusted contradiction kernel

## Demo Guidance

For demos today, prefer proofs like:

- `p -> p`
- `p && q`
- theorem plus matching proof with `given`, `assume`, `assert`, and `conclude`
- chained contradiction demos with an explicit `contradiction()` step
