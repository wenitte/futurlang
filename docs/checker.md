# Checker

`fl check` is the fast structural and judgment-level checker.

## What It Guarantees Today

- theorem/proof names match
- theorem blocks declare a claim
- proofs are non-empty
- simple paired proofs are checked against the theorem goal
- simple implication demos are accepted when the proof assumes the antecedent and derives the consequent
- simple conjunction demos are accepted when both sides are established

## What It Does Not Guarantee Yet

- full semantic proof soundness
- dependent typing
- definitional equality
- normalization
- rich binder elaboration
- complete lemma application semantics

## Demo Guidance

For demos today, prefer proofs like:

- `p -> p`
- `p && q`
- theorem plus matching proof with `assume`, `assert`, and `conclude`
