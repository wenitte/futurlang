# Demo Proofs

The files in `examples/demo/` are the current checked corpus for the categorical kernel.

They cover:

- implication introduction and elimination
- conjunction and disjunction rules
- contradiction and ex falso
- subset transport and subset transitivity
- equality substitution
- union, intersection, image, and preimage reasoning
- bounded `∀` and `∃` rules over membership
- lemma import via `apply()`
- kernel `List(A)` matching and structural recursion
- inter-block connective validation (`∧` vs `→` between proof blocks)

All demo proofs use current syntax:

- `assume(P)` and `declareToProve(P)` in theorem/lemma declaration bodies
- `prove(P)` for intermediate steps in proof bodies
- `conclude(P)` to close a proof
- `∧` between independent `assume()` calls, `→` from the last `assume()` to `declareToProve()`

Most shipped demo proofs are expected to return `PROVED`.

The explicit exceptions are:

- `list-nonstructural-fail.fl` → `UNVERIFIED` (non-structural recursion on `List`)
- `match-exhaustive-fail.fl` → `FAILED` (intentionally incomplete match coverage)

Notable demos:

- `block-connectives.fl` — shows `∧` and `→` between top-level blocks; the checker enforces that `→` is only valid when the next proof calls `apply()` on the current block
- `subset-transport.fl` — the simplest real kernel rule: `x ∈ A`, `A ⊆ B` → `x ∈ B`
- `contradiction-demo.fl` — local assumption discharged via contradiction
- `lemma-apply.fl` — backward chaining through a proved lemma with `apply()`
- `induction-sum.fl` — desugars to the fold kernel path via structural induction
