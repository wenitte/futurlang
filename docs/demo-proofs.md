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
- lemma import
- kernel `List(A)` matching and structural recursion

Most shipped demo proofs are expected to return `PROVED`.

The explicit exception is:

- `list-nonstructural-fail.fl` → `UNVERIFIED`
