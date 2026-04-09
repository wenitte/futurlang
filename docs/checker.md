# Checker

`fl check` runs the Boolean-category kernel over the parsed FuturLang chain.

## What It Checks

- theorem/proof pairing
- premise import from `given(...)`
- assumption import from `assume(...)`
- morphism construction for classical implication, conjunction, disjunction, contradiction, complement, and lemma import
- subset, equality, union, intersection, image, and preimage reasoning used by the shipped demos
- bounded `∀` and `∃` rules used in the current proof corpus
- kernel `List(A)` pattern matching with exactly `[]` and `[x, ...rest]`
- structural recursion over `List(A)` tails
- `ω` propagation, partial-map restrictions, and the `ω`-Barrier

## Output

Every paired proof returns exactly one state:

- `PROVED`
- `PENDING`
- `FAILED`
- `UNVERIFIED`

`PENDING` means the derivation is structurally valid but still contains unresolved `ω`-valued morphisms.

`UNVERIFIED` means the checker accepted the surface structure but could not trust the result as kernel-proved. The current shipped example is non-structural recursion on `List(A)`.

## Current Boundary

The checker is broader than the JS evaluator but still narrower than the full FuturLang surface. Unsupported mathematical claims are retained as pending derivations rather than being silently accepted.

## List and Recursion

`List(A)` is now the first kernel parameterized sort.

The checker knows:

- `[]`
- `[x, ...rest]`
- exhaustive two-case list match
- structural recursion on `rest`

If a recursive call is made on the original list rather than the tail, the result is `UNVERIFIED` instead of `PROVED`.
