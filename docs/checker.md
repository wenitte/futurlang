# Checker

`fl check` runs the Boolean-category kernel over the parsed FuturLang chain.

## What It Checks

- theorem/proof pairing
- premise import from `given(...)`
- assumption import from `assume(...)`
- morphism construction for classical implication, conjunction, disjunction, contradiction, complement, and lemma import
- subset, equality, union, intersection, image, and preimage reasoning used by the shipped demos
- bounded `∀` and `∃` rules used in the current proof corpus
- `ω` propagation, partial-map restrictions, and the `ω`-Barrier

## Output

Every paired proof returns exactly one state:

- `PROVED`
- `PENDING`
- `FAILED`

`PENDING` means the derivation is structurally valid but still contains unresolved `ω`-valued morphisms.

## Current Boundary

The checker is broader than the JS evaluator but still narrower than the full FuturLang surface. Unsupported mathematical claims are retained as pending derivations rather than being silently accepted.
