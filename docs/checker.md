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
- **connective validation between adjacent proof steps** (see below)

## Output

Every paired proof returns exactly one state:

- `PROVED`
- `PENDING`
- `FAILED`
- `UNVERIFIED`

`PENDING` means the derivation is structurally valid but still contains unresolved `ω`-valued morphisms.

`UNVERIFIED` means the checker accepted the surface structure but could not trust the result as kernel-proved. The current shipped example is non-structural recursion on `List(A)`.

## Connective Validation

Inside a proof body, adjacent `assert(...)` and `assume(...)` steps must be joined by the connective that correctly describes their dependency relationship.

**`→` (sequence)**: the current step depends on the previous one. The current step's proof object must have the previous step's proof object in its transitive `inputs`.

**`∧` (parallel)**: the two steps are independent. The current step must NOT transitively depend on the previous step.

Mismatched connectives are reported as errors and cause the proof to return `FAILED`.

### Special cases

**`contradiction()`** is a raw node and does not update the dependency tracker. The connective that governs validation of the step after `contradiction()` is the one on the `assert(...)` immediately before it.

**Reuse steps** (re-proving a claim that already exists in context) create no new proof object and do not update the tracker. The connective governing the step after a reuse step is the one on the last new proof object step.

**`conclude(...)`** is not validated — it closes the proof and is not subject to connective checking.

**After `assume(...)`**: the immediately following derivation step must use `→` (the assumption is its dependency).

### Example

```fl
proof IntersectionCommutativity() {
  setVar(x: Element) →
  assume(x ∈ A ∩ B) →
  assert(x ∈ A) ∧        // independent of x ∈ B (both derived from the same assumption)
  assert(x ∈ B) →
  assert(x ∈ B ∩ A) →
  ...
}
```

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
