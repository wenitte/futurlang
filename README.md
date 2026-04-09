# FuturLang

FuturLang is a proof-oriented programming language where every `.fl` file is a single truth-evaluable chain.

## Kernel

The checker is grounded in Wenittain Logic and a Boolean-category kernel with partial maps and a resolution monad.

- propositions are represented internally as objects
- proof steps are represented internally as morphisms
- implication is interpreted classically as `¬P ∨ Q`
- unresolved propositions are carried by resolution-monad suspension
- proof outcomes are exactly `PROVED`, `PENDING`, or `FAILED`
- `ω` is an epistemic state and is blocked by the structural `ω`-Barrier until Ra fires

The surface language does not expose category theory. Users still write chained `theorem`, `proof`, `given`, `assume`, `assert`, `conclude`, `apply`, and `setVar` statements.

## Commands

- `fl <file.fl>`: auto-runs `fl check` for proof-shaped files, otherwise uses the strict JS evaluator
- `fl check <file.fl>`: runs the categorical proof checker
- `fl web <file.fl> [out-dir]`: renders the visible truth chain as a React app

The JS evaluator is intentionally narrower than the checker. Rich mathematical claims should go through `fl check`.

## Example

```fl
theorem SubsetTransport() {
  given(x ∈ A) →
  given(A ⊂ B) →
  assert(x ∈ B)
} ↔

proof SubsetTransport() {
  conclude(x ∈ B)
}
```

## Status Model

- `PROVED`: the checker found a complete classical morphism path from premises to conclusion
- `PENDING`: the derivation is structurally valid but still contains `ω`-valued morphisms
- `FAILED`: the derivation has no valid morphism path or misuses the kernel rules

## Development

```bash
npm install
npm test
```

Key references:

- `docs/spec.md`
- `docs/checker.md`
- `docs/kernel.md`
