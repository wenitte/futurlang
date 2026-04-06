# Demo Proofs

These are the kinds of proofs FuturLang should demo immediately.

## Identity

```fl
theorem Identity() {
  assert(p -> p)
} ↔

proof Identity() {
  assume(p) →
  conclude(p)
}
```

## Conjunction

```fl
theorem Pair() {
  assert(p && q)
} ↔

proof Pair() {
  assume(p) →
  assert(q)
}
```

## Message for Demos

The honest demo pitch is:

"FuturLang already lets you write simple proof-shaped programs as a single truth chain, checks the goal against the proof for a small propositional subset, and routes advanced math toward Lean."
