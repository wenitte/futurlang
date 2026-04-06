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
  assert(q) →
  conclude(p && q)
}
```

## Conjunction Elimination

```fl
theorem LeftProjection() {
  assert((p && q) -> p)
} ↔

proof LeftProjection() {
  assume(p && q) →
  conclude(p)
}
```

## Modus Ponens

```fl
theorem ModusPonens() {
  given(p -> q) →
  assert(q)
} ↔

proof ModusPonens() {
  assume(p) →
  conclude(q)
}
```

## Lemma Application

```fl
lemma ForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof ForwardStep() {
  assume(p) →
  conclude(q)
} →

theorem UsesForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof UsesForwardStep() {
  assume(p) →
  apply(ForwardStep)
}
```

## Multi-Premise Chain

```fl
theorem ChainImplication() {
  given(p -> q) →
  given(q -> r) →
  assert(r)
} ↔

proof ChainImplication() {
  assume(p) →
  assert(q) →
  conclude(r)
}
```

## Conjunction Premise

```fl
theorem RightProjection() {
  given(p && q) →
  assert(q)
} ↔

proof RightProjection() {
  conclude(q)
}
```

## Contradiction

```fl
theorem ExplosionDemo() {
  given(p) →
  given(¬p) →
  assert(q)
} ↔

proof ExplosionDemo() {
  assume(¬q) →
  contradiction() →
  conclude(q)
}
```

This is the current contradiction demo subset.

- `given(p)` and `given(¬p)` seed the proof context with conflicting premises
- `assume(¬q)` marks the proof as a contradiction-style proof
- `contradiction()` records the explicit contradiction step
- `conclude(q)` is then discharged by contradiction in the current checker

## Message for Demos

The honest demo pitch is:

"FuturLang already lets you write simple proof-shaped programs as a single truth chain, checks the goal against the proof for a small propositional subset, and routes advanced math toward Lean."

For wording during demos:

- say `given` for theorem or lemma premises
- say `assume` for local proof assumptions
- say `assert` for claimed or derived facts
- say `conclude` for the explicit final result the proof is discharging
- say `apply` imports a prior lemma after its hypotheses have been satisfied
