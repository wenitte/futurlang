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

## MI-Style Membership Identity

```fl
theorem MembershipIdentity() {
  assert((x ∈ A) ⇒ (x ∈ A))
} ↔

proof MembershipIdentity() {
  assume(x ∈ A) →
  conclude(x ∈ A)
}
```

## Set-Theoretic Subset Transport

```fl
theorem SubsetTransport() {
  given(x ∈ A) →
  given(A ⊆ B) →
  assert(x ∈ B)
} ↔

proof SubsetTransport() {
  conclude(x ∈ B)
}
```

This is the first genuinely mathematical set-theory rule in the current kernel subset:

- from `x ∈ A`
- and `A ⊆ B`
- the checker derives `x ∈ B`

## Chained Set-Theoretic Transport

```fl
theorem SubsetChain() {
  given(x ∈ A) →
  given(A ⊆ B) →
  given(B ⊆ C) →
  assert(x ∈ C)
} ↔

proof SubsetChain() {
  assert(x ∈ B) →
  conclude(x ∈ C)
}
```

This shows that the current kernel subset can validate a small chained set-theoretic proof rather than only identity-style symbolic demos.

## Subset Transitivity

```fl
theorem SubsetTransitivity() {
  given(A ⊆ B) →
  given(B ⊆ C) →
  assert(A ⊆ C)
} ↔

proof SubsetTransitivity() {
  conclude(A ⊆ C)
}
```

## Equality Substitution

```fl
theorem EqualitySubstitution() {
  given(x = y) →
  given(x ∈ A) →
  assert(y ∈ A)
} ↔

proof EqualitySubstitution() {
  conclude(y ∈ A)
}
```

## Union Introduction

```fl
theorem UnionIntro() {
  given(x ∈ A) →
  assert(x ∈ A ∪ B)
} ↔

proof UnionIntro() {
  conclude(x ∈ A ∪ B)
}
```

## Intersection Left Projection

```fl
theorem IntersectionLeft() {
  given((x ∈ A) ∧ (x ∈ B)) →
  assert(x ∈ A)
} ↔

proof IntersectionLeft() {
  conclude(x ∈ A)
}
```

This is still conjunction elimination internally, but it reads like a set-theoretic fact because the propositions are membership claims written with Unicode notation.

## Intersection Introduction

```fl
theorem IntersectionIntro() {
  given(x ∈ A) →
  given(x ∈ B) →
  assert(x ∈ A ∩ B)
} ↔

proof IntersectionIntro() {
  conclude(x ∈ A ∩ B)
}
```

## MI-Style Order Identity

```fl
theorem OrderIdentity() {
  assert((x ≤ y) ⇒ (x ≤ y))
} ↔

proof OrderIdentity() {
  assume(x ≤ y) →
  conclude(x ≤ y)
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

For the current math-focused demo path, tighten that slightly:

"FuturLang already validates a small kernel-backed subset of Unicode mathematical proofs, including implication, conjunction, and set-membership transport along subset relations, all written as a single visible truth chain."

That can now be stated more precisely:

"FuturLang already validates a small kernel-backed subset of Unicode and word-form mathematical proofs, including subset transport, subset transitivity, equality substitution on membership claims, and basic union/intersection membership reasoning, all written as a single visible truth chain."

For wording during demos:

- say `given` for theorem or lemma premises
- say `assume` for local proof assumptions
- say `assert` for claimed or derived facts
- say `conclude` for the explicit final result the proof is discharging
- say `apply` imports a prior lemma after its hypotheses have been satisfied
