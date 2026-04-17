# Checker

`fl check` runs the Boolean-category kernel over the parsed FuturLang chain.

## What It Checks

- theorem/proof pairing
- assumption import from `assume(...)`
- morphism construction for classical implication, conjunction, disjunction, contradiction, complement, and lemma import
- subset, equality, union, intersection, image, and preimage reasoning used by the shipped demos
- bounded `∀` and `∃` rules used in the current proof corpus
- kernel `List(A)` pattern matching with exactly `[]` and `[x, ...rest]`
- structural recursion over `List(A)` tails
- `ω` propagation, partial-map restrictions, and the `ω`-Barrier
- **connective validation between adjacent proof steps** (see below)
- **connective validation between top-level blocks** (see below)

## Output

Every paired proof returns exactly one state:

- `PROVED`
- `PENDING`
- `FAILED`
- `UNVERIFIED`

`PENDING` means the derivation is structurally valid but still contains unresolved `ω`-valued morphisms.

`UNVERIFIED` means the checker accepted the surface structure but could not trust the result as kernel-proved. The current shipped example is non-structural recursion on `List(A)`.

## Connective Validation

Inside a proof body, adjacent derivation steps must be joined by the connective that correctly describes their dependency relationship. Steps that participate in connective validation:

- `prove(P)` — derives an intermediate fact
- `apply(Name)` — resolves a lemma; validated when it produces a new derived object
- `assume(P)` — introduces a local hypothesis (next step must use `→`)
- `intro(h)` — strips an implication antecedent (next step must use `→`)
- `obtain(x, ∃...)` — destructures an existential (next step must use `→`)

**`→` (sequence)**: the current step depends on the previous one. The current step's proof object must have the previous step's proof object in its transitive `inputs`.

**`∧` (parallel)**: the two steps are independent. The current step must NOT transitively depend on the previous step.

Mismatched connectives are reported as errors and cause the proof to return `FAILED`.

### Special cases

**`contradiction()`** is a raw node and does not update the dependency tracker. The connective that governs validation of the step after `contradiction()` is the one on the `prove(...)` immediately before it.

**Reuse steps** (re-proving a claim that already exists in context) create no new proof object and do not update the tracker. The connective governing the step after a reuse step is the one on the last new proof object step.

**`conclude(...)`** is not validated — it closes the proof and is not subject to connective checking.

**After `assume(...)`, `intro(...)`, or `obtain(...)`**: the immediately following derivation step must use `→`. All three introduce hypotheses into the local context; whatever follows always depends on them.

### Example

```fl
proof IntersectionCommutativity() {
  setVar(x: Element) →
  assume(x ∈ A ∩ B) →
  prove(x ∈ A) ∧        // independent: both derived from the same assumption
  prove(x ∈ B) →
  prove(x ∈ B ∩ A) →
  ...
}
```

## Inter-Block Connective Validation

Between top-level blocks, the connective must reflect whether the following block's proof calls `apply()` on the current block.

**`∧` (independent)**: the next proof does not call `apply(CurrentName)`. Most blocks in a library file are independent and should use `∧`.

**`→` (dependent)**: the next proof calls `apply(CurrentName)`. Only valid when there is a direct apply dependency.

**`↔`**: always used between a theorem/lemma and its proof.

**`∨` (disjunctive)**: accepted by the parser but not yet validated by the checker. A `warning` diagnostic is emitted; the file does not return `FAILED`.

A wrong `∧`/`→` connective causes the file to return `FAILED`.

### Example

```fl
// A and B are independent — use ∧
lemma ModusPonens() {
  assume(P ∧ (P → Q)) →
  declareToProve(Q)
} ↔
proof ModusPonens() {
  conclude(Q)
} ∧

// ModusTollens does not apply ModusPonens — still ∧
lemma ModusTollens() {
  assume((P → Q) ∧ ¬Q) →
  declareToProve(¬P)
} ↔
proof ModusTollens() {
  assume(P) →
  prove(Q) →
  contradiction() →
  conclude(¬P)
} ∧

// HypSyl applies neither above lemma — ∧
lemma HypSyl() {
  assume((P → Q) ∧ (Q → R)) →
  declareToProve(P → R)
} ↔
proof HypSyl() {
  assume(P) →
  prove(Q) →
  conclude(R)
} →

// UsesHypSyl calls apply(HypSyl) — the ∧ above becomes → here
theorem UsesHypSyl() {
  assume((P → Q) ∧ (Q → R)) →
  declareToProve(P → R)
} ↔
proof UsesHypSyl() {
  apply(HypSyl) →
  conclude(P → R)
}
```

## What declareToProve and prove do

**`declareToProve(P)`** sets the target. It says "here is what I am claiming is true." Nothing is proven yet — you are writing down what the proof must deliver. The kernel reads it and waits for `conclude(P)` to close it.

In programming terms: it is a return type annotation. `declareToProve(x ∈ B)` means "this block must return a proof of `x ∈ B`."

**`prove(P)`** derives a stepping stone. It says "I can establish this intermediate fact right now, using what I already have in context." The kernel checks that `P` actually follows from the current pool of facts, then adds `P` to that pool so later steps can use it.

In programming terms: it is a `let` binding where the value is a verified fact.

**`conclude(P)`** is the landing step. It delivers the final claim and closes the proof. The kernel checks that `P` matches the goal set by `declareToProve`.

`declareToProve` is the destination. `prove` is a step on the route. `conclude` is arriving.

## What the kernel does step by step

### SubsetTransport

```fl
theorem SubsetTransport() {
  assume(x ∈ A ∧ A ⊆ B) →
  declareToProve(x ∈ B)
} ↔

proof SubsetTransport() {
  conclude(x ∈ B)
}
```

1. `assume(x ∈ A ∧ A ⊆ B)` — the conjunction is split; both `x ∈ A` and `A ⊆ B` enter the starting pool.
2. `declareToProve(x ∈ B)` — the goal is set to `x ∈ B`.
3. `conclude(x ∈ B)` — the kernel searches for a rule that yields `x ∈ B`. It finds SUBSET_TRANSPORT: if `x ∈ A` and `A ⊆ B`, then `x ∈ B`. Both are in the pool. Rule fires, conclusion matches goal. Returns `PROVED`.

### ModusTollens

```fl
lemma ModusTollens() {
  assume((P → Q) ∧ ¬Q) →
  declareToProve(¬P)
} ↔

proof ModusTollens() {
  assume(P) →
  prove(Q) →
  contradiction() →
  conclude(¬P)
}
```

1. Pool starts with `P → Q` and `¬Q`. Goal is `¬P`.
2. `assume(P)` — adds `P` to the pool as a local hypothesis.
3. `prove(Q)` — kernel finds `P` and `P → Q`. IMPLIES_ELIM fires. `Q` is added to the pool.
4. `contradiction()` — kernel sees `Q` and `¬Q` both in the pool. That is a contradiction: `⊥` is derived.
5. `conclude(¬P)` — from `⊥` anything follows. The local `P` assumption is discharged. Conclusion matches goal. Returns `PROVED`.

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
