# FuturLang (.fl)

A formal proof language that combines mathematical rigor with programming language readability.

## Getting Started

### Installation

```sh
# Clone the repository
git clone https://github.com/wenitte/futurlang
cd futurlang

# Install dependencies
npm install

# Link globally
npm link
```

### Your First Proof

Create a file `hello.fl`:

```fl
theorem Hello() {
  declareToProve(1 = 1)
} ↔

proof Hello() {
  conclude(1 = 1)
}
```

Run it:

```sh
fl hello.fl
```

## Language Features

### Top-Level Blocks

Top-level blocks (`theorem`, `proof`, `lemma`, `definition`, `struct`, `type`, `fn`) are joined by explicit connectives:

- `→` sequence (right block depends on left)
- `∧` parallel blocks
- `↔` pairing (theorem ↔ proof)

### Theorem Structure

```fl
theorem Name() {
  assume(hypothesis) →
  declareToProve(conclusion)
} ↔

proof Name() {
  assume(hypothesis) →
  prove(intermediate step) →
  conclude(conclusion)
}
```

### Proof Statements

- `assume(P)` — introduce a hypothesis
- `prove(P)` — derive an intermediate result
- `conclude(P)` — close the proof
- `apply(LemmaName)` — backward-chain through a lemma
- `setVar(x: T)` — introduce a bound variable
- `contradiction()` — discharge by contradiction
- `obtain(x ∈ S, body)` — destructure an existential

### Connectives Between Proof Steps

Inside a proof, adjacent derivation steps must be connected by:

- `→` when the current step depends on the previous one
- `∧` when the two steps are logically independent

The checker validates these connectives against the kernel's dependency graph. Using `→` when steps are independent (or `∧` when a step genuinely depends on the previous) is a type error.

### Connectives Between Top-Level Blocks

Between top-level blocks the connective must reflect the actual logical relationship:

- `↔` — pairs a `theorem`/`lemma` with its `proof` (always)
- `∧` — the two blocks are independent; the right block does not `apply()` the left
- `→` — the right block depends on the left; the right proof calls `apply(LeftName)`
- `∨` — either block suffices (uncommon at top level)

The checker enforces this: using `→` when the next proof does not call `apply()` on the current block, or using `∧` when it does, is an error.

```fl
// Independent lemmas — joined with ∧
lemma A() { declareToProve(...) } ↔
proof A() { ... } ∧

lemma B() { declareToProve(...) } ↔
proof B() { ... } ∧

// C depends on B — joined with →
lemma C() { assume(...) → declareToProve(...) } ↔
proof C() {
  apply(B) →
  conclude(...)
}
```

### Notation

The parser accepts both symbol and word forms:

| Symbol | Word form |
|--------|-----------|
| `→`, `⇒` | `->` |
| `↔`, `⇔` | `<->` |
| `∧` | `&&` |
| `∨` | `\|\|` |
| `∈` | `in` |
| `⊂` | `subset` |
| `∪` | `union` |
| `∩` | `intersection` |
| `∀` | `forall` |
| `∃` | `exists` |

### Standard Library

The `lib/` directory contains proved lemmas covering:

- `logic.fl` — propositional and predicate logic
- `sets-basic.fl` — subset transport, union/intersection, image/preimage
- `sets-algebra.fl` — commutativity, associativity
- `order.fl` — partial orders, lattices, well-orders
- `math.fl` — arithmetic, modular arithmetic, irrationality
- `number-theory.fl` — divisibility, primes, GCD
- `algebra.fl` — groups, rings, fields
- `linear-algebra.fl` — vector spaces, rank-nullity
- `topology.fl` — open sets, continuity, compactness
- `real-analysis.fl` — limits, completeness, integration
- `combinatorics.fl` — binomial coefficients, counting
- `graph-theory.fl` — paths, trees, connectivity
- `type-system.fl` — type safety, progress, preservation
- `crypto.fl` — RSA, discrete log, zero-knowledge
- `dependent-types.fl` — Pi types, Sigma types, identity types

Import lemmas with:

```fl
import "./lib/logic.fl"
```

### Executable Mode

`.fl` files that contain `fn` declarations without theorem/proof blocks are treated as executable programs:

```sh
fl run server.fl
```

## Proof States

Every checked proof returns exactly one state:

- `PROVED` — fully verified by the kernel
- `PENDING` — valid structure with unresolved `ω`-morphisms
- `FAILED` — connective or derivation error
- `UNVERIFIED` — structure accepted but kernel rule not yet implemented
