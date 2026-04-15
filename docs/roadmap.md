# Roadmap

## Kernel

- Expand the categorical kernel rule coverage without changing the visible `.fl` surface.
- Tighten pending derivations around richer quantified and causal-resolution examples.
- Extend Ra tooling for explicit witness construction and inspection.
- Preserve the fixed three-way proof result model: `PROVED`, `PENDING`, `FAILED`.
- Keep the JS evaluator narrow and route proof-rich programs through `fl check`.

## Library (`lib/`)

The standard library is the primary vehicle for growing kernel coverage. Each new domain file targets a vertical slice: introduce the lemmas, write proof steps that map to kernel rules, and mark what remains `UNVERIFIED` until the kernel catches up.

Current library files and their kernel coverage status:

| File | Kernel coverage |
|------|----------------|
| `sets-basic.fl` | High — subset transport, transitivity, union/intersection, preimage |
| `sets-algebra.fl` | High — commutativity via double-inclusion |
| `math.fl` | Structural — arithmetic identities, modular arithmetic |
| `number-theory.fl` | Partial — congruence reflexivity/symmetry/transitivity derivable; Bezout/CRT structural |
| `algebra.fl` | Partial — identity/inverse uniqueness, cancellation derivable; ring/field structural |
| `linear-algebra.fl` | Partial — kernel/image subspace derivable; rank-nullity structural |
| `topology.fl` | Partial — continuous preimage/closed chain derivable; compactness/connectedness structural |
| `real-analysis.fl` | Structural |
| `type-system.fl` | Structural |
| `crypto.fl` | Structural |

Next kernel priorities:
- Arithmetic kernel rules (add-zero, mul-one) to promote `math.fl` lemmas from structural to `PROVED`
- Congruence equivalence rules to promote `number-theory.fl` congruence chain
- Group axiom rules to promote `algebra.fl` identity/cancellation proofs
