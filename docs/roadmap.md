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

| File | Theorems | State |
|------|----------|-------|
| `logic.fl` | 22 | `PROVED` |
| `sets-basic.fl` | 23 | `PROVED` |
| `sets-algebra.fl` | 10 | `PROVED` |
| `order.fl` | 22 | `PROVED` |
| `math.fl` | 151 | `PROVED` |
| `number-theory.fl` | 18 | `PROVED` |
| `algebra.fl` | 16 | `PROVED` |
| `linear-algebra.fl` | 13 | `PROVED` |
| `topology.fl` | 19 | `PROVED` |
| `real-analysis.fl` | 6 | `PROVED` |
| `combinatorics.fl` | 23 | `PROVED` |
| `graph-theory.fl` | 19 | `PROVED` |
| `type-system.fl` | 7 | `PROVED` |
| `crypto.fl` | 6 | `PROVED` |
| `probability.fl` | 15 | `PROVED` |

All 15 library files return `PROVED`. Next kernel priorities:

- Bounded quantifier rules over structured domains (e.g. well-founded induction, ordinals)
- Richer witness construction and inspection for existential elimination
- Extend `Ra` tooling for explicit causal resolution traces
