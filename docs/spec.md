# FuturLang Spec

## Core Law

Every FuturLang file is one visible truth chain.

- top-level blocks are connected by explicit logical connectives
- proof statements inside blocks are also connected explicitly
- missing connectives between adjacent top-level blocks are syntax errors

Inter-block connectives are validated by the checker:

- `↔` — pairs a theorem/lemma declaration with its proof (required)
- `∧` — the following block is independent; its proof does not call `apply()` on the current block
- `→` — the following block depends on the current one; its proof calls `apply(CurrentName)`
- `∨` — disjunctive relationship (uncommon; not validated by the checker)

Using `→` when the next proof does not call `apply()` on the current block, or using `∧` when it does, causes `FAILED`.

## Surface Blocks

- `import`
- `fn`
- `theorem`
- `proof`
- `lemma`
- `definition`
- `struct`
- `type`

## Proof Statements

- `assume(...)`
- `prove(...)`
- `conclude(...)`
- `apply(...)`
- `setVar(...)`
- `let ...`
- `contradiction()`
- `obtain(...)`
- `intro(...)`
- `rewrite(...)`

Adjacent proof statements inside a proof body are connected by explicit connectives:

- `→` when the current step's derivation depends on the previous step
- `∧` when the two steps are independent of each other

The checker validates these connectives against the kernel's `inputs` graph. A mismatch is a type error that causes `FAILED`.

Steps that participate in connective validation:

| Step | Role | Next step rule |
|------|------|---------------|
| `prove(P)` | derives a fact | validated normally via `inputs` graph |
| `apply(Name)` | resolves a lemma | validated normally when a new object is created |
| `assume(P)` | introduces a hypothesis | next step must use `→` |
| `intro(h)` | strips implication antecedent | next step must use `→` |
| `obtain(x, ∃...)` | destructures existential | next step must use `→` |
| `conclude(P)` | closes the proof | not validated |
| `setVar(x: T)` | binds a variable | not validated (creates no proof object) |
| `rewrite(a = b)` | substitutes in goal | not validated (mutates context) |
| `contradiction()` | derives ⊥ | not validated (see special cases) |

## Executable Expressions

The executable subset currently includes:

- `if cond then a else b`
- `let x = expr in body`
- `fn(x: T) => body`
- value-level `match`
- list literals
- `fold(xs, init, f)`

## Kernel List

`List(A)` is now a kernel primitive.

- `[]` is the empty list
- `[x, ...rest]` is the head/tail pattern
- exhaustive checker-side list match is exactly those two cases
- recursion is trusted only on `rest`
- non-structural recursion is `UNVERIFIED`

## Semantics

The kernel is grounded in Wenittain Logic with truth values `0`, `1`, and `ω`.

- `ω` is epistemic indeterminacy
- `Ra` resolves pending morphisms under a total causal witness
- implication is interpreted classically as `¬P ∨ Q`
- complements are primitive in the Boolean category
- unresolved propositions are suspended by the resolution monad
- conjunction, disjunction, and implication follow the WL-WL-001 tables, not Kleene logic
- `∀` and `∃` are evaluated independently

## Tooling Boundary

- `fl check` runs the proof kernel
- `fl` uses the proof kernel automatically for proof-shaped programs
- the executable runtime covers a growing but still strict subset
- Node HTTP helpers exist only in executable mode
