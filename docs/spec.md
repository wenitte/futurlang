# FuturLang Spec

## Core Law

Every FuturLang file is one visible truth chain.

- top-level blocks are connected by explicit logical connectives
- proof statements inside blocks are also connected explicitly
- missing connectives between adjacent top-level blocks are syntax errors

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

- `given(...)`
- `assert(...)`
- `assume(...)`
- `conclude(...)`
- `apply(...)`
- `setVar(...)`
- `let ...`
- `contradiction()`

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
