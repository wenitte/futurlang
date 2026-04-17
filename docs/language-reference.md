# Language Reference

## Top-Level Blocks

- `import "./other.fl"`
- `fn name(args...) -> Return { ... }`
- `theorem Name() { ... }`
- `proof Name() { ... }`
- `lemma Name() { ... }`
- `definition Name() { ... }`
- `struct Name() { ... }`
- `type Name = | Variant(...) ...`

Top-level blocks are connected by explicit logical connectives. The checker enforces their semantics:

| Connective | Meaning | Rule |
|-----------|---------|------|
| `↔` | pairing | always between a theorem/lemma and its proof |
| `∧` | independent | the next proof does not `apply()` the current block |
| `→` | dependent | the next proof calls `apply(CurrentName)` |
| `∨` | disjunctive | either block suffices (not currently validated) |

Using the wrong connective between blocks causes `FAILED`. `fn`-desugared blocks are exempt from inter-block connective validation.

`fn` is one surface construct with two runtime paths:

- in executable mode, `fn` compiles to a real function
- in checker mode, `fn` is desugared to a theorem/proof pair

## Statements

Theorem/lemma declaration body:

- `assume(P)` — declare a hypothesis
- `declareToProve(P)` — declare the goal (required, exactly once, last)

Proof body:

- `assume(P)` — introduce a local hypothesis
- `prove(P)` — derive an intermediate result
- `conclude(P)` — close the proof (required)
- `apply(Name)` — backward-chain through a proved lemma
- `setVar(x: T)` — introduce a bound variable
- `contradiction()` — derive `⊥` from conflicting assumptions
- `obtain(x, ∃ y ∈ S, P)` — destructure an existential
- `intro(h)` — strip an implication antecedent
- `rewrite(a = b)` — substitute equals
- `let name = expr` — bind a value
- `match value { case ... => ... }` — case split

## Executable Expressions

The executable subset currently includes:

- literals: `true`, `false`, numbers, strings
- function calls: `f(x, y)`
- lambdas: `fn(x: Nat) => x + 1`
- local expression binding: `let x = expr in body`
- conditionals: `if cond then a else b`
- list literals: `[]`, `[1, 2, 3]`
- logical connectives and comparisons
- value-level `match`

## Data Types

FuturLang currently supports:

- `struct` declarations
- `type` sum declarations
- kernel `List(A)`

List syntax:

- sort: `List(Nat)`
- empty list: `[]`
- list literal: `[1, 2, 3]`
- match pattern: `[x, ...rest]`

## Proof-Side List Rules

Inside `fl check`, `List(A)` is treated as a kernel primitive.

- exhaustive list match is exactly two cases: `[]` and `[x, ...rest]`
- structural recursion on the list tail is accepted
- non-structural recursion is reported as `UNVERIFIED`

## Node Server Helpers

The executable runtime includes a small Node HTTP layer:

- `request(method, url, body?, headers?)`
- `text(body, status?, headers?)`
- `html(body, status?, headers?)`
- `json(value, status?, headers?)`
- `route(method, path, handler)`
- `router(routes, fallback?)`
- `dispatch(handler, req)`
- `serve(port, handler, host?)`

Current stable handler style uses named functions:

```fl
fn home(req ∈ Request) -> Response {
  conclude(text("home"))
} →

let app = router([
  route("GET", "/", home)
])
```

## Notation

The parser accepts both symbol and word forms for common logical and set-theoretic notation, including:

- `→`, `⇒`, `->`
- `↔`, `⇔`, `<->`
- `∧`, `&&`
- `∨`, `||`
- `∈`, `in`
- `⊂`, `subset`
- `∪`, `union`
- `∩`, `intersection`
- `∀`, `forall`
- `∃`, `exists`

The proof checker returns exactly one visible proof state:

- `PROVED`
- `PENDING`
- `FAILED`
- `UNVERIFIED`

`UNVERIFIED` means the checker accepted the proof structure but could not trust the claimed justification as kernel-proved. The current shipped example is non-structural recursion over `List`.
