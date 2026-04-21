# FuturLang

FuturLang is an experimental proof-oriented programming language where the entire program is a single chained proposition.

Every `.fl` file is parsed as one truth-evaluable chain. A program succeeds only when that chain resolves to `true`.

## Core Idea

FuturLang treats programs as logical structure first:

- top-level blocks are linked by logical connectives such as `→`, `∧`, and `↔`
- proof steps inside blocks are also chained logically
- the full file is folded into a single proposition
- a program is valid only if the final proposition holds

That means FuturLang is not “proof-themed syntax” layered on top of a normal imperative language. The chain is the program.

Visible chaining is a language law. FuturLang should not evolve toward hidden theorem headers, tactic scripts, or non-chained declaration syntax. If it cannot be written as a visibly connected chain in source, it is not FuturLang.

## Current Architecture

FuturLang has one language surface with a few CLI entrypoints:

- `fl <file.fl>`
  Executes the file. If the file contains theorem-prover constructs, `fl` prints checker output first and then runs the executable path as well.
  Standalone theorem/declaration files are presented as declaration-only proof programs instead of as failed paired proofs.
- `fl check <file.fl>`
  Runs the self-contained kernel checker. This validates proof structure through a categorical kernel grounded in a Boolean category with partial maps and a resolution monad.
- `fl start <file.fl> [out-dir]`
  Starts the app. Server files run directly through the Node runtime. Frontend files generate a React app and launch the Vite dev server.
- `fl web <file.fl> [out-dir]`
  Generates the React app without launching it.

The important boundary is intentional:

- `fl` preserves the single language surface and auto-routes proof-shaped files through checker output before execution
- the JS evaluator is strict and fails closed on unsupported mathematical notation
- the kernel checker is self-contained — no external tools required
- proof objects carry `PROVED` / `PENDING` / `FAILED` / `UNVERIFIED` status
- pending claims cannot be used as inputs to classical derivation rules before Ra fires

## Installation

**npm (recommended)**
```bash
npm install -g futurlang
```

**Homebrew**
```bash
brew tap wenitte/futurlang-
brew install futurlang
```

**VS Code Extension** (syntax highlighting, hover docs, completions)
Search `FuturLang` in the VS Code Extensions panel, or install from the [marketplace](https://marketplace.visualstudio.com/items?itemName=WenitteApiou.futurlang).

**From source**
```bash
git clone https://github.com/wenitte/futurlang
cd futurlang
npm install
npm link
```

## Quick Start

```fl
theorem Hello_World() {
  declareToProve("Hello World can be proven")
} ↔

proof Hello_World() {
  let message = "Hello World" →
  conclude(message == "Hello World")
}
```

Run it:

```bash
fl test/hello.fl
```

## Language Model

### Top-level blocks

FuturLang currently supports:

- `import`
- `fn`
- `theorem`
- `proof`
- `lemma`
- `definition`
- `struct`
- `type`

These blocks are chained together with inter-block connectives:

| Connective | Meaning |
|-----------|---------|
| `↔` | pairs a theorem/lemma with its proof (required) |
| `∧` | the following block does not `apply()` the current one |
| `→` | the following block calls `apply(CurrentName)` |
| `∨` | disjunctive — either block suffices; emits a warning, not yet validated |

### Connectives Between Top-Level Blocks

The connective after a `proof` block must reflect whether the next block's proof calls `apply()` on it:

```fl
lemma ConjRight() {
  assume(P ∧ Q) →
  declareToProve(Q)
} ↔

proof ConjRight() {
  conclude(Q)
} →                   // → because SplitAndUseRight applies ConjRight

theorem SplitAndUseRight() {
  assume(P ∧ Q) →
  declareToProve(Q)
} ↔

proof SplitAndUseRight() {
  apply(ConjRight)
}
```

Using `→` when the next proof does not call `apply()`, or `∧` when it does, causes `FAILED`.

### Proof statements

**Theorem/lemma declaration body:**

- `assume(P)` — declare a hypothesis. Multiple independent hypotheses use `∧` between them.
- `declareToProve(P)` — declare the goal (required, exactly once, last)

Two independent assumptions are written with `∧`:

```fl
theorem Foo() {
  assume(p) ∧
  assume(q) →
  declareToProve(r)
}
```

This is equivalent to the single-conjunct form `assume(p ∧ q) → declareToProve(r)`.

**Proof body:**

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

### What declareToProve and prove actually do

**`declareToProve(P)`** sets the target. It says "here is what I am claiming is true." Nothing is proven yet — you are just writing down what the proof must deliver. The kernel reads it and waits for `conclude(P)` to close it.

In programming terms: it is a return type annotation. `declareToProve(x ∈ B)` means "this block must return a proof of `x ∈ B`."

**`prove(P)`** derives a stepping stone. It says "I can establish this intermediate fact right now, using what I already have in context." The kernel checks that `P` actually follows from the current premises and prior steps, then adds `P` to the pool of known facts available to later steps.

In programming terms: it is a `let` binding where the value is a verified fact. `prove(x ∈ A)` means "compute and store the fact `x ∈ A`."

**`conclude(P)`** is the landing step. It closes the proof by delivering the final claim. The kernel checks that `P` matches the goal set by `declareToProve`.

`declareToProve` is the destination. `prove` is a step on the route. `conclude` is arriving.

### What the kernel does step by step

Here is the SubsetTransport proof walked through plainly:

```fl
theorem SubsetTransport() {
  assume(x ∈ A ∧ A ⊆ B) →
  declareToProve(x ∈ B)
} ↔

proof SubsetTransport() {
  conclude(x ∈ B)
}
```

What happens when the checker runs this:

1. It reads `assume(x ∈ A ∧ A ⊆ B)`. It splits the conjunction and puts two facts into the starting pool: `x ∈ A` and `A ⊆ B`.
2. It reads `declareToProve(x ∈ B)`. It sets the goal: "the proof must end with `x ∈ B`."
3. It enters the proof body and sees `conclude(x ∈ B)`.
4. It checks: can `x ∈ B` be justified from the pool? It finds the rule SUBSET_TRANSPORT: if `x ∈ A` and `A ⊆ B`, then `x ∈ B`. Both are in the pool. Rule fires.
5. The conclusion matches the goal. The kernel returns `PROVED`.

Here is a proof with intermediate steps:

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

Step by step:

1. Pool starts with: `P → Q` and `¬Q`.
2. Goal is set to `¬P`.
3. `assume(P)` — adds `P` to the pool as a local hypothesis.
4. `prove(Q)` — kernel checks: can `Q` be derived? It finds `P` and `P → Q` in the pool. IMPLIES_ELIM fires. `Q` is added to the pool.
5. `contradiction()` — kernel sees `Q` and `¬Q` both in the pool. That is a contradiction. It derives `⊥`.
6. `conclude(¬P)` — from `⊥`, anything follows, including `¬P`. The local assumption `P` is discharged. The conclusion matches the goal. Kernel returns `PROVED`.

Missing connectives between adjacent top-level blocks are syntax errors. If two blocks are related, the relationship must be visible in source.

For the explicit construct-by-construct and rule-by-rule reference, see `docs/language-reference.md`.

## MI-Style Surface

FuturLang is moving toward the repository-style MI syntax rather than tactic syntax.

The current surface now accepts more mathematician-friendly notation such as:

- `⇒` and `⇔`
- `∈`, `∉`, `⊆`, `⊂`
- `∪`, `∩`
- `≤`, `≥`, `≠`
- `ℕ`, `ℤ`, `ℚ`, `ℝ`
- bounded quantifier surface such as `∀x ∈ A, ...` and `∃x ∈ A, ...`

Word-form aliases normalize to the same canonical surface during parsing. Examples:

- `forall`, `exists`
- `in`, `not in`
- `subset`, `subseteq`, `strictsubset`
- `union`, `intersection`
- `Nat`, `Int`, `Rat`, `Real`

These symbols already help the source feel closer to mathematical writing. The important boundary is still the same:

- the parser accepts more notation than the fast checker can semantically prove
- when the parser/checker falls back to structurally present but unresolved claims, FuturLang says so explicitly in checker output
- the checker remains honest about its narrow supported subset
- richer symbolic mathematics should go through `fl check` rather than the JS evaluator

The strongest current math demo path is small set-theoretic reasoning with Unicode notation. FuturLang can now kernel-check examples such as:

```fl
theorem SubsetTransport() {
  assume(x ∈ A ∧ A ⊆ B) →
  declareToProve(x ∈ B)
} ↔

proof SubsetTransport() {
  conclude(x ∈ B)
}
```

That proof is not just parsed nicely. In the current kernel subset, the checker validates the mathematical rule:

- `x ∈ A`
- `A ⊆ B`
- therefore `x ∈ B`

The current kernel subset also validates:

- subset transitivity: from `A ⊆ B` and `B ⊆ C`, derive `A ⊆ C`
- equality substitution on membership claims: from `x = y` and `x ∈ A`, derive `y ∈ A`
- union introduction: from `x ∈ A`, derive `x ∈ A ∪ B`
- intersection introduction and elimination: from `x ∈ A` and `x ∈ B`, derive `x ∈ A ∩ B`; from `x ∈ A ∩ B`, derive either side
- bounded universal elimination: from `∀x ∈ A, P(x)` and `a ∈ A`, derive `P(a)`
- bounded existential introduction: from `a ∈ A` and `P(a)`, derive `∃x ∈ A, P(x)`
- bounded existential elimination in an explicit witness scope: from `∃x ∈ A, P(x)`, open witness `a` with `a ∈ A` and `P(a)`, then discharge a witness-free conclusion

## What The Evaluator Supports

The executable runtime is still intentionally narrow, but it now supports real program structure:

- real `fn` declarations
- `type` constructors and value-level `match`
- `if ... then ... else ...`
- `let ... in ...`
- lambdas
- list literals and `fold`
- imports via `import "./other.fl"`
- a small Node HTTP layer for servers and route dispatch

Server example:

```fl
fn home(req ∈ Request) -> Response {
  conclude(text("home"))
} →

let app = router([
  route("GET", "/", home)
]) →

let server = serve(3000, app)
```

Running that file with either `fl examples/server/hello-http.fl` or `fl start examples/server/hello-http.fl` executes the runtime path directly and prints server startup status in the terminal.

Examples:

```fl
fn length(xs ∈ List(Nat)) -> Nat {
  match xs {
    case [] => conclude(0)
    case [_, ...rest] => conclude(1 + length(rest))
  }
} →

let size = length([1, 2, 3]) →
assert(size == 3)
```

```fl
fn home(req ∈ Request) -> Response {
  conclude(text("home"))
} →

let app = router([
  route("GET", "/", home)
])
```

## What The Evaluator Rejects

Advanced mathematical notation is no longer silently accepted by the JS backend.

Examples that should go through `fl check` instead of plain `fl`:

- `∀(n: ℕ) ⇒ n = n`
- `forall(x: A) implies P(x)`
- `|G| divides |H|`
- set-builder notation
- richer algebraic or typed mathematical syntax

This is deliberate. If FuturLang cannot justify a claim in the strict evaluator, it should reject it rather than pretend it proved it.

## Structural Checking

`fl check` currently focuses on proof shape plus kernel-backed derivation:

- theorem/proof pairing
- assumptions and assertions
- simple conjunction checks
- kernel-checked set-membership transport along subset relations
- kernel-checked subset transitivity
- kernel-checked equality substitution on membership claims
- kernel-checked union/intersection membership reasoning
- kernel-checked bounded quantifier elimination/introduction over set membership
- kernel `List(A)` matching
- structural list recursion
- simple contradiction discharge
- proof-path validation through explicit morphism composition

This is useful feedback, but it is not the same thing as an unrestricted mathematical prover.

## Kernel Verification

`fl check` and proof-shaped `fl` runs use the self-contained kernel checker. No external tools are required.

The checker supports:

- full propositional proof flow in the current kernel subset: `IMPLIES_INTRO`, `IMPLIES_ELIM`, `AND_INTRO`, `AND_ELIM_LEFT`, `AND_ELIM_RIGHT`, `OR_INTRO_LEFT`, `OR_INTRO_RIGHT`, `OR_ELIM`, `NOT_INTRO`, `CONTRADICTION`, `BY_LEMMA`
- set-theoretic rules used by the demo corpus: subset transport and transitivity, equality substitution, union/intersection membership reasoning, image/preimage reasoning, bounded `∀` and `∃` introduction and elimination over membership
- kernel list destructuring and exhaustive list match
- structural recursion checking for `fn` over `List(A)`
- a Boolean-category interpretation where implication is read classically as `¬P ∨ Q`
- a partial-map layer for unresolved domains
- a resolution-monad layer for `ω`-state suspension and Ra-based resolution

Proof object status is exactly `PROVED`, `PENDING`, `FAILED`, or `UNVERIFIED`.

- `PENDING` means unresolved `ω` remains in the proof path
- `UNVERIFIED` means the structure checked, but the result is not trusted as kernel-proved

## Testing

Run the full test suite:

```bash
npm test
```

That currently covers:

- parser regression tests
- checker regression tests for the Wenittain truth tables
- quantifier asymmetry tests
- Ra and `ω`-Barrier tests
- `PROVED` / `PENDING` / `FAILED` status distinction tests
- demo-proof verification across `examples/demo/`

## Docs

Additional documentation now lives in `docs/`:

- `docs/spec.md`
- `docs/language-reference.md`
- `docs/executable.md`
- `docs/kernel.md`
- `docs/checker.md`
- `docs/roadmap.md`
- `docs/demo-proofs.md`

If you want the internal prover model rather than just the surface syntax, start with `docs/kernel.md`. That file explains the Boolean-category foundation, partial maps, the resolution monad, and the current trust boundary.

## React Frontend

FuturLang now has a frontend app path behind `fl start`:

```bash
fl start test/hello.fl
```

For non-server programs, this generates a React app in `generated/futurlang-webapp` and starts the Vite dev server.

If you only want the generated frontend output without launching it:

```bash
fl web test/hello.fl
```

or:

```bash
fl --no-launch start test/hello.fl
```

The generated app:

- preserves the “single truth chain” model
- evaluates the chain in the browser for the executable subset
- renders proof steps and the final verdict as UI
- marks unsupported advanced math as failing in the web runtime instead of pretending it passed

## Example Programs

- list proof demos: `examples/demo/list-length.fl`, `examples/demo/list-sum.fl`, `examples/demo/list-theorem.fl`
- server example: `examples/server/hello-http.fl`

## Standard Library

Reusable math lemmas live in `lib/`. Use `apply(LemmaName)` to import them into proofs.

| File | Domain |
|------|--------|
| `lib/sets-basic.fl` | Set membership, subsets, preimage, image |
| `lib/sets-algebra.fl` | Union/intersection algebra |
| `lib/math.fl` | Arithmetic, even/odd, divisibility, modular arithmetic |
| `lib/number-theory.fl` | GCD, Bezout, Euclid's lemma, CRT, congruences |
| `lib/algebra.fl` | Groups, rings, fields, homomorphisms |
| `lib/linear-algebra.fl` | Vector spaces, linear maps, rank-nullity |
| `lib/topology.fl` | Open/closed sets, continuity, compactness, connectedness |
| `lib/real-analysis.fl` | Limits, IVT, EVT, derivatives |
| `lib/type-system.fl` | Σ-types, Π-types, subtype coercions |
| `lib/crypto.fl` | DH, hash security, commitments, elliptic curves |

To start the server example:

```bash
fl start examples/server/hello-http.fl
```

## Roadmap

High-leverage next steps:

- expand the Boolean-category kernel without changing the visible `.fl` surface
- strengthen pending derivation handling around richer quantified and causal-resolution examples
- improve theorem-to-proof source mapping and diagnostics
- grow the web/backend story so programs can act as proof-driven applications
