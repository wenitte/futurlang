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

## Current Architecture

FuturLang currently has three distinct execution modes:

- `fl <file.fl>`
  Runs the JavaScript evaluator for the strict supported subset. This is the fast path for boolean logic, simple variables, string claims, and proof-shaped control flow.
- `fl check <file.fl>`
  Runs the structural checker. This validates theorem/proof pairing and basic proof-shape rules without claiming full semantic verification.
- `fl verify <file.fl>`
  Transpiles FuturLang to Lean 4 and checks it with Mathlib. This is the long-term source of truth for advanced mathematics.
- `fl web <file.fl> [out-dir]`
  Generates an experimental React app where the FuturLang program is rendered and evaluated as a visible truth chain.

The important boundary is intentional:

- the JS evaluator is strict and fails closed on unsupported mathematical notation
- the checker is structural, not fully semantic
- Lean verification is the path for richer formal claims

## Installation

```bash
git clone https://github.com/wenitte/futurlang
cd futurlang
npm install
npm link
```

## Quick Start

```fl
theorem Hello_World() {
  assert("Hello World can be proven")
} ↔

proof Hello_World() {
  let message = "Hello World" →
  assert(message == "Hello World")
}
```

Run it:

```bash
fl test/hello.fl
```

## Language Model

### Top-level blocks

FuturLang currently supports:

- `theorem`
- `proof`
- `lemma`
- `definition`
- `struct`

These blocks are chained together with inter-block connectives:

- `→` or `->`
- `∧` or `&&`
- `↔` or `<->`

### Proof statements

Inside blocks, the main statements are:

- `assert(...)`
- `assume(...)`
- `conclude(...)`
- `apply(...)`
- `setVar(...)`
- `let ...`

Each statement also participates in the truth chain.

## What The Evaluator Supports

The JS evaluator is intentionally narrow. It is designed for a strict executable subset such as:

- boolean variables
- string claims
- equality and simple relational expressions
- logical connectives
- theorem/proof chaining

Examples:

```fl
theorem ModusPonens() {
  let p = true;
  let q = true;
  assert((p && (p -> q)) -> q);
}
```

```fl
theorem Claim() {
  assert("This claim is carried as a proof label");
}
```

## What The Evaluator Rejects

Advanced mathematical notation is no longer silently accepted by the JS backend.

Examples that should go through `fl verify` instead of plain `fl`:

- `∀(n: ℕ) ⇒ n = n`
- `|G| divides |H|`
- set-builder notation
- richer algebraic or typed mathematical syntax

This is deliberate. If FuturLang cannot justify a claim in the strict evaluator, it should reject it rather than pretend it proved it.

## Structural Checking

`fl check` currently focuses on proof shape:

- theorem/proof pairing
- assumptions and assertions
- simple conjunction checks
- contradiction and induction heuristics
- proof richness metrics

This is useful feedback, but it is not the same as formal semantic proof.

## Lean Verification

`fl verify` transpiles FuturLang to Lean 4 and checks the generated source against Mathlib.

This backend is the strategic direction of the project, but it is still incomplete:

- some advanced constructs still lower to `sorry`
- definitions and structs are only partially modeled
- source-to-Lean mapping is still approximate

So the current state is:

- strict subset: executable now
- structural proof feedback: usable now
- full formal verification: partially implemented, promising, not complete

## Testing

Run the full test suite:

```bash
npm test
```

That currently covers:

- parser regression tests
- checker regression tests
- Lean transpilation regression tests
- sample evaluator runs for supported programs
- structural checking for advanced math examples

## Docs

Additional documentation now lives in `docs/`:

- `docs/spec.md`
- `docs/kernel.md`
- `docs/checker.md`
- `docs/verify.md`
- `docs/roadmap.md`
- `docs/demo-proofs.md`

## React Backend

FuturLang now also has an experimental web backend:

```bash
fl web test/hello.fl
```

By default this generates a React app in `generated/futurlang-webapp`.

The generated app:

- preserves the “single truth chain” model
- evaluates the chain in the browser for the strict executable subset
- renders proof steps and the final verdict as UI
- marks unsupported advanced math as failing in the web runtime instead of pretending it passed

## Roadmap

High-leverage next steps:

- make simple proof demos excellent before expanding the surface area
- make the Lean backend authoritative for a narrow fully-supported subset
- replace remaining `sorry`-driven proof steps with real translations
- expand the proof language without weakening the “fail closed” rule
- improve theorem-to-proof source mapping and diagnostics
- grow the web/backend story so programs can act as proof-driven applications
