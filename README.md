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

FuturLang currently has two distinct execution modes:

- `fl <file.fl>`
  Auto-detects proof-shaped programs. If the file contains theorem-prover constructs, `fl` runs theorem-prover check mode automatically; otherwise it runs the JavaScript evaluator for the strict executable subset.
  Standalone theorem/declaration files are presented as declaration-only proof programs instead of as failed paired proofs.
- `fl check <file.fl>`
  Runs the self-contained kernel checker. This validates proof structure through a categorical kernel grounded in a Boolean category with partial maps and a resolution monad.
- `fl web <file.fl> [out-dir]`
  Generates an experimental React app where the FuturLang program is rendered and evaluated as a visible truth chain.

The important boundary is intentional:

- `fl` now defaults to checker behavior for proof-shaped programs
- the JS evaluator is strict and fails closed on unsupported mathematical notation
- the kernel checker is self-contained — no external tools required
- proof objects carry `PROVED` / `PENDING` / `FAILED` status — no silent fallback outside those three states
- pending claims cannot be used as inputs to classical derivation rules before Ra fires

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

- `given(...)`
- `assert(...)`
- `assume(...)`
- `conclude(...)`
- `apply(...)`
- `setVar(...)`
- `let ...`
- `contradiction()`

Each statement also participates in the truth chain.

Their roles are different:

- `given(...)` declares a theorem or lemma premise. It is available to the paired proof from the start.
- `assume(...)` introduces a local proof assumption inside the proof body.
- `assert(...)` states a claim. In theorem and lemma bodies it expresses the claimed result; in proof bodies it expresses an intermediate derived step.
- `conclude(...)` marks the explicit result the proof is discharging.
- `apply(...)` consumes a previously established lemma or theorem when its `given(...)` hypotheses are already in context.
- `contradiction()` marks an explicit contradiction step inside a contradiction-style proof chain.

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
  given(x ∈ A) →
  given(A ⊆ B) →
  assert(x ∈ B)
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
- simple contradiction discharge
- proof-path validation through explicit morphism composition

This is useful feedback, but it is not the same thing as an unrestricted mathematical prover.

## Kernel Verification

`fl check` and proof-shaped `fl` runs use the self-contained kernel checker. No external tools are required.

The checker supports:

- full propositional proof flow in the current kernel subset: `IMPLIES_INTRO`, `IMPLIES_ELIM`, `AND_INTRO`, `AND_ELIM_LEFT`, `AND_ELIM_RIGHT`, `OR_INTRO_LEFT`, `OR_INTRO_RIGHT`, `OR_ELIM`, `NOT_INTRO`, `CONTRADICTION`, `BY_LEMMA`
- set-theoretic rules used by the demo corpus: subset transport and transitivity, equality substitution, union/intersection membership reasoning, image/preimage reasoning, bounded `∀` and `∃` introduction and elimination over membership
- a Boolean-category interpretation where implication is read classically as `¬P ∨ Q`
- a partial-map layer for unresolved domains
- a resolution-monad layer for `ω`-state suspension and Ra-based resolution

Proof object status is exactly `PROVED`, `PENDING`, or `FAILED`. `PENDING` claims cannot be used as inputs to classical derivation rules.

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
- `docs/kernel.md`
- `docs/checker.md`
- `docs/roadmap.md`
- `docs/demo-proofs.md`

If you want the internal prover model rather than just the surface syntax, start with `docs/kernel.md`. That file explains the Boolean-category foundation, partial maps, the resolution monad, and the current trust boundary.

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

- expand the Boolean-category kernel without changing the visible `.fl` surface
- strengthen pending derivation handling around richer quantified and causal-resolution examples
- improve theorem-to-proof source mapping and diagnostics
- grow the web/backend story so programs can act as proof-driven applications
