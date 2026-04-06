# Kernel Plan

FuturLang does not yet have a trusted kernel comparable to Lean.

## Near-Term Kernel Direction

The next trustworthy core should check derivations over:

- propositions
- variables and scope
- assumptions
- implication introduction and elimination
- conjunction introduction and elimination
- set-membership transport along subset relations
- theorem and lemma application

## Current State

`fl check` now reasons about an explicit theorem goal for simple paired proofs, and it also records a small internal proof-object layer for the current checker subset.

## Current Internal Model

The checker now has four internal layers:

1. Source syntax

- chained `theorem`, `proof`, `lemma`, `given`, `assume`, `assert`, `conclude`, `apply`

2. Base facts

- theorem premises from `given(...)`
- local proof assumptions from `assume(...)`
- typed variables from `setVar(...)`

These are facts introduced directly into the proof context. They do not need derivation nodes.

3. Proof objects

Every established fact becomes a proof object with:

- a stable id
- a proposition string
- a source such as `premise`, `assumption`, `assertion`, `conclusion`, or `lemma_application`
- the rule associated with how it entered the context
- dependency labels and dependency ids

4. Derivation nodes

Whenever the checker accepts a genuinely derived step in the supported subset, it emits a derivation node with:

- the inference rule
- input proof-object ids
- one output proof-object id

So the checker is no longer only producing trace text. It now builds a small derivation graph.

## What Is Actually Checked

In the current subset, the checker can validate derivation nodes independently of the mutable proof-building pass.

That includes:

- `IMPLIES_ELIM`
- `AND_INTRO`
- `AND_ELIM`
- `SUBSET_ELIM`
- `IMPLIES_INTRO`
- `CONTRADICTION`
- `BY_LEMMA` input resolution

The important point is that these rules now resolve against prior proof objects directly. They are not just rediscovered from a bag of ambient claims after the fact.

For the current math-facing subset, `SUBSET_ELIM` is the clearest example of a genuinely mathematical kernel rule:

- input fact 1: a proof object for `x ∈ A`
- input fact 2: a proof object for `A ⊆ B`
- output fact: a proof object for `x ∈ B`

That rule is validated over explicit derivation-node inputs and output, not merely accepted as a structural trace label.

`IMPLIES_INTRO` is now also self-sufficient in the internal model:

- source may still end with `conclude(p)`
- the internal derived proof object is `p → p` when the theorem goal is an implication
- the derivation node is checked against that implication proof object, not only against the theorem goal text

That layer is still narrow:

- each established fact is recorded with a rule, source, step, and dependencies
- proof objects now also carry links to the proof objects they depend on
- accepted proof steps now also emit explicit derivation nodes with input ids and an output id
- theorem premises become `PREMISE` proof objects
- assumptions, derived conclusions, contradiction steps, and lemma imports become proof objects
- supported rules now construct proof objects directly instead of going through a generic dependency-inference pass
- supported derivation rules now resolve their dependencies from prior proof objects directly
- the checker still accepts only a small subset soundly and remains heuristic outside that subset

So this is not yet a trusted kernel, but it is a real move away from pure trace logging and toward explicit derivation objects.

## What Is Not Yet Kernel-Grade

The current checker is still not a trusted kernel for several reasons:

- many mathematical statements outside the demo subset still fall back to structural acceptance
- some proof meanings are still reconstructed from current context rather than carried explicitly in source
- there is no dependent type theory underneath
- there is no normalization or definitional equality engine
- elaboration is minimal
- theorem and lemma application semantics are still narrow
- the trusted boundary is still too wide compared with Lean

So the correct description is:

- FuturLang now has a small internal derivation graph
- some propositional rules are checked against that graph directly
- the project is moving toward a kernel
- the project does not yet have a small trusted kernel

## Target

Long-term, FuturLang should lower user syntax into a small internal proof object language and typecheck that language independently of frontend syntax sugar.
