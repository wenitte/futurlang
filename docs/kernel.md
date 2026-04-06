# Kernel Plan

FuturLang does not yet have a trusted kernel comparable to Lean.

## Near-Term Kernel Direction

The next trustworthy core should check derivations over:

- propositions
- variables and scope
- assumptions
- implication introduction and elimination
- conjunction introduction and elimination
- theorem and lemma application

## Current State

`fl check` now reasons about an explicit theorem goal for simple paired proofs, and it also records a small internal proof-object layer for the current checker subset.

That layer is still narrow:

- each established fact is recorded with a rule, source, step, and dependencies
- theorem premises become `PREMISE` proof objects
- assumptions, derived conclusions, contradiction steps, and lemma imports become proof objects
- the checker still accepts only a small subset soundly and remains heuristic outside that subset

So this is not yet a trusted kernel, but it is a real move away from pure trace logging and toward explicit derivation objects.

## Target

Long-term, FuturLang should lower user syntax into a small internal proof object language and typecheck that language independently of frontend syntax sugar.
