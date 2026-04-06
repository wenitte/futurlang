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

`fl check` now reasons about an explicit theorem goal for simple paired proofs, but it is still not a full proof-term kernel.

## Target

Long-term, FuturLang should lower user syntax into a small internal proof object language and typecheck that language independently of frontend syntax sugar.
