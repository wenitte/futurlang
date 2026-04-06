# Roadmap

## Stage 1

Make simple proof demos excellent.

- implication and conjunction proofs should feel reliable
- checker messages should mention the actual theorem goal
- examples should avoid unsupported advanced syntax unless routed through Lean

## Stage 2

Build a small sound core.

- explicit proof objects
- scoped contexts
- theorem application with tracked conclusions
- elimination rules

## Stage 3

Use Lean as a semantic oracle while expanding the core.

- keep the supported subset narrow
- compare FuturLang judgments against Lean outcomes
- eliminate silent fallbacks

## Stage 4

Add elaboration, equality, and richer libraries.

That is the point where FuturLang starts moving from a strong demo language toward a serious prover.
