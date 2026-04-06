# FuturLang Spec

## Core Execution Model

Every FuturLang file is a single truth-evaluable chain.

- top-level blocks are connected by logical connectives
- statements inside proof-relevant blocks are also connected by logical connectives
- the program is valid only if the folded chain resolves to `true`

## Current Proof Surface

Top-level blocks:

- `theorem`
- `proof`
- `lemma`
- `definition`
- `struct`

Proof statements:

- `assert(...)`
- `assume(...)`
- `conclude(...)`
- `apply(...)`
- `setVar(...)`
- `let ...`

## Current Sound Subset

Today, FuturLang is strongest on simple propositional demos:

- atomic propositions
- implication
- conjunction
- disjunction
- biconditional
- negation
- direct theorem/proof pairing

Advanced mathematics is not treated as proven by the JS evaluator. It must go through `fl verify`.
