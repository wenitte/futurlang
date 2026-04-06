# FuturLang Spec

## Core Execution Model

Every FuturLang file is a single truth-evaluable chain.

- top-level blocks are connected by logical connectives
- statements inside proof-relevant blocks are also connected by logical connectives
- the program is valid only if the folded chain resolves to `true`

## Language Law

Visible chaining is mandatory.

- FuturLang syntax must stay visibly chain-based in source
- new features may not hide logical connectivity behind non-chained declaration forms
- if a construct cannot be lowered from visibly chained source into the single program chain, it does not belong in FuturLang

This is a core language law, not just an implementation detail.

## Current Proof Surface

Official chained surface:

Top-level blocks:

- `theorem`
- `proof`
- `lemma`
- `definition`
- `struct`

Proof statements:

- `given(...)`
- `assert(...)`
- `assume(...)`
- `conclude(...)`
- `apply(...)`
- `setVar(...)`
- `let ...`

Statement roles:

- `given(...)`: theorem or lemma premise
- `assume(...)`: local proof assumption
- `assert(...)`: claim declaration or intermediate derived step
- `conclude(...)`: explicit proof conclusion
- `apply(...)`: theorem or lemma application
- `contradiction()`: explicit contradiction marker inside a proof chain

Compatibility notes:

- unsupported mathematical expressions may still parse as opaque claims for non-JS backends
- some older examples may omit connective markers in places where the intended surface language should keep them visible
- current parser behavior rejects missing connectives between adjacent top-level blocks

## Surface Direction

The intended long-term surface language follows the repository-style FuturLang corpus:

- theorem and lemma blocks may declare premises with `given(...)`
- theorem and lemma blocks declare claims with `assert(...)`
- proof blocks derive conclusions from premises, assumptions, and prior results
- contradiction-style proofs remain chained in visible source by using explicit proof steps like `assume(¬P) → contradiction() → conclude(Q)`
- mathematical notation stays visible in source instead of being rewritten into tactic syntax
- all of this must remain visibly chained in the actual source language

This is the canonical language direction even though the prover core currently supports only a smaller sound subset.

## Current Sound Subset

Today, FuturLang is strongest on simple propositional demos:

- atomic propositions
- implication
- conjunction
- disjunction
- biconditional
- negation
- direct theorem/proof pairing
- first-class theorem premises with `given(...)`

Advanced mathematics is not treated as proven by the JS evaluator. It must go through `fl verify`.
