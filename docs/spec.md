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

## MI-Style Notation

FuturLang now accepts a broader mathematical-looking surface syntax even when the fast checker only understands a narrow semantic subset.

Examples of notation that now parses cleanly in the current surface language:

- logical implication with `⇒`
- biconditional with `⇔`
- membership and containment symbols such as `∈`, `∉`, `⊆`, `⊂`
- union and intersection symbols such as `∪`, `∩`
- set-oriented grouping such as `(x ∈ A) ∧ (x ∈ B)`
- bounded quantifier surface such as `∀x ∈ A, ...` and `∃x ∈ A, ...`
- order and comparison symbols such as `≤`, `≥`, `≠`
- common mathematical alphabets such as `ℕ`, `ℤ`, `ℚ`, `ℝ`

Word aliases normalize to the same internal surface:

- `forall`, `exists`
- `in`, `not in`
- `subset`, `subseteq`, `strictsubset`
- `union`, `intersection`
- `Nat`, `Int`, `Rat`, `Real`

Important boundary:

- the parser may accept these symbols as propositions or proposition atoms
- the fast checker only proves a narrow propositional subset over them
- richer mathematics should still go through `fl verify`

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
- set-membership atoms such as `x ∈ A`
- subset atoms such as `A ⊆ B`
- subset transport of membership:
  from `x ∈ A` and `A ⊆ B`, derive `x ∈ B`
- subset transitivity:
  from `A ⊆ B` and `B ⊆ C`, derive `A ⊆ C`
- equality substitution on membership:
  from `x = y` and `x ∈ A`, derive `y ∈ A`
- union membership introduction:
  from `x ∈ A`, derive `x ∈ A ∪ B`
- intersection membership introduction and elimination:
  from `x ∈ A` and `x ∈ B`, derive `x ∈ A ∩ B`
  from `x ∈ A ∩ B`, derive `x ∈ A` or `x ∈ B`

Advanced mathematics is not treated as proven by the JS evaluator. It must go through `fl verify`.
