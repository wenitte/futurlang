# Language Reference

This file is the explicit reference for the current FuturLang surface language and the current checker's composability rules.

## Program Shape

Every `.fl` file is one visible truth chain.

Two composition levels matter:

- top-level block composition
- statement composition inside blocks

Both must be written explicitly with visible connectives.

## Top-Level Constructs

### `theorem Name() { ... }`

Purpose:
- declares a named claim
- may also declare premises with `given(...)`
- is usually paired with a later `proof Name() { ... }`

Composition rules:
- may be chained to the next top-level block with `→`, `∧`, or `↔`
- if it is paired with a proof, the intended connective is `↔`
- missing top-level connectives between adjacent blocks are syntax errors

### `proof Name() { ... }`

Purpose:
- provides the proof body for a theorem or lemma
- is checked against the paired theorem goal when a matching theorem or lemma exists

Composition rules:
- may be chained to the next top-level block with `→`, `∧`, or `↔`
- inside the block, proof steps are also chained explicitly

### `lemma Name() { ... }`

Purpose:
- declares a reusable intermediate result
- may have `given(...)` premises and an `assert(...)` claim
- may be paired with a later `proof Name() { ... }`

Composition rules:
- behaves like a theorem for pairing and checking
- may be imported later with `apply(Name)`

### `definition Name() { ... }`

Purpose:
- reserved definitional block in the current language surface

Composition rules:
- participates in the visible top-level chain
- checker semantics are still limited compared with theorem/proof blocks

### `struct Name() { ... }`

Purpose:
- reserved structural declaration block in the current language surface

Composition rules:
- participates in the visible top-level chain
- checker semantics are still limited compared with theorem/proof blocks

## Statement Constructs

### `given(P)`

Purpose:
- introduces a theorem or lemma premise

Where it is used:
- theorem bodies
- lemma bodies

Composition rules:
- each `given(...)` is available as a `PREMISE` fact in the paired proof context from the start
- multiple `given(...)` statements compose by simple accumulation of premises

### `assert(P)`

Purpose:
- states a claim

Where it is used:
- theorem and lemma bodies: declares the goal
- proof bodies: introduces an intermediate derived step

Composition rules:
- in theorem and lemma bodies, the first `assert(...)` is the claimed result checked against the paired proof
- in proof bodies, `assert(...)` may be structural, premise-backed, or kernel-derived depending on context

### `assume(P)`

Purpose:
- introduces a local proof assumption

Where it is used:
- proof bodies

Composition rules:
- each assumption becomes an available fact in later proof steps
- assumptions may support implication introduction, contradiction mode, and witness scopes for quantified rules

### `conclude(P)`

Purpose:
- marks the explicit result being discharged by the proof

Where it is used:
- proof bodies

Composition rules:
- may close a direct derivation
- may discharge an implication goal
- may discharge a contradiction proof
- may close a bounded witness-scope quantified derivation if the checker recognizes the pattern

### `apply(Name)`

Purpose:
- imports a previously declared lemma or theorem

Where it is used:
- proof bodies

Composition rules:
- the target lemma's `given(...)` hypotheses must already be established
- when that succeeds, the lemma's conclusions are imported into the current proof context

### `setVar(x)`
### `setVar(x: T)`
### `setVar(x: T, value)`
### `let x = value`

Purpose:
- introduces a variable into the current proof or executable context

Where it is used:
- proof bodies
- executable subset

Composition rules:
- variables are immediately in scope after introduction
- typed variables are recorded as base facts
- witness-style quantified rules use `setVar(...)` to mark explicit witness scope

### `contradiction()`

Purpose:
- marks an explicit contradiction step

Where it is used:
- proof bodies

Composition rules:
- is meaningful only when contradictory facts are already in context, or when the proof is already in contradiction mode
- may discharge a later `conclude(...)`

### Raw lines

Purpose:
- preserves unclassified proof content in the AST

Composition rules:
- checker mostly treats raw lines structurally unless they match a special recognized shape such as `contradiction()`

## Connectives And Chain Composition

### Top-level block connectives

Current top-level connectives:

- `→` or `->`
- `∧` or `&&`
- `↔` or `<->`

Meaning:
- they visibly connect adjacent top-level blocks in the file-wide proposition

### Statement-level connectives

Current statement connectives use the same visible chain style.

Meaning:
- they connect adjacent proof steps
- order matters because the checker only sees earlier facts as established

## Expression Surface

Current logical surface:

- implication: `→`, `⇒`, `->`, `implies`
- biconditional: `↔`, `⇔`, `<->`, `iff`
- conjunction: `∧`, `&&`, `and`
- disjunction: `∨`, `||`, `or`
- negation: `¬`, `!`, `not`

Current mathematical surface:

- membership: `∈`, `∉`, `in`, `not in`
- subset: `⊆`, `⊂`, `subset`, `subseteq`, `strictsubset`
- set operators: `∪`, `∩`, `union`, `intersection`
- equality-style symbols: `=`, `≠`, `!=`
- order symbols: `≤`, `≥`, `<=`, `>=`
- bounded quantifiers: `∀x ∈ A, P(x)`, `∃x ∈ A, P(x)`, plus `forall`, `exists`
- number alphabets: `ℕ`, `ℤ`, `ℚ`, `ℝ`, plus `Nat`, `Int`, `Rat`, `Real`

## Checker Composability Rules

These are the current fast-checker composition rules. A later proof step may be accepted when it composes earlier facts in one of these explicit ways.

### Structural composition

- theorem/proof names must match for paired checking
- theorem and lemma goals come from `assert(...)`
- theorem and lemma premises come from `given(...)`
- proofs must be non-empty
- missing top-level connectives are rejected

### Propositional composition

#### `IMPLIES_ELIM`

From:
- `P → Q`
- `P`

Derive:
- `Q`

#### `IMPLIES_INTRO`

From:
- an implication theorem goal `P → Q`
- an explicit assumption `P`
- an established `Q`

Derive:
- `P → Q`

#### `AND_INTRO`

From:
- `P`
- `Q`

Derive:
- `P ∧ Q`

#### `AND_ELIM`

From:
- `P ∧ Q`

Derive:
- `P`
- or `Q`

### Set-theoretic composition

#### `SUBSET_ELIM`

From:
- `x ∈ A`
- `A ⊆ B`

Derive:
- `x ∈ B`

#### `SUBSET_TRANS`

From:
- `A ⊆ B`
- `B ⊆ C`

Derive:
- `A ⊆ C`

#### `EQUALITY_SUBST`

From:
- `x = y`
- `x ∈ A`

Derive:
- `y ∈ A`

Current limit:
- only small membership-oriented substitution patterns are kernel-checked

#### `UNION_INTRO`

From:
- `x ∈ A`

Derive:
- `x ∈ A ∪ B`

#### `INTERSECTION_INTRO`

From:
- `x ∈ A`
- `x ∈ B`

Derive:
- `x ∈ A ∩ B`

#### `INTERSECTION_ELIM`

From:
- `x ∈ A ∩ B`

Derive:
- `x ∈ A`
- or `x ∈ B`

### Quantified composition

#### `FORALL_IN_ELIM`

From:
- `∀x ∈ A, P(x)`
- `a ∈ A`

Derive:
- `P(a)`

#### `FORALL_IN_INTRO`

From:
- explicit witness scope via `setVar(a)`
- explicit assumption `a ∈ A`
- established body `P(a)`

Derive:
- `∀x ∈ A, P(x)`

Current limit:
- the witness must be fresh relative to the output binder shape
- this is a narrow scope-pattern check, not full binder elaboration
- in the clearest current proof style, first derive `P(a)` as an intermediate fact, then conclude the quantified statement

#### `EXISTS_IN_INTRO`

From:
- `a ∈ A`
- `P(a)`

Derive:
- `∃x ∈ A, P(x)`

#### `EXISTS_IN_ELIM`

From:
- `∃x ∈ A, P(x)`
- explicit witness scope via `setVar(a)`
- explicit assumptions `a ∈ A` and `P(a)`
- a final conclusion that does not mention `a`

Derive:
- that witness-free conclusion

Current limit:
- this is a narrow explicit witness-scope rule
- it is not yet a full scoped subproof calculus

### Lemma composition

#### `BY_LEMMA`

From:
- `apply(LemmaName)`
- all lemma hypotheses already established

Derive:
- the lemma conclusions imported into the current context

### Contradiction composition

#### `CONTRADICTION`

From:
- contradictory facts already in context
- or a contradiction-shaped proof mode already opened

Derive:
- an explicit contradiction fact
- and possibly a later discharged conclusion

## What Does Not Compose Yet

These forms may parse, but they are not fully kernel-composable in the fast checker:

- full definitional equality
- normalization
- arbitrary quantified binder elaboration
- unbounded `∀` / `∃`
- set-builder notation
- deep algebraic rewriting
- richer theorem application semantics

Use `fl verify` for those.
