# Language Reference

## Top-Level Blocks

- `theorem Name() { ... }`
- `proof Name() { ... }`
- `lemma Name() { ... }`
- `definition Name() { ... }`
- `struct Name() { ... }`

Top-level blocks are connected by visible connectives such as `→`, `∧`, and `↔`.

## Proof Statements

- `given(...)`
- `assume(...)`
- `assert(...)`
- `conclude(...)`
- `apply(...)`
- `setVar(...)`
- `contradiction()`

## Notation

The parser accepts both symbol and word forms for common logical and set-theoretic notation, including:

- `→`, `⇒`, `->`
- `↔`, `⇔`, `<->`
- `∧`, `&&`
- `∨`, `||`
- `∈`, `in`
- `⊂`, `subset`
- `∪`, `union`
- `∩`, `intersection`
- `∀`, `forall`
- `∃`, `exists`

The surface language is unchanged by the categorical kernel. The only user-visible proof result is the three-way output:

- `PROVED`
- `PENDING`
- `FAILED`
