# Verify

`fl verify` transpiles FuturLang into Lean 4 and asks Lean to check the generated file.

## Intended Role

This is the authoritative direction for advanced mathematics.

## Current Limits

- some proof steps still use `sorry`
- source mapping is approximate
- the supported FuturLang subset is smaller than the surface syntax suggests

## Practical Rule

- use `fl` for the strict executable subset
- use `fl check` for fast proof-shape feedback
- use `fl verify` for serious mathematical claims
