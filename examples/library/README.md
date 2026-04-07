# Library Files

These files are the beginning of a real FuturLang standard library.

Unlike `examples/demo`, the goal here is reuse rather than isolated rule demos. Each file should package named lemmas that other proofs can import with `apply(...)`.

## Current files

1. `sets-basic.fl`

## Command

```bash
fl check examples/library/sets-basic.fl
```

`sets-basic.fl` currently provides a small reusable set-theory layer:

- subset transport
- subset transitivity
- subset antisymmetry
- intersection membership biconditional
- intersection membership helper lemmas
- union membership biconditional
- preimage/intersection biconditional
- preimage/intersection extensional equality
- preimage/union biconditional
- image introduction
- image/union helper lemmas
- pointwise image-of-union forward theorem

It also includes downstream theorems that reuse those lemmas through `apply(...)`, so the file demonstrates actual proof reuse rather than only standalone declarations.
