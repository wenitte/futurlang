# Demo Proofs

These files are the best current FuturLang theorem-prover demos.

All examples in this directory obey the core FuturLang rule that the source itself must stay visibly chained into a single truth-evaluable program.

## Recommended order

1. `identity.fl`
2. `conjunction-intro.fl`
3. `conjunction-elim.fl`
4. `modus-ponens.fl`
5. `right-projection.fl`
6. `multi-premise-chain.fl`
7. `lemma-apply.fl`
8. `contradiction-demo.fl`

## Demo commands

```bash
fl check examples/demo/identity.fl
fl check examples/demo/conjunction-intro.fl
fl check examples/demo/conjunction-elim.fl
fl check examples/demo/modus-ponens.fl
fl check examples/demo/right-projection.fl
fl check examples/demo/multi-premise-chain.fl
fl check examples/demo/lemma-apply.fl
fl check examples/demo/contradiction-demo.fl
```

These examples stay inside the current fast checker subset, so they are the right files to use for short live demos.

The conjunction introduction demo now includes an explicit `conclude(p && q)` step so `fl check` can display `AND_INTRO` directly in the proof trace.

`modus-ponens.fl` now uses first-class theorem premises with `given(...)`, which is closer to the long-term repository-style FuturLang syntax than repeating the premise inside the proof body.

`right-projection.fl` shows that a theorem premise can directly populate proof context and support elimination without repeating the premise inside the proof.

`multi-premise-chain.fl` shows multiple chained `given(...)` premises in one theorem body.

`lemma-apply.fl` demonstrates a chained lemma with a chained premise, followed by a theorem proof that satisfies the lemma hypothesis and uses `apply(...)`.

`contradiction-demo.fl` shows the current contradiction subset: a proof enters contradiction mode with a negated local assumption, makes an explicit `contradiction()` step, and then discharges the goal with `conclude(...)`.
