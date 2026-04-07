# Demo Proofs

These files are the best current FuturLang theorem-prover demos.

All examples in this directory obey the core FuturLang rule that the source itself must stay visibly chained into a single truth-evaluable program.

## Recommended order

1. `identity.fl`
2. `mi-membership-identity.fl`
3. `subset-transport.fl`
4. `subset-chain.fl`
5. `subset-transitivity.fl`
6. `subset-antisymmetry.fl`
7. `equality-substitution.fl`
8. `union-intro.fl`
9. `union-membership-iff.fl`
10. `forall-in-elim.fl`
11. `forall-in-intro.fl`
12. `exists-in-intro.fl`
13. `exists-in-elim.fl`
14. `intersection-left.fl`
15. `intersection-intro.fl`
16. `intersection-right.fl`
17. `intersection-membership-iff.fl`
18. `preimage-intersection-iff.fl`
19. `mi-order-identity.fl`
20. `conjunction-intro.fl`
21. `conjunction-elim.fl`
22. `modus-ponens.fl`
23. `right-projection.fl`
24. `multi-premise-chain.fl`
25. `iff-intro.fl`
26. `iff-elim.fl`
27. `lemma-apply.fl`
28. `contradiction-demo.fl`

## Demo commands

```bash
fl check examples/demo/identity.fl
fl check examples/demo/mi-membership-identity.fl
fl check examples/demo/subset-transport.fl
fl check examples/demo/subset-chain.fl
fl check examples/demo/subset-transitivity.fl
fl check examples/demo/subset-antisymmetry.fl
fl check examples/demo/equality-substitution.fl
fl check examples/demo/union-intro.fl
fl check examples/demo/union-membership-iff.fl
fl check examples/demo/forall-in-elim.fl
fl check examples/demo/forall-in-intro.fl
fl check examples/demo/exists-in-intro.fl
fl check examples/demo/exists-in-elim.fl
fl check examples/demo/intersection-left.fl
fl check examples/demo/intersection-intro.fl
fl check examples/demo/intersection-right.fl
fl check examples/demo/intersection-membership-iff.fl
fl check examples/demo/preimage-intersection-iff.fl
fl check examples/demo/mi-order-identity.fl
fl check examples/demo/conjunction-intro.fl
fl check examples/demo/conjunction-elim.fl
fl check examples/demo/modus-ponens.fl
fl check examples/demo/right-projection.fl
fl check examples/demo/multi-premise-chain.fl
fl check examples/demo/iff-intro.fl
fl check examples/demo/iff-elim.fl
fl check examples/demo/lemma-apply.fl
fl check examples/demo/contradiction-demo.fl
```

These examples stay inside the current fast checker subset, so they are the right files to use for short live demos.

`mi-membership-identity.fl` and `mi-order-identity.fl` show mathematician-friendly notation like `∈`, `≤`, and `⇒` while staying inside the current honest checker subset.

`subset-transport.fl` is the first real set-theoretic kernel demo: the checker validates `x ∈ A` plus `A ⊆ B` and derives `x ∈ B` via `SUBSET_ELIM`.

`subset-chain.fl` shows two chained set-theoretic derivations in one proof: `x ∈ A`, `A ⊆ B`, `B ⊆ C` yields `x ∈ C` by first deriving `x ∈ B` and then `x ∈ C`.

`subset-transitivity.fl` shows a second genuinely mathematical subset rule in the current kernel: `A ⊆ B`, `B ⊆ C` yields `A ⊆ C`.

`subset-antisymmetry.fl` shows a more mathematician-natural set equality rule: from `A ⊆ B` and `B ⊆ A`, the checker derives `A = B`.

`equality-substitution.fl` shows equality-driven transport across membership claims: `x = y` plus `x ∈ A` yields `y ∈ A`.

`union-intro.fl` shows kernel-checked union membership introduction: from `x ∈ A`, the checker derives `x ∈ A ∪ B`.

`union-membership-iff.fl` is the union counterpart to the intersection theorem: it proves `x ∈ A ∪ B ↔ (x ∈ A ∨ x ∈ B)` from scratch by combining `UNION_ELIM`, `UNION_INTRO`, `OR_ELIM`, and `IFF_INTRO`.

`forall-in-elim.fl` shows bounded universal elimination: from `∀ x ∈ A, x ∈ B` and `a ∈ A`, the checker derives `a ∈ B`.

`forall-in-intro.fl` shows the current narrow witness-scope introduction rule for bounded universals: after `setVar(a)` and `assume(a ∈ A)`, the proof first derives `a ∈ B` and then concludes `∀ x ∈ A, x ∈ B`.

`exists-in-intro.fl` shows bounded existential introduction: from `a ∈ A` and `a ∈ B`, the checker derives `∃ x ∈ A, x ∈ B`.

`exists-in-elim.fl` shows the current narrow witness-scope existential elimination rule: after `setVar(a)`, the proof explicitly assumes `a ∈ A` and `a ∈ B`, then discharges a conclusion that does not mention `a`.

`intersection-left.fl` shows set-style conjunction elimination with Unicode membership notation: from `(x ∈ A) ∧ (x ∈ B)`, the checker derives `x ∈ A`.

`intersection-intro.fl` shows kernel-checked intersection membership introduction: from `x ∈ A` and `x ∈ B`, the checker derives `x ∈ A ∩ B`.

`intersection-right.fl` shows kernel-checked intersection membership elimination in direct set notation: from `x ∈ A ∩ B`, the checker derives `x ∈ B`.

`intersection-membership-iff.fl` is a stronger derived theorem built from the kernel rules: it proves `x ∈ A ∩ B ↔ (x ∈ A ∧ x ∈ B)` from scratch by deriving both implications and then applying `IFF_INTRO`.

`preimage-intersection-iff.fl` is the first honest function-facing theorem in the kernel subset: it uses `PREIMAGE_INTRO`, `PREIMAGE_ELIM`, and intersection rules to prove `x ∈ preimage(f, B ∩ C) ↔ (x ∈ preimage(f, B) ∧ x ∈ preimage(f, C))`.

The conjunction introduction demo now includes an explicit `conclude(p && q)` step so `fl check` can display `AND_INTRO` directly in the proof trace.

`modus-ponens.fl` now uses first-class theorem premises with `given(...)`, which is closer to the long-term repository-style FuturLang syntax than repeating the premise inside the proof body.

`right-projection.fl` shows that a theorem premise can directly populate proof context and support elimination without repeating the premise inside the proof.

`multi-premise-chain.fl` shows multiple chained `given(...)` premises in one theorem body.

`iff-intro.fl` shows kernel-checked biconditional introduction: from `p → q` and `q → p`, the checker derives `p ↔ q`.

`iff-elim.fl` shows kernel-checked biconditional elimination: from `p ↔ q` and `p`, the checker derives `q`.

`lemma-apply.fl` demonstrates a chained lemma with a chained premise, followed by a theorem proof that satisfies the lemma hypothesis and uses `apply(...)`.

`contradiction-demo.fl` shows the current contradiction subset: a proof enters contradiction mode with a negated local assumption, makes an explicit `contradiction()` step, and then discharges the goal with `conclude(...)`.

The parser also accepts ASCII and word equivalents for the math-facing surface. For example, `x in A union B`, `A subset B`, and `forall x in A, ...` normalize to the same internal notation used by the Unicode demos.
