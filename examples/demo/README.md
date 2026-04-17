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
19. `image-union-left.fl`
20. `image-union-forward.fl`
21. `mi-order-identity.fl`
22. `conjunction-intro.fl`
23. `conjunction-elim.fl`
24. `modus-ponens.fl`
25. `right-projection.fl`
26. `multi-premise-chain.fl`
27. `iff-intro.fl`
28. `iff-elim.fl`
29. `lemma-apply.fl`
30. `contradiction-demo.fl`
31. `block-connectives.fl`

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
fl check examples/demo/image-union-left.fl
fl check examples/demo/image-union-forward.fl
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
fl check examples/demo/block-connectives.fl
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

`preimage-intersection-equality.fl` pushes that one level higher: it uses `SUBSET_INTRO` and `SUBSET_ANTISYM` to prove the actual set equality `preimage(f, B ∩ C) = preimage(f, B) ∩ preimage(f, C)`.

`image-union-left.fl` is the first image theorem in the same minimal function layer: from `x ∈ A`, the checker derives `f(x) ∈ image(f, A ∪ B)` by combining `UNION_INTRO` with `IMAGE_INTRO`.

`image-union-forward.fl` is the first nontrivial image theorem: from `x ∈ A ∪ B`, the checker derives `f(x) ∈ image(f, A) ∪ image(f, B)` by combining `UNION_ELIM`, `IMAGE_INTRO`, `UNION_INTRO`, and implication introduction.

The conjunction introduction demo now includes an explicit `conclude(p && q)` step so `fl check` can display `AND_INTRO` directly in the proof trace.

`modus-ponens.fl` uses `assume(P ∧ (P → Q))` to declare both premises in one step, then the proof concludes `Q` by IMPLIES_ELIM.

`right-projection.fl` shows that a declared premise goes directly into proof context and supports elimination without repeating it inside the proof body.

`multi-premise-chain.fl` shows multiple independent premises declared with `assume(H₁ ∧ H₂ ∧ ...)` in one theorem body.

`iff-intro.fl` shows kernel-checked biconditional introduction: from `p → q` and `q → p`, the checker derives `p ↔ q`.

`iff-elim.fl` shows kernel-checked biconditional elimination: from `p ↔ q` and `p`, the checker derives `q`.

`lemma-apply.fl` demonstrates a chained lemma with a chained premise, followed by a theorem proof that satisfies the lemma hypothesis and uses `apply(...)`.

`contradiction-demo.fl` shows the current contradiction subset: a proof enters contradiction mode with a negated local assumption, makes an explicit `contradiction()` step, and then discharges the goal with `conclude(...)`.

`block-connectives.fl` demonstrates the two inter-block connectives the checker validates: `∧` (independent blocks) and `→` (the next proof calls `apply()` on the current block). It shows a minimal example where `ConjLeft` and `ConjRight` are independent (`∧`), then `SplitAndUseRight` depends on `ConjRight` via `apply(ConjRight)` (`→`). Using the wrong connective causes `FAILED`.

The parser also accepts ASCII and word equivalents for the math-facing surface. For example, `x in A union B`, `A subset B`, and `forall x in A, ...` normalize to the same internal notation used by the Unicode demos.
