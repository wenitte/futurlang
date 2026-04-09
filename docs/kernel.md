# Kernel

FuturLang uses a categorical proof kernel justified by Wenittain Logic.

## Internal Model

- propositions are kernel objects
- proof steps are kernel morphisms
- the ambient structure is a Boolean category
- complements are primitive
- implication is interpreted classically as `¬P ∨ Q`
- conjunction and disjunction are Boolean meet and join
- truth and contradiction are the terminal and initial objects
- undefined regions are tracked as partial-map domain restrictions
- `ω` creates suspended objects and pending morphisms in the resolution monad

Each internal morphism record stores:

- `id`
- `domain`
- `codomain`
- `tau ∈ {0, 1, ω}`
- `rule`
- `inputs`
- `pending`
- `domainRestriction`
- `suspended`

## Composition

Proof chains compose only when codomain and domain match. The composed truth value follows the Wenittain implication table.

Pending morphisms cannot be consumed by classical rules. The kernel raises:

`ω-Barrier: pending morphism cannot be used in classical derivation before Ra fires`

## Partial Maps

A morphism may be partial. Its `domainRestriction` records the subobject on which it is defined. Non-denoting terms live outside that restricted domain until resolution is available.

## Resolution Monad

The resolution monad suspends unresolved propositions as `T(P)`.

- `η: P → T(P)` embeds a resolved proposition into suspension
- `μ: T(T(P)) → T(P)` collapses nested suspension
- Ra is the algebra map `߉_κ: T(P) → P`

- partial witnesses raise `RevelationError`
- total witnesses resolve `ω` to `0` or `1`
- composition is preserved across revelation

## Result States

- `PROVED`
- `PENDING`
- `FAILED`

There is no fallback outside these three states.
