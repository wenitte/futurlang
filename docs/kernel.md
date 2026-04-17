# Kernel

FuturLang uses a categorical proof kernel justified by Wenittain Logic.

## Plain English Version

Think of the kernel as a very strict fact-checker.

You give it a pool of starting facts (your `assume()` statements). You tell it a goal (`declareToProve`). Then step by step you either add new facts (`prove`) or use rules the kernel already knows. At every step the kernel asks: "does this actually follow from what we have?" If yes, the new fact goes into the pool. If no, the proof fails.

When you reach `conclude`, the kernel checks that what you concluded matches the goal. If it does, and every intermediate step checked out, it stamps the proof `PROVED`.

The kernel never guesses. It never skips steps. It never accepts a claim it cannot verify from the pool using a rule it knows.

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
