# lib/

The FuturLang standard mathematics library. Each file packages named lemmas that other proofs can import with `apply(...)`.

Unlike `examples/demo` (isolated rule demos), the goal here is reuse across proofs.

```bash
fl check lib/<file>.fl
```

## Files

### `sets-basic.fl`
Set-theoretic foundations with kernel-verified proofs.
- Subset transport, transitivity, antisymmetry
- Intersection and union membership biconditionals
- Preimage/intersection and preimage/union biconditionals
- Preimage intersection extensional equality
- Image introduction and image/union lemmas

### `sets-algebra.fl`
Set-algebraic identities with kernel-verified proofs.
- Subset reflexivity
- Union/intersection subset inclusions
- Intersection and union commutativity (double-inclusion proofs)

### `math.fl`
Arithmetic and number theory.
- Arithmetic identities: add-zero, mul-one, mul-zero, commutativity, associativity
- Even/odd: EvenDouble, EvenPlusEven, EvenTimesAny, EvenSquareImpliesEven
- Divisibility: DividesRefl, EvenIffDivides2
- Ordering: NatNonNeg, SquareNonNeg, AbsNonNeg
- Number theory: Sqrt2Irrational (contradiction proof), FermatLittle, EulerTheorem, RSACorrectness

### `number-theory.fl`
Divisibility, GCD, primes, modular arithmetic.
- DividesRefl, DividesTrans, DividesAntisym
- GCDDividesLeft, GCDDividesRight, GCDComm
- Bezout's identity
- Euclid's lemma (prime divides product)
- HasPrimeDivisor, InfinitelyManyPrimes
- Fundamental Theorem of Arithmetic
- GCDLCMProduct, CoprimeAndDivides
- CongruenceRefl, CongruenceSym, CongruenceTrans
- Chinese Remainder Theorem

### `algebra.fl`
Abstract algebra: groups, rings, fields, homomorphisms.
- GroupIdentityUnique, GroupInverseUnique
- GroupLeftCancel, GroupInvInv, GroupInvProduct
- AbelianComm
- SubgroupClosed, SubgroupIdentity, SubgroupInverse
- HomPreservesIdentity, HomPreservesInverse
- KernelIsSubgroup
- RingDistribLeft, RingZeroAnnihilates
- FieldNonzeroGroup

### `linear-algebra.fl`
Vector spaces and linear maps.
- VZeroUnique, ScalarZeroAnnihilates, VectorZeroAnnihilates, NegIsMinusOne
- SubspaceContainsZero, SubspaceClosed
- LinearMapPreservesZero, LinearMapPreservesNeg
- KernelIsSubspace, ImageIsSubspace
- RankNullity (dimension theorem)
- InjectiveIffTrivialKernel
- IsomorphismPreservesDim

### `topology.fl`
Topological spaces, continuity, compactness, connectedness.
- EmptyIsOpen, WholeSpaceIsOpen
- UnionOfOpenIsOpen, IntersectionOfOpenIsOpen
- OpenComplementClosed, ClosedComplementOpen
- EmptyIsClosed, WholeSpaceIsClosed
- ContinuousOpenPreimage, ContinuousClosedPreimage
- ContinuousComposition
- ClosedSubsetOfCompact, CompactImageIsCompact
- CompactInHausdorffIsClosed, CompactContinuousToHausdorff
- ConnectedIVT, ProductConnected
- HausdorffLimitUnique

### `real-analysis.fl`
Limits, continuity, and derivatives on the reals.
- DiffImpliesCont, LimitByContinuity
- EVT (Extreme Value Theorem), IVT (Intermediate Value Theorem)
- PowerRule

### `type-system.fl`
Dependent types and subtype coercions.
- SigmaFstProj, SigmaSndProj
- NatIsInt, NatIsReal, IntIsReal
- PiElimArith

### `crypto.fl`
Cryptographic primitives and protocols.
- DLogHard, DHSecret
- HashSecurity, CommitBinding
- ECAddComm
