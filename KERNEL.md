# FuturLang Kernel: Formal Specification and Consistency Proof

**Version:** 1.0  
**Status:** Draft — intended for mathematical review  
**Scope:** This document covers the *logical kernel* only. Domain-specific rules (arithmetic, cryptography, topology, etc.) are outside the kernel; they are explicit axioms whose status is discussed in §7.

---

## Abstract

This document gives a formal specification of the FuturLang logical kernel, defines a classical set-theoretic semantics, and proves the kernel *sound*: every claim derivable by the kernel rules is true in every model satisfying the premises. Consistency — that the kernel cannot derive False from no premises — follows immediately as a corollary.

The proof is self-contained and assumes only ZFC set theory, which is the standard working foundation for mathematics. The argument is standard; what is novel here is its application to this specific rule system and the explicit identification of what is and is not in the trusted base.

---

## §1  Syntax

### 1.1  Terms

Let **Var** be a countable set of variable symbols and **Const** a set of constant symbols. The set of *terms* T is defined inductively:

```
t ::= x            (variable, x ∈ Var)
    | c            (constant, c ∈ Const)
    | f(t₁, …, tₙ) (function application, f an n-ary function symbol)
```

### 1.2  Propositions

The set of *propositions* Prop is defined inductively:

```
φ ::= ⊤                       (truth)
    | ⊥                       (falsehood)
    | P(t₁, …, tₙ)            (atomic predicate)
    | t₁ = t₂                 (equality)
    | t ∈ S                   (set membership, S a set term)
    | A ⊆ B                   (subset)
    | φ ∧ ψ                   (conjunction)
    | φ ∨ ψ                   (disjunction)
    | φ → ψ                   (implication)
    | φ ↔ ψ                   (biconditional)
    | ¬φ                      (negation)
    | ∀ x ∈ D, φ              (bounded universal)
    | ∃ x ∈ D, φ              (bounded existential)
```

We use standard notational conventions. φ[t/x] denotes the capture-avoiding substitution of term t for variable x in φ.

### 1.3  Contexts

A *context* Γ is a finite set of propositions. We write Γ, φ for Γ ∪ {φ}.

---

## §2  Kernel Inference Rules

A *judgement* Γ ⊢ φ is read "from context Γ, the proposition φ is derivable." The following rules define the derivability relation. These are the **only** rules in the trusted kernel.

### 2.1  Structural Rules

```
──────────────────── ASSUMPTION
   Γ, φ ⊢ φ

   Γ ⊢ φ
──────────────────── WEAKENING
   Γ, ψ ⊢ φ
```

### 2.2  Conjunction

```
   Γ ⊢ φ    Γ ⊢ ψ
──────────────────── AND_INTRO
   Γ ⊢ φ ∧ ψ

   Γ ⊢ φ ∧ ψ
──────────────────── AND_ELIM_L
   Γ ⊢ φ

   Γ ⊢ φ ∧ ψ
──────────────────── AND_ELIM_R
   Γ ⊢ ψ
```

### 2.3  Disjunction

```
   Γ ⊢ φ
──────────────────── OR_INTRO_L
   Γ ⊢ φ ∨ ψ

   Γ ⊢ ψ
──────────────────── OR_INTRO_R
   Γ ⊢ φ ∨ ψ

   Γ ⊢ φ ∨ ψ    Γ, φ ⊢ χ    Γ, ψ ⊢ χ
─────────────────────────────────────── OR_ELIM
   Γ ⊢ χ
```

### 2.4  Implication

```
   Γ, φ ⊢ ψ
──────────────────── IMPLIES_INTRO
   Γ ⊢ φ → ψ

   Γ ⊢ φ → ψ    Γ ⊢ φ
──────────────────────── IMPLIES_ELIM  (modus ponens)
   Γ ⊢ ψ
```

### 2.5  Biconditional

```
   Γ ⊢ φ → ψ    Γ ⊢ ψ → φ
──────────────────────────── IFF_INTRO
   Γ ⊢ φ ↔ ψ

   Γ ⊢ φ ↔ ψ    Γ ⊢ φ
──────────────────────── IFF_ELIM_L
   Γ ⊢ ψ

   Γ ⊢ φ ↔ ψ    Γ ⊢ ψ
──────────────────────── IFF_ELIM_R
   Γ ⊢ φ
```

### 2.6  Negation (Classical)

```
   Γ, φ ⊢ ⊥
──────────────── NOT_INTRO
   Γ ⊢ ¬φ

   Γ ⊢ ¬¬φ
──────────────── DOUBLE_NEG
   Γ ⊢ φ
```

### 2.7  Falsehood

```
   Γ ⊢ ⊥
──────────────── EX_FALSO
   Γ ⊢ φ
```

### 2.8  Bounded Quantifiers

In all quantifier rules below, x must not occur free in Γ or the set term D.

```
   Γ, (x ∈ D) ⊢ φ
──────────────────────── FORALL_INTRO
   Γ ⊢ ∀ x ∈ D, φ

   Γ ⊢ ∀ x ∈ D, φ    Γ ⊢ t ∈ D
──────────────────────────────────── FORALL_ELIM
   Γ ⊢ φ[t/x]

   Γ ⊢ φ[t/x]    Γ ⊢ t ∈ D
──────────────────────────────── EXISTS_INTRO
   Γ ⊢ ∃ x ∈ D, φ

   Γ ⊢ ∃ x ∈ D, φ    Γ, (x ∈ D), φ ⊢ ψ
─────────────────────────────────────────── EXISTS_ELIM
   Γ ⊢ ψ
   (x not free in ψ or Γ)
```

### 2.9  Equality

```
────────────────── EQ_REFL
   Γ ⊢ t = t

   Γ ⊢ s = t
────────────────── EQ_SYMM
   Γ ⊢ t = s

   Γ ⊢ s = t    Γ ⊢ φ[s/x]
────────────────────────────── EQ_SUBST
   Γ ⊢ φ[t/x]
```

### 2.10  Sets

```
   Γ, (x ∈ A) ⊢ x ∈ B       (x not free in Γ, A, B)
──────────────────────────── SUBSET_INTRO
   Γ ⊢ A ⊆ B

   Γ ⊢ A ⊆ B    Γ ⊢ x ∈ A
──────────────────────────── SUBSET_ELIM
   Γ ⊢ x ∈ B

   Γ ⊢ A ⊆ B    Γ ⊢ B ⊆ C
──────────────────────────── SUBSET_TRANS
   Γ ⊢ A ⊆ C

   Γ ⊢ A ⊆ B    Γ ⊢ B ⊆ A
──────────────────────────── SUBSET_ANTISYM
   Γ ⊢ A = B
```

---

## §3  Semantics

### 3.1  Interpretations

An *interpretation* I = (D, [[·]]) consists of:

- A non-empty set D (the *domain of discourse*)
- For each n-ary function symbol f, a function [[f]]_I : Dⁿ → D
- For each constant c, an element [[c]]_I ∈ D
- For each n-ary predicate P, a function [[P]]_I : Dⁿ → {0,1}
- For each set term S, a subset [[S]]_I ⊆ D

### 3.2  Variable Assignments

A *variable assignment* v : Var → D maps variables to domain elements. We write v[x ↦ d] for the assignment that agrees with v on all variables except x, where it assigns d.

The *denotation* of a term t under I and v is defined inductively:
- [[x]]_{I,v} = v(x)
- [[c]]_{I,v} = [[c]]_I
- [[f(t₁,…,tₙ)]]_{I,v} = [[f]]_I([[t₁]]_{I,v}, …, [[tₙ]]_{I,v})

### 3.3  Satisfaction

*Satisfaction* I,v ⊨ φ is defined inductively on the structure of φ:

| Proposition | Satisfied iff |
|---|---|
| ⊤ | always |
| ⊥ | never |
| P(t₁,…,tₙ) | [[P]]_I([[t₁]]_{I,v},…,[[tₙ]]_{I,v}) = 1 |
| t₁ = t₂ | [[t₁]]_{I,v} = [[t₂]]_{I,v} |
| t ∈ S | [[t]]_{I,v} ∈ [[S]]_I |
| A ⊆ B | [[A]]_I ⊆ [[B]]_I |
| φ ∧ ψ | I,v ⊨ φ  and  I,v ⊨ ψ |
| φ ∨ ψ | I,v ⊨ φ  or  I,v ⊨ ψ |
| φ → ψ | I,v ⊭ φ  or  I,v ⊨ ψ |
| φ ↔ ψ | (I,v ⊨ φ) iff (I,v ⊨ ψ) |
| ¬φ | I,v ⊭ φ |
| ∀ x ∈ D, φ | for all d ∈ [[D]]_I, I,v[x↦d] ⊨ φ |
| ∃ x ∈ D, φ | there exists d ∈ [[D]]_I such that I,v[x↦d] ⊨ φ |

We write I,v ⊨ Γ if I,v ⊨ φ for every φ ∈ Γ.

---

## §4  Soundness

**Theorem 4.1 (Soundness).** If Γ ⊢ φ by the kernel rules, then for every interpretation I and variable assignment v such that I,v ⊨ Γ, we have I,v ⊨ φ.

**Proof.** By structural induction on the derivation of Γ ⊢ φ. We proceed by cases on the last rule applied. In each case, the induction hypothesis (IH) applies to all sub-derivations.

Fix an arbitrary interpretation I and assignment v with I,v ⊨ Γ throughout.

---

**ASSUMPTION.**  Γ = Γ', φ. Since I,v ⊨ Γ, in particular I,v ⊨ φ. ∎

**WEAKENING.**  By IH on the sub-derivation Γ ⊢ φ, since I,v ⊨ Γ ⊆ Γ,ψ. ∎

---

**AND_INTRO.**  Sub-derivations give Γ ⊢ φ and Γ ⊢ ψ. By IH, I,v ⊨ φ and I,v ⊨ ψ. By definition of ∧, I,v ⊨ φ ∧ ψ. ∎

**AND_ELIM_L.**  By IH, I,v ⊨ φ ∧ ψ. By definition, I,v ⊨ φ. ∎

**AND_ELIM_R.**  By IH, I,v ⊨ φ ∧ ψ. By definition, I,v ⊨ ψ. ∎

---

**OR_INTRO_L.**  By IH, I,v ⊨ φ. By definition of ∨ (taking the left disjunct), I,v ⊨ φ ∨ ψ. ∎

**OR_INTRO_R.**  Symmetric. ∎

**OR_ELIM.**  By IH, I,v ⊨ φ ∨ ψ. So either I,v ⊨ φ or I,v ⊨ ψ.

- Case I,v ⊨ φ: Then I,v ⊨ Γ,φ. By IH on Γ,φ ⊢ χ, we get I,v ⊨ χ.
- Case I,v ⊨ ψ: Then I,v ⊨ Γ,ψ. By IH on Γ,ψ ⊢ χ, we get I,v ⊨ χ.

In both cases I,v ⊨ χ. ∎

---

**IMPLIES_INTRO.**  We must show I,v ⊨ φ → ψ, i.e. if I,v ⊨ φ then I,v ⊨ ψ.  
Assume I,v ⊨ φ. Then I,v ⊨ Γ,φ. By IH on the sub-derivation Γ,φ ⊢ ψ, we get I,v ⊨ ψ. ∎

**IMPLIES_ELIM.**  By IH, I,v ⊨ φ → ψ and I,v ⊨ φ. By definition of →, I,v ⊨ ψ. ∎

---

**IFF_INTRO.**  By IH, I,v ⊨ φ → ψ and I,v ⊨ ψ → φ. By definition of ↔, I,v ⊨ φ ↔ ψ. ∎

**IFF_ELIM_L.**  By IH, I,v ⊨ φ ↔ ψ and I,v ⊨ φ. By definition of ↔, I,v ⊨ ψ. ∎

**IFF_ELIM_R.**  Symmetric. ∎

---

**NOT_INTRO.**  We must show I,v ⊨ ¬φ, i.e. I,v ⊭ φ.  
Suppose for contradiction I,v ⊨ φ. Then I,v ⊨ Γ,φ. By IH on Γ,φ ⊢ ⊥, we get I,v ⊨ ⊥. But ⊥ is never satisfied — contradiction. Therefore I,v ⊭ φ, so I,v ⊨ ¬φ. ∎

**DOUBLE_NEG.**  By IH, I,v ⊨ ¬¬φ, i.e. I,v ⊭ ¬φ, i.e. not (I,v ⊭ φ), i.e. I,v ⊨ φ. ∎

---

**EX_FALSO.**  By IH, I,v ⊨ ⊥. But ⊥ is never satisfied, so the hypothesis is vacuously false. The implication holds trivially for any φ. ∎

---

**FORALL_INTRO.**  We must show I,v ⊨ ∀ x ∈ D, φ.  
Let d ∈ [[D]]_I be arbitrary. Since x does not occur free in Γ, we have I,v[x↦d] ⊨ Γ.  
Therefore I,v[x↦d] ⊨ Γ, (x ∈ D).  
By IH on Γ,(x ∈ D) ⊢ φ, we get I,v[x↦d] ⊨ φ.  
Since d was arbitrary, I,v ⊨ ∀ x ∈ D, φ. ∎

**FORALL_ELIM.**  By IH, I,v ⊨ ∀ x ∈ D, φ and I,v ⊨ t ∈ D.  
Let d = [[t]]_{I,v}. Then d ∈ [[D]]_I.  
By definition of ∀, I,v[x↦d] ⊨ φ.  
By the substitution lemma (standard), I,v ⊨ φ[t/x]. ∎

**EXISTS_INTRO.**  By IH, I,v ⊨ φ[t/x] and I,v ⊨ t ∈ D.  
Let d = [[t]]_{I,v}. Then d ∈ [[D]]_I.  
By the substitution lemma, I,v[x↦d] ⊨ φ.  
Therefore I,v ⊨ ∃ x ∈ D, φ. ∎

**EXISTS_ELIM.**  By IH, I,v ⊨ ∃ x ∈ D, φ.  
So there exists d ∈ [[D]]_I with I,v[x↦d] ⊨ φ.  
Since x not free in Γ, I,v[x↦d] ⊨ Γ.  
Thus I,v[x↦d] ⊨ Γ, (x ∈ D), φ.  
By IH on that sub-derivation, I,v[x↦d] ⊨ ψ.  
Since x not free in ψ, I,v ⊨ ψ. ∎

---

**EQ_REFL.**  [[t]]_{I,v} = [[t]]_{I,v} by reflexivity of set equality. Therefore I,v ⊨ t = t. ∎

**EQ_SYMM.**  By IH, [[s]]_{I,v} = [[t]]_{I,v}. By symmetry of equality, [[t]]_{I,v} = [[s]]_{I,v}. ∎

**EQ_SUBST.**  By IH, [[s]]_{I,v} = [[t]]_{I,v} and I,v ⊨ φ[s/x].  
By the substitution lemma, satisfaction of φ[s/x] depends only on the denotation of s.  
Since [[s]]_{I,v} = [[t]]_{I,v}, we have I,v ⊨ φ[t/x]. ∎

---

**SUBSET_INTRO.**  We must show [[A]]_I ⊆ [[B]]_I.  
Let d ∈ [[A]]_I be arbitrary. Since x not free in Γ, A, B, set v' = v[x↦d].  
Then I,v' ⊨ Γ and I,v' ⊨ x ∈ A.  
By IH on Γ,(x ∈ A) ⊢ x ∈ B, we get I,v' ⊨ x ∈ B, i.e. d ∈ [[B]]_I.  
Since d was arbitrary, [[A]]_I ⊆ [[B]]_I, i.e. I,v ⊨ A ⊆ B. ∎

**SUBSET_ELIM.**  By IH, [[A]]_I ⊆ [[B]]_I and [[x]]_{I,v} ∈ [[A]]_I.  
By definition of subset, [[x]]_{I,v} ∈ [[B]]_I, i.e. I,v ⊨ x ∈ B. ∎

**SUBSET_TRANS.**  By IH, [[A]]_I ⊆ [[B]]_I and [[B]]_I ⊆ [[C]]_I.  
By transitivity of ⊆ in ZFC, [[A]]_I ⊆ [[C]]_I, i.e. I,v ⊨ A ⊆ C. ∎

**SUBSET_ANTISYM.**  By IH, [[A]]_I ⊆ [[B]]_I and [[B]]_I ⊆ [[A]]_I.  
By the axiom of extensionality in ZFC, [[A]]_I = [[B]]_I, i.e. I,v ⊨ A = B. ∎

---

This completes the induction. The theorem is proved. □

---

## §5  Consistency

**Corollary 5.1 (Consistency).** There is no derivation of ⊢ ⊥ (i.e. ⊥ is not derivable from the empty context).

**Proof.** Suppose for contradiction that ⊢ ⊥.  
By Theorem 4.1, every interpretation I with I,v ⊨ ∅ (which every interpretation satisfies vacuously) must have I,v ⊨ ⊥.  
But ⊥ is never satisfied by definition — no such interpretation exists.  
This is a contradiction. Therefore ⊢ ⊥ is not derivable. □

**Corollary 5.2 (Non-triviality).** For any proposition φ that is not a tautology (e.g. φ = P(a) for a fresh predicate P and constant a), ⊢ φ is not derivable.

**Proof.** Construct an interpretation where φ is false. By soundness, φ is not derivable. □

---

## §6  Correspondence with the Implementation

The proof above is about the *specification* in §2. For mathematicians to trust the system, the TypeScript implementation must faithfully implement these rules and nothing else. This section maps spec rules to implementation functions and calls out every place where the implementation diverges from the idealized spec.

### 6.1  Trusted surface area

The trusted kernel lives in `src/checker/checker.ts`. The table below lists each spec rule, the implementing function, and the internal rule label stored in the proof object. The label is what appears in a proof certificate; it is **not** the same as the function name.

| Spec Rule | Implementation Function | Internal Rule Label |
|---|---|---|
| AND_INTRO | `deriveAndIntro` | `AND_INTRO` |
| AND_ELIM_L, AND_ELIM_R | `deriveAndElim` | `AND_ELIM_LEFT`, `AND_ELIM_RIGHT` |
| OR_INTRO_L, OR_INTRO_R | `deriveOrIntro` | `OR_INTRO_LEFT`, `OR_INTRO_RIGHT` |
| OR_ELIM | `deriveOrElim` | `OR_ELIM` |
| IMPLIES_INTRO | `deriveImpliesIntro` | `IMPLIES_INTRO` |
| IMPLIES_ELIM | `deriveImpliesElim` | `IMPLIES_ELIM` |
| IFF_INTRO | `deriveIffIntro` | `IFF_INTRO` |
| IFF_ELIM_L, IFF_ELIM_R | `deriveIffElim` | `IFF_ELIM_L`, `IFF_ELIM_R` |
| NOT_INTRO | `deriveNotIntro` | `NOT_INTRO` |
| EX_FALSO | `deriveExFalso` | `CONTRADICTION` |
| FORALL_ELIM | `deriveForallElim` | `FORALL_ELIM` |
| EXISTS_INTRO | `deriveExistsIntro` | `EXISTS_INTRO` |
| EQ_REFL | `deriveEqualityReflexivity` | `EQ_REFL` |
| EQ_SYMM | `deriveEqualitySymmetry` | `EQ_SYMM` |
| EQ_SUBST (membership only) | `deriveEqualitySubstitution` | `IMPLIES_ELIM` |
| SUBSET_ELIM, SUBSET_TRANS, SUBSET_ANTISYM | `deriveSubsetElim`, `deriveSubsetTransitivity`, `deriveSubsetAntisymmetry` | `IMPLIES_ELIM` |
| SUBSET_INTRO | `deriveSubsetIntro` | `IMPLIES_INTRO` |

An auditor needs to verify that each function implements exactly its corresponding rule and introduces no additional derivations.

### 6.2  Implementation notes

The following deviations from the idealized spec in §2 exist in the current implementation. All are sound; none allow deriving false conclusions. They are noted here so an auditor knows where to look.

**Categorical encoding of subsets and equality.** The implementation models `A ⊆ B` as a morphism in an internal category, not as a first-class proposition. As a result, SUBSET_ELIM, SUBSET_TRANS, SUBSET_ANTISYM, and EQ_SUBST are all tagged with the `IMPLIES_ELIM` rule label internally. Soundness is preserved because subset transport (`x ∈ A, A ⊆ B ⊢ x ∈ B`) is exactly modus ponens on the morphism reading. An auditor should check that the parsing of subset claims in these functions is correct and exhaustive.

**OR_ELIM requires materialized implications.** The spec OR_ELIM reads:

```
Γ ⊢ φ ∨ ψ    Γ,φ ⊢ χ    Γ,ψ ⊢ χ
────────────────────────────────── OR_ELIM
Γ ⊢ χ
```

The implementation (`deriveOrElim`) requires that `φ → χ` and `ψ → χ` already appear as objects in the proof context — they must be derived before the OR_ELIM step. This is more restrictive than the spec but strictly sound: it requires the two case arms to be made explicit before elimination, rather than accepting them as sub-derivations.

**FORALL_INTRO is done by goal reduction.** There is no `deriveForallIntro` function. Instead, the `intro()` tactic strips the leading `∀ x ∈ D,` from the current goal, introduces `x ∈ D` as an assumption (labeled `ASSUMPTION`), and updates the goal to the body. This corresponds exactly to the FORALL_INTRO rule: the subsequent proof of the body under `x ∈ D` discharges the assumption and closes the quantifier. An auditor should verify `handleIntro` in `checker.ts`.

**EXISTS_ELIM is done by `obtain()`.** There is no `deriveExistsElim` function. The `obtain()` tactic destructs an existential from context, introducing the witness membership and body as assumptions. This corresponds to EXISTS_ELIM with the side conditions on freshness enforced by variable scoping.

**DOUBLE_NEG is not a standalone rule.** There is no `deriveDoubleNeg` function. Double negation elimination is achieved in the closure phase: `¬¬φ` in context is resolved to `φ` by pattern matching during forward-chaining. This is classically valid (the semantics are classical, as specified in §3).

**EQ_SUBST is restricted to membership.** The implementation handles only the case `s = t, s ∈ S ⊢ t ∈ S` (and its symmetric form). Full positional substitution into arbitrary propositions is not implemented. Every theorem in the standard library that uses equality substitution uses it in this membership form, so no library proof is affected. A future version should generalize to arbitrary `φ[s/x] ⊢ φ[t/x]`.

### 6.3  NOT_INTRO — implementation requirements

The specification states NOT_INTRO as:

```
Γ, φ ⊢ ⊥
────────── NOT_INTRO
Γ ⊢ ¬φ
```

The implementation of `deriveNotIntro` enforces both conditions of this rule precisely:

1. φ is in `ctx.assumptions` — introduced by an explicit `assume()` step. Premises and derived facts do not count; the rule requires an active dischargeable hypothesis.
2. `⊥` is in `ctx.objects` — a contradiction was derived while the assumption was active.

Only when both conditions hold is `¬φ` derived. This implements proof by contradiction: assuming φ led to ⊥, therefore ¬φ. All 21 logic library theorems (ModusTollens, DoubleNegIntro, DeMorgan, ExcludedMiddle, etc.) are verified under this rule.

### 6.4  What is NOT part of the trusted kernel

The following functions in `checker.ts` are **not** part of the logical kernel and must not be treated as such:

- `deriveCryptoClaim` — asserts discrete log hardness and Diffie-Hellman properties as checked patterns
- `deriveArithClaim` — uses probabilistic spot-testing for symbolic equalities
- `deriveAlgebraClaim`, `deriveLinAlgClaim`, `deriveTopologyClaim`, etc. — encode domain knowledge as pattern-matched rules

These are *axiom schemas* whose correctness depends on domain knowledge, not on the logical kernel. They should be refactored into explicit `axiom` declarations in `.fl` files so users can inspect them.

---

## §7  Domain Axioms

Every result that relies on a domain-specific function listed in §6.4 depends on an implicit axiom. The following is a non-exhaustive list; a complete enumeration requires auditing each such function.

**Axioms currently embedded in the checker (should be made explicit):**

```
// Number theory
axiom dlog_hard     : ∀ g ∈ ℕ, ∀ p ∈ Prime, dlog_hard(g, p)
axiom fermat_little : ∀ a ∈ ℕ, ∀ p ∈ Prime, a^p ≡ a (mod p)

// Order theory  
axiom order_refl    : ∀ a, leq(a, a)
axiom order_antisym : ∀ a b, leq(a, b) → leq(b, a) → a = b
axiom order_trans   : ∀ a b c, leq(a, b) → leq(b, c) → leq(a, c)

// Real analysis
axiom diff_implies_cont : ∀ f a, differentiable(f, a) → continuous(f, a)
```

When these are explicit axioms in `.fl` files, users can grep for `axiom` in any proof and see exactly which unproved assumptions it rests on. This is the standard expected by the mathematical community (cf. Lean's `#print axioms` command).

---

## §8  Relative Consistency

This proof establishes consistency *relative to ZFC*: if ZFC is consistent, then the FuturLang kernel is consistent. This is the standard level of assurance for mathematical proof assistants. Coq's kernel is consistent relative to ZFC plus a small number of inaccessible cardinals; Lean 4's kernel is consistent relative to ZFC. We match that standard.

If ZFC is inconsistent (which would invalidate essentially all of modern mathematics), then all bets are off — but this is not considered a practical concern.

---


---

*This document is part of the FuturLang project. Contributions and corrections welcome.*
