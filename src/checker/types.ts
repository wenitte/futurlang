// src/checker/types.ts
// Core types for the natural deduction proof checker

import { Sort } from './sorts';

export type CheckResult =
  | { valid: true;  rule: InferenceRule; message: string }
  | { valid: false; rule: InferenceRule; message: string; hint?: string };

// The inference rules supported by the kernel
export type InferenceRule =
  // Structural
  | 'ASSUMPTION'        // assume(P) introduces P into context
  | 'PREMISE'           // theorem/lemma premise available in the current proof context
  | 'DEFINITION'        // define(X) ↔ ... introduces X into context
  | 'VARIABLE'          // setVar(x: T) introduces typed variable
  // Propositional
  | 'IMPLIES_INTRO'     // assume(P) → ... → conclude(Q) proves P → Q
  | 'IMPLIES_ELIM'      // have P → Q, have P, conclude Q  (modus ponens)
  | 'AND_INTRO'         // have P, have Q, conclude P ∧ Q
  | 'AND_ELIM'          // have P ∧ Q, conclude P  or  have P ∧ Q, conclude Q
  | 'AND_ELIM_LEFT'     // have P ∧ Q, conclude P
  | 'AND_ELIM_RIGHT'    // have P ∧ Q, conclude Q
  | 'OR_INTRO_LEFT'     // have P, conclude P ∨ Q
  | 'OR_INTRO_RIGHT'    // have Q, conclude P ∨ Q
  | 'OR_ELIM'           // have P ∨ Q, P → R, Q → R, conclude R
  | 'NOT_INTRO'         // assume P, derive ⊥, conclude ¬P
  | 'NOT_ELIM'          // have ¬¬P, conclude P  (double negation elimination)
  | 'EX_FALSO'          // have ⊥, conclude anything
  // Set-theoretic
  | 'SUBSET_ELIM'       // have x ∈ A, have A ⊆ B, conclude x ∈ B
  | 'SUBSET_TRANS'      // have A ⊆ B, have B ⊆ C, conclude A ⊆ C
  | 'EQUALITY_REFL'     // conclude x = x
  | 'EQUALITY_SYMM'     // have x = y, conclude y = x
  | 'EQUALITY_TRANS'    // have x = y, have y = z, conclude x = z
  | 'ARITHMETIC_COMM'   // have a = b · c, conclude a = c · b
  | 'EQUALITY_SUBST'    // have x = y and x ∈ A, conclude y ∈ A
  | 'UNION_INTRO'       // have x ∈ A, conclude x ∈ A ∪ B
  | 'SET_BUILDER_INTRO' // have a ∈ A, conclude T(a) ∈ {T(x) | x ∈ A}
  | 'INDEXED_UNION_INTRO' // have a ∈ A and y ∈ T(a), conclude y ∈ ∪{T(x) | x ∈ A}
  | 'INDEXED_UNION_ELIM' // have y ∈ ∪{T(x) | x ∈ A}, open a ∈ A and y ∈ T(a), conclude witness-free Q
  | 'SET_MEMBERSHIP_EQ' // have ∀z∈A, z∈B and ∀z∈B, z∈A, conclude A = B
  | 'INTERSECTION_INTRO'// have x ∈ A and x ∈ B, conclude x ∈ A ∩ B
  | 'INTERSECTION_ELIM' // have x ∈ A ∩ B, conclude x ∈ A or x ∈ B
  | 'FORALL_TYPED_ELIM' // have ∀x: T, P(x) and a: T, conclude P(a)
  | 'FORALL_TYPED_INTRO'// open fresh typed variable a: T and derive P(a), conclude ∀x: T, P(x)
  | 'EXISTS_TYPED_INTRO'// have a: T and P(a), conclude ∃x: T, P(x)
  | 'EXISTS_TYPED_ELIM' // have ∃x: T, P(x), open a: T and P(a), conclude witness-free Q
  | 'EXISTS_UNIQUE_INTRO' // have existence and uniqueness, conclude ∃!x, P(x)
  | 'EXISTS_UNIQUE_ELIM' // from ∃!x, P(x) recover existence or uniqueness component
  | 'DIVIDES_INTRO' // have b = a · k (or b = k · a), conclude a divides b
  | 'FORALL_IN_ELIM'    // have ∀x ∈ A, P(x) and a ∈ A, conclude P(a)
  | 'FORALL_IN_INTRO'   // open fresh witness a with a ∈ A and derive P(a), conclude ∀x ∈ A, P(x)
  | 'EXISTS_IN_INTRO'   // have a ∈ A and P(a), conclude ∃x ∈ A, P(x)
  | 'EXISTS_IN_ELIM'    // have ∃x ∈ A, P(x), open witness a with a ∈ A and P(a), conclude witness-free Q
  // Proof methods
  | 'CONTRADICTION'     // assume(¬P), derive ⊥, conclude P
  | 'INDUCTION'         // base_case + inductive_step → conclude ∀n.P(n)
  | 'BY_LEMMA'          // apply(Lemma) uses a previously proven result
  // Meta
  | 'THEOREM_PROOF'     // theorem ↔ proof pairing is valid
  | 'SORRY'             // explicit gap marker — valid structure, unverified step
  | 'STRUCTURAL'        // basic structural validity — claim is UNVERIFIED

// Three-way proof object status
export type ProofObjectStatus = 'PROVED' | 'UNVERIFIED';

export interface ProofContext {
  // What we've established so far in this proof (PROVED claims only)
  established: Claim[];
  // Claims that were accepted structurally without a derivation (UNVERIFIED)
  unverified: Claim[];
  // Normalized claim strings of UNVERIFIED claims (for fast lookup in isEstablished)
  unverifiedContents: Set<string>;
  // Internal proof objects for established facts in this proof.
  proofObjects: ProofObject[];
  // Internal derivation nodes connecting input proof objects to output proof objects.
  derivations: DerivationNode[];
  // Variables in scope
  variables: Variable[];
  // Sort scope: variable name → sort (for set-theoretic scope checking)
  sortScope: Map<string, Sort>;
  // Explicit nested proof scopes currently open.
  currentScopes: ScopeFrame[];
  // Lemmas available (from earlier in the file or inline)
  lemmas: Map<string, ClaimSet>;
  // The current proof method (contradiction, induction, direct)
  method: ProofMethod;
  // Are we inside a contradiction block (negated assumption in scope)?
  inContradiction: boolean;
  // The current goal proposition, when checking a theorem/proof pair.
  goal: string | null;
}

export interface Claim {
  content: string;       // the claim text
  source: ClaimSource;   // how it was established
  step: number;          // which step introduced it
  scopeIds: string[];
  proofObjectId?: string;
}

export type ClaimSource =
  | 'assumption'
  | 'premise'
  | 'definition'
  | 'variable'
  | 'assertion'
  | 'lemma_application'
  | 'conclusion'

export interface Variable {
  name: string;
  type: string | null;
  step: number;
  scopeId: string;
}

export interface ScopeFrame {
  id: string;
  kind: 'variable' | 'assumption';
  label: string;
  step: number;
}

export type ProofMethod = 'direct' | 'contradiction' | 'induction' | 'construction' | 'unknown';

export interface ClaimSet {
  hypotheses: string[];
  conclusions: string[];
  name?: string;
}

export interface ProofObject {
  id: string;
  claim: string;
  rule: InferenceRule;
  source: ClaimSource;
  step: number;
  scopeIds: string[];
  dischargedScopeIds?: string[];
  dependsOn: string[];
  dependsOnIds: string[];
  imports?: string[];
  status: ProofObjectStatus;
}

export interface DerivationNode {
  id: string;
  step: number;
  rule: InferenceRule;
  inputIds: string[];
  outputId: string;
  dischargedScopeIds?: string[];
}

// A diagnostic message from the checker
export interface Diagnostic {
  severity: 'error' | 'warning' | 'info';
  message: string;
  step?: number;         // which proof step
  hint?: string;         // how to fix it
  rule?: InferenceRule;
}

export interface ProofStepTrace {
  step: number;
  kind: 'assume' | 'assert' | 'conclude' | 'apply' | 'setVar' | 'raw' | 'lemma';
  claim: string;
  rule: InferenceRule;
  valid: boolean;
  message: string;
  status?: ProofObjectStatus;
  uses?: string[];
  imports?: string[];
  establishesAs?: ClaimSource;
}

// Full check report for one theorem+proof pair
export interface ProofReport {
  name: string;
  valid: boolean;
  method: ProofMethod;
  stepCount: number;
  goal: string | null;
  premises: string[];
  derivedConclusion: string | null;
  proofSteps: ProofStepTrace[];
  proofObjects: ProofObject[];
  derivations: DerivationNode[];
  baseFactIds: string[];
  derivedFactIds: string[];
  diagnostics: Diagnostic[];
  // Counts for PROVED vs UNVERIFIED proof objects
  provedCount: number;
  unverifiedCount: number;
  // Structural metrics useful as training signal
  metrics: {
    assumptionCount: number;
    assertionCount: number;
    lemmaApplicationCount: number;
    hasConclusion: boolean;
    hasSorry: boolean;
    dependencyDepth: number;  // longest chain of → in proof body
  };
}

// Full check report for an entire .fl file
export interface FileReport {
  valid: boolean;
  theoremCount: number;
  proofCount: number;
  pairedCount: number;    // theorem ↔ proof pairs
  reports: ProofReport[];
  diagnostics: Diagnostic[];  // file-level diagnostics
  score: number;              // 0-100, training data quality score
}

export interface CheckOptions {
  strict?: boolean;
}
