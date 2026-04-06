// src/checker/types.ts
// Core types for the natural deduction proof checker

export type CheckResult =
  | { valid: true;  rule: InferenceRule; message: string }
  | { valid: false; rule: InferenceRule; message: string; hint?: string };

// The 12 inference rules we check
export type InferenceRule =
  // Structural
  | 'ASSUMPTION'        // assume(P) introduces P into context
  | 'DEFINITION'        // define(X) ↔ ... introduces X into context
  | 'VARIABLE'          // setVar(x: T) introduces typed variable
  // Propositional
  | 'IMPLIES_INTRO'     // assume(P) → ... → conclude(Q) proves P → Q
  | 'IMPLIES_ELIM'      // have P → Q, have P, conclude Q  (modus ponens)
  | 'AND_INTRO'         // have P, have Q, conclude P ∧ Q
  | 'AND_ELIM'          // have P ∧ Q, conclude P (or Q)
  | 'OR_INTRO'          // have P, conclude P ∨ Q
  | 'IFF_INTRO'         // prove P → Q and Q → P, conclude P ↔ Q
  // Proof methods
  | 'CONTRADICTION'     // assume(¬P), derive ⊥, conclude P
  | 'INDUCTION'         // base_case + inductive_step → conclude ∀n.P(n)
  | 'BY_LEMMA'          // apply(Lemma) uses a previously proven result
  // Meta
  | 'THEOREM_PROOF'     // theorem ↔ proof pairing is valid
  | 'SORRY'             // explicit gap marker — valid structure, unverified step
  | 'STRUCTURAL'        // basic structural validity

export interface ProofContext {
  // What we've established so far in this proof
  established: Claim[];
  // Variables in scope
  variables: Variable[];
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
}

export type ClaimSource =
  | 'assumption'
  | 'definition'
  | 'variable'
  | 'assertion'
  | 'lemma_application'
  | 'conclusion'

export interface Variable {
  name: string;
  type: string | null;
  step: number;
}

export type ProofMethod = 'direct' | 'contradiction' | 'induction' | 'construction' | 'unknown';

export interface ClaimSet {
  hypotheses: string[];
  conclusions: string[];
}

// A diagnostic message from the checker
export interface Diagnostic {
  severity: 'error' | 'warning' | 'info';
  message: string;
  step?: number;         // which proof step
  hint?: string;         // how to fix it
  rule?: InferenceRule;
}

// Full check report for one theorem+proof pair
export interface ProofReport {
  name: string;
  valid: boolean;
  method: ProofMethod;
  stepCount: number;
  goal: string | null;
  derivedConclusion: string | null;
  diagnostics: Diagnostic[];
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
