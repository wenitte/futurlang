// src/checker/types.ts
// TypeScript data structures for the categorical proof kernel.

import { WenittainValue } from '../kernel/values';

export type KernelRule =
  | 'PREMISE'
  | 'ASSUMPTION'
  | 'IMPLIES_ELIM'
  | 'IMPLIES_INTRO'
  | 'AND_INTRO'
  | 'AND_ELIM_LEFT'
  | 'AND_ELIM_RIGHT'
  | 'OR_INTRO_LEFT'
  | 'OR_INTRO_RIGHT'
  | 'OR_ELIM'
  | 'NOT_INTRO'
  | 'CONTRADICTION'
  | 'BY_LEMMA'
  | 'REVELATION_APPLY'
  | 'REVELATION_OBJECT'
  | 'REVELATION_MORPHISM'
  | 'CAT_OBJECT'
  | 'CAT_MORPHISM'
  | 'CAT_COMPOSE'
  | 'CAT_IDENTITY'
  | 'CAT_ASSOC'
  | 'CAT_EQUALITY'
  | 'ISO_INTRO'
  | 'ISO_ELIM'
  | 'PRODUCT_INTRO'
  | 'PRODUCT_MEDIATOR'
  | 'PRODUCT_PROJ_LEFT'
  | 'PRODUCT_PROJ_RIGHT'
  | 'COPRODUCT_INTRO'
  | 'COPRODUCT_COPAIR'
  | 'PULLBACK_INTRO'
  | 'PULLBACK_MEDIATOR'
  | 'PUSHOUT_INTRO'
  | 'PUSHOUT_MEDIATOR'
  | 'FUNCTOR_INTRO'
  | 'FUNCTOR_ID'
  | 'FUNCTOR_COMPOSE'
  | 'FOLD_ELIM'
  | 'STRUCT_INTRO'
  | 'STRUCT_ELIM'
  | 'MATCH_EXHAUSTIVE'
  | 'STRUCTURAL';

export type ProofState = 'PROVED' | 'PENDING' | 'FAILED' | 'UNVERIFIED';

export interface Diagnostic {
  severity: 'error' | 'warning' | 'info';
  message: string;
  step?: number;
  hint?: string;
  rule?: KernelRule;
}

export interface ProofObject {
  id: string;
  claim: string;
  domain: string;
  codomain: string;
  domainRestriction: string;
  tau: WenittainValue;
  rule: KernelRule;
  inputs: string[];
  pending: boolean;
  suspended: boolean;
  step: number;
  imports?: string[];
}

export interface DerivationNode {
  id: string;
  rule: KernelRule;
  inputIds: string[];
  outputId: string;
  step: number;
}

export interface ProofStepTrace {
  step: number;
  kind: 'assume' | 'assert' | 'conclude' | 'apply' | 'setVar' | 'induction' | 'match' | 'raw';
  claim: string;
  rule: KernelRule;
  state: ProofState;
  message: string;
  uses?: string[];
  imports?: string[];
}

export interface ProofReport {
  name: string;
  state: ProofState;
  valid: boolean;
  stepCount: number;
  goal: string | null;
  premises: string[];
  derivedConclusion: string | null;
  proofSteps: ProofStepTrace[];
  proofObjects: ProofObject[];
  derivations: DerivationNode[];
  diagnostics: Diagnostic[];
  provedCount: number;
  pendingCount: number;
}

export interface FileReport {
  state: ProofState;
  valid: boolean;
  theoremCount: number;
  proofCount: number;
  pairedCount: number;
  reports: ProofReport[];
  diagnostics: Diagnostic[];
}

export interface CheckOptions {
  strict?: boolean;
}

export interface ClaimSet {
  name: string;
  premises: string[];
  conclusion: string | null;
  state: ProofState;
}
