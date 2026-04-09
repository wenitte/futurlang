import { createHash } from 'crypto';
import { and, implies, isClassical, neg, or, WenittainValue } from './values';
import { KernelRule } from '../checker/types';

export class KernelError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'KernelError';
  }
}

export interface CategoryObject {
  id: string;
  proposition: string;
  tau: WenittainValue;
  partial: boolean;
  unresolvedTerms: string[];
  complementId?: string;
  suspended: boolean;
}

export interface MorphismRecord {
  id: string;
  domain: string;
  codomain: string;
  tau: WenittainValue;
  rule: KernelRule;
  inputs: string[];
  pending: boolean;
  proposition: string;
  unresolvedTerms: string[];
  domainRestriction: string;
  suspended: boolean;
}

export interface ResolutionMonad {
  unit<P extends string>(proposition: P): string;
  multiply<P extends string>(proposition: P): string;
}

export class WenittainCategory {
  readonly objects = new Map<string, CategoryObject>();
  readonly morphisms = new Map<string, MorphismRecord>();
  readonly pendingMorphisms = new Map<string, MorphismRecord>();
  readonly resolutionMonad: ResolutionMonad = {
    unit: (proposition) => `T(${proposition})`,
    multiply: (proposition) => `T(${proposition})`,
  };

  createObject(
    proposition: string,
    tau: WenittainValue = '1',
    unresolvedTerms: string[] = [],
    options: { suspended?: boolean; complementId?: string } = {},
  ): CategoryObject {
    const id = objectId(proposition);
    const partial = tau === 'ω' || unresolvedTerms.length > 0;
    const object: CategoryObject = {
      id,
      proposition,
      tau,
      partial,
      unresolvedTerms: [...new Set(unresolvedTerms)],
      complementId: options.complementId,
      suspended: options.suspended ?? tau === 'ω',
    };
    this.objects.set(id, object);
    return object;
  }

  createMorphism(input: {
    proposition: string;
    domain: string;
    codomain: string;
    tau: WenittainValue;
    rule: KernelRule;
    inputs?: string[];
    unresolvedTerms?: string[];
    domainRestriction?: string;
    suspended?: boolean;
  }): MorphismRecord {
    const pending = input.tau === 'ω';
    const morphism: MorphismRecord = {
      id: morphismId(input.proposition, input.rule, input.inputs ?? []),
      domain: input.domain,
      codomain: input.codomain,
      tau: input.tau,
      rule: input.rule,
      inputs: input.inputs ?? [],
      pending,
      proposition: input.proposition,
      unresolvedTerms: [...new Set(input.unresolvedTerms ?? [])],
      domainRestriction: input.domainRestriction ?? input.domain,
      suspended: input.suspended ?? pending,
    };
    this.morphisms.set(morphism.id, morphism);
    if (pending) {
      this.pendingMorphisms.set(morphism.id, morphism);
    }
    return morphism;
  }

  complementOf(proposition: string): CategoryObject {
    const display = proposition.startsWith('¬') ? proposition.slice(1).trim() : `¬${proposition}`;
    const object = this.createObject(display);
    const source = this.createObject(proposition, object.tau, [], { complementId: object.id });
    object.complementId = source.id;
    this.objects.set(source.id, source);
    this.objects.set(object.id, object);
    return object;
  }

  classicalImplication(left: string, right: string): string {
    return `${this.complementDisplay(left)} ∨ ${right}`;
  }

  suspendObject(proposition: string, unresolvedTerms: string[] = []): CategoryObject {
    const suspended = this.resolutionMonad.unit(proposition);
    return this.createObject(suspended, 'ω', unresolvedTerms, { suspended: true });
  }

  compose(left: MorphismRecord, right: MorphismRecord, proposition: string, rule: KernelRule): MorphismRecord {
    if (left.codomain !== right.domain) {
      throw new KernelError(`Invalid composition: ${left.codomain} does not match ${right.domain}`);
    }
    if (left.pending || right.pending) {
      throw new KernelError('ω-Barrier: pending morphism cannot be used in classical derivation before Ra fires');
    }
    return this.createMorphism({
      proposition,
      domain: left.domain,
      codomain: right.codomain,
      tau: implies(left.tau, right.tau),
      rule,
      inputs: [left.id, right.id],
      unresolvedTerms: [...left.unresolvedTerms, ...right.unresolvedTerms],
      domainRestriction: right.domainRestriction,
      suspended: left.suspended || right.suspended,
    });
  }

  ensureClassical(morphism: MorphismRecord): void {
    if (!isClassical(morphism.tau) || morphism.pending) {
      throw new KernelError('ω-Barrier: pending morphism cannot be used in classical derivation before Ra fires');
    }
  }

  truthValueOfMorphism(morphism: MorphismRecord): WenittainValue {
    if (morphism.pending || morphism.suspended) return 'ω';
    if (morphism.codomain === objectId('⊥') || morphism.proposition === '⊥') return '0';
    return morphism.tau;
  }

  meetTruth(left: WenittainValue, right: WenittainValue): WenittainValue {
    return and(left, right);
  }

  joinTruth(left: WenittainValue, right: WenittainValue): WenittainValue {
    return or(left, right);
  }

  complementTruth(value: WenittainValue): WenittainValue {
    return neg(value);
  }

  private complementDisplay(proposition: string): string {
    return proposition.startsWith('¬') ? proposition.slice(1).trim() : `¬${proposition}`;
  }
}

function objectId(proposition: string): string {
  return `obj:${stableHash(proposition)}`;
}

function morphismId(proposition: string, rule: KernelRule, inputs: string[]): string {
  return `mor:${stableHash(`${proposition}|${rule}|${inputs.join(',')}`)}`;
}

function stableHash(value: string): string {
  return createHash('sha256').update(value).digest('hex').slice(0, 16);
}
