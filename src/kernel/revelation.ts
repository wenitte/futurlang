import { MorphismRecord, WenittainCategory } from './category';
import { isClassical, WenittainValue } from './values';

export type CausalWitness = Map<string, WenittainValue>;

export class RevelationError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'RevelationError';
  }
}

export function applyRevelation(
  category: WenittainCategory,
  morphism: MorphismRecord,
  witness: CausalWitness,
): MorphismRecord {
  ensureTotalWitness(morphism.unresolvedTerms, witness);
  const tau = resolveTau(morphism.unresolvedTerms, witness);
  const resolved = category.createMorphism({
    proposition: morphism.proposition,
    domain: morphism.domain,
    codomain: morphism.codomain,
    tau,
    rule: 'REVELATION_APPLY',
    inputs: [morphism.id],
    unresolvedTerms: [],
    domainRestriction: morphism.domain,
    suspended: false,
  });
  category.pendingMorphisms.delete(morphism.id);
  return resolved;
}

function ensureTotalWitness(unresolvedTerms: string[], witness: CausalWitness): void {
  for (const term of unresolvedTerms) {
    if (!witness.has(term)) {
      throw new RevelationError(`Revelation requires a total witness on U(P); missing '${term}'`);
    }
  }
}

function resolveTau(unresolvedTerms: string[], witness: CausalWitness): '0' | '1' {
  let sawZero = false;
  for (const term of unresolvedTerms) {
    const value = witness.get(term);
    if (!value || !isClassical(value)) {
      throw new RevelationError(`Resolution monad algebra requires a resolved witness value for '${term}'`);
    }
    if (value === '0') {
      sawZero = true;
    }
  }
  return sawZero ? '0' : '1';
}
