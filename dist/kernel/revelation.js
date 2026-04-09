"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.RevelationError = void 0;
exports.applyRevelation = applyRevelation;
const values_1 = require("./values");
class RevelationError extends Error {
    constructor(message) {
        super(message);
        this.name = 'RevelationError';
    }
}
exports.RevelationError = RevelationError;
function applyRevelation(category, morphism, witness) {
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
function ensureTotalWitness(unresolvedTerms, witness) {
    for (const term of unresolvedTerms) {
        if (!witness.has(term)) {
            throw new RevelationError(`Revelation requires a total witness on U(P); missing '${term}'`);
        }
    }
}
function resolveTau(unresolvedTerms, witness) {
    let sawZero = false;
    for (const term of unresolvedTerms) {
        const value = witness.get(term);
        if (!value || !(0, values_1.isClassical)(value)) {
            throw new RevelationError(`Resolution monad algebra requires a resolved witness value for '${term}'`);
        }
        if (value === '0') {
            sawZero = true;
        }
    }
    return sawZero ? '0' : '1';
}
