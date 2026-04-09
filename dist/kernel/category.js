"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.WenittainCategory = exports.KernelError = void 0;
const crypto_1 = require("crypto");
const values_1 = require("./values");
class KernelError extends Error {
    constructor(message) {
        super(message);
        this.name = 'KernelError';
    }
}
exports.KernelError = KernelError;
class WenittainCategory {
    constructor() {
        this.objects = new Map();
        this.morphisms = new Map();
        this.pendingMorphisms = new Map();
        this.resolutionMonad = {
            unit: (proposition) => `T(${proposition})`,
            multiply: (proposition) => `T(${proposition})`,
        };
    }
    createObject(proposition, tau = '1', unresolvedTerms = [], options = {}) {
        const id = objectId(proposition);
        const partial = tau === 'ω' || unresolvedTerms.length > 0;
        const object = {
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
    createMorphism(input) {
        const pending = input.tau === 'ω';
        const morphism = {
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
    complementOf(proposition) {
        const display = proposition.startsWith('¬') ? proposition.slice(1).trim() : `¬${proposition}`;
        const object = this.createObject(display);
        const source = this.createObject(proposition, object.tau, [], { complementId: object.id });
        object.complementId = source.id;
        this.objects.set(source.id, source);
        this.objects.set(object.id, object);
        return object;
    }
    classicalImplication(left, right) {
        return `${this.complementDisplay(left)} ∨ ${right}`;
    }
    suspendObject(proposition, unresolvedTerms = []) {
        const suspended = this.resolutionMonad.unit(proposition);
        return this.createObject(suspended, 'ω', unresolvedTerms, { suspended: true });
    }
    compose(left, right, proposition, rule) {
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
            tau: (0, values_1.implies)(left.tau, right.tau),
            rule,
            inputs: [left.id, right.id],
            unresolvedTerms: [...left.unresolvedTerms, ...right.unresolvedTerms],
            domainRestriction: right.domainRestriction,
            suspended: left.suspended || right.suspended,
        });
    }
    ensureClassical(morphism) {
        if (!(0, values_1.isClassical)(morphism.tau) || morphism.pending) {
            throw new KernelError('ω-Barrier: pending morphism cannot be used in classical derivation before Ra fires');
        }
    }
    truthValueOfMorphism(morphism) {
        if (morphism.pending || morphism.suspended)
            return 'ω';
        if (morphism.codomain === objectId('⊥') || morphism.proposition === '⊥')
            return '0';
        return morphism.tau;
    }
    meetTruth(left, right) {
        return (0, values_1.and)(left, right);
    }
    joinTruth(left, right) {
        return (0, values_1.or)(left, right);
    }
    complementTruth(value) {
        return (0, values_1.neg)(value);
    }
    complementDisplay(proposition) {
        return proposition.startsWith('¬') ? proposition.slice(1).trim() : `¬${proposition}`;
    }
}
exports.WenittainCategory = WenittainCategory;
function objectId(proposition) {
    return `obj:${stableHash(proposition)}`;
}
function morphismId(proposition, rule, inputs) {
    return `mor:${stableHash(`${proposition}|${rule}|${inputs.join(',')}`)}`;
}
function stableHash(value) {
    return (0, crypto_1.createHash)('sha256').update(value).digest('hex').slice(0, 16);
}
