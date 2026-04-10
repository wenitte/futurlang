"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.CategoryDiagramKernel = exports.CategoryDiagramError = void 0;
const propositions_1 = require("../checker/propositions");
class CategoryDiagramError extends Error {
    constructor(message) {
        super(message);
        this.name = 'CategoryDiagramError';
    }
}
exports.CategoryDiagramError = CategoryDiagramError;
const DEFAULT_CATEGORY = 'DefaultCategory';
class CategoryDiagramKernel {
    constructor() {
        this.categories = new Map();
        this.equalities = [];
        this.functors = new Map();
        this.ensureCategory(DEFAULT_CATEGORY);
    }
    registerClaim(claim) {
        const predicate = (0, propositions_1.parseCategoryPredicateCanonical)(claim);
        if (predicate) {
            this.registerPredicate(predicate.name, predicate.args);
            return;
        }
        const morphism = (0, propositions_1.parseMorphismDeclarationCanonical)(claim);
        if (morphism) {
            this.registerMorphism(DEFAULT_CATEGORY, morphism);
            return;
        }
        const equality = looksLikeCategoricalEquality(claim) ? (0, propositions_1.parseCategoricalEqualityCanonical)(claim) : null;
        if (equality) {
            try {
                const left = this.resolveMorphismExpr(equality.left);
                const right = this.resolveMorphismExpr(equality.right);
                if (left.category !== right.category) {
                    throw new CategoryDiagramError('Category error: objects or morphisms belong to different categories');
                }
                this.equalities.push({ left: equality.left, right: equality.right, category: left.category, valid: left.id === right.id || sameType(left, right) });
            }
            catch (e) {
                if (!(e instanceof CategoryDiagramError))
                    throw e;
                // Not a categorical equality (e.g. a measure-theory equality); skip registration.
            }
        }
    }
    ensureCategory(id) {
        const normalized = id.trim();
        const existing = this.categories.get(normalized);
        if (existing)
            return existing;
        const category = {
            id: normalized,
            objects: new Map(),
            morphisms: new Map(),
        };
        this.categories.set(normalized, category);
        return category;
    }
    ensureObject(categoryId, label) {
        const category = this.ensureCategory(categoryId);
        const normalized = normalize(label);
        const existing = category.objects.get(normalized);
        if (existing)
            return existing;
        const object = { id: `${category.id}:${normalized}`, category: category.id, label: normalized };
        category.objects.set(normalized, object);
        return object;
    }
    registerMorphism(categoryId, declaration) {
        const category = this.ensureCategory(categoryId);
        const domain = this.ensureObject(category.id, declaration.domain);
        const codomain = this.ensureObject(category.id, declaration.codomain);
        const existing = category.morphisms.get(normalize(declaration.label));
        if (existing)
            return existing;
        const morphism = {
            id: `${category.id}:${normalize(declaration.label)}`,
            category: category.id,
            label: normalize(declaration.label),
            domain: domain.id,
            codomain: codomain.id,
            primitive: true,
            components: [],
        };
        category.morphisms.set(morphism.label, morphism);
        return morphism;
    }
    resolveMorphismExpr(expr, categoryHint = DEFAULT_CATEGORY) {
        switch (expr.kind) {
            case 'name': {
                const category = this.ensureCategory(categoryHint);
                const direct = category.morphisms.get(normalize(expr.label));
                if (!direct)
                    throw new CategoryDiagramError(`Category error: unknown morphism '${expr.label}'`);
                return direct;
            }
            case 'identity': {
                const object = this.ensureObject(categoryHint, expr.object);
                return {
                    id: `${categoryHint}:id_${object.label}`,
                    category: categoryHint,
                    label: `id_${object.label}`,
                    domain: object.id,
                    codomain: object.id,
                    primitive: false,
                    components: [],
                };
            }
            case 'compose': {
                const right = this.resolveMorphismExpr(expr.right, categoryHint);
                const left = this.resolveMorphismExpr(expr.left, right.category);
                if (left.category !== right.category) {
                    throw new CategoryDiagramError('Category error: objects or morphisms belong to different categories');
                }
                if (right.codomain !== left.domain) {
                    throw new CategoryDiagramError(`Category error: morphisms do not compose (codomain of ${right.label} is ${objectLabel(right.codomain)}, domain of ${left.label} is ${objectLabel(left.domain)})`);
                }
                return {
                    id: `${left.category}:${normalize((0, propositions_1.formatMorphismExpr)(expr))}`,
                    category: left.category,
                    label: (0, propositions_1.formatMorphismExpr)(expr),
                    domain: right.domain,
                    codomain: left.codomain,
                    primitive: false,
                    components: [left.id, right.id],
                };
            }
            case 'functor_map': {
                const functor = this.functors.get(expr.functor);
                if (!functor) {
                    throw new CategoryDiagramError(`Category error: unknown functor '${expr.functor}'`);
                }
                const argument = this.resolveMorphismExpr(expr.argument, functor.source);
                if (argument.category !== functor.source) {
                    throw new CategoryDiagramError('Category error: objects or morphisms belong to different categories');
                }
                const sourceDomain = this.objectById(argument.domain);
                const sourceCodomain = this.objectById(argument.codomain);
                const mappedDomain = this.ensureObject(functor.target, `${expr.functor}(${sourceDomain.label})`);
                const mappedCodomain = this.ensureObject(functor.target, `${expr.functor}(${sourceCodomain.label})`);
                return {
                    id: `${functor.target}:${normalize((0, propositions_1.formatMorphismExpr)(expr))}`,
                    category: functor.target,
                    label: (0, propositions_1.formatMorphismExpr)(expr),
                    domain: mappedDomain.id,
                    codomain: mappedCodomain.id,
                    primitive: false,
                    components: [argument.id],
                };
            }
        }
    }
    equalMorphisms(leftExpr, rightExpr) {
        const left = this.resolveMorphismExpr(leftExpr);
        const right = this.resolveMorphismExpr(rightExpr, left.category);
        if (left.category !== right.category)
            return false;
        if (left.id === right.id)
            return true;
        if (sameType(left, right) && this.equalities.some(eq => eq.category === left.category &&
            (((0, propositions_1.formatMorphismExpr)(eq.left) === (0, propositions_1.formatMorphismExpr)(leftExpr) && (0, propositions_1.formatMorphismExpr)(eq.right) === (0, propositions_1.formatMorphismExpr)(rightExpr)) ||
                ((0, propositions_1.formatMorphismExpr)(eq.left) === (0, propositions_1.formatMorphismExpr)(rightExpr) && (0, propositions_1.formatMorphismExpr)(eq.right) === (0, propositions_1.formatMorphismExpr)(leftExpr))))) {
            return true;
        }
        return normalizeMorphism(left) === normalizeMorphism(right);
    }
    registerPredicate(name, args) {
        switch (name) {
            case 'Category':
                if (args[0])
                    this.ensureCategory(args[0]);
                return;
            case 'Object':
                if (args.length >= 2)
                    this.ensureObject(args[0], args[1]);
                return;
            case 'Morphism':
                if (args.length >= 4)
                    this.registerMorphism(args[0], { label: args[1], domain: args[2], codomain: args[3] });
                return;
            case 'Functor':
                if (args.length >= 3) {
                    this.ensureCategory(args[1]);
                    this.ensureCategory(args[2]);
                    this.functors.set(args[0], { source: args[1], target: args[2] });
                }
                return;
            default:
                return;
        }
    }
    objectById(id) {
        for (const category of this.categories.values()) {
            for (const object of category.objects.values()) {
                if (object.id === id)
                    return object;
            }
        }
        throw new CategoryDiagramError(`Category error: unknown object '${id}'`);
    }
}
exports.CategoryDiagramKernel = CategoryDiagramKernel;
function looksLikeCategoricalEquality(claim) {
    return claim.includes('∘') || /\bid_/.test(claim) || /^[A-Z][\w₀-₉ₐ-ₙ]*\(.+\)\s*=/.test(claim);
}
function normalize(value) {
    return value.trim().replace(/\s+/g, ' ');
}
function normalizeMorphism(morphism) {
    return `${morphism.category}:${morphism.domain}:${morphism.codomain}:${morphism.label}`;
}
function sameType(left, right) {
    return left.category === right.category && left.domain === right.domain && left.codomain === right.codomain;
}
function objectLabel(id) {
    const index = id.indexOf(':');
    return index === -1 ? id : id.slice(index + 1);
}
