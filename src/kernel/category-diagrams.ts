import {
  formatMorphismExpr,
  MorphismDeclarationProp,
  MorphismExpr,
  parseCategoricalEqualityCanonical,
  parseCategoryPredicateCanonical,
  parseMorphismDeclarationCanonical,
} from '../checker/propositions';

export interface ObjectRecord {
  id: string;
  category: string;
  label: string;
}

export interface MorphismRecord {
  id: string;
  category: string;
  label: string;
  domain: string;
  codomain: string;
  primitive: boolean;
  components: string[];
}

export interface CategoryRecord {
  id: string;
  objects: Map<string, ObjectRecord>;
  morphisms: Map<string, MorphismRecord>;
}

export interface DiagramEqualityRecord {
  left: MorphismExpr;
  right: MorphismExpr;
  category: string;
  valid: boolean;
}

export class CategoryDiagramError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'CategoryDiagramError';
  }
}

const DEFAULT_CATEGORY = 'DefaultCategory';

export class CategoryDiagramKernel {
  readonly categories = new Map<string, CategoryRecord>();
  readonly equalities: DiagramEqualityRecord[] = [];
  readonly functors = new Map<string, { source: string; target: string }>();

  constructor() {
    this.ensureCategory(DEFAULT_CATEGORY);
  }

  registerClaim(claim: string): void {
    const predicate = parseCategoryPredicateCanonical(claim);
    if (predicate) {
      this.registerPredicate(predicate.name, predicate.args);
      return;
    }

    const morphism = parseMorphismDeclarationCanonical(claim);
    if (morphism) {
      this.registerMorphism(DEFAULT_CATEGORY, morphism);
      return;
    }

    const equality = looksLikeCategoricalEquality(claim) ? parseCategoricalEqualityCanonical(claim) : null;
    if (equality) {
      try {
        const left = this.resolveMorphismExpr(equality.left);
        const right = this.resolveMorphismExpr(equality.right);
        if (left.category !== right.category) {
          throw new CategoryDiagramError('Category error: objects or morphisms belong to different categories');
        }
        this.equalities.push({ left: equality.left, right: equality.right, category: left.category, valid: left.id === right.id || sameType(left, right) });
      } catch (e) {
        if (!(e instanceof CategoryDiagramError)) throw e;
        // Not a categorical equality (e.g. a measure-theory equality); skip registration.
      }
    }
  }

  ensureCategory(id: string): CategoryRecord {
    const normalized = id.trim();
    const existing = this.categories.get(normalized);
    if (existing) return existing;
    const category: CategoryRecord = {
      id: normalized,
      objects: new Map<string, ObjectRecord>(),
      morphisms: new Map<string, MorphismRecord>(),
    };
    this.categories.set(normalized, category);
    return category;
  }

  ensureObject(categoryId: string, label: string): ObjectRecord {
    const category = this.ensureCategory(categoryId);
    const normalized = normalize(label);
    const existing = category.objects.get(normalized);
    if (existing) return existing;
    const object: ObjectRecord = { id: `${category.id}:${normalized}`, category: category.id, label: normalized };
    category.objects.set(normalized, object);
    return object;
  }

  registerMorphism(categoryId: string, declaration: MorphismDeclarationProp): MorphismRecord {
    const category = this.ensureCategory(categoryId);
    const domain = this.ensureObject(category.id, declaration.domain);
    const codomain = this.ensureObject(category.id, declaration.codomain);
    const existing = category.morphisms.get(normalize(declaration.label));
    if (existing) return existing;
    const morphism: MorphismRecord = {
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

  resolveMorphismExpr(expr: MorphismExpr, categoryHint: string = DEFAULT_CATEGORY): MorphismRecord {
    switch (expr.kind) {
      case 'name': {
        const category = this.ensureCategory(categoryHint);
        const direct = category.morphisms.get(normalize(expr.label));
        if (!direct) throw new CategoryDiagramError(`Category error: unknown morphism '${expr.label}'`);
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
          throw new CategoryDiagramError(
            `Category error: morphisms do not compose (codomain of ${right.label} is ${objectLabel(right.codomain)}, domain of ${left.label} is ${objectLabel(left.domain)})`,
          );
        }
        return {
          id: `${left.category}:${normalize(formatMorphismExpr(expr))}`,
          category: left.category,
          label: formatMorphismExpr(expr),
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
          id: `${functor.target}:${normalize(formatMorphismExpr(expr))}`,
          category: functor.target,
          label: formatMorphismExpr(expr),
          domain: mappedDomain.id,
          codomain: mappedCodomain.id,
          primitive: false,
          components: [argument.id],
        };
      }
    }
  }

  equalMorphisms(leftExpr: MorphismExpr, rightExpr: MorphismExpr): boolean {
    const left = this.resolveMorphismExpr(leftExpr);
    const right = this.resolveMorphismExpr(rightExpr, left.category);
    if (left.category !== right.category) return false;
    if (left.id === right.id) return true;
    if (sameType(left, right) && this.equalities.some(eq =>
      eq.category === left.category &&
      ((formatMorphismExpr(eq.left) === formatMorphismExpr(leftExpr) && formatMorphismExpr(eq.right) === formatMorphismExpr(rightExpr)) ||
        (formatMorphismExpr(eq.left) === formatMorphismExpr(rightExpr) && formatMorphismExpr(eq.right) === formatMorphismExpr(leftExpr))),
    )) {
      return true;
    }
    return normalizeMorphism(left) === normalizeMorphism(right);
  }

  registerPredicate(name: string, args: string[]): void {
    switch (name) {
      case 'Category':
        if (args[0]) this.ensureCategory(args[0]);
        return;
      case 'Object':
        if (args.length >= 2) this.ensureObject(args[0], args[1]);
        return;
      case 'Morphism':
        if (args.length >= 4) this.registerMorphism(args[0], { label: args[1], domain: args[2], codomain: args[3] });
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

  objectById(id: string): ObjectRecord {
    for (const category of this.categories.values()) {
      for (const object of category.objects.values()) {
        if (object.id === id) return object;
      }
    }
    throw new CategoryDiagramError(`Category error: unknown object '${id}'`);
  }
}

function looksLikeCategoricalEquality(claim: string): boolean {
  return claim.includes('∘') || /\bid_/.test(claim) || /^[A-Z][\w₀-₉ₐ-ₙ]*\(.+\)\s*=/.test(claim);
}

function normalize(value: string): string {
  return value.trim().replace(/\s+/g, ' ');
}

function normalizeMorphism(morphism: MorphismRecord): string {
  return `${morphism.category}:${morphism.domain}:${morphism.codomain}:${morphism.label}`;
}

function sameType(left: MorphismRecord, right: MorphismRecord): boolean {
  return left.category === right.category && left.domain === right.domain && left.codomain === right.codomain;
}

function objectLabel(id: string): string {
  const index = id.indexOf(':');
  return index === -1 ? id : id.slice(index + 1);
}
