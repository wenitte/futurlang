import { ExprNode, QuantifiedNode } from '../parser/ast';
import { parseExpr, normalizeSurfaceSyntax } from '../parser/expr';

export type CanonicalProp =
  | { kind: 'membership'; element: string; set: string }
  | { kind: 'nonmembership'; element: string; set: string }
  | { kind: 'subset'; left: string; right: string; strict: boolean }
  | { kind: 'equality'; left: string; right: string }
  | { kind: 'typed_variable'; variable: string; domain: string }
  | { kind: 'atom'; value: string };

export interface CanonicalSetBuilderTerm {
  elementTemplate: string;
  variable: string;
  domain: string;
}

export type QuantifierKind = 'forall' | 'exists' | 'exists_unique';

export interface BoundedQuantifierProp {
  kind: QuantifierKind;
  variable: string;
  set: string;
  body: string;
}

export interface TypedQuantifierProp {
  kind: QuantifierKind;
  variable: string;
  domain: string;
  body: string;
}

export interface StandaloneBoundedQuantifierProp {
  kind: QuantifierKind;
  variable: string;
  set: string;
}

export interface StandaloneTypedQuantifierProp {
  kind: QuantifierKind;
  variable: string;
  domain: string;
}

export interface MorphismDeclarationProp {
  label: string;
  domain: string;
  codomain: string;
}

export type MorphismExpr =
  | { kind: 'name'; label: string }
  | { kind: 'identity'; object: string }
  | { kind: 'compose'; left: MorphismExpr; right: MorphismExpr }
  | { kind: 'functor_map'; functor: string; argument: MorphismExpr };

export interface CategoryPredicateProp {
  name: 'Category' | 'Object' | 'Morphism' | 'Iso' | 'Product' | 'ProductMediator' | 'Coproduct' | 'Pullback' | 'Pushout' | 'Functor';
  args: string[];
}

export function exprToProp(expr: ExprNode): string {
  switch (expr.type) {
    case 'Atom':    return expr.condition;
    case 'SetBuilder':
      return `{${expr.element} | ${expr.variable} ∈ ${expr.domain}}`;
    case 'IndexedUnion':
      return `∪${exprToProp(expr.builder)}`;
    case 'Fold':
      return `fold(${expr.sequence}, ${expr.init}, ${expr.fn})`;
    case 'If':
      return `if ${exprToProp(expr.condition)} then ${exprToProp(expr.thenBranch)} else ${exprToProp(expr.elseBranch)}`;
    case 'LetExpr':
      return `let ${expr.name} = ${exprToProp(expr.value)} in ${exprToProp(expr.body)}`;
    case 'Lambda':
      return `fn(${expr.params.map(param => `${param.name}: ${param.type}`).join(', ')}) => ${exprToProp(expr.body)}`;
    case 'And':     return `${exprToProp(expr.left)} ∧ ${exprToProp(expr.right)}`;
    case 'Or':      return `${exprToProp(expr.left)} ∨ ${exprToProp(expr.right)}`;
    case 'Implies': return `${exprToProp(expr.left)} → ${exprToProp(expr.right)}`;
    case 'Iff':     return `${exprToProp(expr.left)} ↔ ${exprToProp(expr.right)}`;
    case 'Not':     return `¬${exprToProp(expr.operand)}`;
    case 'Quantified': {
      const symbol = expr.quantifier === 'forall' ? '∀' : expr.quantifier === 'exists' ? '∃' : '∃!';
      const binder = expr.binderStyle === 'bounded'
        ? `${expr.variable} ∈ ${expr.domain}`
        : `${expr.variable}: ${expr.domain}`;
      return expr.body ? `${symbol} ${binder}, ${exprToProp(expr.body)}` : `${symbol} ${binder}`;
    }
    default:        return '';
  }
}

export function normalizeProp(s: string): string {
  try {
    return propKey(parseCanonicalExpr(s)).trim().toLowerCase().replace(/\s+/g, ' ');
  } catch {
    return s.trim().toLowerCase().replace(/\s+/g, ' ');
  }
}

export function sameProp(a: string, b: string): boolean {
  return normalizeProp(a) === normalizeProp(b);
}

export function canonicalizeProp(s: string): string {
  const trimmed = s.trim();
  if (!trimmed) return trimmed;
  try {
    return canonicalDisplay(parseCanonicalExpr(trimmed));
  } catch {
    return trimmed;
  }
}

export function parseCanonicalExpr(input: string): ExprNode | CanonicalProp {
  const trimmed = input.trim();
  try {
    const parsed = parseExpr(trimmed);
    return canonicalizeExpr(parsed);
  } catch {
    // When the expression parser fails (e.g. due to function-call syntax like f(x)),
    // apply surface normalization before atom canonicalization so that word aliases
    // like "in" → "∈" are resolved consistently.
    return canonicalizeAtom(normalizeSurfaceSyntax(trimmed));
  }
}

function canonicalizeExpr(expr: ExprNode): ExprNode | CanonicalProp {
  if (expr.type !== 'Atom') return expr;
  return canonicalizeAtom(expr.condition);
}

function canonicalizeAtom(value: string): CanonicalProp {
  const normalized = normalizeTerm(value);
  const typed = splitTopLevelAtom(normalized, ':');
  if (typed && /^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(typed[0])) {
    return {
      kind: 'typed_variable',
      variable: normalizeTerm(typed[0]),
      domain: normalizeTerm(typed[1]),
    };
  }

  const nonmembership = splitTopLevelAtom(normalized, '∉');
  if (nonmembership) {
    return {
      kind: 'nonmembership',
      element: normalizeTerm(nonmembership[0]),
      set: normalizeTerm(nonmembership[1]),
    };
  }

  const membership = splitTopLevelAtom(normalized, '∈');
  if (membership) {
    return {
      kind: 'membership',
      element: normalizeTerm(membership[0]),
      set: normalizeTerm(membership[1]),
    };
  }

  const subseteq = splitTopLevelAtom(normalized, '⊆');
  if (subseteq) {
    return {
      kind: 'subset',
      left: normalizeTerm(subseteq[0]),
      strict: true,
      right: normalizeTerm(subseteq[1]),
    };
  }

  const strictSubset = splitTopLevelAtom(normalized, '⊂');
  if (strictSubset) {
    return {
      kind: 'subset',
      left: normalizeTerm(strictSubset[0]),
      strict: false,
      right: normalizeTerm(strictSubset[1]),
    };
  }

  const equality = splitTopLevelAtom(normalized, '=');
  if (equality) {
    return {
      kind: 'equality',
      left: normalizeTerm(equality[0]),
      right: normalizeTerm(equality[1]),
    };
  }

  return { kind: 'atom', value: normalized };
}

export function parseMembershipCanonical(prop: string): { element: string; set: string } | null {
  const canonical = parseCanonicalExpr(prop);
  return isCanonicalAtom(canonical) && canonical.kind === 'membership'
    ? { element: canonical.element, set: canonical.set }
    : null;
}

export function parseNonMembershipCanonical(prop: string): { element: string; set: string } | null {
  const canonical = parseCanonicalExpr(prop);
  return isCanonicalAtom(canonical) && canonical.kind === 'nonmembership'
    ? { element: canonical.element, set: canonical.set }
    : null;
}

export function parseSubsetCanonical(prop: string): { left: string; right: string; strict: boolean } | null {
  const canonical = parseCanonicalExpr(prop);
  return isCanonicalAtom(canonical) && canonical.kind === 'subset'
    ? { left: canonical.left, right: canonical.right, strict: canonical.strict }
    : null;
}

export function parseEqualityCanonical(prop: string): { left: string; right: string } | null {
  const canonical = parseCanonicalExpr(prop);
  return isCanonicalAtom(canonical) && canonical.kind === 'equality'
    ? { left: canonical.left, right: canonical.right }
    : null;
}

export function parseTypedVariableCanonical(prop: string): { variable: string; domain: string } | null {
  const canonical = parseCanonicalExpr(prop);
  return isCanonicalAtom(canonical) && canonical.kind === 'typed_variable'
    ? { variable: canonical.variable, domain: canonical.domain }
    : null;
}

export function parseMorphismDeclarationCanonical(prop: string): MorphismDeclarationProp | null {
  const value = normalizeTerm(normalizeSurfaceSyntax(prop));
  const match = value.match(/^(.+?)\s*:\s*(.+?)\s*→\s*(.+)$/);
  if (!match) return null;
  const label = normalizeTerm(match[1]);
  const domain = normalizeTerm(match[2]);
  const codomain = normalizeTerm(match[3]);
  if (!label || !domain || !codomain) return null;
  if (label.includes(' ') && !/^id_/.test(label)) return null;
  return { label, domain, codomain };
}

export function parseMorphismExprCanonical(input: string): MorphismExpr | null {
  const value = stripOuterParens(normalizeTerm(normalizeSurfaceSyntax(input)));
  if (!value) return null;

  const compositionIndex = findTopLevelSeparator(value, '∘');
  if (compositionIndex !== -1) {
    const left = parseMorphismExprCanonical(value.slice(0, compositionIndex));
    const right = parseMorphismExprCanonical(value.slice(compositionIndex + 1));
    if (!left || !right) return null;
    return { kind: 'compose', left, right };
  }

  const functorMatch = value.match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)\((.+)\)$/);
  if (functorMatch) {
    const argument = parseMorphismExprCanonical(functorMatch[2]);
    if (!argument) return null;
    return { kind: 'functor_map', functor: normalizeTerm(functorMatch[1]), argument };
  }

  const identityMatch = value.match(/^id_(?:\{(.+)\}|(.+))$/);
  if (identityMatch) {
    return { kind: 'identity', object: normalizeTerm(identityMatch[1] ?? identityMatch[2]) };
  }

  return { kind: 'name', label: value };
}

export function formatMorphismExpr(expr: MorphismExpr): string {
  switch (expr.kind) {
    case 'name':
      return expr.label;
    case 'identity':
      return `id_${expr.object}`;
    case 'compose':
      return `${formatMorphismExpr(expr.left)} ∘ ${formatMorphismExpr(expr.right)}`;
    case 'functor_map':
      return `${expr.functor}(${formatMorphismExpr(expr.argument)})`;
  }
}

export function parseCategoricalEqualityCanonical(prop: string): { left: MorphismExpr; right: MorphismExpr } | null {
  const equality = splitTopLevelAtom(normalizeTerm(normalizeSurfaceSyntax(prop)), '=');
  if (!equality) return null;
  const left = parseMorphismExprCanonical(equality[0]);
  const right = parseMorphismExprCanonical(equality[1]);
  if (!left || !right) return null;
  return { left, right };
}

export function parseCategoryPredicateCanonical(prop: string): CategoryPredicateProp | null {
  const value = normalizeTerm(normalizeSurfaceSyntax(prop));
  const match = value.match(/^(Category|Object|Morphism|Iso|Product|ProductMediator|Coproduct|Pullback|Pushout|Functor)\((.*)\)$/);
  if (!match) return null;
  const name = match[1] as CategoryPredicateProp['name'];
  const args = splitTopLevelArgs(match[2]);
  return { name, args };
}

export interface MeasurePredicateProp {
  name: 'SigmaAlgebra' | 'Measure' | 'ProbabilityMeasure' | 'Measurable';
  args: string[];
}

export function parseMeasurePredicateCanonical(claim: string): MeasurePredicateProp | null {
  const value = normalizeTerm(normalizeSurfaceSyntax(claim));
  const match = value.match(/^(SigmaAlgebra|Measure|ProbabilityMeasure|Measurable)\s*\((.*)\)$/);
  if (!match) return null;
  const name = match[1] as MeasurePredicateProp['name'];
  const args = splitTopLevelArgs(match[2]);
  return { name, args };
}

export function parseImplicationCanonical(prop: string): [string, string] | null {
  return splitTopLevelProp(prop, '→');
}

export function parseConjunctionCanonical(prop: string): [string, string] | null {
  return splitTopLevelProp(prop, '∧');
}

export function parseDisjunctionCanonical(prop: string): [string, string] | null {
  return splitTopLevelProp(prop, '∨');
}

export function parseIffCanonical(prop: string): [string, string] | null {
  return splitTopLevelProp(prop, '↔');
}

export function parseBinarySetCanonical(prop: string, operator: '∪' | '∩'): [string, string] | null {
  return splitTopLevelProp(prop, operator);
}

export function parseSetBuilderCanonical(term: string): CanonicalSetBuilderTerm | null {
  const value = stripOuterParens(normalizeTerm(term));
  if (!(value.startsWith('{') && value.endsWith('}'))) return null;
  const inner = value.slice(1, -1).trim();
  const barIndex = findTopLevelSeparator(inner, '|');
  if (barIndex === -1) return null;
  const elementTemplate = normalizeTerm(inner.slice(0, barIndex));
  const binder = inner.slice(barIndex + 1).trim();
  const membership = splitTopLevelAtom(binder, '∈');
  if (!membership) return null;
  const variable = normalizeTerm(membership[0]);
  if (!/^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(variable)) return null;
  const domain = stripOuterParens(normalizeTerm(membership[1]));
  if (!elementTemplate || !domain) return null;
  return { elementTemplate, variable, domain };
}

export function parseIndexedUnionCanonical(term: string): CanonicalSetBuilderTerm | null {
  const value = stripOuterParens(normalizeTerm(term));
  if (!value.startsWith('∪')) return null;
  return parseSetBuilderCanonical(value.slice(1).trim());
}

export function parseSetBuilderOrUnionCanonical(term: string): CanonicalSetBuilderTerm | null {
  return parseIndexedUnionCanonical(term) ?? parseSetBuilderCanonical(term);
}

export function isSetBuilderLikeCanonical(term: string): boolean {
  return parseSetBuilderOrUnionCanonical(term) !== null;
}

export function parseBoundedQuantifierCanonical(prop: string, kind: QuantifierKind): BoundedQuantifierProp | null {
  const quantifier = parseQuantifiedExpr(prop, kind, 'bounded');
  if (!quantifier || !quantifier.body) return null;
  return {
    kind,
    variable: quantifier.variable,
    set: quantifier.domain,
    body: exprToProp(quantifier.body),
  };
}

export function parseTypedQuantifierCanonical(prop: string, kind: QuantifierKind): TypedQuantifierProp | null {
  const quantifier = parseQuantifiedExpr(prop, kind, 'typed');
  if (!quantifier || !quantifier.body) return null;
  return {
    kind,
    variable: quantifier.variable,
    domain: quantifier.domain,
    body: exprToProp(quantifier.body),
  };
}

export function parseStandaloneBoundedQuantifierCanonical(prop: string, kind: QuantifierKind): StandaloneBoundedQuantifierProp | null {
  const quantifier = parseQuantifiedExpr(prop, kind, 'bounded');
  if (!quantifier || quantifier.body) return null;
  return {
    kind,
    variable: quantifier.variable,
    set: quantifier.domain,
  };
}

export function parseStandaloneTypedQuantifierCanonical(prop: string, kind: QuantifierKind): StandaloneTypedQuantifierProp | null {
  const quantifier = parseQuantifiedExpr(prop, kind, 'typed');
  if (!quantifier || quantifier.body) return null;
  return {
    kind,
    variable: quantifier.variable,
    domain: quantifier.domain,
  };
}

function canonicalDisplay(expr: ExprNode | CanonicalProp): string {
  if (isCanonicalAtom(expr)) return canonicalAtomDisplay(expr);
  return exprToProp(expr);
}

function parseQuantifiedExpr(
  prop: string,
  kind: QuantifierKind,
  binderStyle: 'bounded' | 'typed',
): QuantifiedNode | null {
  let parsed: ExprNode;
  try {
    parsed = parseExpr(prop.trim());
  } catch {
    return null;
  }
  if (parsed.type !== 'Quantified') return null;
  if (parsed.quantifier !== kind || parsed.binderStyle !== binderStyle) return null;
  return parsed;
}

function propKey(expr: ExprNode | CanonicalProp): string {
  if (isCanonicalAtom(expr)) return canonicalAtomKey(expr);
  switch (expr.type) {
    case 'And':
      return `and(${propKey(canonicalizeExpr(expr.left))},${propKey(canonicalizeExpr(expr.right))})`;
    case 'Or':
      return `or(${propKey(canonicalizeExpr(expr.left))},${propKey(canonicalizeExpr(expr.right))})`;
    case 'Implies':
      return `implies(${propKey(canonicalizeExpr(expr.left))},${propKey(canonicalizeExpr(expr.right))})`;
    case 'Iff':
      return `iff(${propKey(canonicalizeExpr(expr.left))},${propKey(canonicalizeExpr(expr.right))})`;
    case 'Not':
      return `not(${propKey(canonicalizeExpr(expr.operand))})`;
    case 'Quantified': {
      const binder = expr.binderStyle === 'bounded'
        ? `${normalizeTerm(expr.variable)}∈${normalizeTerm(expr.domain)}`
        : `${normalizeTerm(expr.variable)}:${normalizeTerm(expr.domain)}`;
      const body = expr.body ? propKey(canonicalizeExpr(expr.body)) : '';
      return `${expr.quantifier}(${expr.binderStyle},${binder},${body})`;
    }
    case 'Fold':
      return `fold(${normalizeTerm(expr.sequence)},${normalizeTerm(expr.init)},${normalizeTerm(expr.fn)})`;
    case 'Atom':
      return canonicalAtomKey(canonicalizeAtom(expr.condition));
  }
  return '';
}

function canonicalAtomDisplay(atom: CanonicalProp): string {
  switch (atom.kind) {
    case 'membership':
      return `${atom.element} ∈ ${atom.set}`;
    case 'nonmembership':
      return `${atom.element} ∉ ${atom.set}`;
    case 'subset':
      return `${atom.left} ${atom.strict ? '⊆' : '⊂'} ${atom.right}`;
    case 'equality':
      return `${atom.left} = ${atom.right}`;
    case 'typed_variable':
      return `${atom.variable}: ${atom.domain}`;
    case 'atom':
      return atom.value;
  }
  return '';
}

function canonicalAtomKey(atom: CanonicalProp): string {
  switch (atom.kind) {
    case 'membership':
      return `membership(${normalizeTerm(atom.element)},${normalizeTerm(atom.set)})`;
    case 'nonmembership':
      return `nonmembership(${normalizeTerm(atom.element)},${normalizeTerm(atom.set)})`;
    case 'subset':
      return `subset(${atom.strict ? 'strict' : 'weak'},${normalizeTerm(atom.left)},${normalizeTerm(atom.right)})`;
    case 'equality':
      return `equality(${normalizeTerm(atom.left)},${normalizeTerm(atom.right)})`;
    case 'typed_variable':
      return `typed(${normalizeTerm(atom.variable)},${normalizeTerm(atom.domain)})`;
    case 'atom':
      return `atom(${normalizeTerm(atom.value)})`;
  }
  return '';
}

function isCanonicalAtom(expr: ExprNode | CanonicalProp): expr is CanonicalProp {
  return typeof (expr as CanonicalProp).kind === 'string';
}

function normalizeTerm(value: string): string {
  return value.trim().replace(/\s+/g, ' ');
}

function splitTopLevelAtom(value: string, operator: string): [string, string] | null {
  let parenDepth = 0;
  let braceDepth = 0;
  let bracketDepth = 0;

  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === '(') parenDepth++;
    else if (ch === ')') parenDepth = Math.max(0, parenDepth - 1);
    else if (ch === '{') braceDepth++;
    else if (ch === '}') braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === '[') bracketDepth++;
    else if (ch === ']') bracketDepth = Math.max(0, bracketDepth - 1);

    if (parenDepth === 0 && braceDepth === 0 && bracketDepth === 0 && value.slice(i, i + operator.length) === operator) {
      const left = normalizeTerm(value.slice(0, i));
      const right = normalizeTerm(value.slice(i + operator.length));
      if (left && right) return [left, right];
    }
  }

  return null;
}

function splitTopLevelProp(value: string, operator: '→' | '∧' | '∨' | '↔' | '∪' | '∩'): [string, string] | null {
  let parenDepth = 0;
  let braceDepth = 0;
  let bracketDepth = 0;

  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === '(') parenDepth++;
    else if (ch === ')') parenDepth = Math.max(0, parenDepth - 1);
    else if (ch === '{') braceDepth++;
    else if (ch === '}') braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === '[') bracketDepth++;
    else if (ch === ']') bracketDepth = Math.max(0, bracketDepth - 1);

    if (parenDepth === 0 && braceDepth === 0 && bracketDepth === 0 && value.slice(i, i + operator.length) === operator) {
      const left = normalizeTerm(value.slice(0, i));
      const right = normalizeTerm(value.slice(i + operator.length));
      if (left && right) return [left, right];
    }
  }

  return null;
}

function findTopLevelSeparator(value: string, separator: string): number {
  let parenDepth = 0;
  let braceDepth = 0;
  let bracketDepth = 0;

  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === '(') parenDepth++;
    else if (ch === ')') parenDepth = Math.max(0, parenDepth - 1);
    else if (ch === '{') braceDepth++;
    else if (ch === '}') braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === '[') bracketDepth++;
    else if (ch === ']') bracketDepth = Math.max(0, bracketDepth - 1);

    if (parenDepth === 0 && braceDepth === 0 && bracketDepth === 0 && value.slice(i, i + separator.length) === separator) {
      return i;
    }
  }

  return -1;
}

function splitTopLevelArgs(value: string): string[] {
  const args: string[] = [];
  let start = 0;
  let parenDepth = 0;
  let braceDepth = 0;
  let bracketDepth = 0;

  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === '(') parenDepth++;
    else if (ch === ')') parenDepth = Math.max(0, parenDepth - 1);
    else if (ch === '{') braceDepth++;
    else if (ch === '}') braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === '[') bracketDepth++;
    else if (ch === ']') bracketDepth = Math.max(0, bracketDepth - 1);

    if (parenDepth === 0 && braceDepth === 0 && bracketDepth === 0 && ch === ',') {
      args.push(normalizeTerm(value.slice(start, i)));
      start = i + 1;
    }
  }

  const final = normalizeTerm(value.slice(start));
  if (final) args.push(final);
  return args;
}

function stripOuterParens(value: string): string {
  let current = value.trim();
  while (hasWrappingParens(current)) {
    current = current.slice(1, -1).trim();
  }
  return current;
}

function hasWrappingParens(value: string): boolean {
  if (!(value.startsWith('(') && value.endsWith(')'))) return false;
  let depth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === '(') depth++;
    else if (ch === ')') {
      depth--;
      if (depth === 0 && i < value.length - 1) return false;
    }
  }
  return depth === 0;
}

export function splitImplication(expr: ExprNode): [string, string] | null {
  if (expr.type !== 'Implies') return null;
  return [exprToProp(expr.left), exprToProp(expr.right)];
}

export function splitConjunction(expr: ExprNode): [string, string] | null {
  if (expr.type !== 'And') return null;
  return [exprToProp(expr.left), exprToProp(expr.right)];
}

export function splitIff(expr: ExprNode): [string, string] | null {
  if (expr.type !== 'Iff') return null;
  return [exprToProp(expr.left), exprToProp(expr.right)];
}

export function splitDisjunction(expr: ExprNode): [string, string] | null {
  if (expr.type !== 'Or') return null;
  return [exprToProp(expr.left), exprToProp(expr.right)];
}
