import { ExprNode } from '../parser/ast';

export function exprToProp(expr: ExprNode): string {
  switch (expr.type) {
    case 'Atom':    return expr.condition;
    case 'SetBuilder':
      return `{${expr.element} | ${expr.variable} ∈ ${expr.domain}}`;
    case 'IndexedUnion':
      return `∪${exprToProp(expr.builder)}`;
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
  return s.trim().toLowerCase().replace(/\s+/g, ' ');
}

export function sameProp(a: string, b: string): boolean {
  return normalizeProp(a) === normalizeProp(b);
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
