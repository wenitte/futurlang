import { ExprNode } from '../parser/ast';

export function exprToProp(expr: ExprNode): string {
  switch (expr.type) {
    case 'Atom':    return expr.condition;
    case 'And':     return `${exprToProp(expr.left)} ∧ ${exprToProp(expr.right)}`;
    case 'Or':      return `${exprToProp(expr.left)} ∨ ${exprToProp(expr.right)}`;
    case 'Implies': return `${exprToProp(expr.left)} → ${exprToProp(expr.right)}`;
    case 'Iff':     return `${exprToProp(expr.left)} ↔ ${exprToProp(expr.right)}`;
    case 'Not':     return `¬${exprToProp(expr.operand)}`;
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
