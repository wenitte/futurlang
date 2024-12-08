"use strict";
import { LogicExpr } from './exprAST';

export function parseLogicExpression(expr: string): LogicExpr {
  const tokens = tokenizeExpr(expr);
  let index = 0;

  function peek(): string | undefined {
    return tokens[index];
  }

  function eat(t?: string): string {
    const cur = peek();
    if (!cur) throw new Error(`Unexpected end of expression`);
    if (t && cur !== t) throw new Error(`Expected '${t}', got '${cur}'`);
    index++;
    return cur;
  }

  // Start parsing
  return parseExpr();

  // Grammar sketch:
  // Expr := QuantifiedExpr | BinaryExpr | UnaryExpr | Atomic
  // QuantifiedExpr := (∀x ∈ X: Expr) | (∃x ∈ X: Expr)
  // BinaryExpr := (Expr op Expr) where op ∧, ∨, ⇒, ↔
  // UnaryExpr := ¬Expr
  // Atomic := (Expr) | Predicate | Var | InSet | EmptySet

  function parseExpr(): LogicExpr {
    const t = peek();
    if (t === '∀' || t === '∃') {
      return parseQuantifier();
    }
    if (t === '¬') {
      eat('¬');
      const expr = parseExpr();
      return { type: 'Not', expr };
    }
    if (t === '(') {
      eat('(');
      const left = parseExpr();
      const next = peek();
      if (next === '∧' || next === '∨' || next === '⇒' || next === '↔') {
        const opSym = eat();
        const right = parseExpr();
        eat(')');
        const op = symbolToOp(opSym);
        return { type: 'BinaryOp', op, left, right };
      } else {
        // Just a parenthesized single expr
        eat(')');
        return left;
      }
    }

    // Otherwise, it's atomic
    return parseAtomic();
  }

  function parseQuantifier(): LogicExpr {
    const qSym = eat(); // ∀ or ∃
    const quantifier = qSym === '∀' ? 'forall' : 'exists';
    const varName = eat(); // x
    eat('∈');
const setName = eat(); // X
// MODIFIED: Allow optional whitespace before the colon
while (peek() === ' ') eat();  // Consume spaces if any
eat(':');

    // Brute force hack: try to eat(':'). If it fails, insert ':' manually.
    try {
      eat(':');
    } catch (err) {
      // Insert ':' at the current index and try again
      tokens.splice(index, 0, ':');
      eat(':');
    }

    const body = parseExpr();
    return { type: 'Quantifier', quantifier, variable: varName, set: setName, body };
  }

  function parseAtomic(): LogicExpr {
    const t = peek();
    if (!t) throw new Error(`Unexpected end of atomic expression`);

    if (t === '∅') {
      eat('∅');
      return { type: 'EmptySet' };
    }

    const first = eat(); // consume one token
    const possibleNext = peek();

    if (possibleNext === '∈' || possibleNext === '∉') {
      const op = eat();
      const setName = eat();
      if (op === '∈') {
        return { type: 'InSet', element: first, set: setName };
      } else {
        return { type: 'NotInSet', element: first, set: setName };
      }
    }

    if (possibleNext === '⊆' || possibleNext === '⊂') {
      const op = eat();
      const right = eat();
      return { type: 'Subset', proper: op === '⊂', left: first, right };
    }

    if (possibleNext === '∪' || possibleNext === '∩') {
      const op = eat();
      const right = eat();
      const opName = op === '∪' ? 'union' : 'intersect';
      return { type: 'SetOp', op: opName, left: first, right };
    }

    // Check if it's a predicate call like P(x)
    if (possibleNext === '(') {
      eat('(');
      const args: string[] = [];
      while (peek() && peek() !== ')') {
        const arg = eat();
        if (arg.endsWith(')')) {
          args.push(arg.replace(')', ''));
          break;
        }
        if (peek() === ')') {
          args.push(arg);
          break;
        }
        if (peek() === ',') {
          eat(',');
        } else if (peek() === ')') {
          args.push(arg);
          break;
        } else {
          args.push(arg);
        }
      }
      eat(')');
      return { type: 'Predicate', name: first, args };
    }

    // If just a single token, it's a variable or a set name
    return { type: 'Var', name: first };
  }

  function symbolToOp(sym: string): 'and' | 'or' | 'implies' | 'iff' {
    switch (sym) {
      case '∧': return 'and';
      case '∨': return 'or';
      case '⇒': return 'implies';
      case '↔': return 'iff';
      default: throw new Error(`Unknown binary operator ${sym}`);
    }
  }
}

function tokenizeExpr(expr: string): string[] {
  const spaced = expr
    .replace(/([\(\)])/g, ' $1 ')
    .replace(/∀/g, ' ∀ ')
    .replace(/∃/g, ' ∃ ')
    .replace(/¬/g, ' ¬ ')
    .replace(/∧/g, ' ∧ ')
    .replace(/∨/g, ' ∨ ')
    .replace(/⇒/g, ' ⇒ ')
    .replace(/↔/g, ' ↔ ')
    .replace(/∈/g, ' ∈ ')
    .replace(/∉/g, ' ∉ ')
    .replace(/⊆/g, ' ⊆ ')
    .replace(/⊂/g, ' ⊂ ')
    .replace(/∪/g, ' ∪ ')
    .replace(/∩/g, ' ∩ ')
    .replace(/∅/g, ' ∅ ')
    // Ensure colons are spaced out as well
    .replace(/:/g, ' : ');

  return spaced.split(/\s+/).filter(t => t.length > 0);
}
