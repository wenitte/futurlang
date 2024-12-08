"use strict";
// src/parsing/exprParser.ts
Object.defineProperty(exports, "__esModule", { value: true });
exports.parseLogicExpression = parseLogicExpression;
function tokenizeExpr(expr) {
    const spaced = expr
        .replace(/([\(\)])/g, ' $1 ') // Add spaces around parentheses
        .replace(/(∀|∃|¬|∧|∨|⇒|↔|∈|∉|⊆|⊂|∪|∩|∅|&&|->|<->)/g, ' $1 ') // Add spaces around symbols
        .split(/\s+/).filter(t => t.length > 0); // Split and filter empty strings
    return spaced;
}
function parseLogicExpression(expr) {
    const tokens = tokenizeExpr(expr);
    let index = 0;
    function peek() {
        return tokens[index];
    }
    function eat(t) {
        const cur = peek();
        if (!cur)
            throw new Error(`Unexpected end of expression at ${index} (remaining tokens: ${tokens.slice(index).join(' ')})`);
        if (t && cur !== t)
            throw new Error(`Expected '${t}', got '${cur}' at ${index}  (remaining tokens: ${tokens.slice(index).join(' ')})`);
        index++;
        return cur;
    }
    function parseExpr() {
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
            if (next === '∧' || next === '∨' || next === '⇒' || next === '↔' || next === '&&' || next === '->' || next === '<->') {
                const opSym = eat();
                const right = parseExpr();
                eat(')');
                const op = symbolToOp(opSym);
                return { type: 'BinaryOp', op, left, right };
            }
            else {
                eat(')');
                return left;
            }
        }
        return parseAtomic();
    }
    function parseQuantifier() {
        const t = peek();
        if (!t)
            throw new Error(`Unexpected end of atomic expression`);
        if (t === '∅') {
            eat('∅');
            return { type: 'EmptySet' };
        }
        const qSym = eat();
        const quantifier = qSym === '∀' ? 'forall' : 'exists';
        const varName = eat();
        eat('∈');
        const setName = eat();
        while (peek() === ' ')
            eat(); // Consume spaces before colon
        eat(':');
        const body = parseExpr();
        return { type: 'Quantifier', quantifier, variable: varName, set: setName, body };
    }
    function parseAtomic() {
        const t = peek();
        if (!t)
            throw new Error(`Unexpected end of atomic expression`);
        if (t === '∅') {
            eat('∅');
            return { type: 'EmptySet' };
        }
        // Check for InSet / NotInSet patterns: x ∈ X or x ∉ X
        // Check for subset: X ⊆ Y or X ⊂ Y
        // Check for set operations: X ∪ Y, X ∩ Y
        // If it doesn't match these patterns, treat as predicate or variable.
        // We try a look-ahead for patterns:
        // Var?
        const first = eat(); // we consumed one token
        const possibleNext = peek();
        if (possibleNext === '∈' || possibleNext === '∉') {
            const op = eat();
            const setName = eat();
            if (op === '∈') {
                return { type: 'InSet', element: first, set: setName };
            }
            else {
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
            // P(x,y)
            eat('(');
            const args = [];
            while (peek() && peek() !== ')') {
                const arg = eat();
                if (arg.endsWith(')')) {
                    // last arg
                    args.push(arg.replace(')', ''));
                    break;
                }
                if (peek() === ')') {
                    args.push(arg);
                    break;
                }
                if (peek() === ',') {
                    eat(',');
                }
                else if (peek() === ')') {
                    args.push(arg);
                    break;
                }
                else {
                    args.push(arg);
                }
            }
            eat(')');
            return { type: 'Predicate', name: first, args };
        }
        // If just a single token, it's a variable or a set name
        return { type: 'Var', name: first };
    }
    function symbolToOp(sym) {
        switch (sym) {
            case '∧':
            case '&&':
                return 'and';
            case '∨':
                return 'or';
            case '⇒':
            case '->':
                return 'implies';
            case '↔':
            case '<->':
                return 'iff';
            default:
                throw new Error(`Unknown binary operator: ${sym}`);
        }
    }
    return parseExpr();
}
