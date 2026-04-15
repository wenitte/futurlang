"use strict";
// src/kernel/term.ts
// Structural term representation for alpha-equality comparison and unification.
Object.defineProperty(exports, "__esModule", { value: true });
exports.termFromExpr = termFromExpr;
exports.termFromString = termFromString;
exports.termEqual = termEqual;
exports.applySubst = applySubst;
exports.termToString = termToString;
exports.rewriteTerm = rewriteTerm;
const propositions_1 = require("../checker/propositions");
function termFromExpr(expr) {
    switch (expr.type) {
        case 'And': return { kind: 'and', left: termFromExpr(expr.left), right: termFromExpr(expr.right) };
        case 'Or': return { kind: 'or', left: termFromExpr(expr.left), right: termFromExpr(expr.right) };
        case 'Implies': return { kind: 'implies', left: termFromExpr(expr.left), right: termFromExpr(expr.right) };
        case 'Iff': return { kind: 'iff', left: termFromExpr(expr.left), right: termFromExpr(expr.right) };
        case 'Not': return { kind: 'not', body: termFromExpr(expr.operand) };
        case 'Quantified': {
            const body = expr.body ? termFromExpr(expr.body) : { kind: 'atom', value: expr.domain };
            return expr.quantifier === 'forall'
                ? { kind: 'forall', variable: expr.variable, domain: expr.domain, body }
                : { kind: 'exists', variable: expr.variable, domain: expr.domain, body };
        }
        case 'Atom': return termFromString(expr.condition);
        default: return { kind: 'atom', value: normalizeAtom((0, propositions_1.exprToProp)(expr)) };
    }
}
function termFromString(s) {
    const normalized = normalizeAtom(s);
    // x ∈ A
    const memMatch = splitTop(normalized, '∈');
    if (memMatch)
        return { kind: 'mem', element: termAtom(memMatch[0]), set: termAtom(memMatch[1]) };
    // x ∉ A (treat as ¬(x ∈ A))
    const nonMemMatch = splitTop(normalized, '∉');
    if (nonMemMatch)
        return { kind: 'not', body: { kind: 'mem', element: termAtom(nonMemMatch[0]), set: termAtom(nonMemMatch[1]) } };
    // a = b
    const eqMatch = splitTop(normalized, '=');
    if (eqMatch)
        return { kind: 'eq', left: termAtom(eqMatch[0]), right: termAtom(eqMatch[1]) };
    // A ⊆ B or A ⊂ B
    const subMatch = splitTop(normalized, '⊆') ?? splitTop(normalized, '⊂');
    if (subMatch)
        return { kind: 'sub', left: termAtom(subMatch[0]), right: termAtom(subMatch[1]) };
    // a → b (implication)
    const implMatch = splitTop(normalized, '→');
    if (implMatch)
        return { kind: 'implies', left: termFromString(implMatch[0]), right: termFromString(implMatch[1]) };
    // a ∧ b
    const andMatch = splitTop(normalized, '∧');
    if (andMatch)
        return { kind: 'and', left: termFromString(andMatch[0]), right: termFromString(andMatch[1]) };
    // a ∨ b
    const orMatch = splitTop(normalized, '∨');
    if (orMatch)
        return { kind: 'or', left: termFromString(orMatch[0]), right: termFromString(orMatch[1]) };
    // ¬a
    if (normalized.startsWith('¬'))
        return { kind: 'not', body: termFromString(normalized.slice(1).trim()) };
    // f(x, y, ...)
    const appMatch = normalized.match(/^(\w[\w₀-₉]*)\s*\((.+)\)$/);
    if (appMatch) {
        const args = splitArgs(appMatch[2]).map(termAtom);
        return { kind: 'app', fn: appMatch[1], args };
    }
    // Arithmetic operators — split rightmost top-level occurrence for left-associativity.
    // Precedence (lowest first): +/- then *//
    const addMatch = splitTopRightArith(normalized, ['+', '-']);
    if (addMatch) {
        return { kind: 'app', fn: addMatch[1], args: [termAtom(addMatch[0]), termAtom(addMatch[2])] };
    }
    const mulMatch = splitTopRightArith(normalized, ['*', '/']);
    if (mulMatch) {
        return { kind: 'app', fn: mulMatch[1], args: [termAtom(mulMatch[0]), termAtom(mulMatch[2])] };
    }
    // simple variable/name
    if (/^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(normalized)) {
        return { kind: 'var', name: normalized };
    }
    return { kind: 'atom', value: normalized };
}
function termAtom(s) {
    const t = termFromString(s.trim());
    return t;
}
function termEqual(a, b) {
    if (a.kind !== b.kind)
        return false;
    switch (a.kind) {
        case 'var': return a.name === b.name;
        case 'atom': return a.value === b.value;
        case 'app': {
            const bb = b;
            return a.fn === bb.fn && a.args.length === bb.args.length && a.args.every((arg, i) => termEqual(arg, bb.args[i]));
        }
        case 'and':
        case 'or':
        case 'iff': {
            const bb = b;
            return termEqual(a.left, bb.left) && termEqual(a.right, bb.right);
        }
        case 'implies': {
            const bb = b;
            return termEqual(a.left, bb.left) && termEqual(a.right, bb.right);
        }
        case 'not': {
            const bb = b;
            return termEqual(a.body, bb.body);
        }
        case 'forall':
        case 'exists': {
            const bb = b;
            if (a.domain !== bb.domain)
                return false;
            // alpha-equivalence: rename bb's variable to a's in bb's body
            const renamed = alphaRename(bb.body, bb.variable, a.variable);
            return termEqual(a.body, renamed);
        }
        case 'mem': {
            const bb = b;
            return termEqual(a.element, bb.element) && termEqual(a.set, bb.set);
        }
        case 'eq': {
            const bb = b;
            // equality is symmetric
            return (termEqual(a.left, bb.left) && termEqual(a.right, bb.right))
                || (termEqual(a.left, bb.right) && termEqual(a.right, bb.left));
        }
        case 'sub': {
            const bb = b;
            return termEqual(a.left, bb.left) && termEqual(a.right, bb.right);
        }
        default: return false;
    }
}
function alphaRename(term, from, to) {
    switch (term.kind) {
        case 'var': return term.name === from ? { kind: 'var', name: to } : term;
        case 'atom': return term;
        case 'app': return { ...term, args: term.args.map(arg => alphaRename(arg, from, to)) };
        case 'and':
        case 'or':
        case 'iff':
        case 'implies':
            return { ...term, left: alphaRename(term.left, from, to), right: alphaRename(term.right, from, to) };
        case 'not': return { kind: 'not', body: alphaRename(term.body, from, to) };
        case 'forall':
        case 'exists':
            if (term.variable === from)
                return term; // shadowed
            return { ...term, body: alphaRename(term.body, from, to) };
        case 'mem': return { kind: 'mem', element: alphaRename(term.element, from, to), set: alphaRename(term.set, from, to) };
        case 'eq': return { kind: 'eq', left: alphaRename(term.left, from, to), right: alphaRename(term.right, from, to) };
        case 'sub': return { kind: 'sub', left: alphaRename(term.left, from, to), right: alphaRename(term.right, from, to) };
        default: return term;
    }
}
function applySubst(term, subst) {
    switch (term.kind) {
        case 'var': return subst.has(term.name) ? applySubst(subst.get(term.name), subst) : term;
        case 'atom': return term;
        case 'app': return { ...term, args: term.args.map(a => applySubst(a, subst)) };
        case 'and':
        case 'or':
        case 'iff':
        case 'implies':
            return { ...term, left: applySubst(term.left, subst), right: applySubst(term.right, subst) };
        case 'not': return { kind: 'not', body: applySubst(term.body, subst) };
        case 'forall':
        case 'exists': {
            const inner = new Map(subst);
            inner.delete(term.variable);
            return { ...term, body: applySubst(term.body, inner) };
        }
        case 'mem': return { kind: 'mem', element: applySubst(term.element, subst), set: applySubst(term.set, subst) };
        case 'eq': return { kind: 'eq', left: applySubst(term.left, subst), right: applySubst(term.right, subst) };
        case 'sub': return { kind: 'sub', left: applySubst(term.left, subst), right: applySubst(term.right, subst) };
        default: return term;
    }
}
function termToString(term) {
    switch (term.kind) {
        case 'var': return term.name;
        case 'atom': return term.value;
        case 'app': {
            const INFIX_OPS = new Set(['+', '-', '*', '/', '%']);
            if (INFIX_OPS.has(term.fn) && term.args.length === 2) {
                const l = termToString(term.args[0]);
                const r = termToString(term.args[1]);
                // Wrap right operand in parens when it is itself an infix op with lower precedence
                const needsParens = (s, op) => {
                    if (op === '*' || op === '/')
                        return /[+\-]/.test(s.replace(/\([^)]*\)/g, ''));
                    return false;
                };
                const rStr = needsParens(r, term.fn) ? `(${r})` : r;
                return `${l} ${term.fn} ${rStr}`;
            }
            return `${term.fn}(${term.args.map(termToString).join(', ')})`;
        }
        case 'and': return `${termToString(term.left)} ∧ ${termToString(term.right)}`;
        case 'or': return `${termToString(term.left)} ∨ ${termToString(term.right)}`;
        case 'implies': return `${termToString(term.left)} → ${termToString(term.right)}`;
        case 'iff': return `${termToString(term.left)} ↔ ${termToString(term.right)}`;
        case 'not': return `¬${termToString(term.body)}`;
        case 'forall': return `∀ ${term.variable} ∈ ${term.domain}, ${termToString(term.body)}`;
        case 'exists': return `∃ ${term.variable} ∈ ${term.domain}, ${termToString(term.body)}`;
        case 'mem': return `${termToString(term.element)} ∈ ${termToString(term.set)}`;
        case 'eq': return `${termToString(term.left)} = ${termToString(term.right)}`;
        case 'sub': return `${termToString(term.left)} ⊆ ${termToString(term.right)}`;
        default: return '';
    }
}
/**
 * Replaces every subterm of `term` that is structurally equal to `from` with `to`.
 * Uses termEqual for matching, so alpha-equivalent subterms are replaced correctly.
 */
function rewriteTerm(term, from, to) {
    if (termEqual(term, from))
        return to;
    switch (term.kind) {
        case 'var':
        case 'atom':
            return term;
        case 'app':
            return { ...term, args: term.args.map(a => rewriteTerm(a, from, to)) };
        case 'and':
        case 'or':
        case 'iff':
        case 'implies':
            return { ...term, left: rewriteTerm(term.left, from, to), right: rewriteTerm(term.right, from, to) };
        case 'not':
            return { kind: 'not', body: rewriteTerm(term.body, from, to) };
        case 'forall':
        case 'exists':
            return { ...term, body: rewriteTerm(term.body, from, to) };
        case 'mem':
            return { kind: 'mem', element: rewriteTerm(term.element, from, to), set: rewriteTerm(term.set, from, to) };
        case 'eq':
            return { kind: 'eq', left: rewriteTerm(term.left, from, to), right: rewriteTerm(term.right, from, to) };
        case 'sub':
            return { kind: 'sub', left: rewriteTerm(term.left, from, to), right: rewriteTerm(term.right, from, to) };
        default:
            return term;
    }
}
// ── Arithmetic helpers ────────────────────────────────────────────────────────
/**
 * Split `s` at the RIGHTMOST top-level occurrence of any operator in `ops`.
 * Returns [left, op, right] or null.  Rightmost gives left-associativity when
 * the caller recurses on the left side.
 */
function splitTopRightArith(s, ops) {
    let depth = 0;
    let bestIdx = -1;
    let bestOp = '';
    for (let i = 0; i < s.length; i++) {
        const ch = s[i];
        if (ch === '(' || ch === '[' || ch === '{') {
            depth++;
            continue;
        }
        if (ch === ')' || ch === ']' || ch === '}') {
            depth--;
            continue;
        }
        if (depth !== 0)
            continue;
        for (const op of ops) {
            if (s.startsWith(op, i)) {
                // Avoid confusing unary minus at the start
                if (op === '-' && i === 0)
                    continue;
                bestIdx = i;
                bestOp = op;
                break;
            }
        }
    }
    if (bestIdx < 0)
        return null;
    const left = s.slice(0, bestIdx).trim();
    const right = s.slice(bestIdx + bestOp.length).trim();
    if (!left || !right)
        return null;
    return [left, bestOp, right];
}
// ── Helpers ──────────────────────────────────────────────────────────────────
function normalizeAtom(s) {
    return s.trim()
        .replace(/\bin\b/g, '∈')
        .replace(/\s+/g, ' ');
}
function splitTop(s, sep) {
    let depth = 0;
    const idx = s.indexOf(sep);
    if (idx < 0)
        return null;
    // walk to find top-level occurrence
    for (let i = 0; i < s.length; i++) {
        const ch = s[i];
        if (ch === '(' || ch === '[' || ch === '{')
            depth++;
        else if (ch === ')' || ch === ']' || ch === '}')
            depth--;
        else if (depth === 0 && s.startsWith(sep, i)) {
            return [s.slice(0, i).trim(), s.slice(i + sep.length).trim()];
        }
    }
    return null;
}
function splitArgs(s) {
    const result = [];
    let depth = 0;
    let start = 0;
    for (let i = 0; i < s.length; i++) {
        const ch = s[i];
        if (ch === '(' || ch === '[')
            depth++;
        else if (ch === ')' || ch === ']')
            depth--;
        else if (depth === 0 && ch === ',') {
            result.push(s.slice(start, i).trim());
            start = i + 1;
        }
    }
    result.push(s.slice(start).trim());
    return result;
}
