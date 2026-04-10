"use strict";
// src/kernel/unify.ts
// First-order Robinson unification for Terms.
Object.defineProperty(exports, "__esModule", { value: true });
exports.unify = unify;
const term_1 = require("./term");
/**
 * Attempts to unify term `a` with term `b` where names in `metavars` are
 * treated as logic variables that can be bound to any term.
 *
 * Returns the most general unifier (substitution) on success, or null on failure.
 */
function unify(a, b, metavars) {
    const subst = new Map();
    if (!unifyInto(a, b, metavars, subst))
        return null;
    return subst;
}
function unifyInto(a, b, metavars, subst) {
    a = (0, term_1.applySubst)(a, subst);
    b = (0, term_1.applySubst)(b, subst);
    // metavar on the left
    if (a.kind === 'var' && metavars.has(a.name)) {
        if (a.kind === b.kind && a.name === b.name)
            return true;
        if (occursIn(a.name, b))
            return false;
        subst.set(a.name, b);
        return true;
    }
    // metavar on the right
    if (b.kind === 'var' && metavars.has(b.name)) {
        if (occursIn(b.name, a))
            return false;
        subst.set(b.name, a);
        return true;
    }
    if (a.kind !== b.kind)
        return false;
    switch (a.kind) {
        case 'var': return a.name === b.name;
        case 'atom': return a.value === b.value;
        case 'app': {
            const bb = b;
            return a.fn === bb.fn && a.args.length === bb.args.length
                && a.args.every((arg, i) => unifyInto(arg, bb.args[i], metavars, subst));
        }
        case 'and':
        case 'or':
        case 'iff':
        case 'implies': {
            const bb = b;
            return unifyInto(a.left, bb.left, metavars, subst)
                && unifyInto(a.right, bb.right, metavars, subst);
        }
        case 'not': {
            return unifyInto(a.body, b.body, metavars, subst);
        }
        case 'forall':
        case 'exists': {
            const aa = a;
            const bb = b;
            if (aa.domain !== bb.domain)
                return false;
            return unifyInto(aa.body, bb.body, metavars, subst);
        }
        case 'mem': {
            const aa = a;
            const bb = b;
            return unifyInto(aa.element, bb.element, metavars, subst)
                && unifyInto(aa.set, bb.set, metavars, subst);
        }
        case 'eq': {
            const aa = a;
            const bb = b;
            // try both orientations (equality is symmetric)
            const saved = new Map(subst);
            if (unifyInto(aa.left, bb.left, metavars, subst) && unifyInto(aa.right, bb.right, metavars, subst))
                return true;
            // restore and try flipped
            subst.clear();
            for (const [k, v] of saved)
                subst.set(k, v);
            return unifyInto(aa.left, bb.right, metavars, subst) && unifyInto(aa.right, bb.left, metavars, subst);
        }
        case 'sub': {
            const aa = a;
            const bb = b;
            return unifyInto(aa.left, bb.left, metavars, subst)
                && unifyInto(aa.right, bb.right, metavars, subst);
        }
        default: return false;
    }
}
function occursIn(name, term) {
    switch (term.kind) {
        case 'var': return term.name === name;
        case 'atom': return false;
        case 'app': return term.args.some(a => occursIn(name, a));
        case 'and':
        case 'or':
        case 'iff':
        case 'implies':
            return occursIn(name, term.left)
                || occursIn(name, term.right);
        case 'not': return occursIn(name, term.body);
        case 'forall':
        case 'exists': {
            const t = term;
            return t.variable !== name && occursIn(name, t.body);
        }
        case 'mem': return occursIn(name, term.element)
            || occursIn(name, term.set);
        case 'eq':
        case 'sub': return occursIn(name, term.left)
            || occursIn(name, term.right);
        default: return false;
    }
}
