// src/kernel/unify.ts
// First-order Robinson unification for Terms.

import { Term, applySubst, termToString } from './term';

export interface UnifyResult {
  subst: Map<string, Term>;
  error?: { expected: string; actual: string };
}

/**
 * Attempts to unify term `a` with term `b` where names in `metavars` are
 * treated as logic variables that can be bound to any term.
 *
 * Returns the UnifyResult containing the unifier on success, or an error on failure.
 */
export function unify(a: Term, b: Term, metavars: Set<string>): UnifyResult {
  const subst = new Map<string, Term>();
  const errorRef: { error?: { expected: string; actual: string } } = {};
  if (!unifyInto(a, b, metavars, subst, errorRef)) {
    return { subst, error: errorRef.error || { expected: termToString(b), actual: termToString(a) } };
  }
  return { subst };
}

function unifyInto(a: Term, b: Term, metavars: Set<string>, subst: Map<string, Term>, errorRef: { error?: { expected: string; actual: string } }): boolean {
  a = applySubst(a, subst);
  b = applySubst(b, subst);

  // metavar on the left
  if (a.kind === 'var' && metavars.has(a.name)) {
    if (a.kind === b.kind && (a as { name: string }).name === (b as { name: string }).name) return true;
    if (occursIn(a.name, b)) {
      errorRef.error = { expected: `No occurs-check cycle for ${a.name}`, actual: termToString(b) };
      return false;
    }
    subst.set(a.name, b);
    return true;
  }
  // metavar on the right
  if (b.kind === 'var' && metavars.has(b.name)) {
    if (occursIn(b.name, a)) {
      errorRef.error = { expected: `No occurs-check cycle for ${b.name}`, actual: termToString(a) };
      return false;
    }
    subst.set(b.name, a);
    return true;
  }

  if (a.kind !== b.kind) {
    errorRef.error = { expected: termToString(b), actual: termToString(a) };
    return false;
  }

  switch (a.kind) {
    case 'var':  return a.name === (b as typeof a).name;
    case 'atom': return a.value === (b as typeof a).value;
    case 'app': {
      const bb = b as typeof a;
      return a.fn === bb.fn && a.args.length === bb.args.length
        && a.args.every((arg, i) => unifyInto(arg, bb.args[i], metavars, subst, errorRef));
    }
    case 'and':
    case 'or':
    case 'iff':
    case 'implies': {
      const bb = b as { kind: string; left: Term; right: Term };
      return unifyInto((a as { left: Term; right: Term }).left, bb.left, metavars, subst, errorRef)
          && unifyInto((a as { left: Term; right: Term }).right, bb.right, metavars, subst, errorRef);
    }
    case 'not': {
      return unifyInto((a as { body: Term }).body, (b as { body: Term }).body, metavars, subst, errorRef);
    }
    case 'forall':
    case 'exists': {
      const aa = a as { variable: string; domain: string; body: Term };
      const bb = b as { variable: string; domain: string; body: Term };
      if (aa.domain !== bb.domain) {
        errorRef.error = { expected: `domain ${bb.domain}`, actual: `domain ${aa.domain}` };
        return false;
      }
      return unifyInto(aa.body, bb.body, metavars, subst, errorRef);
    }
    case 'mem': {
      const aa = a as { element: Term; set: Term };
      const bb = b as { element: Term; set: Term };
      return unifyInto(aa.element, bb.element, metavars, subst, errorRef)
          && unifyInto(aa.set, bb.set, metavars, subst, errorRef);
    }
    case 'eq': {
      const aa = a as { left: Term; right: Term };
      const bb = b as { left: Term; right: Term };
      // try both orientations (equality is symmetric)
      const saved = new Map(subst);
      if (unifyInto(aa.left, bb.left, metavars, subst, errorRef) && unifyInto(aa.right, bb.right, metavars, subst, errorRef)) return true;
      // restore and try flipped
      subst.clear();
      for (const [k, v] of saved) subst.set(k, v);
      return unifyInto(aa.left, bb.right, metavars, subst, errorRef) && unifyInto(aa.right, bb.left, metavars, subst, errorRef);
    }
    case 'sub': {
      const aa = a as { left: Term; right: Term };
      const bb = b as { left: Term; right: Term };
      return unifyInto(aa.left, bb.left, metavars, subst, errorRef)
          && unifyInto(aa.right, bb.right, metavars, subst, errorRef);
    }
    default: return false;
  }
}

function occursIn(name: string, term: Term): boolean {
  switch (term.kind) {
    case 'var':  return term.name === name;
    case 'atom': return false;
    case 'app':  return term.args.some(a => occursIn(name, a));
    case 'and':
    case 'or':
    case 'iff':
    case 'implies':
      return occursIn(name, (term as { left: Term; right: Term }).left)
          || occursIn(name, (term as { left: Term; right: Term }).right);
    case 'not':  return occursIn(name, (term as { body: Term }).body);
    case 'forall':
    case 'exists': {
      const t = term as { variable: string; body: Term };
      return t.variable !== name && occursIn(name, t.body);
    }
    case 'mem':  return occursIn(name, (term as { element: Term; set: Term }).element)
                     || occursIn(name, (term as { element: Term; set: Term }).set);
    case 'eq':
    case 'sub':  return occursIn(name, (term as { left: Term; right: Term }).left)
                     || occursIn(name, (term as { left: Term; right: Term }).right);
    default: return false;
  }
}
