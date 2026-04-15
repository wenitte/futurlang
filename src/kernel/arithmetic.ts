// src/kernel/arithmetic.ts
// Arithmetic expression evaluator and predicate parsers for the number theory kernel.

// ── Tokeniser ────────────────────────────────────────────────────────────────

type Token =
  | { kind: 'num'; value: number }
  | { kind: 'ident'; value: string }
  | { kind: 'op'; value: string }
  | { kind: 'lparen' }
  | { kind: 'rparen' };

function tokenize(s: string): Token[] {
  const tokens: Token[] = [];
  let i = 0;
  while (i < s.length) {
    const ch = s[i];
    if (/\s/.test(ch)) { i++; continue; }
    if (/\d/.test(ch)) {
      let num = '';
      while (i < s.length && /\d/.test(s[i])) num += s[i++];
      tokens.push({ kind: 'num', value: parseInt(num, 10) });
    } else if (/[a-zA-Z_]/.test(ch)) {
      let id = '';
      while (i < s.length && /[a-zA-Z0-9_']/.test(s[i])) id += s[i++];
      tokens.push({ kind: 'ident', value: id });
    } else if (ch === '(') { tokens.push({ kind: 'lparen' }); i++; }
    else if (ch === ')') { tokens.push({ kind: 'rparen' }); i++; }
    else if ('+-*/%^'.includes(ch)) { tokens.push({ kind: 'op', value: ch }); i++; }
    else { i++; }
  }
  return tokens;
}

// ── Recursive-descent evaluator (returns null if any variable present) ────────

interface ParseState { tokens: Token[]; pos: number; subst: Map<string, number> }

function peek(ps: ParseState): Token | undefined { return ps.tokens[ps.pos]; }
function consume(ps: ParseState): Token { return ps.tokens[ps.pos++]; }

function parseExprNum(ps: ParseState): number | null {
  return parseAddSub(ps);
}

function parseAddSub(ps: ParseState): number | null {
  let left = parseMulDiv(ps);
  while (true) {
    const t = peek(ps);
    if (!t || t.kind !== 'op' || (t.value !== '+' && t.value !== '-')) break;
    consume(ps);
    const right = parseMulDiv(ps);
    if (left === null || right === null) return null;
    left = t.value === '+' ? left + right : left - right;
  }
  return left;
}

function parseMulDiv(ps: ParseState): number | null {
  let left = parseUnary(ps);
  while (true) {
    const t = peek(ps);
    if (!t || t.kind !== 'op' || (t.value !== '*' && t.value !== '/' && t.value !== '%')) break;
    consume(ps);
    const right = parseUnary(ps);
    if (left === null || right === null) return null;
    if (t.value === '/') left = right !== 0 ? Math.floor(left / right) : null;
    else if (t.value === '%') left = right !== 0 ? left % right : null;
    else left = left * right;
    if (left === null) return null;
  }
  return left;
}

function parseUnary(ps: ParseState): number | null {
  const t = peek(ps);
  if (t && t.kind === 'op' && t.value === '-') {
    consume(ps);
    const v = parsePrimary(ps);
    return v !== null ? -v : null;
  }
  return parsePrimary(ps);
}

function parsePrimary(ps: ParseState): number | null {
  const t = peek(ps);
  if (!t) return null;
  if (t.kind === 'num') { consume(ps); return t.value; }
  if (t.kind === 'lparen') {
    consume(ps);
    const v = parseExprNum(ps);
    const close = peek(ps);
    if (close && close.kind === 'rparen') consume(ps);
    return v;
  }
  if (t.kind === 'ident') {
    const name = t.value;
    consume(ps);
    // Check for function call — skip it, we can't evaluate
    const next = peek(ps);
    if (next && next.kind === 'lparen') {
      consume(ps);
      let depth = 1;
      while (ps.pos < ps.tokens.length && depth > 0) {
        const tok = consume(ps);
        if (tok.kind === 'lparen') depth++;
        else if (tok.kind === 'rparen') depth--;
      }
      return null;
    }
    // Look up in substitution map
    const val = ps.subst.get(name);
    return val !== undefined ? val : null;
  }
  return null;
}

/** Collect all identifiers (variable names) in an expression string. */
export function collectVars(expr: string): Set<string> {
  const tokens = tokenize(expr.trim());
  const vars = new Set<string>();
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    if (t.kind === 'ident') {
      // Skip if followed by '(' (function call)
      const next = tokens[i + 1];
      if (!next || next.kind !== 'lparen') vars.add(t.value);
    }
  }
  return vars;
}

/** Evaluate expr with a variable substitution map. Returns null if any variable is unbound. */
export function evalWithSubst(expr: string, subst: Map<string, number>): number | null {
  try {
    const tokens = tokenize(expr.trim());
    const ps: ParseState = { tokens, pos: 0, subst };
    const result = parseExprNum(ps);
    if (ps.pos < ps.tokens.length) return null;
    return result;
  } catch {
    return null;
  }
}

/**
 * Evaluate a pure-integer arithmetic expression string.
 * Returns null if the expression contains any variables.
 */
export function evalArith(expr: string): number | null {
  return evalWithSubst(expr, new Map());
}

/**
 * Try to prove `lhs = rhs` by evaluating both sides as integers.
 * Returns true only when both sides evaluate to the same concrete number.
 */
export function arithEqual(lhs: string, rhs: string): boolean {
  const l = evalArith(lhs);
  const r = evalArith(rhs);
  return l !== null && r !== null && l === r;
}

/**
 * Check if `lhs = rhs` holds symbolically by spot-testing with multiple
 * random integer assignments for each free variable.
 * Uses 8 random trials; returns true only if all agree.
 *
 * Note: This is a probabilistic check (Schwartz-Zippel style).
 * It is sound for polynomials over integers with overwhelming probability.
 */
export function arithSymEqual(lhs: string, rhs: string): boolean {
  const vars = new Set([...collectVars(lhs), ...collectVars(rhs)]);
  if (vars.size === 0) return arithEqual(lhs, rhs);

  const TRIALS = 8;
  const RANGE = 97; // prime, keeps values small
  for (let t = 0; t < TRIALS; t++) {
    const subst = new Map<string, number>();
    for (const v of vars) subst.set(v, Math.floor(Math.random() * RANGE) + 1);
    const l = evalWithSubst(lhs, subst);
    const r = evalWithSubst(rhs, subst);
    if (l === null || r === null || l !== r) return false;
  }
  return true;
}

/**
 * Substitute variables in `expr` with their known expressions from `exprSubsts`,
 * then check if `lhs = rhs` holds symbolically.
 *
 * `exprSubsts` maps variable names to expression strings, e.g. { p: "2 * k" }.
 * The substituted claim is then spot-tested with random values for remaining free vars.
 */
export function arithSymEqualWithSubst(
  lhs: string,
  rhs: string,
  exprSubsts: Map<string, string>,
): boolean {
  let l = lhs;
  let r = rhs;
  for (const [varName, expr] of exprSubsts) {
    const re = new RegExp(`\\b${varName}\\b`, 'g');
    l = l.replace(re, `(${expr})`);
    r = r.replace(re, `(${expr})`);
  }
  return arithSymEqual(l, r);
}

// ── Normalisation helpers ─────────────────────────────────────────────────────

/** Strip outer whitespace and collapse internal runs. */
export function normArith(s: string): string {
  return s.trim().replace(/\s+/g, ' ');
}

/** Strip one layer of outer parentheses if present. */
function stripOuter(s: string): string {
  s = s.trim();
  if (s.startsWith('(') && s.endsWith(')')) {
    // Verify the parens match
    let depth = 0;
    for (let i = 0; i < s.length; i++) {
      if (s[i] === '(') depth++;
      else if (s[i] === ')') { depth--; if (depth === 0 && i < s.length - 1) return s; }
    }
    return s.slice(1, -1).trim();
  }
  return s;
}

// ── Predicate parsers ─────────────────────────────────────────────────────────

/** Parse `even(X)` → X, or null. */
export function parseEvenClaim(s: string): string | null {
  const m = s.trim().match(/^even\s*\(\s*([\s\S]+?)\s*\)$/i);
  return m ? normArith(m[1]) : null;
}

/** Parse `odd(X)` → X, or null. */
export function parseOddClaim(s: string): string | null {
  const m = s.trim().match(/^odd\s*\(\s*([\s\S]+?)\s*\)$/i);
  return m ? normArith(m[1]) : null;
}

/** Parse `divides(A, B)` → {a, b}, or null. */
export function parseDividesClaim(s: string): { a: string; b: string } | null {
  const m = s.trim().match(/^divides\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
  return m ? { a: normArith(m[1]), b: normArith(m[2]) } : null;
}

// ── Expression-structure helpers ──────────────────────────────────────────────

/**
 * If expr is literally `2 * K` or `K * 2` (at the top level), return K.
 * Otherwise null.
 */
export function extractDoubleOperand(expr: string): string | null {
  const s = normArith(stripOuter(expr));
  // 2 * K
  const m1 = s.match(/^2\s*\*\s*([\s\S]+)$/);
  if (m1) return normArith(m1[1]);
  // K * 2
  const m2 = s.match(/^([\s\S]+?)\s*\*\s*2$/);
  if (m2) return normArith(m2[1]);
  return null;
}

/**
 * If expr is `2 * K + 1` or `1 + 2 * K` at the top level, return K.
 */
export function extractSuccDoubleOperand(expr: string): string | null {
  const s = normArith(stripOuter(expr));
  // 2 * K + 1
  const m1 = s.match(/^2\s*\*\s*([\s\S]+?)\s*\+\s*1$/);
  if (m1) return normArith(m1[1]);
  // 1 + 2 * K
  const m2 = s.match(/^1\s*\+\s*2\s*\*\s*([\s\S]+)$/);
  if (m2) return normArith(m2[1]);
  return null;
}

/**
 * Split `A * B` at the top-level `*`.
 * Returns [A, B] or null.
 */
export function splitTopMul(s: string): [string, string] | null {
  s = normArith(s);
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth--;
    else if (depth === 0 && ch === '*') {
      return [normArith(s.slice(0, i)), normArith(s.slice(i + 1))];
    }
  }
  return null;
}

/**
 * Check whether an expression literally evaluates to an even integer.
 */
export function isConcreteEven(expr: string): boolean {
  const v = evalArith(expr);
  return v !== null && v % 2 === 0;
}

/**
 * Check whether an expression literally evaluates to an odd integer.
 */
export function isConcreteOdd(expr: string): boolean {
  const v = evalArith(expr);
  return v !== null && v % 2 !== 0;
}
