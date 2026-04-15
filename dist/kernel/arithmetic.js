"use strict";
// src/kernel/arithmetic.ts
// Arithmetic expression evaluator and predicate parsers for the number theory kernel.
Object.defineProperty(exports, "__esModule", { value: true });
exports.collectVars = collectVars;
exports.evalWithSubst = evalWithSubst;
exports.evalArith = evalArith;
exports.arithEqual = arithEqual;
exports.arithSymEqual = arithSymEqual;
exports.arithSymEqualWithSubst = arithSymEqualWithSubst;
exports.normArith = normArith;
exports.stripOuter = stripOuter;
exports.parseEvenClaim = parseEvenClaim;
exports.parseOddClaim = parseOddClaim;
exports.parseDividesClaim = parseDividesClaim;
exports.extractDoubleOperand = extractDoubleOperand;
exports.extractSuccDoubleOperand = extractSuccDoubleOperand;
exports.splitTopMul = splitTopMul;
exports.isConcreteEven = isConcreteEven;
exports.isConcreteOdd = isConcreteOdd;
exports.parseAbsExpr = parseAbsExpr;
exports.parseSignExpr = parseSignExpr;
exports.parseAbsEquality = parseAbsEquality;
exports.parseSignEquality = parseSignEquality;
exports.parseOrder = parseOrder;
exports.evalOrder = evalOrder;
exports.parseCongruence = parseCongruence;
exports.parseModOp = parseModOp;
exports.evalMod = evalMod;
exports.areCongruent = areCongruent;
exports.isPrime = isPrime;
exports.parsePrimePred = parsePrimePred;
exports.parseTotientExpr = parseTotientExpr;
exports.parseTotientEquality = parseTotientEquality;
exports.computeTotient = computeTotient;
exports.parsePower = parsePower;
function tokenize(s) {
    const tokens = [];
    let i = 0;
    while (i < s.length) {
        const ch = s[i];
        if (/\s/.test(ch)) {
            i++;
            continue;
        }
        if (/\d/.test(ch)) {
            let num = '';
            while (i < s.length && /\d/.test(s[i]))
                num += s[i++];
            tokens.push({ kind: 'num', value: parseInt(num, 10) });
        }
        else if (/[a-zA-Z_]/.test(ch)) {
            let id = '';
            while (i < s.length && /[a-zA-Z0-9_']/.test(s[i]))
                id += s[i++];
            tokens.push({ kind: 'ident', value: id });
        }
        else if (ch === '(') {
            tokens.push({ kind: 'lparen' });
            i++;
        }
        else if (ch === ')') {
            tokens.push({ kind: 'rparen' });
            i++;
        }
        else if ('+-*/%^'.includes(ch)) {
            tokens.push({ kind: 'op', value: ch });
            i++;
        }
        else {
            i++;
        }
    }
    return tokens;
}
function peek(ps) { return ps.tokens[ps.pos]; }
function consume(ps) { return ps.tokens[ps.pos++]; }
function parseExprNum(ps) {
    return parseAddSub(ps);
}
function parseAddSub(ps) {
    let left = parseMulDiv(ps);
    while (true) {
        const t = peek(ps);
        if (!t || t.kind !== 'op' || (t.value !== '+' && t.value !== '-'))
            break;
        consume(ps);
        const right = parseMulDiv(ps);
        if (left === null || right === null)
            return null;
        left = t.value === '+' ? left + right : left - right;
    }
    return left;
}
function parseMulDiv(ps) {
    let left = parseUnary(ps);
    while (true) {
        const t = peek(ps);
        if (!t || t.kind !== 'op' || (t.value !== '*' && t.value !== '/' && t.value !== '%'))
            break;
        consume(ps);
        const right = parseUnary(ps);
        if (left === null || right === null)
            return null;
        if (t.value === '/')
            left = right !== 0 ? Math.floor(left / right) : null;
        else if (t.value === '%')
            left = right !== 0 ? left % right : null;
        else
            left = left * right;
        if (left === null)
            return null;
    }
    return left;
}
function parseUnary(ps) {
    const t = peek(ps);
    if (t && t.kind === 'op' && t.value === '-') {
        consume(ps);
        const v = parsePrimary(ps);
        return v !== null ? -v : null;
    }
    return parsePrimary(ps);
}
function parsePrimary(ps) {
    const t = peek(ps);
    if (!t)
        return null;
    if (t.kind === 'num') {
        consume(ps);
        return t.value;
    }
    if (t.kind === 'lparen') {
        consume(ps);
        const v = parseExprNum(ps);
        const close = peek(ps);
        if (close && close.kind === 'rparen')
            consume(ps);
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
                if (tok.kind === 'lparen')
                    depth++;
                else if (tok.kind === 'rparen')
                    depth--;
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
function collectVars(expr) {
    const tokens = tokenize(expr.trim());
    const vars = new Set();
    for (let i = 0; i < tokens.length; i++) {
        const t = tokens[i];
        if (t.kind === 'ident') {
            // Skip if followed by '(' (function call)
            const next = tokens[i + 1];
            if (!next || next.kind !== 'lparen')
                vars.add(t.value);
        }
    }
    return vars;
}
/** Evaluate expr with a variable substitution map. Returns null if any variable is unbound. */
function evalWithSubst(expr, subst) {
    try {
        const tokens = tokenize(expr.trim());
        const ps = { tokens, pos: 0, subst };
        const result = parseExprNum(ps);
        if (ps.pos < ps.tokens.length)
            return null;
        return result;
    }
    catch {
        return null;
    }
}
/**
 * Evaluate a pure-integer arithmetic expression string.
 * Returns null if the expression contains any variables.
 */
function evalArith(expr) {
    return evalWithSubst(expr, new Map());
}
/**
 * Try to prove `lhs = rhs` by evaluating both sides as integers.
 * Returns true only when both sides evaluate to the same concrete number.
 */
function arithEqual(lhs, rhs) {
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
function arithSymEqual(lhs, rhs) {
    const vars = new Set([...collectVars(lhs), ...collectVars(rhs)]);
    if (vars.size === 0)
        return arithEqual(lhs, rhs);
    const TRIALS = 8;
    const RANGE = 97; // prime, keeps values small
    for (let t = 0; t < TRIALS; t++) {
        const subst = new Map();
        for (const v of vars)
            subst.set(v, Math.floor(Math.random() * RANGE) + 1);
        const l = evalWithSubst(lhs, subst);
        const r = evalWithSubst(rhs, subst);
        if (l === null || r === null || l !== r)
            return false;
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
function arithSymEqualWithSubst(lhs, rhs, exprSubsts) {
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
function normArith(s) {
    return s.trim().replace(/\s+/g, ' ');
}
/** Strip one layer of outer parentheses if present. */
function stripOuter(s) {
    s = s.trim();
    if (s.startsWith('(') && s.endsWith(')')) {
        // Verify the parens match
        let depth = 0;
        for (let i = 0; i < s.length; i++) {
            if (s[i] === '(')
                depth++;
            else if (s[i] === ')') {
                depth--;
                if (depth === 0 && i < s.length - 1)
                    return s;
            }
        }
        return s.slice(1, -1).trim();
    }
    return s;
}
// ── Predicate parsers ─────────────────────────────────────────────────────────
/** Parse `even(X)` → X, or null. */
function parseEvenClaim(s) {
    const m = s.trim().match(/^even\s*\(\s*([\s\S]+?)\s*\)$/i);
    return m ? normArith(m[1]) : null;
}
/** Parse `odd(X)` → X, or null. */
function parseOddClaim(s) {
    const m = s.trim().match(/^odd\s*\(\s*([\s\S]+?)\s*\)$/i);
    return m ? normArith(m[1]) : null;
}
/** Parse `divides(A, B)` → {a, b}, or null. */
function parseDividesClaim(s) {
    const m = s.trim().match(/^divides\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
    return m ? { a: normArith(m[1]), b: normArith(m[2]) } : null;
}
// ── Expression-structure helpers ──────────────────────────────────────────────
/**
 * If expr is literally `2 * K` or `K * 2` (at the top level), return K.
 * Otherwise null.
 */
function extractDoubleOperand(expr) {
    const s = normArith(stripOuter(expr));
    // 2 * K
    const m1 = s.match(/^2\s*\*\s*([\s\S]+)$/);
    if (m1)
        return normArith(m1[1]);
    // K * 2
    const m2 = s.match(/^([\s\S]+?)\s*\*\s*2$/);
    if (m2)
        return normArith(m2[1]);
    return null;
}
/**
 * If expr is `2 * K + 1` or `1 + 2 * K` at the top level, return K.
 */
function extractSuccDoubleOperand(expr) {
    const s = normArith(stripOuter(expr));
    // 2 * K + 1
    const m1 = s.match(/^2\s*\*\s*([\s\S]+?)\s*\+\s*1$/);
    if (m1)
        return normArith(m1[1]);
    // 1 + 2 * K
    const m2 = s.match(/^1\s*\+\s*2\s*\*\s*([\s\S]+)$/);
    if (m2)
        return normArith(m2[1]);
    return null;
}
/**
 * Split `A * B` at the top-level `*`.
 * Returns [A, B] or null.
 */
function splitTopMul(s) {
    s = normArith(s);
    let depth = 0;
    for (let i = 0; i < s.length; i++) {
        const ch = s[i];
        if (ch === '(')
            depth++;
        else if (ch === ')')
            depth--;
        else if (depth === 0 && ch === '*') {
            return [normArith(s.slice(0, i)), normArith(s.slice(i + 1))];
        }
    }
    return null;
}
/**
 * Check whether an expression literally evaluates to an even integer.
 */
function isConcreteEven(expr) {
    const v = evalArith(expr);
    return v !== null && v % 2 === 0;
}
/**
 * Check whether an expression literally evaluates to an odd integer.
 */
function isConcreteOdd(expr) {
    const v = evalArith(expr);
    return v !== null && v % 2 !== 0;
}
// ── Integer operations ────────────────────────────────────────────────────────
/** Parse `abs(X)` → X, or null. */
function parseAbsExpr(s) {
    const m = s.trim().match(/^abs\s*\(\s*([\s\S]+?)\s*\)$/i);
    return m ? normArith(m[1]) : null;
}
/** Parse `sign(X)` → X, or null. */
function parseSignExpr(s) {
    const m = s.trim().match(/^sign\s*\(\s*([\s\S]+?)\s*\)$/i);
    return m ? normArith(m[1]) : null;
}
/** Parse `abs(X) = K` or `K = abs(X)` → {arg, value}, or null. */
function parseAbsEquality(s) {
    const m1 = s.trim().match(/^abs\s*\(\s*([\s\S]+?)\s*\)\s*=\s*([\s\S]+)$/i);
    if (m1)
        return { arg: normArith(m1[1]), value: normArith(m1[2]) };
    const m2 = s.trim().match(/^([\s\S]+?)\s*=\s*abs\s*\(\s*([\s\S]+?)\s*\)$/i);
    if (m2)
        return { arg: normArith(m2[2]), value: normArith(m2[1]) };
    return null;
}
/** Parse `sign(X) = K` or `K = sign(X)` → {arg, value}, or null. */
function parseSignEquality(s) {
    const m1 = s.trim().match(/^sign\s*\(\s*([\s\S]+?)\s*\)\s*=\s*([\s\S]+)$/i);
    if (m1)
        return { arg: normArith(m1[1]), value: normArith(m1[2]) };
    const m2 = s.trim().match(/^([\s\S]+?)\s*=\s*sign\s*\(\s*([\s\S]+?)\s*\)$/i);
    if (m2)
        return { arg: normArith(m2[2]), value: normArith(m2[1]) };
    return null;
}
/** Parse `A OP B` for ordering operators → {left, op, right}, or null. */
function parseOrder(s) {
    const ops = ['≤', '≥', '<=', '>=', '<', '>'];
    for (const op of ops) {
        const idx = s.indexOf(op);
        if (idx < 0)
            continue;
        // Make sure we're not inside parens (simple check)
        let depth = 0;
        let found = -1;
        for (let i = 0; i < s.length; i++) {
            if (s[i] === '(' || s[i] === '[')
                depth++;
            else if (s[i] === ')' || s[i] === ']')
                depth--;
            else if (depth === 0 && s.startsWith(op, i)) {
                found = i;
                break;
            }
        }
        if (found < 0)
            continue;
        const left = normArith(s.slice(0, found));
        const right = normArith(s.slice(found + op.length));
        if (left && right)
            return { left, op, right };
    }
    return null;
}
/** Evaluate an ordering claim concretely. Returns true/false/null. */
function evalOrder(left, op, right) {
    const l = evalArith(left);
    const r = evalArith(right);
    if (l === null || r === null)
        return null;
    switch (op) {
        case '<': return l < r;
        case '>': return l > r;
        case '≤':
        case '<=': return l <= r;
        case '≥':
        case '>=': return l >= r;
    }
}
// ── Modular arithmetic ────────────────────────────────────────────────────────
/**
 * Parse `a ≡ b (mod n)` → {a, b, n}, or null.
 * Also accepts `a = b (mod n)` as sugar.
 */
function parseCongruence(s) {
    const m = s.trim().match(/^(.+?)\s*[≡=]\s*(.+?)\s*\(\s*mod\s+(.+?)\s*\)$/i);
    return m ? { a: normArith(m[1]), b: normArith(m[2]), n: normArith(m[3]) } : null;
}
/**
 * Parse `a mod n` → {a, n}, or null.
 */
function parseModOp(s) {
    // Split on top-level 'mod' keyword
    const norm = s.trim();
    const m = norm.match(/^(.+?)\s+mod\s+(.+)$/i);
    return m ? { a: normArith(m[1]), n: normArith(m[2]) } : null;
}
/** Evaluate `a mod n` for concrete integers. */
function evalMod(a, n) {
    const av = evalArith(a);
    const nv = evalArith(n);
    if (av === null || nv === null || nv === 0)
        return null;
    return ((av % nv) + nv) % nv;
}
/** Check if two concrete expressions are congruent mod n. */
function areCongruent(a, b, n) {
    const av = evalArith(a);
    const bv = evalArith(b);
    const nv = evalArith(n);
    if (av === null || bv === null || nv === null || nv === 0)
        return false;
    return ((av - bv) % nv + nv) % nv === 0;
}
// ── Primality ─────────────────────────────────────────────────────────────────
/** Miller-Rabin deterministic check for n < 3,215,031,751. */
function isPrime(n) {
    if (n < 2)
        return false;
    if (n === 2 || n === 3)
        return true;
    if (n % 2 === 0 || n % 3 === 0)
        return false;
    for (let i = 5; i * i <= n; i += 6) {
        if (n % i === 0 || n % (i + 2) === 0)
            return false;
    }
    return true;
}
/**
 * Parse `p ∈ Prime` or `Prime(p)` → p, or null.
 */
function parsePrimePred(s) {
    const m1 = s.trim().match(/^(.+?)\s*∈\s*Prime$/i);
    if (m1)
        return normArith(m1[1]);
    const m2 = s.trim().match(/^Prime\s*\(\s*(.+?)\s*\)$/i);
    if (m2)
        return normArith(m2[1]);
    return null;
}
// ── Euler's totient ───────────────────────────────────────────────────────────
/**
 * Parse `φ(n)` or `totient(n)` → n, or null.
 */
function parseTotientExpr(s) {
    const m1 = s.trim().match(/^[φΦ]\s*\(\s*(.+?)\s*\)$/);
    if (m1)
        return normArith(m1[1]);
    const m2 = s.trim().match(/^totient\s*\(\s*(.+?)\s*\)$/i);
    if (m2)
        return normArith(m2[1]);
    return null;
}
/**
 * Parse `φ(n) = k` or `totient(n) = k` equality claim.
 * Returns {arg, value} or null.
 */
function parseTotientEquality(s) {
    // φ(n) = k  or  k = φ(n)
    const m1 = s.trim().match(/^[φΦ]\s*\(\s*(.+?)\s*\)\s*=\s*(.+)$/);
    if (m1)
        return { arg: normArith(m1[1]), value: normArith(m1[2]) };
    const m2 = s.trim().match(/^(.+?)\s*=\s*[φΦ]\s*\(\s*(.+?)\s*\)$/);
    if (m2)
        return { arg: normArith(m2[2]), value: normArith(m2[1]) };
    const m3 = s.trim().match(/^totient\s*\(\s*(.+?)\s*\)\s*=\s*(.+)$/i);
    if (m3)
        return { arg: normArith(m3[1]), value: normArith(m3[2]) };
    return null;
}
/** Compute Euler's totient for a concrete integer. */
function computeTotient(n) {
    if (n <= 0)
        return 0;
    let result = n;
    let temp = n;
    for (let p = 2; p * p <= temp; p++) {
        if (temp % p === 0) {
            while (temp % p === 0)
                temp = Math.floor(temp / p);
            result -= Math.floor(result / p);
        }
    }
    if (temp > 1)
        result -= Math.floor(result / temp);
    return result;
}
// ── Power expressions ─────────────────────────────────────────────────────────
/**
 * Parse `a^b` or `a ** b` (top-level) → {base, exp}, or null.
 * Strips one layer of outer parentheses before scanning.
 */
function parsePower(s) {
    // Try both raw and outer-paren-stripped forms
    for (const norm of [s.trim(), stripOuter(s.trim())]) {
        let depth = 0;
        for (let i = norm.length - 1; i >= 0; i--) {
            const ch = norm[i];
            if (ch === ')' || ch === ']')
                depth++;
            else if (ch === '(' || ch === '[')
                depth--;
            else if (depth === 0 && ch === '^') {
                const base = norm.slice(0, i).trim();
                const exp = norm.slice(i + 1).trim();
                if (base && exp)
                    return { base, exp };
            }
            else if (depth === 0 && ch === '*' && i > 0 && norm[i - 1] === '*') {
                const base = norm.slice(0, i - 1).trim();
                const exp = norm.slice(i + 1).trim();
                if (base && exp)
                    return { base, exp };
            }
        }
    }
    return null;
}
