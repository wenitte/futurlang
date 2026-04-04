"use strict";
// src/codegen/runtime.ts
Object.defineProperty(exports, "__esModule", { value: true });
exports.runtimePreamble = void 0;
exports.runtimePreamble = `
// ── FuturLang Runtime ─────────────────────────────────────────────────────────

const _usedNames  = new Set();
const _lemmaCache = new Map();
const _vars       = new Map();

// Resolve a result object or raw value to boolean
function _resolve(v) {
  if (v && typeof v === 'object' && 'value' in v) return !!v.value;
  if (typeof v === 'function') return !!v();
  return !!v;
}

// ── Atom ──────────────────────────────────────────────────────────────────────
function atom(v, label) {
  const value = typeof v === 'function' ? !!v() : !!v;
  return { kind: 'atom', value, label: label ?? String(v) };
}

// ── Connectives ───────────────────────────────────────────────────────────────
function and(a, b) {
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'and', value: lv && rv, left: a, right: b };
}
function or(a, b) {
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'or', value: lv || rv, left: a, right: b };
}
function seq(aFn, bFn) {
  // Evaluate left side first (runs setVar side-effects, etc.)
  const a  = aFn();
  const lv = _resolve(a);
  // Only evaluate right side if left holds (short-circuit like →)
  const b  = bFn();
  const rv = _resolve(b);
  return { kind: 'implies', value: !lv || rv, antecedent: a, consequent: b };
}

function implies(a, b) {
  // P → Q  ≡  ¬P ∨ Q  (logical connective inside expressions)
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'implies', value: !lv || rv, antecedent: a, consequent: b };
}

function iff(a, b) {
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'iff', value: lv === rv, left: a, right: b };
}
function not(a) {
  const v = _resolve(a);
  return { kind: 'not', value: !v, operand: a };
}

// ── Describe ──────────────────────────────────────────────────────────────────
function _describe(r) {
  if (typeof r !== 'object' || r === null) return String(r);
  switch (r.kind) {
    case 'atom':    return r.label ?? '(expr)';
    case 'and':     return '(' + _describe(r.left)       + ' ∧ ' + _describe(r.right)      + ')';
    case 'or':      return '(' + _describe(r.left)       + ' ∨ ' + _describe(r.right)      + ')';
    case 'implies': return '(' + _describe(r.antecedent) + ' → ' + _describe(r.consequent) + ')';
    case 'iff':     return '(' + _describe(r.left)       + ' ↔ ' + _describe(r.right)      + ')';
    case 'not':     return '(¬' + _describe(r.operand)   + ')';
    default:        return JSON.stringify(r);
  }
}

// ── Statement evaluators ──────────────────────────────────────────────────────

function assertExpr(result) {
  const val = _resolve(result);
  if (!val) throw new Error('Assertion failed: ' + _describe(result));
  console.log('  assert ✓', _describe(result));
  return result;
}

function assumeExpr(result) {
  // Assumptions are axioms — always accepted, establish the proof context
  const desc = typeof result === 'object' ? _describe(result) : String(result);
  console.log('  assume  ', desc);
  return atom(true, 'assume(' + desc + ')');
}

function concludeExpr(result) {
  const val = _resolve(result);
  console.log('  conclude' + (val ? ' ✓' : ' ✗'), _describe(result));
  return result;
}

function applyLemma(name) {
  const result = _lemmaCache.get(name.toLowerCase());
  if (result === undefined) {
    console.log('  apply   ', name, '(not yet registered, assuming true)');
    return atom(true, 'apply(' + name + ')');
  }
  console.log('  apply ✓ ', name);
  return result;
}

function setVar(name, value, label) {
  // Execute immediately — variable must exist before right-hand side evaluates
  if (value !== undefined) {
    try { globalThis[name] = eval(String(value)); }
    catch(e) { globalThis[name] = value; }
  }
  _vars.set(name, globalThis[name]);
  console.log('  let     ', label ?? name, value !== undefined ? '= ' + String(globalThis[name]) : '');
  return atom(true, label ?? name);
}

// ── Block evaluators ──────────────────────────────────────────────────────────

function theorem(name, fn) {
  const key = name.toLowerCase();
  if (_usedNames.has(key)) throw new Error('Duplicate theorem: ' + name);
  _usedNames.add(key);
  console.log('\\nTheorem ' + name);
  const result = fn();
  const val = _resolve(result);
  console.log(val ? '  ✓ QED' : '  ✗ FAILED');
  return atom(val, 'theorem(' + name + ')');
}

function proof(name, fn) {
  console.log('\\nProof ' + name);
  const result = fn();
  const val = _resolve(result);
  console.log(val ? '  ✓ proof holds' : '  ✗ proof failed');
  return atom(val, 'proof(' + name + ')');
}

function lemma(name, fn) {
  console.log('\\nLemma ' + name);
  const result = fn();
  const val = _resolve(result);
  _lemmaCache.set(name.toLowerCase(), result);
  console.log(val ? '  ✓ lemma holds' : '  ✗ lemma failed');
  return atom(val, 'lemma(' + name + ')');
}

function definition(name, fn) {
  console.log('\\nDefinition ' + name);
  const result = fn();
  _lemmaCache.set(name.toLowerCase(), atom(true, name));
  return atom(true, 'definition(' + name + ')');
}

function struct_(name, fields) {
  console.log('\\nStruct ' + name);
  return atom(true, 'struct(' + name + ')');
}
`;
