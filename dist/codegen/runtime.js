"use strict";
// src/codegen/runtime.ts
Object.defineProperty(exports, "__esModule", { value: true });
exports.runtimePreamble = void 0;
exports.runtimePreamble = `
// ── FuturLang Runtime ─────────────────────────────────────────────────────────

const _usedNames = new Set();

// Resolve a value: thunk, literal, or object with .value
function _resolve(v) {
  if (v && typeof v === 'object' && 'value' in v) return v.value;
  if (typeof v === 'function') return !!v();
  return !!v;
}

// ── Atom ──────────────────────────────────────────────────────────────────────
// atom(valueOrThunk, label?)
function atom(v, label) {
  const value = typeof v === 'function' ? !!v() : !!v;
  return { kind: 'atom', value, label: label ?? String(v) };
}

// ── Connectives ───────────────────────────────────────────────────────────────

function and(a, b) {
  return { kind: 'and', value: _resolve(a) && _resolve(b), left: a, right: b };
}

function or(a, b) {
  return { kind: 'or', value: _resolve(a) || _resolve(b), left: a, right: b };
}

function implies(a, b) {
  // P → Q  ≡  ¬P ∨ Q
  return { kind: 'implies', value: !_resolve(a) || _resolve(b), antecedent: a, consequent: b };
}

function iff(a, b) {
  return { kind: 'iff', value: _resolve(a) === _resolve(b), left: a, right: b };
}

function not(a) {
  return { kind: 'not', value: !_resolve(a), operand: a };
}

// ── describe ──────────────────────────────────────────────────────────────────

function _describe(r) {
  if (typeof r !== 'object' || r === null) return String(r);
  switch (r.kind) {
    case 'atom':    return r.label ?? '(expr)';
    case 'and':     return '(' + _describe(r.left)      + ' ∧ ' + _describe(r.right)      + ')';
    case 'or':      return '(' + _describe(r.left)      + ' ∨ ' + _describe(r.right)      + ')';
    case 'implies': return '(' + _describe(r.antecedent) + ' → ' + _describe(r.consequent) + ')';
    case 'iff':     return '(' + _describe(r.left)      + ' ↔ ' + _describe(r.right)      + ')';
    case 'not':     return '(¬' + _describe(r.operand)  + ')';
    default:        return JSON.stringify(r);
  }
}

// ── assertExpr ────────────────────────────────────────────────────────────────

function assertExpr(result) {
  const val  = _resolve(result);
  const desc = _describe(result);
  if (!val) throw new Error('Assertion failed: ' + desc);
  console.log('  ✓', desc);
  return true;
}

// ── Block helpers ─────────────────────────────────────────────────────────────

function theorem(name, fn) {
  const key = name.toLowerCase();
  if (_usedNames.has(key)) throw new Error('Duplicate theorem name: ' + name);
  _usedNames.add(key);
  console.log('\\nTheorem ' + name + ':');
  fn();
  console.log('  ✓ QED');
}

function definition(name, fn) {
  console.log('\\nDefinition ' + name + ':');
  fn();
}

function setVar(name, value) {
  globalThis[name] = value;
  return true;
}
`;
