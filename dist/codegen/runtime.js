"use strict";
// src/codegen/runtime.ts
Object.defineProperty(exports, "__esModule", { value: true });
exports.runtimePreamble = void 0;
exports.runtimePreamble = `
const usedNames = new Set();  // Track at runtime

const assert = (condition) => {
  if (typeof condition === 'string') {
    console.log('Assert:', condition);
    return true;
  }
  if (!condition) throw new Error('Assertion failed');
  return true;
};

const theorem = (name, body) => { // Changed: body is now the entire expression, not a function
  const lowerName = name.toLowerCase();
  if (usedNames.has(lowerName)) {
    throw new Error(\`Duplicate name: \${name} (case insensitive)\`);
  }
  usedNames.add(lowerName);
  console.log('Theorem:', name, body);  // Log the entire theorem body
  return body; // Return the result of evaluating the body
};

const setVar = (name, value) => {
    globalThis[name] = value; // Use globalThis for better compatibility
    return value;             // Return the assigned value!!  This is crucial
};

// Implement logical and set functions:
function forall(x, domain, body) { return body; }
function exists(x, domain, body) { return body; }
function not(p) { return !p; }
function and(p, q) { return p && q; }
function or(p, q) { return p || q; }
function implies(p, q) { return (!p) || q; }
function iff(p, q) { return p === q; }

function inSet(el, setName) { return true; }
function notInSet(el, setName) { return false; }
function subseteq(a, b) { return true; }
function subset(a, b) { return true; }
function union(a, b) { return a; }
function intersect(a, b) { return a; }
function emptySet() { return []; }

// Predicates like P(x) can also be defined if needed:
function P(x) { return true; }
function Q(x) { return true; }
function R(x) { return true; }
`;
