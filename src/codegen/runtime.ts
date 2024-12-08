// src/codegen/runtime.ts

export const runtimePreamble = `
const usedNames = new Set();  // Track at runtime

const assert = (condition) => {
  if (typeof condition === 'string') {
    console.log('Assert:', condition);
    return true;
  }
  if (!condition) throw new Error('Assertion failed');
  return true;
};

const theorem = (name, fn) => {
  const lowerName = name.toLowerCase();
  if (usedNames.has(lowerName)) {
    throw new Error(\`Duplicate name: \${name} (case insensitive)\`);
  }
  usedNames.add(lowerName);
  console.log('Proving theorem:', name);
  return fn();
};

const setVar = (name, value) => {
  global[name] = value;
  return true;
};
`;
