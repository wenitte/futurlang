"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.parseFormalNotation = parseFormalNotation;
exports.parseFL = parseFL;
function parseFormalNotation(text) {
    const lines = text.split('\n').filter(line => line.trim());
    const statements = [];
    let method = 'direct';
    const prerequisites = [];
    let currentId = 1;
    for (const line of lines) {
        if (line.includes('Induction')) {
            method = 'induction';
            continue;
        }
        if (line.match(/^\(\d+\)/)) {
            const statement = {
                id: currentId++,
                content: line.replace(/^\(\d+\)\s*/, '').trim(),
                type: 'step'
            };
            if (line.includes('assume') || line.includes('Assume')) {
                statement.type = 'assumption';
            }
            else if (line.includes('therefore') || line.includes('Thus')) {
                statement.type = 'conclusion';
            }
            statements.push(statement);
        }
    }
    return {
        statements,
        method,
        prerequisites
    };
}
function parseFL(text) {
    var _a;
    const lines = text.split('\n').filter(line => line.trim());
    const usedNames = new Set(); // Track used names
    let output = '';
    output += `
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
    let inTheorem = false;
    let inProof = false;
    let currentTheorem = '';
    for (const line of lines) {
        if (line.includes('theorem') || line.includes('definition')) {
            const name = (_a = line.match(/(?:theorem|definition)\s+(\w+)/)) === null || _a === void 0 ? void 0 : _a[1];
            if (name) {
                const lowerName = name.toLowerCase();
                if (usedNames.has(lowerName)) {
                    throw new Error(`Duplicate name: ${name} (case insensitive)`);
                }
                usedNames.add(lowerName);
            }
            if (line.includes('theorem')) {
                inTheorem = true;
                currentTheorem = name || '';
                output += `theorem("${currentTheorem}", () => {\n`;
            }
            continue;
        }
        if (line.includes('proof')) {
            inProof = true;
            continue;
        }
        if (line.includes('assert') && line.includes('==')) {
            const match = line.match(/assert\((\w+)\s*==\s*(.+)\);/);
            if (match) {
                const [_, varName, value] = match;
                output += `  assert(global["${varName}"] == ${value})\n`;
                continue;
            }
        }
        if (line.includes('let')) {
            const match = line.match(/let\s+(\w+)\s*=\s*(.+?);/);
            if (match) {
                const [_, varName, value] = match;
                output += `  setVar("${varName}", ${value})\n`;
                continue;
            }
        }
        if (line.includes('}')) {
            if (inProof) {
                inProof = false;
            }
            else if (inTheorem) {
                inTheorem = false;
                output += '});\n';
            }
            continue;
        }
        output += `  ${line}\n`;
    }
    return output;
}
