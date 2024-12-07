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
// Add new FL parser
function parseFL(text) {
    var _a;
    // Convert .fl to JavaScript
    const lines = text.split('\n').filter(line => line.trim());
    let output = '';
    // Add runtime helpers
    output += `
    const assert = (condition) => {
      if (typeof condition === 'string') {
        console.log('Assert:', condition);
        return true;
      }
      if (!condition) throw new Error('Assertion failed');
      return true;
    };

    const theorem = (name, fn) => {
      console.log('Proving theorem:', name);
      return fn();
    };

    const let = (name, value) => {
      global[name] = value;
      return true;
    };
  `;
    // Parse the theorem structure
    let inTheorem = false;
    let inProof = false;
    let currentTheorem = '';
    for (const line of lines) {
        if (line.includes('theorem')) {
            inTheorem = true;
            currentTheorem = ((_a = line.match(/theorem\s+(\w+)/)) === null || _a === void 0 ? void 0 : _a[1]) || '';
            output += `theorem("${currentTheorem}", () => {\n`;
            continue;
        }
        if (line.includes('proof')) {
            inProof = true;
            continue;
        }
        if (line.includes('assert')) {
            output += `  ${line}\n`;
            continue;
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
        // Pass through other lines
        output += `  ${line}\n`;
    }
    return output;
}
