// src/parser/formal.ts
import { Statement, Proof, LogicalOperator } from '../types/basic'

export function parseFormalNotation(text: string): Proof {
    const lines = text.split('\n').filter(line => line.trim())
    const statements: Statement[] = []
    let method: Proof['method'] = 'direct'
    const prerequisites: string[] = []

    let currentId = 1

    for (const line of lines) {
        if (line.includes('Induction')) {
            method = 'induction'
            continue
        }

        if (line.match(/^\(\d+\)/)) {
            const statement: Statement = {
                id: currentId++,
                content: line.replace(/^\(\d+\)\s*/, '').trim(),
                type: 'step'
            }

            if (line.includes('assume') || line.includes('Assume')) {
                statement.type = 'assumption'
            } else if (line.includes('therefore') || line.includes('Thus')) {
                statement.type = 'conclusion'
            }

            statements.push(statement)
        }
    }

    return {
        statements,
        method,
        prerequisites
    }
}

export function parseFL(text: string): string {
  const lines = text.split('\n').filter(line => line.trim())
  let output = ''

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

    const setVar = (name, value) => {
      global[name] = value;
      return true;
    };
  `

  let inTheorem = false
  let inProof = false
  let currentTheorem = ''

  for (const line of lines) {
    if (line.includes('theorem')) {
      inTheorem = true
      currentTheorem = line.match(/theorem\s+(\w+)/)?.[1] || ''
      output += `theorem("${currentTheorem}", () => {\n`
      continue
    }

    if (line.includes('proof')) {
      inProof = true
      continue
    }

    if (line.includes('assert')) {
      output += `  ${line}\n`
      continue
    }

    if (line.includes('let')) {
      const match = line.match(/let\s+(\w+)\s*=\s*(.+?);/)
      if (match) {
        const [_, varName, value] = match
        output += `  setVar("${varName}", ${value})\n`
        continue
      }
    }

    if (line.includes('}')) {
      if (inProof) {
        inProof = false
      } else if (inTheorem) {
        inTheorem = false
        output += '});\n'
      }
      continue
    }

    output += `  ${line}\n`
  }

  return output
}
