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
