// src/parsing/parser.ts

import { ParsedLine } from './lexer';
import { ASTNode, TheoremNode, DefinitionNode, ProofNode, AssertNode, LetNode, RawNode } from './ast';

export function parseLinesToAST(lines: ParsedLine[]): ASTNode[] {
  const ast: ASTNode[] = [];
  const stack: (TheoremNode | DefinitionNode | ProofNode)[] = [];

  for (const line of lines) {
    switch (line.type) {
      case 'theorem': {
        const theoremNode: TheoremNode = { type: 'Theorem', name: line.name!, body: [] };
        stack.push(theoremNode);
        break;
      }

      case 'definition': {
        const defNode: DefinitionNode = { type: 'Definition', name: line.name!, body: [] };
        stack.push(defNode);
        break;
      }

      case 'proof': {
        const proofNode: ProofNode = { type: 'Proof', body: [] };
        stack.push(proofNode);
        break;
      }

      case 'assert': {
        // Match conditions like assert(x == y) or assert(condition)
        const conditionMatch = line.content.match(/assert\((.*?)\);?/);
        const condition = conditionMatch ? conditionMatch[1] : line.content;

        const assertNode: AssertNode = { type: 'Assert', condition };
        getCurrentBlock(stack).body.push(assertNode);
        break;
      }

      case 'let': {
        // Match let variable = value;
        const letMatch = line.content.match(/let\s+(\w+)\s*=\s*(.+?);/);
        if (letMatch) {
          const varName = letMatch[1];
          const value = letMatch[2];
          const letNode: LetNode = { type: 'Let', varName, value };
          getCurrentBlock(stack).body.push(letNode);
        } else {
          // If it doesn't match the pattern, treat as raw
          const rawNode: RawNode = { type: 'Raw', content: line.content };
          getCurrentBlock(stack).body.push(rawNode);
        }
        break;
      }

      case 'raw': {
        const rawNode: RawNode = { type: 'Raw', content: line.content };
        getCurrentBlock(stack).body.push(rawNode);
        break;
      }

      case 'blockEnd': {
        // Closing a theorem, definition, or proof block
        const finishedBlock = stack.pop();
        if (!finishedBlock) {
          throw new Error('Unmatched closing brace');
        }
        if (stack.length === 0) {
          // Top-level block finished
          ast.push(finishedBlock);
        } else {
          // Nested block finished (if you have nesting)
          getCurrentBlock(stack).body.push(finishedBlock);
        }
        break;
      }
    }
  }

  if (stack.length > 0) {
    throw new Error('Some blocks not closed properly');
  }

  return ast;
}

function getCurrentBlock(stack: (TheoremNode | DefinitionNode | ProofNode)[]): (TheoremNode | DefinitionNode | ProofNode) {
  if (stack.length === 0) {
    throw new Error('No current block to add to');
  }
  return stack[stack.length - 1];
}
