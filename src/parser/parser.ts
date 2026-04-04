// src/parser/parser.ts
//
// Converts a flat list of ParsedLines into a statement-level AST.
// Multi-line assert(...) blocks are joined before expression-parsing.

import { ParsedLine } from './lexer';
import { parseExpr } from './expr';
import {
  ASTNode, TheoremNode, DefinitionNode, ProofNode,
  AssertNode, LetNode, RawNode,
} from './ast';

type BlockNode = TheoremNode | DefinitionNode | ProofNode;

export function parseLinesToAST(lines: ParsedLine[]): ASTNode[] {
  const ast: ASTNode[] = [];
  const stack: BlockNode[] = [];

  for (const line of lines) {
    switch (line.type) {
      case 'theorem': {
        const node: TheoremNode = { type: 'Theorem', name: line.name!, body: [] };
        stack.push(node);
        break;
      }
      case 'definition': {
        const node: DefinitionNode = { type: 'Definition', name: line.name!, body: [] };
        stack.push(node);
        break;
      }
      case 'lemma': {
        // Lemma reuses DefinitionNode shape for now
        const node: DefinitionNode = { type: 'Definition', name: `lemma_${line.name!}`, body: [] };
        stack.push(node);
        break;
      }
      case 'proof': {
        const node: ProofNode = { type: 'Proof', body: [] };
        stack.push(node);
        break;
      }

      case 'assert': {
        const exprSrc = extractAssertBody(line.content);
        const expr    = parseExpr(exprSrc);
        const node: AssertNode = { type: 'Assert', expr };
        getCurrentBlock(stack).body.push(node);
        break;
      }

      case 'let': {
        const m = line.content.match(/^let\s+(\w+)\s*=\s*(.+?);?\s*$/);
        if (m) {
          const node: LetNode = { type: 'Let', varName: m[1], value: m[2] };
          getCurrentBlock(stack).body.push(node);
        } else {
          getCurrentBlock(stack).body.push({ type: 'Raw', content: line.content });
        }
        break;
      }

      case 'raw': {
        const node: RawNode = { type: 'Raw', content: line.content };
        // If we're inside a block, attach; otherwise top-level raw
        if (stack.length > 0) {
          getCurrentBlock(stack).body.push(node);
        } else {
          ast.push(node);
        }
        break;
      }

      case 'blockEnd': {
        const finished = stack.pop();
        if (!finished) throw new Error('Unmatched closing brace }');
        if (stack.length === 0) {
          ast.push(finished);
        } else {
          getCurrentBlock(stack).body.push(finished);
        }
        break;
      }
    }
  }

  if (stack.length > 0) {
    throw new Error(`Unclosed block: ${stack[stack.length - 1].type}`);
  }

  return ast;
}

// ── Helpers ─────────────────────────────────────────────────────────────────

function getCurrentBlock(stack: BlockNode[]): BlockNode {
  if (stack.length === 0) throw new Error('No current block');
  return stack[stack.length - 1];
}

/**
 * Extract the expression inside assert(...).
 * Handles multi-line content that has already been joined.
 */
function extractAssertBody(content: string): string {
  // Strip leading "assert" keyword, optional whitespace, then balanced parens
  const m = content.match(/^assert\s*\(([\s\S]*)\)\s*;?\s*$/);
  if (m) return m[1].trim();
  // Fallback: return everything after "assert"
  return content.replace(/^assert\s*/, '').trim();
}


