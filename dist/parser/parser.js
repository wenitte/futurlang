"use strict";
// src/parser/parser.ts
//
// Converts a flat list of ParsedLines into a statement-level AST.
// Multi-line assert(...) blocks are joined before expression-parsing.
Object.defineProperty(exports, "__esModule", { value: true });
exports.parseLinesToAST = parseLinesToAST;
const expr_1 = require("./expr");
function parseLinesToAST(lines) {
    const ast = [];
    const stack = [];
    for (const line of lines) {
        switch (line.type) {
            case 'theorem': {
                const node = { type: 'Theorem', name: line.name, body: [] };
                stack.push(node);
                break;
            }
            case 'definition': {
                const node = { type: 'Definition', name: line.name, body: [] };
                stack.push(node);
                break;
            }
            case 'lemma': {
                // Lemma reuses DefinitionNode shape for now
                const node = { type: 'Definition', name: `lemma_${line.name}`, body: [] };
                stack.push(node);
                break;
            }
            case 'proof': {
                const node = { type: 'Proof', body: [] };
                stack.push(node);
                break;
            }
            case 'assert': {
                const exprSrc = extractAssertBody(line.content);
                const expr = (0, expr_1.parseExpr)(exprSrc);
                const node = { type: 'Assert', expr };
                getCurrentBlock(stack).body.push(node);
                break;
            }
            case 'let': {
                const m = line.content.match(/^let\s+(\w+)\s*=\s*(.+?);?\s*$/);
                if (m) {
                    const node = { type: 'Let', varName: m[1], value: m[2] };
                    getCurrentBlock(stack).body.push(node);
                }
                else {
                    getCurrentBlock(stack).body.push({ type: 'Raw', content: line.content });
                }
                break;
            }
            case 'raw': {
                const node = { type: 'Raw', content: line.content };
                // If we're inside a block, attach; otherwise top-level raw
                if (stack.length > 0) {
                    getCurrentBlock(stack).body.push(node);
                }
                else {
                    ast.push(node);
                }
                break;
            }
            case 'blockEnd': {
                const finished = stack.pop();
                if (!finished)
                    throw new Error('Unmatched closing brace }');
                if (stack.length === 0) {
                    ast.push(finished);
                }
                else {
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
function getCurrentBlock(stack) {
    if (stack.length === 0)
        throw new Error('No current block');
    return stack[stack.length - 1];
}
/**
 * Extract the expression inside assert(...).
 * Handles multi-line content that has already been joined.
 */
function extractAssertBody(content) {
    // Strip leading "assert" keyword, optional whitespace, then balanced parens
    const m = content.match(/^assert\s*\(([\s\S]*)\)\s*;?\s*$/);
    if (m)
        return m[1].trim();
    // Fallback: return everything after "assert"
    return content.replace(/^assert\s*/, '').trim();
}
