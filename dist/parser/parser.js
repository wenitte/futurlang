"use strict";
// src/parser/parser.ts
//
// Builds an AST from lexed lines, preserving inter-block connectives.
// The final output is a flat list of top-level nodes each tagged with
// the connective that connects it to the next node — so the whole
// program can be folded into a single logical expression.
Object.defineProperty(exports, "__esModule", { value: true });
exports.parseLinesToAST = parseLinesToAST;
const expr_1 = require("./expr");
function parseLinesToAST(lines) {
    const ast = [];
    const stack = [];
    for (const line of lines) {
        switch (line.type) {
            // ── Block openers ──────────────────────────────────────────────────────
            case 'theorem': {
                const node = { type: 'Theorem', name: line.name, body: [], connective: null };
                stack.push(node);
                break;
            }
            case 'definition': {
                const node = { type: 'Definition', name: line.name, body: [], connective: null };
                stack.push(node);
                break;
            }
            case 'struct': {
                const node = { type: 'Struct', name: line.name, fields: [], connective: null };
                stack.push(node);
                break;
            }
            case 'proof': {
                const node = { type: 'Proof', name: line.name, body: [], connective: null };
                stack.push(node);
                break;
            }
            case 'lemma': {
                const node = { type: 'Lemma', name: line.name, body: [], connective: null };
                stack.push(node);
                break;
            }
            // ── Block-end: pop, attach connective, push to parent or top-level ─────
            case 'blockEnd': {
                const finished = stack.pop();
                if (!finished)
                    throw new Error('Unmatched }');
                // The connective on the } belongs to this block
                finished.connective = line.connective;
                if (stack.length === 0) {
                    ast.push(finished);
                }
                else {
                    pushToBlock(stack[stack.length - 1], finished);
                }
                break;
            }
            // ── Statement nodes ────────────────────────────────────────────────────
            case 'assert': {
                const body = extractCallBody(line.content, 'assert');
                let expr;
                try {
                    expr = (0, expr_1.parseExpr)(body);
                }
                catch {
                    // Preserve unsupported claims for non-JS backends, but do not
                    // silently turn them into provable string assertions.
                    expr = { type: 'Atom', condition: body, atomKind: 'opaque' };
                }
                const node = { type: 'Assert', expr, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'assume': {
                const body = extractCallBody(line.content, 'assume');
                let expr;
                try {
                    expr = (0, expr_1.parseExpr)(body);
                }
                catch {
                    expr = { type: 'Atom', condition: body, atomKind: 'opaque' };
                }
                const node = { type: 'Assume', expr, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'conclude': {
                const body = extractCallBody(line.content, 'conclude');
                let expr;
                try {
                    expr = (0, expr_1.parseExpr)(body);
                }
                catch {
                    expr = { type: 'Atom', condition: body, atomKind: 'opaque' };
                }
                const node = { type: 'Conclude', expr, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'apply': {
                const node = { type: 'Apply', target: line.name, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'setVar': {
                const node = parseSetVar(line.content, line.connective);
                pushOrTop(stack, ast, node);
                break;
            }
            case 'return':
            case 'level':
            case 'raw': {
                const node = { type: 'Raw', content: line.content, connective: line.connective };
                // Struct fields go into fields[], others go into body
                if (stack.length > 0 && stack[stack.length - 1].type === 'Struct') {
                    stack[stack.length - 1].fields.push(line.content);
                }
                else {
                    pushOrTop(stack, ast, node);
                }
                break;
            }
        }
    }
    if (stack.length > 0)
        throw new Error(`Unclosed block: ${stack[stack.length - 1].type}`);
    return ast;
}
// ── Helpers ──────────────────────────────────────────────────────────────────
function pushOrTop(stack, ast, node) {
    if (stack.length > 0) {
        pushToBlock(stack[stack.length - 1], node);
    }
    else {
        ast.push(node);
    }
}
function pushToBlock(block, node) {
    if (block.type === 'Struct') {
        // structs don't have a body[] for statement nodes — skip
        return;
    }
    block.body.push(node);
}
function extractCallBody(content, keyword) {
    const m = content.match(new RegExp(`^${keyword}\\s*\\(([\\s\\S]*)\\)\\s*;?\\s*$`));
    if (m)
        return m[1].trim();
    return content.replace(new RegExp(`^${keyword}\\s*`), '').trim();
}
function parseSetVar(content, connective) {
    // let name = value  (from let-style lines)
    const letForm = content.match(/^let\s+(\w[\w₀-₉ₐ-ₙ]*)\s*=\s*(.+?);?\s*$/);
    if (letForm) {
        return { type: 'SetVar', varName: letForm[1], varType: null, value: letForm[2].trim(), connective };
    }
    // setVar(name: Type)  or  setVar(name: Type, value)  or  setVar(name, value)
    const inner = extractCallBody(content, 'setVar');
    // Try: name: Type, value
    const typed = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*:\s*([^,]+),\s*(.+)$/);
    if (typed) {
        return { type: 'SetVar', varName: typed[1], varType: typed[2].trim(), value: typed[3].trim(), connective };
    }
    // Try: name: Type  (declaration only)
    const decl = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*:\s*(.+)$/);
    if (decl) {
        return { type: 'SetVar', varName: decl[1], varType: decl[2].trim(), value: null, connective };
    }
    // Try: name, value  (untyped)
    const untyped = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+)$/);
    if (untyped) {
        return { type: 'SetVar', varName: untyped[1], varType: null, value: untyped[2].trim(), connective };
    }
    // Bare name
    return { type: 'SetVar', varName: inner.trim(), varType: null, value: null, connective };
}
