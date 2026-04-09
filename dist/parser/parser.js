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
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i];
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
            case 'typeDecl': {
                const node = { type: 'TypeDecl', name: line.name, variants: [], connective: null };
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
            case 'fn': {
                const signature = parseFnSignature(line.content);
                const node = {
                    type: 'FnDecl',
                    name: signature.name,
                    params: signature.params,
                    returnType: signature.returnType,
                    body: [],
                    connective: null,
                };
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
                if (finished.type === 'Struct') {
                    finished.fields = finished.fields.map(field => parseStructField(field));
                }
                if (finished.type === 'TypeDecl') {
                    finished.variants = finished.variants.map(variant => parseTypeVariant(variant));
                }
                const lowered = finished.type === 'FnDecl' ? desugarFnDecl(finished) : [finished];
                if (stack.length === 0) {
                    ast.push(...lowered);
                }
                else {
                    for (const node of lowered) {
                        pushToBlock(stack[stack.length - 1], node);
                    }
                }
                break;
            }
            // ── Statement nodes ────────────────────────────────────────────────────
            case 'assert': {
                const expr = parseCallExpr(line.content, 'assert');
                const node = { type: 'Assert', expr, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'given': {
                const expr = parseCallExpr(line.content, 'given');
                const node = { type: 'Given', expr, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'assume': {
                const expr = parseCallExpr(line.content, 'assume');
                const node = { type: 'Assume', expr, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'conclude': {
                const expr = parseCallExpr(line.content, 'conclude');
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
            case 'induction': {
                const parsed = parseInduction(lines, i);
                i = parsed.nextIndex;
                pushOrTop(stack, ast, parsed.node);
                break;
            }
            case 'match': {
                const parsed = parseMatch(lines, i);
                i = parsed.nextIndex;
                pushOrTop(stack, ast, parsed.node);
                break;
            }
            case 'base':
            case 'step':
            case 'case':
                throw new Error(`${line.type}: may only appear inside induction(...)`);
            case 'return':
            case 'level':
            case 'raw': {
                const node = { type: 'Raw', content: line.content, connective: line.connective };
                // Struct fields go into fields[], others go into body
                if (stack.length > 0 && stack[stack.length - 1].type === 'Struct') {
                    stack[stack.length - 1].fields.push(line.content);
                }
                else if (stack.length > 0 && stack[stack.length - 1].type === 'TypeDecl') {
                    stack[stack.length - 1].variants.push(line.content);
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
    validateTopLevelConnectives(ast);
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
    if (block.type === 'Struct' || block.type === 'TypeDecl') {
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
function parseCallExpr(content, keyword) {
    const body = extractCallBody(content, keyword);
    try {
        return (0, expr_1.parseExpr)(body);
    }
    catch (error) {
        return {
            type: 'Atom',
            condition: body,
            atomKind: 'opaque',
            parseError: error instanceof Error ? error.message : 'Expression could not be parsed',
        };
    }
}
function parseInduction(lines, start) {
    const line = lines[start];
    const match = line.content.match(/^induction\s*\(([\s\S]+)\)\s*\{$/);
    if (!match) {
        throw new Error('Malformed induction block');
    }
    const iterator = match[1].trim();
    let base = null;
    let step = null;
    let connective = line.connective;
    let cursor = start + 1;
    while (cursor < lines.length) {
        const current = lines[cursor];
        if (current.type === 'blockEnd') {
            connective = current.connective;
            break;
        }
        if (current.type === 'base') {
            base = current.content.replace(/^base\s*:\s*/, '').trim();
        }
        else if (current.type === 'step') {
            step = current.content.replace(/^step\s*:\s*/, '').trim();
        }
        else {
            throw new Error(`Unexpected line inside induction block: ${current.content}`);
        }
        cursor++;
    }
    if (cursor >= lines.length || lines[cursor].type !== 'blockEnd') {
        throw new Error('Unclosed induction block');
    }
    if (!base || !step) {
        throw new Error('induction(...) requires both base: and step:');
    }
    const fold = {
        type: 'Fold',
        sequence: `[0..${iterator}]`,
        init: `proof(${base})`,
        fn: `step_fn(${step})`,
        sugar: 'induction',
    };
    return {
        node: {
            type: 'Induction',
            iterator,
            fold,
            base,
            step,
            connective,
        },
        nextIndex: cursor,
    };
}
function parseFnSignature(content) {
    const match = content.match(/^fn\s+(\w+)\s*\(([\s\S]*)\)\s*->\s*([^{]+)\s*\{$/);
    if (!match) {
        throw new Error(`Malformed fn signature: ${content}`);
    }
    const [, name, rawParams, returnType] = match;
    const params = rawParams.trim()
        ? splitFnParams(rawParams).map(parseFnParam)
        : [];
    return {
        name,
        params,
        returnType: returnType.trim(),
    };
}
function splitFnParams(value) {
    const params = [];
    let depth = 0;
    let start = 0;
    for (let i = 0; i < value.length; i++) {
        const ch = value[i];
        if (ch === '(')
            depth++;
        else if (ch === ')')
            depth = Math.max(0, depth - 1);
        else if (ch === ',' && depth === 0) {
            params.push(value.slice(start, i).trim());
            start = i + 1;
        }
    }
    const final = value.slice(start).trim();
    if (final)
        params.push(final);
    return params;
}
function parseFnParam(value) {
    const match = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
    if (!match) {
        throw new Error(`Malformed fn parameter: ${value}`);
    }
    return { name: match[1], type: normalizeSortName(match[2]) };
}
function parseStructField(value) {
    const trimmed = value.trim().replace(/,+$/, '').trim();
    const match = trimmed.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
    if (!match) {
        throw new Error(`Malformed struct field: ${value}`);
    }
    return {
        name: match[1],
        type: normalizeSortName(match[2]),
    };
}
function parseTypeVariant(value) {
    const trimmed = value.trim().replace(/,+$/, '').trim();
    const match = trimmed.match(/^\|\s*(\w[\w₀-₉ₐ-ₙ]*)\s*\(([\s\S]*)\)\s*$/);
    if (!match) {
        throw new Error(`Malformed type variant: ${value}`);
    }
    const [, name, rawFields] = match;
    const fields = rawFields.trim() ? splitFnParams(rawFields).map(parseStructField) : [];
    return { name, fields };
}
function desugarFnDecl(node) {
    const conclusion = findFnConclusion(node.body);
    const matchBody = findTopLevelMatch(node.body);
    if (!conclusion && !matchBody) {
        throw new Error(`fn '${node.name}' requires a conclude(...) statement`);
    }
    const goalExpr = conclusion
        ? conclusion.expr
        : (0, expr_1.parseExpr)(`${node.name}(${node.params.map(param => param.name).join(', ')}) ∈ ${normalizeSortName(node.returnType)}`);
    const theoremBody = node.params.map(param => ({
        type: 'Given',
        expr: (0, expr_1.parseExpr)(`${param.name} ∈ ${param.type}`),
        connective: '→',
    }));
    theoremBody.push({
        type: 'Assert',
        expr: goalExpr,
        connective: null,
    });
    const theorem = {
        type: 'Theorem',
        name: node.name,
        body: theoremBody,
        connective: '↔',
    };
    const proofBody = conclusion
        ? [
            {
                type: 'Assume',
                expr: conclusion.expr,
                connective: node.body.length > 0 ? '→' : null,
            },
            ...node.body,
        ]
        : node.body;
    const proof = {
        type: 'Proof',
        name: node.name,
        body: proofBody,
        connective: node.connective,
    };
    return [theorem, proof];
}
function normalizeSortName(value) {
    return (0, expr_1.normalizeSurfaceSyntax)(value).trim();
}
function findFnConclusion(body) {
    for (let i = body.length - 1; i >= 0; i--) {
        const node = body[i];
        if (node.type === 'Conclude') {
            return node;
        }
    }
    return null;
}
function findTopLevelMatch(body) {
    for (const node of body) {
        if (node.type === 'Match')
            return node;
    }
    return null;
}
function parseMatch(lines, start) {
    const line = lines[start];
    const match = line.content.match(/^match\s+([\s\S]+)\s*\{$/);
    if (!match) {
        throw new Error('Malformed match block');
    }
    const scrutinee = (0, expr_1.parseExpr)(match[1].trim());
    const cases = [];
    let connective = line.connective;
    let cursor = start + 1;
    while (cursor < lines.length) {
        const current = lines[cursor];
        if (current.type === 'blockEnd') {
            connective = current.connective;
            break;
        }
        if (current.type !== 'case') {
            throw new Error(`Unexpected line inside match block: ${current.content}`);
        }
        cases.push(parseMatchCase(current.content));
        cursor++;
    }
    if (cursor >= lines.length || lines[cursor].type !== 'blockEnd') {
        throw new Error('Unclosed match block');
    }
    return {
        node: {
            type: 'Match',
            scrutinee,
            cases,
            connective,
        },
        nextIndex: cursor,
    };
}
function parseMatchCase(content) {
    const match = content.match(/^case\s+(.+?)\s*=>\s*([\s\S]+)$/);
    if (!match) {
        throw new Error(`Malformed case clause: ${content}`);
    }
    return {
        pattern: parsePattern(match[1].trim()),
        body: [parseInlineStatement(match[2].trim())],
    };
}
function parsePattern(value) {
    if (value === '_') {
        return { constructor: '_', bindings: [] };
    }
    const match = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*\(([\s\S]*)\)\s*$/);
    if (!match) {
        throw new Error(`Malformed pattern: ${value}`);
    }
    const [, constructor, rawBindings] = match;
    const bindings = rawBindings.trim()
        ? splitFnParams(rawBindings).map(binding => binding.trim()).map(binding => binding === '_' ? '_' : binding)
        : [];
    return { constructor, bindings };
}
function parseInlineStatement(content) {
    if (/^conclude\s*\(/.test(content)) {
        return { type: 'Conclude', expr: parseCallExpr(content, 'conclude'), connective: null };
    }
    if (/^assert\s*\(/.test(content)) {
        return { type: 'Assert', expr: parseCallExpr(content, 'assert'), connective: null };
    }
    if (/^assume\s*\(/.test(content)) {
        return { type: 'Assume', expr: parseCallExpr(content, 'assume'), connective: null };
    }
    if (/^apply\s*\(/.test(content)) {
        const target = content.match(/^apply\s*\((.+)\)/)?.[1]?.trim() ?? content;
        return { type: 'Apply', target, connective: null };
    }
    return { type: 'Raw', content, connective: null };
}
function validateTopLevelConnectives(ast) {
    for (let i = 0; i < ast.length - 1; i++) {
        const node = ast[i];
        if (isTopLevelBlock(node) && node.connective === null) {
            throw new Error(`Missing connective between top-level blocks after ${describeTopLevelNode(node)}`);
        }
    }
}
function isTopLevelBlock(node) {
    return node.type === 'Theorem' ||
        node.type === 'Definition' ||
        node.type === 'Struct' ||
        node.type === 'TypeDecl' ||
        node.type === 'Proof' ||
        node.type === 'Lemma' ||
        node.type === 'FnDecl';
}
function describeTopLevelNode(node) {
    switch (node.type) {
        case 'Theorem':
        case 'Definition':
        case 'Struct':
        case 'TypeDecl':
        case 'Proof':
        case 'Lemma':
        case 'FnDecl':
            return `${node.type.toLowerCase()} '${node.name}'`;
    }
}
