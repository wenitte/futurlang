"use strict";
// src/parser/parser.ts
//
// Builds an AST from lexed lines, preserving inter-block connectives.
// The final output is a flat list of top-level nodes each tagged with
// the connective that connects it to the next node — so the whole
// program can be folded into a single logical expression.
Object.defineProperty(exports, "__esModule", { value: true });
exports.parseLinesToAST = parseLinesToAST;
exports.validateDeclarationBody = validateDeclarationBody;
const expr_1 = require("./expr");
function parseLinesToAST(lines, options = {}) {
    const ast = [];
    const stack = [];
    const desugarFns = options.desugarFns ?? true;
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
                    requires: [],
                    ensures: [],
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
                const lowered = finished.type === 'FnDecl' && desugarFns ? desugarFnDecl(finished) : [finished];
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
                // Legacy keyword — kept for backward compatibility but emits a parse error node
                const currentBlock = stack[stack.length - 1];
                const inDecl = currentBlock?.type === 'Theorem' || currentBlock?.type === 'Lemma';
                const suggestion = inDecl
                    ? 'Use declareToProve() to declare the theorem goal'
                    : 'Use prove() for intermediate steps or conclude() for the final step';
                const errExpr = parseCallExpr(line.content, 'assert');
                const node = { type: 'Assert', expr: errExpr, connective: line.connective };
                // Store the migration hint as a parse error on the atom
                node.legacyError = `assert() is no longer valid. ${suggestion}`;
                pushOrTop(stack, ast, node);
                break;
            }
            case 'given': {
                // Legacy keyword — emit error
                const errExpr = parseCallExpr(line.content, 'given');
                const node = { type: 'Given', expr: errExpr, connective: line.connective };
                node.legacyError = 'given() is no longer valid. Use assume() to declare hypotheses';
                pushOrTop(stack, ast, node);
                break;
            }
            case 'declareToProve': {
                const expr = parseCallExpr(line.content, 'declareToProve');
                const node = { type: 'DeclareToProve', expr, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'prove': {
                const expr = parseCallExpr(line.content, 'prove');
                const node = { type: 'Prove', expr, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'andIntroStep': {
                // AndIntro(P, Q) — parse two comma-separated claims
                const inner = line.content.replace(/^AndIntro\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
                const commaIdx = inner.lastIndexOf(',');
                const left = commaIdx >= 0 ? inner.slice(0, commaIdx).trim() : inner;
                const right = commaIdx >= 0 ? inner.slice(commaIdx + 1).trim() : '';
                const node = { type: 'AndIntroStep', left, right, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'orIntroStep': {
                // OrIntro(P ∨ Q) — the full disjunction to introduce
                const claim = line.content.replace(/^OrIntro\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
                const node = { type: 'OrIntroStep', claim, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'requires': {
                const expr = parseCallExpr(line.content, 'requires');
                if (stack.length > 0 && stack[stack.length - 1].type === 'FnDecl') {
                    stack[stack.length - 1].requires.push(expr);
                }
                else {
                    throw new Error('requires() may only appear inside fn blocks');
                }
                break;
            }
            case 'ensures': {
                const expr = parseCallExpr(line.content, 'ensures');
                if (stack.length > 0 && stack[stack.length - 1].type === 'FnDecl') {
                    stack[stack.length - 1].ensures.push(expr);
                }
                else {
                    throw new Error('ensures() may only appear inside fn blocks');
                }
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
            case 'intro': {
                const inner = line.content.replace(/^intro\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
                const colonMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*[:\s]\s*(.+)$/);
                const memMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
                const m = colonMatch ?? memMatch;
                const varName = m?.[1] ?? inner;
                const varType = m?.[2]?.trim() ?? '';
                const node = { type: 'Intro', varName, varType, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'rewrite': {
                const inner = line.content.replace(/^rewrite\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
                const parts = inner.split(',').map(s => s.trim());
                const hyp = parts[0];
                const direction = parts[1] === 'rtl' ? 'rtl' : 'ltr';
                const node = { type: 'Rewrite', hypothesis: hyp, direction, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'exact': {
                const expr = parseCallExpr(line.content, 'exact');
                const node = { type: 'Exact', expr, connective: line.connective };
                pushOrTop(stack, ast, node);
                break;
            }
            case 'obtain': {
                // obtain(varName, ∃ x ∈ S, P(x))
                const inner = line.content.replace(/^obtain\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
                const commaIdx = inner.indexOf(',');
                const varName = commaIdx >= 0 ? inner.slice(0, commaIdx).trim() : inner;
                const source = commaIdx >= 0 ? inner.slice(commaIdx + 1).trim() : '';
                const node = { type: 'Obtain', varName, source, connective: line.connective };
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
        : parseFnGoalExpr(node);
    const theoremBody = node.params.map(param => ({
        type: 'Given',
        expr: (0, expr_1.parseExpr)(`${param.name} ∈ ${param.type}`),
        connective: '→',
    }));
    for (const req of node.requires) {
        theoremBody.push({
            type: 'Given',
            expr: req,
            connective: '→',
        });
    }
    if (node.ensures.length > 0) {
        for (let i = 0; i < node.ensures.length; i++) {
            theoremBody.push({
                type: 'Assert',
                expr: node.ensures[i],
                connective: i === node.ensures.length - 1 ? null : '∧',
            });
        }
    }
    else {
        theoremBody.push({
            type: 'Assert',
            expr: goalExpr,
            connective: null,
        });
    }
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
        fnMeta: {
            params: node.params,
            returnType: normalizeSortName(node.returnType),
        },
    };
    return [theorem, proof];
}
function parseFnGoalExpr(node) {
    const goal = `${node.name}(${node.params.map(param => param.name).join(', ')}) ∈ ${normalizeSortName(node.returnType)}`;
    try {
        return (0, expr_1.parseExpr)(goal);
    }
    catch {
        return {
            type: 'Atom',
            condition: goal,
            atomKind: 'opaque',
        };
    }
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
        const parsedCase = parseMatchCase(lines, cursor);
        cases.push(parsedCase.node);
        cursor = parsedCase.nextIndex;
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
function parseMatchCase(lines, start) {
    const content = lines[start].content;
    const match = content.match(/^case\s+(.+?)\s*=>\s*([\s\S]+)$/);
    const emptyMatch = content.match(/^case\s+(.+?)\s*=>\s*$/);
    if (!match && !emptyMatch) {
        throw new Error(`Malformed case clause: ${content}`);
    }
    const pattern = parsePattern((match ?? emptyMatch)[1].trim());
    const body = [];
    const inlineBody = match?.[2]?.trim() ?? '';
    if (inlineBody) {
        body.push(parseInlineStatement(inlineBody));
    }
    let cursor = start + 1;
    while (cursor < lines.length) {
        const current = lines[cursor];
        if (current.type === 'case' || current.type === 'blockEnd')
            break;
        const parsed = parseNestedStatement(lines, cursor);
        body.push(parsed.node);
        cursor = parsed.nextIndex + 1;
    }
    return {
        node: { pattern, body },
        nextIndex: cursor,
    };
}
function parsePattern(value) {
    if (value === '_') {
        return { kind: 'wildcard' };
    }
    if (value === '[]') {
        return { kind: 'list_nil' };
    }
    const listMatch = value.match(/^\[\s*([^,\]]+)\s*,\s*\.\.\.\s*([A-Za-z_][\w₀-₉ₐ-ₙ]*)\s*\]$/);
    if (listMatch) {
        return {
            kind: 'list_cons',
            head: listMatch[1].trim(),
            tail: listMatch[2].trim(),
        };
    }
    const match = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*\(([\s\S]*)\)\s*$/);
    if (!match) {
        const bare = value.match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)$/);
        if (!bare) {
            throw new Error(`Malformed pattern: ${value}`);
        }
        return { kind: 'variant', constructor: bare[1], bindings: [] };
    }
    const [, constructor, rawBindings] = match;
    const bindings = rawBindings.trim()
        ? splitFnParams(rawBindings).map(binding => binding.trim()).map(binding => binding === '_' ? '_' : binding)
        : [];
    return { kind: 'variant', constructor, bindings };
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
function parseNestedStatement(lines, start) {
    const line = lines[start];
    switch (line.type) {
        case 'assert':
            return { node: { type: 'Assert', expr: parseCallExpr(line.content, 'assert'), connective: line.connective }, nextIndex: start };
        case 'assume':
            return { node: { type: 'Assume', expr: parseCallExpr(line.content, 'assume'), connective: line.connective }, nextIndex: start };
        case 'conclude':
            return { node: { type: 'Conclude', expr: parseCallExpr(line.content, 'conclude'), connective: line.connective }, nextIndex: start };
        case 'apply': {
            const target = line.content.match(/^apply\s*\((.+)\)/)?.[1]?.trim() ?? line.content;
            return { node: { type: 'Apply', target, connective: line.connective }, nextIndex: start };
        }
        case 'setVar':
            return { node: parseSetVar(line.content, line.connective), nextIndex: start };
        case 'intro': {
            const inner = line.content.replace(/^intro\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
            const colonMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*[:\s]\s*(.+)$/);
            const memMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
            const m = colonMatch ?? memMatch;
            const varName = m?.[1] ?? inner;
            const varType = m?.[2]?.trim() ?? '';
            return { node: { type: 'Intro', varName, varType, connective: line.connective }, nextIndex: start };
        }
        case 'rewrite': {
            const inner = line.content.replace(/^rewrite\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
            const parts = inner.split(',').map(s => s.trim());
            const hyp = parts[0];
            const direction = parts[1] === 'rtl' ? 'rtl' : 'ltr';
            return { node: { type: 'Rewrite', hypothesis: hyp, direction, connective: line.connective }, nextIndex: start };
        }
        case 'exact': {
            const expr = parseCallExpr(line.content, 'exact');
            return { node: { type: 'Exact', expr, connective: line.connective }, nextIndex: start };
        }
        case 'match':
            return parseMatch(lines, start);
        case 'raw':
        case 'return':
        case 'level':
            return { node: { type: 'Raw', content: line.content, connective: line.connective }, nextIndex: start };
        default:
            throw new Error(`Unexpected nested statement: ${line.content}`);
    }
}
function validateTopLevelConnectives(ast) {
    for (let i = 0; i < ast.length - 1; i++) {
        const node = ast[i];
        if (isTopLevelBlock(node) && node.connective === null) {
            throw new Error(`Missing connective between top-level blocks after ${describeTopLevelNode(node)}`);
        }
    }
}
// Validate that a theorem/lemma declaration body uses the correct structure:
// - assume() nodes are joined with ∧ (independent hypotheses), not → (which would imply dependency)
// - the last assume() is followed by → to declareToProve()
// - exactly one declareToProve() as the final step
// - no given() or assert() (legacy keywords produce legacyError annotations)
function validateDeclarationBody(name, body) {
    const errors = [];
    for (const node of body) {
        const legacy = node.legacyError;
        if (legacy)
            errors.push(`In '${name}': ${legacy}`);
    }
    const assumes = body.filter(n => n.type === 'Assume');
    const dtp = body.filter(n => n.type === 'DeclareToProve');
    const oldAssert = body.filter(n => n.type === 'Assert');
    const oldGiven = body.filter(n => n.type === 'Given');
    if (oldAssert.length > 0)
        errors.push(`In '${name}': replace assert() with declareToProve() in declarations`);
    if (oldGiven.length > 0)
        errors.push(`In '${name}': replace given() with assume() in declarations`);
    // Only require declareToProve when no legacy assert() is present (backward compat)
    if (dtp.length === 0 && oldAssert.length === 0)
        errors.push(`In '${name}': declaration must end with declareToProve(...)`);
    if (dtp.length > 1)
        errors.push(`In '${name}': declaration must have exactly one declareToProve()`);
    // Validate connectives between assume() nodes and from the last assume() to declareToProve().
    // Hypotheses are always independent of each other — use ∧, not →.
    // Only the final assume() leads to the conclusion — it must use →.
    for (let i = 0; i < assumes.length; i++) {
        const isLast = i === assumes.length - 1;
        const node = assumes[i];
        if (isLast) {
            // Last assume() must connect to declareToProve() via →
            if (node.connective !== '→' && dtp.length > 0)
                errors.push(`In '${name}': assume() before declareToProve() must use → not '${node.connective ?? 'missing'}'`);
        }
        else {
            // Non-last assume() connects to the next assume() — must use ∧ (independent hypotheses)
            if (node.connective === '→')
                errors.push(`In '${name}': assume() followed by another assume() must use ∧, not → (hypotheses are independent)`);
        }
    }
    return errors;
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
