"use strict";
// src/codegen/index.ts
Object.defineProperty(exports, "__esModule", { value: true });
exports.generateJSFromAST = generateJSFromAST;
const typecheck_1 = require("./typecheck");
const expr_1 = require("../parser/expr");
function generateJSFromAST(nodes, runtime) {
    (0, typecheck_1.typecheckExecutableProgram)(nodes);
    let code = runtime + '\n';
    const ctx = buildCodegenContext(nodes);
    const expr = foldNodes(nodes, ctx);
    code += `\n// ── Evaluate program as single logical expression ──\n`;
    code += `const _result = ${expr};\n`;
    code += `if (!_resolve(_result)) throw new Error('Program does not hold: ' + _describe(_result));\n`;
    code += `console.log('\\n✓ Program holds: ' + _describe(_result));\n`;
    return code;
}
function buildCodegenContext(nodes) {
    const variants = new Map();
    for (const node of nodes) {
        if (node.type !== 'TypeDecl')
            continue;
        for (const variant of node.variants) {
            variants.set(variant.name, {
                typeName: node.name,
                fieldNames: variant.fields.map(field => field.name),
            });
        }
    }
    return { variants };
}
function foldNodes(nodes, ctx) {
    return foldNodesWithMode(nodes, false, ctx);
}
function foldNodesWithMode(nodes, symbolicMode, ctx) {
    const meaningful = nodes.filter(n => !(n.type === 'Raw' && n.content.trim().length === 0));
    if (meaningful.length === 0)
        return 'atom(true, "∅")';
    let acc = nodeToExpr(meaningful[meaningful.length - 1], symbolicMode, ctx);
    for (let i = meaningful.length - 2; i >= 0; i--) {
        const node = meaningful[i];
        const conn = node.connective ?? '→';
        const left = nodeToExpr(node, symbolicMode, ctx);
        acc = applyConnective(conn, left, acc);
    }
    return acc;
}
function applyConnective(conn, left, right) {
    switch (conn) {
        case '→': return `seq(()=>${left}, ()=>${right})`;
        case '∧': return `and(${left}, ${right})`;
        case '↔': return `iff(${left}, ${right})`;
        default: return `seq(()=>${left}, ()=>${right})`;
    }
}
function nodeToExpr(node, symbolicMode, ctx) {
    switch (node.type) {
        case 'Theorem': return generateTheorem(node, ctx);
        case 'Proof': return generateProof(node, ctx);
        case 'Lemma': return generateLemma(node, ctx);
        case 'Definition': return generateDefinition(node, ctx);
        case 'Struct': return generateStruct(node);
        case 'TypeDecl': return generateTypeDecl(node);
        case 'FnDecl': return generateFnDecl(node, ctx);
        case 'Assert':
            return symbolicMode
                ? `assertExpr(atom(true, ${JSON.stringify(renderExprSource(node.expr))}))`
                : `assertExpr(atom(() => !!(${generateRuntimeExpr(node.expr)}), ${JSON.stringify(renderExprSource(node.expr))}))`;
        case 'Given': return `assumeExpr(${JSON.stringify(renderExprSource(node.expr))})`;
        case 'Assume': return `assumeExpr(${JSON.stringify(renderExprSource(node.expr))})`;
        case 'Conclude':
            return symbolicMode
                ? `concludeExpr(atom(true, ${JSON.stringify(renderExprSource(node.expr))}))`
                : `concludeExpr(atom(() => ${generateRuntimeExpr(node.expr)}, ${JSON.stringify(renderExprSource(node.expr))}))`;
        case 'Apply': return `applyLemma(${JSON.stringify(node.target)})`;
        case 'SetVar': return generateSetVar(node);
        case 'Induction':
            return symbolicMode
                ? `atom(true, ${JSON.stringify(renderExprSource(node.fold))})`
                : `unsupportedExpr(${JSON.stringify(renderExprSource(node.fold))}, "Iteration is kernel-only in FuturLang. Use 'fl check' for induction.")`;
        case 'Match':
            return symbolicMode
                ? `atom(true, ${JSON.stringify(`match ${renderExprSource(node.scrutinee)}`)})`
                : `execExpr(() => { ${generateMatchStatement(node, ctx, true)} }, "match")`;
        case 'Raw':
            return symbolicMode
                ? `atom(true, ${JSON.stringify(node.content)})`
                : `execExpr(() => { ${generateRawNode(node)} }, ${JSON.stringify(node.content)})`;
        case 'Intro':
            return `assumeExpr(${JSON.stringify(`${node.varName} ∈ ${node.varType}`)})`;
        case 'Rewrite':
            return `atom(true, ${JSON.stringify(`rewrite(${node.hypothesis})`)})`;
        case 'Exact':
            return symbolicMode
                ? `concludeExpr(atom(true, ${JSON.stringify(renderExprSource(node.expr))}))`
                : `concludeExpr(atom(() => !!(${generateRuntimeExpr(node.expr)}), ${JSON.stringify(renderExprSource(node.expr))}))`;
        case 'Obtain':
            return `atom(true, ${JSON.stringify(`obtain(${node.varName})`)})`;
        default: {
            const _ = node;
            throw new Error('Unhandled node type');
        }
    }
}
function generateTheorem(node, ctx) {
    const inner = foldNodesWithMode(node.body, true, ctx);
    return `theorem(${JSON.stringify(node.name)}, () => ${inner})`;
}
function generateProof(node, ctx) {
    const inner = foldNodesWithMode(node.body, true, ctx);
    return `proof(${JSON.stringify(node.name)}, () => ${inner})`;
}
function generateLemma(node, ctx) {
    const inner = foldNodesWithMode(node.body, true, ctx);
    return `lemma(${JSON.stringify(node.name)}, () => ${inner})`;
}
function generateDefinition(node, ctx) {
    const inner = node.body.length > 0 ? foldNodes(node.body, ctx) : 'atom(true, "defined")';
    return `definition(${JSON.stringify(node.name)}, () => ${inner})`;
}
function generateStruct(node) {
    return `struct_(${JSON.stringify(node.name)}, ${JSON.stringify(node.fields)})`;
}
function generateTypeDecl(node) {
    const meta = Object.fromEntries(node.variants.map(variant => [variant.name, variant.fields.map(field => field.name)]));
    return `defineType(${JSON.stringify(node.name)}, ${JSON.stringify(meta)})`;
}
function generateFnDecl(node, ctx) {
    const params = node.params.map(param => param.name).join(', ');
    const body = generateExecutableStatements(node.body, ctx);
    const meta = {
        params: node.params,
        returnType: node.returnType,
    };
    return `defineFn(${JSON.stringify(node.name)}, function ${node.name}(${params}) {\n${indent(body, 1)}\n}, ${JSON.stringify(meta)})`;
}
function generateSetVar(node) {
    const label = node.varType ? `${node.varName}: ${node.varType}` : node.varName;
    if (node.value !== null) {
        return `setVar(${JSON.stringify(node.varName)}, () => (${compileSetVarValue(node.value)}), ${JSON.stringify(label)})`;
    }
    return `setVar(${JSON.stringify(node.varName)}, () => undefined, ${JSON.stringify(label)})`;
}
function generateExecutableStatements(nodes, ctx) {
    const lines = [];
    for (const node of nodes) {
        lines.push(generateExecutableNode(node, ctx));
    }
    return lines.join('\n');
}
function generateExecutableNode(node, ctx) {
    switch (node.type) {
        case 'SetVar':
            return `let ${node.varName} = ${node.value === null ? 'undefined' : compileSetVarValue(node.value)};`;
        case 'Assert':
            return `_runtimeAssert(${generateRuntimeExpr(node.expr)}, ${JSON.stringify(renderExprSource(node.expr))});`;
        case 'Conclude':
            return `return ${generateRuntimeExpr(node.expr)};`;
        case 'Match':
            return generateMatchStatement(node, ctx, false);
        case 'Raw':
            return generateRawNode(node);
        case 'Assume':
        case 'Given':
            return `/* assumption: ${renderExprSource(node.expr)} */`;
        case 'Apply':
            return `applyLemma(${JSON.stringify(node.target)});`;
        default:
            return `throw new Error(${JSON.stringify(`Unsupported executable statement: ${node.type}`)});`;
    }
}
function generateMatchStatement(node, ctx, asExpression) {
    const scrutineeVar = `_match_${Math.random().toString(36).slice(2, 8)}`;
    const lines = [`const ${scrutineeVar} = ${generateRuntimeExpr(node.scrutinee)};`];
    node.cases.forEach((matchCase, index) => {
        const condition = patternCondition(matchCase.pattern, scrutineeVar);
        const prefix = index === 0 ? 'if' : 'else if';
        lines.push(`${prefix} (${condition}) {`);
        const bindings = patternBindings(matchCase.pattern, scrutineeVar, ctx);
        if (bindings)
            lines.push(indent(bindings, 1));
        const branch = generateExecutableStatements(matchCase.body, ctx);
        lines.push(indent(branch, 1));
        lines.push('}');
    });
    lines.push('else { throw new Error("Non-exhaustive match"); }');
    if (asExpression)
        lines.push('return true;');
    return lines.join('\n');
}
function patternCondition(pattern, target) {
    switch (pattern.kind) {
        case 'wildcard':
            return 'true';
        case 'list_nil':
            return `Array.isArray(${target}) && ${target}.length === 0`;
        case 'list_cons':
            return `Array.isArray(${target}) && ${target}.length > 0`;
        case 'variant':
            if (pattern.constructor === 'true' || pattern.constructor === 'false') {
                return `${target} === ${pattern.constructor}`;
            }
            return `${target} && ${target}.tag === ${JSON.stringify(pattern.constructor)}`;
    }
}
function patternBindings(pattern, target, ctx) {
    switch (pattern.kind) {
        case 'wildcard':
        case 'list_nil':
            return '';
        case 'list_cons':
            return [
                pattern.head !== '_' ? `const ${pattern.head} = ${target}[0];` : '',
                `const ${pattern.tail} = ${target}.slice(1);`,
            ].filter(Boolean).join('\n');
        case 'variant': {
            const info = ctx.variants.get(pattern.constructor);
            if (!info)
                return '';
            const lines = [];
            pattern.bindings.forEach((binding, index) => {
                if (!binding || binding === '_')
                    return;
                const fieldName = info.fieldNames[index];
                if (!fieldName)
                    return;
                lines.push(`const ${binding} = ${target}[${JSON.stringify(fieldName)}];`);
            });
            return lines.join('\n');
        }
    }
}
function generateRawNode(node) {
    const trimmed = node.content.trim();
    if (trimmed.startsWith('return '))
        return trimmed.endsWith(';') ? trimmed : `${trimmed};`;
    if (trimmed === 'return')
        return 'return;';
    return trimmed.endsWith(';') ? trimmed : `${trimmed};`;
}
function generateRuntimeExpr(node) {
    switch (node.type) {
        case 'Atom':
            return generateRuntimeExprFromString(node.condition);
        case 'And':
            return `(${generateRuntimeExpr(node.left)} && ${generateRuntimeExpr(node.right)})`;
        case 'Or':
            return `(${generateRuntimeExpr(node.left)} || ${generateRuntimeExpr(node.right)})`;
        case 'Implies':
            return `((!(${generateRuntimeExpr(node.left)})) || (${generateRuntimeExpr(node.right)}))`;
        case 'Iff':
            return `((${generateRuntimeExpr(node.left)}) === (${generateRuntimeExpr(node.right)}))`;
        case 'Not':
            return `(!(${generateRuntimeExpr(node.operand)}))`;
        case 'If':
            return `((${generateRuntimeExpr(node.condition)}) ? (${generateRuntimeExpr(node.thenBranch)}) : (${generateRuntimeExpr(node.elseBranch)}))`;
        case 'LetExpr':
            return `(() => { const ${node.name} = ${generateRuntimeExpr(node.value)}; return ${generateRuntimeExpr(node.body)}; })()`;
        case 'Lambda':
            return `((${node.params.map(param => param.name).join(', ')}) => ${generateRuntimeExpr(node.body)})`;
        case 'Fold':
            return `_fold(${compileSetVarValue(node.sequence)}, ${compileSetVarValue(node.init)}, ${compileSetVarValue(node.fn)})`;
        case 'Quantified':
        case 'SetBuilder':
        case 'IndexedUnion':
            return `unsupportedExpr(${JSON.stringify(renderExprSource(node))}, "Unsupported expression in executable mode")`;
        default: {
            const _ = node;
            throw new Error('Unhandled expr node type');
        }
    }
}
function generateRuntimeExprFromString(value) {
    const trimmed = value.trim();
    if (!trimmed)
        return 'undefined';
    return normalizeJsEquality(trimmed);
}
function compileSetVarValue(value) {
    try {
        return generateRuntimeExpr((0, expr_1.parseExpr)(value));
    }
    catch {
        return generateRuntimeExprFromString(value);
    }
}
function normalizeJsEquality(value) {
    let result = '';
    let inString = false;
    let quote = '';
    for (let index = 0; index < value.length; index++) {
        const ch = value[index];
        if (inString) {
            result += ch;
            if (ch === quote && value[index - 1] !== '\\') {
                inString = false;
                quote = '';
            }
            continue;
        }
        if (ch === '"' || ch === "'") {
            inString = true;
            quote = ch;
            result += ch;
            continue;
        }
        if (ch === '≥') {
            result += '>=';
            continue;
        }
        if (ch === '≤') {
            result += '<=';
            continue;
        }
        if (ch === '≠') {
            result += '!=';
            continue;
        }
        if (ch === '=' &&
            value[index - 1] !== '=' &&
            value[index - 1] !== '!' &&
            value[index - 1] !== '<' &&
            value[index - 1] !== '>' &&
            value[index + 1] !== '=') {
            result += '==';
            continue;
        }
        result += ch;
    }
    return result;
}
function renderExprSource(node) {
    switch (node.type) {
        case 'Atom':
            return node.condition;
        case 'SetBuilder':
            return `{${node.element} | ${node.variable} ∈ ${node.domain}}`;
        case 'IndexedUnion':
            return `∪${renderExprSource(node.builder)}`;
        case 'And':
            return `(${renderExprSource(node.left)} ∧ ${renderExprSource(node.right)})`;
        case 'Or':
            return `(${renderExprSource(node.left)} ∨ ${renderExprSource(node.right)})`;
        case 'Implies':
            return `(${renderExprSource(node.left)} → ${renderExprSource(node.right)})`;
        case 'Iff':
            return `(${renderExprSource(node.left)} ↔ ${renderExprSource(node.right)})`;
        case 'Not':
            return `¬${renderExprSource(node.operand)}`;
        case 'If':
            return `if ${renderExprSource(node.condition)} then ${renderExprSource(node.thenBranch)} else ${renderExprSource(node.elseBranch)}`;
        case 'LetExpr':
            return `let ${node.name} = ${renderExprSource(node.value)} in ${renderExprSource(node.body)}`;
        case 'Lambda':
            return `fn(${node.params.map(param => `${param.name}: ${param.type}`).join(', ')}) => ${renderExprSource(node.body)}`;
        case 'Quantified': {
            const symbol = node.quantifier === 'forall' ? '∀' : node.quantifier === 'exists' ? '∃' : '∃!';
            const binder = node.binderStyle === 'bounded'
                ? `${node.variable} ∈ ${node.domain}`
                : `${node.variable}: ${node.domain}`;
            return node.body ? `${symbol} ${binder}, ${renderExprSource(node.body)}` : `${symbol} ${binder}`;
        }
        case 'Fold':
            return `fold(${node.sequence}, ${node.init}, ${node.fn})`;
        default: {
            const _ = node;
            throw new Error('Unhandled expr node type');
        }
    }
}
function blockUsesSymbolicProofMode(nodes) {
    return nodes.some(node => node.type === 'Given' ||
        node.type === 'Assume' ||
        node.type === 'Apply' ||
        node.type === 'Induction');
}
function indent(value, depth) {
    const prefix = '  '.repeat(depth);
    return value.split('\n').map(line => line.length > 0 ? `${prefix}${line}` : line).join('\n');
}
