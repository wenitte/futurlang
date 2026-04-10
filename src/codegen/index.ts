// src/codegen/index.ts

import {
  ASTNode, BlockConnective,
  TheoremNode, DefinitionNode, StructNode, TypeDeclNode, ProofNode, LemmaNode,
  AssertNode, GivenNode, AssumeNode, ConcludeNode, ApplyNode, SetVarNode, RawNode, InductionNode, FnDeclNode, MatchNode,
  ExprNode, AtomNode, MatchCaseNode, PatternNode,
} from '../parser/ast';
import { typecheckExecutableProgram } from './typecheck';
import { parseExpr } from '../parser/expr';

interface VariantInfo {
  typeName: string;
  fieldNames: string[];
}

interface CodegenContext {
  variants: Map<string, VariantInfo>;
}

export function generateJSFromAST(nodes: ASTNode[], runtime: string): string {
  typecheckExecutableProgram(nodes);

  let code = runtime + '\n';
  const ctx = buildCodegenContext(nodes);

  const expr = foldNodes(nodes, ctx);
  code += `\n// ── Evaluate program as single logical expression ──\n`;
  code += `const _result = ${expr};\n`;
  code += `if (!_resolve(_result)) throw new Error('Program does not hold: ' + _describe(_result));\n`;
  code += `console.log('\\n✓ Program holds: ' + _describe(_result));\n`;

  return code;
}

function buildCodegenContext(nodes: ASTNode[]): CodegenContext {
  const variants = new Map<string, VariantInfo>();
  for (const node of nodes) {
    if (node.type !== 'TypeDecl') continue;
    for (const variant of node.variants) {
      variants.set(variant.name, {
        typeName: node.name,
        fieldNames: variant.fields.map(field => field.name),
      });
    }
  }
  return { variants };
}

function foldNodes(nodes: ASTNode[], ctx: CodegenContext): string {
  return foldNodesWithMode(nodes, false, ctx);
}

function foldNodesWithMode(nodes: ASTNode[], symbolicMode: boolean, ctx: CodegenContext): string {
  const meaningful = nodes.filter(n =>
    !(n.type === 'Raw' && (n as RawNode).content.trim().length === 0)
  );
  if (meaningful.length === 0) return 'atom(true, "∅")';

  let acc = nodeToExpr(meaningful[meaningful.length - 1], symbolicMode, ctx);
  for (let i = meaningful.length - 2; i >= 0; i--) {
    const node = meaningful[i];
    const conn = node.connective ?? '→';
    const left = nodeToExpr(node, symbolicMode, ctx);
    acc = applyConnective(conn, left, acc);
  }
  return acc;
}

function applyConnective(conn: BlockConnective, left: string, right: string): string {
  switch (conn) {
    case '→': return `seq(()=>${left}, ()=>${right})`;
    case '∧': return `and(${left}, ${right})`;
    case '↔': return `iff(${left}, ${right})`;
    default: return `seq(()=>${left}, ()=>${right})`;
  }
}

function nodeToExpr(node: ASTNode, symbolicMode: boolean, ctx: CodegenContext): string {
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
      const _: never = node;
      throw new Error('Unhandled node type');
    }
  }
}

function generateTheorem(node: TheoremNode, ctx: CodegenContext): string {
  const inner = foldNodesWithMode(node.body, true, ctx);
  return `theorem(${JSON.stringify(node.name)}, () => ${inner})`;
}

function generateProof(node: ProofNode, ctx: CodegenContext): string {
  const inner = foldNodesWithMode(node.body, true, ctx);
  return `proof(${JSON.stringify(node.name)}, () => ${inner})`;
}

function generateLemma(node: LemmaNode, ctx: CodegenContext): string {
  const inner = foldNodesWithMode(node.body, true, ctx);
  return `lemma(${JSON.stringify(node.name)}, () => ${inner})`;
}

function generateDefinition(node: DefinitionNode, ctx: CodegenContext): string {
  const inner = node.body.length > 0 ? foldNodes(node.body, ctx) : 'atom(true, "defined")';
  return `definition(${JSON.stringify(node.name)}, () => ${inner})`;
}

function generateStruct(node: StructNode): string {
  return `struct_(${JSON.stringify(node.name)}, ${JSON.stringify(node.fields)})`;
}

function generateTypeDecl(node: TypeDeclNode): string {
  const meta = Object.fromEntries(node.variants.map(variant => [variant.name, variant.fields.map(field => field.name)]));
  return `defineType(${JSON.stringify(node.name)}, ${JSON.stringify(meta)})`;
}

function generateFnDecl(node: FnDeclNode, ctx: CodegenContext): string {
  const params = node.params.map(param => param.name).join(', ');
  const body = generateExecutableStatements(node.body, ctx);
  const meta = {
    params: node.params,
    returnType: node.returnType,
  };
  return `defineFn(${JSON.stringify(node.name)}, function ${node.name}(${params}) {\n${indent(body, 1)}\n}, ${JSON.stringify(meta)})`;
}

function generateSetVar(node: SetVarNode): string {
  const label = node.varType ? `${node.varName}: ${node.varType}` : node.varName;
  if (node.value !== null) {
    return `setVar(${JSON.stringify(node.varName)}, () => (${compileSetVarValue(node.value)}), ${JSON.stringify(label)})`;
  }
  return `setVar(${JSON.stringify(node.varName)}, () => undefined, ${JSON.stringify(label)})`;
}

function generateExecutableStatements(nodes: ASTNode[], ctx: CodegenContext): string {
  const lines: string[] = [];
  for (const node of nodes) {
    lines.push(generateExecutableNode(node, ctx));
  }
  return lines.join('\n');
}

function generateExecutableNode(node: ASTNode, ctx: CodegenContext): string {
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

function generateMatchStatement(node: MatchNode, ctx: CodegenContext, asExpression: boolean): string {
  const scrutineeVar = `_match_${Math.random().toString(36).slice(2, 8)}`;
  const lines: string[] = [`const ${scrutineeVar} = ${generateRuntimeExpr(node.scrutinee)};`];

  node.cases.forEach((matchCase, index) => {
    const condition = patternCondition(matchCase.pattern, scrutineeVar);
    const prefix = index === 0 ? 'if' : 'else if';
    lines.push(`${prefix} (${condition}) {`);
    const bindings = patternBindings(matchCase.pattern, scrutineeVar, ctx);
    if (bindings) lines.push(indent(bindings, 1));
    const branch = generateExecutableStatements(matchCase.body, ctx);
    lines.push(indent(branch, 1));
    lines.push('}');
  });

  lines.push('else { throw new Error("Non-exhaustive match"); }');
  if (asExpression) lines.push('return true;');
  return lines.join('\n');
}

function patternCondition(pattern: PatternNode, target: string): string {
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

function patternBindings(pattern: PatternNode, target: string, ctx: CodegenContext): string {
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
      if (!info) return '';
      const lines: string[] = [];
      pattern.bindings.forEach((binding, index) => {
        if (!binding || binding === '_') return;
        const fieldName = info.fieldNames[index];
        if (!fieldName) return;
        lines.push(`const ${binding} = ${target}[${JSON.stringify(fieldName)}];`);
      });
      return lines.join('\n');
    }
  }
}

function generateRawNode(node: RawNode): string {
  const trimmed = node.content.trim();
  if (trimmed.startsWith('return ')) return trimmed.endsWith(';') ? trimmed : `${trimmed};`;
  if (trimmed === 'return') return 'return;';
  return trimmed.endsWith(';') ? trimmed : `${trimmed};`;
}

function generateRuntimeExpr(node: ExprNode): string {
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
      const _: never = node;
      throw new Error('Unhandled expr node type');
    }
  }
}

function generateRuntimeExprFromString(value: string): string {
  const trimmed = value.trim();
  if (!trimmed) return 'undefined';
  return normalizeJsEquality(trimmed);
}

function compileSetVarValue(value: string): string {
  try {
    return generateRuntimeExpr(parseExpr(value));
  } catch {
    return generateRuntimeExprFromString(value);
  }
}

function normalizeJsEquality(value: string): string {
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
    if (
      ch === '=' &&
      value[index - 1] !== '=' &&
      value[index - 1] !== '!' &&
      value[index - 1] !== '<' &&
      value[index - 1] !== '>' &&
      value[index + 1] !== '='
    ) {
      result += '==';
      continue;
    }
    result += ch;
  }
  return result;
}

function renderExprSource(node: ExprNode): string {
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
      const _: never = node;
      throw new Error('Unhandled expr node type');
    }
  }
}

function blockUsesSymbolicProofMode(nodes: ASTNode[]): boolean {
  return nodes.some(node =>
    node.type === 'Given' ||
    node.type === 'Assume' ||
    node.type === 'Apply' ||
    node.type === 'Induction'
  );
}

function indent(value: string, depth: number): string {
  const prefix = '  '.repeat(depth);
  return value.split('\n').map(line => line.length > 0 ? `${prefix}${line}` : line).join('\n');
}
