// src/parser/parser.ts
//
// Builds an AST from lexed lines, preserving inter-block connectives.
// The final output is a flat list of top-level nodes each tagged with
// the connective that connects it to the next node — so the whole
// program can be folded into a single logical expression.

import { ParsedLine } from './lexer';
import { normalizeSurfaceSyntax, parseExpr } from './expr';
import {
  ASTNode, BlockConnective,
  TheoremNode, DefinitionNode, StructField, StructNode, TypeDeclNode, TypeVariant, PatternNode, MatchCaseNode, MatchNode, ProofNode, LemmaNode, FnDeclNode, FnParam,
  AssertNode, GivenNode, AssumeNode, ConcludeNode, ApplyNode, SetVarNode, RawNode, InductionNode, FoldNode,
  IntroNode, RewriteNode, ExactNode, ObtainNode,
} from './ast';

type BlockNode = TheoremNode | DefinitionNode | StructNode | TypeDeclNode | ProofNode | LemmaNode | FnDeclNode;

export interface ParserOptions {
  desugarFns?: boolean;
}

export function parseLinesToAST(lines: ParsedLine[], options: ParserOptions = {}): ASTNode[] {
  const ast: ASTNode[] = [];
  const stack: BlockNode[] = [];
  const desugarFns = options.desugarFns ?? true;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    switch (line.type) {

      // ── Block openers ──────────────────────────────────────────────────────
      case 'theorem': {
        const node: TheoremNode = { type: 'Theorem', name: line.name!, body: [], connective: null };
        stack.push(node); break;
      }
      case 'definition': {
        const node: DefinitionNode = { type: 'Definition', name: line.name!, body: [], connective: null };
        stack.push(node); break;
      }
      case 'struct': {
        const node: StructNode = { type: 'Struct', name: line.name!, fields: [], connective: null };
        stack.push(node); break;
      }
      case 'typeDecl': {
        const node: TypeDeclNode = { type: 'TypeDecl', name: line.name!, variants: [], connective: null };
        stack.push(node); break;
      }
      case 'proof': {
        const node: ProofNode = { type: 'Proof', name: line.name!, body: [], connective: null };
        stack.push(node); break;
      }
      case 'lemma': {
        const node: LemmaNode = { type: 'Lemma', name: line.name!, body: [], connective: null };
        stack.push(node); break;
      }
      case 'fn': {
        const signature = parseFnSignature(line.content);
        const node: FnDeclNode = {
          type: 'FnDecl',
          name: signature.name,
          params: signature.params,
          returnType: signature.returnType,
          body: [],
          connective: null,
        };
        stack.push(node); break;
      }

      // ── Block-end: pop, attach connective, push to parent or top-level ─────
      case 'blockEnd': {
        const finished = stack.pop();
        if (!finished) throw new Error('Unmatched }');
        // The connective on the } belongs to this block
        finished.connective = line.connective;

        if (finished.type === 'Struct') {
          finished.fields = (finished.fields as unknown as string[]).map(field => parseStructField(field));
        }
        if (finished.type === 'TypeDecl') {
          finished.variants = (finished.variants as unknown as string[]).map(variant => parseTypeVariant(variant));
        }

        const lowered = finished.type === 'FnDecl' && desugarFns ? desugarFnDecl(finished) : [finished];

        if (stack.length === 0) {
          ast.push(...lowered);
        } else {
          for (const node of lowered) {
            pushToBlock(stack[stack.length - 1], node);
          }
        }
        break;
      }

      // ── Statement nodes ────────────────────────────────────────────────────
      case 'assert': {
        const expr = parseCallExpr(line.content, 'assert');
        const node: AssertNode = { type: 'Assert', expr, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'given': {
        const expr = parseCallExpr(line.content, 'given');
        const node: GivenNode = { type: 'Given', expr, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'assume': {
        const expr = parseCallExpr(line.content, 'assume');
        const node: AssumeNode = { type: 'Assume', expr, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'conclude': {
        const expr = parseCallExpr(line.content, 'conclude');
        const node: ConcludeNode = { type: 'Conclude', expr, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'apply': {
        const node: ApplyNode = { type: 'Apply', target: line.name!, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'intro': {
        const inner = line.content.replace(/^intro\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
        const colonMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*[:\s]\s*(.+)$/);
        const memMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
        const m = colonMatch ?? memMatch;
        const varName = m?.[1] ?? inner;
        const varType = m?.[2]?.trim() ?? '';
        const node: IntroNode = { type: 'Intro', varName, varType, connective: line.connective };
        pushOrTop(stack, ast, node);
        break;
      }
      case 'rewrite': {
        const inner = line.content.replace(/^rewrite\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
        const parts = inner.split(',').map(s => s.trim());
        const hyp = parts[0];
        const direction = parts[1] === 'rtl' ? 'rtl' : 'ltr';
        const node: RewriteNode = { type: 'Rewrite', hypothesis: hyp, direction, connective: line.connective };
        pushOrTop(stack, ast, node);
        break;
      }
      case 'exact': {
        const expr = parseCallExpr(line.content, 'exact');
        const node: ExactNode = { type: 'Exact', expr, connective: line.connective };
        pushOrTop(stack, ast, node);
        break;
      }
      case 'obtain': {
        // obtain(varName, ∃ x ∈ S, P(x))
        const inner = line.content.replace(/^obtain\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
        const commaIdx = inner.indexOf(',');
        const varName = commaIdx >= 0 ? inner.slice(0, commaIdx).trim() : inner;
        const source = commaIdx >= 0 ? inner.slice(commaIdx + 1).trim() : '';
        const node: ObtainNode = { type: 'Obtain', varName, source, connective: line.connective };
        pushOrTop(stack, ast, node);
        break;
      }
      case 'setVar': {
        const node = parseSetVar(line.content, line.connective);
        pushOrTop(stack, ast, node); break;
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
        const node: RawNode = { type: 'Raw', content: line.content, connective: line.connective };
        // Struct fields go into fields[], others go into body
        if (stack.length > 0 && stack[stack.length - 1].type === 'Struct') {
          (stack[stack.length - 1] as unknown as { fields: string[] }).fields.push(line.content);
        } else if (stack.length > 0 && stack[stack.length - 1].type === 'TypeDecl') {
          (stack[stack.length - 1] as unknown as { variants: string[] }).variants.push(line.content);
        } else {
          pushOrTop(stack, ast, node);
        }
        break;
      }
    }
  }

  if (stack.length > 0) throw new Error(`Unclosed block: ${stack[stack.length - 1].type}`);
  validateTopLevelConnectives(ast);
  return ast;
}

// ── Helpers ──────────────────────────────────────────────────────────────────

function pushOrTop(stack: BlockNode[], ast: ASTNode[], node: ASTNode) {
  if (stack.length > 0) {
    pushToBlock(stack[stack.length - 1], node);
  } else {
    ast.push(node);
  }
}

function pushToBlock(block: BlockNode, node: ASTNode) {
  if (block.type === 'Struct' || block.type === 'TypeDecl') {
    // structs don't have a body[] for statement nodes — skip
    return;
  }
  (block as TheoremNode | DefinitionNode | ProofNode | LemmaNode | FnDeclNode).body.push(node);
}

function extractCallBody(content: string, keyword: string): string {
  const m = content.match(new RegExp(`^${keyword}\\s*\\(([\\s\\S]*)\\)\\s*;?\\s*$`));
  if (m) return m[1].trim();
  return content.replace(new RegExp(`^${keyword}\\s*`), '').trim();
}

function parseSetVar(content: string, connective: BlockConnective): SetVarNode {
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

function parseCallExpr(content: string, keyword: string) {
  const body = extractCallBody(content, keyword);
  try {
    return parseExpr(body);
  } catch (error) {
    return {
      type: 'Atom' as const,
      condition: body,
      atomKind: 'opaque' as const,
      parseError: error instanceof Error ? error.message : 'Expression could not be parsed',
    };
  }
}

function parseInduction(lines: ParsedLine[], start: number): { node: InductionNode; nextIndex: number } {
  const line = lines[start];
  const match = line.content.match(/^induction\s*\(([\s\S]+)\)\s*\{$/);
  if (!match) {
    throw new Error('Malformed induction block');
  }
  const iterator = match[1].trim();
  let base: string | null = null;
  let step: string | null = null;
  let connective: BlockConnective = line.connective;
  let cursor = start + 1;

  while (cursor < lines.length) {
    const current = lines[cursor];
    if (current.type === 'blockEnd') {
      connective = current.connective;
      break;
    }
    if (current.type === 'base') {
      base = current.content.replace(/^base\s*:\s*/, '').trim();
    } else if (current.type === 'step') {
      step = current.content.replace(/^step\s*:\s*/, '').trim();
    } else {
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

  const fold: FoldNode = {
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

function parseFnSignature(content: string): { name: string; params: FnParam[]; returnType: string } {
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

function splitFnParams(value: string): string[] {
  const params: string[] = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth = Math.max(0, depth - 1);
    else if (ch === ',' && depth === 0) {
      params.push(value.slice(start, i).trim());
      start = i + 1;
    }
  }
  const final = value.slice(start).trim();
  if (final) params.push(final);
  return params;
}

function parseFnParam(value: string): FnParam {
  const match = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
  if (!match) {
    throw new Error(`Malformed fn parameter: ${value}`);
  }
  return { name: match[1], type: normalizeSortName(match[2]) };
}

function parseStructField(value: string): StructField {
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

function parseTypeVariant(value: string): TypeVariant {
  const trimmed = value.trim().replace(/,+$/, '').trim();
  const match = trimmed.match(/^\|\s*(\w[\w₀-₉ₐ-ₙ]*)\s*\(([\s\S]*)\)\s*$/);
  if (!match) {
    throw new Error(`Malformed type variant: ${value}`);
  }
  const [, name, rawFields] = match;
  const fields = rawFields.trim() ? splitFnParams(rawFields).map(parseStructField) : [];
  return { name, fields };
}

function desugarFnDecl(node: FnDeclNode): [TheoremNode, ProofNode] {
  const conclusion = findFnConclusion(node.body);
  const matchBody = findTopLevelMatch(node.body);
  if (!conclusion && !matchBody) {
    throw new Error(`fn '${node.name}' requires a conclude(...) statement`);
  }

  const goalExpr = conclusion
    ? conclusion.expr
    : parseFnGoalExpr(node);

  const theoremBody: ASTNode[] = node.params.map(param => ({
    type: 'Given' as const,
    expr: parseExpr(`${param.name} ∈ ${param.type}`),
    connective: '→' as const,
  }));
  theoremBody.push({
    type: 'Assert' as const,
    expr: goalExpr,
    connective: null,
  });

  const theorem: TheoremNode = {
    type: 'Theorem',
    name: node.name,
    body: theoremBody,
    connective: '↔',
  };

  const proofBody: ASTNode[] = conclusion
    ? [
      {
        type: 'Assume',
        expr: conclusion.expr,
        connective: node.body.length > 0 ? '→' : null,
      },
      ...node.body,
    ]
    : node.body;

  const proof: ProofNode = {
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

function parseFnGoalExpr(node: FnDeclNode) {
  const goal = `${node.name}(${node.params.map(param => param.name).join(', ')}) ∈ ${normalizeSortName(node.returnType)}`;
  try {
    return parseExpr(goal);
  } catch {
    return {
      type: 'Atom' as const,
      condition: goal,
      atomKind: 'opaque' as const,
    };
  }
}

function normalizeSortName(value: string): string {
  return normalizeSurfaceSyntax(value).trim();
}

function findFnConclusion(body: ASTNode[]): ConcludeNode | null {
  for (let i = body.length - 1; i >= 0; i--) {
    const node = body[i];
    if (node.type === 'Conclude') {
      return node;
    }
  }
  return null;
}

function findTopLevelMatch(body: ASTNode[]): MatchNode | null {
  for (const node of body) {
    if (node.type === 'Match') return node;
  }
  return null;
}

function parseMatch(lines: ParsedLine[], start: number): { node: MatchNode; nextIndex: number } {
  const line = lines[start];
  const match = line.content.match(/^match\s+([\s\S]+)\s*\{$/);
  if (!match) {
    throw new Error('Malformed match block');
  }
  const scrutinee = parseExpr(match[1].trim());
  const cases: MatchCaseNode[] = [];
  let connective: BlockConnective = line.connective;
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

function parseMatchCase(lines: ParsedLine[], start: number): { node: MatchCaseNode; nextIndex: number } {
  const content = lines[start].content;
  const match = content.match(/^case\s+(.+?)\s*=>\s*([\s\S]+)$/);
  const emptyMatch = content.match(/^case\s+(.+?)\s*=>\s*$/);
  if (!match && !emptyMatch) {
    throw new Error(`Malformed case clause: ${content}`);
  }
  const pattern = parsePattern((match ?? emptyMatch)![1].trim());
  const body: ASTNode[] = [];
  const inlineBody = match?.[2]?.trim() ?? '';
  if (inlineBody) {
    body.push(parseInlineStatement(inlineBody));
  }

  let cursor = start + 1;
  while (cursor < lines.length) {
    const current = lines[cursor];
    if (current.type === 'case' || current.type === 'blockEnd') break;
    const parsed = parseNestedStatement(lines, cursor);
    body.push(parsed.node);
    cursor = parsed.nextIndex + 1;
  }

  return {
    node: { pattern, body },
    nextIndex: cursor,
  };
}

function parsePattern(value: string): PatternNode {
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

function parseInlineStatement(content: string): ASTNode {
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

function parseNestedStatement(lines: ParsedLine[], start: number): { node: ASTNode; nextIndex: number } {
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
      return { node: { type: 'Intro', varName, varType, connective: line.connective } as IntroNode, nextIndex: start };
    }
    case 'rewrite': {
      const inner = line.content.replace(/^rewrite\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
      const parts = inner.split(',').map(s => s.trim());
      const hyp = parts[0];
      const direction = parts[1] === 'rtl' ? 'rtl' : 'ltr';
      return { node: { type: 'Rewrite', hypothesis: hyp, direction, connective: line.connective } as RewriteNode, nextIndex: start };
    }
    case 'exact': {
      const expr = parseCallExpr(line.content, 'exact');
      return { node: { type: 'Exact', expr, connective: line.connective } as ExactNode, nextIndex: start };
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

function validateTopLevelConnectives(ast: ASTNode[]) {
  for (let i = 0; i < ast.length - 1; i++) {
    const node = ast[i];
    if (isTopLevelBlock(node) && node.connective === null) {
      throw new Error(`Missing connective between top-level blocks after ${describeTopLevelNode(node)}`);
    }
  }
}

function isTopLevelBlock(node: ASTNode): node is BlockNode {
  return node.type === 'Theorem' ||
    node.type === 'Definition' ||
    node.type === 'Struct' ||
    node.type === 'TypeDecl' ||
    node.type === 'Proof' ||
    node.type === 'Lemma' ||
    node.type === 'FnDecl';
}

function describeTopLevelNode(node: BlockNode): string {
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
