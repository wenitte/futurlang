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
  AxiomNode, TheoremNode, DefinitionNode, StructField, StructNode, TypeDeclNode, TypeVariant, PatternNode, MatchCaseNode, MatchNode, ProofNode, LemmaNode, FnDeclNode, FnParam,
  AssertNode, DeclareToProveNode, ProveNode, DeriveNode, AndIntroStepNode, OrIntroStepNode,
  GivenNode, AssumeNode, ConcludeNode, ApplyNode, SetVarNode, RawNode, InductionNode, FoldNode,
  IntroNode, RewriteNode, ExactNode, ObtainNode,
  AccountNode, InstructionNode, InstructionParam, AccountQualifier, ErrorDeclNode, ErrorVariant, ProgramNode, RequireNode,
  EmitNode, PdaNode, CpiNode, TransferNode,
} from './ast';

type BlockNode = TheoremNode | DefinitionNode | StructNode | TypeDeclNode | ProofNode | LemmaNode | FnDeclNode
  | AccountNode | InstructionNode | ErrorDeclNode | ProgramNode;

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
      case 'axiom': {
        // Axioms are single-line — emit immediately, no body
        const node: AxiomNode = { type: 'Axiom', name: line.name!, statement: line.content, connective: line.connective };
        ast.push(node);
        break;
      }
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
          requires: [],
          ensures: [],
          body: [],
          isNative: line.isNative ?? false,
          connective: line.connective,
        };
        if (line.isNative) {
          // Native fns have no body — emit immediately
          ast.push(node);
        } else {
          stack.push(node);
        }
        break;
      }
      case 'program': {
        const node: ProgramNode = {
          type: 'Program',
          name: line.name!,
          programId: '11111111111111111111111111111111',
          body: [],
          connective: null,
        };
        stack.push(node); break;
      }
      case 'account': {
        const node: AccountNode = { type: 'Account', name: line.name!, fields: [], connective: null };
        stack.push(node); break;
      }
      case 'instruction': {
        const sig = parseInstructionSignature(line.content);
        const node: InstructionNode = {
          type: 'Instruction',
          name: sig.name,
          params: sig.params,
          body: [],
          connective: null,
        };
        stack.push(node); break;
      }
      case 'errorDecl': {
        const node: ErrorDeclNode = { type: 'ErrorDecl', name: line.name!, variants: [], connective: null };
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
        if (finished.type === 'Account') {
          finished.fields = (finished.fields as unknown as string[]).map(field => parseStructField(field));
        }
        if (finished.type === 'ErrorDecl') {
          finished.variants = (finished.variants as unknown as string[]).map(raw => parseErrorVariant(raw));
        }

        const lowered = finished.type === 'FnDecl' && desugarFns && !finished.isNative
          ? desugarFnDecl(finished)
          : [finished];

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
        // Legacy keyword — kept for backward compatibility but emits a parse error node
        const currentBlock = stack[stack.length - 1];
        const inDecl = currentBlock?.type === 'Theorem' || currentBlock?.type === 'Lemma';
        const suggestion = inDecl
          ? 'Use declareToProve() to declare the theorem goal'
          : 'Use prove() for intermediate steps or conclude() for the final step';
        const errExpr = parseCallExpr(line.content, 'assert');
        const node: AssertNode = { type: 'Assert', expr: errExpr, connective: line.connective };
        // Store the migration hint as a parse error on the atom
        (node as AssertNode & { legacyError?: string }).legacyError = `assert() is no longer valid. ${suggestion}`;
        pushOrTop(stack, ast, node); break;
      }
      case 'given': {
        // Legacy keyword — emit error
        const errExpr = parseCallExpr(line.content, 'given');
        const node: GivenNode = { type: 'Given', expr: errExpr, connective: line.connective };
        (node as GivenNode & { legacyError?: string }).legacyError = 'given() is no longer valid. Use assume() to declare hypotheses';
        pushOrTop(stack, ast, node); break;
      }
      case 'declareToProve': {
        const expr = parseCallExpr(line.content, 'declareToProve');
        const node: DeclareToProveNode = { type: 'DeclareToProve', expr, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'prove': {
        const expr = parseCallExpr(line.content, 'prove');
        const node: ProveNode = { type: 'Prove', expr, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'derive': {
        const node: DeriveNode = { type: 'Derive', connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'andIntroStep': {
        // AndIntro(P, Q) — parse two comma-separated claims
        const inner = line.content.replace(/^AndIntro\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
        const commaIdx = inner.lastIndexOf(',');
        const left = commaIdx >= 0 ? inner.slice(0, commaIdx).trim() : inner;
        const right = commaIdx >= 0 ? inner.slice(commaIdx + 1).trim() : '';
        const node: AndIntroStepNode = { type: 'AndIntroStep', left, right, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'orIntroStep': {
        // OrIntro(P ∨ Q) — the full disjunction to introduce
        const claim = line.content.replace(/^OrIntro\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
        const node: OrIntroStepNode = { type: 'OrIntroStep', claim, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'requires': {
        const expr = parseCallExpr(line.content, 'requires');
        if (stack.length > 0 && stack[stack.length - 1].type === 'FnDecl') {
          (stack[stack.length - 1] as FnDeclNode).requires.push(expr);
        } else {
          throw new Error('requires() may only appear inside fn blocks');
        }
        break;
      }
      case 'ensures': {
        const expr = parseCallExpr(line.content, 'ensures');
        if (stack.length > 0 && stack[stack.length - 1].type === 'FnDecl') {
          (stack[stack.length - 1] as FnDeclNode).ensures.push(expr);
        } else {
          throw new Error('ensures() may only appear inside fn blocks');
        }
        break;
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
      case 'require': {
        const inner = line.content.replace(/^require\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
        const lastComma = inner.lastIndexOf(',');
        const condStr = lastComma >= 0 ? inner.slice(0, lastComma).trim() : inner;
        const errName = lastComma >= 0 ? inner.slice(lastComma + 1).trim() : '';
        const condition = parseCallExprFromStr(condStr);
        const node: RequireNode = { type: 'Require', condition, error: errName, connective: line.connective };
        pushOrTop(stack, ast, node); break;
      }
      case 'emit': {
        // emit(EventName, field1: value1, field2: value2)
        const inner = line.content.replace(/^emit\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
        const firstComma = inner.indexOf(',');
        const eventName = firstComma >= 0 ? inner.slice(0, firstComma).trim() : inner;
        const fieldsRaw = firstComma >= 0 ? inner.slice(firstComma + 1).trim() : '';
        const fields = fieldsRaw
          ? splitFnParams(fieldsRaw).map(f => {
              const colon = f.indexOf(':');
              return colon >= 0
                ? { name: f.slice(0, colon).trim(), value: f.slice(colon + 1).trim() }
                : { name: f.trim(), value: f.trim() };
            })
          : [];
        const emitNode: EmitNode = { type: 'Emit', eventName, fields, connective: line.connective };
        pushOrTop(stack, ast, emitNode); break;
      }
      case 'pda': {
        // let varName = pda([seed1, seed2, ...])  or  pda([seeds])
        const letMatch = line.content.match(/^let\s+(\w+)\s*=\s*pda\s*\(\[([\s\S]*)\]\)/);
        const bareMatch = line.content.match(/^pda\s*\(\[([\s\S]*)\]\)/);
        const varName = letMatch ? letMatch[1] : '_pda';
        const seedsRaw = letMatch ? letMatch[2] : (bareMatch ? bareMatch[1] : '');
        const seeds = seedsRaw.split(',').map(s => s.trim()).filter(s => s.length > 0);
        const pdaNode: PdaNode = { type: 'Pda', varName, seeds, connective: line.connective };
        pushOrTop(stack, ast, pdaNode); break;
      }
      case 'cpi': {
        // cpi(program_id, instruction_name, [account1, account2])
        const inner = line.content.replace(/^cpi\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
        const parts = splitFnParams(inner);
        const program     = parts[0]?.trim() ?? '';
        const instruction = parts[1]?.trim() ?? '';
        const accountsRaw = parts[2]?.trim() ?? '';
        const accounts = accountsRaw.replace(/^\[/, '').replace(/\]$/, '')
          .split(',').map(s => s.trim()).filter(s => s.length > 0);
        const cpiNode: CpiNode = { type: 'Cpi', program, instruction, accounts, connective: line.connective };
        pushOrTop(stack, ast, cpiNode); break;
      }
      case 'transfer': {
        // transfer(from, to, amount)
        const inner = line.content.replace(/^transfer\s*\(/, '').replace(/\)\s*;?\s*$/, '').trim();
        const parts = splitFnParams(inner);
        const transferNode: TransferNode = {
          type: 'Transfer',
          from:   parts[0]?.trim() ?? '',
          to:     parts[1]?.trim() ?? '',
          amount: parts[2]?.trim() ?? '',
          connective: line.connective,
        };
        pushOrTop(stack, ast, transferNode); break;
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
        // Struct/account fields and type/error variants go into their arrays; others go into body
        const top = stack.length > 0 ? stack[stack.length - 1] : null;
        if (top?.type === 'Struct' || top?.type === 'Account') {
          (top as unknown as { fields: string[] }).fields.push(line.content);
        } else if (top?.type === 'TypeDecl' || top?.type === 'ErrorDecl') {
          (top as unknown as { variants: string[] }).variants.push(line.content);
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
  if (block.type === 'Struct' || block.type === 'TypeDecl' || block.type === 'Account' || block.type === 'ErrorDecl') {
    // field-based blocks don't have a body[] for statement nodes — skip
    return;
  }
  (block as TheoremNode | DefinitionNode | ProofNode | LemmaNode | FnDeclNode | InstructionNode | ProgramNode).body.push(node);
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
  // Accept both `fn name(params) -> T {` (normal) and `fn name(params) -> T` (native, no body)
  const match = content.match(/^fn\s+(\w+)\s*\(([\s\S]*?)\)\s*->\s*([^{]+?)\s*\{?$/);
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

  for (const req of node.requires) {
    theoremBody.push({
      type: 'Given' as const,
      expr: req,
      connective: '→' as const,
    });
  }

  if (node.ensures.length > 0) {
    for (let i = 0; i < node.ensures.length; i++) {
      theoremBody.push({
        type: 'Assert' as const,
        expr: node.ensures[i],
        connective: i === node.ensures.length - 1 ? null : '∧',
      });
    }
  } else {
    theoremBody.push({
      type: 'Assert' as const,
      expr: goalExpr,
      connective: null,
    });
  }

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

// Validate that a theorem/lemma declaration body uses the correct structure:
// - assume() nodes are joined with ∧ (independent hypotheses), not → (which would imply dependency)
// - the last assume() is followed by → to declareToProve()
// - exactly one declareToProve() as the final step
// - no given() or assert() (legacy keywords produce legacyError annotations)
export function validateDeclarationBody(name: string, body: ASTNode[]): string[] {
  const errors: string[] = [];
  for (const node of body) {
    const legacy = (node as ASTNode & { legacyError?: string }).legacyError;
    if (legacy) errors.push(`In '${name}': ${legacy}`);
  }
  const assumes = body.filter(n => n.type === 'Assume') as AssumeNode[];
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
    } else {
      // Non-last assume() connects to the next assume() — must use ∧ (independent hypotheses)
      if (node.connective === '→')
        errors.push(`In '${name}': assume() followed by another assume() must use ∧, not → (hypotheses are independent)`);
    }
  }
  return errors;
}

function isTopLevelBlock(node: ASTNode): node is BlockNode {
  return node.type === 'Theorem' ||
    node.type === 'Definition' ||
    node.type === 'Struct' ||
    node.type === 'TypeDecl' ||
    node.type === 'Proof' ||
    node.type === 'Lemma' ||
    node.type === 'FnDecl' ||
    node.type === 'Program' ||
    node.type === 'Account' ||
    node.type === 'Instruction' ||
    node.type === 'ErrorDecl';
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
    case 'Account':
    case 'Instruction':
    case 'ErrorDecl':
      return `${node.type.toLowerCase()} '${node.name}'`;
    case 'Program':
      return `program '${node.name}'`;
  }
}

// ── Instruction signature parser ──────────────────────────────────────────────

function parseInstructionSignature(content: string): { name: string; params: InstructionParam[] } {
  // instruction TransferTokens(from: mut signer ∈ TokenAccount, amount ∈ Lamport) {
  const match = content.match(/^instruction\s+(\w+)\s*\(([\s\S]*)\)\s*\{?$/);
  if (!match) throw new Error(`Malformed instruction signature: ${content}`);
  const [, name, rawParams] = match;
  const params = rawParams.trim()
    ? splitFnParams(rawParams).map(p => parseInstructionParam(p.trim()))
    : [];
  return { name, params };
}

function parseInstructionParam(value: string): InstructionParam {
  // Account param:  name: [qualifiers] ∈ Type   e.g. "from: mut signer ∈ TokenAccount"
  // Data param:     name ∈ Type                  e.g. "amount ∈ Lamport"
  const accountMatch = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*:\s*(.*?)\s*∈\s*(.+)$/);
  if (accountMatch) {
    const qualifiers = accountMatch[2].trim().split(/\s+/)
      .filter(q => q.length > 0)
      .filter((q): q is AccountQualifier => ['mut', 'signer', 'init', 'close', 'seeds'].includes(q));
    return {
      name: accountMatch[1],
      qualifiers,
      paramType: normalizeSortName(accountMatch[3]),
      isAccount: true,
    };
  }
  // Data param
  const dataMatch = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
  if (dataMatch) {
    return {
      name: dataMatch[1],
      qualifiers: [],
      paramType: normalizeSortName(dataMatch[2]),
      isAccount: false,
    };
  }
  throw new Error(`Malformed instruction parameter: ${value}`);
}

// ── Error variant parser ──────────────────────────────────────────────────────

function parseErrorVariant(raw: string): ErrorVariant {
  // | VariantName("message")  or  | VariantName
  const trimmed = raw.trim().replace(/^[|,]+\s*/, '').trim();
  const withMsg = trimmed.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*\("(.*)"\)\s*$/);
  if (withMsg) return { name: withMsg[1], message: withMsg[2] };
  const bare = trimmed.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*$/);
  if (bare) return { name: bare[1], message: bare[1] };
  throw new Error(`Malformed error variant: ${raw}`);
}

// ── Expression parser from raw string (no keyword prefix) ────────────────────

function parseCallExprFromStr(raw: string) {
  try {
    return parseExpr(raw);
  } catch {
    return { type: 'Atom' as const, condition: raw, atomKind: 'opaque' as const };
  }
}
