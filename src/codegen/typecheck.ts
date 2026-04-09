import {
  ASTNode,
  ConcludeNode,
  ExprNode,
  FnDeclNode,
  MatchNode,
  PatternNode,
  SetVarNode,
  TypeDeclNode,
} from '../parser/ast';
import { parseExpr } from '../parser/expr';

type TypeName = string;

interface FnSig {
  params: TypeName[];
  returnType: TypeName;
}

interface VariantSig {
  typeName: string;
  fields: Array<{ name: string; type: TypeName }>;
}

interface Env {
  vars: Map<string, TypeName>;
  fns: Map<string, FnSig>;
  variants: Map<string, VariantSig>;
}

export function typecheckExecutableProgram(nodes: ASTNode[]): void {
  const env: Env = {
    vars: new Map([
      ['true', 'Bool'],
      ['false', 'Bool'],
      ['None', 'Option(Any)'],
    ]),
    fns: new Map(),
    variants: new Map(),
  };

  collectTypes(nodes, env);
  collectFunctions(nodes, env);

  for (const node of nodes) {
    if (node.type === 'FnDecl') {
      typecheckFunction(node, env);
    } else if (node.type === 'SetVar' && node.value !== null) {
      env.vars.set(node.varName, inferValueType(node.value, env));
    }
  }
}

function collectTypes(nodes: ASTNode[], env: Env) {
  for (const node of nodes) {
    if (node.type !== 'TypeDecl') continue;
    registerType(node, env);
  }
  env.variants.set('Some', { typeName: 'Option(Any)', fields: [{ name: 'value', type: 'Any' }] });
  env.variants.set('Ok', { typeName: 'Result(Any,Any)', fields: [{ name: 'value', type: 'Any' }] });
  env.variants.set('Err', { typeName: 'Result(Any,Any)', fields: [{ name: 'error', type: 'Any' }] });
}

function registerType(node: TypeDeclNode, env: Env) {
  for (const variant of node.variants) {
    env.variants.set(variant.name, {
      typeName: node.name,
      fields: variant.fields.map(field => ({ name: field.name, type: field.type })),
    });
  }
}

function collectFunctions(nodes: ASTNode[], env: Env) {
  env.fns.set('fold', { params: ['List(Any)', 'Any', '(Any,Any)->Any'], returnType: 'Any' });
  env.fns.set('request', { params: ['String', 'String', 'Any', 'Any'], returnType: 'Request' });
  env.fns.set('text', { params: ['Any', 'ℕ', 'Any'], returnType: 'Response' });
  env.fns.set('html', { params: ['Any', 'ℕ', 'Any'], returnType: 'Response' });
  env.fns.set('json', { params: ['Any', 'ℕ', 'Any'], returnType: 'Response' });
  env.fns.set('route', { params: ['String', 'String', 'Any'], returnType: 'Route' });
  env.fns.set('router', { params: ['List(Route)', 'Any'], returnType: 'Handler' });
  env.fns.set('dispatch', { params: ['Handler', 'Request'], returnType: 'Response' });
  env.fns.set('serve', { params: ['ℕ', 'Handler', 'String'], returnType: 'Server' });
  for (const node of nodes) {
    if (node.type !== 'FnDecl') continue;
    env.fns.set(node.name, {
      params: node.params.map(param => normalizeType(param.type)),
      returnType: normalizeType(node.returnType),
    });
  }
}

function typecheckFunction(node: FnDeclNode, rootEnv: Env) {
  const fnSig = rootEnv.fns.get(node.name);
  if (!fnSig) return;
  const env: Env = {
    vars: new Map(rootEnv.vars),
    fns: rootEnv.fns,
    variants: rootEnv.variants,
  };

  node.params.forEach(param => env.vars.set(param.name, normalizeType(param.type)));
  const returns = inferBodyReturnTypes(node.body, env);
  if (returns.length === 0) {
    throw new Error(`Function '${node.name}' has no conclude/return path`);
  }
  for (const resultType of returns) {
    if (!isAssignable(resultType, fnSig.returnType)) {
      throw new Error(`Function '${node.name}' returns '${resultType}' but declared '${fnSig.returnType}'`);
    }
  }
}

function inferBodyReturnTypes(nodes: ASTNode[], env: Env): TypeName[] {
  const returns: TypeName[] = [];
  for (const node of nodes) {
    if (node.type === 'SetVar' && node.value !== null) {
      env.vars.set(node.varName, inferValueType(node.value, env));
    } else if (node.type === 'Conclude') {
      returns.push(inferExprType(node.expr, env));
    } else if (node.type === 'Match') {
      returns.push(...inferMatchReturnTypes(node, env));
    } else if (node.type === 'Raw') {
      const rawReturn = node.content.match(/^return\s+(.+?);?\s*$/);
      if (rawReturn) returns.push(inferRawType(rawReturn[1], env));
    }
  }
  return returns;
}

function inferMatchReturnTypes(node: MatchNode, env: Env): TypeName[] {
  const scrutineeType = inferExprType(node.scrutinee, env);
  const returns: TypeName[] = [];
  for (const matchCase of node.cases) {
    const branchEnv: Env = {
      vars: new Map(env.vars),
      fns: env.fns,
      variants: env.variants,
    };
    bindPattern(matchCase.pattern, scrutineeType, branchEnv);
    returns.push(...inferBodyReturnTypes(matchCase.body, branchEnv));
  }
  return returns;
}

function bindPattern(pattern: PatternNode, scrutineeType: TypeName, env: Env) {
  if (pattern.kind === 'list_cons') {
    const elementType = listElementType(scrutineeType) ?? 'Any';
    if (pattern.head !== '_') env.vars.set(pattern.head, elementType);
    env.vars.set(pattern.tail, scrutineeType);
    return;
  }
  if (pattern.kind !== 'variant') return;
  if (pattern.constructor === 'true' || pattern.constructor === 'false') return;
  const variant = env.variants.get(pattern.constructor);
  if (!variant) return;
  pattern.bindings.forEach((binding, index) => {
    if (!binding || binding === '_') return;
    env.vars.set(binding, variant.fields[index]?.type ?? 'Any');
  });
}

function inferExprType(expr: ExprNode, env: Env): TypeName {
  switch (expr.type) {
    case 'Atom':
      return inferRawType(expr.condition, env);
    case 'And':
    case 'Or':
    case 'Implies':
    case 'Iff':
    case 'Not':
      return 'Bool';
    case 'If': {
      const conditionType = inferExprType(expr.condition, env);
      if (!isAssignable(conditionType, 'Bool')) {
        throw new Error(`if condition must be Bool, got '${conditionType}'`);
      }
      const thenType = inferExprType(expr.thenBranch, env);
      const elseType = inferExprType(expr.elseBranch, env);
      return unifyTypes(thenType, elseType);
    }
    case 'LetExpr': {
      const nextEnv: Env = { vars: new Map(env.vars), fns: env.fns, variants: env.variants };
      nextEnv.vars.set(expr.name, inferExprType(expr.value, env));
      return inferExprType(expr.body, nextEnv);
    }
    case 'Lambda':
      return `(${expr.params.map(param => normalizeType(param.type)).join(',')}) -> ${inferExprType(expr.body, {
        vars: new Map([...env.vars, ...expr.params.map(param => [param.name, normalizeType(param.type)] as const)]),
        fns: env.fns,
        variants: env.variants,
      })}`;
    case 'Fold': {
      const sequenceType = inferRawType(expr.sequence, env);
      const initType = inferRawType(expr.init, env);
      const fnType = inferRawType(expr.fn, env);
      if (!sequenceType.startsWith('List(')) return 'Any';
      if (!fnType.includes('->')) return initType;
      return initType;
    }
    case 'Quantified':
      return 'Bool';
    case 'SetBuilder':
    case 'IndexedUnion':
      return 'Any';
    default:
      return 'Any';
  }
}

function inferValueType(value: string, env: Env): TypeName {
  try {
    return inferExprType(parseExpr(value), env);
  } catch {
    return inferRawType(value, env);
  }
}

function inferRawType(value: string, env: Env): TypeName {
  const trimmed = normalizeType(value);
  if (trimmed === 'true' || trimmed === 'false') return 'Bool';
  if ((trimmed.startsWith('"') && trimmed.endsWith('"')) || (trimmed.startsWith("'") && trimmed.endsWith("'"))) return 'String';
  if (/^\d+$/.test(trimmed)) return 'Nat';
  if (/^\d+\.\d+$/.test(trimmed)) return 'Real';
  if (trimmed === '[]') return 'List(Any)';
  if (/^\[.*\]$/.test(trimmed)) return inferListType(trimmed, env);
  if (env.vars.has(trimmed)) return env.vars.get(trimmed)!;

  const call = trimmed.match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)\s*\(([\s\S]*)\)$/);
  if (call) {
    return inferCallType(call[1], call[2], env);
  }

  if (/^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(trimmed) && env.variants.has(trimmed)) {
    return env.variants.get(trimmed)!.typeName;
  }
  if (/^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(trimmed) && env.fns.has(trimmed)) {
    const sig = env.fns.get(trimmed)!;
    return `(${sig.params.join(',')}) -> ${sig.returnType}`;
  }
  if (/[<>]=?|==|!=/.test(trimmed)) return 'Bool';
  if (/&&|\|\|/.test(trimmed)) return 'Bool';
  if (/[+\-*/]/.test(trimmed)) return inferNumericType(trimmed, env);
  return 'Any';
}

function inferCallType(name: string, argsRaw: string, env: Env): TypeName {
  const args = splitTopLevelArgs(argsRaw);
  const variant = env.variants.get(name);
  if (variant) {
    args.forEach((arg, index) => {
      const expected = variant.fields[index]?.type ?? 'Any';
      const actual = inferRawType(arg, env);
      if (!isAssignable(actual, expected)) {
        throw new Error(`Constructor '${name}' argument ${index + 1} expects '${expected}', got '${actual}'`);
      }
    });
    return variant.typeName;
  }

  const varFnType = env.vars.get(name);
  if (varFnType && isFunctionType(varFnType)) {
    const signature = parseFunctionType(varFnType);
    if (!signature) return 'Any';
    args.forEach((arg, index) => {
      const actual = inferRawType(arg, env);
      const expected = signature.params[index] ?? signature.params[signature.params.length - 1] ?? 'Any';
      if (!isAssignable(actual, expected)) {
        throw new Error(`Call '${name}' argument ${index + 1} expects '${expected}', got '${actual}'`);
      }
    });
    return signature.returnType;
  }

  const fnSig = env.fns.get(name);
  if (!fnSig) return 'Any';
  args.forEach((arg, index) => {
    const actual = inferRawType(arg, env);
    const expected = fnSig.params[index] ?? fnSig.params[fnSig.params.length - 1] ?? 'Any';
    if (!isAssignable(actual, expected)) {
      throw new Error(`Call '${name}' argument ${index + 1} expects '${expected}', got '${actual}'`);
    }
  });
  return fnSig.returnType;
}

function inferListType(value: string, env: Env): TypeName {
  const inner = value.slice(1, -1).trim();
  if (!inner) return 'List(Any)';
  const parts = splitTopLevelArgs(inner);
  const elementTypes = parts.map(part => {
    if (part.startsWith('...')) {
      return listElementType(inferRawType(part.slice(3).trim(), env)) ?? 'Any';
    }
    return inferRawType(part, env);
  });
  return `List(${elementTypes.reduce(unifyTypes)})`;
}

function inferNumericType(value: string, env: Env): TypeName {
  const names = value.match(/[A-Za-z_][\w₀-₉ₐ-ₙ]*/g) ?? [];
  if (value.includes('.') || value.includes('π')) return 'ℝ';
  if (names.some(name => env.vars.get(name) === 'ℝ' || env.vars.get(name) === 'Real')) return 'ℝ';
  return 'ℕ';
}

function listElementType(type: string): string | null {
  const match = normalizeType(type).match(/^List\((.+)\)$/);
  return match ? match[1].trim() : null;
}

function unifyTypes(left: TypeName, right: TypeName): TypeName {
  if (left === right) return left;
  if (left === 'Any') return right;
  if (right === 'Any') return left;
  if ((left === 'Nat' && right === 'Real') || (left === 'Real' && right === 'Nat')) return 'Real';
  return 'Any';
}

function isAssignable(actual: TypeName, expected: TypeName): boolean {
  const normalizedActual = normalizeType(actual);
  const normalizedExpected = normalizeType(expected);
  if (normalizedExpected === 'Any' || normalizedActual === 'Any') return true;
  if (normalizedActual === normalizedExpected) return true;
  if (isTypeVariable(normalizedExpected) || isTypeVariable(normalizedActual)) return true;
  const actualList = listElementType(normalizedActual);
  const expectedList = listElementType(normalizedExpected);
  if (actualList && expectedList) return isAssignable(actualList, expectedList);
  if (normalizedActual === 'ℕ' && normalizedExpected === 'ℝ') return true;
  if (normalizedExpected.startsWith('Option(') && normalizedActual === 'Option(Any)') return true;
  if (normalizedExpected.startsWith('Result(') && normalizedActual === 'Result(Any,Any)') return true;
  return false;
}

function isTypeVariable(value: string): boolean {
  return /^[A-Z]$/.test(value);
}

function isFunctionType(value: string): boolean {
  return value.includes('->');
}

function parseFunctionType(value: string): { params: string[]; returnType: string } | null {
  const normalized = normalizeType(value);
  const arrowIndex = normalized.lastIndexOf('->');
  if (arrowIndex === -1) return null;
  const left = normalized.slice(0, arrowIndex);
  const returnType = normalized.slice(arrowIndex + 2);
  const params = left.startsWith('(') && left.endsWith(')')
    ? splitTopLevelArgs(left.slice(1, -1))
    : [left];
  return { params: params.filter(Boolean), returnType };
}

function normalizeType(value: string): string {
  return value
    .trim()
    .replace(/\bNat\b/g, 'ℕ')
    .replace(/\bInt\b/g, 'ℤ')
    .replace(/\bReal\b/g, 'ℝ')
    .replace(/\bBool\b/g, 'Bool')
    .replace(/\s+/g, '');
}

function splitTopLevelArgs(value: string): string[] {
  const args: string[] = [];
  let start = 0;
  let depth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth = Math.max(0, depth - 1);
    else if (ch === '[') bracketDepth++;
    else if (ch === ']') bracketDepth = Math.max(0, bracketDepth - 1);
    else if (ch === ',' && depth === 0 && bracketDepth === 0) {
      args.push(value.slice(start, i).trim());
      start = i + 1;
    }
  }
  const final = value.slice(start).trim();
  if (final) args.push(final);
  return args;
}
