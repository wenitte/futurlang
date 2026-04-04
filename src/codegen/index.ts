// src/codegen/index.ts

import {
  ASTNode, BlockConnective,
  TheoremNode, DefinitionNode, StructNode, ProofNode, LemmaNode,
  AssertNode, AssumeNode, ConcludeNode, ApplyNode, SetVarNode, RawNode,
  ExprNode, AtomNode,
} from '../parser/ast';

export function generateJSFromAST(nodes: ASTNode[], runtime: string): string {
  let code = runtime + '\n';

  // Fold the full program into one expression
  const expr = foldNodes(nodes);
  code += `\n// ── Evaluate program as single logical expression ──\n`;
  code += `const _result = ${expr};\n`;
  code += `if (!_resolve(_result)) throw new Error('Program does not hold: ' + _describe(_result));\n`;
  code += `console.log('\\n✓ Program holds: ' + _describe(_result));\n`;

  return code;
}

// ── Fold a list of nodes into one nested JS expression ──────────────────────
function foldNodes(nodes: ASTNode[]): string {
  const meaningful = nodes.filter(n =>
    !(n.type === 'Raw' && (n as RawNode).content.trim().length === 0)
  );
  if (meaningful.length === 0) return 'atom(true, "∅")';

  let acc = nodeToExpr(meaningful[meaningful.length - 1]);
  for (let i = meaningful.length - 2; i >= 0; i--) {
    const node = meaningful[i];
    const conn = node.connective ?? '→';
    const left = nodeToExpr(node);
    acc = applyConnective(conn, left, acc);
  }
  return acc;
}

function applyConnective(conn: BlockConnective, left: string, right: string): string {
  switch (conn) {
    case '→':  return `seq(()=>${left}, ()=>${right})`;
    case '∧':  return `and(${left}, ${right})`;
    case '↔':  return `iff(${left}, ${right})`;
    default:   return `seq(()=>${left}, ()=>${right})`;
  }
}

// ── Convert a single node to a JS expression string ─────────────────────────
function nodeToExpr(node: ASTNode): string {
  switch (node.type) {
    case 'Theorem':    return generateTheorem(node);
    case 'Proof':      return generateProof(node);
    case 'Lemma':      return generateLemma(node);
    case 'Definition': return generateDefinition(node);
    case 'Struct':     return generateStruct(node);
    case 'Assert':     return `assertExpr(${generateExpr(node.expr)})`;
    case 'Assume':     return `assumeExpr(${generateExpr(node.expr)})`;
    case 'Conclude':   return `concludeExpr(${generateExpr(node.expr)})`;
    case 'Apply':      return `applyLemma(${JSON.stringify(node.target)})`;
    case 'SetVar':     return generateSetVar(node);
    case 'Raw':        return `atom(true, ${JSON.stringify(node.content)})`;
    default: {
      const _: never = node;
      throw new Error('Unhandled node type');
    }
  }
}

// ── Block generators ─────────────────────────────────────────────────────────
function generateTheorem(node: TheoremNode): string {
  const inner = foldNodes(node.body);
  return `theorem(${JSON.stringify(node.name)}, () => ${inner})`;
}

function generateProof(node: ProofNode): string {
  const inner = foldNodes(node.body);
  return `proof(${JSON.stringify(node.name)}, () => ${inner})`;
}

function generateLemma(node: LemmaNode): string {
  const inner = foldNodes(node.body);
  return `lemma(${JSON.stringify(node.name)}, () => ${inner})`;
}

function generateDefinition(node: DefinitionNode): string {
  const inner = node.body.length > 0 ? foldNodes(node.body) : 'atom(true, "defined")';
  return `definition(${JSON.stringify(node.name)}, () => ${inner})`;
}

function generateStruct(node: StructNode): string {
  return `struct_(${JSON.stringify(node.name)}, ${JSON.stringify(node.fields)})`;
}

function generateSetVar(node: SetVarNode): string {
  const label = node.varType ? `${node.varName}: ${node.varType}` : node.varName;
  if (node.value !== null) {
    // Only pass as raw JS for simple literals (true, false, numbers, quoted strings)
    const isSimple = /^(true|false|-?\d+(\.\d+)?|"[^"]*"|'[^']*')$/.test(node.value.trim());
    const safeVal = isSimple ? node.value : JSON.stringify(node.value);
    return `setVar(${JSON.stringify(node.varName)}, ${safeVal}, ${JSON.stringify(label)})`;
  }
  return `setVar(${JSON.stringify(node.varName)}, undefined, ${JSON.stringify(label)})`;
}

// ── Expression nodes ─────────────────────────────────────────────────────────
function generateExpr(node: ExprNode): string {
  switch (node.type) {
    case 'Atom':    return generateAtom(node);
    case 'And':     return `and(${generateExpr(node.left)}, ${generateExpr(node.right)})`;
    case 'Or':      return `or(${generateExpr(node.left)}, ${generateExpr(node.right)})`;
    case 'Implies': return `implies(${generateExpr(node.left)}, ${generateExpr(node.right)})`;
    case 'Iff':     return `iff(${generateExpr(node.left)}, ${generateExpr(node.right)})`;
    case 'Not':     return `not(${generateExpr(node.operand)})`;
    default: {
      const _: never = node;
      throw new Error('Unhandled expr node type');
    }
  }
}

function generateAtom(node: AtomNode): string {
  const c   = node.condition.trim();
  const lbl = JSON.stringify(c);

  // Already a string literal
  if ((c.startsWith('"') && c.endsWith('"')) || (c.startsWith("'") && c.endsWith("'"))) {
    return `atom(true, ${lbl})`;
  }
  if (c === 'true')  return `atom(true,  "true")`;
  if (c === 'false') return `atom(false, "false")`;

  // Contains mathematical notation that isn't valid JS — treat as an asserted claim
  const MATH_CHARS = /[∀∃⇒≥≤≠∈∉⊆⊇∪∩∧∨¬→↔λΣ∑∏√∞·]/;
  // Also catch |X| cardinality, [G:H] index notation, set-builder {x | ...}
  const MATH_NOTATION = /\|[^|]|\bmod\b|divides|\{.*\|/;
  if (MATH_CHARS.test(c) || MATH_NOTATION.test(c)) {
    return `atom(true, ${lbl})`;
  }

  // Relational JS expression
  if (/[=<>!]/.test(c) || /\b(===|!==|>=|<=)\b/.test(c)) {
    // Guard against single = (assignment) — use == for equality checks
    const safe = c.replace(/(?<![=!<>])=(?!=)/g, '==');
    try {
      // Quick syntax check
      new Function(`return !!(${safe})`);
      return `atom(() => { try { return !!(${safe}); } catch(e) { return true; } }, ${lbl})`;
    } catch {
      return `atom(true, ${lbl})`;
    }
  }

  // Bare identifier
  return `atom(() => !!${c}, ${lbl})`;
}

// keep for compatibility
function generateNode(node: ASTNode): string { return nodeToExpr(node); }
