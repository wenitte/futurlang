// src/codegen/index.ts

import {
  ASTNode, TheoremNode, DefinitionNode, ProofNode,
  AssertNode, LetNode, RawNode,
  ExprNode, AtomNode,
} from '../parser/ast';

export function generateJSFromAST(nodes: ASTNode[], runtime: string): string {
  let code = runtime + '\n';
  for (const node of nodes) {
    code += generateNode(node);
  }
  return code;
}

// ── Statement nodes ───────────────────────────────────────────────────────────

function generateNode(node: ASTNode): string {
  switch (node.type) {
    case 'Theorem':    return generateTheorem(node);
    case 'Definition': return generateDefinition(node);
    case 'Proof':      return generateProof(node);
    case 'Assert':     return `assertExpr(${generateExpr(node.expr)});\n`;
    case 'Let':        return `setVar("${node.varName}", ${node.value});\n`;
    case 'Raw':        return `// ${node.content}\n`;
    default: {
      const _exhaustive: never = node;
      throw new Error('Unhandled node type');
    }
  }
}

function indent(code: string): string {
  return code
    .split('\n')
    .map(l => (l.length ? '  ' + l : ''))
    .join('\n');
}

function generateTheorem(node: TheoremNode): string {
  const body = node.body.map(generateNode).join('');
  return `theorem("${node.name}", () => {\n${indent(body)}\n});\n`;
}

function generateDefinition(node: DefinitionNode): string {
  const body = node.body.map(generateNode).join('');
  return `definition("${node.name}", () => {\n${indent(body)}\n});\n`;
}

function generateProof(node: ProofNode): string {
  return '// proof\n' + node.body.map(generateNode).join('') + '// end proof\n';
}

// ── Expression nodes ──────────────────────────────────────────────────────────

function generateExpr(node: ExprNode): string {
  switch (node.type) {
    case 'Atom':    return generateAtom(node);
    case 'And':     return `and(${generateExpr(node.left)}, ${generateExpr(node.right)})`;
    case 'Or':      return `or(${generateExpr(node.left)}, ${generateExpr(node.right)})`;
    case 'Implies': return `implies(${generateExpr(node.left)}, ${generateExpr(node.right)})`;
    case 'Iff':     return `iff(${generateExpr(node.left)}, ${generateExpr(node.right)})`;
    case 'Not':     return `not(${generateExpr(node.operand)})`;
    default: {
      const _exhaustive: never = node;
      throw new Error('Unhandled expr node type');
    }
  }
}

function generateAtom(node: AtomNode): string {
  const c   = node.condition.trim();
  const lbl = JSON.stringify(c); // safe label string for display

  // String literal claim — always true, displayed as-is
  if ((c.startsWith('"') && c.endsWith('"')) ||
      (c.startsWith("'") && c.endsWith("'"))) {
    return `atom(true, ${lbl})`;
  }

  // Literal true/false
  if (c === 'true')  return `atom(true,  "true")`;
  if (c === 'false') return `atom(false, "false")`;

  // Expression containing relational / equality operators — evaluate as JS
  if (/[=<>!]/.test(c) || /\b(===|!==|>=|<=)\b/.test(c)) {
    return `atom(() => !!(${c}), ${lbl})`;
  }

  // Bare identifier (variable name)
  return `atom(() => !!${c}, ${lbl})`;
}
