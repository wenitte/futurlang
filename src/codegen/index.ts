// src/codegen/index.ts

import { ASTNode, TheoremNode, DefinitionNode, ProofNode, AssertNode, LetNode, RawNode } from '../parser/ast'; // Ensure the correct path

export function generateJSFromAST(nodes: ASTNode[], runtime: string): string {
  let code = runtime + '\n';

  for (const node of nodes) {
    code += generateNode(node);
  }

  return code;
}

function generateNode(node: ASTNode): string {
  switch (node.type) {
    case 'Theorem':
      return generateTheorem(node);
    case 'Definition':
      return `// Definition: ${node.name}\n` + node.body.map(generateNode).join('');
    case 'Proof':
      return '// Proof start\n' + node.body.map(generateNode).join('') + '// Proof end\n';
    case 'Assert':
      return `assert(${node.condition});\n`;
    case 'Let':
      return `setVar("${node.varName}", ${node.value});\n`;
    case 'Raw':
      return `// Raw: ${node.content}\n`;
    default:
      const exhaustiveCheck: never = node;
      throw new Error('Unhandled node type');
  }
}

function generateTheorem(node: TheoremNode): string {
  let result = `theorem("${node.name}", () => {\n`;
  for (const child of node.body) {
    result += generateNode(child);
  }
  result += '});\n';
  return result;
}
