import { ASTNode, TheoremDeclarationNode, DefinitionDeclarationNode, ProofDeclarationNode, LemmaDeclarationNode, AssertNode, LetNode, RawNode, AndNode } from '../parser/ast';
import { LogicExpr } from '../parser/exprParser';
import { generateExprJS } from './exprGen';
import { parseLogicExpression } from '../parser/exprParser';
import { runtimePreamble } from './runtime';

export function generateJSFromAST(node: ASTNode, runtime: string = runtimePreamble): string {
  let code = runtime + '\n';
  code += generateNode(node);
  return code;
}

function generateNode(node: ASTNode, isTheoremBody: boolean = false): string {
  switch (node.type) {
    case 'TheoremDeclaration': {
      const theorem = node as TheoremDeclarationNode;
      const bodyContent = generateNode(theorem.body, true);
      return `theorem("${theorem.name}", () => {
  return ${bodyContent};
});`;
    }

    case 'DefinitionDeclaration': {
      const definition = node as DefinitionDeclarationNode;
      return `// Definition: ${definition.name}\n${generateNode(definition.body)}`;
    }

    case 'ProofDeclaration': {
      const proof = node as ProofDeclarationNode;
      return `(() => {
  // Proof ${proof.name ? `of ${proof.name}` : ''}
${generateNode(proof.body)};
  return true;
})()`;
    }

    case 'LemmaDeclaration': {
      const lemma = node as LemmaDeclarationNode;
      return `// Lemma: ${lemma.name}\n${generateNode(lemma.body)}`;
    }

    case 'Assert': {
      const assert = node as AssertNode;
      let assertArg = '';
      if (assert.condition.startsWith('"') && assert.condition.endsWith('"')) {
        assertArg = assert.condition;
      } else {
        try {
          const exprAst = parseLogicExpression(assert.condition);
          assertArg = generateExprJS(exprAst);
        } catch (e) {
          console.error("Failed to parse assert condition:", assert.condition);
          assertArg = `"${assert.condition}"`;
        }
      }
      return `assert(${assertArg})`;
    }

    case 'Let': {
      const letNode = node as LetNode;
      let letValue = '';
      if (letNode.value.startsWith('"') && letNode.value.endsWith('"')) {
        letValue = letNode.value;
      } else {
        try {
          const valAst = parseLogicExpression(letNode.value);
          letValue = generateExprJS(valAst);
        } catch (e) {
          console.error("Failed to parse let value:", letNode.value);
          letValue = `"${letNode.value}"`;
        }
      }
      return `setVar("${letNode.varName}", ${letValue})`;
    }

    case 'Raw': {
      const rawNode = node as RawNode;
      if (!rawNode.content.trim()) {
        return 'true';
      }
      // If it's a string literal, return it directly
      if (rawNode.content.startsWith('"') && rawNode.content.endsWith('"')) {
        return rawNode.content;
      }
      // For theorem bodies, don't wrap in return since we add it in the theorem case
      if (isTheoremBody) {
        // If content already has return, use it as is
        if (rawNode.content.includes('return')) {
          return rawNode.content;
        }
        // Otherwise return the content directly
        return rawNode.content.trim();
      }
      // Otherwise wrap in a comment
      return `/* ${rawNode.content} */\ntrue`;
    }

    case 'And': {
      const andNode = node as AndNode;
      const left = generateNode(andNode.left);
      const right = generateNode(andNode.right);
      // If either side contains statements (indicated by semicolons or returns),
      // wrap it in an IIFE to ensure proper execution
      const wrapIfNeeded = (code: string) => {
        if (code.includes(';') || code.includes('return')) {
          return `(() => { ${code}; return true; })()`;
        }
        return code;
      };
      return `${wrapIfNeeded(left)} && ${wrapIfNeeded(right)}`;
    }

    default: {
      // Handle any remaining LogicExpr types
      try {
        return generateExprJS(node as LogicExpr);
      } catch (e) {
        console.error("Failed to generate expression:", e);
        return 'true';
      }
    }
  }
}