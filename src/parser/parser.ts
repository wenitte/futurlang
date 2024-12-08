import { ParsedLine, Token } from './lexer'; 
import { ASTNode, TheoremDeclarationNode, DefinitionDeclarationNode, ProofDeclarationNode, LemmaDeclarationNode, AssertNode, LetNode, RawNode, AndNode } from './ast';
import { parseLogicExpression } from './exprParser';

export function parseLinesToAST(lines: ParsedLine[]): ASTNode {
  console.log("Starting to parse lines...");

  let currentExpression: ASTNode | null = null;
  let index = 0;

  function parseBlock(): { nodes: ASTNode[], endIndex: number } {
    let nodes: ASTNode[] = [];
    let blockExpression: ASTNode | null = null;
    let i = index + 1;  // Start after the opening line
    let braceCount = 1;
    let blockContent = '';

    while (i < lines.length && braceCount > 0) {
      const line = lines[i];
      
      // Count braces
      for (const token of line.tokens) {
        if (token.value === '{') braceCount++;
        if (token.value === '}') braceCount--;
      }

      // Don't process the closing brace line
      if (braceCount === 0) break;

      // For declarations, use the preserved body content if available
      const preservedContent = lines[index]?.bodyContent ?? '';
      if (preservedContent) {
        blockContent = preservedContent;
        break;
      } else {
        let expr = parseStatement(line);
        if (expr) {
          if (blockExpression === null) {
            blockExpression = expr;
          } else {
            blockExpression = {
              type: 'And',
              left: blockExpression,
              right: expr
            } as AndNode;
          }
        }
      }

      i++;
    }

    // If we have preserved body content, use it instead of parsed nodes
    if (blockContent) {
      return {
        nodes: [{
          type: 'Raw',
          content: blockContent
        } as RawNode],
        endIndex: i
      };
    }

    return { 
      nodes: blockExpression ? [blockExpression] : [], 
      endIndex: i 
    };
  }

  function parseStatement(line: ParsedLine): ASTNode | null {
    switch (line.type) {
      case 'TheoremDeclaration':
      case 'DefinitionDeclaration':
      case 'ProofDeclaration':
      case 'LemmaDeclaration': {
        const declarationName = line.name || '';
        console.log(`Found ${line.type}: ${declarationName}`);

        const { nodes, endIndex } = parseBlock();
        index = endIndex;  // Update outer index

        const body = nodes.length === 1 ? nodes[0] : 
                    nodes.length > 1 ? nodes.reduce((acc, curr) => ({
                      type: 'And',
                      left: acc,
                      right: curr
                    } as AndNode)) :
                    { type: 'Raw', content: '' } as RawNode;

        switch (line.type) {
          case 'TheoremDeclaration':
            return {
              type: 'TheoremDeclaration',
              name: declarationName,
              body
            } as TheoremDeclarationNode;
          case 'DefinitionDeclaration':
            return {
              type: 'DefinitionDeclaration',
              name: declarationName,
              body
            } as DefinitionDeclarationNode;
          case 'ProofDeclaration':
            return {
              type: 'ProofDeclaration',
              name: declarationName,
              body
            } as ProofDeclarationNode;
          case 'LemmaDeclaration':
            return {
              type: 'LemmaDeclaration',
              name: declarationName,
              body
            } as LemmaDeclarationNode;
        }
        break;
      }

      case 'assert': {
        let condition = line.content;
        if (condition.startsWith('assert(') && condition.endsWith(')')) {
          condition = condition.slice(7, -1).trim();
        }

        // If it's a string literal, keep it as is
        if (condition.startsWith('"') && condition.endsWith('"')) {
          return {
            type: 'Assert',
            condition
          } as AssertNode;
        }

        // Try to parse as logic expression
        try {
          parseLogicExpression(condition);
          return {
            type: 'Assert',
            condition
          } as AssertNode;
        } catch (e) {
          console.error("Failed to parse assert condition:", condition);
          return {
            type: 'Assert',
            condition: `"${condition}"`
          } as AssertNode;
        }
      }

      case 'let': {
        const match = line.content.match(/let\s+(\w+)\s*=\s*(.+?);/);
        if (match) {
          return {
            type: 'Let',
            varName: match[1],
            value: match[2].trim()
          } as LetNode;
        }
        return {
          type: 'Raw',
          content: line.content
        } as RawNode;
      }

      case 'raw': {
        if (line.content === '&&') {
          return null;  // Skip && tokens as they're handled by combination logic
        }
        if (!line.content.trim()) {
          return null;  // Skip empty lines
        }
        return {
          type: 'Raw',
          content: line.content
        } as RawNode;
      }

      default:
        return null;
    }
  }

  while (index < lines.length) {
    const line = lines[index];
    const expr = parseStatement(line);

    if (expr !== null) {
      if (currentExpression === null) {
        currentExpression = expr;
      } else {
        currentExpression = {
          type: 'And',
          left: currentExpression,
          right: expr
        } as AndNode;
      }
    }

    index++;
  }

  if (currentExpression === null) {
    throw new Error("No top level expression");
  }

  return currentExpression;
}