// src/parsing/ast.ts

export interface TheoremNode {
    type: 'Theorem';
    name: string;
    body: ASTNode[];
  }
  
  export interface DefinitionNode {
    type: 'Definition';
    name: string;
    body: ASTNode[];
  }
  
  export interface ProofNode {
    type: 'Proof';
    body: ASTNode[];
  }
  
  export interface AssertNode {
    type: 'Assert';
    condition: string;
  }
  
  export interface LetNode {
    type: 'Let';
    varName: string;
    value: string;
  }
  
  export interface RawNode {
    type: 'Raw';
    content: string;
  }
  
  export type ASTNode = 
    TheoremNode | 
    DefinitionNode | 
    ProofNode | 
    AssertNode | 
    LetNode | 
    RawNode;
  