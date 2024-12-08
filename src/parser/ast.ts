// We reuse the existing LogicExpr from exprAST for expressions within definitions, theorems, etc.
import { LogicExpr } from './exprAST';

export interface TheoremDeclarationNode {
  type: 'TheoremDeclaration';
  name: string;
  body: ASTNode;
}

export interface DefinitionDeclarationNode {
  type: 'DefinitionDeclaration';
  name: string;
  body: ASTNode;
}

export interface ProofDeclarationNode {
  type: 'ProofDeclaration';
  name?: string; // Might not have a name for the main proof
  body: ASTNode;
}

export interface LemmaDeclarationNode {
  type: 'LemmaDeclaration';
  name: string;
  body: ASTNode;
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

export interface AndNode {
  type: 'And';
  left: ASTNode;
  right: ASTNode;
}

export type ASTNode =
  | LogicExpr
  | TheoremDeclarationNode
  | DefinitionDeclarationNode
  | ProofDeclarationNode
  | LemmaDeclarationNode
  | AssertNode
  | LetNode
  | RawNode
  | AndNode;