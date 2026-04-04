// src/parser/ast.ts

// ── Logical connective expression nodes ────────────────────────────────────

export interface AndNode {
  type: 'And';
  left: ExprNode;
  right: ExprNode;
}

export interface OrNode {
  type: 'Or';
  left: ExprNode;
  right: ExprNode;
}

export interface ImpliesNode {
  type: 'Implies';
  left: ExprNode;
  right: ExprNode;
}

export interface IffNode {
  type: 'Iff';
  left: ExprNode;
  right: ExprNode;
}

export interface NotNode {
  type: 'Not';
  operand: ExprNode;
}

/** A leaf expression: a condition string (may include ==, !=, etc.) */
export interface AtomNode {
  type: 'Atom';
  condition: string;
}

export type ExprNode = AndNode | OrNode | ImpliesNode | IffNode | NotNode | AtomNode;

// ── Statement-level AST nodes ───────────────────────────────────────────────

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
  /** Parsed expression tree (may be compound via connectives) */
  expr: ExprNode;
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
  | TheoremNode
  | DefinitionNode
  | ProofNode
  | AssertNode
  | LetNode
  | RawNode;
