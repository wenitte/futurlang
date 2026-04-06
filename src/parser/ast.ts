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

export interface QuantifiedNode {
  type: 'Quantified';
  quantifier: 'forall' | 'exists' | 'exists_unique';
  binderStyle: 'bounded' | 'typed';
  variable: string;
  domain: string;
  body: ExprNode | null;
}

export interface AtomNode {
  type: 'Atom';
  condition: string;
  atomKind: 'expression' | 'string' | 'opaque';
  parseError?: string;
}

export type ExprNode = AndNode | OrNode | ImpliesNode | IffNode | NotNode | QuantifiedNode | AtomNode;

// ── Statement-level AST nodes ───────────────────────────────────────────────

// Inter-block connective: what follows a closing }
export type BlockConnective = '→' | '∧' | '↔' | null; // null = last block, no connective

export interface TheoremNode {
  type: 'Theorem';
  name: string;
  body: ASTNode[];
  connective: BlockConnective; // connective to the NEXT block
}

export interface DefinitionNode {
  type: 'Definition';
  name: string;
  body: ASTNode[];
  connective: BlockConnective;
}

export interface StructNode {
  type: 'Struct';
  name: string;
  fields: string[];           // raw field lines, for now
  connective: BlockConnective;
}

export interface ProofNode {
  type: 'Proof';
  name: string;
  body: ASTNode[];
  connective: BlockConnective;
}

export interface LemmaNode {
  type: 'Lemma';
  name: string;
  body: ASTNode[];
  connective: BlockConnective;
}

export interface AssertNode {
  type: 'Assert';
  expr: ExprNode;
  connective: BlockConnective; // for assert(...) → inside proof bodies
}

export interface GivenNode {
  type: 'Given';
  expr: ExprNode;
  connective: BlockConnective;
}

export interface AssumeNode {
  type: 'Assume';
  expr: ExprNode;
  connective: BlockConnective;
}

export interface ConcludeNode {
  type: 'Conclude';
  expr: ExprNode;
  connective: BlockConnective;
}

export interface ApplyNode {
  type: 'Apply';
  target: string;
  connective: BlockConnective;
}

export interface SetVarNode {
  type: 'SetVar';
  varName: string;
  varType: string | null;   // e.g. 'ℝ', 'ℕ', null if untyped
  value: string | null;     // may be absent for typed declarations
  connective: BlockConnective;
}

export interface RawNode {
  type: 'Raw';
  content: string;
  connective: BlockConnective;
}

export type ASTNode =
  | TheoremNode
  | DefinitionNode
  | StructNode
  | ProofNode
  | LemmaNode
  | AssertNode
  | GivenNode
  | AssumeNode
  | ConcludeNode
  | ApplyNode
  | SetVarNode
  | RawNode;

// The top-level program is a single chained expression built from these nodes.
