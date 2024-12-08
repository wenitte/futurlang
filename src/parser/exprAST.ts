// src/parsing/exprAST.ts

export type LogicExpr =
  | { type: 'Quantifier'; quantifier: 'forall' | 'exists'; variable: string; set: string; body: LogicExpr }
  | { type: 'Not'; expr: LogicExpr }
  | { type: 'BinaryOp'; op: 'and' | 'or' | 'implies' | 'iff'; left: LogicExpr; right: LogicExpr }
  | { type: 'InSet'; element: string; set: string }
  | { type: 'NotInSet'; element: string; set: string }
  | { type: 'Subset'; proper: boolean; left: string; right: string }
  | { type: 'SetOp'; op: 'union' | 'intersect'; left: string; right: string }
  | { type: 'EmptySet' }
  | { type: 'Predicate'; name: string; args: string[] }
  | { type: 'Var'; name: string };
