// src/parser/formal.ts
import { lexFL } from './lexer';
import { parseLinesToAST } from './parser';
import { generateJSFromAST } from '../codegen';
import { runtimePreamble } from '../codegen/runtime';
import { Statement, Proof, LogicalOperator } from '../types/basic'


export function parseFL(text: string): string {
  const lines = lexFL(text);
  const ast = parseLinesToAST(lines);
  const output = generateJSFromAST(ast, runtimePreamble);
  return output;
}