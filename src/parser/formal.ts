// src/parser/formal.ts
import { lexFL } from './lexer';
import { parseLinesToAST } from './parser';
import { generateJSFromAST } from '../codegen';
import { runtimePreamble } from '../codegen/runtime';

export function parseFL(text: string): string {
  const lines = lexFL(text);
  const ast   = parseLinesToAST(lines);
  return generateJSFromAST(ast, runtimePreamble);
}
