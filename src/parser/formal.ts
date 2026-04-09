// src/parser/formal.ts
import { lexFL } from './lexer';
import { parseLinesToAST } from './parser';
import { generateJSFromAST } from '../codegen';
import { runtimePreamble } from '../codegen/runtime';
import * as fs from 'fs';
import * as path from 'path';

export function parseFL(text: string): string {
  const lines = lexFL(text);
  const ast   = parseLinesToAST(lines, { desugarFns: false });
  return generateJSFromAST(ast, runtimePreamble);
}

export function parseFLFile(filePath: string): string {
  const expanded = expandImports(filePath, new Set());
  return parseFL(expanded);
}

function expandImports(filePath: string, seen: Set<string>): string {
  const absolute = path.resolve(filePath);
  if (seen.has(absolute)) return '';
  seen.add(absolute);

  const source = fs.readFileSync(absolute, 'utf8');
  const dir = path.dirname(absolute);
  const chunks: string[] = [];

  for (const line of source.replace(/\r\n/g, '\n').split('\n')) {
    const match = line.trim().match(/^import\s+["'](.+?\.fl)["']\s*;?\s*$/);
    if (!match) {
      chunks.push(line);
      continue;
    }
    const target = path.resolve(dir, match[1]);
    const imported = expandImports(target, seen).trimEnd();
    if (imported.length > 0) {
      chunks.push(ensureTrailingConnective(imported));
    }
  }

  return chunks.join('\n');
}

function ensureTrailingConnective(source: string): string {
  const lines = source.split('\n');
  for (let index = lines.length - 1; index >= 0; index--) {
    const trimmed = lines[index].trim();
    if (!trimmed) continue;
    if (/(→|∧|↔|->|&&|<->)\s*$/.test(trimmed)) return source;
    lines[index] = `${lines[index]} →`;
    return lines.join('\n');
  }
  return source;
}
