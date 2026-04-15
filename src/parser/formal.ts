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

export function expandFLFile(filePath: string): string {
  return expandImports(filePath, new Set());
}

/**
 * Find the project root by walking up from `start` until we find a directory
 * that contains package.json, or return null if not found.
 */
function findProjectRoot(start: string): string | null {
  let dir = path.resolve(start);
  while (true) {
    if (fs.existsSync(path.join(dir, 'package.json'))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) return null;
    dir = parent;
  }
}

/**
 * Resolve a bare module name like "math" or "sets-basic" to a lib/*.fl path.
 * Searches lib/ relative to the project root, then relative to the importing file.
 */
function resolveStdlib(name: string, fromDir: string): string | null {
  const candidates: string[] = [];

  // Walk up to project root and check lib/
  const root = findProjectRoot(fromDir);
  if (root) candidates.push(path.join(root, 'lib', `${name}.fl`));

  // Also check lib/ relative to the file (covers nested projects)
  for (let d = fromDir; ; d = path.dirname(d)) {
    candidates.push(path.join(d, 'lib', `${name}.fl`));
    if (path.dirname(d) === d) break;
  }

  for (const c of candidates) {
    if (fs.existsSync(c)) return c;
  }
  return null;
}

function expandImports(filePath: string, seen: Set<string>): string {
  const absolute = path.resolve(filePath);
  if (seen.has(absolute)) return '';
  seen.add(absolute);

  const source = fs.readFileSync(absolute, 'utf8');
  const dir = path.dirname(absolute);
  const chunks: string[] = [];

  for (const line of source.replace(/\r\n/g, '\n').split('\n')) {
    // Quoted path: import "./foo.fl" or import "../lib/math.fl"
    const quotedMatch = line.trim().match(/^import\s+["'](.+?\.fl)["']\s*;?\s*$/);
    if (quotedMatch) {
      const target = path.resolve(dir, quotedMatch[1]);
      const imported = expandImports(target, seen).trimEnd();
      if (imported.length > 0) chunks.push(ensureTrailingConnective(imported));
      continue;
    }

    // Bare name: import math  /  import sets-basic  /  import "math"
    const bareMatch = line.trim().match(/^import\s+["']?([A-Za-z][A-Za-z0-9_-]*)["']?\s*;?\s*$/);
    if (bareMatch) {
      const resolved = resolveStdlib(bareMatch[1], dir);
      if (resolved) {
        const imported = expandImports(resolved, seen).trimEnd();
        if (imported.length > 0) chunks.push(ensureTrailingConnective(imported));
      } else {
        // Leave the line as-is so the parser can emit a useful error
        chunks.push(line);
      }
      continue;
    }

    chunks.push(line);
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
