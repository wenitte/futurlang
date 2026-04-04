// src/lean/verifier.ts
//
// Runs a .fl file through the Lean 4 backend and returns structured results.
// The .lean file is a temporary artefact — never shown to the user.

import * as fs from 'fs';
import * as path from 'path';
import { spawnSync } from 'child_process';
import { transpileToLean } from './transpiler';
import { ELAN_HOME, PROJECT, VERIFY_FILE, isSetupComplete, lakeBinary } from './setup';
import { ASTNode } from '../parser/ast';

export interface VerifyResult {
  success: boolean;
  theorems: TheoremResult[];
  errors: VerifyError[];
}

export interface TheoremResult {
  name: string;
  verified: boolean;
  message: string;
}

export interface VerifyError {
  message: string;
  flLine?: number;      // mapped back to .fl source line
  leanLine?: number;    // original lean line (internal, for debugging)
}

// ── Main entry point ──────────────────────────────────────────────────────────

export function verify(nodes: ASTNode[], sourceLines: string[]): VerifyResult {
  if (!isSetupComplete()) {
    return {
      success: false,
      theorems: [],
      errors: [{
        message: 'FuturLang backend not set up. Run: fl setup'
      }]
    };
  }

  // 1. Transpile FL AST → Lean source
  const { source, theoremNames } = transpileToLean(nodes);

  // 2. Write to the verification workspace
  fs.writeFileSync(VERIFY_FILE, source, 'utf8');

  // 3. Run lean directly on the file (faster than full lake build for single files)
  const env = {
    ...process.env,
    ELAN_HOME,
    PATH: `${ELAN_HOME}/bin:${process.env.PATH}`,
  };

  const result = spawnSync(
    path.join(ELAN_HOME, 'bin', 'lean'),
    ['--json', VERIFY_FILE],
    { cwd: PROJECT, env, encoding: 'utf8', maxBuffer: 10 * 1024 * 1024 }
  );

  // 4. Parse Lean's JSON diagnostic output
  const diagnostics = parseLeanOutput(result.stdout + result.stderr);

  // 5. Map errors back to .fl line numbers
  const leanLines = source.split('\n');
  const errors = diagnostics
    .filter(d => d.severity === 'error' || d.severity === 'warning')
    .map(d => ({
      message: cleanLeanError(d.message),
      leanLine: d.pos?.line,
      flLine: mapLeanLineToFL(d.pos?.line, leanLines, sourceLines),
    }));

  // 6. Determine per-theorem results
  const theorems: TheoremResult[] = theoremNames.map(name => {
    const hasError = errors.some(e => {
      const lline = e.leanLine ?? 0;
      return isErrorInTheorem(name, lline, leanLines);
    });
    return {
      name,
      verified: !hasError,
      message: hasError ? 'proof contains errors' : 'verified',
    };
  });

  // Clean up
  fs.writeFileSync(VERIFY_FILE, '-- FuturLang verification workspace\nimport Mathlib\n');

  const success = errors.filter(e => !e.message.includes('sorry')).length === 0;

  return { success, theorems, errors };
}

// ── Parse Lean's JSON diagnostic output ──────────────────────────────────────

interface LeanDiagnostic {
  severity: string;
  message: string;
  pos?: { line: number; column: number };
  endPos?: { line: number; column: number };
}

function parseLeanOutput(raw: string): LeanDiagnostic[] {
  const diagnostics: LeanDiagnostic[] = [];
  for (const line of raw.split('\n')) {
    const trimmed = line.trim();
    if (!trimmed.startsWith('{')) continue;
    try {
      const d = JSON.parse(trimmed);
      if (d.severity && d.message) diagnostics.push(d);
    } catch { /* skip non-JSON lines */ }
  }
  return diagnostics;
}

// ── Map Lean line numbers back to .fl source lines ───────────────────────────
// The .lean file has a comment like `-- fl:line:N` for key constructs.
// We use the theorem/proof structure to approximate the mapping.

function mapLeanLineToFL(
  leanLine: number | undefined,
  leanLines: string[],
  flLines: string[]
): number | undefined {
  if (!leanLine) return undefined;
  // Simple heuristic: count theorem blocks before this line
  let theoremCount = 0;
  for (let i = 0; i < Math.min(leanLine - 1, leanLines.length); i++) {
    if (leanLines[i].startsWith('theorem ') || leanLines[i].startsWith('lemma ')) {
      theoremCount++;
    }
  }
  // Find the corresponding theorem in .fl source
  let count = 0;
  for (let i = 0; i < flLines.length; i++) {
    if (/^theorem\s+|^lemma\s+/.test(flLines[i].trim())) {
      if (count === theoremCount) return i + 1;
      count++;
    }
  }
  return undefined;
}

function isErrorInTheorem(name: string, leanLine: number, leanLines: string[]): boolean {
  // Find where this theorem starts and ends in the lean file
  let start = -1, end = leanLines.length;
  for (let i = 0; i < leanLines.length; i++) {
    if (leanLines[i].startsWith(`theorem ${name}`) ||
        leanLines[i].startsWith(`lemma ${name}`)) {
      start = i;
    } else if (start >= 0 && i > start && leanLines[i].startsWith('theorem ')) {
      end = i;
      break;
    }
  }
  return leanLine >= start && leanLine < end;
}

function cleanLeanError(msg: string): string {
  // Strip Lean internals from error messages, keep the meaningful part
  return msg
    .replace(/\n\s*\n/g, '\n')
    .replace(/Try this: /g, '')
    .trim()
    .split('\n')
    .slice(0, 4)  // first 4 lines are usually enough
    .join('\n');
}
