// src/lsp-server.ts — FuturLang Language API Server
//
// An HTTP server that exposes the FL parser, type-checker, and kernel as a
// REST API.  Intended uses:
//   • VS Code extension (real-time diagnostics, hover, completions)
//   • Web playground / online editor
//   • futurchain node (validate FL programs before deployment)
//   • CI / pre-commit hooks
//
// Start:  fl lsp-server [--port 3001]
// Health: GET  /health
// Parse:  POST /parse   { source: string }
// Check:  POST /check   { source: string }
// Eval:   POST /eval    { source: string }
// Hover:  POST /hover   { source: string, line: number, col: number }

import * as http from 'http';
import { lexFL } from './parser/lexer';
import { parseLinesToAST } from './parser/parser';
import { checkFile } from './checker/checker';
import { generateRustFromAST } from './codegen/rust';
import { expandFLFile } from './parser/formal';
import * as fs from 'fs';
import * as path from 'path';

// ── Types ─────────────────────────────────────────────────────────────────────

interface ParseRequest  { source: string }
interface CheckRequest  { source: string; strict?: boolean }
interface EvalRequest   { source: string }
interface HoverRequest  { source: string; line: number; col: number }

interface Diagnostic {
  severity: 'error' | 'warning' | 'info';
  message: string;
  line?: number;
  hint?: string;
}

interface ParseResponse {
  ok: boolean;
  nodeCount: number;
  nodeTypes: string[];
  error?: string;
}

interface CheckResponse {
  ok: boolean;
  state: 'PROVED' | 'PENDING' | 'FAILED' | 'UNVERIFIED';
  theoremCount: number;
  pairedCount: number;
  diagnostics: Diagnostic[];
  reports: Array<{
    name: string;
    state: string;
    premises: string[];
    goal: string | null;
    proofSteps: number;
  }>;
}

interface HoverResponse {
  found: boolean;
  token?: string;
  kind?: string;
  docs?: string;
}

// ── Hover token database ──────────────────────────────────────────────────────

const HOVER_DOCS: Record<string, { kind: string; docs: string }> = {
  theorem:        { kind: 'block', docs: 'Declare a theorem. Paired with a `proof` block via `↔`.' },
  proof:          { kind: 'block', docs: 'Prove a theorem. Must be paired with its `theorem` block via `↔`.' },
  lemma:          { kind: 'block', docs: 'Declare a helper lemma. Paired with a `proof` block via `↔`.' },
  definition:     { kind: 'block', docs: 'Define a mathematical object or value.' },
  fn:             { kind: 'block', docs: 'Declare a function. Desugars into theorem + proof.' },
  struct:         { kind: 'block', docs: 'Declare a data structure with named fields.' },
  type:           { kind: 'block', docs: 'Declare a sum type (tagged union).' },
  program:        { kind: 'block', docs: 'Declare an on-chain FuturChain program (smart contract).' },
  account:        { kind: 'block', docs: 'Declare on-chain account state for a FuturChain program.' },
  instruction:    { kind: 'block', docs: 'Declare an instruction handler for a FuturChain program.' },
  error:          { kind: 'block', docs: 'Declare custom program error variants.' },
  assume:         { kind: 'statement', docs: 'Introduce a hypothesis into the proof context.' },
  conclude:       { kind: 'statement', docs: 'Close the proof. Must match the `declareToProve` goal.' },
  declareToProve: { kind: 'statement', docs: 'Set the proof goal (required exactly once in a theorem body).' },
  prove:          { kind: 'statement', docs: 'Derive and record an intermediate fact.' },
  apply:          { kind: 'statement', docs: 'Back-chain through a proved lemma. Makes the parent connective `→`.' },
  require:        { kind: 'statement', docs: 'Guard: returns the named program error if condition is false.' },
  emit:           { kind: 'statement', docs: 'Emit a named event recorded in the block event log.' },
  pda:            { kind: 'statement', docs: 'Derive a Program-Derived Address from seeds.' },
  cpi:            { kind: 'statement', docs: 'Queue a cross-program invocation.' },
  transfer:       { kind: 'statement', docs: 'Native token transfer between two accounts.' },
  '→':            { kind: 'connective', docs: '`→` (implies): links blocks where the next proof calls `apply()` on the current one.' },
  '↔':            { kind: 'connective', docs: '`↔` (iff): pairs a `theorem`/`lemma` with its `proof` block.' },
  '∧':            { kind: 'connective', docs: '`∧` (and): links independent blocks — next proof does not call `apply()`.' },
  '∨':            { kind: 'connective', docs: '`∨` (or): disjunctive — either block suffices (emits warning, not yet validated).' },
  '∈':            { kind: 'operator', docs: '`∈`: membership. Used in type annotations (`x ∈ Nat`) and membership proofs.' },
  '∀':            { kind: 'operator', docs: '`∀`: universal quantifier. `∀ x ∈ A, P(x)`.' },
  '∃':            { kind: 'operator', docs: '`∃`: existential quantifier. `∃ x ∈ A, P(x)`.' },
  mut:            { kind: 'modifier', docs: '`mut`: marks an instruction account parameter as mutable.' },
  signer:         { kind: 'modifier', docs: '`signer`: marks an instruction account parameter as required signer.' },
  init:           { kind: 'modifier', docs: '`init`: marks an account as newly created in this instruction.' },
  Address:        { kind: 'type', docs: '`Address` ([u8; 32]): a 32-byte public key / account address.' },
  TokenAmount:    { kind: 'type', docs: '`TokenAmount` (u64): a token quantity in the chain\'s native denomination.' },
  Hash:           { kind: 'type', docs: '`Hash` ([u8; 32]): a SHA-256 hash output.' },
  Signature:      { kind: 'type', docs: '`Signature` ([u8; 64]): an Ed25519 signature.' },
  Slot:           { kind: 'type', docs: '`Slot` (u64): a monotonic block slot number.' },
  Nat:            { kind: 'type', docs: '`Nat` (u64): natural number (≥ 0).' },
  Bool:           { kind: 'type', docs: '`Bool`: boolean. Compiles to Rust `bool`.' },
};

// ── Request handling ──────────────────────────────────────────────────────────

function handleParse(body: ParseRequest): ParseResponse {
  try {
    const lines = lexFL(body.source);
    const ast = parseLinesToAST(lines, { desugarFns: false });
    return {
      ok: true,
      nodeCount: ast.length,
      nodeTypes: ast.map(n => n.type),
    };
  } catch (e: any) {
    return { ok: false, nodeCount: 0, nodeTypes: [], error: e.message };
  }
}

function handleCheck(body: CheckRequest): CheckResponse {
  try {
    const lines = lexFL(body.source);
    const ast = parseLinesToAST(lines, { desugarFns: true });
    const report = checkFile(ast, { strict: body.strict ?? false });

    const diagnostics: Diagnostic[] = report.diagnostics.map(d => ({
      severity: d.severity as 'error' | 'warning' | 'info',
      message: d.message,
      hint: d.hint,
    }));

    const reports = report.reports.map(r => ({
      name: r.name,
      state: r.state,
      premises: r.premises,
      goal: r.goal ?? null,
      proofSteps: r.proofSteps.length,
    }));

    return {
      ok: report.state === 'PROVED',
      state: report.state as CheckResponse['state'],
      theoremCount: report.theoremCount,
      pairedCount: report.pairedCount,
      diagnostics,
      reports,
    };
  } catch (e: any) {
    return {
      ok: false,
      state: 'FAILED',
      theoremCount: 0,
      pairedCount: 0,
      diagnostics: [{ severity: 'error', message: e.message }],
      reports: [],
    };
  }
}

function handleHover(body: HoverRequest): HoverResponse {
  try {
    const lines = body.source.split('\n');
    const targetLine = lines[body.line] ?? '';
    // Walk the line to find what word/symbol is at col
    const before = targetLine.slice(0, body.col);
    const after = targetLine.slice(body.col);
    const tokenBefore = before.match(/[\w∀∃∈∧∨→↔]+$/)?.[0] ?? '';
    const tokenAfter  = after.match(/^[\w∀∃∈∧∨→↔]*/)?.[0] ?? '';
    const token = tokenBefore + tokenAfter;
    if (!token) return { found: false };
    const doc = HOVER_DOCS[token];
    if (!doc) return { found: true, token, kind: 'identifier', docs: `\`${token}\`` };
    return { found: true, token, kind: doc.kind, docs: doc.docs };
  } catch {
    return { found: false };
  }
}

function handleEval(body: EvalRequest): { ok: boolean; output?: string; error?: string } {
  // Write source to a temp file and run through the checker
  const tmpFile = path.join(require('os').tmpdir(), `fl-eval-${Date.now()}.fl`);
  try {
    fs.writeFileSync(tmpFile, body.source, 'utf8');
    const source = expandFLFile(tmpFile);
    const ast = parseLinesToAST(lexFL(source), { desugarFns: true });
    const report = checkFile(ast, { strict: false });
    const lines: string[] = [];
    for (const r of report.reports) {
      const icon = r.state === 'PROVED' ? '✓' : r.state === 'PENDING' ? '~' : '✗';
      lines.push(`${icon} ${r.name}  ${r.state}`);
    }
    lines.push(`Result: ${report.state}`);
    return { ok: true, output: lines.join('\n') };
  } catch (e: any) {
    return { ok: false, error: e.message };
  } finally {
    try { fs.unlinkSync(tmpFile); } catch { /* ignore */ }
  }
}

// ── HTTP server ───────────────────────────────────────────────────────────────

function readBody(req: http.IncomingMessage): Promise<string> {
  return new Promise((resolve, reject) => {
    let data = '';
    req.on('data', chunk => { data += chunk; });
    req.on('end', () => resolve(data));
    req.on('error', reject);
  });
}

function json(res: http.ServerResponse, status: number, data: unknown) {
  const body = JSON.stringify(data, null, 2);
  res.writeHead(status, {
    'Content-Type': 'application/json',
    'Access-Control-Allow-Origin': '*',
    'Access-Control-Allow-Headers': 'Content-Type',
    'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
  });
  res.end(body);
}

export async function startLspServer(port: number): Promise<void> {
  const server = http.createServer(async (req, res) => {
    if (req.method === 'OPTIONS') { json(res, 204, {}); return; }

    const url = req.url ?? '/';

    // ── GET /health ──────────────────────────────────────────────────────────
    if (req.method === 'GET' && url === '/health') {
      json(res, 200, { status: 'ok', version: '0.1.0', engine: 'futurlang-lsp' });
      return;
    }

    // ── GET /keywords ────────────────────────────────────────────────────────
    if (req.method === 'GET' && url === '/keywords') {
      json(res, 200, { keywords: Object.keys(HOVER_DOCS) });
      return;
    }

    if (req.method !== 'POST') { json(res, 405, { error: 'Method not allowed' }); return; }

    let rawBody: string;
    try { rawBody = await readBody(req); }
    catch { json(res, 400, { error: 'Failed to read request body' }); return; }

    let body: unknown;
    try { body = JSON.parse(rawBody); }
    catch { json(res, 400, { error: 'Invalid JSON' }); return; }

    // ── POST /parse ──────────────────────────────────────────────────────────
    if (url === '/parse') {
      const req = body as ParseRequest;
      if (typeof req.source !== 'string') { json(res, 400, { error: '`source` string required' }); return; }
      json(res, 200, handleParse(req));
      return;
    }

    // ── POST /check ──────────────────────────────────────────────────────────
    if (url === '/check') {
      const req = body as CheckRequest;
      if (typeof req.source !== 'string') { json(res, 400, { error: '`source` string required' }); return; }
      json(res, 200, handleCheck(req));
      return;
    }

    // ── POST /eval ───────────────────────────────────────────────────────────
    if (url === '/eval') {
      const req = body as EvalRequest;
      if (typeof req.source !== 'string') { json(res, 400, { error: '`source` string required' }); return; }
      json(res, 200, handleEval(req));
      return;
    }

    // ── POST /hover ──────────────────────────────────────────────────────────
    if (url === '/hover') {
      const req = body as HoverRequest;
      if (typeof req.source !== 'string' || typeof req.line !== 'number') {
        json(res, 400, { error: '`source`, `line`, `col` required' });
        return;
      }
      json(res, 200, handleHover(req));
      return;
    }

    // ── POST /rust ───────────────────────────────────────────────────────────
    if (url === '/rust') {
      const req = body as ParseRequest;
      if (typeof req.source !== 'string') { json(res, 400, { error: '`source` string required' }); return; }
      try {
        const ast = parseLinesToAST(lexFL(req.source), { desugarFns: false });
        const rust = generateRustFromAST(ast, 'api');
        json(res, 200, { ok: true, rust });
      } catch (e: any) {
        json(res, 200, { ok: false, error: e.message });
      }
      return;
    }

    json(res, 404, { error: `Unknown endpoint: ${url}` });
  });

  return new Promise((resolve) => {
    server.listen(port, '127.0.0.1', () => {
      console.log(`\nFuturLang Language Server`);
      console.log(`  Listening on http://127.0.0.1:${port}`);
      console.log(`\n  Endpoints:`);
      console.log(`    GET  /health    — health check`);
      console.log(`    GET  /keywords  — all documented keywords`);
      console.log(`    POST /parse     — parse FL source → AST summary`);
      console.log(`    POST /check     — kernel-check FL source → proof status`);
      console.log(`    POST /eval      — evaluate FL source → checker output`);
      console.log(`    POST /hover     — token docs at (line, col)`);
      console.log(`    POST /rust      — transpile FL source → Rust`);
      console.log(`\n  Press Ctrl+C to stop.\n`);
      resolve();
    });
  });
}
