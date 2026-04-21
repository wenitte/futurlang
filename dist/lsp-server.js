"use strict";
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
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.startLspServer = startLspServer;
const http = __importStar(require("http"));
const lexer_1 = require("./parser/lexer");
const parser_1 = require("./parser/parser");
const checker_1 = require("./checker/checker");
const rust_1 = require("./codegen/rust");
const formal_1 = require("./parser/formal");
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
// ── Hover token database ──────────────────────────────────────────────────────
const HOVER_DOCS = {
    theorem: { kind: 'block', docs: 'Declare a theorem. Paired with a `proof` block via `↔`.' },
    proof: { kind: 'block', docs: 'Prove a theorem. Must be paired with its `theorem` block via `↔`.' },
    lemma: { kind: 'block', docs: 'Declare a helper lemma. Paired with a `proof` block via `↔`.' },
    definition: { kind: 'block', docs: 'Define a mathematical object or value.' },
    fn: { kind: 'block', docs: 'Declare a function. Desugars into theorem + proof.' },
    struct: { kind: 'block', docs: 'Declare a data structure with named fields.' },
    type: { kind: 'block', docs: 'Declare a sum type (tagged union).' },
    program: { kind: 'block', docs: 'Declare an on-chain FuturChain program (smart contract).' },
    account: { kind: 'block', docs: 'Declare on-chain account state for a FuturChain program.' },
    instruction: { kind: 'block', docs: 'Declare an instruction handler for a FuturChain program.' },
    error: { kind: 'block', docs: 'Declare custom program error variants.' },
    assume: { kind: 'statement', docs: 'Introduce a hypothesis into the proof context.' },
    conclude: { kind: 'statement', docs: 'Close the proof. Must match the `declareToProve` goal.' },
    declareToProve: { kind: 'statement', docs: 'Set the proof goal (required exactly once in a theorem body).' },
    prove: { kind: 'statement', docs: 'Derive and record an intermediate fact.' },
    apply: { kind: 'statement', docs: 'Back-chain through a proved lemma. Makes the parent connective `→`.' },
    require: { kind: 'statement', docs: 'Guard: returns the named program error if condition is false.' },
    emit: { kind: 'statement', docs: 'Emit a named event recorded in the block event log.' },
    pda: { kind: 'statement', docs: 'Derive a Program-Derived Address from seeds.' },
    cpi: { kind: 'statement', docs: 'Queue a cross-program invocation.' },
    transfer: { kind: 'statement', docs: 'Native token transfer between two accounts.' },
    '→': { kind: 'connective', docs: '`→` (implies): links blocks where the next proof calls `apply()` on the current one.' },
    '↔': { kind: 'connective', docs: '`↔` (iff): pairs a `theorem`/`lemma` with its `proof` block.' },
    '∧': { kind: 'connective', docs: '`∧` (and): links independent blocks — next proof does not call `apply()`.' },
    '∨': { kind: 'connective', docs: '`∨` (or): disjunctive — either block suffices (emits warning, not yet validated).' },
    '∈': { kind: 'operator', docs: '`∈`: membership. Used in type annotations (`x ∈ Nat`) and membership proofs.' },
    '∀': { kind: 'operator', docs: '`∀`: universal quantifier. `∀ x ∈ A, P(x)`.' },
    '∃': { kind: 'operator', docs: '`∃`: existential quantifier. `∃ x ∈ A, P(x)`.' },
    mut: { kind: 'modifier', docs: '`mut`: marks an instruction account parameter as mutable.' },
    signer: { kind: 'modifier', docs: '`signer`: marks an instruction account parameter as required signer.' },
    init: { kind: 'modifier', docs: '`init`: marks an account as newly created in this instruction.' },
    Address: { kind: 'type', docs: '`Address` ([u8; 32]): a 32-byte public key / account address.' },
    TokenAmount: { kind: 'type', docs: '`TokenAmount` (u64): a token quantity in the chain\'s native denomination.' },
    Hash: { kind: 'type', docs: '`Hash` ([u8; 32]): a SHA-256 hash output.' },
    Signature: { kind: 'type', docs: '`Signature` ([u8; 64]): an Ed25519 signature.' },
    Slot: { kind: 'type', docs: '`Slot` (u64): a monotonic block slot number.' },
    Nat: { kind: 'type', docs: '`Nat` (u64): natural number (≥ 0).' },
    Bool: { kind: 'type', docs: '`Bool`: boolean. Compiles to Rust `bool`.' },
};
// ── Request handling ──────────────────────────────────────────────────────────
function handleParse(body) {
    try {
        const lines = (0, lexer_1.lexFL)(body.source);
        const ast = (0, parser_1.parseLinesToAST)(lines, { desugarFns: false });
        return {
            ok: true,
            nodeCount: ast.length,
            nodeTypes: ast.map(n => n.type),
        };
    }
    catch (e) {
        return { ok: false, nodeCount: 0, nodeTypes: [], error: e.message };
    }
}
function handleCheck(body) {
    try {
        const lines = (0, lexer_1.lexFL)(body.source);
        const ast = (0, parser_1.parseLinesToAST)(lines, { desugarFns: true });
        const report = (0, checker_1.checkFile)(ast, { strict: body.strict ?? false });
        const diagnostics = report.diagnostics.map(d => ({
            severity: d.severity,
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
            state: report.state,
            theoremCount: report.theoremCount,
            pairedCount: report.pairedCount,
            diagnostics,
            reports,
        };
    }
    catch (e) {
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
function handleHover(body) {
    try {
        const lines = body.source.split('\n');
        const targetLine = lines[body.line] ?? '';
        // Walk the line to find what word/symbol is at col
        const before = targetLine.slice(0, body.col);
        const after = targetLine.slice(body.col);
        const tokenBefore = before.match(/[\w∀∃∈∧∨→↔]+$/)?.[0] ?? '';
        const tokenAfter = after.match(/^[\w∀∃∈∧∨→↔]*/)?.[0] ?? '';
        const token = tokenBefore + tokenAfter;
        if (!token)
            return { found: false };
        const doc = HOVER_DOCS[token];
        if (!doc)
            return { found: true, token, kind: 'identifier', docs: `\`${token}\`` };
        return { found: true, token, kind: doc.kind, docs: doc.docs };
    }
    catch {
        return { found: false };
    }
}
function handleEval(body) {
    // Write source to a temp file and run through the checker
    const tmpFile = path.join(require('os').tmpdir(), `fl-eval-${Date.now()}.fl`);
    try {
        fs.writeFileSync(tmpFile, body.source, 'utf8');
        const source = (0, formal_1.expandFLFile)(tmpFile);
        const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source), { desugarFns: true });
        const report = (0, checker_1.checkFile)(ast, { strict: false });
        const lines = [];
        for (const r of report.reports) {
            const icon = r.state === 'PROVED' ? '✓' : r.state === 'PENDING' ? '~' : '✗';
            lines.push(`${icon} ${r.name}  ${r.state}`);
        }
        lines.push(`Result: ${report.state}`);
        return { ok: true, output: lines.join('\n') };
    }
    catch (e) {
        return { ok: false, error: e.message };
    }
    finally {
        try {
            fs.unlinkSync(tmpFile);
        }
        catch { /* ignore */ }
    }
}
// ── HTTP server ───────────────────────────────────────────────────────────────
function readBody(req) {
    return new Promise((resolve, reject) => {
        let data = '';
        req.on('data', chunk => { data += chunk; });
        req.on('end', () => resolve(data));
        req.on('error', reject);
    });
}
function json(res, status, data) {
    const body = JSON.stringify(data, null, 2);
    res.writeHead(status, {
        'Content-Type': 'application/json',
        'Access-Control-Allow-Origin': '*',
        'Access-Control-Allow-Headers': 'Content-Type',
        'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
    });
    res.end(body);
}
async function startLspServer(port) {
    const server = http.createServer(async (req, res) => {
        if (req.method === 'OPTIONS') {
            json(res, 204, {});
            return;
        }
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
        if (req.method !== 'POST') {
            json(res, 405, { error: 'Method not allowed' });
            return;
        }
        let rawBody;
        try {
            rawBody = await readBody(req);
        }
        catch {
            json(res, 400, { error: 'Failed to read request body' });
            return;
        }
        let body;
        try {
            body = JSON.parse(rawBody);
        }
        catch {
            json(res, 400, { error: 'Invalid JSON' });
            return;
        }
        // ── POST /parse ──────────────────────────────────────────────────────────
        if (url === '/parse') {
            const req = body;
            if (typeof req.source !== 'string') {
                json(res, 400, { error: '`source` string required' });
                return;
            }
            json(res, 200, handleParse(req));
            return;
        }
        // ── POST /check ──────────────────────────────────────────────────────────
        if (url === '/check') {
            const req = body;
            if (typeof req.source !== 'string') {
                json(res, 400, { error: '`source` string required' });
                return;
            }
            json(res, 200, handleCheck(req));
            return;
        }
        // ── POST /eval ───────────────────────────────────────────────────────────
        if (url === '/eval') {
            const req = body;
            if (typeof req.source !== 'string') {
                json(res, 400, { error: '`source` string required' });
                return;
            }
            json(res, 200, handleEval(req));
            return;
        }
        // ── POST /hover ──────────────────────────────────────────────────────────
        if (url === '/hover') {
            const req = body;
            if (typeof req.source !== 'string' || typeof req.line !== 'number') {
                json(res, 400, { error: '`source`, `line`, `col` required' });
                return;
            }
            json(res, 200, handleHover(req));
            return;
        }
        // ── POST /rust ───────────────────────────────────────────────────────────
        if (url === '/rust') {
            const req = body;
            if (typeof req.source !== 'string') {
                json(res, 400, { error: '`source` string required' });
                return;
            }
            try {
                const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(req.source), { desugarFns: false });
                const rust = (0, rust_1.generateRustFromAST)(ast, 'api');
                json(res, 200, { ok: true, rust });
            }
            catch (e) {
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
