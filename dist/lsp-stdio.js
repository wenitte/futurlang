"use strict";
// src/lsp-stdio.ts — FuturLang LSP server (JSON-RPC over stdio)
//
// VS Code launches this as a child process and talks to it via stdin/stdout.
// Protocol: Language Server Protocol 3.17 (Content-Length framing + JSON-RPC).
Object.defineProperty(exports, "__esModule", { value: true });
const node_1 = require("vscode-languageserver/node");
const vscode_languageserver_textdocument_1 = require("vscode-languageserver-textdocument");
const lexer_1 = require("./parser/lexer");
const parser_1 = require("./parser/parser");
const checker_1 = require("./checker/checker");
// ── Connection setup ──────────────────────────────────────────────────────────
// Use explicit stdin/stdout streams — no --stdio flag needed at launch.
const connection = (0, node_1.createConnection)(new node_1.StreamMessageReader(process.stdin), new node_1.StreamMessageWriter(process.stdout));
const documents = new node_1.TextDocuments(vscode_languageserver_textdocument_1.TextDocument);
connection.onInitialize((_params) => ({
    capabilities: {
        textDocumentSync: node_1.TextDocumentSyncKind.Incremental,
        hoverProvider: true,
        completionProvider: { resolveProvider: false, triggerCharacters: ['(', ' '] },
    },
}));
connection.onInitialized(() => {
    connection.client.register(node_1.DidChangeConfigurationNotification.type, undefined);
});
// ── Diagnostics ───────────────────────────────────────────────────────────────
function validateDocument(doc) {
    const source = doc.getText();
    const diags = [];
    try {
        const lines = (0, lexer_1.lexFL)(source);
        const ast = (0, parser_1.parseLinesToAST)(lines, { desugarFns: true });
        const report = (0, checker_1.checkFile)(ast, { strict: false });
        // Map checker diagnostics to LSP diagnostics
        for (const r of report.reports) {
            for (const d of r.diagnostics) {
                if (d.severity !== 'error')
                    continue;
                // We don't have line numbers from the checker yet — put at top of file
                diags.push({
                    severity: node_1.DiagnosticSeverity.Error,
                    range: { start: node_1.Position.create(0, 0), end: node_1.Position.create(0, 0) },
                    message: `[${r.name}] ${d.message}${d.hint ? ` — ${d.hint}` : ''}`,
                    source: 'futurlang',
                });
            }
        }
        // Top-level diagnostics
        for (const d of report.diagnostics) {
            if (d.severity !== 'error')
                continue;
            diags.push({
                severity: node_1.DiagnosticSeverity.Error,
                range: { start: node_1.Position.create(0, 0), end: node_1.Position.create(0, 0) },
                message: d.message,
                source: 'futurlang',
            });
        }
        // Missing connective errors bubble up from the parser as thrown errors,
        // so if we reached here the file is structurally valid.
        if (report.state === 'FAILED' && diags.length === 0) {
            diags.push({
                severity: node_1.DiagnosticSeverity.Error,
                range: { start: node_1.Position.create(0, 0), end: node_1.Position.create(0, 0) },
                message: 'Proof failed — check connectives and proof structure',
                source: 'futurlang',
            });
        }
    }
    catch (e) {
        // Parse error — try to find the approximate line
        const msg = e.message ?? String(e);
        const lineHint = extractLineHint(source, msg);
        diags.push({
            severity: node_1.DiagnosticSeverity.Error,
            range: { start: node_1.Position.create(lineHint, 0), end: node_1.Position.create(lineHint, 999) },
            message: msg,
            source: 'futurlang',
        });
    }
    connection.sendDiagnostics({ uri: doc.uri, diagnostics: diags });
}
/** Heuristic: if the error mentions a known block name, find it in source */
function extractLineHint(source, msg) {
    const nameMatch = msg.match(/['`"](\w+)['`"]/);
    if (nameMatch) {
        const lines = source.split('\n');
        for (let i = 0; i < lines.length; i++) {
            if (lines[i].includes(nameMatch[1]))
                return i;
        }
    }
    return 0;
}
documents.onDidChangeContent(change => validateDocument(change.document));
documents.onDidOpen(e => validateDocument(e.document));
// ── Hover ─────────────────────────────────────────────────────────────────────
const HOVER_DB = {
    theorem: '**theorem** — Declare a theorem.\nPaired with a `proof` block via `↔`.',
    proof: '**proof** — Prove a theorem.\nMust be paired with its `theorem` via `↔`.',
    lemma: '**lemma** — Declare a helper lemma.\nPaired with a `proof` block via `↔`.',
    definition: '**definition** — Define a mathematical object.',
    fn: '**fn** — Declare a function. Desugars into theorem + proof.',
    struct: '**struct** — Declare a data structure.',
    type: '**type** — Declare a sum type (tagged union).',
    program: '**program** — Declare an on-chain FuturChain program (smart contract).',
    account: '**account** — On-chain account state for a FuturChain program.',
    instruction: '**instruction** — Instruction handler inside a `program` block.',
    error: '**error** — Custom program error variants.',
    assume: '**assume(P)** — Introduce hypothesis `P` into the proof context.',
    conclude: '**conclude(P)** — Close the proof. Must match `declareToProve` goal.',
    declareToProve: '**declareToProve(P)** — Set the proof goal (required exactly once).',
    prove: '**prove(P)** — Derive and record an intermediate fact.',
    apply: '**apply(Name)** — Back-chain through proved lemma `Name`.\nMakes parent connective `→`.',
    require: '**require(cond, Err)** — Guard: returns `Err` if `cond` is false.',
    emit: '**emit(Event, fields)** — Emit a named event recorded in the block log.',
    pda: '**pda([seeds])** — Derive a Program-Derived Address from seeds.',
    cpi: '**cpi(program, ix, accounts)** — Cross-program invocation.',
    transfer: '**transfer(from, to, amount)** — Native token transfer within an instruction.',
    induction: '**induction(n)** — Structural induction. Requires `base:` and `step:` cases.',
    match: '**match value { ... }** — Case split on a sum type or list.',
    setVar: '**setVar(x: T)** or **let x = v** — Introduce a bound variable.',
    intro: '**intro(x: T)** — Strip an implication antecedent.',
    rewrite: '**rewrite(h)** — Substitute equals using hypothesis `h`.',
    exact: '**exact(e)** — Close goal directly with expression `e`.',
    obtain: '**obtain(x, ∃ y ∈ S, P)** — Destructure an existential.',
    mut: '**mut** — Marks an instruction account as mutable.',
    signer: '**signer** — Marks an instruction account as required signer.',
    init: '**init** — Marks an account as newly created in this instruction.',
    Address: '`Address` — 32-byte public key / account address (`[u8; 32]`).',
    TokenAmount: '`TokenAmount` — native token quantity (`u64`).',
    Hash: '`Hash` — SHA-256 output (`[u8; 32]`).',
    Signature: '`Signature` — Ed25519 signature (`[u8; 64]`).',
    Slot: '`Slot` — monotonic block slot number (`u64`).',
    Nat: '`Nat` — natural number, ≥ 0 (`u64`).',
    Bool: '`Bool` — boolean (`bool`).',
    '→': '`→` **(implies / sequences)**: next block calls `apply()` on current.',
    '↔': '`↔` **(iff / pairs)**: pairs a `theorem`/`lemma` with its `proof`.',
    '∧': '`∧` **(and / independent)**: next block does **not** call `apply()`.',
    '∨': '`∨` **(or / disjunctive)**: either block suffices.',
    '∈': '`∈` — membership. Used in type annotations and membership proofs.',
    '∀': '`∀` — universal quantifier. `∀ x ∈ A, P(x)`.',
    '∃': '`∃` — existential quantifier. `∃ x ∈ A, P(x)`.',
};
connection.onHover((params) => {
    const doc = documents.get(params.textDocument.uri);
    if (!doc)
        return null;
    const line = doc.getText({
        start: { line: params.position.line, character: 0 },
        end: { line: params.position.line, character: 999 },
    });
    const col = params.position.character;
    const before = line.slice(0, col).match(/[\w∀∃∈∧∨→↔ℕ]+$/)?.[0] ?? '';
    const after = line.slice(col).match(/^[\w∀∃∈∧∨→↔ℕ]*/)?.[0] ?? '';
    const token = before + after;
    if (!token)
        return null;
    const doc_text = HOVER_DB[token];
    if (!doc_text)
        return null;
    return {
        contents: { kind: node_1.MarkupKind.Markdown, value: doc_text },
    };
});
// ── Completions ───────────────────────────────────────────────────────────────
const COMPLETIONS = [
    // Top-level blocks
    { label: 'theorem', kind: node_1.CompletionItemKind.Keyword, insertText: 'theorem ${1:Name}() {\n  assume(${2:P}) →\n  declareToProve(${3:Q})\n} ↔\n\nproof ${1:Name}() {\n  conclude(${3:Q})\n}', insertTextFormat: 2 },
    { label: 'proof', kind: node_1.CompletionItemKind.Keyword, insertText: 'proof ${1:Name}() {\n  conclude(${2:P})\n}', insertTextFormat: 2 },
    { label: 'lemma', kind: node_1.CompletionItemKind.Keyword, insertText: 'lemma ${1:Name}() {\n  assume(${2:P}) →\n  declareToProve(${3:Q})\n} ↔\n\nproof ${1:Name}() {\n  conclude(${3:Q})\n}', insertTextFormat: 2 },
    { label: 'fn', kind: node_1.CompletionItemKind.Keyword, insertText: 'fn ${1:name}(${2:x} ∈ ${3:Nat}) -> ${4:Nat} {\n  conclude(${5:x})\n}', insertTextFormat: 2 },
    { label: 'struct', kind: node_1.CompletionItemKind.Keyword, insertText: 'struct ${1:Name} {\n  ${2:field} ∈ ${3:Nat},\n}', insertTextFormat: 2 },
    { label: 'definition', kind: node_1.CompletionItemKind.Keyword },
    // Blockchain blocks
    { label: 'program', kind: node_1.CompletionItemKind.Keyword, insertText: 'program ${1:Name} {\n\n  account ${2:State} {\n    ${3:field} ∈ ${4:TokenAmount},\n  } →\n\n  instruction ${5:init}(\n    authority: mut signer ∈ ${2:State},\n  ) {\n    // ...\n  }\n\n}', insertTextFormat: 2 },
    { label: 'account', kind: node_1.CompletionItemKind.Keyword, insertText: 'account ${1:Name} {\n  ${2:field} ∈ ${3:TokenAmount},\n}', insertTextFormat: 2 },
    { label: 'instruction', kind: node_1.CompletionItemKind.Keyword, insertText: 'instruction ${1:name}(\n  ${2:authority}: mut signer ∈ ${3:State},\n) {\n  require(${4:cond}, ${5:Error})\n}', insertTextFormat: 2 },
    { label: 'error', kind: node_1.CompletionItemKind.Keyword, insertText: 'error ${1:Name} {\n  | ${2:Variant}("${3:message}")\n}', insertTextFormat: 2 },
    // Proof statements
    { label: 'assume', kind: node_1.CompletionItemKind.Function, insertText: 'assume(${1:P})', insertTextFormat: 2 },
    { label: 'conclude', kind: node_1.CompletionItemKind.Function, insertText: 'conclude(${1:P})', insertTextFormat: 2 },
    { label: 'declareToProve', kind: node_1.CompletionItemKind.Function, insertText: 'declareToProve(${1:P})', insertTextFormat: 2 },
    { label: 'prove', kind: node_1.CompletionItemKind.Function, insertText: 'prove(${1:P})', insertTextFormat: 2 },
    { label: 'apply', kind: node_1.CompletionItemKind.Function, insertText: 'apply(${1:Lemma})', insertTextFormat: 2 },
    // Blockchain statements
    { label: 'require', kind: node_1.CompletionItemKind.Function, insertText: 'require(${1:condition}, ${2:Error})', insertTextFormat: 2 },
    { label: 'emit', kind: node_1.CompletionItemKind.Function, insertText: 'emit(${1:EventName}, ${2:field}: ${3:value})', insertTextFormat: 2 },
    { label: 'transfer', kind: node_1.CompletionItemKind.Function, insertText: 'transfer(${1:from}, ${2:to}, ${3:amount})', insertTextFormat: 2 },
    { label: 'pda', kind: node_1.CompletionItemKind.Function, insertText: 'let ${1:addr} = pda([${2:seed}])', insertTextFormat: 2 },
    { label: 'cpi', kind: node_1.CompletionItemKind.Function, insertText: 'cpi(${1:program_id}, ${2:instruction}, [${3:accounts}])', insertTextFormat: 2 },
    // Types
    { label: 'Address', kind: node_1.CompletionItemKind.TypeParameter },
    { label: 'TokenAmount', kind: node_1.CompletionItemKind.TypeParameter },
    { label: 'Hash', kind: node_1.CompletionItemKind.TypeParameter },
    { label: 'Signature', kind: node_1.CompletionItemKind.TypeParameter },
    { label: 'Slot', kind: node_1.CompletionItemKind.TypeParameter },
    { label: 'Nat', kind: node_1.CompletionItemKind.TypeParameter },
    { label: 'Bool', kind: node_1.CompletionItemKind.TypeParameter },
    { label: 'String', kind: node_1.CompletionItemKind.TypeParameter },
    { label: 'List', kind: node_1.CompletionItemKind.TypeParameter, insertText: 'List(${1:Nat})', insertTextFormat: 2 },
];
connection.onCompletion((_pos) => COMPLETIONS);
// ── Start ─────────────────────────────────────────────────────────────────────
documents.listen(connection);
connection.listen();
