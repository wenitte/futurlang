// src/lsp-stdio.ts — FuturLang LSP server (JSON-RPC over stdio)
//
// VS Code launches this as a child process and talks to it via stdin/stdout.
// Protocol: Language Server Protocol 3.17 (Content-Length framing + JSON-RPC).

import {
  createConnection,
  TextDocuments,
  ProposedFeatures,
  InitializeParams,
  DidChangeConfigurationNotification,
  CompletionItem,
  CompletionItemKind,
  TextDocumentPositionParams,
  TextDocumentSyncKind,
  InitializeResult,
  Diagnostic,
  DiagnosticSeverity,
  Hover,
  MarkupKind,
  Position,
  StreamMessageReader,
  StreamMessageWriter,
} from 'vscode-languageserver/node';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { lexFL } from './parser/lexer';
import { parseLinesToAST } from './parser/parser';
import { checkFile } from './checker/checker';

// ── Connection setup ──────────────────────────────────────────────────────────
// Use explicit stdin/stdout streams — no --stdio flag needed at launch.

const connection = createConnection(
  new StreamMessageReader(process.stdin),
  new StreamMessageWriter(process.stdout),
);
const documents  = new TextDocuments(TextDocument);

connection.onInitialize((_params: InitializeParams): InitializeResult => ({
  capabilities: {
    textDocumentSync: TextDocumentSyncKind.Incremental,
    hoverProvider:    true,
    completionProvider: { resolveProvider: false, triggerCharacters: ['(', ' '] },
  },
}));

connection.onInitialized(() => {
  connection.client.register(DidChangeConfigurationNotification.type, undefined);
});

// ── Diagnostics ───────────────────────────────────────────────────────────────

function validateDocument(doc: TextDocument): void {
  const source = doc.getText();
  const diags: Diagnostic[] = [];

  try {
    const lines = lexFL(source);
    const ast   = parseLinesToAST(lines, { desugarFns: true });
    const report = checkFile(ast, { strict: false });

    // Map checker diagnostics to LSP diagnostics
    for (const r of report.reports) {
      for (const d of r.diagnostics) {
        if (d.severity !== 'error') continue;
        // We don't have line numbers from the checker yet — put at top of file
        diags.push({
          severity: DiagnosticSeverity.Error,
          range: { start: Position.create(0, 0), end: Position.create(0, 0) },
          message: `[${r.name}] ${d.message}${d.hint ? ` — ${d.hint}` : ''}`,
          source: 'futurlang',
        });
      }
    }

    // Top-level diagnostics
    for (const d of report.diagnostics) {
      if (d.severity !== 'error') continue;
      diags.push({
        severity: DiagnosticSeverity.Error,
        range: { start: Position.create(0, 0), end: Position.create(0, 0) },
        message: d.message,
        source: 'futurlang',
      });
    }

    // Missing connective errors bubble up from the parser as thrown errors,
    // so if we reached here the file is structurally valid.
    if (report.state === 'FAILED' && diags.length === 0) {
      diags.push({
        severity: DiagnosticSeverity.Error,
        range: { start: Position.create(0, 0), end: Position.create(0, 0) },
        message: 'Proof failed — check connectives and proof structure',
        source: 'futurlang',
      });
    }

  } catch (e: any) {
    // Parse error — try to find the approximate line
    const msg: string = e.message ?? String(e);
    const lineHint = extractLineHint(source, msg);
    diags.push({
      severity: DiagnosticSeverity.Error,
      range: { start: Position.create(lineHint, 0), end: Position.create(lineHint, 999) },
      message: msg,
      source: 'futurlang',
    });
  }

  connection.sendDiagnostics({ uri: doc.uri, diagnostics: diags });
}

/** Heuristic: if the error mentions a known block name, find it in source */
function extractLineHint(source: string, msg: string): number {
  const nameMatch = msg.match(/['`"](\w+)['`"]/);
  if (nameMatch) {
    const lines = source.split('\n');
    for (let i = 0; i < lines.length; i++) {
      if (lines[i].includes(nameMatch[1])) return i;
    }
  }
  return 0;
}

documents.onDidChangeContent(change => validateDocument(change.document));
documents.onDidOpen(e => validateDocument(e.document));

// ── Hover ─────────────────────────────────────────────────────────────────────

const HOVER_DB: Record<string, string> = {
  theorem:        '**theorem** — Declare a theorem.\nPaired with a `proof` block via `↔`.',
  proof:          '**proof** — Prove a theorem.\nMust be paired with its `theorem` via `↔`.',
  lemma:          '**lemma** — Declare a helper lemma.\nPaired with a `proof` block via `↔`.',
  definition:     '**definition** — Define a mathematical object.',
  fn:             '**fn** — Declare a function. Desugars into theorem + proof.',
  struct:         '**struct** — Declare a data structure.',
  type:           '**type** — Declare a sum type (tagged union).',
  program:        '**program** — Declare an on-chain FuturChain program (smart contract).',
  account:        '**account** — On-chain account state for a FuturChain program.',
  instruction:    '**instruction** — Instruction handler inside a `program` block.',
  error:          '**error** — Custom program error variants.',
  assume:         '**assume(P)** — Introduce hypothesis `P` into the proof context.',
  conclude:       '**conclude(P)** — Close the proof. Must match `declareToProve` goal.',
  declareToProve: '**declareToProve(P)** — Set the proof goal (required exactly once).',
  prove:          '**prove(P)** — Derive and record an intermediate fact.',
  apply:          '**apply(Name)** — Back-chain through proved lemma `Name`.\nMakes parent connective `→`.',
  require:        '**require(cond, Err)** — Guard: returns `Err` if `cond` is false.',
  emit:           '**emit(Event, fields)** — Emit a named event recorded in the block log.',
  pda:            '**pda([seeds])** — Derive a Program-Derived Address from seeds.',
  cpi:            '**cpi(program, ix, accounts)** — Cross-program invocation.',
  transfer:       '**transfer(from, to, amount)** — Native token transfer within an instruction.',
  induction:      '**induction(n)** — Structural induction. Requires `base:` and `step:` cases.',
  match:          '**match value { ... }** — Case split on a sum type or list.',
  setVar:         '**setVar(x: T)** or **let x = v** — Introduce a bound variable.',
  intro:          '**intro(x: T)** — Strip an implication antecedent.',
  rewrite:        '**rewrite(h)** — Substitute equals using hypothesis `h`.',
  exact:          '**exact(e)** — Close goal directly with expression `e`.',
  obtain:         '**obtain(x, ∃ y ∈ S, P)** — Destructure an existential.',
  mut:            '**mut** — Marks an instruction account as mutable.',
  signer:         '**signer** — Marks an instruction account as required signer.',
  init:           '**init** — Marks an account as newly created in this instruction.',
  Address:        '`Address` — 32-byte public key / account address (`[u8; 32]`).',
  TokenAmount:    '`TokenAmount` — native token quantity (`u64`).',
  Hash:           '`Hash` — SHA-256 output (`[u8; 32]`).',
  Signature:      '`Signature` — Ed25519 signature (`[u8; 64]`).',
  Slot:           '`Slot` — monotonic block slot number (`u64`).',
  Nat:            '`Nat` — natural number, ≥ 0 (`u64`).',
  Bool:           '`Bool` — boolean (`bool`).',
  '→':            '`→` **(implies / sequences)**: next block calls `apply()` on current.',
  '↔':            '`↔` **(iff / pairs)**: pairs a `theorem`/`lemma` with its `proof`.',
  '∧':            '`∧` **(and / independent)**: next block does **not** call `apply()`.',
  '∨':            '`∨` **(or / disjunctive)**: either block suffices.',
  '∈':            '`∈` — membership. Used in type annotations and membership proofs.',
  '∀':            '`∀` — universal quantifier. `∀ x ∈ A, P(x)`.',
  '∃':            '`∃` — existential quantifier. `∃ x ∈ A, P(x)`.',
};

connection.onHover((params: TextDocumentPositionParams): Hover | null => {
  const doc  = documents.get(params.textDocument.uri);
  if (!doc) return null;
  const line = doc.getText({
    start: { line: params.position.line, character: 0 },
    end:   { line: params.position.line, character: 999 },
  });
  const col = params.position.character;
  const before = line.slice(0, col).match(/[\w∀∃∈∧∨→↔ℕ]+$/)?.[0] ?? '';
  const after  = line.slice(col).match(/^[\w∀∃∈∧∨→↔ℕ]*/)?.[0] ?? '';
  const token  = before + after;
  if (!token) return null;
  const doc_text = HOVER_DB[token];
  if (!doc_text) return null;
  return {
    contents: { kind: MarkupKind.Markdown, value: doc_text },
  };
});

// ── Completions ───────────────────────────────────────────────────────────────

const COMPLETIONS: CompletionItem[] = [
  // Top-level blocks
  { label: 'theorem',        kind: CompletionItemKind.Keyword, insertText: 'theorem ${1:Name}() {\n  assume(${2:P}) →\n  declareToProve(${3:Q})\n} ↔\n\nproof ${1:Name}() {\n  conclude(${3:Q})\n}', insertTextFormat: 2 },
  { label: 'proof',          kind: CompletionItemKind.Keyword, insertText: 'proof ${1:Name}() {\n  conclude(${2:P})\n}', insertTextFormat: 2 },
  { label: 'lemma',          kind: CompletionItemKind.Keyword, insertText: 'lemma ${1:Name}() {\n  assume(${2:P}) →\n  declareToProve(${3:Q})\n} ↔\n\nproof ${1:Name}() {\n  conclude(${3:Q})\n}', insertTextFormat: 2 },
  { label: 'fn',             kind: CompletionItemKind.Keyword, insertText: 'fn ${1:name}(${2:x} ∈ ${3:Nat}) -> ${4:Nat} {\n  conclude(${5:x})\n}', insertTextFormat: 2 },
  { label: 'struct',         kind: CompletionItemKind.Keyword, insertText: 'struct ${1:Name} {\n  ${2:field} ∈ ${3:Nat},\n}', insertTextFormat: 2 },
  { label: 'definition',     kind: CompletionItemKind.Keyword },
  // Blockchain blocks
  { label: 'program',        kind: CompletionItemKind.Keyword, insertText: 'program ${1:Name} {\n\n  account ${2:State} {\n    ${3:field} ∈ ${4:TokenAmount},\n  } →\n\n  instruction ${5:init}(\n    authority: mut signer ∈ ${2:State},\n  ) {\n    // ...\n  }\n\n}', insertTextFormat: 2 },
  { label: 'account',        kind: CompletionItemKind.Keyword, insertText: 'account ${1:Name} {\n  ${2:field} ∈ ${3:TokenAmount},\n}', insertTextFormat: 2 },
  { label: 'instruction',    kind: CompletionItemKind.Keyword, insertText: 'instruction ${1:name}(\n  ${2:authority}: mut signer ∈ ${3:State},\n) {\n  require(${4:cond}, ${5:Error})\n}', insertTextFormat: 2 },
  { label: 'error',          kind: CompletionItemKind.Keyword, insertText: 'error ${1:Name} {\n  | ${2:Variant}("${3:message}")\n}', insertTextFormat: 2 },
  // Proof statements
  { label: 'assume',         kind: CompletionItemKind.Function, insertText: 'assume(${1:P})', insertTextFormat: 2 },
  { label: 'conclude',       kind: CompletionItemKind.Function, insertText: 'conclude(${1:P})', insertTextFormat: 2 },
  { label: 'declareToProve', kind: CompletionItemKind.Function, insertText: 'declareToProve(${1:P})', insertTextFormat: 2 },
  { label: 'prove',          kind: CompletionItemKind.Function, insertText: 'prove(${1:P})', insertTextFormat: 2 },
  { label: 'apply',          kind: CompletionItemKind.Function, insertText: 'apply(${1:Lemma})', insertTextFormat: 2 },
  // Blockchain statements
  { label: 'require',        kind: CompletionItemKind.Function, insertText: 'require(${1:condition}, ${2:Error})', insertTextFormat: 2 },
  { label: 'emit',           kind: CompletionItemKind.Function, insertText: 'emit(${1:EventName}, ${2:field}: ${3:value})', insertTextFormat: 2 },
  { label: 'transfer',       kind: CompletionItemKind.Function, insertText: 'transfer(${1:from}, ${2:to}, ${3:amount})', insertTextFormat: 2 },
  { label: 'pda',            kind: CompletionItemKind.Function, insertText: 'let ${1:addr} = pda([${2:seed}])', insertTextFormat: 2 },
  { label: 'cpi',            kind: CompletionItemKind.Function, insertText: 'cpi(${1:program_id}, ${2:instruction}, [${3:accounts}])', insertTextFormat: 2 },
  // Types
  { label: 'Address',        kind: CompletionItemKind.TypeParameter },
  { label: 'TokenAmount',    kind: CompletionItemKind.TypeParameter },
  { label: 'Hash',           kind: CompletionItemKind.TypeParameter },
  { label: 'Signature',      kind: CompletionItemKind.TypeParameter },
  { label: 'Slot',           kind: CompletionItemKind.TypeParameter },
  { label: 'Nat',            kind: CompletionItemKind.TypeParameter },
  { label: 'Bool',           kind: CompletionItemKind.TypeParameter },
  { label: 'String',         kind: CompletionItemKind.TypeParameter },
  { label: 'List',           kind: CompletionItemKind.TypeParameter, insertText: 'List(${1:Nat})', insertTextFormat: 2 },
];

connection.onCompletion((_pos: TextDocumentPositionParams): CompletionItem[] => COMPLETIONS);

// ── Start ─────────────────────────────────────────────────────────────────────

documents.listen(connection);
connection.listen();
