// src/parser/expr.ts
//
// Recursive-descent parser for FuturLang logical expressions.
//
// Precedence (lowest → highest):
//   ↔  ⇔  <->  iff    biconditional, right-assoc
//   →  ⇒  ->  implies implication,   right-assoc
//   ∨  ||   or        left-assoc
//   ∧  &&   and       left-assoc
//   ¬  !  not         prefix
//
// Atoms: string literals, relational expressions (x == y), bare identifiers.

import {
  ExprNode, AtomNode, AndNode, OrNode, ImpliesNode, IffNode, NotNode,
} from './ast';

const WORD_NORMALIZATIONS: Array<[RegExp, string]> = [
  [/\bfor\s+all\b/gi, '∀'],
  [/\bforall\b/gi, '∀'],
  [/\bthere\s+exists\b/gi, '∃'],
  [/\bexists\b/gi, '∃'],
  [/\bnot\s+in\b/gi, '∉'],
  [/\bnotin\b/gi, '∉'],
  [/\bstrictsubset\b/gi, '⊂'],
  [/\bpropersubset\b/gi, '⊂'],
  [/\bsubseteq\b/gi, '⊆'],
  [/\bsubset\b/gi, '⊆'],
  [/\bintersection\b/gi, '∩'],
  [/\bintersect\b/gi, '∩'],
  [/\bunion\b/gi, '∪'],
  [/\bneq\b/gi, '≠'],
  [/\bnot\s*=\b/gi, '≠'],
  [/\bNat\b/g, 'ℕ'],
  [/\bnat\b/g, 'ℕ'],
  [/\bInt\b/g, 'ℤ'],
  [/\bint\b/g, 'ℤ'],
  [/\bRat\b/g, 'ℚ'],
  [/\brat\b/g, 'ℚ'],
  [/\bReal\b/g, 'ℝ'],
  [/\breal\b/g, 'ℝ'],
  [/\b(in)\b/gi, '∈'],
];

function normalizeSurfaceSyntax(src: string): string {
  const segments = src.split(/(".*?"|'.*?')/g);
  return segments.map((segment, index) => {
    if (index % 2 === 1) return segment;
    let value = segment;
    for (const [pattern, replacement] of WORD_NORMALIZATIONS) {
      value = value.replace(pattern, replacement);
    }
    value = value.replace(/!=/g, '≠');
    value = value.replace(/<=/g, '≤');
    value = value.replace(/>=/g, '≥');
    return value;
  }).join('');
}

// ── Operator table ────────────────────────────────────────────────────────────

type TokKind =
  | 'IFF' | 'IMPLIES' | 'OR' | 'AND' | 'NOT'
  | 'LPAREN' | 'RPAREN'
  | 'ATOM' | 'EOF';

interface Token { kind: TokKind; value: string; }

// Ordered longest-match-first so <-> is tried before -> etc.
const OP_TABLE: Array<[RegExp, TokKind]> = [
  [/^(↔|⇔|<->|iff\b)/i,     'IFF'],
  [/^(→|⇒|->|implies\b)/i,  'IMPLIES'],
  [/^(∨|\|\||or\b)/i,     'OR'],
  [/^(∧|&&|and\b)/i,      'AND'],
  [/^(¬|!|not\b)/i,       'NOT'],
  [/^\(/,                  'LPAREN'],
  [/^\)/,                  'RPAREN'],
];

// Returns true if any operator pattern matches at the start of `s`
function startsWithOp(s: string): boolean {
  for (const [re] of OP_TABLE) if (re.test(s)) return true;
  return false;
}

// ── Tokeniser ─────────────────────────────────────────────────────────────────

function tokenise(src: string): Token[] {
  const tokens: Token[] = [];
  let s = src.trim();

  if (!s) { tokens.push({ kind: 'EOF', value: '' }); return tokens; }

  while (s.length > 0) {
    s = s.replace(/^\s+/, '');
    if (!s.length) break;

    // 1. Try operator
    let opMatched = false;
    for (const [re, kind] of OP_TABLE) {
      const m = s.match(re);
      if (m) {
        tokens.push({ kind, value: m[0] });
        s = s.slice(m[0].length);
        opMatched = true;
        break;
      }
    }
    if (opMatched) continue;

    // 2. String literal – may be a standalone claim or the RHS of x == "val"
    if (s[0] === '"' || s[0] === "'") {
      const q   = s[0];
      const end = s.indexOf(q, 1);
      if (end === -1) throw new Error(`Unterminated string: ${s}`);
      const lit = s.slice(0, end + 1);

      // Merge into a preceding relational atom (e.g. `message ==` + `"Hello"`)
      const prev = tokens[tokens.length - 1];
      if (prev?.kind === 'ATOM' && /[=<>!]\s*$/.test(prev.value)) {
        prev.value += lit;
      } else {
        tokens.push({ kind: 'ATOM', value: lit });
      }
      s = s.slice(end + 1);
      continue;
    }

    // 3. Bare atom – consume chars one at a time until we hit an op boundary.
    //    This correctly stops at  ->  &&  ||  <->  etc.
    let atom = '';
    while (s.length > 0) {
      const rest = s.replace(/^\s+/, '');

      // Stop if an operator starts here
      if (startsWithOp(rest)) break;

      // Stop at quote (handled above on next iteration)
      if (rest[0] === '"' || rest[0] === "'") break;

      // Advance by one char (preserve leading whitespace as separator)
      atom += s[0];
      s     = s.slice(1);
    }

    const trimmed = atom.trim();
    if (trimmed.length > 0) {
      tokens.push({ kind: 'ATOM', value: trimmed });
    }
  }

  tokens.push({ kind: 'EOF', value: '' });
  return tokens;
}

// ── Parser ────────────────────────────────────────────────────────────────────

class ExprParser {
  private pos = 0;
  constructor(private readonly tokens: Token[]) {}

  private peek(): Token    { return this.tokens[this.pos]; }
  private consume(): Token { return this.tokens[this.pos++]; }
  private expect(kind: TokKind): void {
    const t = this.consume();
    if (t.kind !== kind) throw new Error(`Expected ${kind}, got ${t.kind} ("${t.value}")`);
  }

  parse(): ExprNode {
    if (this.peek().kind === 'EOF') return { type: 'Atom', condition: 'true', atomKind: 'expression' };
    const node = this.parseIff();
    if (this.peek().kind !== 'EOF')
      throw new Error(`Unexpected token after expression: "${this.peek().value}"`);
    return node;
  }

  private parseIff(): ExprNode {
    const left = this.parseImplies();
    if (this.peek().kind === 'IFF') {
      this.consume();
      return { type: 'Iff', left, right: this.parseIff() } as IffNode;
    }
    return left;
  }

  private parseImplies(): ExprNode {
    const left = this.parseOr();
    if (this.peek().kind === 'IMPLIES') {
      this.consume();
      return { type: 'Implies', left, right: this.parseImplies() } as ImpliesNode;
    }
    return left;
  }

  private parseOr(): ExprNode {
    let left = this.parseAnd();
    while (this.peek().kind === 'OR') {
      this.consume();
      left = { type: 'Or', left, right: this.parseAnd() } as OrNode;
    }
    return left;
  }

  private parseAnd(): ExprNode {
    let left = this.parseNot();
    while (this.peek().kind === 'AND') {
      this.consume();
      left = { type: 'And', left, right: this.parseNot() } as AndNode;
    }
    return left;
  }

  private parseNot(): ExprNode {
    if (this.peek().kind === 'NOT') {
      this.consume();
      return { type: 'Not', operand: this.parseNot() } as NotNode;
    }
    return this.parseAtom();
  }

  private parseAtom(): ExprNode {
    const t = this.peek();

    if (t.kind === 'LPAREN') {
      this.consume();
      const inner = this.parseIff();
      this.expect('RPAREN');
      return inner;
    }

    if (t.kind === 'ATOM') {
      this.consume();
      const condition = t.value.trim();
      const atomKind =
        (condition.startsWith('"') && condition.endsWith('"')) ||
        (condition.startsWith("'") && condition.endsWith("'"))
          ? 'string'
          : 'expression';
      return { type: 'Atom', condition, atomKind } as AtomNode;
    }

    throw new Error(`Unexpected token: "${t.value}" (${t.kind})`);
  }
}

// ── Public API ────────────────────────────────────────────────────────────────

export function parseExpr(src: string): ExprNode {
  return new ExprParser(tokenise(normalizeSurfaceSyntax(src))).parse();
}
