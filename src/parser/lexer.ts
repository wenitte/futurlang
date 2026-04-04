// src/parser/lexer.ts

export interface ParsedLine {
  type: 'theorem' | 'definition' | 'lemma' | 'proof' | 'assert' | 'let' | 'blockEnd' | 'raw';
  content: string;
  name?: string;
}

export function lexFL(text: string): ParsedLine[] {
  const raw = text
    .replace(/\r\n/g, '\n')
    .split('\n')
    .map(l => l.trim());

  const parsed: ParsedLine[] = [];
  let i = 0;

  while (i < raw.length) {
    const line = raw[i];
    i++;

    // Blank lines and comments
    if (!line || line.startsWith('//') || line.startsWith('#')) continue;

    if (/^theorem\b/.test(line)) {
      parsed.push({ type: 'theorem', content: line, name: line.match(/^theorem\s+(\w+)/)?.[1] ?? 'unnamed' });

    } else if (/^definition\b/.test(line)) {
      parsed.push({ type: 'definition', content: line, name: line.match(/^definition\s+(\w+)/)?.[1] ?? 'unnamed' });

    } else if (/^lemma\b/.test(line)) {
      parsed.push({ type: 'lemma', content: line, name: line.match(/^lemma\s+(\w+)/)?.[1] ?? 'unnamed' });

    } else if (/^proof\b/.test(line)) {
      parsed.push({ type: 'proof', content: line });

    } else if (/^let\s+/.test(line)) {
      parsed.push({ type: 'let', content: line });

    } else if (/^assert\s*\(/.test(line)) {
      // Greedily consume continuation lines until parens balance
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += ' ' + raw[i];
        i++;
      }
      // Strip trailing &&  or  ||  that connect assert to the next statement
      const cleaned = combined.replace(/\)\s*(&&|\|\|)\s*$/, ')').trim();
      parsed.push({ type: 'assert', content: cleaned });

    } else if (/^}\s*(&&|\|\|)?\s*$/.test(line) || line === '}') {
      parsed.push({ type: 'blockEnd', content: '}' });

    } else {
      parsed.push({ type: 'raw', content: line });
    }
  }

  return parsed;
}

function parenDepth(s: string): number {
  let d = 0;
  let inStr = false;
  let strChar = '';
  for (const ch of s) {
    if (inStr) {
      if (ch === strChar) inStr = false;
    } else if (ch === '"' || ch === "'") {
      inStr = true; strChar = ch;
    } else if (ch === '(') {
      d++;
    } else if (ch === ')') {
      d--;
    }
  }
  return d;
}
