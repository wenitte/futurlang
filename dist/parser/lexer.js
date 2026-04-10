"use strict";
// src/parser/lexer.ts
Object.defineProperty(exports, "__esModule", { value: true });
exports.lexFL = lexFL;
// Extract the trailing connective from a line, returning [cleaned, connective]
function extractConnective(line) {
    // Match trailing →, ∧, ↔ (with optional whitespace and // comment after)
    const m = line.match(/^([\s\S]*?)\s*(→|∧|↔)\s*(?:\/\/.*)?$/);
    if (m) {
        return [m[1].trimEnd(), m[2]];
    }
    // Also handle ASCII alternatives at end of line
    const ascii = line.match(/^([\s\S]*?)\s*(->|&&|<->)\s*(?:\/\/.*)?$/);
    if (ascii) {
        const map = { '->': '→', '&&': '∧', '<->': '↔' };
        return [ascii[1].trimEnd(), map[ascii[2]]];
    }
    // Strip inline comments with no connective
    const noComment = line.replace(/\s*\/\/.*$/, '').trimEnd();
    return [noComment, null];
}
function parenDepth(s) {
    let d = 0;
    let inStr = false;
    let strChar = '';
    for (const ch of s) {
        if (inStr) {
            if (ch === strChar)
                inStr = false;
        }
        else if (ch === '"' || ch === "'") {
            inStr = true;
            strChar = ch;
        }
        else if (ch === '(' || ch === '[' || ch === '{')
            d++;
        else if (ch === ')' || ch === ']' || ch === '}')
            d--;
    }
    return d;
}
function lexFL(text) {
    const raw = text.replace(/\r\n/g, '\n').split('\n').map(l => l.trim());
    const parsed = [];
    let i = 0;
    while (i < raw.length) {
        const line = raw[i];
        i++;
        if (!line || line.startsWith('//') || line.startsWith('#'))
            continue;
        // ── Block-end: } possibly followed by a connective ──────────────────────
        if (/^}/.test(line)) {
            const [, conn] = extractConnective(line);
            parsed.push({ type: 'blockEnd', content: '}', connective: conn });
            continue;
        }
        // ── Top-level block openers ──────────────────────────────────────────────
        if (/^theorem\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'theorem', content: cleaned,
                name: cleaned.match(/^theorem\s+(\w+)/)?.[1] ?? 'unnamed', connective: conn });
            continue;
        }
        if (/^definition\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'definition', content: cleaned,
                name: cleaned.match(/^definition\s+(\w+)/)?.[1] ?? 'unnamed', connective: conn });
            continue;
        }
        if (/^struct\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'struct', content: cleaned,
                name: cleaned.match(/^struct\s+(\w+)/)?.[1] ?? 'unnamed', connective: conn });
            continue;
        }
        if (/^type\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'typeDecl', content: cleaned,
                name: cleaned.match(/^type\s+(\w+)/)?.[1] ?? 'unnamed', connective: conn });
            continue;
        }
        if (/^proof\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            const name = cleaned.match(/^proof\s+(\w+)/)?.[1] ?? 'unnamed';
            parsed.push({ type: 'proof', content: cleaned, name, connective: conn });
            continue;
        }
        if (/^fn\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            const name = cleaned.match(/^fn\s+(\w+)/)?.[1] ?? 'unnamed';
            parsed.push({ type: 'fn', content: cleaned, name, connective: conn });
            continue;
        }
        if (/^induction\s*\(/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'induction', content: cleaned, connective: conn });
            continue;
        }
        if (/^match\s+/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'match', content: cleaned, connective: conn });
            continue;
        }
        if (/^lemma\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'lemma', content: cleaned,
                name: cleaned.match(/^lemma\s+(\w+)/)?.[1] ?? 'unnamed', connective: conn });
            continue;
        }
        // ── level (metadata, but carries a connective to the next block) ─────────
        if (/^level\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'level', content: cleaned, connective: conn });
            continue;
        }
        // ── return (inside definition bodies) ────────────────────────────────────
        if (/^return\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'return', content: cleaned, connective: conn });
            continue;
        }
        // ── assert(...) — possibly multi-line ────────────────────────────────────
        if (/^assert\s*\(/.test(line)) {
            let combined = line;
            while (parenDepth(combined) !== 0 && i < raw.length) {
                combined += ' ' + raw[i];
                i++;
            }
            const [cleaned, conn] = extractConnective(combined);
            parsed.push({ type: 'assert', content: cleaned, connective: conn });
            continue;
        }
        // ── given(...) — theorem/lemma premises, possibly multi-line ────────────
        if (/^given\s*\(/.test(line)) {
            let combined = line;
            while (parenDepth(combined) !== 0 && i < raw.length) {
                combined += ' ' + raw[i];
                i++;
            }
            const [cleaned, conn] = extractConnective(combined);
            parsed.push({ type: 'given', content: cleaned, connective: conn });
            continue;
        }
        // ── assume(...) — possibly multi-line ────────────────────────────────────
        if (/^assume\s*\(/.test(line)) {
            let combined = line;
            while (parenDepth(combined) !== 0 && i < raw.length) {
                combined += ' ' + raw[i];
                i++;
            }
            const [cleaned, conn] = extractConnective(combined);
            parsed.push({ type: 'assume', content: cleaned, connective: conn });
            continue;
        }
        // ── conclude(...) — possibly multi-line ──────────────────────────────────
        if (/^conclude\s*\(/.test(line)) {
            let combined = line;
            while (parenDepth(combined) !== 0 && i < raw.length) {
                combined += ' ' + raw[i];
                i++;
            }
            const [cleaned, conn] = extractConnective(combined);
            parsed.push({ type: 'conclude', content: cleaned, connective: conn });
            continue;
        }
        // ── apply(...) ────────────────────────────────────────────────────────────
        if (/^apply\s*\(/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            const target = cleaned.match(/^apply\s*\((.+)\)/)?.[1]?.trim() ?? cleaned;
            parsed.push({ type: 'apply', content: cleaned, name: target, connective: conn });
            continue;
        }
        if (/^intro\s*\(/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'intro', content: cleaned, connective: conn });
            continue;
        }
        if (/^rewrite\s*\(/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'rewrite', content: cleaned, connective: conn });
            continue;
        }
        if (/^exact\s*\(/.test(line)) {
            let combined = line;
            while (parenDepth(combined) !== 0 && i < raw.length) {
                combined += ' ' + raw[i];
                i++;
            }
            const [cleaned, conn] = extractConnective(combined);
            parsed.push({ type: 'exact', content: cleaned, connective: conn });
            continue;
        }
        if (/^obtain\s*\(/.test(line)) {
            let combined = line;
            while (parenDepth(combined) !== 0 && i < raw.length) {
                combined += ' ' + raw[i];
                i++;
            }
            const [cleaned, conn] = extractConnective(combined);
            parsed.push({ type: 'obtain', content: cleaned, connective: conn });
            continue;
        }
        // ── setVar(...) ───────────────────────────────────────────────────────────
        if (/^setVar\s*\(/.test(line)) {
            let combined = line;
            while (parenDepth(combined) !== 0 && i < raw.length) {
                combined += ' ' + raw[i];
                i++;
            }
            const [cleaned, conn] = extractConnective(combined);
            parsed.push({ type: 'setVar', content: cleaned, connective: conn });
            continue;
        }
        if (/^base\s*:/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'base', content: cleaned, connective: conn });
            continue;
        }
        if (/^step\s*:/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'step', content: cleaned, connective: conn });
            continue;
        }
        if (/^case\b/.test(line)) {
            const [cleaned, conn] = extractConnective(line);
            parsed.push({ type: 'case', content: cleaned, connective: conn });
            continue;
        }
        // ── let variable binding ──────────────────────────────────────────────────
        if (/^let\s+/.test(line)) {
            let combined = line;
            while (parenDepth(combined) !== 0 && i < raw.length) {
                combined += ' ' + raw[i];
                i++;
            }
            const [cleaned, conn] = extractConnective(combined);
            parsed.push({ type: 'setVar', content: cleaned, connective: conn });
            continue;
        }
        // ── Raw ────────────────────────────────────────────────────────────────────
        const [cleaned, conn] = extractConnective(line);
        parsed.push({ type: 'raw', content: cleaned, connective: conn });
    }
    return parsed;
}
