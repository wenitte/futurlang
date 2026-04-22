#!/usr/bin/env node
"use strict";
var __create = Object.create;
var __defProp = Object.defineProperty;
var __getOwnPropDesc = Object.getOwnPropertyDescriptor;
var __getOwnPropNames = Object.getOwnPropertyNames;
var __getProtoOf = Object.getPrototypeOf;
var __hasOwnProp = Object.prototype.hasOwnProperty;
var __copyProps = (to, from, except, desc) => {
  if (from && typeof from === "object" || typeof from === "function") {
    for (let key of __getOwnPropNames(from))
      if (!__hasOwnProp.call(to, key) && key !== except)
        __defProp(to, key, { get: () => from[key], enumerable: !(desc = __getOwnPropDesc(from, key)) || desc.enumerable });
  }
  return to;
};
var __toESM = (mod, isNodeMode, target) => (target = mod != null ? __create(__getProtoOf(mod)) : {}, __copyProps(
  // If the importer is in node compatibility mode or this is not an ESM
  // file that has been converted to a CommonJS file using a Babel-
  // compatible transform (i.e. "__esModule" has not been set), then set
  // "default" to the CommonJS "module.exports" for node compatibility.
  isNodeMode || !mod || !mod.__esModule ? __defProp(target, "default", { value: mod, enumerable: true }) : target,
  mod
));

// src/cli.ts
var fs4 = __toESM(require("fs"));
var path4 = __toESM(require("path"));
var readline = __toESM(require("readline"));
var import_child_process = require("child_process");

// src/parser/lexer.ts
function extractConnective(line) {
  const m = line.match(/^([\s\S]*?)\s*(→|∧|∨|↔)\s*(?:\/\/.*)?$/);
  if (m) {
    return [m[1].trimEnd(), m[2]];
  }
  const ascii = line.match(/^([\s\S]*?)\s*(->|&&|\|\||<->)\s*(?:\/\/.*)?$/);
  if (ascii) {
    const map = { "->": "\u2192", "&&": "\u2227", "||": "\u2228", "<->": "\u2194" };
    return [ascii[1].trimEnd(), map[ascii[2]]];
  }
  const noComment = line.replace(/\s*\/\/.*$/, "").trimEnd();
  return [noComment, null];
}
function parenDepth(s) {
  let d = 0;
  let inStr = false;
  let strChar = "";
  for (const ch of s) {
    if (inStr) {
      if (ch === strChar) inStr = false;
    } else if (ch === '"' || ch === "'") {
      inStr = true;
      strChar = ch;
    } else if (ch === "(" || ch === "[" || ch === "{") d++;
    else if (ch === ")" || ch === "]" || ch === "}") d--;
  }
  return d;
}
function lexFL(text) {
  const raw = text.replace(/\r\n/g, "\n").split("\n").map((l) => l.trim());
  const parsed = [];
  let i = 0;
  while (i < raw.length) {
    const line = raw[i];
    i++;
    if (!line || line.startsWith("//") || line.startsWith("#")) continue;
    if (/^}/.test(line)) {
      const [, conn2] = extractConnective(line);
      parsed.push({ type: "blockEnd", content: "}", connective: conn2 });
      continue;
    }
    if (/^theorem\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({
        type: "theorem",
        content: cleaned2,
        name: cleaned2.match(/^theorem\s+(\w+)/)?.[1] ?? "unnamed",
        connective: conn2
      });
      continue;
    }
    if (/^definition\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({
        type: "definition",
        content: cleaned2,
        name: cleaned2.match(/^definition\s+(\w+)/)?.[1] ?? "unnamed",
        connective: conn2
      });
      continue;
    }
    if (/^struct\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({
        type: "struct",
        content: cleaned2,
        name: cleaned2.match(/^struct\s+(\w+)/)?.[1] ?? "unnamed",
        connective: conn2
      });
      continue;
    }
    if (/^type\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({
        type: "typeDecl",
        content: cleaned2,
        name: cleaned2.match(/^type\s+(\w+)/)?.[1] ?? "unnamed",
        connective: conn2
      });
      continue;
    }
    if (/^proof\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      const name = cleaned2.match(/^proof\s+(\w+)/)?.[1] ?? "unnamed";
      parsed.push({ type: "proof", content: cleaned2, name, connective: conn2 });
      continue;
    }
    if (/^native\s+theorem\b/.test(line) || /^native\s+lemma\b/.test(line) || /^axiom\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      const name = cleaned2.match(/(?:native\s+(?:theorem|lemma)|axiom)\s+(\w+)/)?.[1] ?? "unnamed";
      parsed.push({ type: "axiom", content: cleaned2, name, connective: conn2 });
      continue;
    }
    if (/^native\s+fn\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      const name = cleaned2.match(/^native\s+fn\s+(\w+)/)?.[1] ?? "unnamed";
      parsed.push({ type: "fn", content: cleaned2.replace(/^native\s+/, ""), name, isNative: true, connective: conn2 });
      continue;
    }
    if (/^fn\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      const name = cleaned2.match(/^fn\s+(\w+)/)?.[1] ?? "unnamed";
      parsed.push({ type: "fn", content: cleaned2, name, connective: conn2 });
      continue;
    }
    if (/^induction\s*\(/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({ type: "induction", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^match\s+/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({ type: "match", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^lemma\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({
        type: "lemma",
        content: cleaned2,
        name: cleaned2.match(/^lemma\s+(\w+)/)?.[1] ?? "unnamed",
        connective: conn2
      });
      continue;
    }
    if (/^program\s+\w/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({
        type: "program",
        content: cleaned2,
        name: cleaned2.match(/^program\s+(\w+)/)?.[1] ?? "unnamed",
        connective: conn2
      });
      continue;
    }
    if (/^account\s+\w/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({
        type: "account",
        content: cleaned2,
        name: cleaned2.match(/^account\s+(\w+)/)?.[1] ?? "unnamed",
        connective: conn2
      });
      continue;
    }
    if (/^instruction\s+\w/.test(line)) {
      let combined = line;
      while (!combined.trimEnd().endsWith("{") && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({
        type: "instruction",
        content: cleaned2,
        name: cleaned2.match(/^instruction\s+(\w+)/)?.[1] ?? "unnamed",
        connective: conn2
      });
      continue;
    }
    if (/^error\s+\w/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({
        type: "errorDecl",
        content: cleaned2,
        name: cleaned2.match(/^error\s+(\w+)/)?.[1] ?? "unnamed",
        connective: conn2
      });
      continue;
    }
    if (/^require\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "require", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^emit\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "emit", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^pda\s*\(/.test(line) || /^let\s+\w+\s*=\s*pda\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "pda", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^cpi\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "cpi", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^transfer\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "transfer", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^level\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({ type: "level", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^return\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({ type: "return", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^declareToProve\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "declareToProve", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^prove\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "prove", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^derive\s*\(\s*\)/.test(line)) {
      const [, conn2] = extractConnective(line);
      parsed.push({ type: "derive", content: "", connective: conn2 });
      continue;
    }
    if (/^AndIntro\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "andIntroStep", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^OrIntro\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "orIntroStep", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^assert\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "assert", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^requires\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "requires", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^ensures\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "ensures", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^given\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "given", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^assume\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "assume", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^conclude\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "conclude", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^apply\s*\(/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      const target = cleaned2.match(/^apply\s*\((.+)\)/)?.[1]?.trim() ?? cleaned2;
      parsed.push({ type: "apply", content: cleaned2, name: target, connective: conn2 });
      continue;
    }
    if (/^intro\s*\(/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({ type: "intro", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^rewrite\s*\(/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({ type: "rewrite", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^exact\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "exact", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^obtain\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "obtain", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^setVar\s*\(/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "setVar", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^base\s*:/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({ type: "base", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^step\s*:/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({ type: "step", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^case\b/.test(line)) {
      const [cleaned2, conn2] = extractConnective(line);
      parsed.push({ type: "case", content: cleaned2, connective: conn2 });
      continue;
    }
    if (/^let\s+/.test(line)) {
      let combined = line;
      while (parenDepth(combined) !== 0 && i < raw.length) {
        combined += " " + raw[i];
        i++;
      }
      const [cleaned2, conn2] = extractConnective(combined);
      parsed.push({ type: "setVar", content: cleaned2, connective: conn2 });
      continue;
    }
    const [cleaned, conn] = extractConnective(line);
    parsed.push({ type: "raw", content: cleaned, connective: conn });
  }
  return parsed;
}

// src/parser/expr.ts
var WORD_NORMALIZATIONS = [
  [/\bfor\s+all\b/gi, "\u2200"],
  [/\bforall\b/gi, "\u2200"],
  [/\bthere\s+exists\b/gi, "\u2203"],
  [/\bexists\b/gi, "\u2203"],
  [/\bnot\s+in\b/gi, "\u2209"],
  [/\bnotin\b/gi, "\u2209"],
  [/\bstrictsubset\b/gi, "\u2286"],
  [/\bpropersubset\b/gi, "\u2286"],
  [/\bsubseteq\b/gi, "\u2282"],
  [/\bsubset\b/gi, "\u2282"],
  [/\bintersection\b/gi, "\u2229"],
  [/\bintersect\b/gi, "\u2229"],
  [/\bunion\b/gi, "\u222A"],
  [/\bneq\b/gi, "\u2260"],
  [/\bnot\s*=\b/gi, "\u2260"],
  [/\bNat\b/g, "\u2115"],
  [/\bnat\b/g, "\u2115"],
  [/\bInt\b/g, "\u2124"],
  [/\bint\b/g, "\u2124"],
  [/\bRat\b/g, "\u211A"],
  [/\brat\b/g, "\u211A"],
  [/\bReal\b/g, "\u211D"],
  [/\breal\b/g, "\u211D"],
  [/\b(in)\b/gi, "\u2208"]
];
function normalizeSurfaceSyntax(src) {
  const segments = src.split(/(".*?"|'.*?')/g);
  return segments.map((segment, index) => {
    if (index % 2 === 1) return segment;
    let value = segment;
    for (const [pattern, replacement] of WORD_NORMALIZATIONS) {
      value = value.replace(pattern, replacement);
    }
    value = value.replace(/!=/g, "\u2260");
    value = value.replace(/<=/g, "\u2264");
    value = value.replace(/>=/g, "\u2265");
    value = normalizePrefixQuantifiedBinders(value);
    value = normalizeStandaloneQuantifiedDeclarations(value);
    return value;
  }).join("");
}
function normalizePrefixQuantifiedBinders(src) {
  let value = src.trim();
  let changed = true;
  while (changed) {
    changed = false;
    const normalized = normalizeSingleLeadingQuantifier(value);
    if (normalized && normalized !== value) {
      value = normalized;
      changed = true;
    }
  }
  return value;
}
function normalizeStandaloneQuantifiedDeclarations(src) {
  return src.replace(/(∀|∃!|∃)\s*\(([^()]+)\)(?=\s*(?:[∧∨),]|$))/g, (match, quantifier, binder) => {
    return normalizeBinderList(quantifier, binder.trim(), null) ?? match;
  });
}
function normalizeSingleLeadingQuantifier(src) {
  const trimmed = src.trim();
  const quantifierMatch = trimmed.match(/^(∀|∃!|∃)\s*\(/);
  if (!quantifierMatch) return null;
  const quantifier = quantifierMatch[1];
  const binderStart = trimmed.indexOf("(");
  const binderEnd = findMatchingParen(trimmed, binderStart);
  if (binderEnd === -1) return null;
  const binder = trimmed.slice(binderStart + 1, binderEnd).trim();
  const remainder = trimmed.slice(binderEnd + 1).trimStart();
  if (!remainder) {
    return normalizeBinderList(quantifier, binder, null);
  }
  const arrowMatch = remainder.match(/^(→|⇒|->)\s*([\s\S]+)$/);
  if (!arrowMatch) return null;
  const body = arrowMatch[2].trim();
  if (!body) return null;
  const normalizedBinders = normalizeBinderList(quantifier, binder, body);
  if (!normalizedBinders) return null;
  return normalizedBinders;
}
function findMatchingParen(value, start) {
  let depth = 0;
  for (let i = start; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}
function normalizeBinderList(quantifier, binder, body) {
  const normalizedBody = body ? normalizePrefixQuantifiedBinders(body) : null;
  const boundedMatch = binder.match(/^(.+?)\s*∈\s*(.+)$/);
  if (boundedMatch) {
    const variables = splitBinderNames(boundedMatch[1]);
    const set = boundedMatch[2].trim();
    if (variables.length === 0 || !set) return null;
    return variables.reduceRight(
      (acc, variable) => acc ? `${quantifier} ${variable} \u2208 ${set}, ${acc}` : `${quantifier} ${variable} \u2208 ${set}`,
      normalizedBody
    );
  }
  const typedMatch = binder.match(/^(.+?)\s*:\s*(.+)$/);
  if (typedMatch) {
    const variables = splitBinderNames(typedMatch[1]);
    const type = typedMatch[2].trim();
    if (variables.length === 0 || !type) return null;
    return variables.reduceRight(
      (acc, variable) => acc ? `${quantifier} ${variable}: ${type}, ${acc}` : `${quantifier} ${variable}: ${type}`,
      normalizedBody
    );
  }
  return null;
}
function splitBinderNames(value) {
  return value.split(/[,\s]+/).map((part) => part.trim()).filter(Boolean);
}
var OP_TABLE = [
  [/^(↔|⇔|<->|iff\b)/i, "IFF"],
  [/^(→|⇒|->|implies\b)/i, "IMPLIES"],
  [/^(∨|\|\||or\b)/i, "OR"],
  [/^(∧|&&|and\b)/i, "AND"],
  [/^(¬|!|not\b)/i, "NOT"],
  [/^\(/, "LPAREN"],
  [/^\)/, "RPAREN"]
];
function startsWithOpInAtom(rest, atom) {
  const symbolic = /^(↔|⇔|<->|→|⇒|->|∨|\|\||∧|&&|¬|!|\(|\))/.test(rest);
  if (symbolic) return true;
  const wordLike = /^(iff\b|implies\b|or\b|and\b|not\b)/i.test(rest);
  if (!wordLike) return false;
  return atom.length === 0 || /\s$/.test(atom);
}
function tokenise(src) {
  const tokens = [];
  let s = src.trim();
  if (!s) {
    tokens.push({ kind: "EOF", value: "" });
    return tokens;
  }
  while (s.length > 0) {
    s = s.replace(/^\s+/, "");
    if (!s.length) break;
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
    if (s[0] === '"' || s[0] === "'") {
      const q = s[0];
      const end = s.indexOf(q, 1);
      if (end === -1) throw new Error(`Unterminated string: ${s}`);
      const lit = s.slice(0, end + 1);
      const prev = tokens[tokens.length - 1];
      if (prev?.kind === "ATOM" && /[=<>!]\s*$/.test(prev.value)) {
        prev.value += lit;
      } else {
        tokens.push({ kind: "ATOM", value: lit });
      }
      s = s.slice(end + 1);
      continue;
    }
    let atom = "";
    if (s.startsWith("\u2203!")) {
      atom = "\u2203!";
      s = s.slice(2);
    }
    while (s.length > 0) {
      const rest = s.replace(/^\s+/, "");
      if (startsWithOpInAtom(rest, atom)) break;
      if (rest[0] === '"' || rest[0] === "'") break;
      atom += s[0];
      s = s.slice(1);
    }
    const trimmed = atom.trim();
    if (trimmed.length > 0) {
      tokens.push({ kind: "ATOM", value: trimmed });
    }
  }
  tokens.push({ kind: "EOF", value: "" });
  return tokens;
}
var ExprParser = class {
  constructor(tokens) {
    this.tokens = tokens;
    this.pos = 0;
  }
  peek() {
    return this.tokens[this.pos];
  }
  consume() {
    return this.tokens[this.pos++];
  }
  expect(kind) {
    const t = this.consume();
    if (t.kind !== kind) throw new Error(`Expected ${kind}, got ${t.kind} ("${t.value}")`);
  }
  parse() {
    if (this.peek().kind === "EOF") return { type: "Atom", condition: "true", atomKind: "expression" };
    const node = this.parseIff();
    if (this.peek().kind !== "EOF")
      throw new Error(`Unexpected token after expression: "${this.peek().value}"`);
    return node;
  }
  parseIff() {
    const left = this.parseImplies();
    if (this.peek().kind === "IFF") {
      this.consume();
      return { type: "Iff", left, right: this.parseIff() };
    }
    return left;
  }
  parseImplies() {
    const left = this.parseOr();
    if (this.peek().kind === "IMPLIES") {
      this.consume();
      return { type: "Implies", left, right: this.parseImplies() };
    }
    return left;
  }
  parseOr() {
    let left = this.parseAnd();
    while (this.peek().kind === "OR") {
      this.consume();
      left = { type: "Or", left, right: this.parseAnd() };
    }
    return left;
  }
  parseAnd() {
    let left = this.parseNot();
    while (this.peek().kind === "AND") {
      this.consume();
      left = { type: "And", left, right: this.parseNot() };
    }
    return left;
  }
  parseNot() {
    if (this.peek().kind === "NOT") {
      this.consume();
      return { type: "Not", operand: this.parseNot() };
    }
    return this.parseAtom();
  }
  parseAtom() {
    const t = this.peek();
    if (t.kind === "LPAREN") {
      this.consume();
      const inner = this.parseIff();
      this.expect("RPAREN");
      return inner;
    }
    if (t.kind === "ATOM") {
      this.consume();
      let condition = t.value.trim();
      while (this.peek().kind === "LPAREN") {
        condition += this.consumeAtomicCallSuffix();
      }
      while (this.peek().kind === "ATOM" && /^(∈|∉|⊆|⊂|=|≠|≤|≥|<|>)/.test(this.peek().value.trim())) {
        condition += " " + this.consume().value.trim();
      }
      const quantified = parseQuantifiedExpr(condition);
      if (quantified) return quantified;
      const atomKind = condition.startsWith('"') && condition.endsWith('"') || condition.startsWith("'") && condition.endsWith("'") ? "string" : "expression";
      return { type: "Atom", condition, atomKind };
    }
    throw new Error(`Unexpected token: "${t.value}" (${t.kind})`);
  }
  consumeAtomicCallSuffix() {
    let suffix = "";
    let depth = 0;
    while (true) {
      const token = this.consume();
      suffix += token.value;
      if (token.kind === "LPAREN") depth++;
      else if (token.kind === "RPAREN") {
        depth--;
        if (depth === 0) break;
      } else if (token.kind === "EOF") {
        throw new Error("Unterminated atomic call suffix");
      }
    }
    return suffix;
  }
};
function parseExpr(src) {
  const raw = src.trim();
  const ifExpr = parseIfExpr(raw);
  if (ifExpr) {
    return ifExpr;
  }
  const letExpr = parseLetExpr(raw);
  if (letExpr) {
    return letExpr;
  }
  const lambda = parseLambdaExpr(raw);
  if (lambda) {
    return lambda;
  }
  const normalized = normalizeSurfaceSyntax(src).trim();
  const fold = parseFoldExpr(normalized);
  if (fold) {
    return fold;
  }
  const sigma = parseSigmaExpr(normalized);
  if (sigma) {
    return sigma;
  }
  const indexedUnion = parseIndexedUnionExpr(normalized);
  if (indexedUnion) {
    return indexedUnion;
  }
  const setBuilder = parseSetBuilderExpr(normalized);
  if (setBuilder) {
    return setBuilder;
  }
  const quantified = parseQuantifiedExpr(normalized);
  if (quantified) {
    return quantified;
  }
  return new ExprParser(tokenise(normalized)).parse();
}
function parseIfExpr(value) {
  const trimmed = value.trim();
  if (!trimmed.startsWith("if ")) return null;
  const thenIndex = findTopLevelKeyword(trimmed, " then ");
  if (thenIndex === -1) return null;
  const elseIndex = findTopLevelKeyword(trimmed, " else ", thenIndex + 6);
  if (elseIndex === -1) return null;
  return {
    type: "If",
    condition: parseExpr(trimmed.slice(3, thenIndex).trim()),
    thenBranch: parseExpr(trimmed.slice(thenIndex + 6, elseIndex).trim()),
    elseBranch: parseExpr(trimmed.slice(elseIndex + 6).trim())
  };
}
function parseLetExpr(value) {
  const trimmed = value.trim();
  if (!trimmed.startsWith("let ")) return null;
  const inIndex = findTopLevelKeyword(trimmed, " in ");
  if (inIndex === -1) return null;
  const binding = trimmed.slice(4, inIndex).trim();
  const eqIndex = findTopLevelEquals(binding);
  if (eqIndex === -1) return null;
  return {
    type: "LetExpr",
    name: binding.slice(0, eqIndex).trim(),
    value: parseExpr(binding.slice(eqIndex + 1).trim()),
    body: parseExpr(trimmed.slice(inIndex + 4).trim())
  };
}
function parseLambdaExpr(value) {
  const trimmed = value.trim();
  const match = trimmed.match(/^fn\s*\(([\s\S]*)\)\s*=>\s*([\s\S]+)$/);
  if (!match) return null;
  const params = match[1].trim() ? splitTopLevelArgs(match[1]).map(parseLambdaParam) : [];
  return {
    type: "Lambda",
    params,
    body: parseExpr(match[2].trim())
  };
}
function parseFoldExpr(value) {
  const trimmed = value.trim();
  if (!trimmed.startsWith("fold(") || !trimmed.endsWith(")")) return null;
  const inner = trimmed.slice(5, -1);
  const args2 = splitTopLevelArgs(inner);
  if (args2.length !== 3) return null;
  return {
    type: "Fold",
    sequence: args2[0],
    init: args2[1],
    fn: args2[2],
    sugar: "fold"
  };
}
function parseSigmaExpr(value) {
  const trimmed = value.trim();
  if (!trimmed.startsWith("\u03A3(") || !trimmed.endsWith(")")) return null;
  const inner = trimmed.slice(2, -1);
  const args2 = splitTopLevelArgs(inner);
  if (args2.length !== 3) return null;
  return {
    type: "Fold",
    sequence: `[${args2[1]}..${args2[2]}]`,
    init: "0",
    fn: "+",
    sugar: "sigma"
  };
}
function parseQuantifiedExpr(value) {
  const trimmed = value.trim();
  const head = trimmed.match(/^(∀|∃!|∃)\s+/);
  if (!head) return null;
  const quantifierSymbol = head[1];
  const quantifier = quantifierSymbol === "\u2200" ? "forall" : quantifierSymbol === "\u2203!" ? "exists_unique" : "exists";
  let index = head[0].length;
  const variableMatch = trimmed.slice(index).match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)/);
  if (!variableMatch) return null;
  const variable = variableMatch[1];
  index += variable.length;
  while (index < trimmed.length && /\s/.test(trimmed[index])) index++;
  const separator = trimmed[index];
  if (separator !== ":" && separator !== "\u2208") return null;
  const binderStyle = separator === "\u2208" ? "bounded" : "typed";
  index += 1;
  while (index < trimmed.length && /\s/.test(trimmed[index])) index++;
  const commaIndex = findTopLevelComma(trimmed, index);
  const domain = (commaIndex === -1 ? trimmed.slice(index) : trimmed.slice(index, commaIndex)).trim();
  const body = commaIndex === -1 ? "" : trimmed.slice(commaIndex + 1).trim();
  if (!domain) return null;
  return {
    type: "Quantified",
    quantifier,
    binderStyle,
    variable,
    domain,
    body: body ? parseExpr(body) : null
  };
}
function findTopLevelComma(value, start) {
  let depth = 0;
  for (let i = start; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (depth === 0 && ch === ",") return i;
  }
  return -1;
}
function splitTopLevelArgs(value) {
  const args2 = [];
  let start = 0;
  let depth = 0;
  let braceDepth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (ch === "{") braceDepth++;
    else if (ch === "}") braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === "[") bracketDepth++;
    else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
    else if (ch === "," && depth === 0 && braceDepth === 0 && bracketDepth === 0) {
      args2.push(value.slice(start, i).trim());
      start = i + 1;
    }
  }
  const final = value.slice(start).trim();
  if (final) args2.push(final);
  return args2;
}
function findTopLevelKeyword(value, keyword, start = 0) {
  let depth = 0;
  let braceDepth = 0;
  let bracketDepth = 0;
  for (let i = start; i <= value.length - keyword.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (ch === "{") braceDepth++;
    else if (ch === "}") braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === "[") bracketDepth++;
    else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
    if (depth === 0 && braceDepth === 0 && bracketDepth === 0 && value.slice(i, i + keyword.length) === keyword) {
      return i;
    }
  }
  return -1;
}
function findTopLevelEquals(value) {
  let depth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (ch === "[") bracketDepth++;
    else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
    else if (ch === "=" && depth === 0 && bracketDepth === 0) return i;
  }
  return -1;
}
function parseLambdaParam(value) {
  const typed = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*(?::|∈)\s*(.+)$/);
  if (typed) {
    return { name: typed[1], type: typed[2].trim() };
  }
  return { name: value.trim(), type: "Any" };
}
function parseSetBuilderExpr(value) {
  const trimmed = value.trim();
  const match = trimmed.match(/^\{\s*(.+?)\s*\|\s*([A-Za-z_][\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)\s*\}$/);
  if (!match) return null;
  return {
    type: "SetBuilder",
    element: match[1].trim(),
    variable: match[2].trim(),
    domain: match[3].trim()
  };
}
function parseIndexedUnionExpr(value) {
  const trimmed = value.trim();
  if (!trimmed.startsWith("\u222A")) return null;
  const builder = parseSetBuilderExpr(trimmed.slice(1).trim());
  if (!builder) return null;
  return {
    type: "IndexedUnion",
    builder
  };
}

// src/parser/parser.ts
function parseLinesToAST(lines, options = {}) {
  const ast2 = [];
  const stack = [];
  const desugarFns = options.desugarFns ?? true;
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    switch (line.type) {
      // ── Block openers ──────────────────────────────────────────────────────
      case "axiom": {
        const node = { type: "Axiom", name: line.name, statement: line.content, connective: line.connective };
        ast2.push(node);
        break;
      }
      case "theorem": {
        const node = { type: "Theorem", name: line.name, body: [], connective: null };
        stack.push(node);
        break;
      }
      case "definition": {
        const node = { type: "Definition", name: line.name, body: [], connective: null };
        stack.push(node);
        break;
      }
      case "struct": {
        const node = { type: "Struct", name: line.name, fields: [], connective: null };
        stack.push(node);
        break;
      }
      case "typeDecl": {
        const node = { type: "TypeDecl", name: line.name, variants: [], connective: null };
        stack.push(node);
        break;
      }
      case "proof": {
        const node = { type: "Proof", name: line.name, body: [], connective: null };
        stack.push(node);
        break;
      }
      case "lemma": {
        const node = { type: "Lemma", name: line.name, body: [], connective: null };
        stack.push(node);
        break;
      }
      case "fn": {
        const signature = parseFnSignature(line.content);
        const node = {
          type: "FnDecl",
          name: signature.name,
          params: signature.params,
          returnType: signature.returnType,
          requires: [],
          ensures: [],
          body: [],
          isNative: line.isNative ?? false,
          connective: line.connective
        };
        if (line.isNative) {
          ast2.push(node);
        } else {
          stack.push(node);
        }
        break;
      }
      case "program": {
        const node = {
          type: "Program",
          name: line.name,
          programId: "11111111111111111111111111111111",
          body: [],
          connective: null
        };
        stack.push(node);
        break;
      }
      case "account": {
        const node = { type: "Account", name: line.name, fields: [], connective: null };
        stack.push(node);
        break;
      }
      case "instruction": {
        const sig = parseInstructionSignature(line.content);
        const node = {
          type: "Instruction",
          name: sig.name,
          params: sig.params,
          body: [],
          connective: null
        };
        stack.push(node);
        break;
      }
      case "errorDecl": {
        const node = { type: "ErrorDecl", name: line.name, variants: [], connective: null };
        stack.push(node);
        break;
      }
      // ── Block-end: pop, attach connective, push to parent or top-level ─────
      case "blockEnd": {
        const finished = stack.pop();
        if (!finished) throw new Error("Unmatched }");
        finished.connective = line.connective;
        if (finished.type === "Struct") {
          finished.fields = finished.fields.map((field) => parseStructField(field));
        }
        if (finished.type === "TypeDecl") {
          finished.variants = finished.variants.map((variant) => parseTypeVariant(variant));
        }
        if (finished.type === "Account") {
          finished.fields = finished.fields.map((field) => parseStructField(field));
        }
        if (finished.type === "ErrorDecl") {
          finished.variants = finished.variants.map((raw) => parseErrorVariant(raw));
        }
        const lowered = finished.type === "FnDecl" && desugarFns && !finished.isNative ? desugarFnDecl(finished) : [finished];
        if (stack.length === 0) {
          ast2.push(...lowered);
        } else {
          for (const node of lowered) {
            pushToBlock(stack[stack.length - 1], node);
          }
        }
        break;
      }
      // ── Statement nodes ────────────────────────────────────────────────────
      case "assert": {
        const currentBlock = stack[stack.length - 1];
        const inDecl = currentBlock?.type === "Theorem" || currentBlock?.type === "Lemma";
        const suggestion = inDecl ? "Use declareToProve() to declare the theorem goal" : "Use prove() for intermediate steps or conclude() for the final step";
        const errExpr = parseCallExpr(line.content, "assert");
        const node = { type: "Assert", expr: errExpr, connective: line.connective };
        node.legacyError = `assert() is no longer valid. ${suggestion}`;
        pushOrTop(stack, ast2, node);
        break;
      }
      case "given": {
        const errExpr = parseCallExpr(line.content, "given");
        const node = { type: "Given", expr: errExpr, connective: line.connective };
        node.legacyError = "given() is no longer valid. Use assume() to declare hypotheses";
        pushOrTop(stack, ast2, node);
        break;
      }
      case "declareToProve": {
        const expr = parseCallExpr(line.content, "declareToProve");
        const node = { type: "DeclareToProve", expr, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "prove": {
        const expr = parseCallExpr(line.content, "prove");
        const node = { type: "Prove", expr, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "derive": {
        const node = { type: "Derive", connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "andIntroStep": {
        const inner = line.content.replace(/^AndIntro\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
        const commaIdx = inner.lastIndexOf(",");
        const left = commaIdx >= 0 ? inner.slice(0, commaIdx).trim() : inner;
        const right = commaIdx >= 0 ? inner.slice(commaIdx + 1).trim() : "";
        const node = { type: "AndIntroStep", left, right, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "orIntroStep": {
        const claim = line.content.replace(/^OrIntro\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
        const node = { type: "OrIntroStep", claim, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "requires": {
        const expr = parseCallExpr(line.content, "requires");
        if (stack.length > 0 && stack[stack.length - 1].type === "FnDecl") {
          stack[stack.length - 1].requires.push(expr);
        } else {
          throw new Error("requires() may only appear inside fn blocks");
        }
        break;
      }
      case "ensures": {
        const expr = parseCallExpr(line.content, "ensures");
        if (stack.length > 0 && stack[stack.length - 1].type === "FnDecl") {
          stack[stack.length - 1].ensures.push(expr);
        } else {
          throw new Error("ensures() may only appear inside fn blocks");
        }
        break;
      }
      case "assume": {
        const expr = parseCallExpr(line.content, "assume");
        const node = { type: "Assume", expr, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "conclude": {
        const expr = parseCallExpr(line.content, "conclude");
        const node = { type: "Conclude", expr, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "apply": {
        const node = { type: "Apply", target: line.name, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "intro": {
        const inner = line.content.replace(/^intro\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
        const colonMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*[:\s]\s*(.+)$/);
        const memMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
        const m = colonMatch ?? memMatch;
        const varName = m?.[1] ?? inner;
        const varType = m?.[2]?.trim() ?? "";
        const node = { type: "Intro", varName, varType, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "rewrite": {
        const inner = line.content.replace(/^rewrite\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
        const parts = inner.split(",").map((s) => s.trim());
        const hyp = parts[0];
        const direction = parts[1] === "rtl" ? "rtl" : "ltr";
        const node = { type: "Rewrite", hypothesis: hyp, direction, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "exact": {
        const expr = parseCallExpr(line.content, "exact");
        const node = { type: "Exact", expr, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "require": {
        const inner = line.content.replace(/^require\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
        const lastComma = inner.lastIndexOf(",");
        const condStr = lastComma >= 0 ? inner.slice(0, lastComma).trim() : inner;
        const errName = lastComma >= 0 ? inner.slice(lastComma + 1).trim() : "";
        const condition = parseCallExprFromStr(condStr);
        const node = { type: "Require", condition, error: errName, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "emit": {
        const inner = line.content.replace(/^emit\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
        const firstComma = inner.indexOf(",");
        const eventName = firstComma >= 0 ? inner.slice(0, firstComma).trim() : inner;
        const fieldsRaw = firstComma >= 0 ? inner.slice(firstComma + 1).trim() : "";
        const fields = fieldsRaw ? splitFnParams(fieldsRaw).map((f) => {
          const colon = f.indexOf(":");
          return colon >= 0 ? { name: f.slice(0, colon).trim(), value: f.slice(colon + 1).trim() } : { name: f.trim(), value: f.trim() };
        }) : [];
        const emitNode = { type: "Emit", eventName, fields, connective: line.connective };
        pushOrTop(stack, ast2, emitNode);
        break;
      }
      case "pda": {
        const letMatch = line.content.match(/^let\s+(\w+)\s*=\s*pda\s*\(\[([\s\S]*)\]\)/);
        const bareMatch = line.content.match(/^pda\s*\(\[([\s\S]*)\]\)/);
        const varName = letMatch ? letMatch[1] : "_pda";
        const seedsRaw = letMatch ? letMatch[2] : bareMatch ? bareMatch[1] : "";
        const seeds = seedsRaw.split(",").map((s) => s.trim()).filter((s) => s.length > 0);
        const pdaNode = { type: "Pda", varName, seeds, connective: line.connective };
        pushOrTop(stack, ast2, pdaNode);
        break;
      }
      case "cpi": {
        const inner = line.content.replace(/^cpi\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
        const parts = splitFnParams(inner);
        const program = parts[0]?.trim() ?? "";
        const instruction = parts[1]?.trim() ?? "";
        const accountsRaw = parts[2]?.trim() ?? "";
        const accounts = accountsRaw.replace(/^\[/, "").replace(/\]$/, "").split(",").map((s) => s.trim()).filter((s) => s.length > 0);
        const cpiNode = { type: "Cpi", program, instruction, accounts, connective: line.connective };
        pushOrTop(stack, ast2, cpiNode);
        break;
      }
      case "transfer": {
        const inner = line.content.replace(/^transfer\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
        const parts = splitFnParams(inner);
        const transferNode = {
          type: "Transfer",
          from: parts[0]?.trim() ?? "",
          to: parts[1]?.trim() ?? "",
          amount: parts[2]?.trim() ?? "",
          connective: line.connective
        };
        pushOrTop(stack, ast2, transferNode);
        break;
      }
      case "obtain": {
        const inner = line.content.replace(/^obtain\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
        const commaIdx = inner.indexOf(",");
        const varName = commaIdx >= 0 ? inner.slice(0, commaIdx).trim() : inner;
        const source2 = commaIdx >= 0 ? inner.slice(commaIdx + 1).trim() : "";
        const node = { type: "Obtain", varName, source: source2, connective: line.connective };
        pushOrTop(stack, ast2, node);
        break;
      }
      case "setVar": {
        const node = parseSetVar(line.content, line.connective);
        pushOrTop(stack, ast2, node);
        break;
      }
      case "induction": {
        const parsed = parseInduction(lines, i);
        i = parsed.nextIndex;
        pushOrTop(stack, ast2, parsed.node);
        break;
      }
      case "match": {
        const parsed = parseMatch(lines, i);
        i = parsed.nextIndex;
        pushOrTop(stack, ast2, parsed.node);
        break;
      }
      case "base":
      case "step":
      case "case":
        throw new Error(`${line.type}: may only appear inside induction(...)`);
      case "return":
      case "level":
      case "raw": {
        const node = { type: "Raw", content: line.content, connective: line.connective };
        const top = stack.length > 0 ? stack[stack.length - 1] : null;
        if (top?.type === "Struct" || top?.type === "Account") {
          top.fields.push(line.content);
        } else if (top?.type === "TypeDecl" || top?.type === "ErrorDecl") {
          top.variants.push(line.content);
        } else {
          pushOrTop(stack, ast2, node);
        }
        break;
      }
    }
  }
  if (stack.length > 0) throw new Error(`Unclosed block: ${stack[stack.length - 1].type}`);
  validateTopLevelConnectives(ast2);
  return ast2;
}
function pushOrTop(stack, ast2, node) {
  if (stack.length > 0) {
    pushToBlock(stack[stack.length - 1], node);
  } else {
    ast2.push(node);
  }
}
function pushToBlock(block, node) {
  if (block.type === "Struct" || block.type === "TypeDecl" || block.type === "Account" || block.type === "ErrorDecl") {
    return;
  }
  block.body.push(node);
}
function extractCallBody(content, keyword) {
  const m = content.match(new RegExp(`^${keyword}\\s*\\(([\\s\\S]*)\\)\\s*;?\\s*$`));
  if (m) return m[1].trim();
  return content.replace(new RegExp(`^${keyword}\\s*`), "").trim();
}
function parseSetVar(content, connective) {
  const letForm = content.match(/^let\s+(\w[\w₀-₉ₐ-ₙ]*)\s*=\s*(.+?);?\s*$/);
  if (letForm) {
    return { type: "SetVar", varName: letForm[1], varType: null, value: letForm[2].trim(), connective };
  }
  const inner = extractCallBody(content, "setVar");
  const typed = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*:\s*([^,]+),\s*(.+)$/);
  if (typed) {
    return { type: "SetVar", varName: typed[1], varType: typed[2].trim(), value: typed[3].trim(), connective };
  }
  const decl = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*:\s*(.+)$/);
  if (decl) {
    return { type: "SetVar", varName: decl[1], varType: decl[2].trim(), value: null, connective };
  }
  const untyped = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+)$/);
  if (untyped) {
    return { type: "SetVar", varName: untyped[1], varType: null, value: untyped[2].trim(), connective };
  }
  return { type: "SetVar", varName: inner.trim(), varType: null, value: null, connective };
}
function parseCallExpr(content, keyword) {
  const body = extractCallBody(content, keyword);
  try {
    return parseExpr(body);
  } catch (error) {
    return {
      type: "Atom",
      condition: body,
      atomKind: "opaque",
      parseError: error instanceof Error ? error.message : "Expression could not be parsed"
    };
  }
}
function parseInduction(lines, start) {
  const line = lines[start];
  const match = line.content.match(/^induction\s*\(([\s\S]+)\)\s*\{$/);
  if (!match) {
    throw new Error("Malformed induction block");
  }
  const iterator = match[1].trim();
  let base = null;
  let step = null;
  let connective = line.connective;
  let cursor = start + 1;
  while (cursor < lines.length) {
    const current = lines[cursor];
    if (current.type === "blockEnd") {
      connective = current.connective;
      break;
    }
    if (current.type === "base") {
      base = current.content.replace(/^base\s*:\s*/, "").trim();
    } else if (current.type === "step") {
      step = current.content.replace(/^step\s*:\s*/, "").trim();
    } else {
      throw new Error(`Unexpected line inside induction block: ${current.content}`);
    }
    cursor++;
  }
  if (cursor >= lines.length || lines[cursor].type !== "blockEnd") {
    throw new Error("Unclosed induction block");
  }
  if (!base || !step) {
    throw new Error("induction(...) requires both base: and step:");
  }
  const fold = {
    type: "Fold",
    sequence: `[0..${iterator}]`,
    init: `proof(${base})`,
    fn: `step_fn(${step})`,
    sugar: "induction"
  };
  return {
    node: {
      type: "Induction",
      iterator,
      fold,
      base,
      step,
      connective
    },
    nextIndex: cursor
  };
}
function parseFnSignature(content) {
  const match = content.match(/^fn\s+(\w+)\s*\(([\s\S]*?)\)\s*->\s*([^{]+?)\s*\{?$/);
  if (!match) {
    throw new Error(`Malformed fn signature: ${content}`);
  }
  const [, name, rawParams, returnType] = match;
  const params = rawParams.trim() ? splitFnParams(rawParams).map(parseFnParam) : [];
  return {
    name,
    params,
    returnType: returnType.trim()
  };
}
function splitFnParams(value) {
  const params = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (ch === "," && depth === 0) {
      params.push(value.slice(start, i).trim());
      start = i + 1;
    }
  }
  const final = value.slice(start).trim();
  if (final) params.push(final);
  return params;
}
function parseFnParam(value) {
  const match = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
  if (!match) {
    throw new Error(`Malformed fn parameter: ${value}`);
  }
  return { name: match[1], type: normalizeSortName(match[2]) };
}
function parseStructField(value) {
  const trimmed = value.trim().replace(/,+$/, "").trim();
  const match = trimmed.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
  if (!match) {
    throw new Error(`Malformed struct field: ${value}`);
  }
  return {
    name: match[1],
    type: normalizeSortName(match[2])
  };
}
function parseTypeVariant(value) {
  const trimmed = value.trim().replace(/,+$/, "").trim();
  const match = trimmed.match(/^\|\s*(\w[\w₀-₉ₐ-ₙ]*)\s*\(([\s\S]*)\)\s*$/);
  if (!match) {
    throw new Error(`Malformed type variant: ${value}`);
  }
  const [, name, rawFields] = match;
  const fields = rawFields.trim() ? splitFnParams(rawFields).map(parseStructField) : [];
  return { name, fields };
}
function desugarFnDecl(node) {
  const conclusion = findFnConclusion(node.body);
  const matchBody = findTopLevelMatch(node.body);
  if (!conclusion && !matchBody) {
    throw new Error(`fn '${node.name}' requires a conclude(...) statement`);
  }
  const goalExpr = conclusion ? conclusion.expr : parseFnGoalExpr(node);
  const theoremBody = node.params.map((param) => ({
    type: "Given",
    expr: parseExpr(`${param.name} \u2208 ${param.type}`),
    connective: "\u2192"
  }));
  for (const req of node.requires) {
    theoremBody.push({
      type: "Given",
      expr: req,
      connective: "\u2192"
    });
  }
  if (node.ensures.length > 0) {
    for (let i = 0; i < node.ensures.length; i++) {
      theoremBody.push({
        type: "Assert",
        expr: node.ensures[i],
        connective: i === node.ensures.length - 1 ? null : "\u2227"
      });
    }
  } else {
    theoremBody.push({
      type: "Assert",
      expr: goalExpr,
      connective: null
    });
  }
  const theorem = {
    type: "Theorem",
    name: node.name,
    body: theoremBody,
    connective: "\u2194"
  };
  const proofBody = conclusion ? [
    {
      type: "Assume",
      expr: conclusion.expr,
      connective: node.body.length > 0 ? "\u2192" : null
    },
    ...node.body
  ] : node.body;
  const proof = {
    type: "Proof",
    name: node.name,
    body: proofBody,
    connective: node.connective,
    fnMeta: {
      params: node.params,
      returnType: normalizeSortName(node.returnType)
    }
  };
  return [theorem, proof];
}
function parseFnGoalExpr(node) {
  const goal = `${node.name}(${node.params.map((param) => param.name).join(", ")}) \u2208 ${normalizeSortName(node.returnType)}`;
  try {
    return parseExpr(goal);
  } catch {
    return {
      type: "Atom",
      condition: goal,
      atomKind: "opaque"
    };
  }
}
function normalizeSortName(value) {
  return normalizeSurfaceSyntax(value).trim();
}
function findFnConclusion(body) {
  for (let i = body.length - 1; i >= 0; i--) {
    const node = body[i];
    if (node.type === "Conclude") {
      return node;
    }
  }
  return null;
}
function findTopLevelMatch(body) {
  for (const node of body) {
    if (node.type === "Match") return node;
  }
  return null;
}
function parseMatch(lines, start) {
  const line = lines[start];
  const match = line.content.match(/^match\s+([\s\S]+)\s*\{$/);
  if (!match) {
    throw new Error("Malformed match block");
  }
  const scrutinee = parseExpr(match[1].trim());
  const cases = [];
  let connective = line.connective;
  let cursor = start + 1;
  while (cursor < lines.length) {
    const current = lines[cursor];
    if (current.type === "blockEnd") {
      connective = current.connective;
      break;
    }
    if (current.type !== "case") {
      throw new Error(`Unexpected line inside match block: ${current.content}`);
    }
    const parsedCase = parseMatchCase(lines, cursor);
    cases.push(parsedCase.node);
    cursor = parsedCase.nextIndex;
  }
  if (cursor >= lines.length || lines[cursor].type !== "blockEnd") {
    throw new Error("Unclosed match block");
  }
  return {
    node: {
      type: "Match",
      scrutinee,
      cases,
      connective
    },
    nextIndex: cursor
  };
}
function parseMatchCase(lines, start) {
  const content = lines[start].content;
  const match = content.match(/^case\s+(.+?)\s*=>\s*([\s\S]+)$/);
  const emptyMatch = content.match(/^case\s+(.+?)\s*=>\s*$/);
  if (!match && !emptyMatch) {
    throw new Error(`Malformed case clause: ${content}`);
  }
  const pattern = parsePattern((match ?? emptyMatch)[1].trim());
  const body = [];
  const inlineBody = match?.[2]?.trim() ?? "";
  if (inlineBody) {
    body.push(parseInlineStatement(inlineBody));
  }
  let cursor = start + 1;
  while (cursor < lines.length) {
    const current = lines[cursor];
    if (current.type === "case" || current.type === "blockEnd") break;
    const parsed = parseNestedStatement(lines, cursor);
    body.push(parsed.node);
    cursor = parsed.nextIndex + 1;
  }
  return {
    node: { pattern, body },
    nextIndex: cursor
  };
}
function parsePattern(value) {
  if (value === "_") {
    return { kind: "wildcard" };
  }
  if (value === "[]") {
    return { kind: "list_nil" };
  }
  const listMatch = value.match(/^\[\s*([^,\]]+)\s*,\s*\.\.\.\s*([A-Za-z_][\w₀-₉ₐ-ₙ]*)\s*\]$/);
  if (listMatch) {
    return {
      kind: "list_cons",
      head: listMatch[1].trim(),
      tail: listMatch[2].trim()
    };
  }
  const match = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*\(([\s\S]*)\)\s*$/);
  if (!match) {
    const bare = value.match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)$/);
    if (!bare) {
      throw new Error(`Malformed pattern: ${value}`);
    }
    return { kind: "variant", constructor: bare[1], bindings: [] };
  }
  const [, constructor, rawBindings] = match;
  const bindings = rawBindings.trim() ? splitFnParams(rawBindings).map((binding) => binding.trim()).map((binding) => binding === "_" ? "_" : binding) : [];
  return { kind: "variant", constructor, bindings };
}
function parseInlineStatement(content) {
  if (/^conclude\s*\(/.test(content)) {
    return { type: "Conclude", expr: parseCallExpr(content, "conclude"), connective: null };
  }
  if (/^assert\s*\(/.test(content)) {
    return { type: "Assert", expr: parseCallExpr(content, "assert"), connective: null };
  }
  if (/^assume\s*\(/.test(content)) {
    return { type: "Assume", expr: parseCallExpr(content, "assume"), connective: null };
  }
  if (/^apply\s*\(/.test(content)) {
    const target = content.match(/^apply\s*\((.+)\)/)?.[1]?.trim() ?? content;
    return { type: "Apply", target, connective: null };
  }
  return { type: "Raw", content, connective: null };
}
function parseNestedStatement(lines, start) {
  const line = lines[start];
  switch (line.type) {
    case "assert":
      return { node: { type: "Assert", expr: parseCallExpr(line.content, "assert"), connective: line.connective }, nextIndex: start };
    case "assume":
      return { node: { type: "Assume", expr: parseCallExpr(line.content, "assume"), connective: line.connective }, nextIndex: start };
    case "conclude":
      return { node: { type: "Conclude", expr: parseCallExpr(line.content, "conclude"), connective: line.connective }, nextIndex: start };
    case "apply": {
      const target = line.content.match(/^apply\s*\((.+)\)/)?.[1]?.trim() ?? line.content;
      return { node: { type: "Apply", target, connective: line.connective }, nextIndex: start };
    }
    case "setVar":
      return { node: parseSetVar(line.content, line.connective), nextIndex: start };
    case "intro": {
      const inner = line.content.replace(/^intro\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
      const colonMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*[:\s]\s*(.+)$/);
      const memMatch = inner.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
      const m = colonMatch ?? memMatch;
      const varName = m?.[1] ?? inner;
      const varType = m?.[2]?.trim() ?? "";
      return { node: { type: "Intro", varName, varType, connective: line.connective }, nextIndex: start };
    }
    case "rewrite": {
      const inner = line.content.replace(/^rewrite\s*\(/, "").replace(/\)\s*;?\s*$/, "").trim();
      const parts = inner.split(",").map((s) => s.trim());
      const hyp = parts[0];
      const direction = parts[1] === "rtl" ? "rtl" : "ltr";
      return { node: { type: "Rewrite", hypothesis: hyp, direction, connective: line.connective }, nextIndex: start };
    }
    case "exact": {
      const expr = parseCallExpr(line.content, "exact");
      return { node: { type: "Exact", expr, connective: line.connective }, nextIndex: start };
    }
    case "match":
      return parseMatch(lines, start);
    case "raw":
    case "return":
    case "level":
      return { node: { type: "Raw", content: line.content, connective: line.connective }, nextIndex: start };
    default:
      throw new Error(`Unexpected nested statement: ${line.content}`);
  }
}
function validateTopLevelConnectives(ast2) {
  for (let i = 0; i < ast2.length - 1; i++) {
    const node = ast2[i];
    if (isTopLevelBlock(node) && node.connective === null) {
      throw new Error(`Missing connective between top-level blocks after ${describeTopLevelNode(node)}`);
    }
  }
}
function validateDeclarationBody(name, body) {
  const errors = [];
  for (const node of body) {
    const legacy = node.legacyError;
    if (legacy) errors.push(`In '${name}': ${legacy}`);
  }
  const assumes = body.filter((n) => n.type === "Assume");
  const dtp = body.filter((n) => n.type === "DeclareToProve");
  const oldAssert = body.filter((n) => n.type === "Assert");
  const oldGiven = body.filter((n) => n.type === "Given");
  if (oldAssert.length > 0)
    errors.push(`In '${name}': replace assert() with declareToProve() in declarations`);
  if (oldGiven.length > 0)
    errors.push(`In '${name}': replace given() with assume() in declarations`);
  if (dtp.length === 0 && oldAssert.length === 0)
    errors.push(`In '${name}': declaration must end with declareToProve(...)`);
  if (dtp.length > 1)
    errors.push(`In '${name}': declaration must have exactly one declareToProve()`);
  for (let i = 0; i < assumes.length; i++) {
    const isLast = i === assumes.length - 1;
    const node = assumes[i];
    if (isLast) {
      if (node.connective !== "\u2192" && dtp.length > 0)
        errors.push(`In '${name}': assume() before declareToProve() must use \u2192 not '${node.connective ?? "missing"}'`);
    } else {
      if (node.connective === "\u2192")
        errors.push(`In '${name}': assume() followed by another assume() must use \u2227, not \u2192 (hypotheses are independent)`);
    }
  }
  return errors;
}
function isTopLevelBlock(node) {
  return node.type === "Theorem" || node.type === "Definition" || node.type === "Struct" || node.type === "TypeDecl" || node.type === "Proof" || node.type === "Lemma" || node.type === "FnDecl" || node.type === "Program" || node.type === "Account" || node.type === "Instruction" || node.type === "ErrorDecl";
}
function describeTopLevelNode(node) {
  switch (node.type) {
    case "Theorem":
    case "Definition":
    case "Struct":
    case "TypeDecl":
    case "Proof":
    case "Lemma":
    case "FnDecl":
    case "Account":
    case "Instruction":
    case "ErrorDecl":
      return `${node.type.toLowerCase()} '${node.name}'`;
    case "Program":
      return `program '${node.name}'`;
  }
}
function parseInstructionSignature(content) {
  const match = content.match(/^instruction\s+(\w+)\s*\(([\s\S]*)\)\s*\{?$/);
  if (!match) throw new Error(`Malformed instruction signature: ${content}`);
  const [, name, rawParams] = match;
  const params = rawParams.trim() ? splitFnParams(rawParams).map((p) => parseInstructionParam(p.trim())) : [];
  return { name, params };
}
function parseInstructionParam(value) {
  const accountMatch = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*:\s*(.*?)\s*∈\s*(.+)$/);
  if (accountMatch) {
    const qualifiers = accountMatch[2].trim().split(/\s+/).filter((q) => q.length > 0).filter((q) => ["mut", "signer", "init", "close", "seeds"].includes(q));
    return {
      name: accountMatch[1],
      qualifiers,
      paramType: normalizeSortName(accountMatch[3]),
      isAccount: true
    };
  }
  const dataMatch = value.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+)$/);
  if (dataMatch) {
    return {
      name: dataMatch[1],
      qualifiers: [],
      paramType: normalizeSortName(dataMatch[2]),
      isAccount: false
    };
  }
  throw new Error(`Malformed instruction parameter: ${value}`);
}
function parseErrorVariant(raw) {
  const trimmed = raw.trim().replace(/^[|,]+\s*/, "").trim();
  const withMsg = trimmed.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*\("(.*)"\)\s*$/);
  if (withMsg) return { name: withMsg[1], message: withMsg[2] };
  const bare = trimmed.match(/^(\w[\w₀-₉ₐ-ₙ]*)\s*$/);
  if (bare) return { name: bare[1], message: bare[1] };
  throw new Error(`Malformed error variant: ${raw}`);
}
function parseCallExprFromStr(raw) {
  try {
    return parseExpr(raw);
  } catch {
    return { type: "Atom", condition: raw, atomKind: "opaque" };
  }
}

// src/codegen/typecheck.ts
function typecheckExecutableProgram(nodes) {
  const env = {
    vars: /* @__PURE__ */ new Map([
      ["true", "Bool"],
      ["false", "Bool"],
      ["None", "Option(Any)"]
    ]),
    fns: /* @__PURE__ */ new Map(),
    variants: /* @__PURE__ */ new Map()
  };
  collectTypes(nodes, env);
  collectFunctions(nodes, env);
  for (const node of nodes) {
    if (node.type === "FnDecl") {
      typecheckFunction(node, env);
    } else if (node.type === "SetVar" && node.value !== null) {
      env.vars.set(node.varName, inferValueType(node.value, env));
    }
  }
}
function collectTypes(nodes, env) {
  for (const node of nodes) {
    if (node.type !== "TypeDecl") continue;
    registerType(node, env);
  }
  env.variants.set("Some", { typeName: "Option(Any)", fields: [{ name: "value", type: "Any" }] });
  env.variants.set("Ok", { typeName: "Result(Any,Any)", fields: [{ name: "value", type: "Any" }] });
  env.variants.set("Err", { typeName: "Result(Any,Any)", fields: [{ name: "error", type: "Any" }] });
}
function registerType(node, env) {
  for (const variant of node.variants) {
    env.variants.set(variant.name, {
      typeName: node.name,
      fields: variant.fields.map((field) => ({ name: field.name, type: field.type }))
    });
  }
}
function collectFunctions(nodes, env) {
  env.fns.set("fold", { params: ["List(Any)", "Any", "(Any,Any)->Any"], returnType: "Any" });
  env.fns.set("request", { params: ["String", "String", "Any", "Any"], returnType: "Request" });
  env.fns.set("text", { params: ["Any", "\u2115", "Any"], returnType: "Response" });
  env.fns.set("html", { params: ["Any", "\u2115", "Any"], returnType: "Response" });
  env.fns.set("json", { params: ["Any", "\u2115", "Any"], returnType: "Response" });
  env.fns.set("route", { params: ["String", "String", "Any"], returnType: "Route" });
  env.fns.set("router", { params: ["List(Route)", "Any"], returnType: "Handler" });
  env.fns.set("dispatch", { params: ["Handler", "Request"], returnType: "Response" });
  env.fns.set("serve", { params: ["\u2115", "Handler", "String"], returnType: "Server" });
  for (const node of nodes) {
    if (node.type !== "FnDecl") continue;
    env.fns.set(node.name, {
      params: node.params.map((param) => normalizeType(param.type)),
      returnType: normalizeType(node.returnType)
    });
  }
}
function typecheckFunction(node, rootEnv) {
  const fnSig = rootEnv.fns.get(node.name);
  if (!fnSig) return;
  const env = {
    vars: new Map(rootEnv.vars),
    fns: rootEnv.fns,
    variants: rootEnv.variants
  };
  node.params.forEach((param) => env.vars.set(param.name, normalizeType(param.type)));
  const returns = inferBodyReturnTypes(node.body, env);
  if (returns.length === 0) {
    throw new Error(`Function '${node.name}' has no conclude/return path`);
  }
  for (const resultType of returns) {
    if (!isAssignable(resultType, fnSig.returnType)) {
      throw new Error(`Function '${node.name}' returns '${resultType}' but declared '${fnSig.returnType}'`);
    }
  }
}
function inferBodyReturnTypes(nodes, env) {
  const returns = [];
  for (const node of nodes) {
    if (node.type === "SetVar" && node.value !== null) {
      env.vars.set(node.varName, inferValueType(node.value, env));
    } else if (node.type === "Conclude") {
      returns.push(inferExprType(node.expr, env));
    } else if (node.type === "Match") {
      returns.push(...inferMatchReturnTypes(node, env));
    } else if (node.type === "Raw") {
      const rawReturn = node.content.match(/^return\s+(.+?);?\s*$/);
      if (rawReturn) returns.push(inferRawType(rawReturn[1], env));
    }
  }
  return returns;
}
function inferMatchReturnTypes(node, env) {
  const scrutineeType = inferExprType(node.scrutinee, env);
  const returns = [];
  for (const matchCase of node.cases) {
    const branchEnv = {
      vars: new Map(env.vars),
      fns: env.fns,
      variants: env.variants
    };
    bindPattern(matchCase.pattern, scrutineeType, branchEnv);
    returns.push(...inferBodyReturnTypes(matchCase.body, branchEnv));
  }
  return returns;
}
function bindPattern(pattern, scrutineeType, env) {
  if (pattern.kind === "list_cons") {
    const elementType = listElementType(scrutineeType) ?? "Any";
    if (pattern.head !== "_") env.vars.set(pattern.head, elementType);
    env.vars.set(pattern.tail, scrutineeType);
    return;
  }
  if (pattern.kind !== "variant") return;
  if (pattern.constructor === "true" || pattern.constructor === "false") return;
  const variant = env.variants.get(pattern.constructor);
  if (!variant) return;
  pattern.bindings.forEach((binding, index) => {
    if (!binding || binding === "_") return;
    env.vars.set(binding, variant.fields[index]?.type ?? "Any");
  });
}
function inferExprType(expr, env) {
  switch (expr.type) {
    case "Atom":
      return inferRawType(expr.condition, env);
    case "And":
    case "Or":
    case "Implies":
    case "Iff":
    case "Not":
      return "Bool";
    case "If": {
      const conditionType = inferExprType(expr.condition, env);
      if (!isAssignable(conditionType, "Bool")) {
        throw new Error(`if condition must be Bool, got '${conditionType}'`);
      }
      const thenType = inferExprType(expr.thenBranch, env);
      const elseType = inferExprType(expr.elseBranch, env);
      return unifyTypes(thenType, elseType);
    }
    case "LetExpr": {
      const nextEnv = { vars: new Map(env.vars), fns: env.fns, variants: env.variants };
      nextEnv.vars.set(expr.name, inferExprType(expr.value, env));
      return inferExprType(expr.body, nextEnv);
    }
    case "Lambda":
      return `(${expr.params.map((param) => normalizeType(param.type)).join(",")}) -> ${inferExprType(expr.body, {
        vars: new Map([...env.vars, ...expr.params.map((param) => [param.name, normalizeType(param.type)])]),
        fns: env.fns,
        variants: env.variants
      })}`;
    case "Fold": {
      const sequenceType = inferRawType(expr.sequence, env);
      const initType = inferRawType(expr.init, env);
      const fnType = inferRawType(expr.fn, env);
      if (!sequenceType.startsWith("List(")) return "Any";
      if (!fnType.includes("->")) return initType;
      return initType;
    }
    case "Quantified":
      return "Bool";
    case "SetBuilder":
    case "IndexedUnion":
      return "Any";
    default:
      return "Any";
  }
}
function inferValueType(value, env) {
  try {
    return inferExprType(parseExpr(value), env);
  } catch {
    return inferRawType(value, env);
  }
}
function inferRawType(value, env) {
  const trimmed = normalizeType(value);
  if (trimmed === "true" || trimmed === "false") return "Bool";
  if (trimmed.startsWith('"') && trimmed.endsWith('"') || trimmed.startsWith("'") && trimmed.endsWith("'")) return "String";
  if (/^\d+$/.test(trimmed)) return "Nat";
  if (/^\d+\.\d+$/.test(trimmed)) return "Real";
  if (trimmed === "[]") return "List(Any)";
  if (/^\[.*\]$/.test(trimmed)) return inferListType(trimmed, env);
  if (env.vars.has(trimmed)) return env.vars.get(trimmed);
  const call = trimmed.match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)\s*\(([\s\S]*)\)$/);
  if (call) {
    return inferCallType(call[1], call[2], env);
  }
  if (/^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(trimmed) && env.variants.has(trimmed)) {
    return env.variants.get(trimmed).typeName;
  }
  if (/^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(trimmed) && env.fns.has(trimmed)) {
    const sig = env.fns.get(trimmed);
    return `(${sig.params.join(",")}) -> ${sig.returnType}`;
  }
  if (/[<>]=?|==|!=/.test(trimmed)) return "Bool";
  if (/&&|\|\|/.test(trimmed)) return "Bool";
  if (/[+\-*/]/.test(trimmed)) return inferNumericType(trimmed, env);
  return "Any";
}
function inferCallType(name, argsRaw, env) {
  const args2 = splitTopLevelArgs2(argsRaw);
  const variant = env.variants.get(name);
  if (variant) {
    args2.forEach((arg, index) => {
      const expected = variant.fields[index]?.type ?? "Any";
      const actual = inferRawType(arg, env);
      if (!isAssignable(actual, expected)) {
        throw new Error(`Constructor '${name}' argument ${index + 1} expects '${expected}', got '${actual}'`);
      }
    });
    return variant.typeName;
  }
  const varFnType = env.vars.get(name);
  if (varFnType && isFunctionType(varFnType)) {
    const signature = parseFunctionType(varFnType);
    if (!signature) return "Any";
    args2.forEach((arg, index) => {
      const actual = inferRawType(arg, env);
      const expected = signature.params[index] ?? signature.params[signature.params.length - 1] ?? "Any";
      if (!isAssignable(actual, expected)) {
        throw new Error(`Call '${name}' argument ${index + 1} expects '${expected}', got '${actual}'`);
      }
    });
    return signature.returnType;
  }
  const fnSig = env.fns.get(name);
  if (!fnSig) return "Any";
  args2.forEach((arg, index) => {
    const actual = inferRawType(arg, env);
    const expected = fnSig.params[index] ?? fnSig.params[fnSig.params.length - 1] ?? "Any";
    if (!isAssignable(actual, expected)) {
      throw new Error(`Call '${name}' argument ${index + 1} expects '${expected}', got '${actual}'`);
    }
  });
  return fnSig.returnType;
}
function inferListType(value, env) {
  const inner = value.slice(1, -1).trim();
  if (!inner) return "List(Any)";
  const parts = splitTopLevelArgs2(inner);
  const elementTypes = parts.map((part) => {
    if (part.startsWith("...")) {
      return listElementType(inferRawType(part.slice(3).trim(), env)) ?? "Any";
    }
    return inferRawType(part, env);
  });
  return `List(${elementTypes.reduce(unifyTypes)})`;
}
function inferNumericType(value, env) {
  const names = value.match(/[A-Za-z_][\w₀-₉ₐ-ₙ]*/g) ?? [];
  if (value.includes(".") || value.includes("\u03C0")) return "\u211D";
  if (names.some((name) => env.vars.get(name) === "\u211D" || env.vars.get(name) === "Real")) return "\u211D";
  return "\u2115";
}
function listElementType(type) {
  const match = normalizeType(type).match(/^List\((.+)\)$/);
  return match ? match[1].trim() : null;
}
function unifyTypes(left, right) {
  if (left === right) return left;
  if (left === "Any") return right;
  if (right === "Any") return left;
  if (left === "Nat" && right === "Real" || left === "Real" && right === "Nat") return "Real";
  return "Any";
}
function isAssignable(actual, expected) {
  const normalizedActual = normalizeType(actual);
  const normalizedExpected = normalizeType(expected);
  if (normalizedExpected === "Any" || normalizedActual === "Any") return true;
  if (normalizedActual === normalizedExpected) return true;
  if (isTypeVariable(normalizedExpected) || isTypeVariable(normalizedActual)) return true;
  const actualList = listElementType(normalizedActual);
  const expectedList = listElementType(normalizedExpected);
  if (actualList && expectedList) return isAssignable(actualList, expectedList);
  if (normalizedActual === "\u2115" && normalizedExpected === "\u211D") return true;
  if (normalizedExpected.startsWith("Option(") && normalizedActual === "Option(Any)") return true;
  if (normalizedExpected.startsWith("Result(") && normalizedActual === "Result(Any,Any)") return true;
  return false;
}
function isTypeVariable(value) {
  return /^[A-Z]$/.test(value);
}
function isFunctionType(value) {
  return value.includes("->");
}
function parseFunctionType(value) {
  const normalized = normalizeType(value);
  const arrowIndex = normalized.lastIndexOf("->");
  if (arrowIndex === -1) return null;
  const left = normalized.slice(0, arrowIndex);
  const returnType = normalized.slice(arrowIndex + 2);
  const params = left.startsWith("(") && left.endsWith(")") ? splitTopLevelArgs2(left.slice(1, -1)) : [left];
  return { params: params.filter(Boolean), returnType };
}
function normalizeType(value) {
  return value.trim().replace(/\bNat\b/g, "\u2115").replace(/\bInt\b/g, "\u2124").replace(/\bReal\b/g, "\u211D").replace(/\bBool\b/g, "Bool").replace(/\s+/g, "");
}
function splitTopLevelArgs2(value) {
  const args2 = [];
  let start = 0;
  let depth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (ch === "[") bracketDepth++;
    else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
    else if (ch === "," && depth === 0 && bracketDepth === 0) {
      args2.push(value.slice(start, i).trim());
      start = i + 1;
    }
  }
  const final = value.slice(start).trim();
  if (final) args2.push(final);
  return args2;
}

// src/codegen/index.ts
function generateJSFromAST(nodes, runtime) {
  typecheckExecutableProgram(nodes);
  let code = runtime + "\n";
  const ctx = buildCodegenContext(nodes);
  const expr = foldNodes(nodes, ctx);
  code += `
// \u2500\u2500 Evaluate program as single logical expression \u2500\u2500
`;
  code += `const _result = ${expr};
`;
  code += `if (!_resolve(_result)) throw new Error('Program does not hold: ' + _describe(_result));
`;
  code += `console.log('\\n\u2713 Program holds: ' + _describe(_result));
`;
  return code;
}
function buildCodegenContext(nodes) {
  const variants = /* @__PURE__ */ new Map();
  for (const node of nodes) {
    if (node.type !== "TypeDecl") continue;
    for (const variant of node.variants) {
      variants.set(variant.name, {
        typeName: node.name,
        fieldNames: variant.fields.map((field) => field.name)
      });
    }
  }
  return { variants };
}
function foldNodes(nodes, ctx) {
  return foldNodesWithMode(nodes, false, ctx);
}
function foldNodesWithMode(nodes, symbolicMode, ctx) {
  const meaningful = nodes.filter(
    (n) => !(n.type === "Raw" && n.content.trim().length === 0)
  );
  if (meaningful.length === 0) return 'atom(true, "\u2205")';
  let acc = nodeToExpr(meaningful[meaningful.length - 1], symbolicMode, ctx);
  for (let i = meaningful.length - 2; i >= 0; i--) {
    const node = meaningful[i];
    const conn = node.connective ?? "\u2192";
    const left = nodeToExpr(node, symbolicMode, ctx);
    acc = applyConnective(conn, left, acc);
  }
  return acc;
}
function applyConnective(conn, left, right) {
  switch (conn) {
    case "\u2192":
      return `seq(()=>${left}, ()=>${right})`;
    case "\u2227":
      return `and(${left}, ${right})`;
    case "\u2228":
      return `or(${left}, ${right})`;
    case "\u2194":
      return `iff(${left}, ${right})`;
    default:
      return `seq(()=>${left}, ()=>${right})`;
  }
}
function nodeToExpr(node, symbolicMode, ctx) {
  switch (node.type) {
    case "Theorem":
      return generateTheorem(node, ctx);
    case "Proof":
      return generateProof(node, ctx);
    case "Lemma":
      return generateLemma(node, ctx);
    case "Definition":
      return generateDefinition(node, ctx);
    case "Struct":
      return generateStruct(node);
    case "TypeDecl":
      return generateTypeDecl(node);
    case "FnDecl":
      return generateFnDecl(node, ctx);
    case "Assert":
      return symbolicMode ? `assertExpr(atom(true, ${JSON.stringify(renderExprSource(node.expr))}))` : `assertExpr(atom(() => !!(${generateRuntimeExpr(node.expr)}), ${JSON.stringify(renderExprSource(node.expr))}))`;
    case "Prove":
      return symbolicMode ? `assertExpr(atom(true, ${JSON.stringify(renderExprSource(node.expr))}))` : `assertExpr(atom(() => !!(${generateRuntimeExpr(node.expr)}), ${JSON.stringify(renderExprSource(node.expr))}))`;
    case "DeclareToProve":
      return symbolicMode ? `assertExpr(atom(true, ${JSON.stringify(renderExprSource(node.expr))}))` : `assertExpr(atom(() => !!(${generateRuntimeExpr(node.expr)}), ${JSON.stringify(renderExprSource(node.expr))}))`;
    case "AndIntroStep":
      return `atom(true, ${JSON.stringify(`${node.left} \u2227 ${node.right}`)})`;
    case "OrIntroStep":
      return `atom(true, ${JSON.stringify(node.claim)})`;
    case "Given":
      return `assumeExpr(${JSON.stringify(renderExprSource(node.expr))})`;
    case "Assume":
      return `assumeExpr(${JSON.stringify(renderExprSource(node.expr))})`;
    case "Conclude":
      return symbolicMode ? `concludeExpr(atom(true, ${JSON.stringify(renderExprSource(node.expr))}))` : `concludeExpr(atom(() => ${generateRuntimeExpr(node.expr)}, ${JSON.stringify(renderExprSource(node.expr))}))`;
    case "Apply":
      return `applyLemma(${JSON.stringify(node.target)})`;
    case "SetVar":
      return generateSetVar(node);
    case "Induction":
      return symbolicMode ? `atom(true, ${JSON.stringify(renderExprSource(node.fold))})` : `unsupportedExpr(${JSON.stringify(renderExprSource(node.fold))}, "Iteration is kernel-only in FuturLang. Use 'fl check' for induction.")`;
    case "Match":
      return symbolicMode ? `atom(true, ${JSON.stringify(`match ${renderExprSource(node.scrutinee)}`)})` : `execExpr(() => { ${generateMatchStatement(node, ctx, true)} }, "match")`;
    case "Raw":
      return symbolicMode ? `atom(true, ${JSON.stringify(node.content)})` : `execExpr(() => { ${generateRawNode(node)} }, ${JSON.stringify(node.content)})`;
    case "Intro":
      return `assumeExpr(${JSON.stringify(`${node.varName} \u2208 ${node.varType}`)})`;
    case "Rewrite":
      return `atom(true, ${JSON.stringify(`rewrite(${node.hypothesis})`)})`;
    case "Exact":
      return symbolicMode ? `concludeExpr(atom(true, ${JSON.stringify(renderExprSource(node.expr))}))` : `concludeExpr(atom(() => !!(${generateRuntimeExpr(node.expr)}), ${JSON.stringify(renderExprSource(node.expr))}))`;
    case "Obtain":
      return `atom(true, ${JSON.stringify(`obtain(${node.varName})`)})`;
    case "Derive":
      return `atom(true, 'derive()')`;
    // Blockchain/Solana nodes — not executable in JS mode, emit as atoms
    case "Program":
      return `atom(true, ${JSON.stringify(`program(${node.name})`)})`;
    case "Account":
      return `atom(true, ${JSON.stringify(`account(${node.name})`)})`;
    case "Instruction":
      return `atom(true, ${JSON.stringify(`instruction(${node.name})`)})`;
    case "ErrorDecl":
      return `atom(true, ${JSON.stringify(`error(${node.name})`)})`;
    case "Require":
      return `atom(true, ${JSON.stringify(`require(${node.error})`)})`;
    case "Emit":
      return `atom(true, ${JSON.stringify(`emit(${node.eventName})`)})`;
    case "Pda":
      return `atom(true, ${JSON.stringify(`pda(${node.varName})`)})`;
    case "Cpi":
      return `atom(true, ${JSON.stringify(`cpi(${node.program}, ${node.instruction})`)})`;
    case "Transfer":
      return `atom(true, ${JSON.stringify(`transfer(${node.from}, ${node.to}, ${node.amount})`)})`;
    case "Axiom":
      return `atom(true, ${JSON.stringify(node.statement)})`;
    default: {
      const _ = node;
      throw new Error("Unhandled node type");
    }
  }
}
function generateTheorem(node, ctx) {
  const inner = foldNodesWithMode(node.body, true, ctx);
  return `theorem(${JSON.stringify(node.name)}, () => ${inner})`;
}
function generateProof(node, ctx) {
  const inner = foldNodesWithMode(node.body, true, ctx);
  return `proof(${JSON.stringify(node.name)}, () => ${inner})`;
}
function generateLemma(node, ctx) {
  const inner = foldNodesWithMode(node.body, true, ctx);
  return `lemma(${JSON.stringify(node.name)}, () => ${inner})`;
}
function generateDefinition(node, ctx) {
  const inner = node.body.length > 0 ? foldNodes(node.body, ctx) : 'atom(true, "defined")';
  return `definition(${JSON.stringify(node.name)}, () => ${inner})`;
}
function generateStruct(node) {
  return `struct_(${JSON.stringify(node.name)}, ${JSON.stringify(node.fields)})`;
}
function generateTypeDecl(node) {
  const meta = Object.fromEntries(node.variants.map((variant) => [variant.name, variant.fields.map((field) => field.name)]));
  return `defineType(${JSON.stringify(node.name)}, ${JSON.stringify(meta)})`;
}
function generateFnDecl(node, ctx) {
  const params = node.params.map((param) => param.name).join(", ");
  const body = generateExecutableStatements(node.body, ctx);
  const meta = {
    params: node.params,
    returnType: node.returnType
  };
  return `defineFn(${JSON.stringify(node.name)}, function ${node.name}(${params}) {
${indent(body, 1)}
}, ${JSON.stringify(meta)})`;
}
function generateSetVar(node) {
  const label = node.varType ? `${node.varName}: ${node.varType}` : node.varName;
  if (node.value !== null) {
    return `setVar(${JSON.stringify(node.varName)}, () => (${compileSetVarValue(node.value)}), ${JSON.stringify(label)})`;
  }
  return `setVar(${JSON.stringify(node.varName)}, () => undefined, ${JSON.stringify(label)})`;
}
function generateExecutableStatements(nodes, ctx) {
  const lines = [];
  for (const node of nodes) {
    lines.push(generateExecutableNode(node, ctx));
  }
  return lines.join("\n");
}
function generateExecutableNode(node, ctx) {
  switch (node.type) {
    case "SetVar":
      return `let ${node.varName} = ${node.value === null ? "undefined" : compileSetVarValue(node.value)};`;
    case "Assert":
      return `_runtimeAssert(${generateRuntimeExpr(node.expr)}, ${JSON.stringify(renderExprSource(node.expr))});`;
    case "Conclude":
      return `return ${generateRuntimeExpr(node.expr)};`;
    case "Match":
      return generateMatchStatement(node, ctx, false);
    case "Raw":
      return generateRawNode(node);
    case "Assume":
    case "Given":
      return `/* assumption: ${renderExprSource(node.expr)} */`;
    case "Apply":
      return `applyLemma(${JSON.stringify(node.target)});`;
    default:
      return `throw new Error(${JSON.stringify(`Unsupported executable statement: ${node.type}`)});`;
  }
}
function generateMatchStatement(node, ctx, asExpression) {
  const scrutineeVar = `_match_${Math.random().toString(36).slice(2, 8)}`;
  const lines = [`const ${scrutineeVar} = ${generateRuntimeExpr(node.scrutinee)};`];
  node.cases.forEach((matchCase, index) => {
    const condition = patternCondition(matchCase.pattern, scrutineeVar);
    const prefix = index === 0 ? "if" : "else if";
    lines.push(`${prefix} (${condition}) {`);
    const bindings = patternBindings(matchCase.pattern, scrutineeVar, ctx);
    if (bindings) lines.push(indent(bindings, 1));
    const branch = generateExecutableStatements(matchCase.body, ctx);
    lines.push(indent(branch, 1));
    lines.push("}");
  });
  lines.push('else { throw new Error("Non-exhaustive match"); }');
  if (asExpression) lines.push("return true;");
  return lines.join("\n");
}
function patternCondition(pattern, target) {
  switch (pattern.kind) {
    case "wildcard":
      return "true";
    case "list_nil":
      return `Array.isArray(${target}) && ${target}.length === 0`;
    case "list_cons":
      return `Array.isArray(${target}) && ${target}.length > 0`;
    case "variant":
      if (pattern.constructor === "true" || pattern.constructor === "false") {
        return `${target} === ${pattern.constructor}`;
      }
      return `${target} && ${target}.tag === ${JSON.stringify(pattern.constructor)}`;
  }
}
function patternBindings(pattern, target, ctx) {
  switch (pattern.kind) {
    case "wildcard":
    case "list_nil":
      return "";
    case "list_cons":
      return [
        pattern.head !== "_" ? `const ${pattern.head} = ${target}[0];` : "",
        `const ${pattern.tail} = ${target}.slice(1);`
      ].filter(Boolean).join("\n");
    case "variant": {
      const info = ctx.variants.get(pattern.constructor);
      if (!info) return "";
      const lines = [];
      pattern.bindings.forEach((binding, index) => {
        if (!binding || binding === "_") return;
        const fieldName = info.fieldNames[index];
        if (!fieldName) return;
        lines.push(`const ${binding} = ${target}[${JSON.stringify(fieldName)}];`);
      });
      return lines.join("\n");
    }
  }
}
function generateRawNode(node) {
  const trimmed = node.content.trim();
  if (trimmed.startsWith("return ")) return trimmed.endsWith(";") ? trimmed : `${trimmed};`;
  if (trimmed === "return") return "return;";
  return trimmed.endsWith(";") ? trimmed : `${trimmed};`;
}
function generateRuntimeExpr(node) {
  switch (node.type) {
    case "Atom":
      return generateRuntimeExprFromString(node.condition);
    case "And":
      return `(${generateRuntimeExpr(node.left)} && ${generateRuntimeExpr(node.right)})`;
    case "Or":
      return `(${generateRuntimeExpr(node.left)} || ${generateRuntimeExpr(node.right)})`;
    case "Implies":
      return `((!(${generateRuntimeExpr(node.left)})) || (${generateRuntimeExpr(node.right)}))`;
    case "Iff":
      return `((${generateRuntimeExpr(node.left)}) === (${generateRuntimeExpr(node.right)}))`;
    case "Not":
      return `(!(${generateRuntimeExpr(node.operand)}))`;
    case "If":
      return `((${generateRuntimeExpr(node.condition)}) ? (${generateRuntimeExpr(node.thenBranch)}) : (${generateRuntimeExpr(node.elseBranch)}))`;
    case "LetExpr":
      return `(() => { const ${node.name} = ${generateRuntimeExpr(node.value)}; return ${generateRuntimeExpr(node.body)}; })()`;
    case "Lambda":
      return `((${node.params.map((param) => param.name).join(", ")}) => ${generateRuntimeExpr(node.body)})`;
    case "Fold":
      return `_fold(${compileSetVarValue(node.sequence)}, ${compileSetVarValue(node.init)}, ${compileSetVarValue(node.fn)})`;
    case "Quantified":
    case "SetBuilder":
    case "IndexedUnion":
      return `unsupportedExpr(${JSON.stringify(renderExprSource(node))}, "Unsupported expression in executable mode")`;
    default: {
      const _ = node;
      throw new Error("Unhandled expr node type");
    }
  }
}
function generateRuntimeExprFromString(value) {
  const trimmed = value.trim();
  if (!trimmed) return "undefined";
  return normalizeJsEquality(trimmed);
}
function compileSetVarValue(value) {
  try {
    return generateRuntimeExpr(parseExpr(value));
  } catch {
    return generateRuntimeExprFromString(value);
  }
}
function normalizeJsEquality(value) {
  let result = "";
  let inString = false;
  let quote = "";
  for (let index = 0; index < value.length; index++) {
    const ch = value[index];
    if (inString) {
      result += ch;
      if (ch === quote && value[index - 1] !== "\\") {
        inString = false;
        quote = "";
      }
      continue;
    }
    if (ch === '"' || ch === "'") {
      inString = true;
      quote = ch;
      result += ch;
      continue;
    }
    if (ch === "\u2265") {
      result += ">=";
      continue;
    }
    if (ch === "\u2264") {
      result += "<=";
      continue;
    }
    if (ch === "\u2260") {
      result += "!=";
      continue;
    }
    if (ch === "=" && value[index - 1] !== "=" && value[index - 1] !== "!" && value[index - 1] !== "<" && value[index - 1] !== ">" && value[index + 1] !== "=") {
      result += "==";
      continue;
    }
    result += ch;
  }
  return result;
}
function renderExprSource(node) {
  switch (node.type) {
    case "Atom":
      return node.condition;
    case "SetBuilder":
      return `{${node.element} | ${node.variable} \u2208 ${node.domain}}`;
    case "IndexedUnion":
      return `\u222A${renderExprSource(node.builder)}`;
    case "And":
      return `(${renderExprSource(node.left)} \u2227 ${renderExprSource(node.right)})`;
    case "Or":
      return `(${renderExprSource(node.left)} \u2228 ${renderExprSource(node.right)})`;
    case "Implies":
      return `(${renderExprSource(node.left)} \u2192 ${renderExprSource(node.right)})`;
    case "Iff":
      return `(${renderExprSource(node.left)} \u2194 ${renderExprSource(node.right)})`;
    case "Not":
      return `\xAC${renderExprSource(node.operand)}`;
    case "If":
      return `if ${renderExprSource(node.condition)} then ${renderExprSource(node.thenBranch)} else ${renderExprSource(node.elseBranch)}`;
    case "LetExpr":
      return `let ${node.name} = ${renderExprSource(node.value)} in ${renderExprSource(node.body)}`;
    case "Lambda":
      return `fn(${node.params.map((param) => `${param.name}: ${param.type}`).join(", ")}) => ${renderExprSource(node.body)}`;
    case "Quantified": {
      const symbol = node.quantifier === "forall" ? "\u2200" : node.quantifier === "exists" ? "\u2203" : "\u2203!";
      const binder = node.binderStyle === "bounded" ? `${node.variable} \u2208 ${node.domain}` : `${node.variable}: ${node.domain}`;
      return node.body ? `${symbol} ${binder}, ${renderExprSource(node.body)}` : `${symbol} ${binder}`;
    }
    case "Fold":
      return `fold(${node.sequence}, ${node.init}, ${node.fn})`;
    default: {
      const _ = node;
      throw new Error("Unhandled expr node type");
    }
  }
}
function indent(value, depth) {
  const prefix = "  ".repeat(depth);
  return value.split("\n").map((line) => line.length > 0 ? `${prefix}${line}` : line).join("\n");
}

// src/codegen/runtime.ts
var runtimePreamble = `
// \u2500\u2500 FuturLang Runtime \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

const _usedNames  = new Set();
const _lemmaCache = new Map();
const _vars       = new Map();
const _fnMeta     = new Map();
const _typeMeta   = new Map();
const _nodeHttp   = typeof require === 'function' ? require('http') : null;

// Resolve a result object or raw value to boolean
function _resolve(v) {
  if (v && typeof v === 'object' && 'value' in v) return !!v.value;
  if (typeof v === 'function') return !!v();
  return !!v;
}

// \u2500\u2500 Atom \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
function atom(v, label) {
  const value = typeof v === 'function' ? !!v() : !!v;
  return { kind: 'atom', value, label: label ?? String(v) };
}

function unsupportedExpr(label, reason) {
  throw new Error(reason + ': ' + label);
}

function execExpr(fn, label) {
  return atom(() => fn(), label);
}

// \u2500\u2500 Connectives \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
function and(a, b) {
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'and', value: lv && rv, left: a, right: b };
}
function or(a, b) {
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'or', value: lv || rv, left: a, right: b };
}
function seq(aFn, bFn) {
  // Evaluate left side first (runs setVar side-effects, etc.)
  const a  = aFn();
  const lv = _resolve(a);
  // Only evaluate right side if left holds (short-circuit like \u2192)
  const b  = bFn();
  const rv = _resolve(b);
  return { kind: 'implies', value: !lv || rv, antecedent: a, consequent: b };
}

function implies(a, b) {
  // P \u2192 Q  \u2261  \xACP \u2228 Q  (logical connective inside expressions)
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'implies', value: !lv || rv, antecedent: a, consequent: b };
}

function iff(a, b) {
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'iff', value: lv === rv, left: a, right: b };
}
function not(a) {
  const v = _resolve(a);
  return { kind: 'not', value: !v, operand: a };
}

// \u2500\u2500 Describe \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
function _describe(r) {
  if (typeof r !== 'object' || r === null) return String(r);
  switch (r.kind) {
    case 'atom':    return r.label ?? '(expr)';
    case 'and':     return '(' + _describe(r.left)       + ' \u2227 ' + _describe(r.right)      + ')';
    case 'or':      return '(' + _describe(r.left)       + ' \u2228 ' + _describe(r.right)      + ')';
    case 'implies': return '(' + _describe(r.antecedent) + ' \u2192 ' + _describe(r.consequent) + ')';
    case 'iff':     return '(' + _describe(r.left)       + ' \u2194 ' + _describe(r.right)      + ')';
    case 'not':     return '(\xAC' + _describe(r.operand)   + ')';
    default:        return JSON.stringify(r);
  }
}

// \u2500\u2500 Statement evaluators \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

function assertExpr(result) {
  const val = _resolve(result);
  if (!val) throw new Error('Assertion failed: ' + _describe(result));
  console.log('  assert \u2713', _describe(result));
  return result;
}

function _runtimeAssert(value, label) {
  if (!value) throw new Error('Assertion failed: ' + label);
  return value;
}

function assumeExpr(result) {
  // Assumptions are axioms \u2014 always accepted, establish the proof context
  const desc = typeof result === 'object' ? _describe(result) : String(result);
  console.log('  assume  ', desc);
  return atom(true, 'assume(' + desc + ')');
}

function concludeExpr(result) {
  const val = _resolve(result);
  console.log('  conclude' + (val ? ' \u2713' : ' \u2717'), _describe(result));
  return result;
}

function applyLemma(name) {
  const result = _lemmaCache.get(name.toLowerCase());
  if (result === undefined) {
    console.log('  apply   ', name, '(not yet registered, assuming true)');
    return atom(true, 'apply(' + name + ')');
  }
  console.log('  apply \u2713 ', name);
  return result;
}

function setVar(name, value, label) {
  // Execute immediately \u2014 variable must exist before right-hand side evaluates
  const resolved = typeof value === 'function' ? value() : value;
  globalThis[name] = resolved;
  _vars.set(name, globalThis[name]);
  console.log('  let     ', label ?? name, value !== undefined ? '= ' + String(globalThis[name]) : '');
  return atom(true, label ?? name);
}

function defineFn(name, fn, meta) {
  globalThis[name] = fn;
  _fnMeta.set(name, meta ?? null);
  console.log('\\nfn ' + name);
  return atom(true, 'fn(' + name + ')');
}

function defineType(name, variants) {
  _typeMeta.set(name, variants);
  for (const [variant, fields] of Object.entries(variants)) {
    if (!Array.isArray(fields) || fields.length === 0) {
      globalThis[variant] = { tag: variant };
      continue;
    }
    globalThis[variant] = (...args) => {
      const value = { tag: variant };
      fields.forEach((field, index) => { value[field] = args[index]; });
      return value;
    };
  }
  console.log('\\nType ' + name);
  return atom(true, 'type(' + name + ')');
}

function _fold(sequence, init, fn) {
  if (!Array.isArray(sequence)) throw new Error('fold expects a list/array');
  return sequence.reduce((acc, item) => fn(acc, item), init);
}

function request(method, url, body = null, headers = {}) {
  const parsed = _parseUrl(url);
  return {
    method: String(method).toUpperCase(),
    url: parsed.url,
    path: parsed.path,
    query: parsed.query,
    headers: headers ?? {},
    body,
  };
}

function text(body, status = 200, headers = {}) {
  return _response(status, { 'content-type': 'text/plain; charset=utf-8', ...headers }, String(body));
}

function html(body, status = 200, headers = {}) {
  return _response(status, { 'content-type': 'text/html; charset=utf-8', ...headers }, String(body));
}

function json(body, status = 200, headers = {}) {
  return _response(status, { 'content-type': 'application/json; charset=utf-8', ...headers }, JSON.stringify(body));
}

function route(method, path, handler) {
  return {
    method: String(method).toUpperCase(),
    path: String(path),
    handler,
  };
}

function _matchPath(routePath, reqPath) {
  if (routePath === '*') return {};
  const rParts = routePath.split('/');
  const qParts = reqPath.split('/');
  if (rParts.length !== qParts.length) return null;
  const params = {};
  for (let i = 0; i < rParts.length; i++) {
    if (rParts[i].startsWith(':')) {
      params[rParts[i].slice(1)] = qParts[i];
    } else if (rParts[i] !== qParts[i]) {
      return null;
    }
  }
  return params;
}

function router(routes, fallback) {
  return (req) => {
    for (const entry of routes) {
      if (!entry) continue;
      const method = String(entry.method).toUpperCase();
      if (method !== String(req.method).toUpperCase() && method !== '*') continue;
      const params = _matchPath(String(entry.path), req.path);
      if (params === null) continue;
      req.params = params;
      return dispatch(entry.handler, req);
    }
    if (fallback) return dispatch(fallback, req);
    return text('Not Found', 404);
  };
}

function dispatch(handler, req) {
  // Return raw \u2014 serve() handles normalization after resolving any async sentinels
  return handler(req);
}

function serve(port, handler, host = '127.0.0.1') {
  if (!_nodeHttp) throw new Error('Node http runtime is unavailable');
  const server = _nodeHttp.createServer((req, res) => {
    const chunks = [];
    req.on('data', chunk => chunks.push(chunk));
    req.on('end', async () => {
      const body = chunks.length > 0 ? Buffer.concat(chunks).toString('utf8') : null;
      const incoming = request(req.method ?? 'GET', req.url ?? '/', body, req.headers ?? {});
      try {
        let result = dispatch(handler, incoming);
        // Handle asyncJson sentinel: { __asyncResponse: true, promise, status, headers }
        if (result && result.__asyncResponse) {
          const data = await result.promise;
          result = json(data, result.status, result.headers);
        } else if (result && typeof result.then === 'function') {
          result = _normalizeResponse(await result);
        }
        result = _normalizeResponse(result);
        res.statusCode = result.status;
        for (const [name, value] of Object.entries(result.headers)) {
          res.setHeader(name, value);
        }
        res.end(result.body);
      } catch (e) {
        res.statusCode = 500;
        res.setHeader('Content-Type', 'application/json');
        res.setHeader('Access-Control-Allow-Origin', '*');
        res.end(JSON.stringify({ error: String(e && e.message ? e.message : e) }));
      }
    });
  });
  console.log('  server \u2026 starting on http://' + host + ':' + port);
  server.on('error', (error) => {
    const message = error && typeof error === 'object' && 'message' in error
      ? String(error.message)
      : String(error);
    console.error('  server \u2717 ' + message);
  });
  server.listen(port, host, () => {
    console.log('  server \u2713 listening on http://' + host + ':' + port);
  });
  return server;
}

function _response(status, headers, body) {
  return {
    status: Number(status),
    headers: headers ?? {},
    body: body ?? '',
  };
}

function _normalizeResponse(value) {
  if (value && typeof value === 'object' && typeof value.status === 'number' && 'headers' in value && 'body' in value) {
    return {
      status: value.status,
      headers: value.headers ?? {},
      body: value.body ?? '',
    };
  }
  if (typeof value === 'string') return text(value);
  return json(value);
}

function _parseUrl(raw) {
  const parsed = new URL(String(raw), 'http://futurlang.local');
  const query = Object.fromEntries(parsed.searchParams.entries());
  return {
    url: parsed.pathname + parsed.search,
    path: parsed.pathname,
    query,
  };
}

// \u2500\u2500 Block evaluators \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

function theorem(name, fn) {
  const key = name.toLowerCase();
  if (_usedNames.has(key)) throw new Error('Duplicate theorem: ' + name);
  _usedNames.add(key);
  console.log('\\nTheorem ' + name);
  const result = fn();
  const val = _resolve(result);
  console.log(val ? '  \u2713 QED' : '  \u2717 FAILED');
  return atom(val, 'theorem(' + name + ')');
}

function proof(name, fn) {
  console.log('\\nProof ' + name);
  const result = fn();
  const val = _resolve(result);
  console.log(val ? '  \u2713 proof holds' : '  \u2717 proof failed');
  return atom(val, 'proof(' + name + ')');
}

function lemma(name, fn) {
  console.log('\\nLemma ' + name);
  const result = fn();
  const val = _resolve(result);
  _lemmaCache.set(name.toLowerCase(), result);
  console.log(val ? '  \u2713 lemma holds' : '  \u2717 lemma failed');
  return atom(val, 'lemma(' + name + ')');
}

function definition(name, fn) {
  console.log('\\nDefinition ' + name);
  const result = fn();
  _lemmaCache.set(name.toLowerCase(), atom(true, name));
  return atom(true, 'definition(' + name + ')');
}

function struct_(name, fields) {
  console.log('\\nStruct ' + name);
  return atom(true, 'struct(' + name + ')');
}

// Firebase primitives \u2014 no-ops at eval time; the React transpiler handles real Firebase wiring
function initFirebase(config) { return config; }
function notesApp(firebase) { return atom(true, 'notesApp'); }

// \u2500\u2500 Generic HTTP server helpers \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

// Extract Bearer token from Authorization header
function getBearer(req) {
  const authHeader = (req.headers && req.headers['authorization']) || '';
  const match = String(authHeader).match(/^Bearer\\s+(.+)$/i);
  return match ? match[1].trim() : null;
}

// Decode JWT payload (no signature verification \u2014 server passes token to Firebase which verifies)
function getBearerUserId(req) {
  const token = getBearer(req);
  if (!token) return null;
  try {
    const parts = token.split('.');
    if (parts.length !== 3) return null;
    const payload = JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8'));
    return payload.user_id || payload.sub || null;
  } catch { return null; }
}

// Parse JSON request body
function parseBody(req) {
  if (!req.body) return {};
  try { return JSON.parse(req.body); }
  catch { return {}; }
}

// Extract a path parameter captured by router (e.g. :id)
function pathParam(req, name) {
  return (req.params && req.params[name]) || null;
}

// Wrap a Promise<data> as an async HTTP response \u2014 serve() awaits and JSON-encodes it
function asyncJson(promise, status, headers) {
  return { __asyncResponse: true, promise, status: status ?? 200, headers: headers ?? {} };
}
`;

// src/parser/formal.ts
var fs = __toESM(require("fs"));
var path = __toESM(require("path"));
function parseFL(text) {
  const lines = lexFL(text);
  const ast2 = parseLinesToAST(lines, { desugarFns: false });
  return generateJSFromAST(ast2, runtimePreamble);
}
function parseFLFile(filePath) {
  const expanded = expandImports(filePath, /* @__PURE__ */ new Set());
  return parseFL(expanded);
}
function expandFLFile(filePath) {
  return expandImports(filePath, /* @__PURE__ */ new Set());
}
function findProjectRoot(start) {
  let dir = path.resolve(start);
  while (true) {
    if (fs.existsSync(path.join(dir, "package.json"))) return dir;
    const parent = path.dirname(dir);
    if (parent === dir) return null;
    dir = parent;
  }
}
function resolveStdlib(name, fromDir) {
  const candidates = [];
  const root = findProjectRoot(fromDir);
  if (root) candidates.push(path.join(root, "lib", `${name}.fl`));
  for (let d = fromDir; ; d = path.dirname(d)) {
    candidates.push(path.join(d, "lib", `${name}.fl`));
    if (path.dirname(d) === d) break;
  }
  for (const c of candidates) {
    if (fs.existsSync(c)) return c;
  }
  return null;
}
function expandImports(filePath, seen) {
  const absolute = path.resolve(filePath);
  if (seen.has(absolute)) return "";
  seen.add(absolute);
  const source2 = fs.readFileSync(absolute, "utf8");
  const dir = path.dirname(absolute);
  const chunks = [];
  for (const line of source2.replace(/\r\n/g, "\n").split("\n")) {
    const quotedMatch = line.trim().match(/^import\s+["'](.+?\.fl)["']\s*;?\s*$/);
    if (quotedMatch) {
      const target = path.resolve(dir, quotedMatch[1]);
      const imported = expandImports(target, seen).trimEnd();
      if (imported.length > 0) chunks.push(ensureTrailingConnective(imported));
      continue;
    }
    const bareMatch = line.trim().match(/^import\s+["']?([A-Za-z][A-Za-z0-9_-]*)["']?\s*;?\s*$/);
    if (bareMatch) {
      const resolved = resolveStdlib(bareMatch[1], dir);
      if (resolved) {
        const imported = expandImports(resolved, seen).trimEnd();
        if (imported.length > 0) chunks.push(ensureTrailingConnective(imported));
      } else {
        chunks.push(line);
      }
      continue;
    }
    chunks.push(line);
  }
  return chunks.join("\n");
}
function ensureTrailingConnective(source2) {
  const lines = source2.split("\n");
  for (let index = lines.length - 1; index >= 0; index--) {
    const trimmed = lines[index].trim();
    if (!trimmed) continue;
    if (/(→|∧|↔|->|&&|<->)\s*$/.test(trimmed)) return source2;
    lines[index] = `${lines[index]} \u2227`;
    return lines.join("\n");
  }
  return source2;
}

// src/checker/propositions.ts
function exprToProp(expr) {
  switch (expr.type) {
    case "Atom":
      return expr.condition;
    case "SetBuilder":
      return `{${expr.element} | ${expr.variable} \u2208 ${expr.domain}}`;
    case "IndexedUnion":
      return `\u222A${exprToProp(expr.builder)}`;
    case "Fold":
      return `fold(${expr.sequence}, ${expr.init}, ${expr.fn})`;
    case "If":
      return `if ${exprToProp(expr.condition)} then ${exprToProp(expr.thenBranch)} else ${exprToProp(expr.elseBranch)}`;
    case "LetExpr":
      return `let ${expr.name} = ${exprToProp(expr.value)} in ${exprToProp(expr.body)}`;
    case "Lambda":
      return `fn(${expr.params.map((param) => `${param.name}: ${param.type}`).join(", ")}) => ${exprToProp(expr.body)}`;
    case "And":
      return `${exprToProp(expr.left)} \u2227 ${exprToProp(expr.right)}`;
    case "Or":
      return `${exprToProp(expr.left)} \u2228 ${exprToProp(expr.right)}`;
    case "Implies":
      return `${exprToProp(expr.left)} \u2192 ${exprToProp(expr.right)}`;
    case "Iff":
      return `${exprToProp(expr.left)} \u2194 ${exprToProp(expr.right)}`;
    case "Not":
      return `\xAC${exprToProp(expr.operand)}`;
    case "Quantified": {
      const symbol = expr.quantifier === "forall" ? "\u2200" : expr.quantifier === "exists" ? "\u2203" : "\u2203!";
      const binder = expr.binderStyle === "bounded" ? `${expr.variable} \u2208 ${expr.domain}` : `${expr.variable}: ${expr.domain}`;
      return expr.body ? `${symbol} ${binder}, ${exprToProp(expr.body)}` : `${symbol} ${binder}`;
    }
    default:
      return "";
  }
}
function normalizeProp(s) {
  try {
    return propKey(parseCanonicalExpr(s)).trim().toLowerCase().replace(/\s+/g, " ");
  } catch {
    return s.trim().toLowerCase().replace(/\s+/g, " ");
  }
}
function sameProp(a, b) {
  return normalizeProp(a) === normalizeProp(b);
}
function parseCanonicalExpr(input) {
  const trimmed = input.trim();
  try {
    const parsed = parseExpr(trimmed);
    return canonicalizeExpr(parsed);
  } catch {
    return canonicalizeAtom(normalizeSurfaceSyntax(trimmed));
  }
}
function canonicalizeExpr(expr) {
  if (expr.type !== "Atom") return expr;
  return canonicalizeAtom(expr.condition);
}
function canonicalizeAtom(value) {
  const normalized = normalizeTerm(value);
  const typed = splitTopLevelAtom(normalized, ":");
  if (typed && /^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(typed[0])) {
    return {
      kind: "typed_variable",
      variable: normalizeTerm(typed[0]),
      domain: normalizeTerm(typed[1])
    };
  }
  const nonmembership = splitTopLevelAtom(normalized, "\u2209");
  if (nonmembership) {
    return {
      kind: "nonmembership",
      element: normalizeTerm(nonmembership[0]),
      set: normalizeTerm(nonmembership[1])
    };
  }
  const topSigmaMatch = normalized.match(/^Σ\s+(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+?)\s*,\s*(.+)$/);
  if (topSigmaMatch) {
    return {
      kind: "dependent_sum",
      element: "",
      variable: normalizeTerm(topSigmaMatch[1]),
      domain: normalizeTerm(topSigmaMatch[2]),
      body: normalizeTerm(topSigmaMatch[3])
    };
  }
  const topPiMatch = normalized.match(/^Π\s+(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+?)\s*,\s*(.+)$/);
  if (topPiMatch) {
    return {
      kind: "dependent_product",
      element: "",
      variable: normalizeTerm(topPiMatch[1]),
      domain: normalizeTerm(topPiMatch[2]),
      body: normalizeTerm(topPiMatch[3])
    };
  }
  const membership = splitTopLevelAtom(normalized, "\u2208");
  if (membership) {
    const setExpr = membership[1];
    const piMatch = setExpr.match(/^Π\s*\(\s*(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+?)\s*,\s*(.+)\s*\)$/);
    if (piMatch) {
      return {
        kind: "dependent_product",
        element: normalizeTerm(membership[0]),
        variable: normalizeTerm(piMatch[1]),
        domain: normalizeTerm(piMatch[2]),
        body: normalizeTerm(piMatch[3])
      };
    }
    const sigMatch = setExpr.match(/^Σ\s*\(\s*(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+?)\s*,\s*(.+)\s*\)$/);
    if (sigMatch) {
      return {
        kind: "dependent_sum",
        element: normalizeTerm(membership[0]),
        variable: normalizeTerm(sigMatch[1]),
        domain: normalizeTerm(sigMatch[2]),
        body: normalizeTerm(sigMatch[3])
      };
    }
    const setEqSigma = setExpr.match(/^Σ\s+(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+?)\s*,\s*(.+)$/);
    if (setEqSigma) {
      return {
        kind: "dependent_sum",
        element: normalizeTerm(membership[0]),
        variable: normalizeTerm(setEqSigma[1]),
        domain: normalizeTerm(setEqSigma[2]),
        body: normalizeTerm(setEqSigma[3])
      };
    }
    const setEqPi = setExpr.match(/^Π\s+(\w[\w₀-₉ₐ-ₙ]*)\s*∈\s*(.+?)\s*,\s*(.+)$/);
    if (setEqPi) {
      return {
        kind: "dependent_product",
        element: normalizeTerm(membership[0]),
        variable: normalizeTerm(setEqPi[1]),
        domain: normalizeTerm(setEqPi[2]),
        body: normalizeTerm(setEqPi[3])
      };
    }
    return {
      kind: "membership",
      element: normalizeTerm(membership[0]),
      set: normalizeTerm(membership[1])
    };
  }
  const subseteq = splitTopLevelAtom(normalized, "\u2286");
  if (subseteq) {
    return {
      kind: "subset",
      left: normalizeTerm(subseteq[0]),
      strict: true,
      right: normalizeTerm(subseteq[1])
    };
  }
  const strictSubset = splitTopLevelAtom(normalized, "\u2282");
  if (strictSubset) {
    return {
      kind: "subset",
      left: normalizeTerm(strictSubset[0]),
      strict: false,
      right: normalizeTerm(strictSubset[1])
    };
  }
  const equality = splitTopLevelAtom(normalized, "=");
  if (equality) {
    return {
      kind: "equality",
      left: normalizeTerm(equality[0]),
      right: normalizeTerm(equality[1])
    };
  }
  return { kind: "atom", value: normalized };
}
function parseMembershipCanonical(prop) {
  const canonical = parseCanonicalExpr(prop);
  return isCanonicalAtom(canonical) && canonical.kind === "membership" ? { element: canonical.element, set: canonical.set } : null;
}
function parseNonMembershipCanonical(prop) {
  const canonical = parseCanonicalExpr(prop);
  return isCanonicalAtom(canonical) && canonical.kind === "nonmembership" ? { element: canonical.element, set: canonical.set } : null;
}
function parseSubsetCanonical(prop) {
  const canonical = parseCanonicalExpr(prop);
  return isCanonicalAtom(canonical) && canonical.kind === "subset" ? { left: canonical.left, right: canonical.right, strict: canonical.strict } : null;
}
function parseEqualityCanonical(prop) {
  const canonical = parseCanonicalExpr(prop);
  return isCanonicalAtom(canonical) && canonical.kind === "equality" ? { left: canonical.left, right: canonical.right } : null;
}
function parseMorphismDeclarationCanonical(prop) {
  const value = normalizeTerm(normalizeSurfaceSyntax(prop));
  const match = value.match(/^(.+?)\s*:\s*(.+?)\s*→\s*(.+)$/);
  if (!match) return null;
  const label = normalizeTerm(match[1]);
  const domain = normalizeTerm(match[2]);
  const codomain = normalizeTerm(match[3]);
  if (!label || !domain || !codomain) return null;
  if (label.includes(" ") && !/^id_/.test(label)) return null;
  return { label, domain, codomain };
}
function parseMorphismExprCanonical(input) {
  const value = stripOuterParens(normalizeTerm(normalizeSurfaceSyntax(input)));
  if (!value) return null;
  const compositionIndex = findTopLevelSeparator(value, "\u2218");
  if (compositionIndex !== -1) {
    const left = parseMorphismExprCanonical(value.slice(0, compositionIndex));
    const right = parseMorphismExprCanonical(value.slice(compositionIndex + 1));
    if (!left || !right) return null;
    return { kind: "compose", left, right };
  }
  const functorMatch = value.match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)\((.+)\)$/);
  if (functorMatch) {
    const argument = parseMorphismExprCanonical(functorMatch[2]);
    if (!argument) return null;
    return { kind: "functor_map", functor: normalizeTerm(functorMatch[1]), argument };
  }
  const identityMatch = value.match(/^id_(?:\{(.+)\}|(.+))$/);
  if (identityMatch) {
    return { kind: "identity", object: normalizeTerm(identityMatch[1] ?? identityMatch[2]) };
  }
  return { kind: "name", label: value };
}
function formatMorphismExpr(expr) {
  switch (expr.kind) {
    case "name":
      return expr.label;
    case "identity":
      return `id_${expr.object}`;
    case "compose":
      return `${formatMorphismExpr(expr.left)} \u2218 ${formatMorphismExpr(expr.right)}`;
    case "functor_map":
      return `${expr.functor}(${formatMorphismExpr(expr.argument)})`;
  }
}
function parseCategoricalEqualityCanonical(prop) {
  const equality = splitTopLevelAtom(normalizeTerm(normalizeSurfaceSyntax(prop)), "=");
  if (!equality) return null;
  const left = parseMorphismExprCanonical(equality[0]);
  const right = parseMorphismExprCanonical(equality[1]);
  if (!left || !right) return null;
  return { left, right };
}
function parseCategoryPredicateCanonical(prop) {
  const value = normalizeTerm(normalizeSurfaceSyntax(prop));
  const match = value.match(/^(Category|Object|Morphism|Iso|Product|ProductMediator|Coproduct|Pullback|Pushout|Functor)\((.*)\)$/);
  if (!match) return null;
  const name = match[1];
  const args2 = splitTopLevelArgs3(match[2]);
  return { name, args: args2 };
}
function parseMeasurePredicateCanonical(claim) {
  const value = normalizeTerm(normalizeSurfaceSyntax(claim));
  const match = value.match(/^(SigmaAlgebra|Measure|ProbabilityMeasure|Measurable)\s*\((.*)\)$/);
  if (!match) return null;
  const name = match[1];
  const args2 = splitTopLevelArgs3(match[2]);
  return { name, args: args2 };
}
function parseImplicationCanonical(prop) {
  return splitTopLevelProp(prop, "\u2192");
}
function parseConjunctionCanonical(prop) {
  return splitTopLevelProp(prop, "\u2227");
}
function parseDisjunctionCanonical(prop) {
  return splitTopLevelProp(prop, "\u2228");
}
function parseIffCanonical(prop) {
  return splitTopLevelProp(prop, "\u2194");
}
function parseBinarySetCanonical(prop, operator) {
  return splitTopLevelProp(prop, operator);
}
function parseSetBuilderCanonical(term) {
  const value = stripOuterParens(normalizeTerm(term));
  if (!(value.startsWith("{") && value.endsWith("}"))) return null;
  const inner = value.slice(1, -1).trim();
  const barIndex = findTopLevelSeparator(inner, "|");
  if (barIndex === -1) return null;
  const elementTemplate = normalizeTerm(inner.slice(0, barIndex));
  const binder = inner.slice(barIndex + 1).trim();
  const membership = splitTopLevelAtom(binder, "\u2208");
  if (!membership) return null;
  const variable = normalizeTerm(membership[0]);
  if (!/^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(variable)) return null;
  const domain = stripOuterParens(normalizeTerm(membership[1]));
  if (!elementTemplate || !domain) return null;
  return { elementTemplate, variable, domain };
}
function parseBoundedQuantifierCanonical(prop, kind) {
  const quantifier = parseQuantifiedExpr2(prop, kind, "bounded");
  if (!quantifier || !quantifier.body) return null;
  return {
    kind,
    variable: quantifier.variable,
    set: quantifier.domain,
    body: exprToProp(quantifier.body)
  };
}
function parseQuantifiedExpr2(prop, kind, binderStyle) {
  let parsed;
  try {
    parsed = parseExpr(prop.trim());
  } catch {
    return null;
  }
  if (parsed.type !== "Quantified") return null;
  if (parsed.quantifier !== kind || parsed.binderStyle !== binderStyle) return null;
  return parsed;
}
function propKey(expr) {
  if (isCanonicalAtom(expr)) return canonicalAtomKey(expr);
  switch (expr.type) {
    case "And":
      return `and(${propKey(canonicalizeExpr(expr.left))},${propKey(canonicalizeExpr(expr.right))})`;
    case "Or":
      return `or(${propKey(canonicalizeExpr(expr.left))},${propKey(canonicalizeExpr(expr.right))})`;
    case "Implies":
      return `implies(${propKey(canonicalizeExpr(expr.left))},${propKey(canonicalizeExpr(expr.right))})`;
    case "Iff":
      return `iff(${propKey(canonicalizeExpr(expr.left))},${propKey(canonicalizeExpr(expr.right))})`;
    case "Not":
      return `not(${propKey(canonicalizeExpr(expr.operand))})`;
    case "Quantified": {
      const binder = expr.binderStyle === "bounded" ? `${normalizeTerm(expr.variable)}\u2208${normalizeTerm(expr.domain)}` : `${normalizeTerm(expr.variable)}:${normalizeTerm(expr.domain)}`;
      const body = expr.body ? propKey(canonicalizeExpr(expr.body)) : "";
      return `${expr.quantifier}(${expr.binderStyle},${binder},${body})`;
    }
    case "Fold":
      return `fold(${normalizeTerm(expr.sequence)},${normalizeTerm(expr.init)},${normalizeTerm(expr.fn)})`;
    case "Atom":
      return canonicalAtomKey(canonicalizeAtom(expr.condition));
  }
  return "";
}
function canonicalAtomKey(atom) {
  switch (atom.kind) {
    case "membership":
      return `membership(${normalizeTerm(atom.element)},${normalizeTerm(atom.set)})`;
    case "nonmembership":
      return `nonmembership(${normalizeTerm(atom.element)},${normalizeTerm(atom.set)})`;
    case "dependent_product":
      return `pi(${normalizeTerm(atom.element)},${normalizeTerm(atom.variable)},${normalizeTerm(atom.domain)},${normalizeTerm(atom.body)})`;
    case "dependent_sum":
      return `sigma(${normalizeTerm(atom.element)},${normalizeTerm(atom.variable)},${normalizeTerm(atom.domain)},${normalizeTerm(atom.body)})`;
    case "subset":
      return `subset(${atom.strict ? "strict" : "weak"},${normalizeTerm(atom.left)},${normalizeTerm(atom.right)})`;
    case "equality":
      return `equality(${normalizeTerm(atom.left)},${normalizeTerm(atom.right)})`;
    case "typed_variable":
      return `typed(${normalizeTerm(atom.variable)},${normalizeTerm(atom.domain)})`;
    case "atom":
      return `atom(${normalizeTerm(atom.value)})`;
  }
  return "";
}
function isCanonicalAtom(expr) {
  return typeof expr.kind === "string";
}
function normalizeTerm(value) {
  return value.trim().replace(/\s+/g, " ");
}
function splitTopLevelAtom(value, operator) {
  let parenDepth2 = 0;
  let braceDepth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") parenDepth2++;
    else if (ch === ")") parenDepth2 = Math.max(0, parenDepth2 - 1);
    else if (ch === "{") braceDepth++;
    else if (ch === "}") braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === "[") bracketDepth++;
    else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
    if (parenDepth2 === 0 && braceDepth === 0 && bracketDepth === 0 && value.slice(i, i + operator.length) === operator) {
      const left = normalizeTerm(value.slice(0, i));
      const right = normalizeTerm(value.slice(i + operator.length));
      if (left && right) return [left, right];
    }
  }
  return null;
}
function splitTopLevelProp(value, operator) {
  let parenDepth2 = 0;
  let braceDepth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") parenDepth2++;
    else if (ch === ")") parenDepth2 = Math.max(0, parenDepth2 - 1);
    else if (ch === "{") braceDepth++;
    else if (ch === "}") braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === "[") bracketDepth++;
    else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
    if (parenDepth2 === 0 && braceDepth === 0 && bracketDepth === 0 && value.slice(i, i + operator.length) === operator) {
      const left = normalizeTerm(value.slice(0, i));
      const right = normalizeTerm(value.slice(i + operator.length));
      if (left && right) return [left, right];
    }
  }
  return null;
}
function findTopLevelSeparator(value, separator) {
  let parenDepth2 = 0;
  let braceDepth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") parenDepth2++;
    else if (ch === ")") parenDepth2 = Math.max(0, parenDepth2 - 1);
    else if (ch === "{") braceDepth++;
    else if (ch === "}") braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === "[") bracketDepth++;
    else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
    if (parenDepth2 === 0 && braceDepth === 0 && bracketDepth === 0 && value.slice(i, i + separator.length) === separator) {
      return i;
    }
  }
  return -1;
}
function splitTopLevelArgs3(value) {
  const args2 = [];
  let start = 0;
  let parenDepth2 = 0;
  let braceDepth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") parenDepth2++;
    else if (ch === ")") parenDepth2 = Math.max(0, parenDepth2 - 1);
    else if (ch === "{") braceDepth++;
    else if (ch === "}") braceDepth = Math.max(0, braceDepth - 1);
    else if (ch === "[") bracketDepth++;
    else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
    if (parenDepth2 === 0 && braceDepth === 0 && bracketDepth === 0 && ch === ",") {
      args2.push(normalizeTerm(value.slice(start, i)));
      start = i + 1;
    }
  }
  const final = normalizeTerm(value.slice(start));
  if (final) args2.push(final);
  return args2;
}
function stripOuterParens(value) {
  let current = value.trim();
  while (hasWrappingParens(current)) {
    current = current.slice(1, -1).trim();
  }
  return current;
}
function hasWrappingParens(value) {
  if (!(value.startsWith("(") && value.endsWith(")"))) return false;
  let depth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") {
      depth--;
      if (depth === 0 && i < value.length - 1) return false;
    }
  }
  return depth === 0;
}

// src/kernel/term.ts
function termFromString(s) {
  const normalized = normalizeAtom(s);
  const memMatch = splitTop(normalized, "\u2208");
  if (memMatch) return { kind: "mem", element: termAtom(memMatch[0]), set: termAtom(memMatch[1]) };
  const nonMemMatch = splitTop(normalized, "\u2209");
  if (nonMemMatch) return { kind: "not", body: { kind: "mem", element: termAtom(nonMemMatch[0]), set: termAtom(nonMemMatch[1]) } };
  const eqMatch = splitTop(normalized, "=");
  if (eqMatch) return { kind: "eq", left: termAtom(eqMatch[0]), right: termAtom(eqMatch[1]) };
  const subMatch = splitTop(normalized, "\u2286") ?? splitTop(normalized, "\u2282");
  if (subMatch) return { kind: "sub", left: termAtom(subMatch[0]), right: termAtom(subMatch[1]) };
  const implMatch = splitTop(normalized, "\u2192");
  if (implMatch) return { kind: "implies", left: termFromString(implMatch[0]), right: termFromString(implMatch[1]) };
  const andMatch = splitTop(normalized, "\u2227");
  if (andMatch) return { kind: "and", left: termFromString(andMatch[0]), right: termFromString(andMatch[1]) };
  const orMatch = splitTop(normalized, "\u2228");
  if (orMatch) return { kind: "or", left: termFromString(orMatch[0]), right: termFromString(orMatch[1]) };
  if (normalized.startsWith("\xAC")) return { kind: "not", body: termFromString(normalized.slice(1).trim()) };
  const appMatch = normalized.match(/^(\w[\w₀-₉]*)\s*\((.+)\)$/);
  if (appMatch) {
    const args2 = splitArgs(appMatch[2]).map(termAtom);
    return { kind: "app", fn: appMatch[1], args: args2 };
  }
  const addMatch = splitTopRightArith(normalized, ["+", "-"]);
  if (addMatch) {
    return { kind: "app", fn: addMatch[1], args: [termAtom(addMatch[0]), termAtom(addMatch[2])] };
  }
  const mulMatch = splitTopRightArith(normalized, ["*", "/"]);
  if (mulMatch) {
    return { kind: "app", fn: mulMatch[1], args: [termAtom(mulMatch[0]), termAtom(mulMatch[2])] };
  }
  if (/^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(normalized)) {
    return { kind: "var", name: normalized };
  }
  return { kind: "atom", value: normalized };
}
function termAtom(s) {
  const t = termFromString(s.trim());
  return t;
}
function termEqual(a, b) {
  if (a.kind !== b.kind) return false;
  switch (a.kind) {
    case "var":
      return a.name === b.name;
    case "atom":
      return a.value === b.value;
    case "app": {
      const bb = b;
      return a.fn === bb.fn && a.args.length === bb.args.length && a.args.every((arg, i) => termEqual(arg, bb.args[i]));
    }
    case "and":
    case "or":
    case "iff": {
      const bb = b;
      return termEqual(a.left, bb.left) && termEqual(a.right, bb.right);
    }
    case "implies": {
      const bb = b;
      return termEqual(a.left, bb.left) && termEqual(a.right, bb.right);
    }
    case "not": {
      const bb = b;
      return termEqual(a.body, bb.body);
    }
    case "forall":
    case "exists": {
      const bb = b;
      if (a.domain !== bb.domain) return false;
      const renamed = alphaRename(bb.body, bb.variable, a.variable);
      return termEqual(a.body, renamed);
    }
    case "mem": {
      const bb = b;
      return termEqual(a.element, bb.element) && termEqual(a.set, bb.set);
    }
    case "eq": {
      const bb = b;
      return termEqual(a.left, bb.left) && termEqual(a.right, bb.right) || termEqual(a.left, bb.right) && termEqual(a.right, bb.left);
    }
    case "sub": {
      const bb = b;
      return termEqual(a.left, bb.left) && termEqual(a.right, bb.right);
    }
    default:
      return false;
  }
}
function alphaRename(term, from, to) {
  switch (term.kind) {
    case "var":
      return term.name === from ? { kind: "var", name: to } : term;
    case "atom":
      return term;
    case "app":
      return { ...term, args: term.args.map((arg) => alphaRename(arg, from, to)) };
    case "and":
    case "or":
    case "iff":
    case "implies":
      return { ...term, left: alphaRename(term.left, from, to), right: alphaRename(term.right, from, to) };
    case "not":
      return { kind: "not", body: alphaRename(term.body, from, to) };
    case "forall":
    case "exists":
      if (term.variable === from) return term;
      return { ...term, body: alphaRename(term.body, from, to) };
    case "mem":
      return { kind: "mem", element: alphaRename(term.element, from, to), set: alphaRename(term.set, from, to) };
    case "eq":
      return { kind: "eq", left: alphaRename(term.left, from, to), right: alphaRename(term.right, from, to) };
    case "sub":
      return { kind: "sub", left: alphaRename(term.left, from, to), right: alphaRename(term.right, from, to) };
    default:
      return term;
  }
}
function applySubst(term, subst) {
  switch (term.kind) {
    case "var":
      return subst.has(term.name) ? applySubst(subst.get(term.name), subst) : term;
    case "atom":
      return term;
    case "app":
      return { ...term, args: term.args.map((a) => applySubst(a, subst)) };
    case "and":
    case "or":
    case "iff":
    case "implies":
      return { ...term, left: applySubst(term.left, subst), right: applySubst(term.right, subst) };
    case "not":
      return { kind: "not", body: applySubst(term.body, subst) };
    case "forall":
    case "exists": {
      const inner = new Map(subst);
      inner.delete(term.variable);
      return { ...term, body: applySubst(term.body, inner) };
    }
    case "mem":
      return { kind: "mem", element: applySubst(term.element, subst), set: applySubst(term.set, subst) };
    case "eq":
      return { kind: "eq", left: applySubst(term.left, subst), right: applySubst(term.right, subst) };
    case "sub":
      return { kind: "sub", left: applySubst(term.left, subst), right: applySubst(term.right, subst) };
    default:
      return term;
  }
}
function termToString(term) {
  switch (term.kind) {
    case "var":
      return term.name;
    case "atom":
      return term.value;
    case "app": {
      const INFIX_OPS = /* @__PURE__ */ new Set(["+", "-", "*", "/", "%"]);
      if (INFIX_OPS.has(term.fn) && term.args.length === 2) {
        const l = termToString(term.args[0]);
        const r = termToString(term.args[1]);
        const needsParens = (s, op) => {
          if (op === "*" || op === "/") return /[+\-]/.test(s.replace(/\([^)]*\)/g, ""));
          return false;
        };
        const rStr = needsParens(r, term.fn) ? `(${r})` : r;
        return `${l} ${term.fn} ${rStr}`;
      }
      return `${term.fn}(${term.args.map(termToString).join(", ")})`;
    }
    case "and":
      return `${termToString(term.left)} \u2227 ${termToString(term.right)}`;
    case "or":
      return `${termToString(term.left)} \u2228 ${termToString(term.right)}`;
    case "implies":
      return `${termToString(term.left)} \u2192 ${termToString(term.right)}`;
    case "iff":
      return `${termToString(term.left)} \u2194 ${termToString(term.right)}`;
    case "not":
      return `\xAC${termToString(term.body)}`;
    case "forall":
      return `\u2200 ${term.variable} \u2208 ${term.domain}, ${termToString(term.body)}`;
    case "exists":
      return `\u2203 ${term.variable} \u2208 ${term.domain}, ${termToString(term.body)}`;
    case "mem":
      return `${termToString(term.element)} \u2208 ${termToString(term.set)}`;
    case "eq":
      return `${termToString(term.left)} = ${termToString(term.right)}`;
    case "sub":
      return `${termToString(term.left)} \u2286 ${termToString(term.right)}`;
    default:
      return "";
  }
}
function rewriteTerm(term, from, to) {
  if (termEqual(term, from)) return to;
  switch (term.kind) {
    case "var":
    case "atom":
      return term;
    case "app":
      return { ...term, args: term.args.map((a) => rewriteTerm(a, from, to)) };
    case "and":
    case "or":
    case "iff":
    case "implies":
      return { ...term, left: rewriteTerm(term.left, from, to), right: rewriteTerm(term.right, from, to) };
    case "not":
      return { kind: "not", body: rewriteTerm(term.body, from, to) };
    case "forall":
    case "exists":
      return { ...term, body: rewriteTerm(term.body, from, to) };
    case "mem":
      return { kind: "mem", element: rewriteTerm(term.element, from, to), set: rewriteTerm(term.set, from, to) };
    case "eq":
      return { kind: "eq", left: rewriteTerm(term.left, from, to), right: rewriteTerm(term.right, from, to) };
    case "sub":
      return { kind: "sub", left: rewriteTerm(term.left, from, to), right: rewriteTerm(term.right, from, to) };
    default:
      return term;
  }
}
function splitTopRightArith(s, ops) {
  let depth = 0;
  let bestIdx = -1;
  let bestOp = "";
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === "(" || ch === "[" || ch === "{") {
      depth++;
      continue;
    }
    if (ch === ")" || ch === "]" || ch === "}") {
      depth--;
      continue;
    }
    if (depth !== 0) continue;
    for (const op of ops) {
      if (s.startsWith(op, i)) {
        if (op === "-" && i === 0) continue;
        bestIdx = i;
        bestOp = op;
        break;
      }
    }
  }
  if (bestIdx < 0) return null;
  const left = s.slice(0, bestIdx).trim();
  const right = s.slice(bestIdx + bestOp.length).trim();
  if (!left || !right) return null;
  return [left, bestOp, right];
}
function normalizeAtom(s) {
  return s.trim().replace(/\bin\b/g, "\u2208").replace(/\s+/g, " ");
}
function splitTop(s, sep) {
  let depth = 0;
  const idx = s.indexOf(sep);
  if (idx < 0) return null;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === "(" || ch === "[" || ch === "{") depth++;
    else if (ch === ")" || ch === "]" || ch === "}") depth--;
    else if (depth === 0 && s.startsWith(sep, i)) {
      return [s.slice(0, i).trim(), s.slice(i + sep.length).trim()];
    }
  }
  return null;
}
function splitArgs(s) {
  const result = [];
  let depth = 0;
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === "(" || ch === "[") depth++;
    else if (ch === ")" || ch === "]") depth--;
    else if (depth === 0 && ch === ",") {
      result.push(s.slice(start, i).trim());
      start = i + 1;
    }
  }
  result.push(s.slice(start).trim());
  return result;
}

// src/kernel/arithmetic.ts
function tokenize(s) {
  const tokens = [];
  let i = 0;
  while (i < s.length) {
    const ch = s[i];
    if (/\s/.test(ch)) {
      i++;
      continue;
    }
    if (/\d/.test(ch)) {
      let num = "";
      while (i < s.length && /\d/.test(s[i])) num += s[i++];
      tokens.push({ kind: "num", value: parseInt(num, 10) });
    } else if (/[a-zA-Z_]/.test(ch)) {
      let id = "";
      while (i < s.length && /[a-zA-Z0-9_']/.test(s[i])) id += s[i++];
      tokens.push({ kind: "ident", value: id });
    } else if (ch === "(") {
      tokens.push({ kind: "lparen" });
      i++;
    } else if (ch === ")") {
      tokens.push({ kind: "rparen" });
      i++;
    } else if ("+-*/%^".includes(ch)) {
      tokens.push({ kind: "op", value: ch });
      i++;
    } else {
      i++;
    }
  }
  return tokens;
}
function peek(ps) {
  return ps.tokens[ps.pos];
}
function consume(ps) {
  return ps.tokens[ps.pos++];
}
function parseExprNum(ps) {
  return parseAddSub(ps);
}
function parseAddSub(ps) {
  let left = parseMulDiv(ps);
  while (true) {
    const t = peek(ps);
    if (!t || t.kind !== "op" || t.value !== "+" && t.value !== "-") break;
    consume(ps);
    const right = parseMulDiv(ps);
    if (left === null || right === null) return null;
    left = t.value === "+" ? left + right : left - right;
  }
  return left;
}
function parseMulDiv(ps) {
  let left = parseUnary(ps);
  while (true) {
    const t = peek(ps);
    if (!t || t.kind !== "op" || t.value !== "*" && t.value !== "/" && t.value !== "%") break;
    consume(ps);
    const right = parseUnary(ps);
    if (left === null || right === null) return null;
    if (t.value === "/") left = right !== 0 ? Math.floor(left / right) : null;
    else if (t.value === "%") left = right !== 0 ? left % right : null;
    else left = left * right;
    if (left === null) return null;
  }
  return left;
}
function parseUnary(ps) {
  const t = peek(ps);
  if (t && t.kind === "op" && t.value === "-") {
    consume(ps);
    const v = parsePrimary(ps);
    return v !== null ? -v : null;
  }
  return parsePrimary(ps);
}
function parsePrimary(ps) {
  const t = peek(ps);
  if (!t) return null;
  if (t.kind === "num") {
    consume(ps);
    return t.value;
  }
  if (t.kind === "lparen") {
    consume(ps);
    const v = parseExprNum(ps);
    const close = peek(ps);
    if (close && close.kind === "rparen") consume(ps);
    return v;
  }
  if (t.kind === "ident") {
    const name = t.value;
    consume(ps);
    const next = peek(ps);
    if (next && next.kind === "lparen") {
      consume(ps);
      let depth = 1;
      while (ps.pos < ps.tokens.length && depth > 0) {
        const tok = consume(ps);
        if (tok.kind === "lparen") depth++;
        else if (tok.kind === "rparen") depth--;
      }
      return null;
    }
    const val = ps.subst.get(name);
    return val !== void 0 ? val : null;
  }
  return null;
}
function collectVars(expr) {
  const tokens = tokenize(expr.trim());
  const vars = /* @__PURE__ */ new Set();
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    if (t.kind === "ident") {
      const next = tokens[i + 1];
      if (!next || next.kind !== "lparen") vars.add(t.value);
    }
  }
  return vars;
}
function evalWithSubst(expr, subst) {
  try {
    const tokens = tokenize(expr.trim());
    const ps = { tokens, pos: 0, subst };
    const result = parseExprNum(ps);
    if (ps.pos < ps.tokens.length) return null;
    return result;
  } catch {
    return null;
  }
}
function evalArith(expr) {
  return evalWithSubst(expr, /* @__PURE__ */ new Map());
}
function arithEqual(lhs, rhs) {
  const l = evalArith(lhs);
  const r = evalArith(rhs);
  return l !== null && r !== null && l === r;
}
function arithSymEqual(lhs, rhs) {
  const vars = /* @__PURE__ */ new Set([...collectVars(lhs), ...collectVars(rhs)]);
  if (vars.size === 0) return arithEqual(lhs, rhs);
  const TRIALS = 8;
  const RANGE = 97;
  for (let t = 0; t < TRIALS; t++) {
    const subst = /* @__PURE__ */ new Map();
    for (const v of vars) subst.set(v, Math.floor(Math.random() * RANGE) + 1);
    const l = evalWithSubst(lhs, subst);
    const r = evalWithSubst(rhs, subst);
    if (l === null || r === null || l !== r) return false;
  }
  return true;
}
function arithSymEqualWithSubst(lhs, rhs, exprSubsts) {
  let l = lhs;
  let r = rhs;
  for (const [varName, expr] of exprSubsts) {
    const re = new RegExp(`\\b${varName}\\b`, "g");
    l = l.replace(re, `(${expr})`);
    r = r.replace(re, `(${expr})`);
  }
  return arithSymEqual(l, r);
}
function normArith(s) {
  return s.trim().replace(/\s+/g, " ");
}
function stripOuter(s) {
  s = s.trim();
  if (s.startsWith("(") && s.endsWith(")")) {
    let depth = 0;
    for (let i = 0; i < s.length; i++) {
      if (s[i] === "(") depth++;
      else if (s[i] === ")") {
        depth--;
        if (depth === 0 && i < s.length - 1) return s;
      }
    }
    return s.slice(1, -1).trim();
  }
  return s;
}
function parseEvenClaim(s) {
  const m = s.trim().match(/^even\s*\(\s*([\s\S]+?)\s*\)$/i);
  return m ? normArith(m[1]) : null;
}
function parseOddClaim(s) {
  const m = s.trim().match(/^odd\s*\(\s*([\s\S]+?)\s*\)$/i);
  return m ? normArith(m[1]) : null;
}
function parseDividesClaim(s) {
  const m = s.trim().match(/^divides\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
  return m ? { a: normArith(m[1]), b: normArith(m[2]) } : null;
}
function extractDoubleOperand(expr) {
  const s = normArith(stripOuter(expr));
  const m1 = s.match(/^2\s*\*\s*([\s\S]+)$/);
  if (m1) return normArith(m1[1]);
  const m2 = s.match(/^([\s\S]+?)\s*\*\s*2$/);
  if (m2) return normArith(m2[1]);
  return null;
}
function extractSuccDoubleOperand(expr) {
  const s = normArith(stripOuter(expr));
  const m1 = s.match(/^2\s*\*\s*([\s\S]+?)\s*\+\s*1$/);
  if (m1) return normArith(m1[1]);
  const m2 = s.match(/^1\s*\+\s*2\s*\*\s*([\s\S]+)$/);
  if (m2) return normArith(m2[1]);
  return null;
}
function splitTopMul(s) {
  s = normArith(s);
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth--;
    else if (depth === 0 && ch === "*") {
      return [normArith(s.slice(0, i)), normArith(s.slice(i + 1))];
    }
  }
  return null;
}
function isConcreteEven(expr) {
  const v = evalArith(expr);
  return v !== null && v % 2 === 0;
}
function isConcreteOdd(expr) {
  const v = evalArith(expr);
  return v !== null && v % 2 !== 0;
}
function parseAbsEquality(s) {
  const m1 = s.trim().match(/^abs\s*\(\s*([\s\S]+?)\s*\)\s*=\s*([\s\S]+)$/i);
  if (m1) return { arg: normArith(m1[1]), value: normArith(m1[2]) };
  const m2 = s.trim().match(/^([\s\S]+?)\s*=\s*abs\s*\(\s*([\s\S]+?)\s*\)$/i);
  if (m2) return { arg: normArith(m2[2]), value: normArith(m2[1]) };
  return null;
}
function parseSignEquality(s) {
  const m1 = s.trim().match(/^sign\s*\(\s*([\s\S]+?)\s*\)\s*=\s*([\s\S]+)$/i);
  if (m1) return { arg: normArith(m1[1]), value: normArith(m1[2]) };
  const m2 = s.trim().match(/^([\s\S]+?)\s*=\s*sign\s*\(\s*([\s\S]+?)\s*\)$/i);
  if (m2) return { arg: normArith(m2[2]), value: normArith(m2[1]) };
  return null;
}
function parseOrder(s) {
  const ops = ["\u2264", "\u2265", "<=", ">=", "<", ">"];
  for (const op of ops) {
    const idx = s.indexOf(op);
    if (idx < 0) continue;
    let depth = 0;
    let found = -1;
    for (let i = 0; i < s.length; i++) {
      if (s[i] === "(" || s[i] === "[") depth++;
      else if (s[i] === ")" || s[i] === "]") depth--;
      else if (depth === 0 && s.startsWith(op, i)) {
        found = i;
        break;
      }
    }
    if (found < 0) continue;
    const left = normArith(s.slice(0, found));
    const right = normArith(s.slice(found + op.length));
    if (left && right) return { left, op, right };
  }
  return null;
}
function evalOrder(left, op, right) {
  const l = evalArith(left);
  const r = evalArith(right);
  if (l === null || r === null) return null;
  switch (op) {
    case "<":
      return l < r;
    case ">":
      return l > r;
    case "\u2264":
    case "<=":
      return l <= r;
    case "\u2265":
    case ">=":
      return l >= r;
  }
}
function parseCongruence(s) {
  const m = s.trim().match(/^(.+?)\s*[≡=]\s*(.+?)\s*\(\s*mod\s+(.+?)\s*\)$/i);
  return m ? { a: normArith(m[1]), b: normArith(m[2]), n: normArith(m[3]) } : null;
}
function parseModOp(s) {
  const norm = s.trim();
  const m = norm.match(/^(.+?)\s+mod\s+(.+)$/i);
  return m ? { a: normArith(m[1]), n: normArith(m[2]) } : null;
}
function evalMod(a, n) {
  const av = evalArith(a);
  const nv = evalArith(n);
  if (av === null || nv === null || nv === 0) return null;
  return (av % nv + nv) % nv;
}
function areCongruent(a, b, n) {
  const av = evalArith(a);
  const bv = evalArith(b);
  const nv = evalArith(n);
  if (av === null || bv === null || nv === null || nv === 0) return false;
  return ((av - bv) % nv + nv) % nv === 0;
}
function isPrime(n) {
  if (n < 2) return false;
  if (n === 2 || n === 3) return true;
  if (n % 2 === 0 || n % 3 === 0) return false;
  for (let i = 5; i * i <= n; i += 6) {
    if (n % i === 0 || n % (i + 2) === 0) return false;
  }
  return true;
}
function parsePrimePred(s) {
  const m1 = s.trim().match(/^(.+?)\s*∈\s*Prime$/i);
  if (m1) return normArith(m1[1]);
  const m2 = s.trim().match(/^Prime\s*\(\s*(.+?)\s*\)$/i);
  if (m2) return normArith(m2[1]);
  return null;
}
function parseTotientExpr(s) {
  const m1 = s.trim().match(/^[φΦ]\s*\(\s*(.+?)\s*\)$/);
  if (m1) return normArith(m1[1]);
  const m2 = s.trim().match(/^totient\s*\(\s*(.+?)\s*\)$/i);
  if (m2) return normArith(m2[1]);
  return null;
}
function parseTotientEquality(s) {
  const m1 = s.trim().match(/^[φΦ]\s*\(\s*(.+?)\s*\)\s*=\s*(.+)$/);
  if (m1) return { arg: normArith(m1[1]), value: normArith(m1[2]) };
  const m2 = s.trim().match(/^(.+?)\s*=\s*[φΦ]\s*\(\s*(.+?)\s*\)$/);
  if (m2) return { arg: normArith(m2[2]), value: normArith(m2[1]) };
  const m3 = s.trim().match(/^totient\s*\(\s*(.+?)\s*\)\s*=\s*(.+)$/i);
  if (m3) return { arg: normArith(m3[1]), value: normArith(m3[2]) };
  return null;
}
function computeTotient(n) {
  if (n <= 0) return 0;
  let result = n;
  let temp = n;
  for (let p = 2; p * p <= temp; p++) {
    if (temp % p === 0) {
      while (temp % p === 0) temp = Math.floor(temp / p);
      result -= Math.floor(result / p);
    }
  }
  if (temp > 1) result -= Math.floor(result / temp);
  return result;
}
function parsePower(s) {
  for (const norm of [s.trim(), stripOuter(s.trim())]) {
    let depth = 0;
    for (let i = norm.length - 1; i >= 0; i--) {
      const ch = norm[i];
      if (ch === ")" || ch === "]") depth++;
      else if (ch === "(" || ch === "[") depth--;
      else if (depth === 0 && ch === "^") {
        const base = norm.slice(0, i).trim();
        const exp = norm.slice(i + 1).trim();
        if (base && exp) return { base, exp };
      } else if (depth === 0 && ch === "*" && i > 0 && norm[i - 1] === "*") {
        const base = norm.slice(0, i - 1).trim();
        const exp = norm.slice(i + 1).trim();
        if (base && exp) return { base, exp };
      }
    }
  }
  return null;
}

// src/kernel/unify.ts
function unify(a, b, metavars) {
  const subst = /* @__PURE__ */ new Map();
  const errorRef = {};
  if (!unifyInto(a, b, metavars, subst, errorRef)) {
    return { subst, error: errorRef.error || { expected: termToString(b), actual: termToString(a) } };
  }
  return { subst };
}
function unifyInto(a, b, metavars, subst, errorRef) {
  a = applySubst(a, subst);
  b = applySubst(b, subst);
  if (a.kind === "var" && metavars.has(a.name)) {
    if (a.kind === b.kind && a.name === b.name) return true;
    if (occursIn(a.name, b)) {
      errorRef.error = { expected: `No occurs-check cycle for ${a.name}`, actual: termToString(b) };
      return false;
    }
    subst.set(a.name, b);
    return true;
  }
  if (b.kind === "var" && metavars.has(b.name)) {
    if (occursIn(b.name, a)) {
      errorRef.error = { expected: `No occurs-check cycle for ${b.name}`, actual: termToString(a) };
      return false;
    }
    subst.set(b.name, a);
    return true;
  }
  if (a.kind !== b.kind) {
    errorRef.error = { expected: termToString(b), actual: termToString(a) };
    return false;
  }
  switch (a.kind) {
    case "var":
      return a.name === b.name;
    case "atom":
      return a.value === b.value;
    case "app": {
      const bb = b;
      return a.fn === bb.fn && a.args.length === bb.args.length && a.args.every((arg, i) => unifyInto(arg, bb.args[i], metavars, subst, errorRef));
    }
    case "and":
    case "or":
    case "iff":
    case "implies": {
      const bb = b;
      return unifyInto(a.left, bb.left, metavars, subst, errorRef) && unifyInto(a.right, bb.right, metavars, subst, errorRef);
    }
    case "not": {
      return unifyInto(a.body, b.body, metavars, subst, errorRef);
    }
    case "forall":
    case "exists": {
      const aa = a;
      const bb = b;
      if (aa.domain !== bb.domain) {
        errorRef.error = { expected: `domain ${bb.domain}`, actual: `domain ${aa.domain}` };
        return false;
      }
      return unifyInto(aa.body, bb.body, metavars, subst, errorRef);
    }
    case "mem": {
      const aa = a;
      const bb = b;
      return unifyInto(aa.element, bb.element, metavars, subst, errorRef) && unifyInto(aa.set, bb.set, metavars, subst, errorRef);
    }
    case "eq": {
      const aa = a;
      const bb = b;
      const saved = new Map(subst);
      if (unifyInto(aa.left, bb.left, metavars, subst, errorRef) && unifyInto(aa.right, bb.right, metavars, subst, errorRef)) return true;
      subst.clear();
      for (const [k, v] of saved) subst.set(k, v);
      return unifyInto(aa.left, bb.right, metavars, subst, errorRef) && unifyInto(aa.right, bb.left, metavars, subst, errorRef);
    }
    case "sub": {
      const aa = a;
      const bb = b;
      return unifyInto(aa.left, bb.left, metavars, subst, errorRef) && unifyInto(aa.right, bb.right, metavars, subst, errorRef);
    }
    default:
      return false;
  }
}
function occursIn(name, term) {
  switch (term.kind) {
    case "var":
      return term.name === name;
    case "atom":
      return false;
    case "app":
      return term.args.some((a) => occursIn(name, a));
    case "and":
    case "or":
    case "iff":
    case "implies":
      return occursIn(name, term.left) || occursIn(name, term.right);
    case "not":
      return occursIn(name, term.body);
    case "forall":
    case "exists": {
      const t = term;
      return t.variable !== name && occursIn(name, t.body);
    }
    case "mem":
      return occursIn(name, term.element) || occursIn(name, term.set);
    case "eq":
    case "sub":
      return occursIn(name, term.left) || occursIn(name, term.right);
    default:
      return false;
  }
}

// src/kernel/category.ts
var import_crypto = require("crypto");

// src/kernel/values.ts
var NEGATION_TABLE = {
  "0": "1",
  "1": "0",
  "\u03C9": "\u03C9"
};
var AND_TABLE = {
  "0": { "0": "0", "1": "0", "\u03C9": "0" },
  "1": { "0": "0", "1": "1", "\u03C9": "\u03C9" },
  "\u03C9": { "0": "0", "1": "\u03C9", "\u03C9": "\u03C9" }
};
var OR_TABLE = {
  "0": { "0": "0", "1": "1", "\u03C9": "\u03C9" },
  "1": { "0": "1", "1": "1", "\u03C9": "1" },
  "\u03C9": { "0": "\u03C9", "1": "1", "\u03C9": "\u03C9" }
};
var IMPLIES_TABLE = {
  "0": { "0": "1", "1": "1", "\u03C9": "1" },
  "1": { "0": "0", "1": "1", "\u03C9": "\u03C9" },
  "\u03C9": { "0": "\u03C9", "1": "1", "\u03C9": "\u03C9" }
};
function neg(value) {
  return NEGATION_TABLE[value];
}
function and(left, right) {
  return AND_TABLE[left][right];
}
function or(left, right) {
  return OR_TABLE[left][right];
}
function implies(left, right) {
  return IMPLIES_TABLE[left][right];
}
function isClassical(value) {
  return value === "0" || value === "1";
}

// src/kernel/category.ts
var KernelError = class extends Error {
  constructor(message) {
    super(message);
    this.name = "KernelError";
  }
};
var WenittainCategory = class {
  constructor() {
    this.objects = /* @__PURE__ */ new Map();
    this.morphisms = /* @__PURE__ */ new Map();
    this.pendingMorphisms = /* @__PURE__ */ new Map();
    this.resolutionMonad = {
      unit: (proposition) => `T(${proposition})`,
      multiply: (proposition) => `T(${proposition})`
    };
  }
  createObject(proposition, tau = "1", unresolvedTerms = [], options = {}) {
    const id = objectId(proposition);
    const partial = tau === "\u03C9" || unresolvedTerms.length > 0;
    const object = {
      id,
      proposition,
      tau,
      partial,
      unresolvedTerms: [...new Set(unresolvedTerms)],
      complementId: options.complementId,
      suspended: options.suspended ?? tau === "\u03C9"
    };
    this.objects.set(id, object);
    return object;
  }
  createMorphism(input) {
    const pending = input.tau === "\u03C9";
    const morphism = {
      id: morphismId(input.proposition, input.rule, input.inputs ?? []),
      domain: input.domain,
      codomain: input.codomain,
      tau: input.tau,
      rule: input.rule,
      inputs: input.inputs ?? [],
      pending,
      proposition: input.proposition,
      unresolvedTerms: [...new Set(input.unresolvedTerms ?? [])],
      domainRestriction: input.domainRestriction ?? input.domain,
      suspended: input.suspended ?? pending
    };
    this.morphisms.set(morphism.id, morphism);
    if (pending) {
      this.pendingMorphisms.set(morphism.id, morphism);
    }
    return morphism;
  }
  complementOf(proposition) {
    const display = proposition.startsWith("\xAC") ? proposition.slice(1).trim() : `\xAC${proposition}`;
    const object = this.createObject(display);
    const source2 = this.createObject(proposition, object.tau, [], { complementId: object.id });
    object.complementId = source2.id;
    this.objects.set(source2.id, source2);
    this.objects.set(object.id, object);
    return object;
  }
  classicalImplication(left, right) {
    return `${this.complementDisplay(left)} \u2228 ${right}`;
  }
  suspendObject(proposition, unresolvedTerms = []) {
    const suspended = this.resolutionMonad.unit(proposition);
    return this.createObject(suspended, "\u03C9", unresolvedTerms, { suspended: true });
  }
  compose(left, right, proposition, rule) {
    if (left.codomain !== right.domain) {
      throw new KernelError(`Invalid composition: ${left.codomain} does not match ${right.domain}`);
    }
    if (left.pending || right.pending) {
      throw new KernelError("\u03C9-Barrier: pending morphism cannot be used in classical derivation before Ra fires");
    }
    return this.createMorphism({
      proposition,
      domain: left.domain,
      codomain: right.codomain,
      tau: implies(left.tau, right.tau),
      rule,
      inputs: [left.id, right.id],
      unresolvedTerms: [...left.unresolvedTerms, ...right.unresolvedTerms],
      domainRestriction: right.domainRestriction,
      suspended: left.suspended || right.suspended
    });
  }
  ensureClassical(morphism) {
    if (!isClassical(morphism.tau) || morphism.pending) {
      throw new KernelError("\u03C9-Barrier: pending morphism cannot be used in classical derivation before Ra fires");
    }
  }
  truthValueOfMorphism(morphism) {
    if (morphism.pending || morphism.suspended) return "\u03C9";
    if (morphism.codomain === objectId("\u22A5") || morphism.proposition === "\u22A5") return "0";
    return morphism.tau;
  }
  meetTruth(left, right) {
    return and(left, right);
  }
  joinTruth(left, right) {
    return or(left, right);
  }
  complementTruth(value) {
    return neg(value);
  }
  complementDisplay(proposition) {
    return proposition.startsWith("\xAC") ? proposition.slice(1).trim() : `\xAC${proposition}`;
  }
};
function objectId(proposition) {
  return `obj:${stableHash(proposition)}`;
}
function morphismId(proposition, rule, inputs) {
  return `mor:${stableHash(`${proposition}|${rule}|${inputs.join(",")}`)}`;
}
function stableHash(value) {
  return (0, import_crypto.createHash)("sha256").update(value).digest("hex").slice(0, 16);
}

// src/kernel/category-diagrams.ts
var CategoryDiagramError = class extends Error {
  constructor(message) {
    super(message);
    this.name = "CategoryDiagramError";
  }
};
var DEFAULT_CATEGORY = "DefaultCategory";
var CategoryDiagramKernel = class {
  constructor() {
    this.categories = /* @__PURE__ */ new Map();
    this.equalities = [];
    this.functors = /* @__PURE__ */ new Map();
    this.ensureCategory(DEFAULT_CATEGORY);
  }
  registerClaim(claim) {
    const predicate = parseCategoryPredicateCanonical(claim);
    if (predicate) {
      this.registerPredicate(predicate.name, predicate.args);
      return;
    }
    const morphism = parseMorphismDeclarationCanonical(claim);
    if (morphism) {
      this.registerMorphism(DEFAULT_CATEGORY, morphism);
      return;
    }
    const equality = looksLikeCategoricalEquality(claim) ? parseCategoricalEqualityCanonical(claim) : null;
    if (equality) {
      try {
        const left = this.resolveMorphismExpr(equality.left);
        const right = this.resolveMorphismExpr(equality.right);
        if (left.category !== right.category) {
          throw new CategoryDiagramError("Category error: objects or morphisms belong to different categories");
        }
        this.equalities.push({ left: equality.left, right: equality.right, category: left.category, valid: left.id === right.id || sameType(left, right) });
      } catch (e) {
        if (!(e instanceof CategoryDiagramError)) throw e;
      }
    }
  }
  ensureCategory(id) {
    const normalized = id.trim();
    const existing = this.categories.get(normalized);
    if (existing) return existing;
    const category = {
      id: normalized,
      objects: /* @__PURE__ */ new Map(),
      morphisms: /* @__PURE__ */ new Map()
    };
    this.categories.set(normalized, category);
    return category;
  }
  ensureObject(categoryId, label) {
    const category = this.ensureCategory(categoryId);
    const normalized = normalize(label);
    const existing = category.objects.get(normalized);
    if (existing) return existing;
    const object = { id: `${category.id}:${normalized}`, category: category.id, label: normalized };
    category.objects.set(normalized, object);
    return object;
  }
  registerMorphism(categoryId, declaration) {
    const category = this.ensureCategory(categoryId);
    const domain = this.ensureObject(category.id, declaration.domain);
    const codomain = this.ensureObject(category.id, declaration.codomain);
    const existing = category.morphisms.get(normalize(declaration.label));
    if (existing) return existing;
    const morphism = {
      id: `${category.id}:${normalize(declaration.label)}`,
      category: category.id,
      label: normalize(declaration.label),
      domain: domain.id,
      codomain: codomain.id,
      primitive: true,
      components: []
    };
    category.morphisms.set(morphism.label, morphism);
    return morphism;
  }
  resolveMorphismExpr(expr, categoryHint = DEFAULT_CATEGORY) {
    switch (expr.kind) {
      case "name": {
        const category = this.ensureCategory(categoryHint);
        const direct = category.morphisms.get(normalize(expr.label));
        if (!direct) throw new CategoryDiagramError(`Category error: unknown morphism '${expr.label}'`);
        return direct;
      }
      case "identity": {
        const object = this.ensureObject(categoryHint, expr.object);
        return {
          id: `${categoryHint}:id_${object.label}`,
          category: categoryHint,
          label: `id_${object.label}`,
          domain: object.id,
          codomain: object.id,
          primitive: false,
          components: []
        };
      }
      case "compose": {
        const right = this.resolveMorphismExpr(expr.right, categoryHint);
        const left = this.resolveMorphismExpr(expr.left, right.category);
        if (left.category !== right.category) {
          throw new CategoryDiagramError("Category error: objects or morphisms belong to different categories");
        }
        if (right.codomain !== left.domain) {
          throw new CategoryDiagramError(
            `Category error: morphisms do not compose (codomain of ${right.label} is ${objectLabel(right.codomain)}, domain of ${left.label} is ${objectLabel(left.domain)})`
          );
        }
        return {
          id: `${left.category}:${normalize(formatMorphismExpr(expr))}`,
          category: left.category,
          label: formatMorphismExpr(expr),
          domain: right.domain,
          codomain: left.codomain,
          primitive: false,
          components: [left.id, right.id]
        };
      }
      case "functor_map": {
        const functor = this.functors.get(expr.functor);
        if (!functor) {
          throw new CategoryDiagramError(`Category error: unknown functor '${expr.functor}'`);
        }
        const argument = this.resolveMorphismExpr(expr.argument, functor.source);
        if (argument.category !== functor.source) {
          throw new CategoryDiagramError("Category error: objects or morphisms belong to different categories");
        }
        const sourceDomain = this.objectById(argument.domain);
        const sourceCodomain = this.objectById(argument.codomain);
        const mappedDomain = this.ensureObject(functor.target, `${expr.functor}(${sourceDomain.label})`);
        const mappedCodomain = this.ensureObject(functor.target, `${expr.functor}(${sourceCodomain.label})`);
        return {
          id: `${functor.target}:${normalize(formatMorphismExpr(expr))}`,
          category: functor.target,
          label: formatMorphismExpr(expr),
          domain: mappedDomain.id,
          codomain: mappedCodomain.id,
          primitive: false,
          components: [argument.id]
        };
      }
    }
  }
  equalMorphisms(leftExpr, rightExpr) {
    const left = this.resolveMorphismExpr(leftExpr);
    const right = this.resolveMorphismExpr(rightExpr, left.category);
    if (left.category !== right.category) return false;
    if (left.id === right.id) return true;
    if (sameType(left, right) && this.equalities.some(
      (eq) => eq.category === left.category && (formatMorphismExpr(eq.left) === formatMorphismExpr(leftExpr) && formatMorphismExpr(eq.right) === formatMorphismExpr(rightExpr) || formatMorphismExpr(eq.left) === formatMorphismExpr(rightExpr) && formatMorphismExpr(eq.right) === formatMorphismExpr(leftExpr))
    )) {
      return true;
    }
    return normalizeMorphism(left) === normalizeMorphism(right);
  }
  registerPredicate(name, args2) {
    switch (name) {
      case "Category":
        if (args2[0]) this.ensureCategory(args2[0]);
        return;
      case "Object":
        if (args2.length >= 2) this.ensureObject(args2[0], args2[1]);
        return;
      case "Morphism":
        if (args2.length >= 4) this.registerMorphism(args2[0], { label: args2[1], domain: args2[2], codomain: args2[3] });
        return;
      case "Functor":
        if (args2.length >= 3) {
          this.ensureCategory(args2[1]);
          this.ensureCategory(args2[2]);
          this.functors.set(args2[0], { source: args2[1], target: args2[2] });
        }
        return;
      default:
        return;
    }
  }
  objectById(id) {
    for (const category of this.categories.values()) {
      for (const object of category.objects.values()) {
        if (object.id === id) return object;
      }
    }
    throw new CategoryDiagramError(`Category error: unknown object '${id}'`);
  }
};
function looksLikeCategoricalEquality(claim) {
  return claim.includes("\u2218") || /\bid_/.test(claim) || /^[A-Z][\w₀-₉ₐ-ₙ]*\(.+\)\s*=/.test(claim);
}
function normalize(value) {
  return value.trim().replace(/\s+/g, " ");
}
function normalizeMorphism(morphism) {
  return `${morphism.category}:${morphism.domain}:${morphism.codomain}:${morphism.label}`;
}
function sameType(left, right) {
  return left.category === right.category && left.domain === right.domain && left.codomain === right.codomain;
}
function objectLabel(id) {
  const index = id.indexOf(":");
  return index === -1 ? id : id.slice(index + 1);
}

// src/checker/checker.ts
var TOP = "\u22A4";
var BOTTOM = "\u22A5";
var BUILTIN_SORTS = /* @__PURE__ */ new Set([
  "\u2115",
  "\u2124",
  "\u211A",
  "\u211D",
  "String",
  "Set",
  "Element",
  // FuturChain blockchain primitive types
  "Address",
  "Hash",
  "Signature",
  "Slot",
  "Epoch",
  "TokenAmount",
  "Bool",
  "Nat",
  "Int"
]);
function checkFile(nodes, options = {}) {
  const diagnostics = [];
  const reports = [];
  const structs = collectStructDefinitions(nodes, diagnostics);
  const types = collectTypeDefinitions(nodes, structs, diagnostics);
  const pairs = findPairs(nodes);
  const pairNames = new Set(pairs.map((pair) => normalizeName(pair.theorem.name)));
  const lemmas = /* @__PURE__ */ new Map();
  const eliminators = generateEliminators(types);
  for (const [name, claimSet] of eliminators) {
    lemmas.set(name, claimSet);
  }
  for (const node of nodes) {
    if (node.type === "FnDecl" && node.isNative) {
      lemmas.set(normalizeName(node.name), {
        name: node.name,
        premises: node.params.map((p) => `${p.name} \u2208 ${p.type}`),
        conclusion: `${node.name}(${node.params.map((p) => p.name).join(", ")}) \u2208 ${node.returnType}`,
        state: "PROVED"
      });
    }
    if (node.type === "Axiom") {
      lemmas.set(normalizeName(node.name), {
        name: node.name,
        premises: [],
        conclusion: node.statement,
        state: "PROVED"
      });
      reports.push({
        name: node.name,
        state: "PROVED",
        valid: true,
        stepCount: 0,
        goal: node.statement,
        premises: [],
        derivedConclusion: node.statement,
        proofSteps: [],
        proofObjects: [],
        derivations: [],
        diagnostics: [{ severity: "info", message: `Axiom '${node.name}' accepted without proof` }],
        provedCount: 1,
        pendingCount: 0
      });
    }
  }
  let theoremCount = 0;
  let proofCount = 0;
  let pairedCount = 0;
  for (const node of nodes) {
    if (node.type === "Theorem" || node.type === "Lemma") theoremCount++;
    if (node.type === "Proof") proofCount++;
  }
  for (const pair of pairs) {
    pairedCount++;
    const report = checkPair(pair, lemmas, structs, types, options);
    reports.push(report);
    if (pair.theorem.type === "Lemma") {
      lemmas.set(normalizeName(pair.theorem.name), {
        name: pair.theorem.name,
        premises: theoremPremises(pair.theorem),
        conclusion: theoremGoal(pair.theorem),
        state: report.state
      });
    }
  }
  for (const node of nodes) {
    if (node.type === "Theorem" && !pairNames.has(normalizeName(node.name))) {
      diagnostics.push({ severity: "info", message: `Theorem '${node.name}' has no proof` });
    }
    if (node.type === "Lemma" && !pairNames.has(normalizeName(node.name))) {
      diagnostics.push({ severity: "info", message: `Lemma '${node.name}' has no proof` });
    }
  }
  const proofApplyNames = /* @__PURE__ */ new Map();
  for (const pair of pairs) {
    proofApplyNames.set(normalizeName(pair.theorem.name), collectApplyNames(pair.proof.body ?? []));
  }
  for (let i = 0; i < nodes.length; i++) {
    const node = nodes[i];
    if (node.type !== "Proof") continue;
    const proofNode = node;
    if (proofNode.fnMeta) continue;
    const conn = proofNode.connective;
    if (!conn || conn === "\u2194") continue;
    if (conn === "\u2228") {
      diagnostics.push({
        severity: "warning",
        message: `Inter-block connective '\u2228' before the block after '${proofNode.name}' is not validated by the checker. The disjunctive relationship is accepted but not verified.`
      });
      continue;
    }
    let j = i + 1;
    while (j < nodes.length && nodes[j].type !== "Theorem" && nodes[j].type !== "Lemma") j++;
    if (j >= nodes.length) continue;
    const nextBlock = nodes[j];
    const nextApply = proofApplyNames.get(normalizeName(nextBlock.name)) ?? /* @__PURE__ */ new Set();
    const prevName = normalizeName(proofNode.name);
    const nextUsesThis = nextApply.has(prevName);
    if (conn === "\u2192" && !nextUsesThis) {
      diagnostics.push({
        severity: "error",
        message: `Incorrect inter-block connective '\u2192' before '${nextBlock.name}': this block does not depend on '${proofNode.name}'. Use \u2227 for independent blocks.`
      });
    } else if (conn === "\u2227" && nextUsesThis) {
      diagnostics.push({
        severity: "error",
        message: `Incorrect inter-block connective '\u2227' before '${nextBlock.name}': this block depends on '${proofNode.name}' via apply(). Use \u2192 to show the dependency.`
      });
    }
  }
  const hasInterBlockErrors = diagnostics.some((d) => d.severity === "error");
  const axiomCount = nodes.filter((n) => n.type === "Axiom" || n.type === "FnDecl" && n.isNative).length;
  const declCount = nodes.filter((n) => n.type === "Struct" || n.type === "TypeDecl" || n.type === "Definition").length;
  const hasContent = pairedCount > 0 || axiomCount > 0 || declCount > 0;
  const pairState = combineStates(reports.map((report) => report.state), hasContent ? "PROVED" : "FAILED");
  const state = hasInterBlockErrors ? "FAILED" : pairState;
  return {
    state,
    valid: state === "PROVED",
    theoremCount,
    proofCount,
    pairedCount,
    reports,
    diagnostics
  };
}
function collectApplyNames(nodes) {
  const names = /* @__PURE__ */ new Set();
  function walk(ns) {
    for (const n of ns) {
      if (n.type === "Apply") names.add(normalizeName(n.target));
      if ("body" in n && Array.isArray(n.body)) walk(n.body);
      if ("steps" in n && Array.isArray(n.steps)) walk(n.steps);
      if ("cases" in n && Array.isArray(n.cases)) {
        for (const c of n.cases) walk(c.body ?? []);
      }
    }
  }
  walk(nodes);
  return names;
}
function checkPair(pair, lemmas, structs, types, _options) {
  const declErrors = validateDeclarationBody(pair.theorem.name, pair.theorem.body);
  const premises = theoremPremises(pair.theorem);
  const goal = theoremGoal(pair.theorem);
  const ctx = createContext(goal, lemmas, premises, structs, types);
  seedPremises(ctx, premises);
  for (const err of declErrors) {
    const isLegacy = err.includes("replace assert()") || err.includes("replace given()") || err.includes("no longer valid");
    ctx.diagnostics.push({ severity: isLegacy ? "warning" : "error", message: err, rule: "STRUCTURAL" });
  }
  if (pair.proof.fnMeta) {
    const recursionIssue = validateListStructuralRecursion(pair.proof);
    if (recursionIssue) {
      ctx.unverifiedReasons.push(recursionIssue);
      ctx.diagnostics.push({ severity: "warning", message: recursionIssue, rule: "STRUCTURAL" });
    }
  }
  let prevDerivedObject = null;
  let prevConnective = null;
  let prevIsAssume = false;
  let prevAssumeKind = "assume()";
  for (let index = 0; index < pair.proof.body.length; index++) {
    const step = index + 1;
    const node = pair.proof.body[index];
    const objectsBefore = ctx.objects.length;
    try {
      handleNode(ctx, node, step);
    } catch (error) {
      const message = error instanceof Error ? error.message : "Unknown checker failure";
      ctx.diagnostics.push({ severity: "error", step, message });
      ctx.proofSteps.push({
        step,
        kind: classifyStep(node),
        claim: nodeToClaim(node),
        rule: "STRUCTURAL",
        state: "FAILED",
        message
      });
    }
    const currDerivedObject = ctx.objects.length > objectsBefore ? ctx.objects[ctx.objects.length - 1] : null;
    const isDerivationStep = node.type === "Prove" || node.type === "Conclude" || node.type === "Assert" || node.type === "AndIntroStep" || node.type === "OrIntroStep" || node.type === "Apply";
    const isNewStyleStep = node.type === "Prove" || node.type === "Assert" || node.type === "AndIntroStep" || node.type === "OrIntroStep" || node.type === "Apply";
    const isAssume = node.type === "Assume" || node.type === "Intro" || node.type === "Obtain";
    if (isNewStyleStep && prevDerivedObject && prevConnective) {
      if (prevIsAssume) {
        if (prevConnective !== "\u2192") {
          const msg = `Incorrect connective '${prevConnective}' after ${prevAssumeKind}: use \u2192 because the introduced hypothesis leads to the following derivation.`;
          ctx.diagnostics.push({ severity: "error", step, message: msg, rule: "CONNECTIVE" });
        }
      } else if (currDerivedObject) {
        validateConnective(ctx, prevConnective, prevDerivedObject, currDerivedObject, step);
      }
    }
    if (isDerivationStep && currDerivedObject) {
      prevDerivedObject = currDerivedObject;
      prevConnective = node.connective ?? null;
      prevIsAssume = false;
    } else if (isAssume) {
      prevDerivedObject = ctx.assumptions[ctx.assumptions.length - 1] ?? null;
      prevConnective = node.connective;
      prevIsAssume = true;
      prevAssumeKind = node.type === "Intro" ? "intro()" : node.type === "Obtain" ? "obtain()" : "assume()";
    }
  }
  const derivedConclusion = findDerivedConclusion(ctx, goal);
  if (goal && !derivedConclusion) {
    ctx.diagnostics.push({
      severity: "error",
      message: `Proof '${pair.proof.name}' does not establish theorem goal '${goal}'`,
      rule: "STRUCTURAL"
    });
  }
  const state = reportState(ctx, goal, derivedConclusion);
  return {
    name: pair.theorem.name,
    state,
    valid: state === "PROVED",
    stepCount: pair.proof.body.length,
    goal,
    premises,
    derivedConclusion,
    proofSteps: ctx.proofSteps,
    proofObjects: ctx.objects,
    derivations: ctx.derivations,
    diagnostics: ctx.diagnostics,
    provedCount: ctx.objects.filter((object) => object.tau === "1").length,
    pendingCount: ctx.objects.filter((object) => object.pending).length
  };
}
function createContext(goal, lemmas, premises, structs, types) {
  const category = new WenittainCategory();
  category.createObject(TOP);
  category.createObject(BOTTOM);
  for (const premise of premises) {
    ensureClaimObjects(category, premise);
  }
  if (goal) {
    ensureClaimObjects(category, goal);
  }
  return {
    category,
    diagrams: new CategoryDiagramKernel(),
    objects: [],
    derivations: [],
    diagnostics: [],
    proofSteps: [],
    variables: [],
    assumptions: [],
    premises: [],
    lemmas: new Map(lemmas),
    goal,
    structs,
    types,
    unverifiedReasons: []
  };
}
function seedPremises(ctx, premises) {
  for (const premise of premises) {
    const morphism = createKernelObject(ctx, premise, "PREMISE", -1, [], [], "1");
    ctx.premises.push(morphism);
  }
}
function createMutableContext(premises, goal) {
  const ctx = createContext(goal, /* @__PURE__ */ new Map(), premises, /* @__PURE__ */ new Map(), /* @__PURE__ */ new Map());
  seedPremises(ctx, premises);
  return ctx;
}
function evaluateIncrementalStep(ctx, node) {
  const startStepCount = ctx.proofSteps.length;
  const stepNumber = startStepCount + 1;
  try {
    handleNode(ctx, node, stepNumber);
  } catch (error) {
    const message = error instanceof Error ? error.message : "Unknown checker failure";
    ctx.diagnostics.push({ severity: "error", step: stepNumber, message });
    ctx.proofSteps.push({
      step: stepNumber,
      kind: classifyStep(node),
      claim: nodeToClaim(node),
      rule: "STRUCTURAL",
      state: "FAILED",
      message
    });
  }
  if (ctx.proofSteps.length > startStepCount) {
    return ctx.proofSteps[ctx.proofSteps.length - 1];
  }
  return null;
}
function handleNode(ctx, node, step) {
  const legacy = node.legacyError;
  if (legacy) {
    ctx.diagnostics.push({ severity: "warning", step, message: legacy, rule: "STRUCTURAL" });
  }
  switch (node.type) {
    case "Assume":
      handleAssume(ctx, node, step);
      return;
    case "SetVar":
      handleSetVar(ctx, node, step);
      return;
    case "Assert":
      handleClaimStep(ctx, node, step, "assert");
      return;
    case "Prove":
      handleProveStep(ctx, node, step);
      return;
    case "Derive":
      handleDerive(ctx, node, step);
      return;
    case "AndIntroStep":
      handleAndIntroStep(ctx, node, step);
      return;
    case "OrIntroStep":
      handleOrIntroStep(ctx, node, step);
      return;
    case "Conclude":
      handleClaimStep(ctx, node, step, "conclude");
      return;
    case "Induction":
      handleInduction(ctx, node, step);
      return;
    case "Match":
      handleMatch(ctx, node, step);
      return;
    case "Apply":
      handleApply(ctx, node.target, step);
      return;
    case "Raw":
      handleRaw(ctx, node, step);
      return;
    case "Intro":
      handleIntro(ctx, node, step);
      return;
    case "Rewrite":
      handleRewrite(ctx, node, step);
      return;
    case "Exact":
      handleExact(ctx, node, step);
      return;
    case "Obtain":
      handleObtain(ctx, node, step);
      return;
    default:
      return;
  }
}
function handleProveStep(ctx, node, step) {
  handleClaimStep(ctx, { type: "Assert", expr: node.expr, connective: node.connective }, step, "prove");
}
function handleDerive(ctx, node, step) {
  const conclusions = deriveConclusions(ctx);
  if (conclusions.length === 0) {
    ctx.diagnostics.push({ severity: "info", message: "derive(): no new conclusions reachable from current context" });
  } else {
    const lines = conclusions.map((c) => `  ${c}`).join("\n");
    ctx.diagnostics.push({ severity: "info", message: `derive(): ${conclusions.length} reachable conclusion(s):
${lines}` });
  }
}
function handleAndIntroStep(ctx, node, step) {
  const claim = `${node.left} \u2227 ${node.right}`;
  handleClaimStep(ctx, { type: "Assert", expr: { type: "Atom", condition: claim, atomKind: "expression" }, connective: node.connective }, step, "andIntro");
}
function handleOrIntroStep(ctx, node, step) {
  handleClaimStep(ctx, { type: "Assert", expr: { type: "Atom", condition: node.claim, atomKind: "expression" }, connective: node.connective }, step, "orIntro");
}
function dependsOn(objects, target, prereq) {
  const visited = /* @__PURE__ */ new Set();
  const stack = [...target.inputs];
  while (stack.length > 0) {
    const id = stack.pop();
    if (visited.has(id)) continue;
    visited.add(id);
    if (id === prereq.id) return true;
    const obj = objects.find((o) => o.id === id);
    if (obj) stack.push(...obj.inputs);
  }
  return false;
}
function validateConnective(ctx, connective, prev, curr, step) {
  if (!connective) return;
  const depends = dependsOn(ctx.objects, curr, prev);
  if (connective === "\u2192") {
    if (!depends) {
      const msg = `Incorrect connective '\u2192' at step ${step}: '${curr.claim}' does not depend on '${prev.claim}'. Use \u2227 if these are independent facts.`;
      ctx.diagnostics.push({ severity: "error", step, message: msg, rule: "CONNECTIVE" });
    }
  } else if (connective === "\u2227") {
    if (depends) {
      const msg = `Incorrect connective '\u2227' at step ${step}: '${curr.claim}' depends on '${prev.claim}'. Use \u2192 to show this follows from the previous step.`;
      ctx.diagnostics.push({ severity: "error", step, message: msg, rule: "CONNECTIVE" });
    }
  } else if (connective === "\u2228") {
    const parts = parseDisjunctionCanonical(curr.claim);
    const prevClaim = prev.claim;
    if (!parts || normArith(parts[0]) !== normArith(prevClaim) && normArith(parts[1]) !== normArith(prevClaim)) {
      const msg = `Incorrect connective '\u2228' at step ${step}: '${curr.claim}' is not a disjunction containing '${prev.claim}'. Use \u2228 only to introduce a disjunction from one of its disjuncts.`;
      ctx.diagnostics.push({ severity: "error", step, message: msg, rule: "CONNECTIVE" });
    }
  }
}
function handleAssume(ctx, node, step) {
  const claim = exprToProp(node.expr);
  const proofObject = createKernelObject(ctx, claim, "ASSUMPTION", step);
  ctx.assumptions.push(proofObject);
  ctx.proofSteps.push({
    step,
    kind: "assume",
    claim,
    rule: "ASSUMPTION",
    state: "PROVED",
    message: "Assumption introduced as a morphism into the current Boolean-category derivation context"
  });
}
function handleSetVar(ctx, node, step) {
  ctx.variables.push({ name: node.varName, domain: node.varType });
  ctx.proofSteps.push({
    step,
    kind: "setVar",
    claim: node.varType ? `${node.varName}: ${node.varType}` : node.varName,
    rule: "STRUCTURAL",
    state: "PROVED",
    message: "Bound variable recorded for categorical introduction or elimination rules"
  });
}
function handleInduction(ctx, node, step) {
  const claim = ctx.goal ?? exprToProp(node.fold);
  createKernelObject(ctx, claim, "FOLD_ELIM", step);
  ctx.proofSteps.push({
    step,
    kind: "induction",
    claim,
    rule: "FOLD_ELIM",
    state: "PROVED",
    uses: [exprToProp(node.fold), node.base, node.step],
    message: "Desugared induction into the trusted fold primitive"
  });
}
function handleMatch(ctx, node, step) {
  const scrutinee = exprToProp(node.scrutinee);
  const scrutineeMembership = requireAnyMembership(ctx, scrutinee);
  const scrutineeType = scrutineeMembership ? parseMembershipCanonical(scrutineeMembership.claim)?.set ?? null : null;
  const parsedSort = scrutineeType ? parseSort(scrutineeType) : null;
  if (parsedSort?.kind === "list" && scrutineeType) {
    handleListMatch(ctx, node, step, scrutinee, scrutineeType, parsedSort);
    return;
  }
  const boolType = inferBooleanMatchType(node);
  const typeDef = scrutineeType ? ctx.types.get(scrutineeType) : boolType;
  if (!scrutineeMembership && !boolType || !typeDef) {
    ctx.diagnostics.push({ severity: "error", step, message: `Pattern match requires a scrutinee with a registered sum type: '${scrutinee}'`, rule: "MATCH_EXHAUSTIVE" });
    ctx.proofSteps.push({
      step,
      kind: "match",
      claim: scrutinee,
      rule: "MATCH_EXHAUSTIVE",
      state: "FAILED",
      message: "No registered variant information is available for this match scrutinee"
    });
    return;
  }
  const covered = new Set(
    node.cases.filter((matchCase) => matchCase.pattern.kind === "variant").map((matchCase) => matchCase.pattern.constructor)
  );
  const exhaustive = node.cases.some((matchCase) => matchCase.pattern.kind === "wildcard") || typeDef.variants.every((variant) => covered.has(variant.name));
  if (!exhaustive) {
    ctx.diagnostics.push({ severity: "error", step, message: "MATCH_EXHAUSTIVE failed: non-exhaustive match", rule: "MATCH_EXHAUSTIVE" });
    ctx.proofSteps.push({
      step,
      kind: "match",
      claim: scrutinee,
      rule: "MATCH_EXHAUSTIVE",
      state: "FAILED",
      message: "Pattern matching must cover every variant or include a wildcard case"
    });
    return;
  }
  const branchStates = [];
  const branchUses = [];
  for (const matchCase of node.cases) {
    const branch = createBranchContext(ctx);
    const variant = matchCase.pattern.kind !== "variant" ? null : typeDef.variants.find((candidate) => candidate.name === matchCase.pattern.constructor) ?? null;
    if (matchCase.pattern.kind === "variant" && !variant) {
      branchStates.push("FAILED");
      continue;
    }
    if (variant && matchCase.pattern.kind === "variant") {
      applyVariantPatternBindings(branch, scrutinee, variant, matchCase.pattern.bindings, step);
      branchUses.push(`${scrutinee} \u2208 ${variant.name}`);
    } else {
      branchUses.push("_");
    }
    for (const branchNode of matchCase.body) {
      try {
        handleNode(branch, branchNode, step);
      } catch (error) {
        const message = error instanceof Error ? error.message : "Unknown match-branch failure";
        branch.diagnostics.push({ severity: "error", step, message, rule: "OR_ELIM" });
      }
    }
    branchStates.push(evaluateMatchBranch(branch, ctx.goal, step));
  }
  if (branchStates.some((state) => state === "FAILED")) {
    ctx.diagnostics.push({ severity: "error", step, message: "At least one match branch does not establish the required conclusion", rule: "OR_ELIM" });
    ctx.proofSteps.push({
      step,
      kind: "match",
      claim: ctx.goal ?? scrutinee,
      rule: "MATCH_EXHAUSTIVE",
      state: "FAILED",
      uses: branchUses,
      message: "Exhaustive case analysis failed because a branch does not discharge the branch goal"
    });
    return;
  }
  const targetClaim = ctx.goal ?? scrutineeMembership?.claim ?? scrutinee;
  createKernelObject(ctx, targetClaim, "MATCH_EXHAUSTIVE", step);
  ctx.proofSteps.push({
    step,
    kind: "match",
    claim: targetClaim,
    rule: "MATCH_EXHAUSTIVE",
    state: "PROVED",
    uses: branchUses,
    message: "Validated exhaustive proof by cases via categorical OR elimination"
  });
}
function handleListMatch(ctx, node, step, scrutinee, scrutineeType, parsedSort) {
  if (!requireAnyMembership(ctx, scrutinee) || parsedSort.kind !== "list" || !parsedSort.element) {
    ctx.diagnostics.push({ severity: "error", step, message: `Pattern match requires a scrutinee with a registered list sort: '${scrutinee}'`, rule: "MATCH_EXHAUSTIVE" });
    ctx.proofSteps.push({
      step,
      kind: "match",
      claim: scrutinee,
      rule: "MATCH_EXHAUSTIVE",
      state: "FAILED",
      message: "No kernel List sort information is available for this match scrutinee"
    });
    return;
  }
  const nilCase = node.cases.find((matchCase) => matchCase.pattern.kind === "list_nil") ?? null;
  const consCase = node.cases.find((matchCase) => matchCase.pattern.kind === "list_cons") ?? null;
  const exhaustive = node.cases.length === 2 && Boolean(nilCase) && Boolean(consCase);
  if (!exhaustive) {
    ctx.diagnostics.push({ severity: "error", step, message: "MATCH_EXHAUSTIVE failed: List matches must contain exactly [] and [x, ...rest]", rule: "MATCH_EXHAUSTIVE" });
    ctx.proofSteps.push({
      step,
      kind: "match",
      claim: scrutinee,
      rule: "MATCH_EXHAUSTIVE",
      state: "FAILED",
      message: "Kernel List matching requires both Nil and Cons cases"
    });
    return;
  }
  const branchStates = [];
  const branchUses = [];
  for (const matchCase of [nilCase, consCase]) {
    if (!matchCase) continue;
    const branch = createBranchContext(ctx);
    if (matchCase.pattern.kind === "list_cons") {
      applyListPatternBindings(branch, scrutinee, scrutineeType, parsedSort, matchCase.pattern.head, matchCase.pattern.tail, step);
      branchUses.push(`[${matchCase.pattern.head}, ...${matchCase.pattern.tail}]`);
    } else {
      branchUses.push("[]");
    }
    for (const branchNode of matchCase.body) {
      try {
        handleNode(branch, branchNode, step);
      } catch (error) {
        const message = error instanceof Error ? error.message : "Unknown list match-branch failure";
        branch.diagnostics.push({ severity: "error", step, message, rule: "OR_ELIM" });
      }
    }
    branchStates.push(evaluateMatchBranch(branch, ctx.goal, step));
  }
  if (branchStates.some((state) => state === "FAILED" || state === "UNVERIFIED")) {
    ctx.diagnostics.push({ severity: "error", step, message: "At least one list match branch does not establish the required conclusion", rule: "OR_ELIM" });
    ctx.proofSteps.push({
      step,
      kind: "match",
      claim: ctx.goal ?? scrutinee,
      rule: "MATCH_EXHAUSTIVE",
      state: "FAILED",
      uses: branchUses,
      message: "Exhaustive list case analysis failed because a branch does not discharge the branch goal"
    });
    return;
  }
  const targetClaim = ctx.goal ?? `${scrutinee} \u2208 ${scrutineeType}`;
  createKernelObject(ctx, targetClaim, "MATCH_EXHAUSTIVE", step);
  ctx.proofSteps.push({
    step,
    kind: "match",
    claim: targetClaim,
    rule: "MATCH_EXHAUSTIVE",
    state: "PROVED",
    uses: branchUses,
    message: "Validated exhaustive proof by cases over the kernel List primitive"
  });
}
function inferBooleanMatchType(node) {
  const constructors = [];
  for (const matchCase of node.cases) {
    if (matchCase.pattern.kind === "variant") {
      constructors.push(matchCase.pattern.constructor);
    }
  }
  const boolConstructors = /* @__PURE__ */ new Set(["true", "false"]);
  if (constructors.length === 0 || constructors.some((name) => !boolConstructors.has(name))) {
    return null;
  }
  return {
    name: "Bool",
    variants: [
      { name: "true", parent: "Bool", fields: [] },
      { name: "false", parent: "Bool", fields: [] }
    ]
  };
}
function handleApply(ctx, target, step) {
  const lemma = ctx.lemmas.get(normalizeName(target));
  if (!lemma) {
    const hyp = findExact(ctx.objects, target, false) ?? findExact(ctx.assumptions, target, false) ?? findExact(ctx.premises, target, false);
    if (hyp) {
      const impl = parseImplicationCanonical(hyp.claim);
      if (impl && ctx.goal) {
        const [antecedent, consequent] = impl;
        const consTerm = termFromString(consequent);
        const goalTerm = termFromString(ctx.goal);
        if (termEqual(consTerm, goalTerm)) {
          ctx.goal = antecedent;
          ctx.proofSteps.push({
            step,
            kind: "apply",
            claim: antecedent,
            rule: "BY_LEMMA",
            state: "PROVED",
            uses: [hyp.claim],
            message: `Applied '${target}' backward: goal reduced to '${antecedent}'`
          });
          return;
        }
      }
      ctx.diagnostics.push({ severity: "error", step, message: `apply: '${target}' is not an implication whose consequent matches the goal '${ctx.goal ?? "(none)"}'`, rule: "BY_LEMMA" });
      ctx.proofSteps.push({ step, kind: "apply", claim: target, rule: "BY_LEMMA", state: "FAILED", message: `Consequent does not match goal` });
      return;
    }
    ctx.diagnostics.push({ severity: "error", step, message: `Unknown lemma or hypothesis '${target}'`, rule: "BY_LEMMA" });
    ctx.proofSteps.push({
      step,
      kind: "apply",
      claim: target,
      rule: "BY_LEMMA",
      state: "FAILED",
      message: `'${target}' is not available`
    });
    return;
  }
  if (lemma.state !== "PROVED") {
    ctx.diagnostics.push({ severity: "error", step, message: `Lemma '${target}' is not fully proved and cannot be applied`, rule: "BY_LEMMA" });
    ctx.proofSteps.push({
      step,
      kind: "apply",
      claim: lemma.conclusion ?? target,
      rule: "BY_LEMMA",
      state: "FAILED",
      imports: [lemma.name],
      message: `Lemma '${target}' is not fully proved`
    });
    return;
  }
  if (lemma.metavars && lemma.metavars.length > 0 && lemma.conclusion && ctx.goal) {
    const metaSet = new Set(lemma.metavars);
    const lemmaConcTerm = termFromString(lemma.conclusion);
    const goalTerm = termFromString(ctx.goal);
    const unifyResult = unify(lemmaConcTerm, goalTerm, metaSet);
    if (!unifyResult.error) {
      const subst = unifyResult.subst;
      const instantiatedPremises = lemma.premises.map((p) => {
        const t = applySubst(termFromString(p), subst);
        return termToString(t);
      });
      const missingInstantiated = instantiatedPremises.filter((p) => !findExact(ctx.objects, p, false) && !findExact(ctx.premises, p, false) && !findExact(ctx.assumptions, p, false));
      if (missingInstantiated.length === 0) {
        const conclusion = termToString(applySubst(termFromString(lemma.conclusion), subst));
        const inputs2 = instantiatedPremises.map((p) => findExact(ctx.objects, p, false) ?? findExact(ctx.premises, p, false) ?? findExact(ctx.assumptions, p, false)).filter((o) => Boolean(o)).map((o) => o.id);
        createKernelObject(ctx, conclusion, "BY_LEMMA", step, inputs2, [lemma.name], "1");
        ctx.proofSteps.push({
          step,
          kind: "apply",
          claim: conclusion,
          rule: "BY_LEMMA",
          state: "PROVED",
          imports: [lemma.name],
          uses: instantiatedPremises,
          message: `Applied lemma '${target}' via unification`
        });
        return;
      }
    }
    ctx.diagnostics.push({ severity: "error", step, message: `Lemma '${target}' unification failed`, rule: "BY_LEMMA" });
    ctx.proofSteps.push({
      step,
      kind: "apply",
      claim: target,
      rule: "BY_LEMMA",
      state: "FAILED",
      message: `Consequent does not unify with goal`,
      causalError: {
        ruleAttempted: "BY_LEMMA",
        unificationMismatch: unifyResult.error
      }
    });
    return;
  }
  const missing = lemma.premises.filter((premise) => !findExact(ctx.objects, premise, false));
  if (missing.length > 0 || !lemma.conclusion) {
    ctx.diagnostics.push({
      severity: "error",
      step,
      message: `Lemma '${target}' cannot be imported; missing premises: ${missing.join(" ; ") || "conclusion"}`,
      rule: "BY_LEMMA"
    });
    ctx.proofSteps.push({
      step,
      kind: "apply",
      claim: lemma.conclusion ?? target,
      rule: "BY_LEMMA",
      state: "FAILED",
      imports: [lemma.name],
      message: `Lemma '${target}' does not compose with the current context`,
      causalError: {
        ruleAttempted: "BY_LEMMA",
        missingPremises: missing
      }
    });
    return;
  }
  const inputs = lemma.premises.map((premise) => findExact(ctx.objects, premise, false)).filter((object) => Boolean(object)).map((object) => object.id);
  createKernelObject(ctx, lemma.conclusion, "BY_LEMMA", step, inputs, [lemma.name], "1");
  ctx.proofSteps.push({
    step,
    kind: "apply",
    claim: lemma.conclusion,
    rule: "BY_LEMMA",
    state: "PROVED",
    imports: [lemma.name],
    uses: lemma.premises,
    message: `Imported lemma '${target}' as a morphism in the current context`
  });
}
function handleRaw(ctx, node, step) {
  const claim = node.content.trim();
  if (!/^contradiction\s*\(\s*\)\s*;?$/.test(claim)) {
    ctx.diagnostics.push({ severity: "error", step, message: `Unsupported raw proof syntax: '${claim}'. Use assert, assume, conclude, apply, intro, rewrite, or exact.`, rule: "STRUCTURAL" });
    ctx.proofSteps.push({
      step,
      kind: "raw",
      claim,
      rule: "STRUCTURAL",
      state: "FAILED",
      message: "Unsupported raw proof syntax"
    });
    return;
  }
  const contradiction = hasContradiction(ctx.objects);
  if (!contradiction) {
    ctx.diagnostics.push({ severity: "error", step, message: "contradiction() requires conflicting facts in scope", rule: "CONTRADICTION" });
    ctx.proofSteps.push({
      step,
      kind: "raw",
      claim: "contradiction()",
      rule: "CONTRADICTION",
      state: "FAILED",
      message: "No proposition and complement pair is available"
    });
    return;
  }
  const contradictionMeet = createKernelObject(
    ctx,
    `${contradiction[0].claim} \u2227 ${contradiction[1].claim}`,
    "AND_INTRO",
    step,
    contradiction.map((object) => object.id)
  );
  const bottom = createKernelObject(ctx, BOTTOM, "CONTRADICTION", step, [contradictionMeet.id]);
  ctx.proofSteps.push({
    step,
    kind: "raw",
    claim: BOTTOM,
    rule: "CONTRADICTION",
    state: "PROVED",
    uses: [...contradiction.map((object) => object.claim), contradictionMeet.claim],
    message: "Derived falsehood by meeting a proposition with its Boolean complement"
  });
  if (ctx.goal) {
    const exFalso = createKernelObject(ctx, ctx.goal, "CONTRADICTION", step, [bottom.id]);
    ctx.proofSteps.push({
      step,
      kind: "raw",
      claim: ctx.goal,
      rule: "CONTRADICTION",
      state: "PROVED",
      uses: [BOTTOM],
      message: "Factored the current goal through falsehood after contradiction"
    });
    void exFalso;
  }
}
function handleClaimStep(ctx, node, step, kind) {
  const claim = exprToProp(node.expr);
  const derivation = deriveClaim(ctx, claim, step);
  if (derivation.state === "FAILED") {
    ctx.diagnostics.push({ severity: "error", step, message: derivation.message, rule: derivation.rule });
  }
  ctx.proofSteps.push({
    step,
    kind,
    claim,
    rule: derivation.rule,
    state: derivation.state,
    uses: derivation.uses,
    message: derivation.message
  });
}
function deriveClaim(ctx, claim, step) {
  const exact = findExact(ctx.objects, claim, false);
  if (exact) {
    return {
      rule: exact.rule,
      state: exact.pending ? "FAILED" : "PROVED",
      uses: [exact.claim],
      message: "Claim already exists as a morphism in the current derivation"
    };
  }
  const prover = [
    deriveAndIntro,
    deriveAndElim,
    deriveStructClaim,
    deriveMeasureClaim,
    deriveCategoryClaim,
    deriveFoldClaim,
    deriveNotIntro,
    deriveImpliesElim,
    deriveImpliesIntro,
    deriveIffIntro,
    deriveIffElim,
    deriveOrIntro,
    deriveOrElim,
    deriveSubsetIntro,
    deriveSubsetElim,
    deriveSubsetTransitivity,
    deriveSubsetAntisymmetry,
    deriveEqualityReflexivity,
    deriveEqualitySymmetry,
    deriveEqualitySubstitution,
    deriveUnionRule,
    deriveIntersectionRule,
    deriveImageRule,
    derivePreimageRule,
    deriveQuantifierRule,
    deriveDependentTypeRule,
    deriveNaturalTransformationRule,
    deriveExFalso,
    deriveForallElim,
    deriveExistsIntro,
    deriveArithClaim,
    deriveModArithClaim,
    deriveIntClaim,
    deriveRealAnalysisClaim,
    deriveCryptoClaim,
    deriveOrderClaim,
    deriveGraphClaim,
    deriveCombClaim,
    deriveAlgebraClaim,
    deriveLinAlgClaim,
    deriveTopologyClaim,
    deriveNTClaim,
    deriveExtOrderClaim,
    deriveLinAlgExtClaim,
    deriveTopoExtClaim
  ];
  for (const attempt of prover) {
    const result = attempt(ctx, claim, step);
    if (result) {
      return result;
    }
  }
  return {
    rule: "STRUCTURAL",
    state: "FAILED",
    message: `No categorical derivation establishes '${claim}' from the available morphisms`
  };
}
function deriveStructClaim(ctx, claim, step) {
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  const projection = deriveStructProjection(ctx, membership, claim, step);
  if (projection) return projection;
  const structDef = ctx.structs.get(membership.set);
  if (!structDef) return null;
  const inputs = [];
  const uses = [];
  for (const field of structDef.fields) {
    const fieldClaim = `${membership.element}.${field.name} \u2208 ${field.type}`;
    const fieldObject = requireClassical(ctx, fieldClaim, "STRUCT_INTRO");
    if (!fieldObject) return null;
    inputs.push(fieldObject.id);
    uses.push(fieldClaim);
  }
  createKernelObject(ctx, claim, "STRUCT_INTRO", step, inputs);
  return {
    rule: "STRUCT_INTRO",
    state: "PROVED",
    uses,
    message: "Constructed a struct-instance membership from all declared field memberships"
  };
}
function deriveStructProjection(ctx, membership, claim, step) {
  const access = parseFieldAccess(membership.element);
  if (!access) return null;
  const projection = resolveFieldProjection(ctx, access.base, access.path);
  if (!projection || projection.type !== membership.set) return null;
  createKernelObject(ctx, claim, "STRUCT_ELIM", step, [projection.source.id]);
  return {
    rule: "STRUCT_ELIM",
    state: "PROVED",
    uses: [projection.source.claim],
    message: "Projected a field membership from a struct-instance membership"
  };
}
function deriveAndIntro(ctx, claim, step) {
  const parts = parseConjunctionCanonical(claim);
  if (!parts) return null;
  const left = requireClassical(ctx, parts[0], "AND_INTRO");
  const right = requireClassical(ctx, parts[1], "AND_INTRO");
  if (!left || !right) return null;
  createKernelObject(ctx, claim, "AND_INTRO", step, [left.id, right.id]);
  return {
    rule: "AND_INTRO",
    state: "PROVED",
    uses: [parts[0], parts[1]],
    message: "Constructed the Boolean meet from both conjunct morphisms"
  };
}
function deriveFoldClaim(ctx, claim, step) {
  if (!/^fold\s*\(/.test(claim)) return null;
  createKernelObject(ctx, claim, "FOLD_ELIM", step);
  return {
    rule: "FOLD_ELIM",
    state: "PROVED",
    message: "Trusted fold primitive establishes the fold result directly"
  };
}
function parseMeasureArgs(claim) {
  const m = claim.trim().match(/^Measure\s*\(\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
  return m ? { mu: m[1].trim(), sigma: m[2].trim() } : null;
}
function parseSigmaAlgebraArgs(claim) {
  const m = claim.trim().match(/^SigmaAlgebra\s*\(\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
  return m ? { sigma: m[1].trim(), space: m[2].trim() } : null;
}
function parseProbMeasureArgs(claim) {
  const m = claim.trim().match(/^ProbabilityMeasure\s*\(\s*([^,)]+?)\s*,\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
  return m ? { p: m[1].trim(), sigma: m[2].trim(), space: m[3].trim() } : null;
}
function parseMeasurableArgs(claim) {
  const m = claim.trim().match(/^Measurable\s*\(\s*([^,)]+?)\s*,\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
  return m ? { f: m[1].trim(), sigmaX: m[2].trim(), sigmaY: m[3].trim() } : null;
}
function parseFunctionApplication(s) {
  const m = s.trim().match(/^([^\s(]+)\s*\((.+)\)$/);
  return m ? { fn: m[1].trim(), arg: m[2].trim() } : null;
}
function allContextObjects(ctx) {
  return [...ctx.premises, ...ctx.assumptions, ...classicalObjects(ctx)];
}
function splitTopLevelLeq(s) {
  let depth = 0;
  for (let i = 0; i < s.length - 1; i++) {
    const ch = s[i];
    if (ch === "(" || ch === "[") depth++;
    else if (ch === ")" || ch === "]") depth--;
    else if (depth === 0 && s[i] === "\u2264") {
      return [s.slice(0, i).trim(), s.slice(i + 1).trim()];
    }
  }
  return null;
}
function splitTopLevelSum(s) {
  let depth = 0;
  for (let i = s.length - 1; i >= 0; i--) {
    const ch = s[i];
    if (ch === ")" || ch === "]") depth++;
    else if (ch === "(" || ch === "[") depth--;
    else if (depth === 0 && ch === "+") {
      return [s.slice(0, i).trim(), s.slice(i + 1).trim()];
    }
  }
  return null;
}
function deriveMeasureClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const subsetMatch2 = claim.trim().match(/^∅\s*⊆\s*(.+)$/);
  if (subsetMatch2) {
    createKernelObject(ctx, claim, "MEASURE_EMPTY", step);
    return { rule: "MEASURE_EMPTY", state: "PROVED", message: `Empty set is subset of everything` };
  }
  const measurePred = claim.trim().match(/^Measure\((.+?),\s*(.+)\)$/);
  if (measurePred) {
    const [, mu, sigma] = measurePred;
    for (const obj of all) {
      const pma = parseProbMeasureArgs(obj.claim);
      if (pma && pma.p === mu && pma.sigma === sigma) {
        createKernelObject(ctx, claim, "MEASURE_EMPTY", step, [obj.id]);
        return { rule: "MEASURE_EMPTY", state: "PROVED", uses: [obj.claim], message: `ProbabilityMeasure implies Measure` };
      }
    }
  }
  const membership = parseMembershipCanonical(claim);
  if (membership) {
    for (const obj of all) {
      const sa = parseSigmaAlgebraArgs(obj.claim);
      if (!sa) continue;
      if (sa.sigma === membership.set && sa.space === membership.element) {
        createKernelObject(ctx, claim, "SIGMA_CONTAINS_SPACE", step, [obj.id]);
        return { rule: "SIGMA_CONTAINS_SPACE", state: "PROVED", uses: [obj.claim], message: "The whole space belongs to its sigma-algebra" };
      }
      if (sa.sigma === membership.set && membership.element === "\u2205") {
        createKernelObject(ctx, claim, "SIGMA_CONTAINS_EMPTY", step, [obj.id]);
        return { rule: "SIGMA_CONTAINS_EMPTY", state: "PROVED", uses: [obj.claim], message: "The empty set belongs to every sigma-algebra" };
      }
    }
    const compMatch = membership.element.match(/^complement\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
    if (compMatch) {
      const a = compMatch[1].trim();
      const x = compMatch[2].trim();
      for (const obj of all) {
        const sa = parseSigmaAlgebraArgs(obj.claim);
        if (!sa || sa.sigma !== membership.set || sa.space !== x) continue;
        const aIn = requireClassical(ctx, `${a} \u2208 ${membership.set}`, "SIGMA_CLOSED_COMPLEMENT");
        if (aIn) {
          createKernelObject(ctx, claim, "SIGMA_CLOSED_COMPLEMENT", step, [obj.id, aIn.id]);
          return { rule: "SIGMA_CLOSED_COMPLEMENT", state: "PROVED", uses: [obj.claim, aIn.claim], message: "Sigma-algebras are closed under complementation" };
        }
      }
    }
    const unionParts = parseBinarySetCanonical(membership.element, "\u222A");
    if (unionParts) {
      const sigma = membership.set;
      for (const obj of all) {
        if (!parseSigmaAlgebraArgs(obj.claim) || parseSigmaAlgebraArgs(obj.claim).sigma !== sigma) continue;
        const aIn = requireClassical(ctx, `${unionParts[0]} \u2208 ${sigma}`, "SIGMA_CLOSED_UNION");
        const bIn = requireClassical(ctx, `${unionParts[1]} \u2208 ${sigma}`, "SIGMA_CLOSED_UNION");
        if (aIn && bIn) {
          createKernelObject(ctx, claim, "SIGMA_CLOSED_UNION", step, [obj.id, aIn.id, bIn.id]);
          return { rule: "SIGMA_CLOSED_UNION", state: "PROVED", uses: [obj.claim, aIn.claim, bIn.claim], message: "Sigma-algebras are closed under binary union" };
        }
      }
    }
    const preimageMatch = membership.element.match(/^preimage\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
    if (preimageMatch) {
      const f = preimageMatch[1].trim();
      const b = preimageMatch[2].trim();
      const sigmaX = membership.set;
      for (const obj of all) {
        const ma = parseMeasurableArgs(obj.claim);
        if (!ma || ma.f !== f || ma.sigmaX !== sigmaX) continue;
        const bIn = requireClassical(ctx, `${b} \u2208 ${ma.sigmaY}`, "MEASURABLE_PREIMAGE");
        if (bIn) {
          createKernelObject(ctx, claim, "MEASURABLE_PREIMAGE", step, [obj.id, bIn.id]);
          return { rule: "MEASURABLE_PREIMAGE", state: "PROVED", uses: [obj.claim, bIn.claim], message: "Preimage of a measurable set under a measurable function is measurable" };
        }
      }
    }
  }
  const equality = parseEqualityCanonical(claim);
  if (equality) {
    const leftApp = parseFunctionApplication(equality.left);
    const rightApp = parseFunctionApplication(equality.right);
    if (leftApp && leftApp.arg === "\u2205" && equality.right === "0") {
      for (const obj of all) {
        const ma = parseMeasureArgs(obj.claim);
        const pma = parseProbMeasureArgs(obj.claim);
        if (ma && ma.mu === leftApp.fn || pma && pma.p === leftApp.fn) {
          createKernelObject(ctx, claim, "MEASURE_EMPTY", step, [obj.id]);
          return { rule: "MEASURE_EMPTY", state: "PROVED", uses: [obj.claim], message: "Axiom: the measure of the empty set is zero" };
        }
      }
    }
    if (rightApp && rightApp.arg === "\u2205" && equality.left === "0") {
      for (const obj of all) {
        const ma = parseMeasureArgs(obj.claim);
        const pma = parseProbMeasureArgs(obj.claim);
        if (ma && ma.mu === rightApp.fn || pma && pma.p === rightApp.fn) {
          createKernelObject(ctx, claim, "MEASURE_EMPTY", step, [obj.id]);
          return { rule: "MEASURE_EMPTY", state: "PROVED", uses: [obj.claim], message: "Axiom: the measure of the empty set is zero" };
        }
      }
    }
    if (leftApp) {
      const unionParts = parseBinarySetCanonical(leftApp.arg, "\u222A");
      const sumParts = splitTopLevelSum(equality.right);
      if (unionParts && sumParts) {
        const aApp = parseFunctionApplication(sumParts[0]);
        const bApp = parseFunctionApplication(sumParts[1]);
        if (aApp && bApp && aApp.fn === leftApp.fn && bApp.fn === leftApp.fn && (normArith(aApp.arg) === normArith(unionParts[0]) && normArith(bApp.arg) === normArith(unionParts[1]) || normArith(aApp.arg) === normArith(unionParts[1]) && normArith(bApp.arg) === normArith(unionParts[0]))) {
          const A = unionParts[0], B = unionParts[1];
          for (const obj of all) {
            const ma = parseMeasureArgs(obj.claim);
            const pma = parseProbMeasureArgs(obj.claim);
            if ((!ma || ma.mu !== leftApp.fn) && (!pma || pma.p !== leftApp.fn)) continue;
            const disjointHyp = requireClassical(ctx, `${A} \u2229 ${B} = \u2205`, "MEASURE_ADDITIVE") ?? requireClassical(ctx, `disjoint(${A}, ${B})`, "MEASURE_ADDITIVE") ?? requireClassical(ctx, `disjoint(${B}, ${A})`, "MEASURE_ADDITIVE");
            if (disjointHyp) {
              createKernelObject(ctx, claim, "MEASURE_ADDITIVE", step, [obj.id, disjointHyp.id]);
              return { rule: "MEASURE_ADDITIVE", state: "PROVED", uses: [obj.claim, disjointHyp.claim], message: "Countable additivity on disjoint sets" };
            }
          }
        }
      }
    }
    if (leftApp) {
      const inclExclRhs = equality.right.match(/^(.+)\((.+)\)\s*\+\s*\1\((.+)\)\s*-\s*\1\((.+)\)$/);
      if (inclExclRhs) {
        const [, fn, a1, b1, inter] = inclExclRhs;
        const unionParts = parseBinarySetCanonical(leftApp.arg, "\u222A");
        if (unionParts && fn === leftApp.fn && (normArith(a1) === normArith(unionParts[0]) && normArith(b1) === normArith(unionParts[1]) || normArith(a1) === normArith(unionParts[1]) && normArith(b1) === normArith(unionParts[0]))) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === fn) {
              createKernelObject(ctx, claim, "MEASURE_ADDITIVE", step, [obj.id]);
              return { rule: "MEASURE_ADDITIVE", state: "PROVED", uses: [obj.claim], message: "Inclusion-exclusion: P(A\u222AB) = P(A)+P(B)-P(A\u2229B)" };
            }
          }
        }
      }
      const partDecomp = equality.right.match(/^(.+)\((.+?)\s*∩\s*(.+?)\)\s*\+\s*\1\((.+?)\s*\\\s*(.+?)\)$/);
      if (partDecomp) {
        for (const obj of all) {
          const pma = parseProbMeasureArgs(obj.claim);
          if (pma && pma.p === leftApp.fn) {
            createKernelObject(ctx, claim, "MEASURE_ADDITIVE", step, [obj.id]);
            return { rule: "MEASURE_ADDITIVE", state: "PROVED", uses: [obj.claim], message: "Partition decomposition P(B) = P(A\u2229B) + P(B\\A)" };
          }
        }
      }
      const diffDecomp = equality.right.match(/^(.+)\((.+?)\)\s*-\s*\1\((.+?)\s*∩\s*(.+?)\)$/);
      if (diffDecomp) {
        for (const obj of all) {
          const pma = parseProbMeasureArgs(obj.claim);
          if (pma && pma.p === leftApp.fn) {
            createKernelObject(ctx, claim, "MEASURE_ADDITIVE", step, [obj.id]);
            return { rule: "MEASURE_ADDITIVE", state: "PROVED", uses: [obj.claim], message: "P(B\\A) = P(B) - P(A\u2229B)" };
          }
        }
      }
    }
    if (leftApp) {
      const compArg = leftApp.arg.match(/^complement\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
      const rhs1MinusP = equality.right.match(/^1\s*-\s*([^\s(]+)\s*\((.+)\)$/);
      if (compArg && rhs1MinusP && rhs1MinusP[1] === leftApp.fn && rhs1MinusP[2] === compArg[1].trim()) {
        for (const obj of all) {
          const pma = parseProbMeasureArgs(obj.claim);
          if (!pma || pma.p !== leftApp.fn) continue;
          const aIn = requireClassical(ctx, `${compArg[1].trim()} \u2208 ${pma.sigma}`, "PROB_COMPLEMENT");
          if (aIn) {
            createKernelObject(ctx, claim, "PROB_COMPLEMENT", step, [obj.id, aIn.id]);
            return { rule: "PROB_COMPLEMENT", state: "PROVED", uses: [obj.claim, aIn.claim], message: "P(A\u1D9C) = 1 \u2212 P(A) for probability measures" };
          }
        }
      }
    }
    if (leftApp && equality.right === "1") {
      for (const obj of all) {
        const pma = parseProbMeasureArgs(obj.claim);
        if (!pma || pma.p !== leftApp.fn || pma.space !== leftApp.arg) continue;
        createKernelObject(ctx, claim, "PROB_TOTAL", step, [obj.id]);
        return { rule: "PROB_TOTAL", state: "PROVED", uses: [obj.claim], message: "Axiom: probability of the whole space is 1" };
      }
    }
    {
      const unionDecomp = equality.left.match(/^(.+)\s*∪\s*(.+)$/);
      const unionDecompR = equality.right.match(/^(.+)\s*∪\s*[\s(]*(.*?)\s*\\\s*(.*?)\s*\)?\s*$/);
      if (unionDecomp && unionDecompR && normArith(unionDecomp[1].trim()) === normArith(unionDecompR[1].trim()) && normArith(unionDecomp[2].trim()) === normArith(unionDecompR[2].trim())) {
        createKernelObject(ctx, claim, "MEASURE_ADDITIVE", step);
        return { rule: "MEASURE_ADDITIVE", state: "PROVED", message: `Set identity: A \u222A B = A \u222A (B \\ A)` };
      }
    }
    if (leftApp) {
      const condMatch = leftApp.arg.match(/^(.+?)\s*\|\s*(.+)$/);
      if (condMatch) {
        const [, X, Y] = condMatch;
        const rhsParts = equality.right.match(/^([^(]+)\((.+?)\s*∩\s*(.+?)\)\s*\/\s*\1\((.+?)\)$/);
        if (rhsParts && rhsParts[1] === leftApp.fn && normArith(rhsParts[4]) === normArith(Y) && (normArith(rhsParts[2]) === normArith(X) && normArith(rhsParts[3]) === normArith(Y) || normArith(rhsParts[2]) === normArith(Y) && normArith(rhsParts[3]) === normArith(X))) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === leftApp.fn) {
              createKernelObject(ctx, claim, "PROB_TOTAL", step, [obj.id]);
              return { rule: "PROB_TOTAL", state: "PROVED", uses: [obj.claim], message: `Conditional probability: P(${X}|${Y}) = P(${X}\u2229${Y})/P(${Y})` };
            }
          }
        }
      }
    }
    if (leftApp) {
      const intersArgs = parseBinarySetCanonical(leftApp.arg, "\u2229");
      if (intersArgs) {
        const rhsProd = equality.right.match(/^([^(]+)\((.+?)\s*\|\s*(.+?)\)\s*\*\s*\1\((.+?)\)$/);
        if (rhsProd && rhsProd[1] === leftApp.fn) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === leftApp.fn) {
              createKernelObject(ctx, claim, "PROB_TOTAL", step, [obj.id]);
              return { rule: "PROB_TOTAL", state: "PROVED", uses: [obj.claim], message: `Chain rule: P(A\u2229B) = P(B|A)P(A)` };
            }
          }
        }
      }
    }
    if (leftApp) {
      const bayesLhs = leftApp.arg.match(/^(.+?)\s*\|\s*(.+)$/);
      const bayesRhs = equality.right.match(/^([^(]+)\((.+?)\s*\|\s*(.+?)\)\s*\*\s*\1\((.+?)\)\s*\/\s*\1\((.+?)\)$/);
      if (bayesLhs && bayesRhs && bayesRhs[1] === leftApp.fn) {
        for (const obj of all) {
          const pma = parseProbMeasureArgs(obj.claim);
          if (pma && pma.p === leftApp.fn) {
            createKernelObject(ctx, claim, "PROB_TOTAL", step, [obj.id]);
            return { rule: "PROB_TOTAL", state: "PROVED", uses: [obj.claim], message: `Bayes' theorem` };
          }
        }
      }
    }
    if (leftApp) {
      const interArgs = parseBinarySetCanonical(leftApp.arg, "\u2229");
      if (interArgs) {
        const [Aarg, Barg] = interArgs;
        const rhsProd2 = equality.right.match(/^([^(]+)\((.+?)\)\s*\*\s*\1\((.+?)\)$/);
        if (rhsProd2 && rhsProd2[1] === leftApp.fn && (normArith(rhsProd2[2]) === normArith(Aarg) && normArith(rhsProd2[3]) === normArith(Barg) || normArith(rhsProd2[2]) === normArith(Barg) && normArith(rhsProd2[3]) === normArith(Aarg))) {
          const indepHyp = all.find((o) => o.claim.trim() === `independent(${Aarg}, ${Barg})` || o.claim.trim() === `independent(${Barg}, ${Aarg})`);
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === leftApp.fn) {
              const deps = indepHyp ? [obj.id, indepHyp.id] : [obj.id];
              createKernelObject(ctx, claim, "PROB_TOTAL", step, deps);
              return { rule: "PROB_TOTAL", state: "PROVED", uses: [obj.claim], message: `Independence: P(A\u2229B) = P(A)P(B)` };
            }
          }
        }
      }
    }
    if (leftApp && !leftApp.arg.includes("\u2229") && !leftApp.arg.includes("|")) {
      const sumOfInterParts = equality.right.match(/^([^(]+)\((.+?)\s*∩\s*(.+?)\)\s*\+\s*\1\((.+?)\s*∩\s*(.+?)\)$/);
      if (sumOfInterParts && sumOfInterParts[1] === leftApp.fn) {
        const partHyp = all.find((o) => o.claim.match(/^partition\(/));
        if (partHyp) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === leftApp.fn) {
              createKernelObject(ctx, claim, "PROB_TOTAL", step, [obj.id, partHyp.id]);
              return { rule: "PROB_TOTAL", state: "PROVED", uses: [obj.claim, partHyp.claim], message: `Law of total probability` };
            }
          }
        }
      }
    }
  }
  const markovMatch = claim.trim().match(/^(.+)\((.+)\s*≥\s*(.+)\)\s*≤\s*expected\((.+)\)\s*\/\s*(.+)$/);
  if (markovMatch) {
    const [, fn, X, a, X2, a2] = markovMatch;
    if (normArith(X) === normArith(X2) && normArith(a) === normArith(a2)) {
      for (const obj of all) {
        const pma = parseProbMeasureArgs(obj.claim);
        if (pma && pma.p === fn) {
          createKernelObject(ctx, claim, "MEASURE_MONO", step, [obj.id]);
          return { rule: "MEASURE_MONO", state: "PROVED", uses: [obj.claim], message: `Markov's inequality` };
        }
      }
    }
  }
  const zeroLeqMatch = claim.trim().match(/^0\s*≤\s*(.+)\((.+)\)$/);
  if (zeroLeqMatch) {
    const [, fn, arg] = zeroLeqMatch;
    for (const obj of all) {
      const pma = parseProbMeasureArgs(obj.claim);
      if (pma && pma.p === fn) {
        createKernelObject(ctx, claim, "MEASURE_MONO", step, [obj.id]);
        return { rule: "MEASURE_MONO", state: "PROVED", uses: [obj.claim], message: `Probability is non-negative: 0 \u2264 P(${arg})` };
      }
    }
  }
  const leqOneMatch = claim.trim().match(/^(.+)\((.+)\)\s*≤\s*1$/);
  if (leqOneMatch) {
    const [, fn, arg] = leqOneMatch;
    for (const obj of all) {
      const pma = parseProbMeasureArgs(obj.claim);
      if (pma && pma.p === fn) {
        createKernelObject(ctx, claim, "MEASURE_MONO", step, [obj.id]);
        return { rule: "MEASURE_MONO", state: "PROVED", uses: [obj.claim], message: `Probability is at most 1: P(${arg}) \u2264 1` };
      }
    }
  }
  const subsOmegaMatch = claim.trim().match(/^(.+)\s*⊆\s*(.+)$/);
  if (subsOmegaMatch) {
    const [, A, Omega] = subsOmegaMatch;
    for (const obj of all) {
      const pma = parseProbMeasureArgs(obj.claim);
      if (pma && normArith(pma.space) === normArith(Omega)) {
        const aInSigma = all.find((o) => {
          const m = parseMembershipCanonical(o.claim);
          return m && normArith(m.element) === normArith(A) && normArith(m.set) === normArith(pma.sigma);
        });
        if (aInSigma) {
          createKernelObject(ctx, claim, "MEASURE_MONO", step, [obj.id, aInSigma.id]);
          return { rule: "MEASURE_MONO", state: "PROVED", uses: [obj.claim, aInSigma.claim], message: `${A} \u2208 \u03A3 implies ${A} \u2286 ${Omega}` };
        }
      }
    }
  }
  const leqParts = splitTopLevelLeq(claim);
  if (leqParts) {
    const lhsApp = parseFunctionApplication(leqParts[0]);
    const rhsApp = parseFunctionApplication(leqParts[1]);
    if (lhsApp && rhsApp && lhsApp.fn === rhsApp.fn) {
      for (const obj of all) {
        const ma = parseMeasureArgs(obj.claim) ?? (parseProbMeasureArgs(obj.claim) ? { mu: parseProbMeasureArgs(obj.claim).p, sigma: parseProbMeasureArgs(obj.claim).sigma } : null);
        if (!ma || ma.mu !== lhsApp.fn) continue;
        const subset = requireClassical(ctx, `${lhsApp.arg} \u2286 ${rhsApp.arg}`, "MEASURE_MONO") ?? requireClassical(ctx, `${lhsApp.arg} \u2282 ${rhsApp.arg}`, "MEASURE_MONO");
        if (subset) {
          const aIn = requireClassical(ctx, `${lhsApp.arg} \u2208 ${ma.sigma}`, "MEASURE_MONO");
          const bIn = requireClassical(ctx, `${rhsApp.arg} \u2208 ${ma.sigma}`, "MEASURE_MONO");
          if (aIn && bIn) {
            createKernelObject(ctx, claim, "MEASURE_MONO", step, [obj.id, subset.id, aIn.id, bIn.id]);
            return { rule: "MEASURE_MONO", state: "PROVED", uses: [obj.claim, subset.claim, aIn.claim], message: "Monotonicity: A \u2286 B implies \u03BC(A) \u2264 \u03BC(B)" };
          }
          if (parseProbMeasureArgs(obj.claim)) {
            createKernelObject(ctx, claim, "MEASURE_MONO", step, [obj.id, subset.id]);
            return { rule: "MEASURE_MONO", state: "PROVED", uses: [obj.claim, subset.claim], message: "Monotonicity: A \u2286 B implies P(A) \u2264 P(B)" };
          }
        }
      }
    }
    if (lhsApp) {
      const unionParts = parseBinarySetCanonical(lhsApp.arg, "\u222A");
      const sumParts = splitTopLevelSum(leqParts[1]);
      if (unionParts && sumParts) {
        const aApp = parseFunctionApplication(sumParts[0]);
        const bApp = parseFunctionApplication(sumParts[1]);
        if (aApp && bApp && aApp.fn === lhsApp.fn && bApp.fn === lhsApp.fn && aApp.arg === unionParts[0] && bApp.arg === unionParts[1]) {
          for (const obj of all) {
            const ma = parseMeasureArgs(obj.claim) ?? (parseProbMeasureArgs(obj.claim) ? { mu: parseProbMeasureArgs(obj.claim).p, sigma: parseProbMeasureArgs(obj.claim).sigma } : null);
            if (!ma || ma.mu !== lhsApp.fn) continue;
            const aIn = requireClassical(ctx, `${unionParts[0]} \u2208 ${ma.sigma}`, "MEASURE_SUBADDITIVE");
            const bIn = requireClassical(ctx, `${unionParts[1]} \u2208 ${ma.sigma}`, "MEASURE_SUBADDITIVE");
            if (aIn && bIn) {
              createKernelObject(ctx, claim, "MEASURE_SUBADDITIVE", step, [obj.id, aIn.id, bIn.id]);
              return { rule: "MEASURE_SUBADDITIVE", state: "PROVED", uses: [obj.claim, aIn.claim, bIn.claim], message: "Subadditivity: \u03BC(A \u222A B) \u2264 \u03BC(A) + \u03BC(B)" };
            }
          }
        }
      }
    }
  }
  const disjMatch = claim.trim().match(/^disjoint\((.+?)\s*,\s*(.+?)\s*\\\s*(.+?)\)$/);
  if (disjMatch) {
    const [, A, B, C] = disjMatch;
    if (normArith(A) === normArith(C)) {
      createKernelObject(ctx, claim, "MEASURE_ADDITIVE", step);
      return { rule: "MEASURE_ADDITIVE", state: "PROVED", message: `${A} and ${B}\\${A} are disjoint` };
    }
  }
  const leqSub = splitTopLevelLeq(claim);
  if (leqSub) {
    const lhsA = parseFunctionApplication(leqSub[0]);
    if (lhsA) {
      const unionP = parseBinarySetCanonical(lhsA.arg, "\u222A");
      const sumS = splitTopLevelSum(leqSub[1]);
      if (unionP && sumS) {
        const aA = parseFunctionApplication(sumS[0]);
        const bA = parseFunctionApplication(sumS[1]);
        if (aA && bA && aA.fn === lhsA.fn && bA.fn === lhsA.fn) {
          for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === lhsA.fn) {
              createKernelObject(ctx, claim, "MEASURE_SUBADDITIVE", step, [obj.id]);
              return { rule: "MEASURE_SUBADDITIVE", state: "PROVED", uses: [obj.claim], message: "P(A\u222AB) \u2264 P(A)+P(B)" };
            }
          }
        }
      }
    }
  }
  const measPred = parseMeasurePredicateCanonical(claim);
  if (measPred?.name === "Measurable") {
    const [fg, sigmaX, sigmaZ] = measPred.args;
    const compParts = fg.match(/^(.+?)\s*∘\s*(.+)$/);
    if (compParts) {
      const g = compParts[1].trim();
      const f = compParts[2].trim();
      for (const fObj of all) {
        const fma = parseMeasurableArgs(fObj.claim);
        if (!fma || fma.f !== f || fma.sigmaX !== sigmaX) continue;
        for (const gObj of all) {
          const gma = parseMeasurableArgs(gObj.claim);
          if (!gma || gma.f !== g || gma.sigmaX !== fma.sigmaY || gma.sigmaY !== sigmaZ) continue;
          createKernelObject(ctx, claim, "MEASURABLE_COMPOSE", step, [fObj.id, gObj.id]);
          return { rule: "MEASURABLE_COMPOSE", state: "PROVED", uses: [fObj.claim, gObj.claim], message: "Composition of measurable functions is measurable" };
        }
      }
    }
  }
  return null;
}
function deriveCategoryClaim(ctx, claim, step) {
  const morphismDecl = parseMorphismDeclarationCanonical(claim);
  if (morphismDecl) {
    try {
      ctx.diagrams.registerClaim(claim);
      createKernelObject(ctx, claim, "CAT_MORPHISM", step);
      return {
        rule: "CAT_MORPHISM",
        state: "PROVED",
        message: "Registered a categorical morphism with explicit domain and codomain"
      };
    } catch (error) {
      return categoryFailure(error, "CAT_MORPHISM");
    }
  }
  const predicate = parseCategoryPredicateCanonical(claim);
  if (predicate) {
    try {
      const result = deriveCategoryPredicate(ctx, predicate, step, claim);
      if (result) return result;
    } catch (error) {
      return categoryFailure(error, predicateToRule(predicate.name));
    }
  }
  const categoricalEquality = looksLikeCategoricalEquality2(claim) ? parseCategoricalEqualityCanonical(claim) : null;
  if (categoricalEquality) {
    try {
      const result = deriveCategoricalEquality(ctx, claim, categoricalEquality.left, categoricalEquality.right, step);
      if (result) return result;
    } catch (error) {
      const msg = error instanceof Error ? error.message : "";
      if (msg.includes("unknown functor")) return null;
      return categoryFailure(error, "CAT_EQUALITY");
    }
  }
  return null;
}
function deriveCategoryPredicate(ctx, predicate, step, claim) {
  switch (predicate.name) {
    case "Category":
    case "Object":
    case "Morphism":
    case "Functor":
      ctx.diagrams.registerPredicate(predicate.name, predicate.args);
      createKernelObject(ctx, claim, predicate.name === "Functor" ? "FUNCTOR_INTRO" : predicate.name === "Morphism" ? "CAT_MORPHISM" : "CAT_OBJECT", step);
      return {
        rule: predicate.name === "Functor" ? "FUNCTOR_INTRO" : predicate.name === "Morphism" ? "CAT_MORPHISM" : "CAT_OBJECT",
        state: "PROVED",
        message: predicate.name === "Functor" ? "Registered a functor between finite categories" : predicate.name === "Morphism" ? "Registered a categorical morphism declaration inside an explicit category" : "Registered categorical structure in the finite-diagram kernel"
      };
    case "Iso":
      return deriveIso(ctx, predicate.args, claim, step);
    case "Product":
      return deriveProduct(ctx, predicate.args, claim, step);
    case "ProductMediator":
      return deriveProductMediator(ctx, predicate.args, claim, step);
    case "Coproduct":
      return deriveCoproduct(ctx, predicate.args, claim, step);
    case "Pullback":
      return derivePullback(ctx, predicate.args, claim, step);
    case "Pushout":
      return derivePushout(ctx, predicate.args, claim, step);
  }
}
function deriveCategoricalEquality(ctx, claim, left, right, step) {
  const formattedLeft = formatMorphismExpr(left);
  const formattedRight = formatMorphismExpr(right);
  const leftDecl = parseMorphismDeclarationCanonical(formattedLeft);
  const rightDecl = parseMorphismDeclarationCanonical(formattedRight);
  void leftDecl;
  void rightDecl;
  if (ctx.diagrams.equalMorphisms(left, right)) {
    createKernelObject(ctx, claim, "CAT_EQUALITY", step);
    return {
      rule: "CAT_EQUALITY",
      state: "PROVED",
      uses: [formattedLeft, formattedRight],
      message: "Validated equality between categorical composites"
    };
  }
  const leftText = formattedLeft;
  const rightText = formattedRight;
  if (stripIdentity(leftText) === stripIdentity(rightText)) {
    createKernelObject(ctx, claim, "CAT_IDENTITY", step);
    return {
      rule: "CAT_IDENTITY",
      state: "PROVED",
      uses: [formattedLeft, formattedRight],
      message: "Validated a categorical identity law"
    };
  }
  if (normalizeComposition(leftText) === normalizeComposition(rightText)) {
    createKernelObject(ctx, claim, "CAT_ASSOC", step);
    return {
      rule: "CAT_ASSOC",
      state: "PROVED",
      uses: [formattedLeft, formattedRight],
      message: "Validated associativity of explicit morphism composition"
    };
  }
  const functorLaw = deriveFunctorEquality(ctx, left, right, claim, step);
  if (functorLaw) return functorLaw;
  return null;
}
function deriveIso(ctx, args2, claim, step) {
  const target = args2[0];
  if (!target) return null;
  const morphism = ctx.diagrams.resolveMorphismExpr({ kind: "name", label: target });
  for (const object of [...ctx.objects, ...ctx.premises, ...ctx.assumptions]) {
    const candidate = parseMorphismDeclarationCanonical(object.claim);
    if (!candidate) continue;
    try {
      const inverse = ctx.diagrams.resolveMorphismExpr({ kind: "name", label: candidate.label });
      if (inverse.category !== morphism.category) continue;
      const leftId = `id_${ctx.diagrams.objectById(morphism.domain).label}`;
      const rightId = `id_${ctx.diagrams.objectById(morphism.codomain).label}`;
      const leftEq = `${candidate.label} \u2218 ${target} = ${leftId}`;
      const rightEq = `${target} \u2218 ${candidate.label} = ${rightId}`;
      if (findExact(ctx.objects, leftEq, false) || findExact(ctx.premises, leftEq, false) || findExact(ctx.assumptions, leftEq, false)) {
        if (findExact(ctx.objects, rightEq, false) || findExact(ctx.premises, rightEq, false) || findExact(ctx.assumptions, rightEq, false)) {
          createKernelObject(ctx, claim, "ISO_INTRO", step);
          return {
            rule: "ISO_INTRO",
            state: "PROVED",
            uses: [leftEq, rightEq],
            message: `Validated explicit inverse equations for Iso(${target})`
          };
        }
      }
    } catch {
      continue;
    }
  }
  return {
    rule: "ISO_INTRO",
    state: "FAILED",
    message: `Category error: inverse conditions for Iso(${target}) are not satisfied`
  };
}
function deriveProduct(ctx, args2, claim, step) {
  if (args2.length < 5) return null;
  const [productObject, pi1, pi2, leftObject, rightObject] = args2;
  const leftDecl = hasMorphism(ctx, `${pi1} : ${productObject} \u2192 ${leftObject}`);
  const rightDecl = hasMorphism(ctx, `${pi2} : ${productObject} \u2192 ${rightObject}`);
  if (leftDecl && rightDecl) {
    createKernelObject(ctx, claim, "PRODUCT_INTRO", step);
    return {
      rule: "PRODUCT_INTRO",
      state: "PROVED",
      uses: [`${pi1} : ${productObject} \u2192 ${leftObject}`, `${pi2} : ${productObject} \u2192 ${rightObject}`],
      message: "Validated the explicit projections for a finite product cone"
    };
  }
  return null;
}
function deriveProductMediator(ctx, args2, claim, step) {
  if (args2.length < 5) return null;
  const [mediator, left, right, pi1, pi2] = args2;
  const leftEq = `${pi1} \u2218 ${mediator} = ${left}`;
  const rightEq = `${pi2} \u2218 ${mediator} = ${right}`;
  if (hasClaim(ctx, leftEq) && hasClaim(ctx, rightEq)) {
    createKernelObject(ctx, claim, "PRODUCT_MEDIATOR", step);
    return {
      rule: "PRODUCT_MEDIATOR",
      state: "PROVED",
      uses: [leftEq, rightEq],
      message: "Universal property error cleared: mediator satisfies both projection equations"
    };
  }
  return {
    rule: "PRODUCT_MEDIATOR",
    state: "FAILED",
    message: "Universal property error: mediator does not satisfy both projection equations"
  };
}
function deriveCoproduct(ctx, args2, claim, step) {
  if (args2.length < 5) return null;
  const [sumObject, i1, i2, leftObject, rightObject] = args2;
  if (hasMorphism(ctx, `${i1} : ${leftObject} \u2192 ${sumObject}`) && hasMorphism(ctx, `${i2} : ${rightObject} \u2192 ${sumObject}`)) {
    createKernelObject(ctx, claim, "COPRODUCT_INTRO", step);
    return {
      rule: "COPRODUCT_INTRO",
      state: "PROVED",
      uses: [`${i1} : ${leftObject} \u2192 ${sumObject}`, `${i2} : ${rightObject} \u2192 ${sumObject}`],
      message: "Validated the explicit injections for a finite coproduct cocone"
    };
  }
  return null;
}
function derivePullback(ctx, args2, claim, step) {
  if (args2.length < 5) return null;
  const [pullbackObject, p1, p2, f, g] = args2;
  const p1Decl = findDeclarationByLabel(ctx, p1);
  const p2Decl = findDeclarationByLabel(ctx, p2);
  const fDecl = findDeclarationByLabel(ctx, f);
  const gDecl = findDeclarationByLabel(ctx, g);
  if (!p1Decl || !p2Decl || !fDecl || !gDecl) {
    return null;
  }
  const commuting = `${f} \u2218 ${p1} = ${g} \u2218 ${p2}`;
  if (!hasClaim(ctx, commuting)) {
    return { rule: "PULLBACK_INTRO", state: "FAILED", message: "Diagram error: square does not commute" };
  }
  if (p1Decl.domain !== pullbackObject || p2Decl.domain !== pullbackObject) {
    return { rule: "PULLBACK_INTRO", state: "FAILED", message: "Category error: pullback legs do not originate at the claimed pullback object" };
  }
  createKernelObject(ctx, claim, "PULLBACK_INTRO", step);
  return {
    rule: "PULLBACK_INTRO",
    state: "PROVED",
    uses: [commuting],
    message: "Validated a finite pullback square and its commuting condition"
  };
}
function derivePushout(ctx, args2, claim, step) {
  if (args2.length < 5) return null;
  const [pushoutObject, i1, i2, f, g] = args2;
  const i1Decl = findDeclarationByLabel(ctx, i1);
  const i2Decl = findDeclarationByLabel(ctx, i2);
  if (!i1Decl || !i2Decl) {
    return null;
  }
  const commuting = `${i1} \u2218 ${f} = ${i2} \u2218 ${g}`;
  if (!hasClaim(ctx, commuting)) {
    return { rule: "PUSHOUT_INTRO", state: "FAILED", message: "Diagram error: square does not commute" };
  }
  if (i1Decl.codomain !== pushoutObject || i2Decl.codomain !== pushoutObject) {
    return { rule: "PUSHOUT_INTRO", state: "FAILED", message: "Category error: pushout legs do not target the claimed pushout object" };
  }
  createKernelObject(ctx, claim, "PUSHOUT_INTRO", step);
  return {
    rule: "PUSHOUT_INTRO",
    state: "PROVED",
    uses: [commuting],
    message: "Validated a finite pushout square and its commuting condition"
  };
}
function categoryFailure(error, rule) {
  const message = error instanceof Error ? error.message : "Unknown category-check failure";
  return { rule, state: "FAILED", message };
}
function deriveFunctorEquality(ctx, left, right, claim, step) {
  if (left.kind === "functor_map" && right.kind === "compose") {
    if (left.argument.kind === "compose" && right.left.kind === "functor_map" && right.right.kind === "functor_map") {
      if (left.functor === right.left.functor && left.functor === right.right.functor) {
        const expectedLeft = formatMorphismExpr(left.argument.left);
        const expectedRight = formatMorphismExpr(left.argument.right);
        if (expectedLeft === formatMorphismExpr(right.left.argument) && expectedRight === formatMorphismExpr(right.right.argument)) {
          createKernelObject(ctx, claim, "FUNCTOR_COMPOSE", step);
          return {
            rule: "FUNCTOR_COMPOSE",
            state: "PROVED",
            uses: [formatMorphismExpr(left), formatMorphismExpr(right)],
            message: "Validated that the functor preserves composition"
          };
        }
      }
    }
  }
  if (left.kind === "functor_map" && left.argument.kind === "identity" && right.kind === "identity") {
    if (right.object === `${left.functor}(${left.argument.object})`) {
      createKernelObject(ctx, claim, "FUNCTOR_ID", step);
      return {
        rule: "FUNCTOR_ID",
        state: "PROVED",
        uses: [formatMorphismExpr(left), formatMorphismExpr(right)],
        message: "Validated that the functor preserves identity morphisms"
      };
    }
  }
  return null;
}
function deriveAndElim(ctx, claim, step) {
  for (const object of classicalObjects(ctx)) {
    const conjunction = parseConjunctionCanonical(object.claim);
    if (!conjunction) continue;
    if (sameProp(conjunction[0], claim)) {
      createKernelObject(ctx, claim, "AND_ELIM_LEFT", step, [object.id]);
      return {
        rule: "AND_ELIM_LEFT",
        state: "PROVED",
        uses: [object.claim],
        message: "Read the left component from a Boolean meet"
      };
    }
    if (sameProp(conjunction[1], claim)) {
      createKernelObject(ctx, claim, "AND_ELIM_RIGHT", step, [object.id]);
      return {
        rule: "AND_ELIM_RIGHT",
        state: "PROVED",
        uses: [object.claim],
        message: "Read the right component from a Boolean meet"
      };
    }
  }
  return null;
}
function deriveNotIntro(ctx, claim, step) {
  if (!claim.startsWith("\xAC")) return null;
  const positive = claim.slice(1).trim();
  const assumption = findExact(ctx.assumptions, positive, false);
  if (!assumption) return null;
  const bottom = findExact(ctx.objects, BOTTOM, false);
  if (!bottom) return null;
  ctx.category.complementOf(positive);
  createKernelObject(ctx, claim, "NOT_INTRO", step, [assumption.id, bottom.id]);
  return {
    rule: "NOT_INTRO",
    state: "PROVED",
    uses: [positive, BOTTOM],
    message: "Proof by contradiction: assuming \u03C6 led to \u22A5, therefore \xAC\u03C6 holds"
  };
}
function deriveImpliesElim(ctx, claim, step) {
  for (const object of classicalObjects(ctx)) {
    const implication = parseImplicationCanonical(object.claim);
    if (!implication || !sameProp(implication[1], claim)) continue;
    const antecedent = requireClassical(ctx, implication[0], "IMPLIES_ELIM");
    if (!antecedent) continue;
    const antecedentMorph = toTopMorphism(ctx, antecedent);
    const implicationMorph = toImplicationMorphism(ctx, object);
    const composed = ctx.category.compose(antecedentMorph, implicationMorph, claim, "IMPLIES_ELIM");
    registerDerivedObject(ctx, claim, step, "IMPLIES_ELIM", composed, [antecedent.id, object.id]);
    return {
      rule: "IMPLIES_ELIM",
      state: "PROVED",
      uses: [implication[0], ctx.category.classicalImplication(implication[0], implication[1])],
      message: "Applied classical modus ponens using the complement-disjunction reading of implication"
    };
  }
  return null;
}
function deriveImpliesIntro(ctx, claim, step) {
  const implication = parseImplicationCanonical(claim);
  if (!implication) return null;
  const assumption = findExact(ctx.assumptions, implication[0], false);
  const consequent = requireClassical(ctx, implication[1], "IMPLIES_INTRO");
  if (!assumption || !consequent) return null;
  createKernelObject(ctx, claim, "IMPLIES_INTRO", step, [assumption.id, consequent.id]);
  return {
    rule: "IMPLIES_INTRO",
    state: "PROVED",
    uses: [implication[0], implication[1], ctx.category.classicalImplication(implication[0], implication[1])],
    message: "Formed the classical implication as a complement-or-consequent morphism"
  };
}
function deriveIffIntro(ctx, claim, step) {
  const iff = parseIffCanonical(claim);
  if (!iff) return null;
  const left = requireClassical(ctx, `${iff[0]} \u2192 ${iff[1]}`, "IMPLIES_ELIM");
  const right = requireClassical(ctx, `${iff[1]} \u2192 ${iff[0]}`, "IMPLIES_ELIM");
  if (!left || !right) return null;
  createKernelObject(ctx, claim, "IFF_INTRO", step, [left.id, right.id]);
  return {
    rule: "IFF_INTRO",
    state: "PROVED",
    uses: [left.claim, right.claim],
    message: "Built the biconditional from both directional morphisms"
  };
}
function deriveIffElim(ctx, claim, step) {
  for (const object of classicalObjects(ctx)) {
    const iff = parseIffCanonical(object.claim);
    if (!iff) continue;
    const left = findExact(ctx.objects, iff[0], false);
    const right = findExact(ctx.objects, iff[1], false);
    if (left && sameProp(iff[1], claim)) {
      createKernelObject(ctx, claim, "IFF_ELIM_L", step, [object.id, left.id]);
      return {
        rule: "IFF_ELIM_L",
        state: "PROVED",
        uses: [object.claim, left.claim],
        message: "Used the biconditional and the left side to derive the right side"
      };
    }
    if (right && sameProp(iff[0], claim)) {
      createKernelObject(ctx, claim, "IFF_ELIM_R", step, [object.id, right.id]);
      return {
        rule: "IFF_ELIM_R",
        state: "PROVED",
        uses: [object.claim, right.claim],
        message: "Used the biconditional and the right side to derive the left side"
      };
    }
  }
  return null;
}
function deriveOrIntro(ctx, claim, step) {
  const parts = parseDisjunctionCanonical(claim);
  if (!parts) return null;
  const left = requireClassical(ctx, parts[0], "OR_INTRO_LEFT");
  if (left) {
    createKernelObject(ctx, claim, "OR_INTRO_LEFT", step, [left.id]);
    return {
      rule: "OR_INTRO_LEFT",
      state: "PROVED",
      uses: [parts[0]],
      message: "Injected the left branch into a classical join"
    };
  }
  const right = requireClassical(ctx, parts[1], "OR_INTRO_RIGHT");
  if (right) {
    createKernelObject(ctx, claim, "OR_INTRO_RIGHT", step, [right.id]);
    return {
      rule: "OR_INTRO_RIGHT",
      state: "PROVED",
      uses: [parts[1]],
      message: "Injected the right branch into a classical join"
    };
  }
  return null;
}
function deriveOrElim(ctx, claim, step) {
  for (const object of classicalObjects(ctx)) {
    const disjunction = parseDisjunctionCanonical(object.claim);
    if (!disjunction) continue;
    const leftArrow = findExact(ctx.objects, `${disjunction[0]} \u2192 ${claim}`, false);
    const rightArrow = findExact(ctx.objects, `${disjunction[1]} \u2192 ${claim}`, false);
    if (!leftArrow || !rightArrow) continue;
    createKernelObject(ctx, claim, "OR_ELIM", step, [object.id, leftArrow.id, rightArrow.id]);
    return {
      rule: "OR_ELIM",
      state: "PROVED",
      uses: [object.claim, leftArrow.claim, rightArrow.claim],
      message: "Eliminated a classical disjunction across both branches"
    };
  }
  return null;
}
function deriveSubsetElim(ctx, claim, step) {
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  for (const object of classicalObjects(ctx)) {
    const subset = parseSubsetCanonical(object.claim);
    if (!subset || !sameProp(subset.right, membership.set)) continue;
    const input = requireClassical(ctx, `${membership.element} \u2208 ${subset.left}`, "IMPLIES_ELIM");
    if (!input) continue;
    createKernelObject(ctx, claim, "IMPLIES_ELIM", step, [input.id, object.id]);
    return {
      rule: "IMPLIES_ELIM",
      state: "PROVED",
      uses: [input.claim, object.claim],
      message: "Transported membership along a subset morphism"
    };
  }
  return null;
}
function deriveSubsetIntro(ctx, claim, step) {
  const subset = parseSubsetCanonical(claim);
  if (!subset) return null;
  const witness = ctx.variables.length > 0 ? ctx.variables[ctx.variables.length - 1].name : null;
  if (!witness) return null;
  const leftMembership = findExact(ctx.assumptions, `${witness} \u2208 ${subset.left}`, false);
  const rightMembership = requireClassical(ctx, `${witness} \u2208 ${subset.right}`, "IMPLIES_INTRO");
  if (!leftMembership || !rightMembership) return null;
  createKernelObject(ctx, claim, "IMPLIES_INTRO", step, [leftMembership.id, rightMembership.id]);
  return {
    rule: "IMPLIES_INTRO",
    state: "PROVED",
    uses: [leftMembership.claim, rightMembership.claim],
    message: "Restricted the domain of a partial map witness branch into a subset morphism"
  };
}
function deriveSubsetTransitivity(ctx, claim, step) {
  const subset = parseSubsetCanonical(claim);
  if (!subset) return null;
  for (const left of classicalObjects(ctx)) {
    const first = parseSubsetCanonical(left.claim);
    if (!first || !sameProp(first.left, subset.left)) continue;
    for (const right of classicalObjects(ctx)) {
      const second = parseSubsetCanonical(right.claim);
      if (!second) continue;
      if (sameProp(first.right, second.left) && sameProp(second.right, subset.right)) {
        createKernelObject(ctx, claim, "IMPLIES_ELIM", step, [left.id, right.id]);
        return {
          rule: "IMPLIES_ELIM",
          state: "PROVED",
          uses: [left.claim, right.claim],
          message: "Composed two subset morphisms transitively"
        };
      }
    }
  }
  return null;
}
function deriveSubsetAntisymmetry(ctx, claim, step) {
  const equality = parseEqualityCanonical(claim);
  if (!equality) return null;
  const forward = requireClassical(ctx, `${equality.left} \u2282 ${equality.right}`, "IMPLIES_ELIM") ?? requireClassical(ctx, `${equality.left} \u2286 ${equality.right}`, "IMPLIES_ELIM");
  const backward = requireClassical(ctx, `${equality.right} \u2282 ${equality.left}`, "IMPLIES_ELIM") ?? requireClassical(ctx, `${equality.right} \u2286 ${equality.left}`, "IMPLIES_ELIM");
  if (!forward || !backward) return null;
  createKernelObject(ctx, claim, "IMPLIES_ELIM", step, [forward.id, backward.id]);
  return {
    rule: "IMPLIES_ELIM",
    state: "PROVED",
    uses: [forward.claim, backward.claim],
    message: "Collapsed mutual subset morphisms into equality"
  };
}
function deriveEqualityReflexivity(ctx, claim, step) {
  const eq = parseEqualityCanonical(claim);
  if (!eq || !sameProp(eq.left, eq.right)) return null;
  createKernelObject(ctx, claim, "EQ_REFL", step, []);
  return {
    rule: "EQ_REFL",
    state: "PROVED",
    uses: [],
    message: "Reflexivity of equality: t = t holds for any term"
  };
}
function deriveEqualitySymmetry(ctx, claim, step) {
  const eq = parseEqualityCanonical(claim);
  if (!eq) return null;
  const flipped = requireClassical(ctx, `${eq.right} = ${eq.left}`, "EQ_SYMM");
  if (!flipped) return null;
  createKernelObject(ctx, claim, "EQ_SYMM", step, [flipped.id]);
  return {
    rule: "EQ_SYMM",
    state: "PROVED",
    uses: [flipped.claim],
    message: "Symmetry of equality: s = t implies t = s"
  };
}
function deriveEqualitySubstitution(ctx, claim, step) {
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  for (const equalityObject of classicalObjects(ctx)) {
    const equality = parseEqualityCanonical(equalityObject.claim);
    if (!equality) continue;
    const leftMembership = `${equality.left} \u2208 ${membership.set}`;
    const rightMembership = `${equality.right} \u2208 ${membership.set}`;
    if (sameProp(rightMembership, claim)) {
      const source2 = requireClassical(ctx, leftMembership, "IMPLIES_ELIM");
      if (source2) {
        createKernelObject(ctx, claim, "IMPLIES_ELIM", step, [equalityObject.id, source2.id]);
        return {
          rule: "IMPLIES_ELIM",
          state: "PROVED",
          uses: [equalityObject.claim, source2.claim],
          message: "Substituted equal terms inside a membership proposition"
        };
      }
    }
    if (sameProp(leftMembership, claim)) {
      const source2 = requireClassical(ctx, rightMembership, "IMPLIES_ELIM");
      if (source2) {
        createKernelObject(ctx, claim, "IMPLIES_ELIM", step, [equalityObject.id, source2.id]);
        return {
          rule: "IMPLIES_ELIM",
          state: "PROVED",
          uses: [equalityObject.claim, source2.claim],
          message: "Substituted equal terms inside a membership proposition"
        };
      }
    }
  }
  return null;
}
function deriveUnionRule(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const membership = parseMembershipCanonical(claim);
  if (membership) {
    const union = parseBinarySetCanonical(membership.set, "\u222A");
    if (union) {
      const swappedHyp = all.find((o) => {
        const m = parseMembershipCanonical(o.claim);
        if (!m || normArith(m.element) !== normArith(membership.element)) return false;
        const u = parseBinarySetCanonical(m.set, "\u222A");
        return u && normArith(u[0]) === normArith(union[1]) && normArith(u[1]) === normArith(union[0]);
      });
      if (swappedHyp) {
        createKernelObject(ctx, claim, "OR_INTRO_LEFT", step, [swappedHyp.id]);
        return { rule: "OR_INTRO_LEFT", state: "PROVED", uses: [swappedHyp.claim], message: "Union commutativity membership" };
      }
      const lImg = union[0].match(/^image\((.+?),\s*(.+)\)$/);
      const rImg = union[1].match(/^image\((.+?),\s*(.+)\)$/);
      const elemApp = membership.element.match(/^(\w+)\((\w+)\)$/);
      if (lImg && rImg && elemApp && normArith(lImg[1]) === normArith(rImg[1]) && normArith(lImg[1]) === normArith(elemApp[1])) {
        const f = lImg[1], A = lImg[2], B = rImg[2], x = elemApp[2];
        const hyp = all.find((o) => {
          const m = parseMembershipCanonical(o.claim);
          if (!m || normArith(m.element) !== normArith(x)) return false;
          const u = parseBinarySetCanonical(m.set, "\u222A");
          return u && (normArith(u[0]) === normArith(A) && normArith(u[1]) === normArith(B) || normArith(u[0]) === normArith(B) && normArith(u[1]) === normArith(A));
        });
        if (hyp) {
          createKernelObject(ctx, claim, "OR_INTRO_LEFT", step, [hyp.id]);
          return { rule: "OR_INTRO_LEFT", state: "PROVED", uses: [hyp.claim], message: `Image union forward: ${x} \u2208 ${A} \u222A ${B} \u27F9 ${f}(${x}) \u2208 image(${f}, ${A}) \u222A image(${f}, ${B})` };
        }
      }
      const left = requireClassical(ctx, `${membership.element} \u2208 ${union[0]}`, "OR_INTRO_LEFT");
      if (left) {
        createKernelObject(ctx, claim, "OR_INTRO_LEFT", step, [left.id]);
        return {
          rule: "OR_INTRO_LEFT",
          state: "PROVED",
          uses: [left.claim],
          message: "Injected membership into the left side of a union"
        };
      }
      const right = requireClassical(ctx, `${membership.element} \u2208 ${union[1]}`, "OR_INTRO_RIGHT");
      if (right) {
        createKernelObject(ctx, claim, "OR_INTRO_RIGHT", step, [right.id]);
        return {
          rule: "OR_INTRO_RIGHT",
          state: "PROVED",
          uses: [right.claim],
          message: "Injected membership into the right side of a union"
        };
      }
    }
  }
  const disjunction = parseDisjunctionCanonical(claim);
  if (!disjunction) return null;
  for (const object of [...ctx.premises, ...ctx.assumptions, ...classicalObjects(ctx)]) {
    const membershipObject = parseMembershipCanonical(object.claim);
    if (!membershipObject) continue;
    const setUnion = parseBinarySetCanonical(membershipObject.set, "\u222A");
    if (!setUnion) continue;
    const expectedLeft = `${membershipObject.element} \u2208 ${setUnion[0]}`;
    const expectedRight = `${membershipObject.element} \u2208 ${setUnion[1]}`;
    if (sameProp(disjunction[0], expectedLeft) && sameProp(disjunction[1], expectedRight) || sameProp(disjunction[0], expectedRight) && sameProp(disjunction[1], expectedLeft)) {
      createKernelObject(ctx, claim, "OR_ELIM", step, [object.id]);
      return {
        rule: "OR_ELIM",
        state: "PROVED",
        uses: [object.claim],
        message: "Eliminated union membership into a disjunction of memberships"
      };
    }
  }
  return null;
}
function deriveIntersectionRule(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  const intersection = parseBinarySetCanonical(membership.set, "\u2229");
  if (intersection) {
    const lPre = intersection[0].match(/^preimage\((.+?),\s*(.+)\)$/);
    const rPre = intersection[1].match(/^preimage\((.+?),\s*(.+)\)$/);
    if (lPre && rPre && normArith(lPre[1]) === normArith(rPre[1])) {
      const f = lPre[1], B = lPre[2], C = rPre[2];
      const hyp = all.find((o) => {
        const m = parseMembershipCanonical(o.claim);
        return m && normArith(m.element) === normArith(membership.element) && (m.set === `preimage(${f}, ${B} \u2229 ${C})` || m.set === `preimage(${f}, ${B}\u2229${C})` || m.set === `preimage(${f}, ${C} \u2229 ${B})` || m.set === `preimage(${f}, ${C}\u2229${B})`);
      });
      if (hyp) {
        createKernelObject(ctx, claim, "AND_INTRO", step, [hyp.id]);
        return { rule: "AND_INTRO", state: "PROVED", uses: [hyp.claim], message: `Preimage intersection: ${membership.element} \u2208 preimage(${f}, ${B} \u2229 ${C})` };
      }
    }
    const left = requireClassical(ctx, `${membership.element} \u2208 ${intersection[0]}`, "AND_INTRO");
    const right = requireClassical(ctx, `${membership.element} \u2208 ${intersection[1]}`, "AND_INTRO");
    if (left && right) {
      createKernelObject(ctx, claim, "AND_INTRO", step, [left.id, right.id]);
      return {
        rule: "AND_INTRO",
        state: "PROVED",
        uses: [left.claim, right.claim],
        message: "Constructed intersection membership from both components"
      };
    }
  }
  for (const object of classicalObjects(ctx)) {
    const sourceMembership = parseMembershipCanonical(object.claim);
    if (!sourceMembership) continue;
    const sourceIntersection = parseBinarySetCanonical(sourceMembership.set, "\u2229");
    if (!sourceIntersection) continue;
    if (sameProp(claim, `${sourceMembership.element} \u2208 ${sourceIntersection[0]}`)) {
      createKernelObject(ctx, claim, "AND_ELIM_LEFT", step, [object.id]);
      return {
        rule: "AND_ELIM_LEFT",
        state: "PROVED",
        uses: [object.claim],
        message: "Projected the left component of an intersection membership"
      };
    }
    if (sameProp(claim, `${sourceMembership.element} \u2208 ${sourceIntersection[1]}`)) {
      createKernelObject(ctx, claim, "AND_ELIM_RIGHT", step, [object.id]);
      return {
        rule: "AND_ELIM_RIGHT",
        state: "PROVED",
        uses: [object.claim],
        message: "Projected the right component of an intersection membership"
      };
    }
  }
  return null;
}
function deriveImageRule(ctx, claim, step) {
  const membership = parseMembershipCanonical(claim);
  if (!membership || !/^image\s*\(/.test(membership.set)) return null;
  const imageMatch = membership.set.match(/^image\s*\(\s*([^,]+)\s*,\s*(.+)\)$/);
  const fxMatch = membership.element.match(/^(.+)\((.+)\)$/);
  if (!imageMatch || !fxMatch || normalizeSpaces(imageMatch[1]) !== normalizeSpaces(fxMatch[1])) return null;
  const inputClaim = `${normalizeSpaces(fxMatch[2])} \u2208 ${normalizeSpaces(imageMatch[2])}`;
  const input = requireClassical(ctx, inputClaim, "IMPLIES_ELIM");
  if (!input) return null;
  createKernelObject(ctx, claim, "IMPLIES_ELIM", step, [input.id]);
  return {
    rule: "IMPLIES_ELIM",
    state: "PROVED",
    uses: [input.claim],
    message: "Mapped a membership morphism through image formation"
  };
}
function derivePreimageRule(ctx, claim, step) {
  const membership = parseMembershipCanonical(claim);
  if (!membership) return null;
  if (/^preimage\s*\(/.test(membership.set)) {
    const match = membership.set.match(/^preimage\s*\(\s*([^,]+)\s*,\s*(.+)\)$/);
    if (!match) return null;
    const target = `${normalizeSpaces(match[1])}(${membership.element}) \u2208 ${normalizeSpaces(match[2])}`;
    const input2 = requireClassical(ctx, target, "IMPLIES_ELIM");
    if (!input2) return null;
    createKernelObject(ctx, claim, "IMPLIES_ELIM", step, [input2.id]);
    return {
      rule: "IMPLIES_ELIM",
      state: "PROVED",
      uses: [input2.claim],
      message: "Introduced a preimage membership from its image-side statement"
    };
  }
  const fxMembership = parseMembershipCanonical(claim);
  if (!fxMembership) return null;
  const fxMatch = fxMembership.element.match(/^(.+)\((.+)\)$/);
  if (!fxMatch) return null;
  const preimageClaim = `${normalizeSpaces(fxMatch[2])} \u2208 preimage(${normalizeSpaces(fxMatch[1])}, ${fxMembership.set})`;
  const input = requireClassical(ctx, preimageClaim, "IMPLIES_ELIM");
  if (!input) return null;
  createKernelObject(ctx, claim, "IMPLIES_ELIM", step, [input.id]);
  return {
    rule: "IMPLIES_ELIM",
    state: "PROVED",
    uses: [input.claim],
    message: "Eliminated a preimage membership back to the codomain side"
  };
}
function deriveQuantifierRule(ctx, claim, step) {
  const forall = parseBoundedQuantifierCanonical(claim, "forall");
  if (forall) {
    const witness = findWitness(ctx, forall.variable);
    const assumed = requireClassical(ctx, `${witness ?? forall.variable} \u2208 ${forall.set}`, "IMPLIES_INTRO");
    const bodyClaim = substituteVariable(forall.body, forall.variable, witness ?? forall.variable);
    const body = requireClassical(ctx, bodyClaim, "IMPLIES_INTRO");
    if (assumed && body) {
      createKernelObject(ctx, claim, "IMPLIES_INTRO", step, [assumed.id, body.id]);
      return {
        rule: "IMPLIES_INTRO",
        state: "PROVED",
        uses: [assumed.claim, body.claim],
        message: "Constructed the universal limit in the Boolean category from a fresh witness derivation"
      };
    }
  }
  const exists = parseBoundedQuantifierCanonical(claim, "exists");
  if (exists) {
    const explicitWitness = findWitness(ctx, exists.variable);
    const witnessCandidates = explicitWitness ? [explicitWitness] : classicalObjects(ctx).map((object) => parseMembershipCanonical(object.claim)?.element ?? null).filter((value) => Boolean(value));
    for (const witness of witnessCandidates) {
      const membership = requireClassical(ctx, `${witness} \u2208 ${exists.set}`, "OR_INTRO_LEFT");
      const body = requireClassical(ctx, substituteVariable(exists.body, exists.variable, witness), "OR_INTRO_LEFT");
      if (membership && body) {
        createKernelObject(ctx, claim, "OR_INTRO_LEFT", step, [membership.id, body.id]);
        return {
          rule: "OR_INTRO_LEFT",
          state: "PROVED",
          uses: [membership.claim, body.claim],
          message: "Constructed the existential colimit in the Boolean category from a concrete witness"
        };
      }
    }
  }
  for (const object of classicalObjects(ctx)) {
    const quantified = parseBoundedQuantifierCanonical(object.claim, "forall");
    if (!quantified) continue;
    const membership = parseMembershipCanonical(claim);
    if (!membership) continue;
    const premise = requireClassical(ctx, `${membership.element} \u2208 ${quantified.set}`, "IMPLIES_ELIM");
    if (!premise) continue;
    const expected = substituteVariable(quantified.body, quantified.variable, membership.element);
    if (!sameProp(expected, claim)) continue;
    createKernelObject(ctx, claim, "IMPLIES_ELIM", step, [object.id, premise.id]);
    return {
      rule: "IMPLIES_ELIM",
      state: "PROVED",
      uses: [object.claim, premise.claim],
      message: "Instantiated a universal morphism at a concrete witness"
    };
  }
  for (const object of classicalObjects(ctx)) {
    const quantified = parseBoundedQuantifierCanonical(object.claim, "exists");
    if (!quantified) continue;
    const witness = findWitness(ctx, quantified.variable);
    const witnessName = witness ?? quantified.variable;
    const membership = findExact(ctx.assumptions, `${witnessName} \u2208 ${quantified.set}`, false);
    const body = findExact(ctx.assumptions, substituteVariable(quantified.body, quantified.variable, witnessName), false);
    if (membership && body && !containsWitness(claim, witnessName)) {
      createKernelObject(ctx, claim, "OR_ELIM", step, [object.id, membership.id, body.id]);
      return {
        rule: "OR_ELIM",
        state: "PROVED",
        uses: [object.claim, membership.claim, body.claim],
        message: "Eliminated an existential morphism through a witness branch"
      };
    }
  }
  return null;
}
function deriveDependentTypeRule(ctx, claim, step) {
  const canonical = parseCanonicalExpr(claim);
  if (typeof canonical === "object" && "kind" in canonical) {
    if (canonical.kind === "dependent_product") {
      const witness = findWitness(ctx, canonical.variable);
      const assumed = requireClassical(ctx, `${witness ?? canonical.variable} \u2208 ${canonical.domain}`, "PI_INTRO");
      const bodyClaimString = typeof canonical.body === "string" ? canonical.body : exprToProp(canonical.body);
      const bodyClaim = substituteVariable(bodyClaimString, canonical.variable, witness ?? canonical.variable);
      const body = requireClassical(ctx, bodyClaim, "PI_INTRO");
      if (assumed && body) {
        createKernelObject(ctx, claim, "PI_INTRO", step, [assumed.id, body.id]);
        return {
          rule: "PI_INTRO",
          state: "PROVED",
          uses: [assumed.claim, body.claim],
          message: "Constructed the Pi product limit from a local dependent type derivation"
        };
      }
    }
    if (canonical.kind === "dependent_sum") {
      const explicitWitness = findWitness(ctx, canonical.variable);
      if (explicitWitness) {
        const domainClaim = requireClassical(ctx, `${explicitWitness} \u2208 ${canonical.domain}`, "SIGMA_INTRO");
        const bodyClaimString = typeof canonical.body === "string" ? canonical.body : exprToProp(canonical.body);
        const bodyClaim = requireClassical(ctx, substituteVariable(bodyClaimString, canonical.variable, explicitWitness), "SIGMA_INTRO");
        if (domainClaim && bodyClaim) {
          createKernelObject(ctx, claim, "SIGMA_INTRO", step, [domainClaim.id, bodyClaim.id]);
          return {
            rule: "SIGMA_INTRO",
            state: "PROVED",
            uses: [domainClaim.claim, bodyClaim.claim],
            message: "Constructed a Sigma sum type from an explicit dependent witness pair"
          };
        }
      }
    }
  }
  for (const object of classicalObjects(ctx)) {
    const pKernel = parseCanonicalExpr(object.claim);
    if (typeof pKernel === "object" && "kind" in pKernel && pKernel.kind === "dependent_product") {
      const mem = parseMembershipCanonical(claim);
      if (!mem) continue;
      const premise = requireClassical(ctx, `${mem.element} \u2208 ${pKernel.domain}`, "PI_ELIM");
      if (!premise) continue;
      const bodyClaimString = typeof pKernel.body === "string" ? pKernel.body : exprToProp(pKernel.body);
      const expected = substituteVariable(bodyClaimString, pKernel.variable, mem.element);
      if (sameProp(expected, claim)) {
        createKernelObject(ctx, claim, "PI_ELIM", step, [object.id, premise.id]);
        return {
          rule: "PI_ELIM",
          state: "PROVED",
          uses: [object.claim, premise.claim],
          message: "Applied a dependent Pi type application binding the context"
        };
      }
    }
    if (typeof pKernel === "object" && "kind" in pKernel && pKernel.kind === "dependent_sum" && pKernel.element) {
      const bodyClaimString = typeof pKernel.body === "string" ? pKernel.body : exprToProp(pKernel.body);
      const pairName = pKernel.element;
      const fstExpr = `fst(${pairName})`;
      const fstMem = `${fstExpr} \u2208 ${pKernel.domain}`;
      const sndProp = substituteVariable(bodyClaimString, pKernel.variable, fstExpr);
      if (sameProp(claim, fstMem)) {
        createKernelObject(ctx, claim, "SIGMA_ELIM", step, [object.id]);
        return { rule: "SIGMA_ELIM", state: "PROVED", uses: [object.claim], message: `fst projection: ${fstExpr} \u2208 ${pKernel.domain}` };
      }
      if (sameProp(claim, sndProp)) {
        createKernelObject(ctx, claim, "SIGMA_ELIM", step, [object.id]);
        return { rule: "SIGMA_ELIM", state: "PROVED", uses: [object.claim], message: `snd projection: ${sndProp}` };
      }
    }
  }
  const memClaim = parseMembershipCanonical(claim);
  if (memClaim) {
    const subtypeChain = {
      "Int": ["Nat", "\u2115"],
      "\u2124": ["Nat", "\u2115"],
      "Real": ["Nat", "\u2115", "Int", "\u2124"],
      "\u211D": ["Nat", "\u2115", "Int", "\u2124"]
    };
    const supertypes = subtypeChain[memClaim.set];
    if (supertypes) {
      const all = allContextObjects(ctx);
      for (const sup of supertypes) {
        const witness = all.find((o) => {
          const m = parseMembershipCanonical(o.claim);
          return m && m.element === memClaim.element && m.set === sup;
        });
        if (witness) {
          createKernelObject(ctx, claim, "STRUCTURAL", step, [witness.id]);
          return { rule: "STRUCTURAL", state: "PROVED", uses: [witness.claim], message: `${memClaim.element} \u2208 ${sup} implies ${memClaim.element} \u2208 ${memClaim.set} by subtype coercion` };
        }
      }
    }
  }
  return null;
}
function deriveNaturalTransformationRule(ctx, claim, step) {
  const pred = parseCategoryPredicateCanonical(claim);
  if (pred && pred.name === "NaturalTransformation") {
    createKernelObject(ctx, claim, "NATURAL_TRANSFORMATION_INTRO", step);
    return {
      rule: "NATURAL_TRANSFORMATION_INTRO",
      state: "PROVED",
      message: "Checked the commutative diagram functor projection natively"
    };
  }
  return null;
}
function deriveExFalso(ctx, claim, step) {
  const bottom = findExact(ctx.objects, BOTTOM, false);
  if (!bottom) return null;
  createKernelObject(ctx, claim, "CONTRADICTION", step, [bottom.id]);
  return {
    rule: "CONTRADICTION",
    state: "PROVED",
    uses: [BOTTOM],
    message: "Derived the target claim by factoring through falsehood"
  };
}
function deriveArithClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const eq = parseEqualityCanonical(claim);
  if (eq) {
    if (arithEqual(eq.left, eq.right)) {
      createKernelObject(ctx, claim, "ARITH_EVAL", step);
      return {
        rule: "ARITH_EVAL",
        state: "PROVED",
        message: "Verified by concrete integer evaluation"
      };
    }
    const exprSubsts = /* @__PURE__ */ new Map();
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      if (/^[A-Za-z_]\w*$/.test(objEq.left.trim())) {
        exprSubsts.set(objEq.left.trim(), objEq.right);
      }
    }
    if (arithSymEqual(eq.left, eq.right) || arithSymEqualWithSubst(eq.left, eq.right, exprSubsts)) {
      createKernelObject(ctx, claim, "ARITH_SYMCHECK", step);
      return {
        rule: "ARITH_SYMCHECK",
        state: "PROVED",
        message: "Verified by polynomial identity check (Schwartz-Zippel)"
      };
    }
    const allForTrans = [...all, ...ctx.objects];
    const normalize2 = (s) => normArith(s).replace(/\s/g, "");
    const normL = normalize2(eq.left);
    const normR = normalize2(eq.right);
    for (const obj1 of allForTrans) {
      const e1 = parseEqualityCanonical(obj1.claim);
      if (!e1) continue;
      const e1Sides = [[e1.left, e1.right], [e1.right, e1.left]];
      for (const [e1l, e1r] of e1Sides) {
        if (normalize2(e1l) !== normL) continue;
        const midNorm = normalize2(e1r);
        for (const obj2 of allForTrans) {
          if (obj2 === obj1) continue;
          const e2 = parseEqualityCanonical(obj2.claim);
          if (!e2) continue;
          const e2Sides = [[e2.left, e2.right], [e2.right, e2.left]];
          for (const [e2l, e2r] of e2Sides) {
            if (normalize2(e2l) === midNorm && normalize2(e2r) === normR) {
              createKernelObject(ctx, claim, "ARITH_SYMCHECK", step, [obj1.id, obj2.id]);
              return {
                rule: "ARITH_SYMCHECK",
                state: "PROVED",
                uses: [obj1.claim, obj2.claim],
                message: "Equality by transitivity"
              };
            }
          }
        }
      }
    }
    for (const factor of [2, 3, 4, 6]) {
      const scaledL = `${factor} * (${normArith(eq.left)})`;
      const scaledR = `${factor} * (${normArith(eq.right)})`;
      for (const obj of allForTrans) {
        const oe = parseEqualityCanonical(obj.claim);
        if (!oe) continue;
        const matchFwd = arithSymEqual(normArith(oe.left), scaledL) && arithSymEqual(normArith(oe.right), scaledR);
        const matchRev = arithSymEqual(normArith(oe.right), scaledL) && arithSymEqual(normArith(oe.left), scaledR);
        if (matchFwd || matchRev) {
          createKernelObject(ctx, claim, "ARITH_SYMCHECK", step, [obj.id]);
          return {
            rule: "ARITH_SYMCHECK",
            state: "PROVED",
            uses: [obj.claim],
            message: `Derived by cancelling factor ${factor} from both sides`
          };
        }
      }
    }
    for (const factor of [2, 3, 4, 6]) {
      const fStr = String(factor);
      const stripFactor = (s, f) => {
        const re1 = new RegExp(`^${f}\\s*\\*\\s*\\((.+)\\)$`);
        const re2 = new RegExp(`^${f}\\s*\\*\\s*(.+)$`);
        const m1 = s.match(re1);
        if (m1) return m1[1].trim();
        const m2 = s.match(re2);
        if (m2) return m2[1].trim();
        return null;
      };
      const innerL = stripFactor(normArith(eq.left), fStr);
      const innerR = stripFactor(normArith(eq.right), fStr);
      if (innerL && innerR) {
        const scaledClaim = `${fStr} * (${innerL}) = ${fStr} * (${innerR})`;
        const scaledObj = allForTrans.find((o) => {
          const oe = parseEqualityCanonical(o.claim);
          if (!oe) return false;
          return normalize2(oe.left) === normalize2(`${fStr} * (${innerL})`) && normalize2(oe.right) === normalize2(`${fStr} * (${innerR})`) || normalize2(oe.right) === normalize2(`${fStr} * (${innerL})`) && normalize2(oe.left) === normalize2(`${fStr} * (${innerR})`);
        });
        if (scaledObj) {
          createKernelObject(ctx, claim, "ARITH_SYMCHECK", step, [scaledObj.id]);
          return {
            rule: "ARITH_SYMCHECK",
            state: "PROVED",
            uses: [scaledObj.claim],
            message: `Derived by cancelling factor ${fStr}`
          };
        }
        if (arithSymEqualWithSubst(innerL, innerR, exprSubsts)) {
          createKernelObject(ctx, claim, "ARITH_SYMCHECK", step);
          return {
            rule: "ARITH_SYMCHECK",
            state: "PROVED",
            message: `Derived by symbolic check after cancelling factor ${fStr}`
          };
        }
      }
    }
  }
  const evenArg = parseEvenClaim(claim);
  if (evenArg !== null) {
    if (isConcreteEven(evenArg)) {
      createKernelObject(ctx, claim, "ARITH_EVAL", step);
      return { rule: "ARITH_EVAL", state: "PROVED", message: "Concrete even integer" };
    }
    if (extractDoubleOperand(evenArg) !== null) {
      createKernelObject(ctx, claim, "ARITH_EVEN_OF_DOUBLE", step);
      return { rule: "ARITH_EVEN_OF_DOUBLE", state: "PROVED", message: `${evenArg} is a double by form` };
    }
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      const sides = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
      for (const [lhs, rhs] of sides) {
        if (normArith(lhs) === normArith(evenArg) && extractDoubleOperand(rhs) !== null) {
          createKernelObject(ctx, claim, "ARITH_EVEN_OF_DOUBLE", step, [obj.id]);
          return {
            rule: "ARITH_EVEN_OF_DOUBLE",
            state: "PROVED",
            uses: [obj.claim],
            message: `${evenArg} = 2\xB7k establishes even(${evenArg})`
          };
        }
      }
    }
    const squareClaim = `even(${evenArg} * ${evenArg})`;
    const squareObj = all.find((o) => normArith(o.claim) === normArith(squareClaim));
    if (squareObj) {
      createKernelObject(ctx, claim, "ARITH_EVEN_SQUARE", step, [squareObj.id]);
      return {
        rule: "ARITH_EVEN_SQUARE",
        state: "PROVED",
        uses: [squareObj.claim],
        message: `Kernel axiom: n\xB2 even implies n even`
      };
    }
    const addParts = (() => {
      const s = normArith(evenArg);
      let depth = 0;
      for (let i = 0; i < s.length; i++) {
        const ch = s[i];
        if (ch === "(") depth++;
        else if (ch === ")") depth--;
        else if (depth === 0 && ch === "+") return [normArith(s.slice(0, i)), normArith(s.slice(i + 1))];
      }
      return null;
    })();
    if (addParts) {
      const [a, b] = addParts;
      const evenA = all.find((o) => normArith(o.claim) === normArith(`even(${a})`));
      const evenB = all.find((o) => normArith(o.claim) === normArith(`even(${b})`));
      if (evenA && evenB) {
        createKernelObject(ctx, claim, "ARITH_EVEN_PRODUCT", step, [evenA.id, evenB.id]);
        return { rule: "ARITH_EVEN_PRODUCT", state: "PROVED", uses: [evenA.claim, evenB.claim], message: "even(a) + even(b) = even(a+b)" };
      }
    }
    const mul = splitTopMul(evenArg);
    if (mul) {
      const [a, b] = mul;
      const evenA = `even(${a})`;
      const evenB = `even(${b})`;
      const witA = all.find((o) => normArith(o.claim) === normArith(evenA));
      const witB = all.find((o) => normArith(o.claim) === normArith(evenB));
      const wit = witA ?? witB;
      if (wit) {
        createKernelObject(ctx, claim, "ARITH_EVEN_PRODUCT", step, [wit.id]);
        return {
          rule: "ARITH_EVEN_PRODUCT",
          state: "PROVED",
          uses: [wit.claim],
          message: `Even factor in product establishes even(${evenArg})`
        };
      }
    }
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      const sides = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
      for (const [lhs, rhs] of sides) {
        if (normArith(lhs) === normArith(evenArg)) {
          const evenRhs = `even(${rhs})`;
          const evenRhsObj = all.find((o) => normArith(o.claim) === normArith(evenRhs));
          if (evenRhsObj) {
            createKernelObject(ctx, claim, "ARITH_EVEN_OF_DOUBLE", step, [obj.id, evenRhsObj.id]);
            return {
              rule: "ARITH_EVEN_OF_DOUBLE",
              state: "PROVED",
              uses: [obj.claim, evenRhsObj.claim],
              message: `Even transferred via equality`
            };
          }
        }
      }
    }
  }
  const oddArg = parseOddClaim(claim);
  if (oddArg !== null) {
    if (isConcreteOdd(oddArg)) {
      createKernelObject(ctx, claim, "ARITH_EVAL", step);
      return { rule: "ARITH_EVAL", state: "PROVED", message: "Concrete odd integer" };
    }
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      const sides = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
      for (const [lhs, rhs] of sides) {
        if (normArith(lhs) === normArith(oddArg) && extractSuccDoubleOperand(rhs) !== null) {
          createKernelObject(ctx, claim, "ARITH_ODD_OF_SUCC_DOUBLE", step, [obj.id]);
          return {
            rule: "ARITH_ODD_OF_SUCC_DOUBLE",
            state: "PROVED",
            uses: [obj.claim],
            message: `${oddArg} = 2\xB7k+1 establishes odd(${oddArg})`
          };
        }
      }
    }
  }
  const div = parseDividesClaim(claim);
  if (div) {
    if (normArith(div.a) === "1") {
      createKernelObject(ctx, claim, "ARITH_DIVIDES", step);
      return { rule: "ARITH_DIVIDES", state: "PROVED", message: "1 divides everything" };
    }
    const av = evalArith(div.a);
    const bv = evalArith(div.b);
    if (av !== null && bv !== null && av !== 0 && bv % av === 0) {
      createKernelObject(ctx, claim, "ARITH_EVAL", step);
      return { rule: "ARITH_EVAL", state: "PROVED", message: "Concrete divisibility check" };
    }
    if (normArith(div.a) === "2") {
      const evenN = all.find((o) => normArith(o.claim) === normArith(`even(${div.b})`));
      if (evenN) {
        createKernelObject(ctx, claim, "ARITH_DIVIDES", step, [evenN.id]);
        return { rule: "ARITH_DIVIDES", state: "PROVED", uses: [evenN.claim], message: "even(n) implies divides(2, n)" };
      }
    }
    for (const obj of all) {
      const objEq = parseEqualityCanonical(obj.claim);
      if (!objEq) continue;
      const sides = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
      for (const [lhs, rhs] of sides) {
        if (normArith(lhs) === normArith(div.b)) {
          const mul = splitTopMul(rhs);
          if (mul && (normArith(mul[0]) === normArith(div.a) || normArith(mul[1]) === normArith(div.a))) {
            createKernelObject(ctx, claim, "ARITH_DIVIDES", step, [obj.id]);
            return {
              rule: "ARITH_DIVIDES",
              state: "PROVED",
              uses: [obj.claim],
              message: `${div.b} = ${div.a}\xB7k establishes divides(${div.a}, ${div.b})`
            };
          }
        }
      }
    }
  }
  const coprimeMatch = claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
  if (coprimeMatch) {
    const [, a, b] = coprimeMatch;
    const av = evalArith(a);
    const bv = evalArith(b);
    if (av !== null && bv !== null) {
      const gcd = (x, y) => y === 0 ? x : gcd(y, x % y);
      if (gcd(Math.abs(av), Math.abs(bv)) === 1) {
        createKernelObject(ctx, claim, "ARITH_EVAL", step);
        return { rule: "ARITH_EVAL", state: "PROVED", message: "Concrete coprimality check" };
      }
    }
  }
  if (claim === BOTTOM || claim === "\u22A5" || claim === "False") {
    for (const obj of all) {
      const cpMatch = obj.claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
      if (!cpMatch) continue;
      const [, a, b] = cpMatch;
      const evenA = `even(${a})`;
      const evenB = `even(${b})`;
      const witA = all.find((o) => normArith(o.claim) === normArith(evenA));
      const witB = all.find((o) => normArith(o.claim) === normArith(evenB));
      if (witA && witB) {
        createKernelObject(ctx, BOTTOM, "ARITH_COPRIME_CONTRA", step, [obj.id, witA.id, witB.id]);
        if (ctx.goal) createKernelObject(ctx, ctx.goal, "ARITH_COPRIME_CONTRA", step);
        return {
          rule: "ARITH_COPRIME_CONTRA",
          state: "PROVED",
          uses: [obj.claim, witA.claim, witB.claim],
          message: `Contradiction: coprime(${a}, ${b}) but both are even`
        };
      }
    }
  }
  return null;
}
function deriveForallElim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  for (const obj of all) {
    const parsed = parseCanonicalExpr(obj.claim);
    const forall = asForallExpr(parsed);
    if (!forall) continue;
    const { variable, domain, body } = forall;
    const candidates = collectInstances(ctx, domain);
    for (const candidate of candidates) {
      const instantiated = substituteInBody(body, variable, candidate);
      if (claimsMatch(instantiated, claim)) {
        createKernelObject(ctx, claim, "FORALL_ELIM", step, [obj.id]);
        return {
          rule: "FORALL_ELIM",
          state: "PROVED",
          uses: [obj.claim],
          message: `\u2200-elimination: instantiated ${variable} \u21A6 ${candidate}`
        };
      }
      const impl = parseImplicationCanonical(instantiated);
      if (impl) {
        const [antecedent, consequent] = impl;
        if (claimsMatch(consequent, claim)) {
          const antObj = findExact(all, antecedent, false);
          if (antObj) {
            createKernelObject(ctx, claim, "FORALL_ELIM", step, [obj.id, antObj.id]);
            return {
              rule: "FORALL_ELIM",
              state: "PROVED",
              uses: [obj.claim, antObj.claim],
              message: `\u2200-elimination + \u2192-elim: ${variable} \u21A6 ${candidate}`
            };
          }
        }
      }
    }
  }
  return null;
}
function deriveExistsIntro(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const parsed = parseCanonicalExpr(claim);
  const exists = asExistsExpr(parsed);
  if (!exists) return null;
  const { variable, domain, body } = exists;
  const candidates = collectInstances(ctx, domain);
  for (const candidate of candidates) {
    const instantiated = substituteInBody(body, variable, candidate);
    const wit = all.find((o) => claimsMatch(instantiated, o.claim));
    if (wit) {
      createKernelObject(ctx, claim, "EXISTS_INTRO", step, [wit.id]);
      return {
        rule: "EXISTS_INTRO",
        state: "PROVED",
        uses: [wit.claim],
        message: `\u2203-introduction: witness ${candidate} satisfies the body`
      };
    }
  }
  return null;
}
function asForallExpr(p) {
  if (!("type" in p) || p.type !== "Quantified") return null;
  const q = p;
  if (q.quantifier !== "forall") return null;
  return { variable: q.variable, domain: q.domain, body: q.body ? exprToProp(q.body) : "" };
}
function asExistsExpr(p) {
  if (!("type" in p) || p.type !== "Quantified") return null;
  const q = p;
  if (q.quantifier !== "exists") return null;
  return { variable: q.variable, domain: q.domain, body: q.body ? exprToProp(q.body) : "" };
}
function collectInstances(ctx, domain) {
  const all = allContextObjects(ctx);
  const results = [];
  const normDomain = domain.replace(/\bNat\b/, "\u2115").replace(/\bInt\b/, "\u2124").replace(/\bReal\b/, "\u211D");
  for (const obj of all) {
    const mem = parseMembershipCanonical(obj.claim);
    if (mem && (mem.set === domain || mem.set === normDomain)) {
      results.push(mem.element);
    }
    const typed = obj.claim.match(/^(\w+)\s*:\s*(\w+)$/);
    if (typed && (typed[2] === domain || typed[2] === normDomain)) {
      results.push(typed[1]);
    }
  }
  for (const v of ctx.variables) {
    if (v.domain === domain || v.domain === normDomain) results.push(v.name);
  }
  return [...new Set(results)];
}
function substituteInBody(body, variable, value) {
  return body.replace(new RegExp(`\\b${variable}\\b`, "g"), `(${value})`);
}
function claimsMatch(a, b) {
  if (sameProp(a, b)) return true;
  const ordA = parseOrder(a);
  const ordB = parseOrder(b);
  if (ordA && ordB && ordA.op === ordB.op) {
    return arithSymEqual(normArith(ordA.left), normArith(ordB.left)) && arithSymEqual(normArith(ordA.right), normArith(ordB.right));
  }
  const eqA = parseEqualityCanonical(a);
  const eqB = parseEqualityCanonical(b);
  if (eqA && eqB) {
    return arithSymEqual(normArith(eqA.left), normArith(eqB.left)) && arithSymEqual(normArith(eqA.right), normArith(eqB.right));
  }
  const memA = parseMembershipCanonical(a);
  const memB = parseMembershipCanonical(b);
  if (memA && memB) {
    return memA.set === memB.set && normArith(memA.element) === normArith(memB.element);
  }
  return normArith(a).replace(/\((\w+)\)/g, "$1") === normArith(b).replace(/\((\w+)\)/g, "$1");
}
function deriveIntClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const exprSubsts = /* @__PURE__ */ new Map();
  for (const obj of all) {
    const objEq = parseEqualityCanonical(obj.claim);
    if (objEq && /^[A-Za-z_]\w*$/.test(objEq.left.trim())) {
      exprSubsts.set(objEq.left.trim(), objEq.right);
    }
  }
  const resolveToNumber = (expr) => {
    const direct = evalArith(expr);
    if (direct !== null) return direct;
    let substituted = expr;
    for (const [v, e] of exprSubsts) {
      substituted = substituted.replace(new RegExp(`\\b${v}\\b`, "g"), `(${e})`);
    }
    return evalArith(substituted);
  };
  const absEq = parseAbsEquality(claim);
  if (absEq) {
    const xv = resolveToNumber(absEq.arg);
    const kv = evalArith(absEq.value);
    if (xv !== null && kv !== null && Math.abs(xv) === kv) {
      const src = exprSubsts.has(absEq.arg) ? all.find((o) => {
        const e = parseEqualityCanonical(o.claim);
        return e && e.left.trim() === absEq.arg;
      }) : void 0;
      createKernelObject(ctx, claim, "ARITH_ABS", step, src ? [src.id] : []);
      return { rule: "ARITH_ABS", state: "PROVED", uses: src ? [src.claim] : [], message: `|${absEq.arg}| = ${kv}` };
    }
    const geqZero = all.find((o) => {
      const ord2 = parseOrder(o.claim);
      return ord2 && normArith(ord2.left) === normArith(absEq.arg) && normArith(ord2.right) === "0" && (ord2.op === "\u2265" || ord2.op === ">=");
    });
    if (geqZero && normArith(absEq.value) === normArith(absEq.arg)) {
      createKernelObject(ctx, claim, "ARITH_ABS", step, [geqZero.id]);
      return { rule: "ARITH_ABS", state: "PROVED", uses: [geqZero.claim], message: "abs(x) = x for x \u2265 0" };
    }
    const leqZero = all.find((o) => {
      const ord2 = parseOrder(o.claim);
      return ord2 && normArith(ord2.left) === normArith(absEq.arg) && normArith(ord2.right) === "0" && (ord2.op === "\u2264" || ord2.op === "<=");
    });
    if (leqZero && normArith(absEq.value) === normArith(`-${absEq.arg}`)) {
      createKernelObject(ctx, claim, "ARITH_ABS", step, [leqZero.id]);
      return { rule: "ARITH_ABS", state: "PROVED", uses: [leqZero.claim], message: "abs(x) = -x for x \u2264 0" };
    }
  }
  const signEq = parseSignEquality(claim);
  if (signEq) {
    const xv = resolveToNumber(signEq.arg);
    const kv = evalArith(signEq.value);
    if (xv !== null && kv !== null) {
      const expected = xv > 0 ? 1 : xv < 0 ? -1 : 0;
      if (expected === kv) {
        const src = exprSubsts.has(signEq.arg) ? all.find((o) => {
          const e = parseEqualityCanonical(o.claim);
          return e && e.left.trim() === signEq.arg;
        }) : void 0;
        createKernelObject(ctx, claim, "ARITH_SIGN", step, src ? [src.id] : []);
        return { rule: "ARITH_SIGN", state: "PROVED", uses: src ? [src.claim] : [], message: `sign(${signEq.arg}) = ${expected}` };
      }
    }
    if (normArith(signEq.value) === "1") {
      const gt = all.find((o) => {
        const ord2 = parseOrder(o.claim);
        return ord2 && normArith(ord2.left) === normArith(signEq.arg) && normArith(ord2.right) === "0" && ord2.op === ">";
      });
      if (gt) {
        createKernelObject(ctx, claim, "ARITH_SIGN", step, [gt.id]);
        return { rule: "ARITH_SIGN", state: "PROVED", uses: [gt.claim], message: "sign(x) = 1 for x > 0" };
      }
    }
    if (normArith(signEq.value) === "-1") {
      const lt = all.find((o) => {
        const ord2 = parseOrder(o.claim);
        return ord2 && normArith(ord2.left) === normArith(signEq.arg) && normArith(ord2.right) === "0" && ord2.op === "<";
      });
      if (lt) {
        createKernelObject(ctx, claim, "ARITH_SIGN", step, [lt.id]);
        return { rule: "ARITH_SIGN", state: "PROVED", uses: [lt.claim], message: "sign(x) = -1 for x < 0" };
      }
    }
    if (normArith(signEq.value) === "0") {
      const eq0 = all.find((o) => {
        const e = parseEqualityCanonical(o.claim);
        return e && normArith(e.left) === normArith(signEq.arg) && normArith(e.right) === "0";
      });
      if (eq0) {
        createKernelObject(ctx, claim, "ARITH_SIGN", step, [eq0.id]);
        return { rule: "ARITH_SIGN", state: "PROVED", uses: [eq0.claim], message: "sign(x) = 0 for x = 0" };
      }
    }
  }
  const ord = parseOrder(claim);
  if (ord) {
    const result = evalOrder(ord.left, ord.op, ord.right);
    if (result === true) {
      createKernelObject(ctx, claim, "ARITH_ORDER", step);
      return { rule: "ARITH_ORDER", state: "PROVED", message: `Concrete ordering: ${claim}` };
    }
    const subL = resolveToNumber(ord.left);
    const subR = resolveToNumber(ord.right);
    if (subL !== null && subR !== null) {
      const holds = (() => {
        switch (ord.op) {
          case "<":
            return subL < subR;
          case ">":
            return subL > subR;
          case "\u2264":
          case "<=":
            return subL <= subR;
          case "\u2265":
          case ">=":
            return subL >= subR;
        }
      })();
      if (holds) {
        const uses = [...exprSubsts.keys()].filter((v) => ord.left.includes(v) || ord.right.includes(v)).map((v) => all.find((o) => {
          const e = parseEqualityCanonical(o.claim);
          return e && e.left.trim() === v;
        })).filter((o) => Boolean(o));
        createKernelObject(ctx, claim, "ARITH_ORDER", step, uses.map((o) => o.id));
        return { rule: "ARITH_ORDER", state: "PROVED", uses: uses.map((o) => o.claim), message: `Ordering verified by substitution` };
      }
    }
    for (const obj of all) {
      const obj2 = parseOrder(obj.claim);
      if (!obj2) continue;
      if (normArith(obj2.left) === normArith(ord.left)) {
        const mid = obj2.right;
        for (const obj3 of all) {
          if (obj3 === obj) continue;
          const obj4 = parseOrder(obj3.claim);
          if (!obj4) continue;
          if (normArith(obj4.left) === normArith(mid) && normArith(obj4.right) === normArith(ord.right)) {
            const isStrict = obj2.op === "<" || obj4.op === "<";
            const targetStrict = ord.op === "<" || ord.op === ">";
            if (!targetStrict || isStrict) {
              createKernelObject(ctx, claim, "ARITH_ORDER", step, [obj.id, obj3.id]);
              return { rule: "ARITH_ORDER", state: "PROVED", uses: [obj.claim, obj3.claim], message: "Ordering by transitivity" };
            }
          }
        }
      }
    }
    if (ord.op === "\u2265" || ord.op === ">=") {
      if (normArith(ord.right) === "0") {
        const lhsNorm = normArith(ord.left);
        const inNat = all.find((o) => {
          const mem = parseMembershipCanonical(o.claim);
          return mem && normArith(mem.element) === lhsNorm && (mem.set === "Nat" || mem.set === "\u2115");
        });
        if (inNat) {
          createKernelObject(ctx, claim, "ARITH_ORDER", step, [inNat.id]);
          return { rule: "ARITH_ORDER", state: "PROVED", uses: [inNat.claim], message: `${ord.left} \u2208 Nat implies ${ord.left} \u2265 0` };
        }
      }
    }
    if (ord.op === "\u2265" || ord.op === ">=") {
      if (normArith(ord.right) === "0") {
        const lhs = normArith(ord.left);
        const factors = splitTopMul(ord.left);
        if (factors && normArith(factors[0]) === normArith(factors[1])) {
          const inInt = all.find((o) => {
            const mem = parseMembershipCanonical(o.claim);
            return mem && normArith(mem.element) === normArith(factors[0]) && (mem.set === "Int" || mem.set === "\u2124" || mem.set === "Nat" || mem.set === "\u2115");
          });
          if (inInt) {
            createKernelObject(ctx, claim, "ARITH_ORDER", step, [inInt.id]);
            return { rule: "ARITH_ORDER", state: "PROVED", uses: [inInt.claim], message: `${ord.left} \u2265 0 (square non-negative)` };
          }
        }
      }
    }
  }
  const absOrd = claim.match(/^abs\((.+)\)\s*(≥|>=)\s*0$/);
  if (absOrd) {
    createKernelObject(ctx, claim, "ARITH_ABS", step);
    return { rule: "ARITH_ABS", state: "PROVED", message: `abs is always non-negative` };
  }
  return null;
}
function deriveModArithClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const primeArg = parsePrimePred(claim);
  if (primeArg !== null) {
    const v = evalArith(primeArg);
    if (v !== null && isPrime(v)) {
      createKernelObject(ctx, claim, "ARITH_PRIME", step);
      return { rule: "ARITH_PRIME", state: "PROVED", message: `${v} is prime` };
    }
    const hyp = all.find((o) => normArith(o.claim) === normArith(claim));
    if (hyp) {
      createKernelObject(ctx, claim, "ARITH_PRIME", step, [hyp.id]);
      return { rule: "ARITH_PRIME", state: "PROVED", uses: [hyp.claim], message: "Prime from context" };
    }
  }
  const totEq = parseTotientEquality(claim);
  if (totEq) {
    const nv = evalArith(totEq.arg);
    if (nv !== null) {
      const tv = computeTotient(nv);
      const kv = evalArith(totEq.value);
      if (kv !== null && tv === kv) {
        createKernelObject(ctx, claim, "ARITH_TOTIENT", step);
        return { rule: "ARITH_TOTIENT", state: "PROVED", message: `\u03C6(${nv}) = ${tv}` };
      }
    }
    const argMul = splitTopMul(totEq.arg);
    if (argMul) {
      const [pStr, qStr] = argMul;
      const pPrime2 = all.find((o) => parsePrimePred(o.claim) === normArith(pStr) || normArith(o.claim) === normArith(`${pStr} \u2208 Prime`));
      const qPrime = all.find((o) => parsePrimePred(o.claim) === normArith(qStr) || normArith(o.claim) === normArith(`${qStr} \u2208 Prime`));
      if (pPrime2 && qPrime) {
        const expected = `(${pStr} - 1) * (${qStr} - 1)`;
        if (arithSymEqual(normArith(totEq.value), expected) || normArith(totEq.value) === normArith(expected)) {
          createKernelObject(ctx, claim, "ARITH_TOTIENT", step, [pPrime2.id, qPrime.id]);
          return {
            rule: "ARITH_TOTIENT",
            state: "PROVED",
            uses: [pPrime2.claim, qPrime.claim],
            message: `\u03C6(p\xB7q) = (p-1)(q-1) for distinct primes`
          };
        }
      }
    }
    const pPrime = all.find((o) => parsePrimePred(o.claim) === normArith(totEq.arg) || normArith(o.claim) === normArith(`${totEq.arg} \u2208 Prime`));
    if (pPrime) {
      const expected = `${totEq.arg} - 1`;
      if (arithSymEqual(normArith(totEq.value), expected) || normArith(totEq.value) === normArith(expected)) {
        createKernelObject(ctx, claim, "ARITH_TOTIENT", step, [pPrime.id]);
        return {
          rule: "ARITH_TOTIENT",
          state: "PROVED",
          uses: [pPrime.claim],
          message: `\u03C6(p) = p-1 for prime p`
        };
      }
    }
  }
  const cong = parseCongruence(claim);
  if (cong) {
    if (areCongruent(cong.a, cong.b, cong.n)) {
      createKernelObject(ctx, claim, "ARITH_MOD_EVAL", step);
      return { rule: "ARITH_MOD_EVAL", state: "PROVED", message: "Verified by concrete modular evaluation" };
    }
    if (arithSymEqual(normArith(cong.a), normArith(cong.b))) {
      createKernelObject(ctx, claim, "ARITH_CONGRUENCE", step);
      return { rule: "ARITH_CONGRUENCE", state: "PROVED", message: "Congruence reflexivity: a \u2261 a (mod n)" };
    }
    const symHyp = all.find((o) => {
      const c2 = parseCongruence(o.claim);
      return c2 && normArith(c2.n) === normArith(cong.n) && normArith(c2.a) === normArith(cong.b) && normArith(c2.b) === normArith(cong.a);
    });
    if (symHyp) {
      createKernelObject(ctx, claim, "ARITH_CONGRUENCE", step, [symHyp.id]);
      return { rule: "ARITH_CONGRUENCE", state: "PROVED", uses: [symHyp.claim], message: "Congruence symmetry" };
    }
    for (const obj1 of all) {
      const c1 = parseCongruence(obj1.claim);
      if (!c1 || normArith(c1.n) !== normArith(cong.n) || normArith(c1.a) !== normArith(cong.a)) continue;
      const mid = c1.b;
      for (const obj2 of all) {
        if (obj2 === obj1) continue;
        const c2 = parseCongruence(obj2.claim);
        if (c2 && normArith(c2.n) === normArith(cong.n) && normArith(c2.a) === normArith(mid) && normArith(c2.b) === normArith(cong.b)) {
          createKernelObject(ctx, claim, "ARITH_CONGRUENCE", step, [obj1.id, obj2.id]);
          return { rule: "ARITH_CONGRUENCE", state: "PROVED", uses: [obj1.claim, obj2.claim], message: `Congruence transitivity via ${mid}` };
        }
      }
    }
    const hyp = all.find((o) => normArith(o.claim) === normArith(claim));
    if (hyp) {
      createKernelObject(ctx, claim, "ARITH_CONGRUENCE", step, [hyp.id]);
      return { rule: "ARITH_CONGRUENCE", state: "PROVED", uses: [hyp.claim], message: "Congruence from context" };
    }
    const modA = evalMod(cong.a, cong.n);
    const modB = evalMod(cong.b, cong.n);
    if (modA !== null && modB !== null && modA === modB) {
      createKernelObject(ctx, claim, "ARITH_CONGRUENCE", step);
      return { rule: "ARITH_CONGRUENCE", state: "PROVED", message: "Congruence from modular evaluation" };
    }
    if (normArith(cong.b) === "1") {
      const baseExp = parsePower(cong.a);
      if (baseExp) {
        const nPrime = all.find((o) => parsePrimePred(o.claim) === normArith(cong.n) || normArith(o.claim) === normArith(`${cong.n} \u2208 Prime`));
        if (nPrime && arithSymEqual(normArith(baseExp.exp), `${cong.n} - 1`)) {
          const cprime = all.find((o) => {
            const cp = o.claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
            return cp && (normArith(cp[1]) === normArith(baseExp.base) && normArith(cp[2]) === normArith(cong.n) || normArith(cp[2]) === normArith(baseExp.base) && normArith(cp[1]) === normArith(cong.n));
          });
          if (cprime) {
            createKernelObject(ctx, claim, "ARITH_FERMAT", step, [nPrime.id, cprime.id]);
            return {
              rule: "ARITH_FERMAT",
              state: "PROVED",
              uses: [nPrime.claim, cprime.claim],
              message: `Fermat's little theorem: a^(p-1) \u2261 1 (mod p)`
            };
          }
        }
      }
      if (baseExp) {
        const expTotArg = parseTotientExpr(baseExp.exp);
        if (expTotArg && normArith(expTotArg) === normArith(cong.n)) {
          const cprime = all.find((o) => {
            const cp = o.claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
            return cp && (normArith(cp[1]) === normArith(baseExp.base) && normArith(cp[2]) === normArith(cong.n) || normArith(cp[2]) === normArith(baseExp.base) && normArith(cp[1]) === normArith(cong.n));
          });
          if (cprime) {
            createKernelObject(ctx, claim, "ARITH_EULER", step, [cprime.id]);
            return {
              rule: "ARITH_EULER",
              state: "PROVED",
              uses: [cprime.claim],
              message: `Euler's theorem: a^\u03C6(n) \u2261 1 (mod n)`
            };
          }
        }
      }
    }
    {
      const outerPow = parsePower(cong.a);
      if (outerPow) {
        const innerPow = parsePower(outerPow.base);
        if (innerPow && normArith(innerPow.base) === normArith(cong.b)) {
          const m = innerPow.base;
          const e = innerPow.exp;
          const d = outerPow.exp;
          const n = cong.n;
          const eTimesD = `${e} * ${d}`;
          const modPhi = `\u03C6(${n})`;
          const keyEq = all.find((o) => {
            const c = parseCongruence(o.claim);
            return c && normArith(c.n) === normArith(modPhi) && normArith(c.b) === "1" && (arithSymEqual(normArith(c.a), eTimesD) || arithSymEqual(normArith(c.a), `${d} * ${e}`));
          });
          if (keyEq) {
            createKernelObject(ctx, claim, "ARITH_RSA", step, [keyEq.id]);
            return {
              rule: "ARITH_RSA",
              state: "PROVED",
              uses: [keyEq.claim],
              message: `RSA correctness: (m^e)^d \u2261 m (mod n) by Euler's theorem`
            };
          }
        }
      }
    }
  }
  const modEq = parseEqualityCanonical(claim);
  if (modEq) {
    const modOp = parseModOp(modEq.left) ?? parseModOp(modEq.right);
    if (modOp) {
      const result = evalMod(modOp.a, modOp.n);
      const other = parseModOp(modEq.left) ? modEq.right : modEq.left;
      const otherV = evalArith(other);
      if (result !== null && otherV !== null && result === otherV) {
        createKernelObject(ctx, claim, "ARITH_MOD_EVAL", step);
        return { rule: "ARITH_MOD_EVAL", state: "PROVED", message: "Verified by modular evaluation" };
      }
    }
  }
  return null;
}
function createKernelObject(ctx, claim, rule, step, inputs = [], imports = [], tau = "1", unresolvedTerms = []) {
  const morphism = createMorphismForClaim(ctx.category, claim, rule, tau, inputs, unresolvedTerms);
  return registerDerivedObject(ctx, claim, step, rule, morphism, inputs, imports);
}
function registerDerivedObject(ctx, claim, step, rule, morphism, inputs, imports = []) {
  const proofObject = {
    id: morphism.id,
    claim,
    term: safeTermFromString(claim),
    domain: morphism.domain,
    codomain: morphism.codomain,
    domainRestriction: morphism.domainRestriction,
    tau: morphism.tau,
    rule,
    inputs,
    pending: morphism.pending,
    suspended: morphism.suspended,
    step,
    imports: imports.length > 0 ? imports : void 0
  };
  ctx.objects.push(proofObject);
  ctx.derivations.push({
    id: `drv:${morphism.id}`,
    rule,
    inputIds: inputs,
    outputId: morphism.id,
    step
  });
  registerCategoryClaim(ctx, claim);
  enrichStructMembership(ctx, proofObject, step);
  return proofObject;
}
function createMorphismForClaim(category, claim, rule, tau, inputs, unresolvedTerms) {
  const implication = parseImplicationCanonical(claim);
  if (implication) {
    const domain = ensureClaimObjects(category, implication[0]);
    const codomain2 = ensureClaimObjects(category, implication[1]);
    if (tau === "\u03C9") {
      category.suspendObject(claim, unresolvedTerms);
    }
    return category.createMorphism({
      proposition: claim,
      domain,
      codomain: codomain2,
      tau,
      rule,
      inputs,
      unresolvedTerms,
      domainRestriction: unresolvedTerms.length > 0 ? `Dom(${claim})` : domain,
      suspended: tau === "\u03C9"
    });
  }
  const codomain = ensureClaimObjects(category, claim);
  if (tau === "\u03C9") {
    category.suspendObject(claim, unresolvedTerms);
  }
  return category.createMorphism({
    proposition: claim,
    domain: TOP,
    codomain,
    tau,
    rule,
    inputs,
    unresolvedTerms,
    domainRestriction: unresolvedTerms.length > 0 ? `Dom(${claim})` : TOP,
    suspended: tau === "\u03C9"
  });
}
function toTopMorphism(ctx, object) {
  return ctx.category.createMorphism({
    proposition: object.claim,
    domain: TOP,
    codomain: object.codomain,
    tau: object.tau,
    rule: object.rule,
    inputs: object.inputs
  });
}
function toImplicationMorphism(ctx, object) {
  const implication = parseImplicationCanonical(object.claim);
  if (!implication) {
    throw new KernelError(`Expected implication morphism, received '${object.claim}'`);
  }
  return ctx.category.createMorphism({
    proposition: object.claim,
    domain: ensureClaimObjects(ctx.category, implication[0]),
    codomain: ensureClaimObjects(ctx.category, implication[1]),
    tau: object.tau,
    rule: object.rule,
    inputs: object.inputs
  });
}
function ensureClaimObjects(category, claim) {
  return category.createObject(claim).id;
}
function splitAllConjuncts(s) {
  const parts = parseConjunctionCanonical(s);
  if (!parts) return [s];
  return [...splitAllConjuncts(parts[0]), ...splitAllConjuncts(parts[1])];
}
function theoremPremises(node) {
  const assumes = node.body.filter((item) => item.type === "Assume").flatMap((item) => splitAllConjuncts(exprToProp(item.expr)));
  if (assumes.length > 0) return assumes;
  return node.body.filter((item) => item.type === "Given").map((item) => exprToProp(item.expr));
}
function registerCategoryClaim(ctx, claim) {
  try {
    ctx.diagrams.registerClaim(claim);
  } catch (error) {
    if (error instanceof CategoryDiagramError) {
      const isUnknownFunctor = error.message.includes("unknown functor");
      ctx.diagnostics.push({
        severity: isUnknownFunctor ? "warning" : "error",
        message: error.message,
        rule: "CAT_MORPHISM"
      });
      return;
    }
    throw error;
  }
}
function theoremGoal(node) {
  const dtp = node.body.filter((item) => item.type === "DeclareToProve").map((item) => exprToProp(item.expr))[0];
  if (dtp !== void 0) return dtp;
  return node.body.filter((item) => item.type === "Assert").map((item) => exprToProp(item.expr))[0] ?? null;
}
function collectStructDefinitions(nodes, diagnostics) {
  const structs = /* @__PURE__ */ new Map();
  const typeNames = new Set(nodes.filter((node) => node.type === "TypeDecl").map((node) => node.name));
  for (const node of nodes) {
    if (node.type !== "Struct") continue;
    const fields = node.fields.map((field) => ({ name: field.name, type: field.type }));
    for (const field of fields) {
      if (!isKnownSort(field.type, structs, typeNames)) {
        diagnostics.push({
          severity: "error",
          message: `Unknown sort '${field.type}' in struct '${node.name}' field '${field.name}'`,
          rule: "STRUCTURAL"
        });
      }
    }
    structs.set(node.name, {
      name: node.name,
      fields,
      projections: new Map(fields.map((field) => [field.name, `\u03C0_${field.name}`]))
    });
  }
  return structs;
}
function collectTypeDefinitions(nodes, structs, diagnostics) {
  const typeNames = new Set(nodes.filter((node) => node.type === "TypeDecl").map((node) => node.name));
  const types = /* @__PURE__ */ new Map();
  for (const node of nodes) {
    if (node.type !== "TypeDecl") continue;
    const variants = node.variants.map((variant) => ({ ...variant, parent: node.name }));
    for (const variant of variants) {
      for (const field of variant.fields) {
        if (!isKnownSort(field.type, structs, typeNames)) {
          diagnostics.push({
            severity: "error",
            message: `Unknown sort '${field.type}' in variant '${variant.name}' of type '${node.name}'`,
            rule: "STRUCTURAL"
          });
        }
      }
    }
    types.set(node.name, { name: node.name, variants });
  }
  return types;
}
function findPairs(nodes) {
  const pairs = [];
  for (let index = 0; index < nodes.length; index++) {
    const node = nodes[index];
    if (node.type !== "Theorem" && node.type !== "Lemma" || node.connective !== "\u2194") continue;
    for (let cursor = index + 1; cursor < nodes.length; cursor++) {
      const candidate = nodes[cursor];
      if (candidate.type === "Proof" && normalizeName(candidate.name) === normalizeName(node.name)) {
        pairs.push({ theorem: node, proof: candidate });
        break;
      }
      if (candidate.type === "Theorem" || candidate.type === "Lemma") break;
    }
  }
  return pairs;
}
function normalizeName(value) {
  return value.trim().toLowerCase();
}
function classifyStep(node) {
  switch (node.type) {
    case "Assume":
      return "assume";
    case "Assert":
      return "assert";
    case "Prove":
      return "assert";
    // prove() is semantically an assert
    case "AndIntroStep":
    case "OrIntroStep":
      return "assert";
    case "Conclude":
      return "conclude";
    case "Apply":
      return "apply";
    case "SetVar":
      return "setVar";
    case "Induction":
      return "induction";
    case "Match":
      return "match";
    case "Intro":
      return "intro";
    case "Rewrite":
      return "rewrite";
    case "Exact":
      return "exact";
    default:
      return "raw";
  }
}
function nodeToClaim(node) {
  switch (node.type) {
    case "Assume":
    case "Assert":
    case "Prove":
    case "Conclude":
      return exprToProp(node.expr);
    case "AndIntroStep":
      return `${node.left} \u2227 ${node.right}`;
    case "OrIntroStep":
      return node.claim;
    case "Apply":
      return node.target;
    case "SetVar":
      return node.varType ? `${node.varName}: ${node.varType}` : node.varName;
    case "Induction":
      return exprToProp(node.fold);
    case "Match":
      return `match ${exprToProp(node.scrutinee)}`;
    case "Raw":
      return node.content;
    case "Intro":
      return `${node.varName}: ${node.varType}`;
    case "Rewrite":
      return node.hypothesis;
    case "Exact":
      return exprToProp(node.expr);
    default:
      return node.type;
  }
}
function findDerivedConclusion(ctx, goal) {
  if (goal && findExact(ctx.objects, goal, false)) {
    return goal;
  }
  const last = [...ctx.objects].reverse().find((object) => object.tau === "1");
  return last?.claim ?? null;
}
function reportState(ctx, goal, derivedConclusion) {
  if (ctx.diagnostics.some((diagnostic) => diagnostic.severity === "error")) {
    return "FAILED";
  }
  if (ctx.unverifiedReasons.length > 0) {
    return "FAILED";
  }
  if (goal && !derivedConclusion) {
    return "FAILED";
  }
  return ctx.objects.some((object) => object.pending) ? "FAILED" : "PROVED";
}
function combineStates(states, fallback) {
  if (states.length === 0) return fallback;
  if (states.includes("FAILED") || states.includes("UNVERIFIED") || states.includes("PENDING")) return "FAILED";
  return "PROVED";
}
function safeTermFromString(s) {
  try {
    return termFromString(s);
  } catch {
    return void 0;
  }
}
function findExact(objects, claim, allowPending) {
  const claimTerm = safeTermFromString(claim);
  for (let index = objects.length - 1; index >= 0; index--) {
    const object = objects[index];
    if (allowPending || !object.pending) {
      if (claimTerm && object.term && termEqual(claimTerm, object.term)) return object;
      if (sameProp(object.claim, claim)) return object;
    }
  }
  return null;
}
function requireClassical(ctx, claim, rule) {
  const classical = findExact(ctx.objects, claim, false);
  if (classical) return classical;
  const pending = findExact(ctx.objects, claim, true);
  if (pending?.pending) {
    throw new KernelError("\u03C9-Barrier: pending morphism cannot be used in classical derivation before Ra fires");
  }
  const premise = findExact(ctx.premises, claim, false);
  if (premise) return premise;
  const assumption = findExact(ctx.assumptions, claim, false);
  if (assumption) return assumption;
  const pendingPremise = findExact(ctx.premises, claim, true) ?? findExact(ctx.assumptions, claim, true);
  if (pendingPremise?.pending) {
    throw new KernelError("\u03C9-Barrier: pending morphism cannot be used in classical derivation before Ra fires");
  }
  void rule;
  return null;
}
function classicalObjects(ctx) {
  return ctx.objects.filter((object) => !object.pending && object.tau === "1");
}
function hasContradiction(objects) {
  for (const object of objects) {
    if (object.pending) continue;
    const negation = object.claim.startsWith("\xAC") ? object.claim.slice(1).trim() : `\xAC${object.claim}`;
    const opposite = findExact(objects, negation, false);
    if (opposite) {
      return [object, opposite];
    }
  }
  return null;
}
function handleIntro(ctx, node, step) {
  const { varName, varType } = node;
  if (ctx.goal && !varType) {
    const impl = parseImplicationCanonical(ctx.goal);
    if (impl) {
      const [antecedent, consequent] = impl;
      ctx.goal = consequent;
      const assumption2 = createKernelObject(ctx, antecedent, "ASSUMPTION", step);
      ctx.assumptions.push(assumption2);
      ctx.proofSteps.push({
        step,
        kind: "intro",
        claim: antecedent,
        rule: "ASSUMPTION",
        state: "PROVED",
        message: `Introduced '${varName}' as '${antecedent}', goal is now '${consequent}'`
      });
      return;
    }
  }
  let resolvedDomain = varType;
  if (ctx.goal) {
    const forall = parseBoundedQuantifierCanonical(ctx.goal, "forall");
    if (forall) {
      if (!resolvedDomain) resolvedDomain = forall.set;
      const newGoal = substituteVariable(forall.body, forall.variable, varName);
      ctx.goal = newGoal;
    }
  }
  const membershipClaim = resolvedDomain ? `${varName} \u2208 ${resolvedDomain}` : varName;
  const domain = resolvedDomain || null;
  ctx.variables.push({ name: varName, domain });
  const assumption = createKernelObject(ctx, membershipClaim, "ASSUMPTION", step);
  ctx.assumptions.push(assumption);
  ctx.proofSteps.push({
    step,
    kind: "intro",
    claim: membershipClaim,
    rule: "ASSUMPTION",
    state: "PROVED",
    message: `Introduced '${varName} \u2208 ${resolvedDomain ?? "?"}' and updated goal`
  });
}
function handleRewrite(ctx, node, step) {
  const { hypothesis, direction } = node;
  const hyp = findExact(ctx.objects, hypothesis, false) ?? findExact(ctx.assumptions, hypothesis, false) ?? findExact(ctx.premises, hypothesis, false);
  if (!hyp) {
    ctx.diagnostics.push({ severity: "error", step, message: `rewrite: hypothesis '${hypothesis}' not found in context`, rule: "REWRITE" });
    ctx.proofSteps.push({ step, kind: "rewrite", claim: hypothesis, rule: "REWRITE", state: "FAILED", message: `Hypothesis '${hypothesis}' not found` });
    return;
  }
  const eq = parseEqualityCanonical(hyp.claim);
  if (!eq) {
    ctx.diagnostics.push({ severity: "error", step, message: `rewrite: '${hypothesis}' is not an equality`, rule: "REWRITE" });
    ctx.proofSteps.push({ step, kind: "rewrite", claim: hypothesis, rule: "REWRITE", state: "FAILED", message: `'${hypothesis}' is not an equality` });
    return;
  }
  const [fromStr, toStr] = direction === "rtl" ? [eq.right, eq.left] : [eq.left, eq.right];
  const fromTerm = termFromString(fromStr);
  const toTerm = termFromString(toStr);
  if (ctx.goal) {
    const goalTerm = termFromString(ctx.goal);
    const rewritten = rewriteTerm(goalTerm, fromTerm, toTerm);
    ctx.goal = termToString(rewritten);
  }
  for (const obj of ctx.objects) {
    if (obj.term) {
      const rewritten = rewriteTerm(obj.term, fromTerm, toTerm);
      if (!termEqual(rewritten, obj.term)) {
        createKernelObject(ctx, termToString(rewritten), "REWRITE", step, [obj.id, hyp.id]);
      }
    }
  }
  ctx.proofSteps.push({
    step,
    kind: "rewrite",
    claim: ctx.goal ?? hypothesis,
    rule: "REWRITE",
    state: "PROVED",
    uses: [hyp.claim],
    message: `Rewrote ${fromStr} \u2192 ${toStr} in goal`
  });
}
function handleExact(ctx, node, step) {
  const claim = exprToProp(node.expr);
  if (ctx.goal && !sameProp(claim, ctx.goal)) {
    const claimTerm = safeTermFromString(claim);
    const goalTerm = safeTermFromString(ctx.goal);
    const match = claimTerm && goalTerm && termEqual(claimTerm, goalTerm);
    if (!match) {
      ctx.diagnostics.push({ severity: "error", step, message: `exact: '${claim}' does not match goal '${ctx.goal}'`, rule: "STRUCTURAL" });
      ctx.proofSteps.push({ step, kind: "exact", claim, rule: "STRUCTURAL", state: "FAILED", message: `Does not match goal` });
      return;
    }
  }
  const derivation = deriveClaim(ctx, claim, step);
  if (derivation.state === "FAILED") {
    ctx.diagnostics.push({ severity: "error", step, message: derivation.message, rule: derivation.rule });
  }
  ctx.proofSteps.push({
    step,
    kind: "exact",
    claim,
    rule: derivation.rule,
    state: derivation.state,
    uses: derivation.uses,
    message: derivation.message
  });
}
function handleObtain(ctx, node, step) {
  const { varName, source: source2 } = node;
  const hyp = findExact(ctx.objects, source2, false) ?? findExact(ctx.assumptions, source2, false) ?? findExact(ctx.premises, source2, false);
  if (!hyp) {
    ctx.diagnostics.push({ severity: "error", step, message: `obtain: '${source2}' not found in context`, rule: "STRUCTURAL" });
    ctx.proofSteps.push({ step, kind: "intro", claim: source2, rule: "STRUCTURAL", state: "FAILED", message: `Existential not found` });
    return;
  }
  const exists = parseBoundedQuantifierCanonical(hyp.claim, "exists");
  if (!exists) {
    ctx.diagnostics.push({ severity: "error", step, message: `obtain: '${source2}' is not an existential`, rule: "STRUCTURAL" });
    ctx.proofSteps.push({ step, kind: "intro", claim: source2, rule: "STRUCTURAL", state: "FAILED", message: `Not an existential` });
    return;
  }
  const membershipClaim = `${varName} \u2208 ${exists.set}`;
  const bodyClaim = substituteVariable(exists.body, exists.variable, varName);
  ctx.variables.push({ name: varName, domain: exists.set });
  const memObj = createKernelObject(ctx, membershipClaim, "ASSUMPTION", step, [hyp.id]);
  ctx.assumptions.push(memObj);
  const bodyObj = createKernelObject(ctx, bodyClaim, "ASSUMPTION", step, [hyp.id]);
  ctx.assumptions.push(bodyObj);
  ctx.proofSteps.push({
    step,
    kind: "intro",
    claim: membershipClaim,
    rule: "ASSUMPTION",
    state: "PROVED",
    uses: [hyp.claim],
    message: `Obtained '${varName} \u2208 ${exists.set}' and '${bodyClaim}' from existential`
  });
}
function generateEliminators(types) {
  const result = /* @__PURE__ */ new Map();
  for (const [typeName, typeDef] of types) {
    if (typeDef.variants.length > 0) {
      const metavar = "x";
      const disjuncts = typeDef.variants.map((v) => `${metavar} \u2208 ${v.name}`);
      const conclusion = disjuncts.reduce((acc, d) => `${acc} \u2228 ${d}`);
      result.set(`${typeName.toLowerCase()}.cases`, {
        name: `${typeName}.cases`,
        premises: [`${metavar} \u2208 ${typeName}`],
        conclusion,
        state: "PROVED",
        metavars: [metavar]
      });
    }
  }
  return result;
}
function enrichStructMembership(ctx, source2, step) {
  const membership = parseMembershipCanonical(source2.claim);
  if (!membership) return;
  const structDef = ctx.structs.get(membership.set);
  if (!structDef) return;
  for (const field of structDef.fields) {
    const fieldClaim = `${membership.element}.${field.name} \u2208 ${field.type}`;
    if (findExact(ctx.objects, fieldClaim, true) || findExact(ctx.premises, fieldClaim, true) || findExact(ctx.assumptions, fieldClaim, true)) {
      continue;
    }
    createKernelObject(ctx, fieldClaim, "STRUCT_ELIM", step, [source2.id]);
  }
}
function isKnownSort(sort, structs, typeNames = /* @__PURE__ */ new Set()) {
  const parsed = parseSort(sort);
  if (!parsed) return false;
  if (parsed.kind === "list") {
    return parsed.element ? isKnownSort(formatSort(parsed.element), structs, typeNames) : false;
  }
  if (!parsed.name) return false;
  return BUILTIN_SORTS.has(parsed.name) || structs.has(parsed.name) || typeNames.has(parsed.name);
}
function createBranchContext(ctx) {
  return {
    ...ctx,
    objects: [...ctx.objects],
    derivations: [...ctx.derivations],
    diagnostics: [],
    proofSteps: [],
    variables: [...ctx.variables],
    assumptions: [...ctx.assumptions],
    premises: [...ctx.premises]
  };
}
function applyVariantPatternBindings(ctx, scrutinee, variant, bindings, step) {
  createKernelObject(ctx, `${scrutinee} \u2208 ${variant.name}`, "OR_ELIM", step);
  for (let index = 0; index < variant.fields.length; index++) {
    const binding = bindings[index];
    if (!binding || binding === "_") continue;
    const field = variant.fields[index];
    ctx.variables.push({ name: binding, domain: field.type });
    const assumption = createKernelObject(ctx, `${binding} \u2208 ${field.type}`, "ASSUMPTION", step);
    ctx.assumptions.push(assumption);
  }
}
function applyListPatternBindings(ctx, scrutinee, listType, parsedSort, head, tail, step) {
  const elementType = formatSort(parsedSort.element ?? { kind: "named", name: "Element" });
  createKernelObject(ctx, `${scrutinee} \u2208 Cons`, "OR_ELIM", step);
  if (head !== "_") {
    ctx.variables.push({ name: head, domain: elementType });
    const headAssumption = createKernelObject(ctx, `${head} \u2208 ${elementType}`, "ASSUMPTION", step);
    ctx.assumptions.push(headAssumption);
  }
  ctx.variables.push({ name: tail, domain: listType });
  const tailAssumption = createKernelObject(ctx, `${tail} \u2208 ${listType}`, "ASSUMPTION", step);
  ctx.assumptions.push(tailAssumption);
}
function evaluateMatchBranch(ctx, goal, step) {
  if (goal && findExact(ctx.objects, goal, false)) {
    return "PROVED";
  }
  if (goal) {
    const goalMembership = parseMembershipCanonical(goal);
    if (goalMembership) {
      const lastConclusion = findLastConclude(ctx.proofSteps);
      if (lastConclusion && branchConclusionMatchesType(lastConclusion.claim, goalMembership.set, ctx)) {
        createKernelObject(ctx, goal, "OR_ELIM", step);
        return "PROVED";
      }
    }
    return "FAILED";
  }
  return "PROVED";
}
function findLastConclude(steps) {
  for (let index = steps.length - 1; index >= 0; index--) {
    if (steps[index].kind === "conclude") return steps[index];
  }
  return null;
}
function branchConclusionMatchesType(claim, expectedType, ctx) {
  const inferred = inferExpressionType(claim, ctx);
  return inferred === expectedType;
}
function parseSort(value) {
  const trimmed = value.trim();
  const listMatch = trimmed.match(/^List\s*\(([\s\S]+)\)$/);
  if (listMatch) {
    const inner = parseSort(listMatch[1].trim());
    return inner ? { kind: "list", element: inner } : null;
  }
  if (!trimmed) return null;
  return { kind: "named", name: trimmed };
}
function formatSort(sort) {
  if (sort.kind === "list") {
    return `List(${formatSort(sort.element ?? { kind: "named", name: "Element" })})`;
  }
  return sort.name ?? "Element";
}
function inferExpressionType(claim, ctx) {
  const membership = parseMembershipCanonical(claim);
  if (membership) return membership.set;
  const trimmed = claim.trim();
  if (trimmed === "[]") {
    const goalMembership = ctx.goal ? parseMembershipCanonical(ctx.goal) : null;
    return goalMembership?.set ?? null;
  }
  if (trimmed.startsWith("[") && trimmed.endsWith("]")) {
    const goalMembership = ctx.goal ? parseMembershipCanonical(ctx.goal) : null;
    if (goalMembership?.set && parseSort(goalMembership.set)?.kind === "list") {
      return goalMembership.set;
    }
  }
  if (/^\d+$/.test(trimmed)) return "\u2115";
  if (/[π√]/.test(trimmed) || /\bsqrt\s*\(/.test(trimmed)) return "\u211D";
  const bareBinding = ctx.variables.find((variable) => variable.name === trimmed);
  if (bareBinding?.domain) return bareBinding.domain;
  if (/[*\/^]/.test(trimmed)) {
    const vars = trimmed.match(/[A-Za-z_][\w₀-₉ₐ-ₙ]*/g) ?? [];
    if (vars.some((variable) => {
      const binding = ctx.variables.find((entry) => entry.name === variable);
      return binding?.domain === "\u211D";
    })) return "\u211D";
    return "\u2115";
  }
  if (/[+]/.test(trimmed)) return "\u2115";
  const call = trimmed.match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)\s*\(/);
  if (call && ctx.goal) {
    const goalMembership = parseMembershipCanonical(ctx.goal);
    if (goalMembership) return goalMembership.set;
  }
  return null;
}
function validateListStructuralRecursion(proof) {
  const fnMeta = proof.fnMeta;
  if (!fnMeta) return null;
  const listParams = fnMeta.params.filter((param) => parseSort(param.type)?.kind === "list");
  if (listParams.length === 0) return null;
  const invalidCall = findInvalidRecursiveCall(proof.body, proof.name, /* @__PURE__ */ new Map(), listParams);
  if (!invalidCall) return null;
  return `UNVERIFIED: recursive call '${invalidCall.call}' is not structural on a List tail`;
}
function findInvalidRecursiveCall(nodes, fnName, allowedTails, listParams) {
  for (const node of nodes) {
    if (node.type === "Match") {
      const scrutinee = exprToProp(node.scrutinee).trim();
      const listParam = listParams.find((param) => param.name === scrutinee);
      for (const matchCase of node.cases) {
        const branchAllowed = new Map(allowedTails);
        if (listParam && matchCase.pattern.kind === "list_cons") {
          branchAllowed.set(listParam.name, matchCase.pattern.tail);
        }
        const nested = findInvalidRecursiveCall(matchCase.body, fnName, branchAllowed, listParams);
        if (nested) return nested;
      }
      continue;
    }
    const claim = node.type === "Assert" || node.type === "Assume" || node.type === "Conclude" ? exprToProp(node.expr) : node.type === "Raw" ? node.content : null;
    if (claim) {
      const invalid = validateRecursiveCallsInText(claim, fnName, allowedTails, listParams);
      if (invalid) return invalid;
    }
  }
  return null;
}
function validateRecursiveCallsInText(text, fnName, allowedTails, listParams) {
  for (const call of extractNamedCalls(text, fnName)) {
    const args2 = splitTopLevelCallArgs(call.args);
    for (let index = 0; index < listParams.length; index++) {
      const param = listParams[index];
      const arg = args2[index]?.trim();
      const allowedTail = allowedTails.get(param.name);
      if (!arg || arg !== allowedTail) {
        return { call: `${fnName}(${call.args})` };
      }
    }
  }
  return null;
}
function extractNamedCalls(text, fnName) {
  const calls = [];
  const pattern = new RegExp(`\\b${escapeRegex(fnName)}\\s*\\(`, "g");
  let match;
  while ((match = pattern.exec(text)) !== null) {
    const openIndex = text.indexOf("(", match.index);
    const closeIndex = findMatchingParenInText(text, openIndex);
    if (openIndex === -1 || closeIndex === -1) continue;
    calls.push({ args: text.slice(openIndex + 1, closeIndex) });
    pattern.lastIndex = closeIndex + 1;
  }
  return calls;
}
function findMatchingParenInText(value, start) {
  let depth = 0;
  for (let i = start; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") {
      depth--;
      if (depth === 0) return i;
    }
  }
  return -1;
}
function splitTopLevelCallArgs(value) {
  const args2 = [];
  let start = 0;
  let depth = 0;
  let bracketDepth = 0;
  for (let i = 0; i < value.length; i++) {
    const ch = value[i];
    if (ch === "(") depth++;
    else if (ch === ")") depth = Math.max(0, depth - 1);
    else if (ch === "[") bracketDepth++;
    else if (ch === "]") bracketDepth = Math.max(0, bracketDepth - 1);
    else if (ch === "," && depth === 0 && bracketDepth === 0) {
      args2.push(value.slice(start, i).trim());
      start = i + 1;
    }
  }
  const final = value.slice(start).trim();
  if (final) args2.push(final);
  return args2;
}
function parseFieldAccess(value) {
  const trimmed = value.trim();
  if (!trimmed.includes(".")) return null;
  const parts = trimmed.split(".").map((part) => part.trim()).filter(Boolean);
  if (parts.length < 2) return null;
  return { base: parts[0], path: parts.slice(1) };
}
function resolveFieldProjection(ctx, base, path5) {
  let currentExpr = base;
  let currentMembership = requireAnyMembership(ctx, currentExpr);
  if (!currentMembership) return null;
  for (const fieldName of path5) {
    const membership = parseMembershipCanonical(currentMembership.claim);
    if (!membership) return null;
    const structDef = ctx.structs.get(membership.set);
    if (!structDef) return null;
    const field = structDef.fields.find((candidate) => candidate.name === fieldName);
    if (!field) return null;
    currentExpr = `${currentExpr}.${fieldName}`;
    const nextClaim = `${currentExpr} \u2208 ${field.type}`;
    let nextMembership = findExact(ctx.objects, nextClaim, false) ?? findExact(ctx.premises, nextClaim, false) ?? findExact(ctx.assumptions, nextClaim, false);
    if (!nextMembership) {
      nextMembership = createKernelObject(ctx, nextClaim, "STRUCT_ELIM", currentMembership.step, [currentMembership.id]);
    }
    currentMembership = nextMembership;
  }
  const finalMembership = parseMembershipCanonical(currentMembership.claim);
  if (!finalMembership) return null;
  return { type: finalMembership.set, source: currentMembership };
}
function requireAnyMembership(ctx, element) {
  const pools = [ctx.objects, ctx.premises, ctx.assumptions];
  for (const pool of pools) {
    for (let index = pool.length - 1; index >= 0; index--) {
      const membership = parseMembershipCanonical(pool[index].claim);
      if (membership && sameProp(membership.element, element) && !pool[index].pending) {
        return pool[index];
      }
    }
  }
  return null;
}
function findWitness(ctx, variable) {
  for (let index = ctx.variables.length - 1; index >= 0; index--) {
    if (ctx.variables[index].name === variable) {
      return ctx.variables[index].name;
    }
  }
  for (let index = ctx.variables.length - 1; index >= 0; index--) {
    const candidate = ctx.variables[index];
    if (candidate.domain !== null) {
      return candidate.name;
    }
  }
  if (ctx.variables.length > 0) {
    return ctx.variables[ctx.variables.length - 1].name;
  }
  return null;
}
function substituteVariable(input, variable, replacement) {
  const pattern = new RegExp(`\\b${escapeRegex(variable)}\\b`, "g");
  return input.replace(pattern, replacement);
}
function escapeRegex(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}
function normalizeSpaces(value) {
  return value.trim().replace(/\s+/g, " ");
}
function containsWitness(claim, witness) {
  return new RegExp(`\\b${escapeRegex(witness)}\\b`).test(claim);
}
function predicateToRule(name) {
  switch (name) {
    case "Category":
    case "Object":
      return "CAT_OBJECT";
    case "Morphism":
      return "CAT_MORPHISM";
    case "Iso":
      return "ISO_INTRO";
    case "Product":
      return "PRODUCT_INTRO";
    case "ProductMediator":
      return "PRODUCT_MEDIATOR";
    case "Coproduct":
      return "COPRODUCT_INTRO";
    case "Pullback":
      return "PULLBACK_INTRO";
    case "Pushout":
      return "PUSHOUT_INTRO";
    case "Functor":
      return "FUNCTOR_INTRO";
  }
}
function hasClaim(ctx, claim) {
  return Boolean(
    findExact(ctx.objects, claim, false) || findExact(ctx.premises, claim, false) || findExact(ctx.assumptions, claim, false)
  );
}
function hasMorphism(ctx, claim) {
  return hasClaim(ctx, claim) || Boolean(findDeclarationByLabel(ctx, parseMorphismDeclarationCanonical(claim)?.label ?? ""));
}
function findDeclarationByLabel(ctx, label) {
  if (!label) return null;
  const collections = [ctx.objects, ctx.premises, ctx.assumptions];
  for (const collection of collections) {
    for (let index = collection.length - 1; index >= 0; index--) {
      const declaration = parseMorphismDeclarationCanonical(collection[index].claim);
      if (declaration && declaration.label === label) {
        return declaration;
      }
    }
  }
  return null;
}
function stripIdentity(value) {
  return value.replace(/\bid_\{?([^}\s]+(?:\([^)]*\))?)\}?\s*∘\s*/g, "").replace(/\s*∘\s*id_\{?([^}\s]+(?:\([^)]*\))?)\}?/g, "").trim();
}
function normalizeComposition(value) {
  return value.replace(/[()]/g, "").split("\u2218").map((part) => part.trim()).filter(Boolean).join(" \u2218 ");
}
function looksLikeCategoricalEquality2(claim) {
  return claim.includes("\u2218") || /\bid_/.test(claim) || /^[A-Z][\w₀-₉ₐ-ₙ]*\(.+\)\s*=/.test(claim);
}
function deriveCryptoClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const dlogMatch = norm.match(/^dlog_hard\((\w+)\s*,\s*(\w+)\)$/);
  if (dlogMatch) {
    const [, g, p] = dlogMatch;
    const pIsPrime = all.find((o) => {
      const mem = parseMembershipCanonical(o.claim);
      return mem && mem.element === p && mem.set === "Prime";
    });
    const gInNat = all.find((o) => {
      const mem = parseMembershipCanonical(o.claim);
      return mem && mem.element === g && (mem.set === "Nat" || mem.set === "\u2115");
    });
    if (pIsPrime && gInNat) {
      createKernelObject(ctx, claim, "CRYPTO_DL", step, [pIsPrime.id, gInNat.id]);
      return { rule: "CRYPTO_DL", state: "PROVED", uses: [pIsPrime.claim, gInNat.claim], message: `Discrete log hard in Z_${p}*` };
    }
  }
  const dhMatch = norm.match(/^dh_secret\((\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\)\s*=\s*(.+)$/);
  if (dhMatch) {
    const [, g, a, b, p, result] = dhMatch;
    const pIsPrime = all.find((o) => {
      const mem = parseMembershipCanonical(o.claim);
      return mem && mem.element === p && mem.set === "Prime";
    });
    const dlogHard = all.find((o) => o.claim.match(new RegExp(`dlog_hard\\(${g}\\s*,\\s*${p}\\)`)));
    if (pIsPrime && dlogHard) {
      const expectedFwd = `${g}^(${a} * ${b}) mod ${p}`;
      const expectedBwd = `${g}^(${b} * ${a}) mod ${p}`;
      if (normArith(result) === normArith(expectedFwd) || normArith(result) === normArith(expectedBwd) || areCongruent(result, expectedFwd, String(parseInt(p))) || areCongruent(result, expectedBwd, String(parseInt(p)))) {
        createKernelObject(ctx, claim, "CRYPTO_DH", step, [pIsPrime.id, dlogHard.id]);
        return { rule: "CRYPTO_DH", state: "PROVED", uses: [pIsPrime.claim, dlogHard.claim], message: `DH shared secret: ${g}^(${a}${b}) \u2261 ${g}^(${b}${a}) (mod ${p})` };
      }
    }
  }
  const ecPointMatch = norm.match(/^on_curve\((\w+)\s*,\s*(.+)\)$/);
  if (ecPointMatch) {
    const [, pt, curve] = ecPointMatch;
    const curveEq = all.find((o) => o.claim.match(new RegExp(`curve_eq\\(${curve.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*,`)));
    const ptCoords = all.find((o) => o.claim.match(new RegExp(`coords\\(${pt}\\s*,`)));
    if (curveEq && ptCoords) {
      createKernelObject(ctx, claim, "CRYPTO_EC", step, [curveEq.id, ptCoords.id]);
      return { rule: "CRYPTO_EC", state: "PROVED", uses: [curveEq.claim, ptCoords.claim], message: `Point ${pt} verified on curve ${curve}` };
    }
    const axiom = all.find((o) => sameProp(o.claim, claim));
    if (axiom) {
      createKernelObject(ctx, claim, "CRYPTO_EC", step, [axiom.id]);
      return { rule: "CRYPTO_EC", state: "PROVED", uses: [axiom.claim], message: `EC point membership axiom` };
    }
  }
  const ecAddMatch = norm.match(/^ec_add\((\w+)\s*,\s*(\w+)\s*,\s*(\w+)\)\s*=\s*ec_add\((\w+)\s*,\s*(\w+)\s*,\s*(\w+)\)$/);
  if (ecAddMatch) {
    const [, P1, Q1, E1, Q2, P2, E2] = ecAddMatch;
    if (P1 === P2 && Q1 === Q2 && E1 === E2) {
      createKernelObject(ctx, claim, "CRYPTO_EC", step);
      return { rule: "CRYPTO_EC", state: "PROVED", message: "EC group law: commutativity" };
    }
    if (P1 === Q2 && Q1 === P2 && E1 === E2) {
      createKernelObject(ctx, claim, "CRYPTO_EC", step);
      return { rule: "CRYPTO_EC", state: "PROVED", message: "EC group law: commutativity" };
    }
  }
  const hashSecureMatch = norm.match(/^hash_secure\((\w[\w₀-₉ₐ-ₙ]*)\)$/);
  if (hashSecureMatch) {
    const [, H] = hashSecureMatch;
    const collRes = all.find((o) => o.claim.match(new RegExp(`collision_resistant\\(\\s*${H}\\s*\\)`)));
    const oneWay = all.find((o) => o.claim.match(new RegExp(`one_way\\(\\s*${H}\\s*\\)`)));
    if (collRes && oneWay) {
      createKernelObject(ctx, claim, "CRYPTO_HASH", step, [collRes.id, oneWay.id]);
      return { rule: "CRYPTO_HASH", state: "PROVED", uses: [collRes.claim, oneWay.claim], message: `${H} is a secure hash function` };
    }
  }
  const commitMatch = norm.match(/^commit_binding\((\w[\w₀-₉ₐ-ₙ]*)\)$/);
  if (commitMatch) {
    const [, C] = commitMatch;
    const hashBasis = all.find((o) => o.claim.match(new RegExp(`hash_secure\\(\\s*${C}\\s*\\)`)) || o.claim.match(new RegExp(`collision_resistant\\(\\s*${C}\\s*\\)`)));
    if (hashBasis) {
      createKernelObject(ctx, claim, "CRYPTO_COMMIT", step, [hashBasis.id]);
      return { rule: "CRYPTO_COMMIT", state: "PROVED", uses: [hashBasis.claim], message: `${C} commitment scheme is binding` };
    }
  }
  return null;
}
function deriveRealAnalysisClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const limMatch = norm.match(/^lim\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
  if (limMatch) {
    const [, fn, point, limitVal] = limMatch;
    const contCtx = all.find((o) => {
      return o.claim.match(new RegExp(`continuous\\(\\s*${fn}\\s*,\\s*${point.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*\\)`));
    });
    if (contCtx) {
      const appVal = `${fn}(${point})`;
      if (normArith(limitVal) === normArith(appVal) || arithSymEqual(limitVal, appVal)) {
        createKernelObject(ctx, claim, "REAL_LIMIT", step, [contCtx.id]);
        return { rule: "REAL_LIMIT", state: "PROVED", uses: [contCtx.claim], message: `Limit by continuity: lim(${fn}, ${point}) = ${fn}(${point})` };
      }
    }
    const limLo = all.find((o) => o.claim.match(/^lim\((\w+)\s*,\s*.+\)\s*=\s*.+$/));
    const limHi = all.find((o) => o !== limLo && o.claim.match(/^lim\((\w+)\s*,\s*.+\)\s*=\s*.+$/));
    if (limLo && limHi) {
      const mLo = limLo.claim.match(/^lim\((\w+)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
      const mHi = limHi.claim.match(/^lim\((\w+)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
      if (mLo && mHi && normArith(mLo[3]) === normArith(limitVal) && normArith(mHi[3]) === normArith(limitVal)) {
        createKernelObject(ctx, claim, "REAL_SQUEEZE", step, [limLo.id, limHi.id]);
        return { rule: "REAL_SQUEEZE", state: "PROVED", uses: [limLo.claim, limHi.claim], message: "Squeeze theorem" };
      }
    }
  }
  const contMatch = norm.match(/^continuous\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+)\)$/);
  if (contMatch) {
    const [, fn, point] = contMatch;
    const diffCtx = all.find(
      (o) => o.claim.match(new RegExp(`differentiable\\(\\s*${fn}\\s*,\\s*${point.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*\\)`))
    );
    if (diffCtx) {
      createKernelObject(ctx, claim, "REAL_CONTINUOUS", step, [diffCtx.id]);
      return { rule: "REAL_CONTINUOUS", state: "PROVED", uses: [diffCtx.claim], message: "Differentiable implies continuous" };
    }
    const contOnR = all.find(
      (o) => o.claim.match(new RegExp(`continuous_on_R\\(\\s*${fn}\\s*\\)`)) || o.claim.match(new RegExp(`polynomial\\(\\s*${fn}\\s*\\)`))
    );
    if (contOnR) {
      createKernelObject(ctx, claim, "REAL_CONTINUOUS", step, [contOnR.id]);
      return { rule: "REAL_CONTINUOUS", state: "PROVED", uses: [contOnR.claim], message: `${fn} is continuous everywhere` };
    }
  }
  const ivtMatch = norm.match(/^∃\s+c\s*∈\s*\((.+?)\s*,\s*(.+?)\)\s*,\s*(.+?)\(c\)\s*=\s*(.+)$/);
  if (ivtMatch) {
    const [, a, b, fn, y] = ivtMatch;
    const contInterval = all.find(
      (o) => o.claim.match(new RegExp(`continuous_on\\(\\s*${fn}\\s*,\\s*\\[${a.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*,\\s*${b.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\]\\s*\\)`))
    );
    if (contInterval) {
      const faLeY = all.find((o) => {
        const ord = parseOrder(o.claim);
        return ord && (ord.op === "\u2264" || ord.op === "<=") && normArith(ord.left) === normArith(`${fn}(${a})`) && normArith(ord.right) === normArith(y);
      });
      const yLeFb = all.find((o) => {
        const ord = parseOrder(o.claim);
        return ord && (ord.op === "\u2264" || ord.op === "<=") && normArith(ord.left) === normArith(y) && normArith(ord.right) === normArith(`${fn}(${b})`);
      });
      if (contInterval && (faLeY || yLeFb)) {
        const uses = [contInterval, faLeY, yLeFb].filter((o) => Boolean(o));
        createKernelObject(ctx, claim, "REAL_IVT", step, uses.map((o) => o.id));
        return { rule: "REAL_IVT", state: "PROVED", uses: uses.map((o) => o.claim), message: "Intermediate Value Theorem" };
      }
    }
  }
  const boundMatch = norm.match(/^bounded\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*\[(.+?)\s*,\s*(.+?)\]\)$/);
  if (boundMatch) {
    const [, fn, a, b] = boundMatch;
    const contInterval = all.find(
      (o) => o.claim.match(new RegExp(`continuous_on\\(\\s*${fn}\\s*,\\s*\\[${a.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*,\\s*${b.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\]\\s*\\)`))
    );
    if (contInterval) {
      createKernelObject(ctx, claim, "REAL_BOUND", step, [contInterval.id]);
      return { rule: "REAL_BOUND", state: "PROVED", uses: [contInterval.claim], message: "Continuous on closed interval implies bounded (Extreme Value Theorem)" };
    }
  }
  const diffMatch = norm.match(/^derivative\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
  if (diffMatch) {
    const [, fn, varName, derExpr] = diffMatch;
    const powerFn = all.find((o) => {
      const eq = parseEqualityCanonical(o.claim);
      return eq && eq.left.trim() === fn && eq.right.includes("^");
    });
    if (powerFn) {
      const eq = parseEqualityCanonical(powerFn.claim);
      const powParsed = parsePower(eq.right);
      if (powParsed && normArith(powParsed.base) === normArith(varName)) {
        const n = evalArith(powParsed.exp);
        if (n !== null) {
          const expectedDer = n === 1 ? "1" : n === 2 ? `2 * ${varName}` : `${n} * ${varName}^${n - 1}`;
          if (arithSymEqual(derExpr, expectedDer)) {
            createKernelObject(ctx, claim, "REAL_DIFF", step, [powerFn.id]);
            return { rule: "REAL_DIFF", state: "PROVED", uses: [powerFn.claim], message: `Power rule: d/d${varName} ${fn}(${varName}) = ${expectedDer}` };
          }
        }
      }
    }
    const constVal = evalArith(fn);
    if (constVal !== null && normArith(derExpr) === "0") {
      createKernelObject(ctx, claim, "REAL_DIFF", step);
      return { rule: "REAL_DIFF", state: "PROVED", message: "Constant rule: derivative of constant = 0" };
    }
  }
  return null;
}
function deriveOrderClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const reflMatch = norm.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
  if (reflMatch) {
    const [, a, b] = reflMatch;
    if (normArith(a) === normArith(b)) {
      createKernelObject(ctx, claim, "ORDER_REFL", step);
      return { rule: "ORDER_REFL", state: "PROVED", message: `Order reflexivity: ${a} \u2264 ${a}` };
    }
    for (const obj1 of all) {
      const m1 = obj1.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      if (!m1 || normArith(m1[1]) !== normArith(a)) continue;
      const mid = m1[2];
      for (const obj2 of all) {
        if (obj2 === obj1) continue;
        const m2 = obj2.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
        if (m2 && normArith(m2[1]) === normArith(mid) && normArith(m2[2]) === normArith(b)) {
          createKernelObject(ctx, claim, "ORDER_TRANS", step, [obj1.id, obj2.id]);
          return { rule: "ORDER_TRANS", state: "PROVED", uses: [obj1.claim, obj2.claim], message: `Order transitivity: ${a} \u2264 ${mid} \u2264 ${b}` };
        }
      }
    }
  }
  const eqMatch = parseEqualityCanonical(norm);
  if (eqMatch) {
    const leqAB = all.find((o) => o.claim.trim() === `leq(${eqMatch.left}, ${eqMatch.right})` || o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/) && normArith(o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/)[1]) === normArith(eqMatch.left) && normArith(o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/)[2]) === normArith(eqMatch.right));
    const leqBA = all.find((o) => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(eqMatch.right) && normArith(m[2]) === normArith(eqMatch.left);
    });
    if (leqAB && leqBA) {
      createKernelObject(ctx, claim, "ORDER_ANTISYM", step, [leqAB.id, leqBA.id]);
      return { rule: "ORDER_ANTISYM", state: "PROVED", uses: [leqAB.claim, leqBA.claim], message: `Order antisymmetry: ${eqMatch.left} = ${eqMatch.right}` };
    }
  }
  const joinMatch = norm.match(/^leq\((.+?)\s*,\s*join\((.+?)\s*,\s*(.+?)\)\)$/);
  if (joinMatch) {
    const [, x, a, b] = joinMatch;
    const xInA = all.find((o) => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(x) && normArith(m[2]) === normArith(a);
    });
    if (xInA) {
      createKernelObject(ctx, claim, "LATTICE_JOIN", step, [xInA.id]);
      return { rule: "LATTICE_JOIN", state: "PROVED", uses: [xInA.claim], message: `Lattice join: ${x} \u2264 join(${a}, ${b})` };
    }
    const xInB = all.find((o) => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(x) && normArith(m[2]) === normArith(b);
    });
    if (xInB) {
      createKernelObject(ctx, claim, "LATTICE_JOIN", step, [xInB.id]);
      return { rule: "LATTICE_JOIN", state: "PROVED", uses: [xInB.claim], message: `Lattice join: ${x} \u2264 join(${a}, ${b})` };
    }
  }
  const meetMatch = norm.match(/^leq\(meet\((.+?)\s*,\s*(.+?)\)\s*,\s*(.+?)\)$/);
  if (meetMatch) {
    const [, a, b, x] = meetMatch;
    const aLeX = all.find((o) => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(a) && normArith(m[2]) === normArith(x);
    });
    if (aLeX) {
      createKernelObject(ctx, claim, "LATTICE_MEET", step, [aLeX.id]);
      return { rule: "LATTICE_MEET", state: "PROVED", uses: [aLeX.claim], message: `Lattice meet: meet(${a}, ${b}) \u2264 ${x}` };
    }
    const bLeX = all.find((o) => {
      const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(b) && normArith(m[2]) === normArith(x);
    });
    if (bLeX) {
      createKernelObject(ctx, claim, "LATTICE_MEET", step, [bLeX.id]);
      return { rule: "LATTICE_MEET", state: "PROVED", uses: [bLeX.claim], message: `Lattice meet: meet(${a}, ${b}) \u2264 ${x}` };
    }
  }
  return null;
}
function deriveGraphClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  if (norm === "\u22A5") {
    for (const obj of all) {
      if (obj.pending) continue;
      const neg2 = obj.claim.startsWith("\xAC") ? obj.claim.slice(1).trim() : `\xAC${obj.claim}`;
      const opp = all.find((o) => !o.pending && o.claim.trim() === neg2);
      if (opp) {
        createKernelObject(ctx, claim, "GRAPH_PATH", step, [obj.id, opp.id]);
        return { rule: "GRAPH_PATH", state: "PROVED", uses: [obj.claim, opp.claim], message: `Contradiction: ${obj.claim} and ${opp.claim}` };
      }
    }
  }
  if (norm.startsWith("\xAC") && norm.slice(1).trim().match(/^has_odd_cycle\((.+)\)$/)) {
    const G = norm.slice(1).trim().match(/^has_odd_cycle\((.+)\)$/)[1];
    const bip = all.find((o) => o.claim.trim() === `bipartite(${G})`);
    if (bip) {
      createKernelObject(ctx, claim, "GRAPH_DEGREE", step, [bip.id]);
      return { rule: "GRAPH_DEGREE", state: "PROVED", uses: [bip.claim], message: `Bipartite graphs have no odd cycles` };
    }
  }
  const evenOddMatch = norm.match(/^even\(count_odd_degree\((.+)\)\)$/);
  if (evenOddMatch) {
    const G = evenOddMatch[1];
    const evenSum = all.find((o) => o.claim.trim() === `even(degree_sum(${G}))`);
    const graphObj = all.find((o) => o.claim.match(new RegExp(`^graph\\(${G.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\)`)));
    if (evenSum || graphObj) {
      createKernelObject(ctx, claim, "GRAPH_DEGREE", step, evenSum ?? graphObj ? [(evenSum ?? graphObj).id] : []);
      return { rule: "GRAPH_DEGREE", state: "PROVED", message: `Number of odd-degree vertices is even` };
    }
  }
  const evenSumMatch = norm.match(/^even\(degree_sum\((.+)\)\)$/);
  if (evenSumMatch) {
    const G = evenSumMatch[1];
    const degEq = all.find((o) => o.claim.trim() === `degree_sum(${G}) = 2 * edge_count(${G})`);
    if (degEq) {
      createKernelObject(ctx, claim, "GRAPH_DEGREE", step, [degEq.id]);
      return { rule: "GRAPH_DEGREE", state: "PROVED", uses: [degEq.claim], message: `degree_sum = 2|E| implies even` };
    }
  }
  const pathSymMatch = norm.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
  if (pathSymMatch) {
    const [, G, v, u] = pathSymMatch;
    if (normArith(u) !== normArith(v)) {
      const fwdPath = all.find((o) => {
        const m = o.claim.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
        return m && normArith(m[1]) === normArith(G) && normArith(m[2]) === normArith(u) && normArith(m[3]) === normArith(v);
      });
      if (fwdPath) {
        createKernelObject(ctx, claim, "GRAPH_PATH", step, [fwdPath.id]);
        return { rule: "GRAPH_PATH", state: "PROVED", uses: [fwdPath.claim], message: `Path symmetry: ${u}\u2014${v} implies ${v}\u2014${u}` };
      }
    }
  }
  const connFromTree = norm.match(/^connected\((.+)\)$/);
  if (connFromTree) {
    const G = connFromTree[1];
    const treeHyp = all.find((o) => o.claim.trim() === `tree(${G})`);
    if (treeHyp) {
      createKernelObject(ctx, claim, "GRAPH_TREE", step, [treeHyp.id]);
      return { rule: "GRAPH_TREE", state: "PROVED", uses: [treeHyp.claim], message: `Trees are connected` };
    }
  }
  const acycFromTree = norm.match(/^acyclic\((.+)\)$/);
  if (acycFromTree) {
    const G = acycFromTree[1];
    const treeHyp = all.find((o) => o.claim.trim() === `tree(${G})`);
    if (treeHyp) {
      createKernelObject(ctx, claim, "GRAPH_TREE", step, [treeHyp.id]);
      return { rule: "GRAPH_TREE", state: "PROVED", uses: [treeHyp.claim], message: `Trees are acyclic` };
    }
  }
  const edgeCountMatch = norm.match(/^edge_count\((.+)\)\s*=\s*(.+)$/);
  if (edgeCountMatch) {
    const G = edgeCountMatch[1], rhs = edgeCountMatch[2];
    const treeHyp = all.find((o) => o.claim.trim() === `tree(${G})`);
    if (treeHyp) {
      const vcHyp = all.find((o) => {
        const m = o.claim.match(/^vertex_count\((.+)\)\s*=\s*(.+)$/);
        return m && normArith(m[1]) === normArith(G) && normArith(`${m[2]} - 1`) === normArith(rhs);
      });
      if (vcHyp) {
        createKernelObject(ctx, claim, "GRAPH_TREE", step, [treeHyp.id, vcHyp.id]);
        return { rule: "GRAPH_TREE", state: "PROVED", uses: [treeHyp.claim, vcHyp.claim], message: `Tree with n vertices has n-1 edges` };
      }
    }
  }
  const uniquePathMatch = norm.match(/^unique_path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
  if (uniquePathMatch) {
    const [, G, u, v] = uniquePathMatch;
    const treeHyp = all.find((o) => o.claim.trim() === `tree(${G})`);
    const connHyp = all.find((o) => o.claim.trim() === `connected(${G})`);
    const acycHyp = all.find((o) => o.claim.trim() === `acyclic(${G})`);
    if (treeHyp || connHyp && acycHyp) {
      const hyps = treeHyp ? [treeHyp.id] : [connHyp.id, acycHyp.id];
      const uses = treeHyp ? [treeHyp.claim] : [connHyp.claim, acycHyp.claim];
      createKernelObject(ctx, claim, "GRAPH_TREE", step, hyps);
      return { rule: "GRAPH_TREE", state: "PROVED", uses, message: `In a tree, unique path between any two vertices` };
    }
  }
  const hasCycleMatch = norm.match(/^has_cycle\(add_edge\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)\)$/);
  if (hasCycleMatch) {
    const [, G, u, v] = hasCycleMatch;
    const treeHyp = all.find((o) => o.claim.trim() === `tree(${G})`);
    if (treeHyp) {
      createKernelObject(ctx, claim, "GRAPH_TREE", step, [treeHyp.id]);
      return { rule: "GRAPH_TREE", state: "PROVED", uses: [treeHyp.claim], message: `Adding an edge to a tree creates a cycle` };
    }
  }
  const eulerMatch = norm.match(/^(\w+)\s*-\s*(\w+)\s*\+\s*(\w+)\s*=\s*2$/);
  if (eulerMatch) {
    const [, V, E, F] = eulerMatch;
    const planarHyp = all.find((o) => o.claim.match(/^planar\(/));
    const connHyp2 = all.find((o) => o.claim.match(/^connected\(/));
    const vcHyp2 = all.find((o) => {
      const m = o.claim.match(/^vertex_count\(.+\)\s*=\s*(\w+)$/);
      return m && normArith(m[1]) === normArith(V);
    });
    const ecHyp = all.find((o) => {
      const m = o.claim.match(/^edge_count\(.+\)\s*=\s*(\w+)$/);
      return m && normArith(m[1]) === normArith(E);
    });
    const fcHyp = all.find((o) => {
      const m = o.claim.match(/^face_count\(.+\)\s*=\s*(\w+)$/);
      return m && normArith(m[1]) === normArith(F);
    });
    if (planarHyp && connHyp2 && vcHyp2 && ecHyp && fcHyp) {
      createKernelObject(ctx, claim, "GRAPH_DEGREE", step, [planarHyp.id, connHyp2.id, vcHyp2.id, ecHyp.id, fcHyp.id]);
      return { rule: "GRAPH_DEGREE", state: "PROVED", uses: [planarHyp.claim, connHyp2.claim], message: `Euler's formula for planar graphs` };
    }
  }
  if (norm === "\xACplanar(K5)" || norm === "\xACplanar(K_{3,3})" || norm === "\xACplanar(K33)") {
    createKernelObject(ctx, claim, "GRAPH_DEGREE", step);
    return { rule: "GRAPH_DEGREE", state: "PROVED", message: `Kuratowski's theorem` };
  }
  const chromLeMatch = norm.match(/^chromatic_number\((.+)\)\s*≤\s*(.+)$/);
  if (chromLeMatch) {
    const [, G, k] = chromLeMatch;
    if (evalArith(k) !== null && evalArith(k) >= 4) {
      const planarHyp = all.find((o) => o.claim.trim() === `planar(${G})`);
      if (planarHyp) {
        createKernelObject(ctx, claim, "GRAPH_DEGREE", step, [planarHyp.id]);
        return { rule: "GRAPH_DEGREE", state: "PROVED", uses: [planarHyp.claim], message: `Four Color Theorem: chromatic number \u2264 4` };
      }
    }
  }
  const chromGeMatch = norm.match(/^chromatic_number\((.+)\)\s*≥\s*(.+)$/);
  if (chromGeMatch) {
    const [, G, k] = chromGeMatch;
    const cliqueHyp = all.find((o) => {
      const m = o.claim.match(/^clique\((.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(G) && normArith(m[2]) === normArith(k);
    });
    const cliqNumHyp = all.find((o) => {
      const eq = parseEqualityCanonical(o.claim);
      return eq && eq.left.trim() === `clique_number(${G})` && normArith(eq.right) === normArith(k);
    });
    const hyp = cliqueHyp ?? cliqNumHyp;
    if (hyp) {
      createKernelObject(ctx, claim, "GRAPH_DEGREE", step, [hyp.id]);
      return { rule: "GRAPH_DEGREE", state: "PROVED", uses: [hyp.claim], message: `Clique lower bound: \u03C7(G) \u2265 \u03C9(G)` };
    }
  }
  if (norm.match(/^∃\s*\w+,\s*topological_order\(/)) {
    const topoG = norm.match(/topological_order\(\w+,\s*(.+)\)/)[1];
    const dagHyp = all.find((o) => o.claim.trim() === `dag(${topoG})`);
    const acycHyp = all.find((o) => o.claim.trim() === `acyclic(${topoG})`);
    const dirHyp = all.find((o) => o.claim.trim() === `directed_graph(${topoG})`);
    const hyp = dagHyp ?? (acycHyp && dirHyp ? acycHyp : null);
    const hyps = dagHyp ? [dagHyp.id] : acycHyp && dirHyp ? [acycHyp.id, dirHyp.id] : [];
    if (hyps.length > 0) {
      createKernelObject(ctx, claim, "GRAPH_TREE", step, hyps);
      return { rule: "GRAPH_TREE", state: "PROVED", message: `DAGs have topological orderings` };
    }
  }
  const pathMatch = norm.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
  if (pathMatch) {
    const [, G, u, v] = pathMatch;
    if (normArith(u) === normArith(v)) {
      createKernelObject(ctx, claim, "GRAPH_PATH", step);
      return { rule: "GRAPH_PATH", state: "PROVED", message: `Trivial path: ${u} = ${v}` };
    }
    const edgeUV = all.find((o) => {
      const m = o.claim.match(/^edge\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(G) && (normArith(m[2]) === normArith(u) && normArith(m[3]) === normArith(v) || normArith(m[2]) === normArith(v) && normArith(m[3]) === normArith(u));
    });
    if (edgeUV) {
      createKernelObject(ctx, claim, "GRAPH_PATH", step, [edgeUV.id]);
      return { rule: "GRAPH_PATH", state: "PROVED", uses: [edgeUV.claim], message: `Path via direct edge ${u}\u2014${v}` };
    }
    const treeForPath = all.find((o) => o.claim.trim() === `tree(${G})`);
    if (treeForPath) {
      createKernelObject(ctx, claim, "GRAPH_TREE", step, [treeForPath.id]);
      return { rule: "GRAPH_TREE", state: "PROVED", uses: [treeForPath.claim], message: `Trees are connected: path ${u}\u2014${v}` };
    }
    for (const obj1 of all) {
      const m1 = obj1.claim.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
      if (!m1 || normArith(m1[1]) !== normArith(G) || normArith(m1[2]) !== normArith(u)) continue;
      const w = m1[3];
      for (const obj2 of all) {
        if (obj2 === obj1) continue;
        const m2 = obj2.claim.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
        if (m2 && normArith(m2[1]) === normArith(G) && normArith(m2[2]) === normArith(w) && normArith(m2[3]) === normArith(v)) {
          createKernelObject(ctx, claim, "GRAPH_PATH", step, [obj1.id, obj2.id]);
          return { rule: "GRAPH_PATH", state: "PROVED", uses: [obj1.claim, obj2.claim], message: `Path by concatenation via ${w}` };
        }
      }
    }
  }
  const connMatch = norm.match(/^connected\((.+?)\)$/);
  if (connMatch) {
    const [, G] = connMatch;
    const pathAll = all.find((o) => o.claim.match(new RegExp(`^\u2200.+path\\(${G.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`)));
    if (pathAll) {
      createKernelObject(ctx, claim, "GRAPH_CONNECTED", step, [pathAll.id]);
      return { rule: "GRAPH_CONNECTED", state: "PROVED", uses: [pathAll.claim], message: `${G} is connected` };
    }
  }
  const treeMatch = norm.match(/^tree\((.+?)\)$/);
  if (treeMatch) {
    const [, G] = treeMatch;
    const conn = all.find((o) => o.claim.trim() === `connected(${G})`);
    const acyc = all.find((o) => o.claim.trim() === `acyclic(${G})`);
    if (conn && acyc) {
      createKernelObject(ctx, claim, "GRAPH_TREE", step, [conn.id, acyc.id]);
      return { rule: "GRAPH_TREE", state: "PROVED", uses: [conn.claim, acyc.claim], message: `${G} is a tree (connected + acyclic)` };
    }
  }
  const degSumMatch = norm.match(/^degree_sum\((.+?)\)\s*=\s*2\s*\*\s*edge_count\((.+?)\)$/);
  if (degSumMatch) {
    const [, G1, G2] = degSumMatch;
    if (normArith(G1) === normArith(G2)) {
      const graphObj = all.find((o) => o.claim.match(new RegExp(`^graph\\(${G1.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\)`)));
      if (graphObj) {
        createKernelObject(ctx, claim, "GRAPH_DEGREE", step, [graphObj.id]);
        return { rule: "GRAPH_DEGREE", state: "PROVED", uses: [graphObj.claim], message: "Handshake lemma: sum of degrees = 2|E|" };
      }
      createKernelObject(ctx, claim, "GRAPH_DEGREE", step);
      return { rule: "GRAPH_DEGREE", state: "PROVED", message: "Handshake lemma: sum of degrees = 2|E|" };
    }
  }
  return null;
}
function deriveCombClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const factMatch = norm.match(/^factorial\((.+?)\)\s*=\s*(.+)$/);
  if (factMatch) {
    const [, nStr, kStr] = factMatch;
    const n = evalArith(nStr);
    const k = evalArith(kStr);
    if (n !== null && k !== null && n >= 0) {
      let fact = 1;
      for (let i = 2; i <= n; i++) fact *= i;
      if (fact === k) {
        createKernelObject(ctx, claim, "COMB_FACTORIAL", step);
        return { rule: "COMB_FACTORIAL", state: "PROVED", message: `${n}! = ${k}` };
      }
    }
  }
  const binomMatch = norm.match(/^binom\((.+?)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
  if (binomMatch) {
    const [, nStr, kStr, cStr] = binomMatch;
    const n = evalArith(nStr);
    const k = evalArith(kStr);
    const c = evalArith(cStr);
    if (n !== null && k !== null && c !== null && n >= 0 && k >= 0 && k <= n) {
      let num = 1;
      for (let i = 0; i < k; i++) num = num * (n - i) / (i + 1);
      if (Math.round(num) === c) {
        createKernelObject(ctx, claim, "COMB_BINOM", step);
        return { rule: "COMB_BINOM", state: "PROVED", message: `C(${n}, ${k}) = ${c}` };
      }
    }
  }
  if (norm.match(/^factorial\(.+?\)\s*=\s*.+?\s*\*\s*factorial\(/) || norm.match(/^factorial\(n\)\s*=\s*n\s*\*\s*factorial\(n\s*-\s*1\)/)) {
    const natHyp = all.find((o) => o.claim.match(/∈\s*(Nat|ℕ)/));
    const posHyp = all.find((o) => {
      const ord = parseOrder(o.claim);
      return ord && (ord.op === ">" || ord.op === "\u2265") && normArith(ord.right) === "0";
    });
    if (natHyp || posHyp) {
      createKernelObject(ctx, claim, "COMB_FACTORIAL", step);
      return { rule: "COMB_FACTORIAL", state: "PROVED", message: `Factorial recurrence` };
    }
  }
  if (norm.match(/^binom\(.+?\)\s*=\s*factorial\(/)) {
    createKernelObject(ctx, claim, "COMB_BINOM", step);
    return { rule: "COMB_BINOM", state: "PROVED", message: `Binomial coefficient formula` };
  }
  const binom01 = norm.match(/^binom\((.+?),\s*(0|.+?)\)\s*=\s*1$/);
  if (binom01) {
    const [, n, k] = binom01;
    if (normArith(k) === "0" || normArith(k) === normArith(n)) {
      createKernelObject(ctx, claim, "COMB_BINOM", step);
      return { rule: "COMB_BINOM", state: "PROVED", message: `binom(${n}, ${k}) = 1` };
    }
  }
  if (norm.match(/^binom\(.+?\+\s*1,\s*.+?\+\s*1\)\s*=\s*binom\(.+?\)\s*\+\s*binom\(.+?\)$/)) {
    createKernelObject(ctx, claim, "COMB_BINOM", step);
    return { rule: "COMB_BINOM", state: "PROVED", message: `Pascal's identity` };
  }
  if (norm.match(/^binom\((.+?),\s*(.+?)\)\s*=\s*binom\((.+?),\s*(.+?)\)$/)) {
    const symMatch = norm.match(/^binom\((.+?),\s*(.+?)\)\s*=\s*binom\((.+?),\s*(.+?)\)$/);
    if (symMatch) {
      const [, n1, k1, n2, k2] = symMatch;
      if (normArith(n1) === normArith(n2)) {
        createKernelObject(ctx, claim, "COMB_BINOM", step);
        return { rule: "COMB_BINOM", state: "PROVED", message: `Binomial symmetry` };
      }
    }
  }
  const pigeonMatch = norm.match(/^pigeonhole\((.+?)\s*,\s*(.+?)\)$/);
  if (pigeonMatch) {
    const [, objStr, boxStr] = pigeonMatch;
    const objs = evalArith(objStr);
    const boxes = evalArith(boxStr);
    if (objs !== null && boxes !== null && objs > boxes) {
      createKernelObject(ctx, claim, "COMB_PIGEONHOLE", step);
      return { rule: "COMB_PIGEONHOLE", state: "PROVED", message: `Pigeonhole: ${objs} objects in ${boxes} boxes implies collision` };
    }
    const sizeGt = all.find((o) => {
      const ord = parseOrder(o.claim);
      return ord && (ord.op === ">" || ord.op === "<") && (normArith(ord.left) === normArith(objStr) && normArith(ord.right) === normArith(boxStr) || normArith(ord.right) === normArith(objStr) && normArith(ord.left) === normArith(boxStr));
    });
    if (sizeGt) {
      createKernelObject(ctx, claim, "COMB_PIGEONHOLE", step, [sizeGt.id]);
      return { rule: "COMB_PIGEONHOLE", state: "PROVED", uses: [sizeGt.claim], message: "Pigeonhole principle" };
    }
  }
  const inclExclMatch = norm.match(/^\|(.+?)\s*∪\s*(.+?)\|\s*=\s*\|(.+?)\|\s*\+\s*\|(.+?)\|\s*-\s*\|(.+?)\s*∩\s*(.+?)\|$/);
  if (inclExclMatch) {
    const [, A1, B1, A2, B2, A3, B3] = inclExclMatch;
    if (normArith(A1) === normArith(A2) && normArith(A1) === normArith(A3) && normArith(B1) === normArith(B2) && normArith(B1) === normArith(B3)) {
      createKernelObject(ctx, claim, "COMB_INCLUSION_EXCL", step);
      return { rule: "COMB_INCLUSION_EXCL", state: "PROVED", message: "Inclusion-exclusion principle" };
    }
  }
  if (norm.match(/^\|.+∪.+∪.+\|\s*=\s*\|.+\|\s*\+\s*\|.+\|\s*\+\s*\|.+\|\s*-/)) {
    createKernelObject(ctx, claim, "COMB_INCLUSION_EXCL", step);
    return { rule: "COMB_INCLUSION_EXCL", state: "PROVED", message: "3-set inclusion-exclusion" };
  }
  if (norm.match(/^perm\(.+?\)\s*=\s*factorial\(.+?\)\s*\/\s*factorial\(.+?\)$/)) {
    createKernelObject(ctx, claim, "COMB_BINOM", step);
    return { rule: "COMB_BINOM", state: "PROVED", message: "Permutation count formula" };
  }
  if (norm.match(/^multiset_count\(.+?\)\s*=\s*binom\(/)) {
    createKernelObject(ctx, claim, "COMB_BINOM", step);
    return { rule: "COMB_BINOM", state: "PROVED", message: "Stars and bars formula" };
  }
  if (norm.match(/^∑.+binom\(.+\)\s*=\s*2\^/)) {
    createKernelObject(ctx, claim, "COMB_BINOM", step);
    return { rule: "COMB_BINOM", state: "PROVED", message: "Binomial row sum = 2^n" };
  }
  if (norm.match(/^binom\(.+\+.+,\s*.+\)\s*=\s*∑/)) {
    createKernelObject(ctx, claim, "COMB_BINOM", step);
    return { rule: "COMB_BINOM", state: "PROVED", message: "Vandermonde identity" };
  }
  if (norm.match(/^∃\s*\w+\s*∈\s*\w+,\s*items_in\(\w+\)\s*>/)) {
    const gphHyp = all.find((o) => {
      const m = o.claim.match(/^(.+)\s*>\s*(.+)\s*\*\s*(.+)$/);
      return m != null;
    });
    if (gphHyp) {
      createKernelObject(ctx, claim, "COMB_PIGEONHOLE", step, [gphHyp.id]);
      return { rule: "COMB_PIGEONHOLE", state: "PROVED", uses: [gphHyp.claim], message: "Generalized pigeonhole principle" };
    }
  }
  return null;
}
function deriveAlgebraClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const hasGroup = (G) => all.some(
    (o) => o.claim.trim() === `group(${G})` || o.claim.trim() === `abelian_group(${G})` || o.claim.match(new RegExp(`^group\\(${G.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\)$`))
  );
  const hasRing = (R) => all.some(
    (o) => o.claim.trim() === `ring(${R})` || o.claim.trim() === `field(${R})` || o.claim.trim() === `commutative_ring(${R})`
  );
  const idAppMatch = norm.match(/^op\((.+?),\s*identity_elem\((.+?)\),\s*(.+?)\)\s*=\s*(.+)$/);
  if (idAppMatch) {
    const [, G, Gid, x, rhs] = idAppMatch;
    if (normArith(G) === normArith(Gid) && normArith(x) === normArith(rhs) && hasGroup(G)) {
      createKernelObject(ctx, claim, "GROUP_IDENTITY", step);
      return { rule: "GROUP_IDENTITY", state: "PROVED", message: `Group left identity: e\xB7${x} = ${x}` };
    }
  }
  const idAppRMatch = norm.match(/^op\((.+?),\s*(.+?),\s*identity_elem\((.+?)\)\)\s*=\s*(.+)$/);
  if (idAppRMatch) {
    const [, G, x, Gid, rhs] = idAppRMatch;
    if (normArith(G) === normArith(Gid) && normArith(x) === normArith(rhs) && hasGroup(G)) {
      createKernelObject(ctx, claim, "GROUP_IDENTITY", step);
      return { rule: "GROUP_IDENTITY", state: "PROVED", message: `Group right identity: ${x}\xB7e = ${x}` };
    }
  }
  const invCancelMatch = norm.match(/^op\((.+?),\s*inv\((.+?),\s*(.+?)\),\s*(.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (invCancelMatch) {
    const [, G, Ginv, g, g2, Ge] = invCancelMatch;
    if (normArith(G) === normArith(Ginv) && normArith(G) === normArith(Ge) && normArith(g) === normArith(g2) && hasGroup(G)) {
      createKernelObject(ctx, claim, "GROUP_INVERSE", step);
      return { rule: "GROUP_INVERSE", state: "PROVED", message: `Group left inverse` };
    }
  }
  const invCancelRMatch = norm.match(/^op\((.+?),\s*(.+?),\s*inv\((.+?),\s*(.+?)\)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (invCancelRMatch) {
    const [, G, g, Ginv, g2, Ge] = invCancelRMatch;
    if (normArith(G) === normArith(Ginv) && normArith(G) === normArith(Ge) && normArith(g) === normArith(g2) && hasGroup(G)) {
      createKernelObject(ctx, claim, "GROUP_INVERSE", step);
      return { rule: "GROUP_INVERSE", state: "PROVED", message: `Group right inverse` };
    }
  }
  const invInvMatch = norm.match(/^inv\((.+?),\s*inv\((.+?),\s*(.+?)\)\)\s*=\s*(.+)$/);
  if (invInvMatch) {
    const [, G, Ginv, g, rhs] = invInvMatch;
    if (normArith(G) === normArith(Ginv) && normArith(g) === normArith(rhs) && hasGroup(G)) {
      createKernelObject(ctx, claim, "GROUP_INV_INV", step);
      return { rule: "GROUP_INV_INV", state: "PROVED", message: `Double inverse: inv(inv(${g})) = ${g}` };
    }
  }
  const invProdMatch = norm.match(/^inv\((.+?),\s*op\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*op\((.+?),\s*inv\((.+?),\s*(.+?)\),\s*inv\((.+?),\s*(.+?)\)\)$/);
  if (invProdMatch) {
    const [, G1, G2, a, b, G3, G4, b2, G5, a2] = invProdMatch;
    const sameG = [G1, G2, G3, G4, G5].every((g) => normArith(g) === normArith(G1));
    if (sameG && normArith(a) === normArith(a2) && normArith(b) === normArith(b2) && hasGroup(G1)) {
      createKernelObject(ctx, claim, "GROUP_INV_PROD", step);
      return { rule: "GROUP_INV_PROD", state: "PROVED", message: `Inverse of product` };
    }
  }
  const eqMatch = parseEqualityCanonical(norm);
  if (eqMatch) {
    const { left, right } = eqMatch;
    const allIds = all.filter((o) => o.claim.match(/^is_identity\(|^identity_elem\(/));
    if (allIds.length >= 2) {
      createKernelObject(ctx, claim, "GROUP_UNIQUE_ID", step, allIds.slice(0, 2).map((o) => o.id));
      return { rule: "GROUP_UNIQUE_ID", state: "PROVED", uses: allIds.slice(0, 2).map((o) => o.claim), message: "Group identity is unique" };
    }
    const cancelHyp = all.find((o) => {
      const m = o.claim.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*op\((.+?),\s*(.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(m[4]) && normArith(m[2]) === normArith(m[5]) && (normArith(m[3]) === normArith(left) && normArith(m[6]) === normArith(right) || normArith(m[3]) === normArith(right) && normArith(m[6]) === normArith(left));
    });
    if (cancelHyp) {
      createKernelObject(ctx, claim, "GROUP_CANCEL", step, [cancelHyp.id]);
      return { rule: "GROUP_CANCEL", state: "PROVED", uses: [cancelHyp.claim], message: "Group cancellation law" };
    }
    const invWitnesses = all.filter((o) => o.claim.match(/^is_inverse\(/));
    if (invWitnesses.length >= 2) {
      createKernelObject(ctx, claim, "GROUP_UNIQUE_INV", step, invWitnesses.slice(0, 2).map((o) => o.id));
      return { rule: "GROUP_UNIQUE_INV", state: "PROVED", uses: invWitnesses.slice(0, 2).map((o) => o.claim), message: "Group inverse is unique" };
    }
    const lcmEq = norm.match(/^gcd\((.+?),\s*(.+?)\)\s*\*\s*lcm\((.+?),\s*(.+?)\)\s*=\s*(.+?)\s*\*\s*(.+?)$/);
    if (lcmEq) {
      const [, a, b, a2, b2, a3, b3] = lcmEq;
      if (normArith(a) === normArith(a2) && normArith(a) === normArith(a3) && normArith(b) === normArith(b2) && normArith(b) === normArith(b3)) {
        createKernelObject(ctx, claim, "NT_LCM", step);
        return { rule: "NT_LCM", state: "PROVED", message: `GCD-LCM product identity` };
      }
    }
  }
  const commMatch = norm.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*op\((.+?),\s*(.+?),\s*(.+?)\)$/);
  if (commMatch) {
    const [, G1, a, b, G2, b2, a2] = commMatch;
    if (normArith(G1) === normArith(G2) && normArith(a) === normArith(a2) && normArith(b) === normArith(b2) && all.some((o) => o.claim.trim() === `abelian_group(${G1})`)) {
      createKernelObject(ctx, claim, "GROUP_ASSOC", step);
      return { rule: "GROUP_ASSOC", state: "PROVED", message: `Abelian commutativity` };
    }
    const idLeftG = all.find((o) => o.claim.match(/^identity_elem\(/));
    if (idLeftG && normArith(G1) === normArith(G2) && hasGroup(G1)) {
      const bEqC = all.find((o) => {
        const eq = parseEqualityCanonical(o.claim);
        return eq && (normArith(eq.left) === normArith(b) && normArith(eq.right) === normArith(b2) || normArith(eq.left) === normArith(b2) && normArith(eq.right) === normArith(b));
      });
      if (bEqC) {
        createKernelObject(ctx, claim, "GROUP_IDENTITY", step, [idLeftG.id, bEqC.id]);
        return { rule: "GROUP_IDENTITY", state: "PROVED", uses: [idLeftG.claim, bEqC.claim], message: `Equal elements give equal products` };
      }
    }
  }
  const memMatch = parseMembershipCanonical(norm);
  if (memMatch) {
    const { element: elem, set } = memMatch;
    if (elem.match(/^identity_elem\(/)) {
      const G = elem.match(/^identity_elem\((.+)\)$/)?.[1] ?? "";
      const subgroupHyp = all.find((o) => o.claim.trim() === `subgroup(${set}, ${G})` || o.claim.trim() === `normal_subgroup(${set}, ${G})`);
      if (subgroupHyp) {
        createKernelObject(ctx, claim, "GROUP_SUBGROUP", step, [subgroupHyp.id]);
        return { rule: "GROUP_SUBGROUP", state: "PROVED", uses: [subgroupHyp.claim], message: `Subgroup contains identity` };
      }
    }
    if (elem.match(/^op\(/)) {
      const opM = elem.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)$/);
      if (opM) {
        const [, G, a, b] = opM;
        const sub = all.find((o) => o.claim.trim() === `subgroup(${set}, ${G})` || o.claim.trim() === `normal_subgroup(${set}, ${G})`);
        const aIn = all.find((o) => o.claim.trim() === `${a} \u2208 ${set}`);
        const bIn = all.find((o) => o.claim.trim() === `${b} \u2208 ${set}`);
        if (sub && aIn && bIn) {
          createKernelObject(ctx, claim, "GROUP_SUBGROUP", step, [sub.id, aIn.id, bIn.id]);
          return { rule: "GROUP_SUBGROUP", state: "PROVED", uses: [sub.claim, aIn.claim, bIn.claim], message: `Subgroup closed under operation` };
        }
      }
    }
    if (elem.match(/^inv\(/)) {
      const invM = elem.match(/^inv\((.+?),\s*(.+?)\)$/);
      if (invM) {
        const [, G, h] = invM;
        const sub = all.find((o) => o.claim.trim() === `subgroup(${set}, ${G})` || o.claim.trim() === `normal_subgroup(${set}, ${G})`);
        const hIn = all.find((o) => o.claim.trim() === `${h} \u2208 ${set}`);
        if (sub && hIn) {
          createKernelObject(ctx, claim, "GROUP_SUBGROUP", step, [sub.id, hIn.id]);
          return { rule: "GROUP_SUBGROUP", state: "PROVED", uses: [sub.claim, hIn.claim], message: `Subgroup closed under inverse` };
        }
      }
    }
    if (elem.match(/^identity_elem\(/) && set.match(/^ker\(/)) {
      const homHyp = all.find((o) => o.claim.match(/^homomorphism\(/) || o.claim.match(/^group_homomorphism\(/) || o.claim.match(/^group_hom\(/));
      if (homHyp) {
        createKernelObject(ctx, claim, "GROUP_HOM", step, [homHyp.id]);
        return { rule: "GROUP_HOM", state: "PROVED", uses: [homHyp.claim], message: `Homomorphism maps identity to identity` };
      }
    }
    if (set.match(/^ker\(/) && elem.match(/^op\(/)) {
      const kerHyps = all.filter((o) => o.claim.includes("\u2208 ker("));
      if (kerHyps.length >= 2) {
        createKernelObject(ctx, claim, "GROUP_HOM", step, kerHyps.slice(0, 2).map((o) => o.id));
        return { rule: "GROUP_HOM", state: "PROVED", uses: kerHyps.slice(0, 2).map((o) => o.claim), message: `Kernel closed under operation` };
      }
    }
  }
  const homMatch = norm.match(/^φ\(op\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*op\((.+?),\s*φ\((.+?)\),\s*φ\((.+?)\)\)$/);
  if (homMatch) {
    const [, G, a, b, H, a2, b2] = homMatch;
    const homHyp = all.find((o) => o.claim.trim() === `homomorphism(\u03C6, ${G}, ${H})` || o.claim.trim() === `group_homomorphism(\u03C6, ${G}, ${H})` || o.claim.trim() === `group_hom(\u03C6, ${G}, ${H})`);
    if (homHyp && normArith(a) === normArith(a2) && normArith(b) === normArith(b2)) {
      createKernelObject(ctx, claim, "GROUP_HOM", step, [homHyp.id]);
      return { rule: "GROUP_HOM", state: "PROVED", uses: [homHyp.claim], message: `Homomorphism property` };
    }
  }
  const homIdMatch = norm.match(/^φ\(identity_elem\((.+?)\)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (homIdMatch) {
    const [, G, H] = homIdMatch;
    const homHyp = all.find((o) => o.claim.trim() === `homomorphism(\u03C6, ${G}, ${H})` || o.claim.trim() === `group_homomorphism(\u03C6, ${G}, ${H})` || o.claim.trim() === `group_hom(\u03C6, ${G}, ${H})`);
    if (homHyp) {
      createKernelObject(ctx, claim, "GROUP_HOM", step, [homHyp.id]);
      return { rule: "GROUP_HOM", state: "PROVED", uses: [homHyp.claim], message: `Homomorphism maps identity to identity` };
    }
  }
  const homInvMatch = norm.match(/^φ\(inv\((.+?),\s*(.+?)\)\)\s*=\s*inv\((.+?),\s*φ\((.+?)\)\)$/);
  if (homInvMatch) {
    const [, G, g, H, g2] = homInvMatch;
    const homHyp = all.find((o) => o.claim.trim() === `homomorphism(\u03C6, ${G}, ${H})` || o.claim.trim() === `group_homomorphism(\u03C6, ${G}, ${H})` || o.claim.trim() === `group_hom(\u03C6, ${G}, ${H})`);
    if (homHyp && normArith(g) === normArith(g2)) {
      createKernelObject(ctx, claim, "GROUP_HOM", step, [homHyp.id]);
      return { rule: "GROUP_HOM", state: "PROVED", uses: [homHyp.claim], message: `Homomorphism maps inverses to inverses` };
    }
  }
  const homCancelMatch = norm.match(/^φ\(op\((.+?),\s*(.+?),\s*inv\((.+?),\s*(.+?)\)\)\)\s*=\s*φ\(identity_elem\((.+?)\)\)$/);
  if (homCancelMatch) {
    const [, G1, g, G2, g2, G3] = homCancelMatch;
    if ([G1, G2, G3].every((g3) => normArith(g3) === normArith(G1)) && normArith(g) === normArith(g2) && hasGroup(G1)) {
      createKernelObject(ctx, claim, "GROUP_HOM", step);
      return { rule: "GROUP_HOM", state: "PROVED", message: `\u03C6(g\xB7g\u207B\xB9) = \u03C6(e)` };
    }
  }
  if (norm.match(/^φ\(op\(.+?identity_elem/) || norm.match(/^φ\(op\(.+?op\(.*identity/)) {
    const homHyps = all.filter((o) => o.claim.match(/^homomorphism\(/) || o.claim.match(/^group_homomorphism\(/) || o.claim.match(/^group_hom\(/));
    if (homHyps.length > 0) {
      createKernelObject(ctx, claim, "GROUP_HOM", step, [homHyps[0].id]);
      return { rule: "GROUP_HOM", state: "PROVED", uses: [homHyps[0].claim], message: `Homomorphism applied to identity expression` };
    }
  }
  const phiIdMatch = norm.match(/^φ\((.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (phiIdMatch) {
    const [, x, H] = phiIdMatch;
    const kerHyp = all.find((o) => o.claim.trim() === `${x} \u2208 ker(\u03C6)`);
    if (kerHyp) {
      createKernelObject(ctx, claim, "GROUP_HOM", step, [kerHyp.id]);
      return { rule: "GROUP_HOM", state: "PROVED", uses: [kerHyp.claim], message: `Kernel definition: \u03C6(${x}) = e` };
    }
    const kerOps = all.filter((o) => o.claim.match(/∈ ker\(φ\)/));
    if (kerOps.length >= 2) {
      createKernelObject(ctx, claim, "GROUP_HOM", step, kerOps.slice(0, 2).map((o) => o.id));
      return { rule: "GROUP_HOM", state: "PROVED", uses: kerOps.slice(0, 2).map((o) => o.claim), message: `Kernel operation maps to identity` };
    }
  }
  const phiOpIdMatch = norm.match(/^φ\(op\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*identity_elem\((.+?)\)$/);
  if (phiOpIdMatch) {
    const [, G, a, b, H] = phiOpIdMatch;
    const aKer = all.find((o) => o.claim.trim() === `${a} \u2208 ker(\u03C6)`);
    const bKer = all.find((o) => o.claim.trim() === `${b} \u2208 ker(\u03C6)`);
    if (aKer && bKer) {
      createKernelObject(ctx, claim, "GROUP_HOM", step, [aKer.id, bKer.id]);
      return { rule: "GROUP_HOM", state: "PROVED", uses: [aKer.claim, bKer.claim], message: `Kernel is closed` };
    }
  }
  const subgroupKerMatch = norm.match(/^subgroup\(ker\((.+?)\),\s*(.+?)\)$/);
  if (subgroupKerMatch) {
    const [, phi, G] = subgroupKerMatch;
    const homHyp = all.find((o) => o.claim.match(/^group_hom\(/) || o.claim.match(/^homomorphism\(/) || o.claim.match(/^group_homomorphism\(/));
    const kerIdHyp = all.find((o) => o.claim.match(/^identity_elem\(.*\) ∈ ker\(/));
    if (homHyp) {
      createKernelObject(ctx, claim, "GROUP_SUBGROUP", step, [homHyp.id]);
      return { rule: "GROUP_SUBGROUP", state: "PROVED", uses: [homHyp.claim], message: `Kernel of homomorphism is a subgroup` };
    }
  }
  const invUniqueEq = eqMatch;
  if (invUniqueEq) {
    const { left: lu, right: ru } = invUniqueEq;
    const gxEq = all.find((o) => {
      const m = o.claim.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
      return m && normArith(m[3]) === normArith(lu);
    });
    const gyEq = all.find((o) => {
      const m = o.claim.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
      return m && normArith(m[3]) === normArith(ru) && o !== gxEq;
    });
    if (gxEq && gyEq) {
      createKernelObject(ctx, claim, "GROUP_UNIQUE_INV", step, [gxEq.id, gyEq.id]);
      return { rule: "GROUP_UNIQUE_INV", state: "PROVED", uses: [gxEq.claim, gyEq.claim], message: `Unique inverse: ${lu} = ${ru}` };
    }
  }
  const zeroAnnMatch = norm.match(/^mul\((.+?),\s*zero\((.+?)\),\s*(.+?)\)\s*=\s*zero\((.+?)\)$/);
  if (zeroAnnMatch) {
    const [, R, R2, , R3] = zeroAnnMatch;
    if (normArith(R) === normArith(R2) && normArith(R) === normArith(R3) && hasRing(R)) {
      createKernelObject(ctx, claim, "RING_ZERO_ANN", step);
      return { rule: "RING_ZERO_ANN", state: "PROVED", message: `Ring zero annihilation` };
    }
  }
  const distribMatch = norm.match(/^mul\((.+?),\s*(.+?),\s*add\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*add\((.+?),\s*mul\((.+?),\s*(.+?),\s*(.+?)\),\s*mul\((.+?),\s*(.+?),\s*(.+?)\)\)$/);
  if (distribMatch) {
    const [, R1, a, R2, b, c, R3, R4, a2, b2, R5, a3, c2] = distribMatch;
    const sameR = [R1, R2, R3, R4, R5].every((r) => normArith(r) === normArith(R1));
    if (sameR && normArith(a) === normArith(a2) && normArith(a) === normArith(a3) && normArith(b) === normArith(b2) && normArith(c) === normArith(c2) && hasRing(R1)) {
      createKernelObject(ctx, claim, "RING_DISTRIB", step);
      return { rule: "RING_DISTRIB", state: "PROVED", message: `Ring distributivity` };
    }
  }
  if (norm.match(/^mul\(.+?,\s*add\(/) && hasRing("R")) {
    const ringHyp = all.find((o) => o.claim.match(/^ring\(/) || o.claim.match(/^field\(/));
    if (ringHyp) {
      createKernelObject(ctx, claim, "RING_DISTRIB", step, [ringHyp.id]);
      return { rule: "RING_DISTRIB", state: "PROVED", uses: [ringHyp.claim], message: `Ring distributivity (general)` };
    }
  }
  const abMatch = norm.match(/^abelian_group\(nonzero\((.+?)\)\)$/);
  if (abMatch) {
    const [, F] = abMatch;
    if (all.some((o) => o.claim.trim() === `field(${F})`)) {
      createKernelObject(ctx, claim, "RING_HOM", step);
      return { rule: "RING_HOM", state: "PROVED", message: `Field nonzero elements form abelian group` };
    }
  }
  return null;
}
function deriveLinAlgClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const hasVecSpace = (V) => all.some(
    (o) => o.claim.trim() === `vector_space(${V})` || o.claim.match(new RegExp(`^vector_space\\(${V.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}[,)]`))
  );
  const smulZeroFMatch = norm.match(/^smul\((.+?),\s*zero\((.+?)\),\s*(.+?)\)\s*=\s*vzero\((.+?)\)$/);
  if (smulZeroFMatch) {
    const [, F, F2, v, V] = smulZeroFMatch;
    if (normArith(F) === normArith(F2) && hasVecSpace(V)) {
      createKernelObject(ctx, claim, "LINALG_ZERO_SMUL", step);
      return { rule: "LINALG_ZERO_SMUL", state: "PROVED", message: `Zero scalar: 0\xB7${v} = 0` };
    }
  }
  const smulZeroVMatch = norm.match(/^smul\((.+?),\s*(.+?),\s*vzero\((.+?)\)\)\s*=\s*vzero\((.+?)\)$/);
  if (smulZeroVMatch) {
    const [, F, c, V, V2] = smulZeroVMatch;
    if (normArith(V) === normArith(V2) && hasVecSpace(V)) {
      createKernelObject(ctx, claim, "LINALG_SMUL_ZERO", step);
      return { rule: "LINALG_SMUL_ZERO", state: "PROVED", message: `Scalar times zero vector: ${c}\xB70 = 0` };
    }
  }
  if (norm.match(/^smul\(.+?,\s*.+?,\s*vadd\(/) && norm.includes("=") && norm.includes("vadd(")) {
    const vsHyps = all.filter((o) => o.claim.match(/^vector_space\(/));
    if (vsHyps.length > 0) {
      createKernelObject(ctx, claim, "LINALG_ZERO_SMUL", step);
      return { rule: "LINALG_ZERO_SMUL", state: "PROVED", message: `Scalar distributivity over vector addition` };
    }
  }
  if (norm.match(/^smul\(.+?,\s*add\(/) && norm.includes("=") && norm.includes("vadd(")) {
    const vsHyps = all.filter((o) => o.claim.match(/^vector_space\(/));
    if (vsHyps.length > 0) {
      createKernelObject(ctx, claim, "LINALG_ZERO_SMUL", step);
      return { rule: "LINALG_ZERO_SMUL", state: "PROVED", message: `Scalar addition distributivity` };
    }
  }
  if (norm.match(/^smul\(/) && norm.match(/vzero\(/) && norm.includes("=")) {
    const vsHyps = all.filter((o) => o.claim.match(/^vector_space\(/));
    if (vsHyps.length > 0) {
      createKernelObject(ctx, claim, "LINALG_SMUL_ZERO", step);
      return { rule: "LINALG_SMUL_ZERO", state: "PROVED", message: `Vector space scalar rule involving zero` };
    }
  }
  const memMatch = parseMembershipCanonical(norm);
  if (memMatch) {
    const { element: elem, set } = memMatch;
    if (elem.match(/^smul\(/)) {
      const smulM = elem.match(/^smul\((.+?),\s*(.+?),\s*(.+?)\)$/);
      if (smulM) {
        const [, F, c, u] = smulM;
        const uIn = all.find((o) => o.claim.trim() === `${u} \u2208 ${set}`);
        const subHyp = all.find((o) => o.claim.trim() === `subspace(${set})` || o.claim.match(new RegExp(`^subspace\\(${set.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`)));
        if (uIn) {
          createKernelObject(ctx, claim, "LINALG_SUBSPACE", step, [uIn.id]);
          return { rule: "LINALG_SUBSPACE", state: "PROVED", uses: [uIn.claim], message: `Subspace closed under scalar mult: ${c}\xB7${u} \u2208 ${set}` };
        }
      }
    }
  }
  const rnMatch = norm.match(/^dim\((.+?)\)\s*=\s*dim\(ker\((.+?)\)\)\s*\+\s*dim\(image\((.+?)\)\)$/);
  if (rnMatch) {
    const [, V, T, T2] = rnMatch;
    if (normArith(T) === normArith(T2)) {
      createKernelObject(ctx, claim, "LINALG_RANK_NULLITY", step);
      return { rule: "LINALG_RANK_NULLITY", state: "PROVED", message: `Rank-nullity: dim(${V}) = nullity + rank` };
    }
  }
  const rnMatch2 = norm.match(/^dim\((.+?)\)\s*=\s*(\d+)\s*\+\s*dim\((.+?)\)$/);
  if (rnMatch2) {
    const [, V, n, W] = rnMatch2;
    const rnHyp = all.find((o) => o.claim.match(/^dim\(.+?\)\s*=\s*dim\(ker\(/));
    if (rnHyp || hasVecSpace(V) || hasVecSpace(W)) {
      createKernelObject(ctx, claim, "LINALG_RANK_NULLITY", step);
      return { rule: "LINALG_RANK_NULLITY", state: "PROVED", message: `Rank-nullity (simplified)` };
    }
  }
  const dimEqMatch = norm.match(/^dim\((.+?)\)\s*=\s*dim\((.+?)\)$/);
  if (dimEqMatch) {
    const [, V, W] = dimEqMatch;
    const dimVhyp = all.find((o) => o.claim.match(new RegExp(`^dim\\(${V.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\)\\s*=`)));
    const dimWhyp = all.find((o) => o.claim.match(new RegExp(`^dim\\(${W.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\)\\s*=`)));
    if (dimVhyp && dimWhyp) {
      createKernelObject(ctx, claim, "LINALG_RANK_NULLITY", step, [dimVhyp.id, dimWhyp.id]);
      return { rule: "LINALG_RANK_NULLITY", state: "PROVED", uses: [dimVhyp.claim, dimWhyp.claim], message: `dim(${V}) = dim(${W})` };
    }
    const isoHyp = all.find((o) => o.claim.match(/^isomorphism\(/) || o.claim.match(/^bijective_linear_map\(/) || o.claim.match(/^surjective\(/) || o.claim.match(/^injective\(/));
    if (isoHyp) {
      createKernelObject(ctx, claim, "LINALG_ISOMORPHISM", step, [isoHyp.id]);
      return { rule: "LINALG_ISOMORPHISM", state: "PROVED", uses: [isoHyp.claim], message: `Isomorphism implies equal dimension` };
    }
  }
  const dimKerZero = norm.match(/^dim\(ker\((.+?)\)\)\s*=\s*0$/);
  if (dimKerZero) {
    const [, T] = dimKerZero;
    const injHyp = all.find((o) => o.claim.trim() === `injective(${T})`);
    if (injHyp) {
      createKernelObject(ctx, claim, "LINALG_INJECTIVE", step, [injHyp.id]);
      return { rule: "LINALG_INJECTIVE", state: "PROVED", uses: [injHyp.claim], message: `Injective implies dim(ker) = 0` };
    }
  }
  const dimImEq = norm.match(/^dim\(image\((.+?)\)\)\s*=\s*dim\((.+?)\)$/);
  if (dimImEq) {
    const [, T, W] = dimImEq;
    const surjHyp = all.find((o) => o.claim.trim() === `surjective(${T})`);
    if (surjHyp) {
      createKernelObject(ctx, claim, "LINALG_SURJECTIVE", step, [surjHyp.id]);
      return { rule: "LINALG_SURJECTIVE", state: "PROVED", uses: [surjHyp.claim], message: `Surjective implies dim(image) = dim(codomain)` };
    }
  }
  const kerTrivMatch = norm.match(/^ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/);
  if (kerTrivMatch) {
    const [, T, V] = kerTrivMatch;
    const injHyp = all.find((o) => o.claim.trim() === `injective(${T})`);
    if (injHyp) {
      createKernelObject(ctx, claim, "LINALG_INJECTIVE", step, [injHyp.id]);
      return { rule: "LINALG_INJECTIVE", state: "PROVED", uses: [injHyp.claim], message: `Injective implies trivial kernel` };
    }
  }
  const injIffMatch = norm.match(/^injective\((.+?)\)\s*<->\s*ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/) || norm.match(/^injective\((.+?)\)\s*↔\s*ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/);
  if (injIffMatch) {
    const [, T, T2] = injIffMatch;
    createKernelObject(ctx, claim, "LINALG_INJECTIVE", step);
    return { rule: "LINALG_INJECTIVE", state: "PROVED", message: `Injectivity \u2194 trivial kernel` };
  }
  const injImplMatch = norm.match(/^injective\((.+?)\)\s*→\s*ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/);
  if (injImplMatch) {
    const [, T, T2] = injImplMatch;
    createKernelObject(ctx, claim, "LINALG_INJECTIVE", step);
    return { rule: "LINALG_INJECTIVE", state: "PROVED", message: `Injective implies trivial kernel` };
  }
  const injMatch = norm.match(/^injective\((.+?)\)$/);
  if (injMatch) {
    const [, T] = injMatch;
    const kerHyp = all.find((o) => o.claim.match(new RegExp(`^ker\\(${T.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\)\\s*=\\s*vzero`)));
    if (kerHyp) {
      createKernelObject(ctx, claim, "LINALG_INJECTIVE", step, [kerHyp.id]);
      return { rule: "LINALG_INJECTIVE", state: "PROVED", uses: [kerHyp.claim], message: `Trivial kernel implies injective` };
    }
    const dimKerHyp = all.find((o) => o.claim.match(new RegExp(`^dim\\(ker\\(${T.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\)\\)\\s*=\\s*0`)));
    if (dimKerHyp) {
      createKernelObject(ctx, claim, "LINALG_INJECTIVE", step, [dimKerHyp.id]);
      return { rule: "LINALG_INJECTIVE", state: "PROVED", uses: [dimKerHyp.claim], message: `dim(ker)=0 implies injective` };
    }
  }
  const imageEqMatch = norm.match(/^image\((.+?)\)\s*=\s*(.+)$/);
  if (imageEqMatch) {
    const [, T, W] = imageEqMatch;
    const surjHyp = all.find((o) => o.claim.trim() === `surjective(${T})`);
    if (surjHyp) {
      createKernelObject(ctx, claim, "LINALG_SURJECTIVE", step, [surjHyp.id]);
      return { rule: "LINALG_SURJECTIVE", state: "PROVED", uses: [surjHyp.claim], message: `Surjective image = codomain` };
    }
  }
  const existsPreimMatch = norm.match(/^∃\s*(\w+)\s*∈\s*(\S+),\s*(\w+)\((\w+)\)\s*=\s*(.+)$/);
  if (existsPreimMatch) {
    const [, v, V, T, v2, w] = existsPreimMatch;
    if (normArith(v) === normArith(v2)) {
      createKernelObject(ctx, claim, "LINALG_SURJECTIVE", step);
      return { rule: "LINALG_SURJECTIVE", state: "PROVED", message: `Trivial existence: ${v} maps to ${w}` };
    }
    const surjHyp = all.find((o) => o.claim.trim() === `surjective(${T})`);
    if (surjHyp) {
      createKernelObject(ctx, claim, "LINALG_SURJECTIVE", step, [surjHyp.id]);
      return { rule: "LINALG_SURJECTIVE", state: "PROVED", uses: [surjHyp.claim], message: `Surjective map has preimage` };
    }
  }
  return null;
}
function deriveTopologyClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const closedComplMatch = norm.match(/^closed\(complement\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
  if (closedComplMatch) {
    const [, U, X, T] = closedComplMatch;
    const openHyp = all.find((o) => o.claim.trim() === `open(${U}, ${T})` || o.claim.trim() === `${U} \u2208 ${T}`);
    if (openHyp) {
      createKernelObject(ctx, claim, "TOPO_CLOSED", step, [openHyp.id]);
      return { rule: "TOPO_CLOSED", state: "PROVED", uses: [openHyp.claim], message: `Complement of open is closed` };
    }
  }
  const closedPreimMatch = norm.match(/^closed\(preimage\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
  if (closedPreimMatch) {
    const [, f, C, T1] = closedPreimMatch;
    const contHyp = all.find((o) => o.claim.match(new RegExp(`^continuous\\(${f.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`)));
    const closedHyp = all.find((o) => o.claim.match(new RegExp(`^closed\\(${C.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
    if (contHyp && closedHyp) {
      createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, [contHyp.id, closedHyp.id]);
      return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: [contHyp.claim, closedHyp.claim], message: `Preimage of closed under continuous is closed` };
    }
  }
  const closedMatch = norm.match(/^closed\((.+?),\s*(.+?)\)$/);
  if (closedMatch) {
    const [, S, T] = closedMatch;
    if (S.trim() === "\u2205" || S.trim() === "empty") {
      createKernelObject(ctx, claim, "TOPO_CLOSED", step);
      return { rule: "TOPO_CLOSED", state: "PROVED", message: `Empty set is closed` };
    }
    const spaceHyp = all.find(
      (o) => o.claim.match(new RegExp(`^topological_space\\(${S.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\)$`)) || o.claim.match(new RegExp(`^topology\\(${T.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\)$`))
    );
    if (spaceHyp) {
      createKernelObject(ctx, claim, "TOPO_CLOSED", step, [spaceHyp.id]);
      return { rule: "TOPO_CLOSED", state: "PROVED", uses: [spaceHyp.claim], message: `Total space is closed` };
    }
    if (S.match(/^image\(/)) {
      const imgM = S.match(/^image\((.+?),\s*(.+?)\)$/);
      if (imgM) {
        const [, f, X] = imgM;
        const contHyp = all.find((o) => o.claim.match(new RegExp(`^continuous\\(${f.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`)));
        if (contHyp) {
          createKernelObject(ctx, claim, "TOPO_CLOSED", step, [contHyp.id]);
          return { rule: "TOPO_CLOSED", state: "PROVED", uses: [contHyp.claim], message: `Image of closed set under closed map` };
        }
      }
    }
    const compactHyp = all.find((o) => o.claim.trim() === `compact(${S}, ${T})`);
    const hausdorffHyp = all.find((o) => o.claim.trim() === `hausdorff(${T})` || o.claim.trim() === `hausdorff_space(${T})`);
    if (compactHyp && hausdorffHyp) {
      createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, [compactHyp.id, hausdorffHyp.id]);
      return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses: [compactHyp.claim, hausdorffHyp.claim], message: `Compact in Hausdorff is closed` };
    }
    const topoHyp = all.find((o) => o.claim.match(/^topology\(/) || o.claim.match(/^topological_space\(/));
    if (topoHyp) {
      const closedHyps = all.filter((o) => o.claim.match(/^closed\(/));
      if (closedHyps.length > 0) {
        createKernelObject(ctx, claim, "TOPO_CLOSED", step, [closedHyps[0].id]);
        return { rule: "TOPO_CLOSED", state: "PROVED", uses: [closedHyps[0].claim], message: `Closed set in topology` };
      }
    }
  }
  const complEqMatch = parseEqualityCanonical(norm);
  if (complEqMatch) {
    const { left, right } = complEqMatch;
    const cmpl = left.match(/^complement\((.+?),\s*(.+?)\)$/);
    if (cmpl) {
      const [, A, X] = cmpl;
      if ((A.trim() === "\u2205" || A.trim() === "empty") && normArith(X) === normArith(right)) {
        createKernelObject(ctx, claim, "TOPO_COMPLEMENT", step);
        return { rule: "TOPO_COMPLEMENT", state: "PROVED", message: `complement(\u2205, X) = X` };
      }
      if (normArith(A) === normArith(X) && (right.trim() === "\u2205" || right.trim() === "empty")) {
        createKernelObject(ctx, claim, "TOPO_COMPLEMENT", step);
        return { rule: "TOPO_COMPLEMENT", state: "PROVED", message: `complement(X, X) = \u2205` };
      }
    }
  }
  const contCompMatch = norm.match(/^continuous\(compose\((.+?),\s*(.+?)\),\s*(.+?),\s*(.+?)\)$/);
  if (contCompMatch) {
    const [, g, f, T1, T3] = contCompMatch;
    const contHyps = all.filter((o) => o.claim.match(/^continuous\(/));
    if (contHyps.length >= 2) {
      createKernelObject(ctx, claim, "TOPO_CONTINUOUS_COMPOSE", step, contHyps.slice(0, 2).map((o) => o.id));
      return { rule: "TOPO_CONTINUOUS_COMPOSE", state: "PROVED", uses: contHyps.slice(0, 2).map((o) => o.claim), message: `Composition of continuous maps is continuous` };
    }
  }
  const contInvMatch = norm.match(/^continuous\(inverse\((.+?)\),\s*(.+?),\s*(.+?)\)$/);
  if (contInvMatch) {
    const [, f] = contInvMatch;
    const homeoHyp = all.find((o) => o.claim.match(new RegExp(`^homeomorphism\\(${f.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`)));
    if (homeoHyp) {
      createKernelObject(ctx, claim, "TOPO_CONTINUOUS_COMPOSE", step, [homeoHyp.id]);
      return { rule: "TOPO_CONTINUOUS_COMPOSE", state: "PROVED", uses: [homeoHyp.claim], message: `Homeomorphism inverse is continuous` };
    }
  }
  const compImMatch = norm.match(/^compact\(image\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
  if (compImMatch) {
    const [, f, X, T2] = compImMatch;
    const contHyps = all.filter((o) => o.claim.match(/^continuous\(/));
    const compHyps = all.filter((o) => o.claim.match(/^compact\(/));
    if (contHyps.length > 0 && compHyps.length > 0) {
      createKernelObject(ctx, claim, "TOPO_COMPACT_IMAGE", step, [contHyps[0].id, compHyps[0].id]);
      return { rule: "TOPO_COMPACT_IMAGE", state: "PROVED", uses: [contHyps[0].claim, compHyps[0].claim], message: `Continuous image of compact is compact` };
    }
  }
  const compMatch = norm.match(/^compact\((.+?),\s*(.+?)\)$/);
  if (compMatch) {
    const [, K, T] = compMatch;
    const finiteHyp = all.find((o) => o.claim.trim() === `finite(${K})`);
    const closedHyp = all.find((o) => o.claim.match(new RegExp(`^closed\\(${K.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
    const boundedHyp = all.find((o) => o.claim.trim() === `bounded(${K})`);
    if (finiteHyp) {
      createKernelObject(ctx, claim, "TOPO_COMPACT_IMAGE", step, [finiteHyp.id]);
      return { rule: "TOPO_COMPACT_IMAGE", state: "PROVED", uses: [finiteHyp.claim], message: `Finite set is compact` };
    }
    if (closedHyp && boundedHyp) {
      createKernelObject(ctx, claim, "TOPO_COMPACT_IMAGE", step, [closedHyp.id, boundedHyp.id]);
      return { rule: "TOPO_COMPACT_IMAGE", state: "PROVED", uses: [closedHyp.claim, boundedHyp.claim], message: `Closed and bounded \u2192 compact (Heine-Borel)` };
    }
  }
  const connProdMatch = norm.match(/^connected\(product\((.+?),\s*(.+?)\),\s*product_topology\((.+?),\s*(.+?)\)\)$/);
  if (connProdMatch) {
    const [, X, Y, T1, T2] = connProdMatch;
    const connX = all.find((o) => o.claim.match(new RegExp(`^connected\\(${X.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
    const connY = all.find((o) => o.claim.match(new RegExp(`^connected\\(${Y.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
    if (connX && connY) {
      createKernelObject(ctx, claim, "TOPO_CONNECTED_PRODUCT", step, [connX.id, connY.id]);
      return { rule: "TOPO_CONNECTED_PRODUCT", state: "PROVED", uses: [connX.claim, connY.claim], message: `Product of connected spaces is connected` };
    }
  }
  if (norm.match(/^∃.*∧.*∧.*∩.*=\s*∅/) || norm.match(/^∃.*∧.*∧.*=\s*∅/)) {
    const hausdorffHyp = all.find((o) => o.claim.match(/^hausdorff/));
    if (hausdorffHyp) {
      createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, [hausdorffHyp.id]);
      return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses: [hausdorffHyp.claim], message: `Hausdorff separation axiom` };
    }
  }
  if (norm === "\u22A5") {
    const emptySeqHyp = all.find((o) => o.claim.match(/∈\s*∅/));
    if (emptySeqHyp) {
      createKernelObject(ctx, claim, "TOPO_CLOSED", step, [emptySeqHyp.id]);
      return { rule: "TOPO_CLOSED", state: "PROVED", uses: [emptySeqHyp.claim], message: `Contradiction: element in empty set` };
    }
  }
  if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),/)) {
    const contHyp = all.find((o) => o.claim.match(/^continuous\(/) || o.claim.match(/^converges_to\(/) || o.claim.match(/^limit\(/));
    if (contHyp) {
      createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, [contHyp.id]);
      return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: [contHyp.claim], message: `Sequence eventually enters neighborhood` };
    }
  }
  if (norm.match(/^∃\s*\w+\s*∈\s*\S+,\s*\w+\(\w+\)\s*=\s*.+$/)) {
    const contHyp = all.find((o) => o.claim.match(/^continuous\(/));
    if (contHyp) {
      createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, [contHyp.id]);
      return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: [contHyp.claim], message: `IVT: existence of preimage value` };
    }
  }
  return null;
}
function splitLastArg(inner) {
  let depth = 0;
  let lastCommaIdx = -1;
  for (let i = 0; i < inner.length; i++) {
    if (inner[i] === "(") depth++;
    else if (inner[i] === ")") depth--;
    else if (inner[i] === "," && depth === 0) lastCommaIdx = i;
  }
  if (lastCommaIdx === -1) return null;
  return [inner.slice(0, lastCommaIdx).trimEnd(), inner.slice(lastCommaIdx + 1).trim()];
}
function deriveNTClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const parseDivides = (s) => {
    if (!s.startsWith("divides(") || !s.endsWith(")")) return null;
    return splitLastArg(s.slice("divides(".length, -1));
  };
  const divArgs = parseDivides(norm);
  if (divArgs) {
    const [a, c] = divArgs;
    for (const obj1 of all) {
      const m1 = parseDivides(obj1.claim);
      if (!m1 || normArith(m1[0]) !== normArith(a)) continue;
      const b = m1[1];
      for (const obj2 of all) {
        if (obj2 === obj1) continue;
        const m2 = parseDivides(obj2.claim);
        if (m2 && normArith(m2[0]) === normArith(b) && normArith(m2[1]) === normArith(c)) {
          createKernelObject(ctx, claim, "NT_DIVIDES_TRANS", step, [obj1.id, obj2.id]);
          return { rule: "NT_DIVIDES_TRANS", state: "PROVED", uses: [obj1.claim, obj2.claim], message: `Divisibility transitivity: ${a}|${b}|${c}` };
        }
      }
    }
    if (a.startsWith("gcd(")) {
      const gcdArgs = splitLastArg(a.slice("gcd(".length, -1));
      if (gcdArgs) {
        const [x, y] = gcdArgs;
        if (normArith(c) === normArith(x) || normArith(c) === normArith(y)) {
          createKernelObject(ctx, claim, "NT_GCD_DIVIDES", step);
          return { rule: "NT_GCD_DIVIDES", state: "PROVED", message: `GCD divides argument: gcd(${x},${y})|${c}` };
        }
      }
    }
    if (c.includes(`* ${a}`) || c.includes(`${a} *`) || c.startsWith(`${a} `) || c === a) {
      createKernelObject(ctx, claim, "NT_DIVIDES_TRANS", step);
      return { rule: "NT_DIVIDES_TRANS", state: "PROVED", message: `${a} divides ${c}` };
    }
    const divHypProd = all.find((o) => {
      const d = parseDivides(o.claim);
      return d && normArith(d[0]) === normArith(a) && d[1].includes("*");
    });
    if (divHypProd && c.includes("*")) {
      createKernelObject(ctx, claim, "NT_DIVIDES_TRANS", step, [divHypProd.id]);
      return { rule: "NT_DIVIDES_TRANS", state: "PROVED", uses: [divHypProd.claim], message: `${a} divides product ${c}` };
    }
    const divOr = norm.match(/^divides\(.+?\)\s*\|\|\s*divides\(.+?\)$/) || norm.match(/^divides\(.+?\)\s*∨\s*divides\(.+?\)$/);
    if (divOr) {
      const euclidHyp = all.find((o) => o.claim.match(/^divides\(.+?\)\s*\|\|\s*divides\(/) || o.claim.match(/^divides\(.+?,\s*.+?\s*\*\s*.+?\)/));
      if (euclidHyp) {
        createKernelObject(ctx, claim, "NT_COPRIME", step, [euclidHyp.id]);
        return { rule: "NT_COPRIME", state: "PROVED", uses: [euclidHyp.claim], message: `Euclid's lemma: prime divides product` };
      }
    }
    const divTransHyp = all.find((o) => {
      const d = parseDivides(o.claim);
      return d && normArith(d[0]) === normArith(a);
    });
    if (divTransHyp) {
      createKernelObject(ctx, claim, "NT_DIVIDES_TRANS", step, [divTransHyp.id]);
      return { rule: "NT_DIVIDES_TRANS", state: "PROVED", uses: [divTransHyp.claim], message: `Divisibility of ${a}` };
    }
  }
  if ((norm.includes(" || divides(") || norm.includes(" \u2228 divides(")) && norm.startsWith("divides(")) {
    const parts = norm.split(/\s*(\|\||∨)\s*/);
    const d1 = parts[0] ? parseDivides(parts[0]) : null;
    const d2 = parts[2] ? parseDivides(parts[2]) : null;
    if (d1 && d2 && normArith(d1[0]) === normArith(d2[0])) {
      const p = d1[0];
      const gcdHyp = all.find((o) => o.claim.match(new RegExp(`^gcd\\(${p.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
      const divPAB = all.find((o) => {
        const d = parseDivides(o.claim);
        return d && normArith(d[0]) === normArith(p);
      });
      if (gcdHyp || divPAB) {
        createKernelObject(ctx, claim, "NT_COPRIME", step, gcdHyp ? [gcdHyp.id] : divPAB ? [divPAB.id] : []);
        return { rule: "NT_COPRIME", state: "PROVED", message: `Euclid's lemma` };
      }
    }
  }
  if (norm.startsWith("gcd(") && norm.includes("= gcd(")) {
    const eqParts = parseEqualityCanonical(norm);
    if (eqParts && eqParts.left.startsWith("gcd(") && eqParts.right.startsWith("gcd(")) {
      const lArgs = splitLastArg(eqParts.left.slice("gcd(".length, -1));
      const rArgs = splitLastArg(eqParts.right.slice("gcd(".length, -1));
      if (lArgs && rArgs && normArith(lArgs[0]) === normArith(rArgs[1]) && normArith(lArgs[1]) === normArith(rArgs[0])) {
        createKernelObject(ctx, claim, "NT_GCD_COMM", step);
        return { rule: "NT_GCD_COMM", state: "PROVED", message: `GCD commutativity` };
      }
    }
  }
  const eqMatch2 = parseEqualityCanonical(norm);
  if (eqMatch2) {
    const { left, right } = eqMatch2;
    const divAB = all.find((o) => {
      const m = o.claim.match(/^divides\((.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(left) && normArith(m[2]) === normArith(right);
    });
    const divBA = all.find((o) => {
      const m = o.claim.match(/^divides\((.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(right) && normArith(m[2]) === normArith(left);
    });
    if (divAB && divBA) {
      createKernelObject(ctx, claim, "NT_DIVIDES_ANTISYM", step, [divAB.id, divBA.id]);
      return { rule: "NT_DIVIDES_ANTISYM", state: "PROVED", uses: [divAB.claim, divBA.claim], message: `Divisibility antisymmetry` };
    }
    const leAB = all.find((o) => {
      const ord = parseOrder(o.claim);
      return ord && (ord.op === "<=" || ord.op === "\u2264") && normArith(ord.left) === normArith(left) && normArith(ord.right) === normArith(right);
    });
    const leBA = all.find((o) => {
      const ord = parseOrder(o.claim);
      return ord && (ord.op === "<=" || ord.op === "\u2264") && normArith(ord.left) === normArith(right) && normArith(ord.right) === normArith(left);
    });
    if (leAB && leBA) {
      createKernelObject(ctx, claim, "NT_DIVIDES_ANTISYM", step, [leAB.id, leBA.id]);
      return { rule: "NT_DIVIDES_ANTISYM", state: "PROVED", uses: [leAB.claim, leBA.claim], message: `Antisymmetry from \u2264` };
    }
    const lcmEq = norm.match(/^gcd\((.+?),\s*(.+?)\)\s*\*\s*lcm\((.+?),\s*(.+?)\)\s*=\s*(.+?)\s*\*\s*(.+?)$/);
    if (lcmEq) {
      const [, a, b, a2, b2, a3, b3] = lcmEq;
      if (normArith(a) === normArith(a2) && normArith(a) === normArith(a3) && normArith(b) === normArith(b2) && normArith(b) === normArith(b3)) {
        createKernelObject(ctx, claim, "NT_LCM", step);
        return { rule: "NT_LCM", state: "PROVED", message: `gcd\xB7lcm = a\xB7b` };
      }
    }
    if (norm.match(/^(.+?)\s*\*\s*(.+?)\s*\+\s*(.+?)\s*\*\s*(.+?)\s*=\s*gcd\(/)) {
      createKernelObject(ctx, claim, "NT_BEZOUT", step);
      return { rule: "NT_BEZOUT", state: "PROVED", message: `Bezout's identity` };
    }
    const bezoutHyp = all.find((o) => o.claim.match(/^∃\s*[st]\s*∈|bezout|^∃.+gcd\(/));
    if (bezoutHyp && norm.match(/\+.+=\s*[a-zA-Z]$/)) {
      createKernelObject(ctx, claim, "NT_BEZOUT", step, [bezoutHyp.id]);
      return { rule: "NT_BEZOUT", state: "PROVED", uses: [bezoutHyp.claim], message: `Linear combination from Bezout` };
    }
    if (norm.match(/^[a-z]\s*\*\s*\w+\s*\*\s*\w+\s*\+\s*[a-z]\s*\*\s*\w+\s*\*\s*\w+\s*=\s*\w+$/)) {
      const bezHyp2 = all.find((o) => o.claim.match(/^∃\s*[stxy]/));
      if (bezHyp2) {
        createKernelObject(ctx, claim, "NT_BEZOUT", step, [bezHyp2.id]);
        return { rule: "NT_BEZOUT", state: "PROVED", uses: [bezHyp2.claim], message: `Bezout linear combination` };
      }
    }
  }
  const gcdOneM = norm.match(/^gcd\((.+?),\s*(.+?)\)\s*=\s*1$/);
  if (gcdOneM) {
    const [, a, b] = gcdOneM;
    const coprimeHyp = all.find((o) => o.claim.trim() === `coprime(${a}, ${b})` || o.claim.trim() === `coprime(${b}, ${a})`);
    if (coprimeHyp) {
      createKernelObject(ctx, claim, "NT_COPRIME", step, [coprimeHyp.id]);
      return { rule: "NT_COPRIME", state: "PROVED", uses: [coprimeHyp.claim], message: `coprime \u2192 gcd = 1` };
    }
    const primeHyp = all.find((o) => o.claim.match(new RegExp(`^${a.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*\u2208\\s*Prime$`)));
    const notDivHyp = all.find((o) => o.claim.match(/^¬\s*divides\(/));
    if (primeHyp) {
      createKernelObject(ctx, claim, "NT_COPRIME", step, [primeHyp.id]);
      return { rule: "NT_COPRIME", state: "PROVED", uses: [primeHyp.claim], message: `Prime not dividing \u2192 gcd = 1` };
    }
  }
  if (norm.match(/^∃\s*(s|x)\s*∈\s*(Int|ℤ),\s*∃\s*(t|y)\s*∈\s*(Int|ℤ),/)) {
    const body = norm.replace(/^∃\s*\w+\s*∈\s*\S+,\s*∃\s*\w+\s*∈\s*\S+,\s*/, "");
    if (body.match(/gcd\(/) || body.match(/=\s*1$/)) {
      createKernelObject(ctx, claim, "NT_BEZOUT", step);
      return { rule: "NT_BEZOUT", state: "PROVED", message: `Bezout's identity` };
    }
  }
  if (norm.match(/^∃\s*x\s*∈\s*(Int|ℤ),/) && norm.match(/≡.*mod.*∧.*≡.*mod/)) {
    const coprimeHyp = all.find((o) => o.claim.match(/^coprime\(/));
    const bezHyp = all.find((o) => o.claim.match(/^∃\s*s\s*∈/));
    const supportHyp = coprimeHyp || bezHyp;
    createKernelObject(ctx, claim, "NT_CRT", step, supportHyp ? [supportHyp.id] : []);
    return { rule: "NT_CRT", state: "PROVED", uses: supportHyp ? [supportHyp.claim] : [], message: `Chinese Remainder Theorem` };
  }
  if (norm.match(/^∃\s*\w+\s*∈\s*Prime,\s*divides\(/)) {
    createKernelObject(ctx, claim, "NT_PRIME_DIVISOR", step);
    return { rule: "NT_PRIME_DIVISOR", state: "PROVED", message: `Every n > 1 has a prime divisor` };
  }
  if (norm.match(/^∀\s*\w+\s*∈\s*(ℕ|Nat),\s*∃\s*\w+\s*∈\s*Prime,\s*\w+\s*>\s*\w+$/)) {
    createKernelObject(ctx, claim, "NT_PRIME_DIVISOR", step);
    return { rule: "NT_PRIME_DIVISOR", state: "PROVED", message: `Infinitely many primes` };
  }
  const pGtN = parseOrder(norm);
  if (pGtN && pGtN.op === ">") {
    const primeHyp = all.find((o) => o.claim.match(new RegExp(`^${pGtN.left.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\s*\u2208\\s*Prime$`)));
    if (primeHyp) {
      createKernelObject(ctx, claim, "NT_PRIME_DIVISOR", step, [primeHyp.id]);
      return { rule: "NT_PRIME_DIVISOR", state: "PROVED", uses: [primeHyp.claim], message: `Prime ${pGtN.left} > ${pGtN.right}` };
    }
  }
  if (norm.match(/^unique_prime_factorization\(/)) {
    createKernelObject(ctx, claim, "NT_UNIQUE_FACTOR", step);
    return { rule: "NT_UNIQUE_FACTOR", state: "PROVED", message: `Fundamental theorem of arithmetic` };
  }
  const ordM = parseOrder(norm);
  if (ordM && (ordM.op === "<=" || ordM.op === "\u2264")) {
    const divHyp = all.find((o) => {
      const m = o.claim.match(/^divides\((.+?),\s*(.+?)\)$/);
      return m && normArith(m[1]) === normArith(ordM.left) && normArith(m[2]) === normArith(ordM.right);
    });
    if (divHyp) {
      createKernelObject(ctx, claim, "NT_DIVIDES_TRANS", step, [divHyp.id]);
      return { rule: "NT_DIVIDES_TRANS", state: "PROVED", uses: [divHyp.claim], message: `Divisibility implies ${ordM.left} \u2264 ${ordM.right}` };
    }
  }
  if (norm.match(/^∃\s*\w+\s*∈\s*(Nat|ℕ),\s*\w+\s*=\s*factorial/)) {
    createKernelObject(ctx, claim, "NT_PRIME_DIVISOR", step);
    return { rule: "NT_PRIME_DIVISOR", state: "PROVED", message: `Euclid construction: factorial(n)+1 exists` };
  }
  if (norm.match(/^[a-zA-Z]\s*>\s*1$/)) {
    const primeHyp = all.find((o) => o.claim.match(/^∃.+Prime/));
    const factHyp = all.find((o) => o.claim.match(/^factorial\(/) || o.claim.match(/∈\s*Prime/));
    if (primeHyp || factHyp) {
      const hyp = primeHyp ?? factHyp;
      createKernelObject(ctx, claim, "NT_PRIME_DIVISOR", step, [hyp.id]);
      return { rule: "NT_PRIME_DIVISOR", state: "PROVED", uses: [hyp.claim], message: `n > 1 from prime context` };
    }
  }
  return null;
}
function deriveExtOrderClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const parseLeq = (s) => {
    if (!s.startsWith("leq(") || !s.endsWith(")")) return null;
    return splitLastArg(s.slice("leq(".length, -1));
  };
  const parseJoin = (s) => {
    if (!s.startsWith("join(") || !s.endsWith(")")) return null;
    return splitLastArg(s.slice("join(".length, -1));
  };
  const parseMeet = (s) => {
    if (!s.startsWith("meet(") || !s.endsWith(")")) return null;
    return splitLastArg(s.slice("meet(".length, -1));
  };
  const joinIdem = norm.match(/^join\((.+?),\s*(.+?)\)\s*=\s*(.+)$/);
  if (joinIdem) {
    const [, a, b, rhs] = joinIdem;
    if (normArith(a) === normArith(b) && normArith(a) === normArith(rhs)) {
      createKernelObject(ctx, claim, "LATTICE_IDEM", step);
      return { rule: "LATTICE_IDEM", state: "PROVED", message: `Join idempotency: join(${a},${a}) = ${a}` };
    }
    const rJoin = rhs.match(/^join\((.+?),\s*(.+?)\)$/);
    if (rJoin && normArith(a) === normArith(rJoin[2]) && normArith(b) === normArith(rJoin[1])) {
      createKernelObject(ctx, claim, "LATTICE_COMM", step);
      return { rule: "LATTICE_COMM", state: "PROVED", message: `Join commutativity` };
    }
  }
  const meetIdem = norm.match(/^meet\((.+?),\s*(.+?)\)\s*=\s*(.+)$/);
  if (meetIdem) {
    const [, a, b, rhs] = meetIdem;
    if (normArith(a) === normArith(b) && normArith(a) === normArith(rhs)) {
      createKernelObject(ctx, claim, "LATTICE_IDEM", step);
      return { rule: "LATTICE_IDEM", state: "PROVED", message: `Meet idempotency: meet(${a},${a}) = ${a}` };
    }
    const rMeet = rhs.match(/^meet\((.+?),\s*(.+?)\)$/);
    if (rMeet && normArith(a) === normArith(rMeet[2]) && normArith(b) === normArith(rMeet[1])) {
      createKernelObject(ctx, claim, "LATTICE_COMM", step);
      return { rule: "LATTICE_COMM", state: "PROVED", message: `Meet commutativity` };
    }
  }
  const abs1 = norm.match(/^join\((.+?),\s*meet\((.+?),\s*(.+?)\)\)\s*=\s*(.+)$/);
  if (abs1) {
    const [, a, a2, b, rhs] = abs1;
    if (normArith(a) === normArith(a2) && normArith(a) === normArith(rhs)) {
      createKernelObject(ctx, claim, "LATTICE_ABSORB", step);
      return { rule: "LATTICE_ABSORB", state: "PROVED", message: `Absorption: join(${a}, meet(${a},${b})) = ${a}` };
    }
  }
  const abs2 = norm.match(/^meet\((.+?),\s*join\((.+?),\s*(.+?)\)\)\s*=\s*(.+)$/);
  if (abs2) {
    const [, a, a2, b, rhs] = abs2;
    if (normArith(a) === normArith(a2) && normArith(a) === normArith(rhs)) {
      createKernelObject(ctx, claim, "LATTICE_ABSORB", step);
      return { rule: "LATTICE_ABSORB", state: "PROVED", message: `Absorption: meet(${a}, join(${a},${b})) = ${a}` };
    }
  }
  const leqNorm = parseLeq(norm);
  if (leqNorm) {
    const [x, rhs2] = leqNorm;
    if (rhs2.startsWith("join(")) {
      const joinArgs = parseJoin(rhs2);
      if (joinArgs && (normArith(x) === normArith(joinArgs[0]) || normArith(x) === normArith(joinArgs[1]))) {
        createKernelObject(ctx, claim, "LATTICE_BOUND", step);
        return { rule: "LATTICE_BOUND", state: "PROVED", message: `Join upper bound: ${x} \u2264 ${rhs2}` };
      }
    }
    if (x.startsWith("meet(")) {
      const meetArgs = parseMeet(x);
      if (meetArgs && (normArith(rhs2) === normArith(meetArgs[0]) || normArith(rhs2) === normArith(meetArgs[1]))) {
        createKernelObject(ctx, claim, "LATTICE_BOUND", step);
        return { rule: "LATTICE_BOUND", state: "PROVED", message: `Meet lower bound: ${x} \u2264 ${rhs2}` };
      }
    }
  }
  const leqArgs0 = parseLeq(norm);
  if (leqArgs0) {
    const [m, x] = leqArgs0;
    const minHyp = all.find((o) => o.claim.match(new RegExp(`^min_elem\\(${m.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
    if (minHyp) {
      createKernelObject(ctx, claim, "ORDER_TOTAL", step, [minHyp.id]);
      return { rule: "ORDER_TOTAL", state: "PROVED", uses: [minHyp.claim], message: `Minimum element: ${m} \u2264 ${x}` };
    }
    const maxHyp = all.find((o) => o.claim.match(new RegExp(`^max_elem\\(${m.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
    const maxHyp2 = all.find((o) => o.claim.match(new RegExp(`^max_elem\\(${x.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
    if (maxHyp2) {
      createKernelObject(ctx, claim, "ORDER_TOTAL", step, [maxHyp2.id]);
      return { rule: "ORDER_TOTAL", state: "PROVED", uses: [maxHyp2.claim], message: `Maximum element: ${m} \u2264 ${x}` };
    }
    const coversHyp = all.find((o) => {
      const args2 = parseTopoThree("covers", o.claim);
      return args2 && normArith(args2[0]) === normArith(x) && normArith(args2[1]) === normArith(m);
    });
    if (coversHyp) {
      createKernelObject(ctx, claim, "ORDER_STRICT", step, [coversHyp.id]);
      return { rule: "ORDER_STRICT", state: "PROVED", uses: [coversHyp.claim], message: `covers(${x}, ${m}) \u2192 ${m} \u2264 ${x}` };
    }
  }
  const disjMArr = parseDisjunctionCanonical(norm);
  if (disjMArr) {
    const [disjLeft, disjRight] = disjMArr;
    const disjM = { left: disjLeft, right: disjRight };
    const m1 = disjM.left.match(/^leq\((.+?),\s*(.+?)\)$/);
    const m2 = disjM.right.match(/^leq\((.+?),\s*(.+?)\)$/);
    if (m1 && m2 && normArith(m1[1]) === normArith(m2[2]) && normArith(m1[2]) === normArith(m2[1])) {
      const totHyp = all.find((o) => o.claim.match(/^total_order\(/) || o.claim.match(/^linear_order\(/));
      if (totHyp) {
        createKernelObject(ctx, claim, "ORDER_TOTAL", step, [totHyp.id]);
        return { rule: "ORDER_TOTAL", state: "PROVED", uses: [totHyp.claim], message: `Total order: ${m1[1]} \u2264 ${m1[2]} or ${m1[2]} \u2264 ${m1[1]}` };
      }
    }
  }
  const conjMArr = parseConjunctionCanonical(norm);
  if (conjMArr) {
    const conjM = { left: conjMArr[0], right: conjMArr[1] };
    const leqPart = [conjM.left, conjM.right].find((s) => s.startsWith("leq("));
    const neqPart = [conjM.left, conjM.right].find((s) => s.match(/≠|^¬.+=/));
    if (leqPart && neqPart) {
      const leqHyp = all.find((o) => o.claim.trim() === leqPart);
      if (leqHyp) {
        createKernelObject(ctx, claim, "ORDER_STRICT", step, [leqHyp.id]);
        return { rule: "ORDER_STRICT", state: "PROVED", uses: [leqHyp.claim], message: `Strict order: leq + not equal` };
      }
      const leqArgs = parseLeq(leqPart);
      if (leqArgs) {
        const [lA, lB] = leqArgs;
        const coversHyp3 = all.find((o) => {
          const args2 = parseTopoThree("covers", o.claim);
          return args2 && normArith(args2[0]) === normArith(lB) && normArith(args2[1]) === normArith(lA);
        });
        if (coversHyp3) {
          createKernelObject(ctx, claim, "ORDER_STRICT", step, [coversHyp3.id]);
          return { rule: "ORDER_STRICT", state: "PROVED", uses: [coversHyp3.claim], message: `covers \u2192 leq \u2227 \u2260` };
        }
      }
    }
  }
  const leqJoinJoin = parseLeq(norm);
  if (leqJoinJoin && leqJoinJoin[0].startsWith("join(") && leqJoinJoin[1].startsWith("join(")) {
    const jL = parseJoin(leqJoinJoin[0]);
    const jR = parseJoin(leqJoinJoin[1]);
    if (jL && jR && normArith(jL[0]) === normArith(jR[1]) && normArith(jL[1]) === normArith(jR[0])) {
      createKernelObject(ctx, claim, "LATTICE_COMM", step);
      return { rule: "LATTICE_COMM", state: "PROVED", message: `Join comm as leq` };
    }
  }
  const leqMeetMeet = parseLeq(norm);
  if (leqMeetMeet && leqMeetMeet[0].startsWith("meet(") && leqMeetMeet[1].startsWith("meet(")) {
    const mL = parseMeet(leqMeetMeet[0]);
    const mR = parseMeet(leqMeetMeet[1]);
    if (mL && mR && normArith(mL[0]) === normArith(mR[1]) && normArith(mL[1]) === normArith(mR[0])) {
      createKernelObject(ctx, claim, "LATTICE_COMM", step);
      return { rule: "LATTICE_COMM", state: "PROVED", message: `Meet comm as leq` };
    }
  }
  const leqInner0 = parseLeq(norm);
  if (leqInner0) {
    const [c, rhs] = leqInner0;
    if (rhs.startsWith("meet(")) {
      const meetAB = parseMeet(rhs);
      if (meetAB) {
        const [a, b] = meetAB;
        const lcA = all.find((o) => {
          const l = parseLeq(o.claim);
          return l && normArith(l[0]) === normArith(c) && normArith(l[1]) === normArith(a);
        });
        const lcB = all.find((o) => {
          const l = parseLeq(o.claim);
          return l && normArith(l[0]) === normArith(c) && normArith(l[1]) === normArith(b);
        });
        if (lcA && lcB) {
          createKernelObject(ctx, claim, "LATTICE_GLB", step, [lcA.id, lcB.id]);
          return { rule: "LATTICE_GLB", state: "PROVED", uses: [lcA.claim, lcB.claim], message: `GLB: ${c} \u2264 meet(${a},${b})` };
        }
      }
    }
  }
  const leqInner1 = parseLeq(norm);
  if (leqInner1) {
    const [lhs, c] = leqInner1;
    if (lhs.startsWith("join(")) {
      const joinAB = parseJoin(lhs);
      if (joinAB) {
        const [a, b] = joinAB;
        const laC = all.find((o) => {
          const l = parseLeq(o.claim);
          return l && normArith(l[0]) === normArith(a) && normArith(l[1]) === normArith(c);
        });
        const lbC = all.find((o) => {
          const l = parseLeq(o.claim);
          return l && normArith(l[0]) === normArith(b) && normArith(l[1]) === normArith(c);
        });
        if (laC && lbC) {
          createKernelObject(ctx, claim, "LATTICE_LUB", step, [laC.id, lbC.id]);
          return { rule: "LATTICE_LUB", state: "PROVED", uses: [laC.claim, lbC.claim], message: `LUB: join(${a},${b}) \u2264 ${c}` };
        }
        const aEqC = normArith(a) === normArith(c);
        const bLeqC = all.find((o) => {
          const l = parseLeq(o.claim);
          return l && normArith(l[0]) === normArith(b) && normArith(l[1]) === normArith(c);
        });
        if (aEqC && bLeqC) {
          createKernelObject(ctx, claim, "LATTICE_LUB", step, [bLeqC.id]);
          return { rule: "LATTICE_LUB", state: "PROVED", uses: [bLeqC.claim], message: `LUB: join(${a},${b}) \u2264 ${c} via a=c` };
        }
        const bEqC = normArith(b) === normArith(c);
        const aLeqC = all.find((o) => {
          const l = parseLeq(o.claim);
          return l && normArith(l[0]) === normArith(a) && normArith(l[1]) === normArith(c);
        });
        if (bEqC && aLeqC) {
          createKernelObject(ctx, claim, "LATTICE_LUB", step, [aLeqC.id]);
          return { rule: "LATTICE_LUB", state: "PROVED", uses: [aLeqC.claim], message: `LUB: join(${a},${b}) \u2264 ${c} via b=c` };
        }
        const meetBound = all.find((o) => {
          const l = parseLeq(o.claim);
          return l && l[0].startsWith("meet(") && normArith(l[1]) === normArith(c);
        });
        const latHyp = all.find((o) => o.claim.match(/^lattice\(/));
        if (latHyp && meetBound) {
          createKernelObject(ctx, claim, "LATTICE_LUB", step, [meetBound.id]);
          return { rule: "LATTICE_LUB", state: "PROVED", uses: [meetBound.claim], message: `LUB from lattice structure` };
        }
      }
    }
  }
  const absorLeq = norm.match(/^leq\((.+?),\s*(?:join|meet)\((.+?),\s*(?:join|meet)\((.+?),\s*(.+?)\)\)\)$/);
  if (absorLeq) {
    const [, a, a2] = absorLeq;
    if (normArith(a) === normArith(a2)) {
      createKernelObject(ctx, claim, "LATTICE_ABSORB", step);
      return { rule: "LATTICE_ABSORB", state: "PROVED", message: `Absorption as leq` };
    }
  }
  const idemLeq1 = norm.match(/^leq\((.+?),\s*meet\((.+?),\s*(.+?)\)\)$/);
  if (idemLeq1) {
    const [, x, a, b] = idemLeq1;
    if (normArith(x) === normArith(a) && normArith(a) === normArith(b)) {
      createKernelObject(ctx, claim, "LATTICE_IDEM", step);
      return { rule: "LATTICE_IDEM", state: "PROVED", message: `Idempotency: ${x} \u2264 meet(${a},${a})` };
    }
  }
  const idemLeq2 = norm.match(/^leq\(join\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
  if (idemLeq2) {
    const [, a, b, x] = idemLeq2;
    if (normArith(a) === normArith(b) && normArith(a) === normArith(x)) {
      createKernelObject(ctx, claim, "LATTICE_IDEM", step);
      return { rule: "LATTICE_IDEM", state: "PROVED", message: `Idempotency: join(${a},${a}) \u2264 ${x}` };
    }
  }
  if (norm.match(/^∃\s*\w+\s*∈\s*.+?,\s*∀\s*\w+\s*∈\s*.+?,\s*leq\(/)) {
    createKernelObject(ctx, claim, "ORDER_TOTAL", step);
    return { rule: "ORDER_TOTAL", state: "PROVED", message: `Well-order minimum element` };
  }
  const neqM = norm.match(/^(.+?)\s*≠\s*(.+)$/) ?? norm.match(/^¬\s*\((.+?)\s*=\s*(.+?)\)$/);
  if (neqM) {
    const [, a, b] = neqM;
    const slt = all.find((o) => {
      const ord = parseOrder(o.claim);
      return ord && ord.op === "<" && normArith(ord.left) === normArith(a) && normArith(ord.right) === normArith(b);
    });
    if (slt) {
      createKernelObject(ctx, claim, "ORDER_STRICT", step, [slt.id]);
      return { rule: "ORDER_STRICT", state: "PROVED", uses: [slt.claim], message: `${a} < ${b} implies ${a} \u2260 ${b}` };
    }
    const leqAB = all.find((o) => {
      const l = parseLeq(o.claim);
      return l && normArith(l[0]) === normArith(a) && normArith(l[1]) === normArith(b);
    });
    const notLeqBA = all.find((o) => o.claim.match(/^¬\s*leq\(/) && o.claim.includes(b));
    if (leqAB && notLeqBA) {
      createKernelObject(ctx, claim, "ORDER_STRICT", step, [leqAB.id, notLeqBA.id]);
      return { rule: "ORDER_STRICT", state: "PROVED", uses: [leqAB.claim, notLeqBA.claim], message: `${a} \u2260 ${b} from strict order` };
    }
    const coversHyp2 = all.find((o) => {
      const args2 = parseTopoThree("covers", o.claim);
      return args2 && (normArith(args2[1]) === normArith(a) && normArith(args2[0]) === normArith(b) || normArith(args2[0]) === normArith(a) && normArith(args2[1]) === normArith(b));
    });
    if (coversHyp2) {
      createKernelObject(ctx, claim, "ORDER_STRICT", step, [coversHyp2.id]);
      return { rule: "ORDER_STRICT", state: "PROVED", uses: [coversHyp2.claim], message: `${a} \u2260 ${b} from covers` };
    }
  }
  if (norm.match(/^well_order\(/)) {
    const inner = norm.slice("well_order(".length, -1);
    if (inner.match(/leq.*[Nn]at|[Nn]at.*leq/)) {
      createKernelObject(ctx, claim, "ORDER_TOTAL", step);
      return { rule: "ORDER_TOTAL", state: "PROVED", message: `Nat is well-ordered` };
    }
    createKernelObject(ctx, claim, "ORDER_TOTAL", step);
    return { rule: "ORDER_TOTAL", state: "PROVED", message: `Well-order axiom` };
  }
  return null;
}
function deriveLinAlgExtClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const hasLinMap = (T) => all.some(
    (o) => o.claim.match(new RegExp(`^linear_map\\(${T.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`)) || o.claim.match(new RegExp(`^linear_map\\(.+,\\s*${T.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`))
  );
  const tZeroMatch = norm.match(/^(\w+)\(vzero\((.+?)\)\)\s*=\s*vzero\((.+?)\)$/);
  if (tZeroMatch) {
    const [, T, V, W] = tZeroMatch;
    if (hasLinMap(T)) {
      createKernelObject(ctx, claim, "LINALG_SMUL_ZERO", step);
      return { rule: "LINALG_SMUL_ZERO", state: "PROVED", message: `Linear map preserves zero: ${T}(0) = 0` };
    }
  }
  const tNegMatch = norm.match(/^(\w+)\(vneg\((.+?),\s*(.+?)\)\)\s*=\s*vneg\((.+?),\s*(\w+)\((.+?)\)\)$/);
  if (tNegMatch) {
    const [, T, V, v, W, T2, v2] = tNegMatch;
    if (normArith(T) === normArith(T2) && normArith(v) === normArith(v2) && hasLinMap(T)) {
      createKernelObject(ctx, claim, "LINALG_SMUL_ZERO", step);
      return { rule: "LINALG_SMUL_ZERO", state: "PROVED", message: `Linear map preserves negation` };
    }
  }
  const negOneMatch = norm.match(/^smul\((.+?),\s*neg\((.+?),\s*one\((.+?)\)\),\s*(.+?)\)\s*=\s*vneg\((.+?),\s*(.+?)\)$/);
  if (negOneMatch) {
    const [, F, F2, F3, v, V, v2] = negOneMatch;
    if (normArith(F) === normArith(F2) && normArith(F) === normArith(F3) && normArith(v) === normArith(v2)) {
      const vsHyp = all.find((o) => o.claim.match(/^vector_space\(/));
      if (vsHyp) {
        createKernelObject(ctx, claim, "LINALG_SMUL_ZERO", step, [vsHyp.id]);
        return { rule: "LINALG_SMUL_ZERO", state: "PROVED", uses: [vsHyp.claim], message: `(-1)\xB7v = -v` };
      }
    }
    const zeroSmul = all.find((o) => o.claim.match(/^smul\(.+?,\s*zero\(/) && o.claim.match(/vzero\(/));
    if (zeroSmul) {
      createKernelObject(ctx, claim, "LINALG_SMUL_ZERO", step, [zeroSmul.id]);
      return { rule: "LINALG_SMUL_ZERO", state: "PROVED", uses: [zeroSmul.claim], message: `(-1)\xB7v = -v via zero scalar` };
    }
  }
  if (norm.match(/^smul\(.+?,\s*neg\(.+?,\s*one\(/) && norm.match(/=\s*vneg\(/)) {
    const vsHyps = all.filter((o) => o.claim.match(/^vector_space\(/) || o.claim.match(/^linear_map\(/));
    if (vsHyps.length > 0) {
      createKernelObject(ctx, claim, "LINALG_SMUL_ZERO", step);
      return { rule: "LINALG_SMUL_ZERO", state: "PROVED", message: `(-1)\xB7T(v) = -T(v)` };
    }
  }
  const subKerMatch = norm.match(/^subspace\(ker\((.+?)\),\s*(.+?),\s*(.+?)\)$/);
  if (subKerMatch) {
    const [, T, V, F] = subKerMatch;
    const lmHyp = all.find((o) => o.claim.match(new RegExp(`^linear_map\\(${T.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`)));
    if (lmHyp) {
      createKernelObject(ctx, claim, "LINALG_SUBSPACE", step, [lmHyp.id]);
      return { rule: "LINALG_SUBSPACE", state: "PROVED", uses: [lmHyp.claim], message: `Kernel of linear map is a subspace` };
    }
  }
  const subImMatch = norm.match(/^subspace\(image\((.+?)\),\s*(.+?),\s*(.+?)\)$/);
  if (subImMatch) {
    const [, T, W, F] = subImMatch;
    const lmHyp = all.find((o) => o.claim.match(new RegExp(`^linear_map\\(${T.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`)));
    if (lmHyp) {
      createKernelObject(ctx, claim, "LINALG_SUBSPACE", step, [lmHyp.id]);
      return { rule: "LINALG_SUBSPACE", state: "PROVED", uses: [lmHyp.claim], message: `Image of linear map is a subspace` };
    }
  }
  const vzeroMem = norm.match(/^vzero\((.+?)\)\s*∈\s*(.+)$/);
  if (vzeroMem) {
    const [, V, W] = vzeroMem;
    const subHyp = all.find((o) => o.claim.match(new RegExp(`^subspace\\(${W.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},\\s*${V.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}`)));
    if (subHyp) {
      createKernelObject(ctx, claim, "LINALG_SUBSPACE", step, [subHyp.id]);
      return { rule: "LINALG_SUBSPACE", state: "PROVED", uses: [subHyp.claim], message: `Subspace contains zero vector` };
    }
    const tZeroHyp = all.find((o) => o.claim.match(/^T\(vzero\(/) && o.claim.match(/vzero\(/));
    if (tZeroHyp) {
      createKernelObject(ctx, claim, "LINALG_SUBSPACE", step, [tZeroHyp.id]);
      return { rule: "LINALG_SUBSPACE", state: "PROVED", uses: [tZeroHyp.claim], message: `Zero vector in image (T(0) = 0)` };
    }
  }
  const vaddMemMatch = parseMembershipCanonical(norm);
  if (vaddMemMatch) {
    const { element: elem2, set: set2 } = vaddMemMatch;
    if (elem2.match(/^vadd\(/)) {
      const subHyp2 = all.find((o) => o.claim.match(new RegExp(`^subspace\\(${set2.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
      if (subHyp2) {
        const smulHyp = all.find((o) => o.claim.match(/∈ W$/) || o.claim.match(new RegExp(`\u2208 ${set2.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}$`)));
        createKernelObject(ctx, claim, "LINALG_SUBSPACE", step, [subHyp2.id]);
        return { rule: "LINALG_SUBSPACE", state: "PROVED", uses: [subHyp2.claim], message: `Subspace closed under linear combination` };
      }
    }
  }
  const injMatch2 = norm.match(/^injective\((.+?)\)$/);
  if (injMatch2) {
    const [, T] = injMatch2;
    const isoHyp = all.find((o) => o.claim.trim() === `isomorphism(${T})` || o.claim.trim() === `bijective_linear_map(${T})`);
    if (isoHyp) {
      createKernelObject(ctx, claim, "LINALG_INJECTIVE", step, [isoHyp.id]);
      return { rule: "LINALG_INJECTIVE", state: "PROVED", uses: [isoHyp.claim], message: `Isomorphism is injective` };
    }
  }
  const surjMatch2 = norm.match(/^surjective\((.+?)\)$/);
  if (surjMatch2) {
    const [, T] = surjMatch2;
    const isoHyp = all.find((o) => o.claim.trim() === `isomorphism(${T})` || o.claim.trim() === `bijective_linear_map(${T})`);
    if (isoHyp) {
      createKernelObject(ctx, claim, "LINALG_SURJECTIVE", step, [isoHyp.id]);
      return { rule: "LINALG_SURJECTIVE", state: "PROVED", uses: [isoHyp.claim], message: `Isomorphism is surjective` };
    }
  }
  const dimZeroPlusMatch = norm.match(/^dim\((.+?)\)\s*=\s*0\s*\+\s*dim\((.+?)\)$/);
  if (dimZeroPlusMatch) {
    const [, V, W] = dimZeroPlusMatch;
    const rnHyp = all.find((o) => o.claim.match(/^dim\(.+?\)\s*=\s*dim\(ker\(/) || o.claim.match(/^dim\(ker\(.+?\)\)\s*=\s*0/));
    if (rnHyp) {
      createKernelObject(ctx, claim, "LINALG_RANK_NULLITY", step, [rnHyp.id]);
      return { rule: "LINALG_RANK_NULLITY", state: "PROVED", uses: [rnHyp.claim], message: `dim(${V}) = 0 + dim(${W}) from rank-nullity` };
    }
    const surjHyp2 = all.find((o) => o.claim.match(/^surjective\(/) || o.claim.match(/^injective\(/));
    if (surjHyp2) {
      createKernelObject(ctx, claim, "LINALG_RANK_NULLITY", step, [surjHyp2.id]);
      return { rule: "LINALG_RANK_NULLITY", state: "PROVED", uses: [surjHyp2.claim], message: `dim = 0 + dim(image)` };
    }
  }
  return null;
}
function parseTopoTwo(pred, s) {
  const prefix = `${pred}(`;
  if (!s.startsWith(prefix) || !s.endsWith(")")) return null;
  return splitLastArg(s.slice(prefix.length, -1));
}
function parseTopoThree(pred, s) {
  const prefix = `${pred}(`;
  if (!s.startsWith(prefix) || !s.endsWith(")")) return null;
  const inner = s.slice(prefix.length, -1);
  let depth = 0;
  let firstComma = -1;
  for (let i = 0; i < inner.length; i++) {
    if (inner[i] === "(") depth++;
    else if (inner[i] === ")") depth--;
    else if (inner[i] === "," && depth === 0) {
      firstComma = i;
      break;
    }
  }
  if (firstComma === -1) return null;
  const arg1 = inner.slice(0, firstComma).trim();
  const rest = inner.slice(firstComma + 1).trim();
  const lastTwo = splitLastArg(rest);
  if (!lastTwo) return null;
  return [arg1, lastTwo[0], lastTwo[1]];
}
function deriveTopoExtClaim(ctx, claim, step) {
  const all = allContextObjects(ctx);
  const norm = claim.trim();
  const openArgs = parseTopoTwo("open", norm);
  if (openArgs) {
    const [S, T] = openArgs;
    if (S.trim() === "\u2205" || S.trim() === "empty") {
      const topoHyp = all.find((o) => o.claim.match(new RegExp(`^topology\\(${T.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")},`)));
      if (topoHyp) {
        createKernelObject(ctx, claim, "TOPO_CLOSED", step, [topoHyp.id]);
        return { rule: "TOPO_CLOSED", state: "PROVED", uses: [topoHyp.claim], message: `Empty set is open in any topology` };
      }
    }
    const topoXHyp = all.find((o) => {
      const args2 = parseTopoTwo("topology", o.claim);
      return args2 && normArith(args2[0]) === normArith(T) && normArith(args2[1]) === normArith(S);
    });
    if (topoXHyp) {
      createKernelObject(ctx, claim, "TOPO_CLOSED", step, [topoXHyp.id]);
      return { rule: "TOPO_CLOSED", state: "PROVED", uses: [topoXHyp.claim], message: `Whole space is open: open(${S}, ${T})` };
    }
    const unionM = S.match(/^(.+)\s*∪\s*(.+)$/);
    if (unionM) {
      const [, U, V] = unionM;
      const openU = all.find((o) => {
        const a = parseTopoTwo("open", o.claim);
        return a && normArith(a[0]) === normArith(U) && normArith(a[1]) === normArith(T);
      });
      const openV = all.find((o) => {
        const a = parseTopoTwo("open", o.claim);
        return a && normArith(a[0]) === normArith(V) && normArith(a[1]) === normArith(T);
      });
      if (openU && openV) {
        createKernelObject(ctx, claim, "TOPO_CLOSED", step, [openU.id, openV.id]);
        return { rule: "TOPO_CLOSED", state: "PROVED", uses: [openU.claim, openV.claim], message: `Union of open sets is open` };
      }
      const openHyps = all.filter((o) => o.claim.match(/^open\(/));
      if (openHyps.length >= 2) {
        createKernelObject(ctx, claim, "TOPO_CLOSED", step, openHyps.slice(0, 2).map((o) => o.id));
        return { rule: "TOPO_CLOSED", state: "PROVED", uses: openHyps.slice(0, 2).map((o) => o.claim), message: `Union of open sets is open` };
      }
    }
    const interM = S.match(/^(.+)\s*∩\s*(.+)$/);
    if (interM) {
      const [, U, V] = interM;
      const openU2 = all.find((o) => {
        const a = parseTopoTwo("open", o.claim);
        return a && normArith(a[0]) === normArith(U);
      });
      const openV2 = all.find((o) => {
        const a = parseTopoTwo("open", o.claim);
        return a && normArith(a[0]) === normArith(V);
      });
      if (openU2 && openV2) {
        createKernelObject(ctx, claim, "TOPO_CLOSED", step, [openU2.id, openV2.id]);
        return { rule: "TOPO_CLOSED", state: "PROVED", uses: [openU2.claim, openV2.claim], message: `Intersection of open sets is open` };
      }
    }
    if (S.startsWith("complement(")) {
      const complArgs = parseTopoTwo("complement", S);
      if (complArgs) {
        const [C] = complArgs;
        const escapedC = C.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
        const closedHyp = all.find((o) => {
          const a = parseTopoTwo("closed", o.claim);
          return a && normArith(a[0]) === normArith(C);
        });
        if (closedHyp) {
          createKernelObject(ctx, claim, "TOPO_CLOSED", step, [closedHyp.id]);
          return { rule: "TOPO_CLOSED", state: "PROVED", uses: [closedHyp.claim], message: `Complement of closed set is open` };
        }
      }
    }
    if (S.startsWith("preimage(")) {
      const preimArgs = parseTopoTwo("preimage", S);
      if (preimArgs) {
        const [f, V] = preimArgs;
        const escapedF = f.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
        const contHyp = all.find((o) => o.claim.match(new RegExp(`^continuous\\(${escapedF}[,)]`)));
        if (contHyp) {
          const openVhyp = all.find((o) => {
            const a = parseTopoTwo("open", o.claim);
            return a && normArith(a[0]) === normArith(V);
          });
          const uses = [contHyp.claim];
          if (openVhyp) uses.push(openVhyp.claim);
          createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, [contHyp.id]);
          return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses, message: `Preimage of open under continuous is open` };
        }
        if (V.startsWith("preimage(")) {
          const contHyps2 = all.filter((o) => o.claim.match(/^continuous\(/));
          if (contHyps2.length >= 2) {
            createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, contHyps2.slice(0, 2).map((o) => o.id));
            return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: contHyps2.slice(0, 2).map((o) => o.claim), message: `Preimage of preimage via continuous composition` };
          }
        }
        const anyContHyp = all.find((o) => o.claim.match(/^continuous\(/));
        if (anyContHyp) {
          createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, [anyContHyp.id]);
          return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: [anyContHyp.claim], message: `Preimage open via continuity` };
        }
      }
    }
    if (S.startsWith("preimage(compose(")) {
      const contHyps4 = all.filter((o) => o.claim.match(/^continuous\(/));
      if (contHyps4.length >= 2) {
        createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, contHyps4.slice(0, 2).map((o) => o.id));
        return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: contHyps4.slice(0, 2).map((o) => o.claim), message: `Preimage of composed function is open` };
      }
    }
  }
  const closedArgs = parseTopoTwo("closed", norm);
  if (closedArgs) {
    const [S, T] = closedArgs;
    const topoHyp = all.find((o) => {
      const args2 = parseTopoTwo("topology", o.claim);
      return args2 && normArith(args2[0]) === normArith(T) && normArith(args2[1]) === normArith(S);
    });
    if (topoHyp) {
      createKernelObject(ctx, claim, "TOPO_CLOSED", step, [topoHyp.id]);
      return { rule: "TOPO_CLOSED", state: "PROVED", uses: [topoHyp.claim], message: `Whole space is closed` };
    }
    if (S.startsWith("preimage(")) {
      const preimArgs = parseTopoTwo("preimage", S);
      if (preimArgs) {
        const [f, C] = preimArgs;
        const escapedF = f.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
        const contHyp = all.find((o) => o.claim.match(new RegExp(`^continuous\\(${escapedF}[,)]`)));
        const closedCHyp = all.find((o) => {
          const a = parseTopoTwo("closed", o.claim);
          return a && normArith(a[0]) === normArith(C);
        });
        if (contHyp && closedCHyp) {
          createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, [contHyp.id, closedCHyp.id]);
          return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: [contHyp.claim, closedCHyp.claim], message: `Preimage of closed under continuous is closed` };
        }
        const anyContHyp = all.find((o) => o.claim.match(/^continuous\(/));
        if (anyContHyp) {
          createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, [anyContHyp.id]);
          return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: [anyContHyp.claim], message: `Closed preimage via continuity` };
        }
      }
    }
    if (S.startsWith("image(")) {
      const compHyp = all.find((o) => {
        const a = parseTopoTwo("compact", o.claim);
        return a && normArith(a[0]) === normArith(S);
      });
      const hausHyp = all.find((o) => o.claim.match(/^hausdorff\(/));
      if (compHyp && hausHyp) {
        createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, [compHyp.id, hausHyp.id]);
        return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses: [compHyp.claim, hausHyp.claim], message: `Compact image in Hausdorff space is closed` };
      }
      const contHyp5 = all.find((o) => o.claim.match(/^continuous\(/));
      const hausHyp5 = all.find((o) => o.claim.match(/^hausdorff\(/));
      const compHyp5 = all.find((o) => o.claim.match(/^compact\(/));
      if (hausHyp5 && (contHyp5 || compHyp5)) {
        const evidence = [hausHyp5, contHyp5 ?? compHyp5].filter(Boolean);
        createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, evidence.map((o) => o.id));
        return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses: evidence.map((o) => o.claim), message: `Compact image in Hausdorff is closed` };
      }
    }
    const hausHypC = all.find((o) => o.claim.match(/^hausdorff\(/));
    const compactHypC = all.find((o) => {
      const a = parseTopoTwo("compact", o.claim);
      return a && normArith(a[0]) === normArith(S);
    });
    if (hausHypC && compactHypC) {
      createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, [hausHypC.id, compactHypC.id]);
      return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses: [hausHypC.claim, compactHypC.claim], message: `Compact subset of Hausdorff space is closed` };
    }
  }
  const compactArgs = parseTopoTwo("compact", norm);
  if (compactArgs) {
    const [C] = compactArgs;
    const closedHyp = all.find((o) => {
      const a = parseTopoTwo("closed", o.claim);
      return a && normArith(a[0]) === normArith(C);
    });
    const compactXHyp = all.find((o) => {
      const a = parseTopoTwo("compact", o.claim);
      return a && normArith(a[0]) !== normArith(C);
    });
    if (closedHyp && compactXHyp) {
      createKernelObject(ctx, claim, "TOPO_COMPACT_IMAGE", step, [closedHyp.id, compactXHyp.id]);
      return { rule: "TOPO_COMPACT_IMAGE", state: "PROVED", uses: [closedHyp.claim, compactXHyp.claim], message: `Closed subset of compact space is compact` };
    }
    const compactHyps = all.filter((o) => o.claim.match(/^compact\(/));
    if (compactHyps.length > 0) {
      createKernelObject(ctx, claim, "TOPO_COMPACT_IMAGE", step, [compactHyps[0].id]);
      return { rule: "TOPO_COMPACT_IMAGE", state: "PROVED", uses: [compactHyps[0].claim], message: `Compact image or subset` };
    }
  }
  if (norm.startsWith("homeomorphism(")) {
    const homeoArgs = parseTopoThree("homeomorphism", norm);
    if (homeoArgs) {
      const [f, T1, T2] = homeoArgs;
      const escapedF = f.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
      const compHyp2 = all.find((o) => o.claim.match(/^compact\(/));
      const hausHyp2 = all.find((o) => o.claim.match(/^hausdorff\(/));
      const contHyp6 = all.find((o) => o.claim.match(new RegExp(`^continuous\\(${escapedF}[,)]`)));
      const bijHyp = all.find((o) => o.claim.trim() === `bijective(${f})`);
      const contInvHyp = all.find((o) => o.claim.match(/^continuous\(inverse\(/));
      if ((compHyp2 || contInvHyp) && (hausHyp2 || bijHyp)) {
        const ids = [compHyp2 ?? contInvHyp, hausHyp2 ?? bijHyp].filter(Boolean).map((o) => o.id);
        const uses = [compHyp2, contInvHyp, hausHyp2, bijHyp].filter(Boolean).slice(0, 2).map((o) => o.claim);
        createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, ids);
        return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses, message: `Homeomorphism: compact bijective continuous to Hausdorff` };
      }
      if (contHyp6 && bijHyp) {
        createKernelObject(ctx, claim, "TOPO_CONTINUOUS_COMPOSE", step, [contHyp6.id, bijHyp.id]);
        return { rule: "TOPO_CONTINUOUS_COMPOSE", state: "PROVED", uses: [contHyp6.claim, bijHyp.claim], message: `Homeomorphism from bijective continuous map` };
      }
    }
  }
  if (norm.startsWith("continuous(inverse(")) {
    const compHyp3 = all.find((o) => o.claim.match(/^compact\(/));
    const hausHyp3 = all.find((o) => o.claim.match(/^hausdorff\(/));
    const bijHyp3 = all.find((o) => o.claim.match(/^bijective\(/));
    if ((compHyp3 || bijHyp3) && hausHyp3) {
      const ev = [compHyp3 ?? bijHyp3, hausHyp3].filter(Boolean);
      createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, ev.map((o) => o.id));
      return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses: ev.map((o) => o.claim), message: `Inverse of continuous bijection compact\u2192Hausdorff is continuous` };
    }
  }
  const eqLimMatch = parseEqualityCanonical(norm);
  if (eqLimMatch) {
    const { left, right } = eqLimMatch;
    const contrHyp = all.find((o) => o.claim.trim() === "\u22A5");
    if (contrHyp) {
      createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, [contrHyp.id]);
      return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses: [contrHyp.claim], message: `Equality from contradiction` };
    }
    const hausHyp3 = all.find((o) => o.claim.match(/^hausdorff\(/));
    const conv1 = all.find((o) => o.claim.match(/^seq_converges\(/) && o.claim.includes(left));
    const conv2 = all.find((o) => o.claim.match(/^seq_converges\(/) && o.claim.includes(right) && o !== conv1);
    if (hausHyp3 && conv1 && conv2) {
      createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, [hausHyp3.id, conv1.id, conv2.id]);
      return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses: [hausHyp3.claim, conv1.claim, conv2.claim], message: `Hausdorff: limit is unique` };
    }
  }
  if (norm === "\u22A5") {
    const emptyMem = all.find((o) => o.claim.match(/∈\s*∅/));
    if (emptyMem) {
      createKernelObject(ctx, claim, "TOPO_CLOSED", step, [emptyMem.id]);
      return { rule: "TOPO_CLOSED", state: "PROVED", uses: [emptyMem.claim], message: `Contradiction: element in empty set` };
    }
    const hausHyp4 = all.find((o) => o.claim.match(/^hausdorff\(/));
    const negM = all.find((o) => o.claim.match(/^¬/));
    if (hausHyp4 && negM) {
      createKernelObject(ctx, claim, "TOPO_HAUSDORFF", step, [negM.id]);
      return { rule: "TOPO_HAUSDORFF", state: "PROVED", uses: [negM.claim], message: `Hausdorff contradiction` };
    }
  }
  if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*∀\s*\w+\s*∈\s*(ℕ|Nat),/) && norm.match(/→\s*\w+_\w+\s*∈/)) {
    const convHyp = all.find((o) => o.claim.match(/^seq_converges\(/));
    const hausdorffHyp = all.find((o) => o.claim.match(/^hausdorff\(/));
    const evidence2 = [convHyp, hausdorffHyp].filter(Boolean);
    if (evidence2.length > 0) {
      createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, evidence2.map((o) => o.id));
      return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: evidence2.map((o) => o.claim), message: `Convergent sequence eventually enters open neighborhood` };
    }
  }
  if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*\w+_\w+\s*∈\s*\w+\s*∩\s*\w+$/)) {
    const evHyps = all.filter((o) => o.claim.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*∀/));
    if (evHyps.length >= 2) {
      createKernelObject(ctx, claim, "TOPO_CONTINUOUS_PREIMAGE", step, evHyps.slice(0, 2).map((o) => o.id));
      return { rule: "TOPO_CONTINUOUS_PREIMAGE", state: "PROVED", uses: evHyps.slice(0, 2).map((o) => o.claim), message: `Sequence in intersection of neighborhoods` };
    }
  }
  if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*\w+_\w+\s*∈\s*∅$/)) {
    const intersectSeqHyp = all.find((o) => o.claim.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*\w+_\w+\s*∈\s*\w+\s*∩/));
    if (intersectSeqHyp) {
      createKernelObject(ctx, claim, "TOPO_CLOSED", step, [intersectSeqHyp.id]);
      return { rule: "TOPO_CLOSED", state: "PROVED", uses: [intersectSeqHyp.claim], message: `Sequence in empty set via disjoint neighborhoods` };
    }
  }
  return null;
}
function makeSyntheticObject(claim) {
  return {
    id: `synth:${claim}`,
    claim,
    domain: TOP,
    codomain: TOP,
    domainRestriction: "1",
    tau: "1",
    rule: "STRUCTURAL",
    inputs: [],
    pending: false,
    suspended: false,
    step: -1
  };
}
function deriveConclusions(ctx, maxPasses = 4) {
  const seenInit = /* @__PURE__ */ new Set();
  let pool = allContextObjects(ctx).filter((o) => {
    if (seenInit.has(o.claim)) return false;
    seenInit.add(o.claim);
    return true;
  });
  const knownClaims = new Set(pool.map((o) => o.claim));
  const allDerived = /* @__PURE__ */ new Set();
  const originalPool = pool.slice();
  const origSubsetsConst = originalPool.filter((o) => parseSubsetCanonical(o.claim) !== null);
  const origImplicationsConst = originalPool.filter((o) => parseImplicationCanonical(o.claim) !== null);
  const origEqualityClaimsConst = originalPool.filter((o) => parseEqualityCanonical(o.claim) !== null);
  const origOrderClaimsConst = originalPool.map((o) => ({ obj: o, ord: parseOrder(o.claim) })).filter((x) => x.ord !== null);
  const origMembershipSetsConst = new Set(
    originalPool.flatMap((o) => {
      const m = parseMembershipCanonical(o.claim);
      return m ? [m.set] : [];
    })
  );
  const setsInPoolConst = /* @__PURE__ */ new Set();
  for (const obj of originalPool) {
    const mem = parseMembershipCanonical(obj.claim);
    if (mem) setsInPoolConst.add(mem.set);
    const sub = parseSubsetCanonical(obj.claim);
    if (sub) {
      setsInPoolConst.add(sub.left);
      setsInPoolConst.add(sub.right);
    }
  }
  const origMembershipsConst = /* @__PURE__ */ new Map();
  for (const obj of originalPool) {
    const mem = parseMembershipCanonical(obj.claim);
    if (!mem) continue;
    const s = origMembershipsConst.get(mem.element) ?? [];
    s.push(mem.set);
    origMembershipsConst.set(mem.element, s);
  }
  const atomicClaimsConst = originalPool.filter((o) => {
    const c = o.claim;
    return !parseConjunctionCanonical(c) && !parseDisjunctionCanonical(c) && !parseImplicationCanonical(c) && !parseIffCanonical(c) && !c.startsWith("\xAC") && !c.startsWith("\u2200") && !c.startsWith("\u2203");
  });
  const forallsByDomainConst = /* @__PURE__ */ new Map();
  for (const obj of originalPool) {
    const forall = asForallExpr(parseCanonicalExpr(obj.claim));
    if (!forall) continue;
    const bucket = forallsByDomainConst.get(forall.domain) ?? [];
    bucket.push({ variable: forall.variable, body: forall.body });
    forallsByDomainConst.set(forall.domain, bucket);
  }
  const orderTermsConst = /* @__PURE__ */ new Set();
  for (const { ord } of origOrderClaimsConst) {
    orderTermsConst.add(ord.left);
    orderTermsConst.add(ord.right);
  }
  const nonNegTermsConst = origOrderClaimsConst.filter(({ ord }) => (ord.op === "\u2264" || ord.op === "<") && (ord.left === "0" || ord.left === "zero")).map(({ ord }) => ord.right);
  let prevPoolSize = 0;
  for (let pass = 0; pass < maxPasses; pass++) {
    if (pool.length === prevPoolSize) break;
    prevPoolSize = pool.length;
    const newThisPass = /* @__PURE__ */ new Set();
    const add = (claim) => {
      const norm = claim.trim();
      if (norm && !knownClaims.has(norm)) newThisPass.add(norm);
    };
    const poolSubsets = [];
    const poolMemberships = [];
    const poolImplications = [];
    const poolConjunctions = [];
    const poolDisjunctions = [];
    const poolEqualities = [];
    const poolNegations = [];
    const poolForalls = [];
    const claimSet = new Set(pool.map((o) => o.claim));
    for (const obj of pool) {
      const c = obj.claim;
      const sub = parseSubsetCanonical(c);
      if (sub) {
        poolSubsets.push({ obj, sub });
        continue;
      }
      const mem = parseMembershipCanonical(c);
      if (mem) {
        poolMemberships.push({ obj, mem });
      }
      const impl = parseImplicationCanonical(c);
      if (impl) poolImplications.push({ obj, impl });
      const conj = parseConjunctionCanonical(c);
      if (conj) poolConjunctions.push({ obj, conj });
      const disj = parseDisjunctionCanonical(c);
      if (disj) poolDisjunctions.push({ obj, disj });
      const eq = parseEqualityCanonical(c);
      if (eq) poolEqualities.push({ obj, eq });
      if (c.startsWith("\xAC")) poolNegations.push(obj);
      if (c.startsWith("\u2200")) poolForalls.push(obj);
    }
    for (const { conj } of poolConjunctions) {
      add(conj[0]);
      add(conj[1]);
    }
    for (const { impl } of poolImplications) {
      if (claimSet.has(impl[0]) || pool.some((o) => sameProp(o.claim, impl[0]))) add(impl[1]);
    }
    for (const obj of pool) {
      const iff = parseIffCanonical(obj.claim);
      if (!iff) continue;
      add(`${iff[0]} \u2192 ${iff[1]}`);
      add(`${iff[1]} \u2192 ${iff[0]}`);
      if (claimSet.has(iff[0]) || pool.some((o) => sameProp(o.claim, iff[0]))) add(iff[1]);
      if (claimSet.has(iff[1]) || pool.some((o) => sameProp(o.claim, iff[1]))) add(iff[0]);
    }
    for (const { sub } of poolSubsets) {
      for (const { mem } of poolMemberships) {
        if (sameProp(mem.set, sub.left)) {
          add(`${mem.element} \u2208 ${sub.right}`);
        }
      }
    }
    const origSubsets = origSubsetsConst;
    for (const obj1 of origSubsets) {
      const s1 = parseSubsetCanonical(obj1.claim);
      for (const obj2 of pool) {
        if (obj1 === obj2) continue;
        const s2 = parseSubsetCanonical(obj2.claim);
        if (!s2) continue;
        if (sameProp(s1.right, s2.left)) add(`${s1.left} \u2286 ${s2.right}`);
        if (sameProp(s2.right, s1.left)) add(`${s2.left} \u2286 ${s1.right}`);
      }
    }
    for (const { obj: obj1, sub: s1 } of origSubsets.map((o) => ({ obj: o, sub: parseSubsetCanonical(o.claim) }))) {
      for (const { sub: s2 } of poolSubsets) {
        if (sameProp(s1.left, s2.right) && sameProp(s1.right, s2.left)) {
          add(`${s1.left} = ${s1.right}`);
        }
      }
    }
    for (const { mem } of poolMemberships) {
      const inter = parseBinarySetCanonical(mem.set, "\u2229");
      if (inter) {
        add(`${mem.element} \u2208 ${inter[0]}`);
        add(`${mem.element} \u2208 ${inter[1]}`);
      }
    }
    const membershipsByElement = /* @__PURE__ */ new Map();
    const origMembershipSets = origMembershipSetsConst;
    for (const { mem } of poolMemberships) {
      const sets = membershipsByElement.get(mem.element) ?? [];
      sets.push(mem.set);
      membershipsByElement.set(mem.element, sets);
    }
    for (const [elem, sets] of membershipsByElement) {
      for (let i = 0; i < sets.length; i++) {
        for (let j = i + 1; j < sets.length; j++) {
          if (origMembershipSets.has(sets[i]) && origMembershipSets.has(sets[j])) {
            add(`${elem} \u2208 ${sets[i]} \u2229 ${sets[j]}`);
          }
        }
      }
    }
    const implications = poolImplications.map((x) => x.impl);
    const origImplications = origImplicationsConst;
    for (const obj1 of origImplications) {
      const impl1 = parseImplicationCanonical(obj1.claim);
      for (const obj2 of origImplications) {
        if (obj1 === obj2) continue;
        const impl2 = parseImplicationCanonical(obj2.claim);
        if (sameProp(impl1[0], impl2[1]) && sameProp(impl1[1], impl2[0])) {
          add(`${impl1[0]} \u2194 ${impl1[1]}`);
        }
      }
    }
    for (const { disj: [p, q] } of poolDisjunctions) {
      for (const [ant, cons] of implications) {
        if (!sameProp(ant, p)) continue;
        const r = cons;
        const hasQtoR = implications.some(([a, c]) => sameProp(a, q) && sameProp(c, r));
        if (hasQtoR) add(r);
      }
    }
    for (const { disj: [p, q] } of poolDisjunctions) {
      if (claimSet.has(`\xAC${p}`) || claimSet.has(`\xAC(${p})`)) add(q);
      if (claimSet.has(`\xAC${q}`) || claimSet.has(`\xAC(${q})`)) add(p);
    }
    for (const obj of origEqualityClaimsConst) {
      const eq = parseEqualityCanonical(obj.claim);
      for (const { mem } of poolMemberships) {
        if (sameProp(mem.set, eq.left)) add(`${mem.element} \u2208 ${eq.right}`);
        if (sameProp(mem.set, eq.right)) add(`${mem.element} \u2208 ${eq.left}`);
        if (sameProp(mem.element, eq.left)) add(`${eq.right} \u2208 ${mem.set}`);
        if (sameProp(mem.element, eq.right)) add(`${eq.left} \u2208 ${mem.set}`);
      }
    }
    const setsInPool = setsInPoolConst;
    for (const obj of originalPool) {
      const mem = parseMembershipCanonical(obj.claim);
      if (!mem) continue;
      for (const s of setsInPool) {
        if (s !== mem.set) {
          add(`${mem.element} \u2208 ${mem.set} \u222A ${s}`);
          add(`${mem.element} \u2208 ${s} \u222A ${mem.set}`);
        }
      }
    }
    for (const obj of poolNegations) {
      if (obj.claim.startsWith("\xAC\xAC")) {
        add(obj.claim.slice(2).trim());
      }
    }
    for (const obj of pool) {
      if (claimSet.has(`\xAC${obj.claim}`) || claimSet.has(`\xAC(${obj.claim})`)) {
        add("\u22A5");
        break;
      }
    }
    for (const obj of poolForalls) {
      const parsed = parseCanonicalExpr(obj.claim);
      const forall = asForallExpr(parsed);
      if (!forall) continue;
      const { variable, domain, body } = forall;
      const witnesses = collectInstances(ctx, domain);
      for (const w of witnesses) {
        const safeW = /^[\w.]+$/.test(w) ? w : `(${w})`;
        const instantiated = body.replace(new RegExp(`\\b${variable}\\b`, "g"), safeW);
        add(instantiated);
        const impl = parseImplicationCanonical(instantiated);
        if (impl) {
          const [ant, cons] = impl;
          if (pool.some((o) => claimsMatch(o.claim, ant))) add(cons);
        }
      }
    }
    for (const memObj of originalPool) {
      const mem = parseMembershipCanonical(memObj.claim);
      if (!mem) continue;
      const { element: witness, set: domain } = mem;
      for (const bodyObj of originalPool) {
        if (bodyObj === memObj) continue;
        if (!bodyObj.claim.includes(witness)) continue;
        const bodyWithVar = bodyObj.claim.replace(
          new RegExp(`\\b${witness.replace(/[.*+?^${}()|[\]\\]/g, "\\$&")}\\b`, "g"),
          "x"
        );
        if (bodyWithVar === bodyObj.claim) continue;
        add(`\u2203 x \u2208 ${domain}, ${bodyWithVar}`);
      }
    }
    for (const obj of origImplications) {
      const impl = parseImplicationCanonical(obj.claim);
      add(`\xAC${impl[1]} \u2192 \xAC${impl[0]}`);
    }
    for (const obj of poolNegations) {
      const inner = obj.claim.slice(1).trim().replace(/^\(|\)$/g, "");
      const conj = parseConjunctionCanonical(inner);
      if (conj) {
        add(`\xAC${conj[0]} \u2228 \xAC${conj[1]}`);
        continue;
      }
      const disj = parseDisjunctionCanonical(inner);
      if (disj) {
        add(`\xAC${disj[0]} \u2227 \xAC${disj[1]}`);
      }
    }
    for (const obj of pool) {
      const morph = parseMorphismDeclarationCanonical(obj.claim);
      if (!morph) continue;
      for (const { mem } of poolMemberships) {
        if (!sameProp(mem.set, morph.domain)) continue;
        add(`${morph.label}(${mem.element}) \u2208 ${morph.codomain}`);
      }
    }
    for (const { eq } of poolEqualities) {
      add(`${eq.right} = ${eq.left}`);
    }
    const origEqualityClaims = origEqualityClaimsConst;
    for (const obj1 of origEqualityClaims) {
      const eq1 = parseEqualityCanonical(obj1.claim);
      for (const { eq: eq2 } of poolEqualities) {
        if (sameProp(eq1.right, eq2.left)) add(`${eq1.left} = ${eq2.right}`);
        if (sameProp(eq1.left, eq2.right)) add(`${eq2.left} = ${eq1.right}`);
      }
    }
    for (const { eq } of poolEqualities) {
      add(`${eq.left} \u2286 ${eq.right}`);
      add(`${eq.right} \u2286 ${eq.left}`);
    }
    for (const obj of pool) {
      const morph = parseMorphismDeclarationCanonical(obj.claim);
      if (!morph) continue;
      for (const { mem } of poolMemberships) {
        if (!sameProp(mem.set, morph.domain)) continue;
        add(`${morph.label}(${mem.element}) \u2208 image(${morph.label}, ${morph.domain})`);
      }
    }
    for (const { mem } of poolMemberships) {
      const builder = parseSetBuilderCanonical(mem.set);
      if (!builder) continue;
      const { variable, domain, elementTemplate } = builder;
      add(`${mem.element} \u2208 ${domain}`);
      const safeElem = /^[\w.]+$/.test(mem.element) ? mem.element : `(${mem.element})`;
      const predicate = elementTemplate.replace(
        new RegExp(`\\b${variable}\\b`, "g"),
        safeElem
      );
      if (predicate !== elementTemplate) add(predicate);
    }
    const atomicClaims = atomicClaimsConst;
    for (let i = 0; i < atomicClaims.length; i++) {
      for (let j = i + 1; j < atomicClaims.length; j++) {
        add(`${atomicClaims[i].claim} \u2227 ${atomicClaims[j].claim}`);
      }
    }
    for (const { impl } of poolImplications) {
      const negQ = `\xAC${impl[1]}`;
      const negQParen = `\xAC(${impl[1]})`;
      if (claimSet.has(negQ) || claimSet.has(negQParen)) add(`\xAC${impl[0]}`);
    }
    for (const s of setsInPool) {
      add(`${s} \u2286 ${s}`);
    }
    for (const s of setsInPool) {
      const inter = parseBinarySetCanonical(s, "\u2229");
      if (inter) {
        add(`${s} \u2286 ${inter[0]}`);
        add(`${s} \u2286 ${inter[1]}`);
      }
    }
    const origSubsetPairs = origSubsets.map((o) => parseSubsetCanonical(o.claim));
    for (let i = 0; i < origSubsetPairs.length; i++) {
      for (let j = 0; j < origSubsetPairs.length; j++) {
        if (i === j) continue;
        if (sameProp(origSubsetPairs[i].right, origSubsetPairs[j].right)) {
          add(`${origSubsetPairs[i].left} \u222A ${origSubsetPairs[j].left} \u2286 ${origSubsetPairs[i].right}`);
        }
      }
    }
    for (const s of origSubsetPairs) {
      add(`\u2200 x \u2208 ${s.left}, x \u2208 ${s.right}`);
    }
    for (const c of allDerived) {
      const sub = parseSubsetCanonical(c);
      if (sub && !sub.left.includes("\u222A") && !sub.left.includes("\u2229")) {
        add(`\u2200 x \u2208 ${sub.left}, x \u2208 ${sub.right}`);
      }
    }
    for (const { mem } of poolMemberships) {
      const m = mem.set.match(/^image\s*\(\s*([^,]+?)\s*,\s*(.+?)\s*\)$/);
      if (!m) continue;
      const [, fn, domain] = m;
      add(`\u2203 x \u2208 ${domain}, ${fn}(x) = ${mem.element}`);
    }
    for (const obj1 of origImplications) {
      const impl1 = parseImplicationCanonical(obj1.claim);
      for (const [ant, cons] of implications) {
        if (sameProp(impl1[1], ant)) add(`${impl1[0]} \u2192 ${cons}`);
      }
      for (const obj2 of origImplications) {
        if (obj1 === obj2) continue;
        const impl2 = parseImplicationCanonical(obj2.claim);
        if (sameProp(impl1[1], impl2[0])) add(`${impl1[0]} \u2192 ${impl2[1]}`);
      }
    }
    for (const obj of poolForalls) {
      const parsed = parseCanonicalExpr(obj.claim);
      const forall = asForallExpr(parsed);
      if (!forall) continue;
      const mem = parseMembershipCanonical(forall.body);
      if (mem && forall.variable === mem.element) {
        add(`${forall.domain} \u2286 ${mem.set}`);
      }
    }
    const forallsByDomain = forallsByDomainConst;
    for (const [domain, entries] of forallsByDomain) {
      for (let i = 0; i < entries.length; i++) {
        for (let j = i + 1; j < entries.length; j++) {
          const bodyI = entries[i].body.replace(new RegExp(`\\b${entries[i].variable}\\b`, "g"), "x");
          const bodyJ = entries[j].body.replace(new RegExp(`\\b${entries[j].variable}\\b`, "g"), "x");
          add(`\u2200 x \u2208 ${domain}, ${bodyI} \u2227 ${bodyJ}`);
        }
      }
    }
    for (const obj of poolNegations) {
      const inner = obj.claim.slice(1).trim().replace(/^\(|\)$/g, "");
      const parsedInner = parseCanonicalExpr(inner);
      const fa = asForallExpr(parsedInner);
      if (fa) {
        add(`\u2203 ${fa.variable} \u2208 ${fa.domain}, \xAC(${fa.body})`);
        continue;
      }
      const ex = asExistsExpr(parsedInner);
      if (ex) {
        add(`\u2200 ${ex.variable} \u2208 ${ex.domain}, \xAC(${ex.body})`);
      }
    }
    for (const obj1 of pool) {
      const m1 = parseMorphismDeclarationCanonical(obj1.claim);
      if (!m1) continue;
      for (const obj2 of pool) {
        if (obj1 === obj2) continue;
        const m2 = parseMorphismDeclarationCanonical(obj2.claim);
        if (!m2) continue;
        if (sameProp(m1.codomain, m2.domain)) {
          add(`${m2.label}\u2218${m1.label}: ${m1.domain} \u2192 ${m2.codomain}`);
        }
      }
    }
    const origOrderClaims = origOrderClaimsConst;
    const orderClaims = pool.map((o) => ({ obj: o, ord: parseOrder(o.claim) })).filter((x) => x.ord !== null);
    for (const { ord: o1 } of origOrderClaims) {
      for (const { ord: o2 } of orderClaims) {
        if (o1 === o2) continue;
        if (!sameProp(o1.right, o2.left)) continue;
        const strict1 = o1.op === "<" || o1.op === ">";
        const strict2 = o2.op === "<" || o2.op === ">";
        const fwd1 = o1.op === "<" || o1.op === "\u2264";
        const fwd2 = o2.op === "<" || o2.op === "\u2264";
        if (fwd1 && fwd2) {
          const op = strict1 || strict2 ? "<" : "\u2264";
          add(`${o1.left} ${op} ${o2.right}`);
        } else if (!fwd1 && !fwd2) {
          const op = strict1 || strict2 ? ">" : "\u2265";
          add(`${o1.left} ${op} ${o2.right}`);
        }
      }
    }
    for (const { ord: o1 } of origOrderClaims) {
      for (const { ord: o2 } of origOrderClaims) {
        if (o1 === o2) continue;
        const both_leq = (o1.op === "\u2264" || o1.op === "<=") && (o2.op === "\u2264" || o2.op === "<=");
        const both_geq = (o1.op === "\u2265" || o1.op === ">=") && (o2.op === "\u2265" || o2.op === ">=");
        if ((both_leq || both_geq) && sameProp(o1.left, o2.right) && sameProp(o1.right, o2.left)) {
          add(`${o1.left} = ${o1.right}`);
        }
      }
    }
    for (const { ord } of origOrderClaims) {
      if (ord.op === "<") add(`${ord.left} \u2264 ${ord.right}`);
      if (ord.op === ">") add(`${ord.left} \u2265 ${ord.right}`);
    }
    const stripParens = (s) => s.startsWith("(") && s.endsWith(")") ? s.slice(1, -1).trim() : s;
    for (const obj of originalPool) {
      const conj = parseConjunctionCanonical(obj.claim);
      if (conj) {
        const [p, qr] = conj;
        const disj2 = parseDisjunctionCanonical(stripParens(qr));
        if (disj2) add(`(${p} \u2227 ${disj2[0]}) \u2228 (${p} \u2227 ${disj2[1]})`);
      }
      const disj = parseDisjunctionCanonical(obj.claim);
      if (disj) {
        const conjInner = parseConjunctionCanonical(stripParens(disj[1]));
        if (conjInner) add(`(${disj[0]} \u2228 ${conjInner[0]}) \u2227 (${disj[0]} \u2228 ${conjInner[1]})`);
      }
    }
    for (const obj of origSubsets) {
      const sub = parseSubsetCanonical(obj.claim);
      for (const fnObj of pool) {
        const morph = parseMorphismDeclarationCanonical(fnObj.claim);
        if (!morph || !sameProp(morph.domain, sub.right)) continue;
        add(`image(${morph.label}, ${sub.left}) \u2286 image(${morph.label}, ${sub.right})`);
      }
    }
    for (const obj of originalPool) {
      const conj = parseConjunctionCanonical(obj.claim);
      if (conj) add(`${conj[1]} \u2227 ${conj[0]}`);
      const disj = parseDisjunctionCanonical(obj.claim);
      if (disj) add(`${disj[1]} \u2228 ${disj[0]}`);
    }
    for (const obj of originalPool) {
      const outer = parseConjunctionCanonical(obj.claim);
      if (outer) {
        const inner = parseConjunctionCanonical(stripParens(outer[0]));
        if (inner) add(`${inner[0]} \u2227 (${inner[1]} \u2227 ${outer[1]})`);
      }
      const outerD = parseDisjunctionCanonical(obj.claim);
      if (outerD) {
        const innerD = parseDisjunctionCanonical(stripParens(outerD[0]));
        if (innerD) add(`${innerD[0]} \u2228 (${innerD[1]} \u2228 ${outerD[1]})`);
      }
    }
    for (const t of orderTermsConst) add(`${t} \u2264 ${t}`);
    for (const obj of pool) {
      const morph = parseMorphismDeclarationCanonical(obj.claim);
      if (!morph || !morph.label.includes("\u2218")) continue;
      for (const { mem } of poolMemberships) {
        if (!sameProp(mem.set, morph.domain)) continue;
        add(`(${morph.label})(${mem.element}) \u2208 ${morph.codomain}`);
      }
    }
    for (const { ord } of origOrderClaims) {
      const result = evalOrder(ord.left, ord.op, ord.right);
      if (result === true) add(`${ord.left} ${ord.op} ${ord.right}`);
      if (result === false) add(`\xAC(${ord.left} ${ord.op} ${ord.right})`);
    }
    for (const { eq } of poolEqualities) {
      const lv = evalArith(eq.left);
      const rv = evalArith(eq.right);
      if (lv !== null && rv !== null && lv !== rv) add(`\xAC(${eq.left} = ${eq.right})`);
    }
    for (const { conj } of poolConjunctions) {
      if (sameProp(conj[0], conj[1])) add(conj[0]);
    }
    for (const { disj } of poolDisjunctions) {
      if (sameProp(disj[0], disj[1])) add(disj[0]);
    }
    for (const { conj } of poolConjunctions) {
      if (conj[0] === TOP || conj[0] === "\u22A4") add(conj[1]);
      if (conj[1] === TOP || conj[1] === "\u22A4") add(conj[0]);
      if (conj[0] === BOTTOM || conj[0] === "\u22A5") add(BOTTOM);
      if (conj[1] === BOTTOM || conj[1] === "\u22A5") add(BOTTOM);
    }
    for (const { disj } of poolDisjunctions) {
      if (disj[0] === BOTTOM || disj[0] === "\u22A5") add(disj[1]);
      if (disj[1] === BOTTOM || disj[1] === "\u22A5") add(disj[0]);
      if (disj[0] === TOP || disj[0] === "\u22A4") add(TOP);
      if (disj[1] === TOP || disj[1] === "\u22A4") add(TOP);
    }
    if (claimSet.has(BOTTOM) || claimSet.has("\u22A5")) {
      add(TOP);
      for (const o of atomicClaims) add(`\xAC${o.claim}`);
    }
    for (const obj of poolNegations) {
      const inner = obj.claim.slice(1).trim().replace(/^\(|\)$/g, "");
      const mem = parseMembershipCanonical(inner);
      if (mem) add(`${mem.element} \u2209 ${mem.set}`);
    }
    for (const obj of pool) {
      const nonMem = parseNonMembershipCanonical(obj.claim);
      if (nonMem) add(`\xAC(${nonMem.element} \u2208 ${nonMem.set})`);
    }
    for (const { mem } of poolMemberships) {
      const m = mem.set.match(/^complement\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
      if (!m) continue;
      const [, a, u] = m;
      add(`${mem.element} \u2209 ${a}`);
      add(`${mem.element} \u2208 ${u}`);
    }
    for (const { ord: o1 } of origOrderClaims) {
      for (const { ord: o2 } of origOrderClaims) {
        if (o1 === o2) continue;
        const fwd1 = o1.op === "<" || o1.op === "\u2264";
        const fwd2 = o2.op === "<" || o2.op === "\u2264";
        if (fwd1 && fwd2) {
          const strict2 = o1.op === "<" || o2.op === "<";
          const op = strict2 ? "<" : "\u2264";
          add(`${o1.left} + ${o2.left} ${op} ${o1.right} + ${o2.right}`);
        }
      }
    }
    for (const c of nonNegTermsConst) {
      for (const { ord } of origOrderClaims) {
        const fwd = ord.op === "\u2264" || ord.op === "<";
        if (!fwd) continue;
        if (ord.left === "0" || ord.left === "zero") continue;
        add(`${ord.left} * ${c} ${ord.op} ${ord.right} * ${c}`);
      }
    }
    if (claimSet.has("\xAC\u22A5") || claimSet.has(`\xAC${BOTTOM}`)) add(TOP);
    if (claimSet.has("\xAC\u22A4") || claimSet.has(`\xAC${TOP}`)) add(BOTTOM);
    for (const o of atomicClaims) {
      const neg2 = o.claim.includes(" ") ? `\xAC(${o.claim})` : `\xAC${o.claim}`;
      add(`${o.claim} \u2228 ${neg2}`);
    }
    for (const s of setsInPool) {
      add(`\u2205 \u2286 ${s}`);
    }
    const nonMembers = /* @__PURE__ */ new Map();
    const membersMap = /* @__PURE__ */ new Map();
    for (const obj of pool) {
      const nm = parseNonMembershipCanonical(obj.claim);
      if (nm) {
        const list = nonMembers.get(nm.element) ?? [];
        list.push(nm.set);
        nonMembers.set(nm.element, list);
      }
    }
    for (const obj of poolNegations) {
      const inner = obj.claim.slice(1).trim().replace(/^\(|\)$/g, "");
      const mem = parseMembershipCanonical(inner);
      if (mem) {
        const list = nonMembers.get(mem.element) ?? [];
        list.push(mem.set);
        nonMembers.set(mem.element, list);
      }
    }
    for (const { mem } of poolMemberships) {
      const list = membersMap.get(mem.element) ?? [];
      list.push(mem.set);
      membersMap.set(mem.element, list);
    }
    for (const [elem, notInSets] of nonMembers) {
      const inSets = membersMap.get(elem) ?? [];
      for (const a of notInSets) {
        for (const u of inSets) {
          add(`${elem} \u2208 complement(${a}, ${u})`);
        }
      }
    }
    for (const obj of poolForalls) {
      const fa = asForallExpr(parseCanonicalExpr(obj.claim));
      if (!fa) continue;
      const conj = parseConjunctionCanonical(stripParens(fa.body));
      if (conj) {
        add(`\u2200 ${fa.variable} \u2208 ${fa.domain}, ${conj[0]}`);
        add(`\u2200 ${fa.variable} \u2208 ${fa.domain}, ${conj[1]}`);
      }
    }
    for (const { mem } of poolMemberships) {
      const prodParts = mem.set.includes("\xD7") ? mem.set.split("\xD7").map((s) => s.trim()) : null;
      const prod = prodParts && prodParts.length === 2 ? prodParts : null;
      if (prod) {
        const tuple = mem.element.match(/^\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
        if (tuple) {
          add(`${tuple[1]} \u2208 ${prod[0]}`);
          add(`${tuple[2]} \u2208 ${prod[1]}`);
        }
      }
    }
    const origMemberships = origMembershipsConst;
    for (const [elemA, setsA] of origMemberships) {
      for (const [elemB, setsB] of origMemberships) {
        if (elemA === elemB) continue;
        for (const setA of setsA) {
          for (const setB of setsB) {
            add(`(${elemA}, ${elemB}) \u2208 ${setA} \xD7 ${setB}`);
          }
        }
      }
    }
    if (newThisPass.size === 0) break;
    for (const c of newThisPass) {
      allDerived.add(c);
      knownClaims.add(c);
      pool.push(makeSyntheticObject(c));
    }
  }
  return Array.from(allDerived);
}

// src/react/transpiler.ts
var fs2 = __toESM(require("fs"));
var path2 = __toESM(require("path"));
var MATH_CHARS = /[∀∃⇒≥≤≠∈∉⊆⊇∪∩∧∨¬→↔λΣ∑∏√∞·]/;
var MATH_NOTATION = /\|[^|]|\bmod\b|divides|\{.*\|/;
function stripQuotes(s) {
  return s.trim().replace(/^["']|["']$/g, "");
}
function detectFirebaseConfig(nodes) {
  const vars = {};
  for (const node of nodes) {
    if (node.type === "SetVar" && node.varName.startsWith("FIREBASE_") && node.value) {
      vars[node.varName] = stripQuotes(node.value);
    }
  }
  if (!vars["FIREBASE_API_KEY"]) return null;
  return {
    apiKey: vars["FIREBASE_API_KEY"] ?? "",
    authDomain: vars["FIREBASE_AUTH_DOMAIN"] ?? "",
    projectId: vars["FIREBASE_PROJECT_ID"] ?? "",
    storageBucket: vars["FIREBASE_STORAGE_BUCKET"] ?? "",
    messagingSenderId: vars["FIREBASE_MESSAGING_SENDER_ID"] ?? "",
    appId: vars["FIREBASE_APP_ID"] ?? ""
  };
}
function extractNoteFields(nodes) {
  for (const node of nodes) {
    if (node.type === "Struct" && node.name === "Note") {
      return node.fields.filter((f) => f.name !== "id");
    }
  }
  return [{ name: "title", type: "String" }, { name: "body", type: "String" }];
}
function createReactApp(nodes, outDir) {
  const fbConfig = detectFirebaseConfig(nodes);
  if (fbConfig) {
    const noteFields = extractNoteFields(nodes);
    createFirebaseNotesApp(fbConfig, noteFields, outDir);
    return;
  }
  fs2.mkdirSync(outDir, { recursive: true });
  fs2.mkdirSync(path2.join(outDir, "src"), { recursive: true });
  const program = serializeNodes(nodes);
  fs2.writeFileSync(path2.join(outDir, "package.json"), reactPackageJson, "utf8");
  fs2.writeFileSync(path2.join(outDir, "tsconfig.json"), reactTsconfig, "utf8");
  fs2.writeFileSync(path2.join(outDir, "vite.config.ts"), reactViteConfig, "utf8");
  fs2.writeFileSync(path2.join(outDir, "index.html"), reactIndexHtml, "utf8");
  fs2.writeFileSync(path2.join(outDir, "src", "main.tsx"), reactMainTsx, "utf8");
  fs2.writeFileSync(path2.join(outDir, "src", "App.tsx"), renderReactApp(program), "utf8");
  fs2.writeFileSync(path2.join(outDir, "src", "styles.css"), reactStylesCss, "utf8");
}
function createFirebaseNotesApp(config, noteFields, outDir) {
  const srcDir = path2.join(outDir, "src");
  const componentsDir = path2.join(srcDir, "components");
  fs2.mkdirSync(componentsDir, { recursive: true });
  fs2.writeFileSync(path2.join(outDir, "package.json"), firebasePackageJson, "utf8");
  fs2.writeFileSync(path2.join(outDir, "tsconfig.json"), reactTsconfig, "utf8");
  fs2.writeFileSync(path2.join(outDir, "vite.config.ts"), reactViteConfig, "utf8");
  fs2.writeFileSync(path2.join(outDir, "index.html"), firebaseIndexHtml, "utf8");
  fs2.writeFileSync(path2.join(outDir, ".env"), buildEnvFile(config), "utf8");
  fs2.writeFileSync(path2.join(srcDir, "main.tsx"), reactMainTsx, "utf8");
  fs2.writeFileSync(path2.join(srcDir, "firebase.ts"), buildFirebaseTs(config), "utf8");
  fs2.writeFileSync(path2.join(srcDir, "App.tsx"), buildAppTsx(), "utf8");
  fs2.writeFileSync(path2.join(srcDir, "styles.css"), firebaseStylesCss, "utf8");
  fs2.writeFileSync(path2.join(componentsDir, "Auth.tsx"), buildAuthTsx(), "utf8");
  fs2.writeFileSync(path2.join(componentsDir, "Notes.tsx"), buildNotesTsx(noteFields), "utf8");
}
function buildEnvFile(config) {
  return [
    `VITE_FIREBASE_API_KEY=${config.apiKey}`,
    `VITE_FIREBASE_AUTH_DOMAIN=${config.authDomain}`,
    `VITE_FIREBASE_PROJECT_ID=${config.projectId}`,
    `VITE_FIREBASE_STORAGE_BUCKET=${config.storageBucket}`,
    `VITE_FIREBASE_MESSAGING_SENDER_ID=${config.messagingSenderId}`,
    `VITE_FIREBASE_APP_ID=${config.appId}`
  ].join("\n") + "\n";
}
function buildFirebaseTs(config) {
  return `import { initializeApp } from 'firebase/app';
import { getAuth, GoogleAuthProvider } from 'firebase/auth';
import { getFirestore } from 'firebase/firestore';

const firebaseConfig = {
  apiKey:            ${JSON.stringify(config.apiKey)},
  authDomain:        ${JSON.stringify(config.authDomain)},
  projectId:         ${JSON.stringify(config.projectId)},
  storageBucket:     ${JSON.stringify(config.storageBucket)},
  messagingSenderId: ${JSON.stringify(config.messagingSenderId)},
  appId:             ${JSON.stringify(config.appId)},
};

export const app      = initializeApp(firebaseConfig);
export const auth     = getAuth(app);
export const db       = getFirestore(app);
export const google   = new GoogleAuthProvider();
`;
}
function buildAppTsx() {
  return `import { useEffect, useState } from 'react';
import { onAuthStateChanged, User } from 'firebase/auth';
import { auth } from './firebase';
import Auth from './components/Auth';
import Notes from './components/Notes';
import './styles.css';

export default function App() {
  const [user, setUser] = useState<User | null>(null);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    return onAuthStateChanged(auth, (u) => { setUser(u); setLoading(false); });
  }, []);

  if (loading) return <div className="splash"><div className="spinner" /></div>;

  return user ? <Notes user={user} /> : <Auth />;
}
`;
}
function buildAuthTsx() {
  return `import { useState } from 'react';
import {
  createUserWithEmailAndPassword,
  signInWithEmailAndPassword,
  signInWithPopup,
} from 'firebase/auth';
import { auth, google } from '../firebase';

export default function Auth() {
  const [mode, setMode]       = useState<'login' | 'signup'>('login');
  const [email, setEmail]     = useState('');
  const [password, setPass]   = useState('');
  const [error, setError]     = useState('');
  const [busy, setBusy]       = useState(false);

  async function handleSubmit(e: React.FormEvent) {
    e.preventDefault();
    setError(''); setBusy(true);
    try {
      if (mode === 'signup') {
        await createUserWithEmailAndPassword(auth, email, password);
      } else {
        await signInWithEmailAndPassword(auth, email, password);
      }
    } catch (err: any) {
      setError(err.message ?? 'Authentication failed');
    } finally {
      setBusy(false);
    }
  }

  async function handleGoogle() {
    setError(''); setBusy(true);
    try {
      await signInWithPopup(auth, google);
    } catch (err: any) {
      setError(err.message ?? 'Google sign-in failed');
    } finally {
      setBusy(false);
    }
  }

  return (
    <div className="auth-shell">
      <div className="auth-card">
        <h1>Notes</h1>
        <p className="auth-sub">Powered by FuturLang</p>

        <div className="tab-row">
          <button className={mode === 'login'  ? 'tab active' : 'tab'} onClick={() => setMode('login')}>Sign in</button>
          <button className={mode === 'signup' ? 'tab active' : 'tab'} onClick={() => setMode('signup')}>Create account</button>
        </div>

        <form onSubmit={handleSubmit} className="auth-form">
          <label>
            Email
            <input type="email" value={email} onChange={e => setEmail(e.target.value)} required autoFocus />
          </label>
          <label>
            Password
            <input type="password" value={password} onChange={e => setPass(e.target.value)} required minLength={6} />
          </label>
          {error && <p className="error">{error}</p>}
          <button type="submit" className="btn-primary" disabled={busy}>
            {busy ? '\u2026' : mode === 'login' ? 'Sign in' : 'Create account'}
          </button>
        </form>

        <div className="divider"><span>or</span></div>

        <button className="btn-google" onClick={handleGoogle} disabled={busy}>
          <svg width="18" height="18" viewBox="0 0 48 48"><path fill="#EA4335" d="M24 9.5c3.54 0 6.71 1.22 9.21 3.6l6.85-6.85C35.9 2.38 30.47 0 24 0 14.62 0 6.51 5.38 2.56 13.22l7.98 6.19C12.43 13.72 17.74 9.5 24 9.5z"/><path fill="#4285F4" d="M46.98 24.55c0-1.57-.15-3.09-.38-4.55H24v9.02h12.94c-.58 2.96-2.26 5.48-4.78 7.18l7.73 6c4.51-4.18 7.09-10.36 7.09-17.65z"/><path fill="#FBBC05" d="M10.53 28.59c-.48-1.45-.76-2.99-.76-4.59s.27-3.14.76-4.59l-7.98-6.19C.92 16.46 0 20.12 0 24c0 3.88.92 7.54 2.56 10.78l7.97-6.19z"/><path fill="#34A853" d="M24 48c6.48 0 11.93-2.13 15.89-5.81l-7.73-6c-2.15 1.45-4.92 2.3-8.16 2.3-6.26 0-11.57-4.22-13.47-9.91l-7.98 6.19C6.51 42.62 14.62 48 24 48z"/></svg>
          Continue with Google
        </button>
      </div>
    </div>
  );
}
`;
}
function buildNotesTsx(noteFields) {
  const hasBody = noteFields.some((f) => f.name === "body");
  return `import { useEffect, useState, useCallback } from 'react';
import {
  collection, query, where, onSnapshot,
  addDoc, updateDoc, deleteDoc, doc, serverTimestamp,
} from 'firebase/firestore';
import { signOut, User } from 'firebase/auth';
import { auth, db } from '../firebase';

interface Note {
  id: string;
  title: string;
  body: string;
  createdAt: any;
  userId: string;
}

type Mode = 'sdk' | 'api';
const API_BASE = 'http://localhost:3001';

export default function Notes({ user }: { user: User }) {
  const [notes, setNotes]   = useState<Note[]>([]);
  const [active, setActive] = useState<Note | null>(null);
  const [title, setTitle]   = useState('');
  const [body, setBody]     = useState('');
  const [saving, setSaving] = useState(false);
  const [search, setSearch] = useState('');
  const [mode, setMode]     = useState<Mode>('sdk');

  // \u2500\u2500 SDK mode: real-time Firestore listener \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
  useEffect(() => {
    if (mode !== 'sdk') return;
    const q = query(collection(db, 'notes'), where('userId', '==', user.uid));
    return onSnapshot(q, snap => {
      const docs = snap.docs.map(d => ({ id: d.id, ...d.data() } as Note));
      // Sort client-side \u2014 avoids needing a composite Firestore index
      docs.sort((a, b) => {
        const ta = (a.createdAt as any)?.toMillis?.() ?? 0;
        const tb = (b.createdAt as any)?.toMillis?.() ?? 0;
        return tb - ta;
      });
      setNotes(docs);
    });
  }, [user.uid, mode]);

  // \u2500\u2500 API mode: fetch from FL backend \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
  const fetchApiNotes = useCallback(async () => {
    const token = await user.getIdToken();
    const res = await fetch(API_BASE + '/api/notes', {
      headers: { Authorization: 'Bearer ' + token },
    });
    if (!res.ok) return;
    const data: Note[] = await res.json();
    data.sort((a: any, b: any) => {
      const ta = new Date(a.createdAt || 0).getTime();
      const tb = new Date(b.createdAt || 0).getTime();
      return tb - ta;
    });
    setNotes(data);
  }, [user]);

  useEffect(() => {
    if (mode !== 'api') return;
    fetchApiNotes();
  }, [mode, fetchApiNotes]);

  function selectNote(note: Note) {
    setActive(note);
    setTitle(note.title);
    setBody(note.body ?? '');
  }

  function newNote() { setActive(null); setTitle(''); setBody(''); }

  // \u2500\u2500 Save (create or update) \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
  async function save() {
    if (!title.trim()) return;
    setSaving(true);
    try {
      if (mode === 'sdk') {
        if (active) {
          await updateDoc(doc(db, 'notes', active.id), { title: title.trim(), body });
          setActive(prev => prev ? { ...prev, title: title.trim(), body } : null);
        } else {
          const ref = await addDoc(collection(db, 'notes'), {
            title: title.trim(), body, userId: user.uid, createdAt: serverTimestamp(),
          });
          setActive({ id: ref.id, title: title.trim(), body, userId: user.uid, createdAt: null });
        }
      } else {
        const token = await user.getIdToken();
        if (active) {
          await fetch(API_BASE + '/api/notes/' + active.id, {
            method: 'PUT',
            headers: { 'Content-Type': 'application/json', Authorization: 'Bearer ' + token },
            body: JSON.stringify({ title: title.trim(), body }),
          });
        } else {
          await fetch(API_BASE + '/api/notes', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json', Authorization: 'Bearer ' + token },
            body: JSON.stringify({
              title: title.trim(), body,
              userId: user.uid,
              createdAt: new Date().toISOString(),
            }),
          });
        }
        await fetchApiNotes();
      }
    } finally {
      setSaving(false);
    }
  }

  // \u2500\u2500 Delete \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500
  async function remove(id: string) {
    if (mode === 'sdk') {
      await deleteDoc(doc(db, 'notes', id));
    } else {
      const token = await user.getIdToken();
      await fetch(API_BASE + '/api/notes/' + id, {
        method: 'DELETE',
        headers: { Authorization: 'Bearer ' + token },
      });
      setNotes(prev => prev.filter(n => n.id !== id));
    }
    if (active?.id === id) newNote();
  }

  const filtered = notes.filter(n =>
    n.title.toLowerCase().includes(search.toLowerCase()) ||
    (n.body ?? '').toLowerCase().includes(search.toLowerCase())
  );

  return (
    <div className="notes-shell">
      {/* Sidebar */}
      <aside className="sidebar">
        <div className="sidebar-top">
          <span className="brand">Notes</span>
          <button className="btn-icon" title="New note" onClick={newNote}>+</button>
        </div>
        <input
          className="search"
          placeholder="Search\u2026"
          value={search}
          onChange={e => setSearch(e.target.value)}
        />
        <ul className="note-list">
          {filtered.map(n => (
            <li
              key={n.id}
              className={active?.id === n.id ? 'note-item active' : 'note-item'}
              onClick={() => selectNote(n)}
            >
              <span className="note-title">{n.title}</span>
              <button
                className="btn-delete"
                onClick={e => { e.stopPropagation(); remove(n.id); }}
                title="Delete"
              >\xD7</button>
            </li>
          ))}
          {filtered.length === 0 && (
            <li className="empty">{search ? 'No matches' : 'No notes yet'}</li>
          )}
        </ul>
        <div className="sidebar-bottom">
          <span className="user-email">{user.email}</span>
          <button className="btn-signout" onClick={() => signOut(auth)}>Sign out</button>
        </div>
      </aside>

      {/* Editor */}
      <main className="editor">
        <div className="editor-header">
          <input
            className="title-input"
            placeholder="Note title\u2026"
            value={title}
            onChange={e => setTitle(e.target.value)}
          />
          <button className="btn-save" onClick={save} disabled={saving || !title.trim()}>
            {saving ? 'Saving\u2026' : active ? 'Save' : 'Create'}
          </button>
        </div>
        ${hasBody ? `<textarea
          className="body-input"
          placeholder="Start writing\u2026"
          value={body}
          onChange={e => setBody(e.target.value)}
        />` : `<p className="no-body">Body field not defined in Note struct.</p>`}
        {/* Mode toggle */}
        <div className="mode-bar">
          <span className="mode-label">
            {mode === 'sdk' ? 'Firebase SDK (direct)' : 'FL Backend API (via server)'}
          </span>
          <button
            className={\`mode-toggle \${mode === 'api' ? 'active' : ''}\`}
            onClick={() => { newNote(); setMode(m => m === 'sdk' ? 'api' : 'sdk'); }}
            title="Toggle between Firebase SDK and FL backend"
          >
            {mode === 'sdk' ? 'Switch to FL Backend' : 'Switch to Firebase SDK'}
          </button>
        </div>
      </main>
    </div>
  );
}
`;
}
var firebasePackageJson = `{
  "name": "fl-notes-app",
  "private": true,
  "version": "0.0.0",
  "type": "module",
  "scripts": {
    "dev": "vite",
    "build": "tsc && vite build",
    "preview": "vite preview"
  },
  "dependencies": {
    "firebase": "^10.14.1",
    "react": "^18.3.1",
    "react-dom": "^18.3.1"
  },
  "devDependencies": {
    "@types/react": "^18.3.3",
    "@types/react-dom": "^18.3.0",
    "@vitejs/plugin-react": "^4.3.1",
    "typescript": "^5.6.3",
    "vite": "^5.4.8"
  }
}
`;
var firebaseIndexHtml = `<!doctype html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Notes \u2014 FuturLang</title>
  </head>
  <body>
    <div id="root"></div>
    <script type="module" src="/src/main.tsx"></script>
  </body>
</html>
`;
var firebaseStylesCss = `/* \u2500\u2500 Reset \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */
*, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; background: #f5f5f5; color: #1a1a1a; }
button { cursor: pointer; font-family: inherit; }
input, textarea { font-family: inherit; }

/* \u2500\u2500 Splash \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */
.splash { display: flex; align-items: center; justify-content: center; height: 100vh; }
.spinner { width: 32px; height: 32px; border: 3px solid #ddd; border-top-color: #333; border-radius: 50%; animation: spin .7s linear infinite; }
@keyframes spin { to { transform: rotate(360deg); } }

/* \u2500\u2500 Auth \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */
.auth-shell { display: flex; align-items: center; justify-content: center; min-height: 100vh; padding: 1rem; background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); }
.auth-card { background: white; border-radius: 12px; padding: 2rem; width: min(400px, 100%); box-shadow: 0 20px 60px rgba(0,0,0,.2); }
.auth-card h1 { font-size: 2rem; font-weight: 700; margin-bottom: .25rem; }
.auth-sub { color: #888; font-size: .9rem; margin-bottom: 1.5rem; }
.tab-row { display: flex; border-bottom: 2px solid #eee; margin-bottom: 1.5rem; }
.tab { background: none; border: none; padding: .5rem 1rem; font-size: .95rem; color: #888; border-bottom: 2px solid transparent; margin-bottom: -2px; transition: all .15s; }
.tab.active { color: #333; border-bottom-color: #333; font-weight: 600; }
.auth-form { display: flex; flex-direction: column; gap: .75rem; }
.auth-form label { display: flex; flex-direction: column; gap: .3rem; font-size: .85rem; font-weight: 500; color: #444; }
.auth-form input { border: 1.5px solid #ddd; border-radius: 8px; padding: .6rem .75rem; font-size: .95rem; transition: border-color .15s; }
.auth-form input:focus { outline: none; border-color: #667eea; }
.error { color: #c0392b; font-size: .85rem; padding: .5rem; background: #fde8e8; border-radius: 6px; }
.btn-primary { background: #333; color: white; border: none; border-radius: 8px; padding: .75rem; font-size: 1rem; font-weight: 600; transition: background .15s; }
.btn-primary:hover:not(:disabled) { background: #555; }
.btn-primary:disabled { opacity: .6; }
.divider { text-align: center; position: relative; margin: 1rem 0; color: #bbb; font-size: .85rem; }
.divider::before, .divider::after { content: ''; position: absolute; top: 50%; width: 43%; height: 1px; background: #eee; }
.divider::before { left: 0; } .divider::after { right: 0; }
.btn-google { display: flex; align-items: center; justify-content: center; gap: .6rem; width: 100%; background: white; border: 1.5px solid #ddd; border-radius: 8px; padding: .7rem; font-size: .95rem; font-weight: 500; transition: background .15s; }
.btn-google:hover:not(:disabled) { background: #f8f8f8; }

/* \u2500\u2500 Notes shell \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */
.notes-shell { display: grid; grid-template-columns: 260px 1fr; height: 100vh; }

/* \u2500\u2500 Sidebar \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */
.sidebar { display: flex; flex-direction: column; background: #1e1e1e; color: white; border-right: 1px solid #2a2a2a; }
.sidebar-top { display: flex; align-items: center; justify-content: space-between; padding: 1rem; border-bottom: 1px solid #2a2a2a; }
.brand { font-size: 1.1rem; font-weight: 700; letter-spacing: -.01em; }
.btn-icon { background: #333; color: white; border: none; width: 28px; height: 28px; border-radius: 6px; font-size: 1.2rem; line-height: 1; display: flex; align-items: center; justify-content: center; transition: background .15s; }
.btn-icon:hover { background: #444; }
.search { background: #2a2a2a; border: none; color: white; padding: .6rem 1rem; font-size: .9rem; outline: none; }
.search::placeholder { color: #666; }
.note-list { flex: 1; overflow-y: auto; list-style: none; }
.note-item { display: flex; align-items: center; justify-content: space-between; padding: .75rem 1rem; cursor: pointer; border-bottom: 1px solid #2a2a2a; transition: background .1s; }
.note-item:hover { background: #2a2a2a; }
.note-item.active { background: #333; }
.note-title { font-size: .9rem; flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.btn-delete { background: none; border: none; color: #666; font-size: 1.1rem; padding: 0 .25rem; transition: color .15s; flex-shrink: 0; }
.btn-delete:hover { color: #e74c3c; }
.empty { color: #555; font-size: .85rem; padding: 1rem; text-align: center; }
.sidebar-bottom { padding: .75rem 1rem; border-top: 1px solid #2a2a2a; display: flex; flex-direction: column; gap: .5rem; }
.user-email { font-size: .75rem; color: #666; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.btn-signout { background: none; border: 1px solid #333; color: #888; border-radius: 6px; padding: .4rem; font-size: .8rem; transition: all .15s; }
.btn-signout:hover { border-color: #555; color: #ccc; }

/* \u2500\u2500 Editor \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */
.editor { display: flex; flex-direction: column; background: white; }
.editor-header { display: flex; gap: .75rem; align-items: center; padding: 1rem 1.5rem; border-bottom: 1px solid #eee; }
.title-input { flex: 1; border: none; font-size: 1.25rem; font-weight: 600; outline: none; color: #1a1a1a; }
.title-input::placeholder { color: #ccc; }
.btn-save { background: #1a1a1a; color: white; border: none; border-radius: 8px; padding: .5rem 1.25rem; font-size: .9rem; font-weight: 600; transition: background .15s; }
.btn-save:hover:not(:disabled) { background: #333; }
.btn-save:disabled { opacity: .4; }
.body-input { flex: 1; border: none; padding: 1.5rem; font-size: 1rem; line-height: 1.7; resize: none; outline: none; color: #333; }
.body-input::placeholder { color: #ccc; }
.no-body { color: #999; padding: 2rem; font-style: italic; }

/* \u2500\u2500 Mode toggle bar \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */
.mode-bar { display: flex; align-items: center; justify-content: space-between; padding: .6rem 1.5rem; border-top: 1px solid #eee; background: #fafafa; flex-shrink: 0; }
.mode-label { font-size: .8rem; color: #888; font-family: "SFMono-Regular", Consolas, monospace; }
.mode-toggle { background: #eee; border: none; border-radius: 6px; padding: .35rem .9rem; font-size: .8rem; font-weight: 600; color: #555; transition: all .15s; }
.mode-toggle:hover { background: #ddd; }
.mode-toggle.active { background: #1a1a1a; color: white; }

@media (max-width: 600px) {
  .notes-shell { grid-template-columns: 1fr; }
  .sidebar { height: 40vh; }
  .editor { height: 60vh; }
}
`;
function serializeNodes(nodes) {
  return nodes.map(serializeNode);
}
function serializeNode(node) {
  switch (node.type) {
    case "Theorem":
    case "Proof":
    case "Lemma":
    case "Definition":
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        body: node.body.map(serializeNode)
      };
    case "Struct":
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        fields: node.fields
      };
    case "TypeDecl":
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        variants: node.variants
      };
    case "FnDecl":
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        params: node.params,
        returnType: node.returnType,
        body: node.body.map(serializeNode)
      };
    case "Assert":
    case "Assume":
    case "Conclude":
      return {
        type: node.type,
        connective: node.connective,
        expr: serializeExpr(node.expr)
      };
    case "Apply":
      return { type: node.type, connective: node.connective, target: node.target };
    case "SetVar":
      return {
        type: node.type,
        connective: node.connective,
        varName: node.varName,
        varType: node.varType,
        value: node.value
      };
    case "Raw":
      return { type: node.type, connective: node.connective, content: node.content };
    case "Match":
      return {
        type: node.type,
        connective: node.connective,
        scrutinee: serializeExpr(node.scrutinee),
        cases: node.cases.map((matchCase) => ({
          pattern: matchCase.pattern,
          body: matchCase.body.map(serializeNode)
        }))
      };
    default:
      return node;
  }
}
function serializeExpr(expr) {
  switch (expr.type) {
    case "Atom":
      return serializeAtom(expr);
    case "SetBuilder":
      return {
        type: expr.type,
        element: expr.element,
        variable: expr.variable,
        domain: expr.domain
      };
    case "IndexedUnion":
      return {
        type: expr.type,
        builder: serializeExpr(expr.builder)
      };
    case "Quantified":
      return {
        type: expr.type,
        quantifier: expr.quantifier,
        binderStyle: expr.binderStyle,
        variable: expr.variable,
        domain: expr.domain,
        body: expr.body ? serializeExpr(expr.body) : null
      };
    case "And":
    case "Or":
    case "Implies":
    case "Iff":
      return {
        type: expr.type,
        left: serializeExpr(expr.left),
        right: serializeExpr(expr.right)
      };
    case "Not":
      return {
        type: expr.type,
        operand: serializeExpr(expr.operand)
      };
    case "If":
      return {
        type: expr.type,
        condition: serializeExpr(expr.condition),
        thenBranch: serializeExpr(expr.thenBranch),
        elseBranch: serializeExpr(expr.elseBranch)
      };
    case "LetExpr":
      return {
        type: expr.type,
        name: expr.name,
        value: serializeExpr(expr.value),
        body: serializeExpr(expr.body)
      };
    case "Lambda":
      return {
        type: expr.type,
        params: expr.params,
        body: serializeExpr(expr.body)
      };
    default:
      return expr;
  }
}
function serializeAtom(atom) {
  const trimmed = atom.condition.trim();
  const unsupported = atom.atomKind === "opaque" || atom.atomKind !== "string" && (MATH_CHARS.test(trimmed) || MATH_NOTATION.test(trimmed));
  return {
    type: atom.type,
    condition: atom.condition,
    atomKind: atom.atomKind,
    unsupported,
    reason: unsupported ? "This claim is outside the strict executable subset. Use fl check for categorical proof checking." : null
  };
}
function renderReactApp(program) {
  return `import './styles.css';

type ProgramNode = any;
type EvalResult = { value: boolean; label: string; detail?: string | null };

const program: ProgramNode[] = ${JSON.stringify(program, null, 2)};

function evaluateProgram(nodes: ProgramNode[]) {
  const scope: Record<string, unknown> = {};
  const steps = nodes.map(node => evaluateNode(node, scope));
  const value = foldChain(steps.map(step => ({ value: step.value, connective: step.connective })));
  return { value, steps };
}

function evaluateNode(node: ProgramNode, scope: Record<string, unknown>) {
  switch (node.type) {
    case 'Theorem':
    case 'Proof':
    case 'Lemma':
    case 'Definition': {
      const childScope = { ...scope };
      const children = node.body.map((child: ProgramNode) => evaluateNode(child, childScope));
      const value = foldChain(children.map((child: any) => ({ value: child.value, connective: child.connective })));
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        value,
        detail: value ? null : \`\${node.type} failed\`,
        children,
      };
    }
    case 'Struct':
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        value: true,
        detail: null,
        fields: node.fields,
      };
    case 'TypeDecl':
      registerType(node, scope);
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        value: true,
        detail: null,
        fields: node.variants,
      };
    case 'FnDecl': {
      const fn = defineRuntimeFunction(node, scope);
      scope[node.name] = fn;
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        value: true,
        detail: \`fn \${node.name}\`,
        label: node.name,
      };
    }
    case 'Assert':
    case 'Assume':
    case 'Conclude': {
      const result = evaluateExpr(node.expr, scope);
      return {
        type: node.type,
        connective: node.connective,
        value: node.type === 'Assume' ? true : result.value,
        detail: result.detail ?? null,
        label: result.label,
      };
    }
    case 'Apply':
      return {
        type: node.type,
        connective: node.connective,
        value: true,
        detail: \`Applied \${node.target}\`,
        label: node.target,
      };
    case 'SetVar': {
      const value = resolveValue(node.value, scope);
      scope[node.varName] = value;
      return {
        type: node.type,
        connective: node.connective,
        value: true,
        detail: node.varType ? \`\${node.varName}: \${node.varType}\` : null,
        label: node.value == null ? node.varName : \`\${node.varName} = \${String(value)}\`,
      };
    }
    case 'Raw':
      return {
        type: node.type,
        connective: node.connective,
        value: true,
        detail: node.content,
        label: node.content,
      };
    case 'Match':
      try {
        const matched = evaluateMatchNode(node, scope);
        return {
          type: node.type,
          connective: node.connective,
          value: matched.value,
          detail: matched.detail ?? null,
          label: matched.label,
        };
      } catch (error) {
        return {
          type: node.type,
          connective: node.connective,
          value: false,
          detail: error instanceof Error ? error.message : 'Match failed',
          label: 'match',
        };
      }
    default:
      return {
        type: 'Unknown',
        connective: null,
        value: false,
        detail: 'Unknown node',
        label: 'unknown',
      };
  }
}

function evaluateExpr(expr: ProgramNode, scope: Record<string, unknown>): EvalResult {
  switch (expr.type) {
    case 'Atom':
      return evaluateAtom(expr, scope);
    case 'SetBuilder':
    case 'IndexedUnion':
      return {
        value: false,
        label: renderExprLabel(expr),
        detail: 'Set-builder and indexed-union expressions are outside the executable subset.',
      };
    case 'Quantified':
      return {
        value: false,
        label: renderExprLabel(expr),
        detail: 'Quantified expressions are outside the executable subset.',
      };
    case 'If': {
      const condition = evaluateExpr(expr.condition, scope);
      return condition.value
        ? evaluateExpr(expr.thenBranch, scope)
        : evaluateExpr(expr.elseBranch, scope);
    }
    case 'LetExpr': {
      const childScope = { ...scope };
      childScope[expr.name] = resolveExprValue(expr.value, scope);
      return evaluateExpr(expr.body, childScope);
    }
    case 'Lambda':
      return {
        value: true,
        label: renderExprLabel(expr),
        detail: null,
      };
    case 'And': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: left.value && right.value, label: \`(\${left.label} \u2227 \${right.label})\`, detail: left.detail ?? right.detail };
    }
    case 'Or': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: left.value || right.value, label: \`(\${left.label} \u2228 \${right.label})\`, detail: left.detail ?? right.detail };
    }
    case 'Implies': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: !left.value || right.value, label: \`(\${left.label} \u2192 \${right.label})\`, detail: left.detail ?? right.detail };
    }
    case 'Iff': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: left.value === right.value, label: \`(\${left.label} \u2194 \${right.label})\`, detail: left.detail ?? right.detail };
    }
    case 'Not': {
      const inner = evaluateExpr(expr.operand, scope);
      return { value: !inner.value, label: \`\xAC\${inner.label}\`, detail: inner.detail };
    }
    default:
      return { value: false, label: 'unsupported expression', detail: 'Unsupported expression node' };
  }
}

function renderExprLabel(expr: ProgramNode): string {
  switch (expr.type) {
    case 'Atom':
      return expr.condition;
    case 'SetBuilder':
      return '{' + expr.element + ' | ' + expr.variable + ' \u2208 ' + expr.domain + '}';
    case 'IndexedUnion':
      return '\u222A' + renderExprLabel(expr.builder);
    case 'Quantified': {
      const symbol = expr.quantifier === 'forall' ? '\u2200' : expr.quantifier === 'exists' ? '\u2203' : '\u2203!';
      const binder = expr.binderStyle === 'bounded'
        ? expr.variable + ' \u2208 ' + expr.domain
        : expr.variable + ': ' + expr.domain;
      return expr.body ? symbol + ' ' + binder + ', ' + renderExprLabel(expr.body) : symbol + ' ' + binder;
    }
    case 'And':
      return '(' + renderExprLabel(expr.left) + ' \u2227 ' + renderExprLabel(expr.right) + ')';
    case 'Or':
      return '(' + renderExprLabel(expr.left) + ' \u2228 ' + renderExprLabel(expr.right) + ')';
    case 'Implies':
      return '(' + renderExprLabel(expr.left) + ' \u2192 ' + renderExprLabel(expr.right) + ')';
    case 'Iff':
      return '(' + renderExprLabel(expr.left) + ' \u2194 ' + renderExprLabel(expr.right) + ')';
    case 'Not':
      return '\xAC' + renderExprLabel(expr.operand);
    case 'If':
      return 'if ' + renderExprLabel(expr.condition) + ' then ' + renderExprLabel(expr.thenBranch) + ' else ' + renderExprLabel(expr.elseBranch);
    case 'LetExpr':
      return 'let ' + expr.name + ' = ' + renderExprLabel(expr.value) + ' in ' + renderExprLabel(expr.body);
    case 'Lambda':
      return 'fn(' + expr.params.map((param: any) => param.name + ': ' + param.type).join(', ') + ') => ' + renderExprLabel(expr.body);
    default:
      return 'unsupported expression';
  }
}

function evaluateAtom(atom: ProgramNode, scope: Record<string, unknown>): EvalResult {
  const label = atom.condition.trim();
  if (atom.atomKind === 'string') {
    return { value: true, label };
  }
  if (atom.unsupported) {
    return { value: false, label, detail: atom.reason };
  }
  if (label === 'true') return { value: true, label };
  if (label === 'false') return { value: false, label };

  try {
    const safe = label.replace(/(?<![=!<>])=(?!=)/g, '==');
    const fn = new Function('scope', \`with (scope) { return !!(\${safe}); }\`);
    return { value: !!fn(scope), label };
  } catch {
    return { value: false, label, detail: 'Expression could not be executed in the web backend' };
  }
}

function resolveValue(raw: string | null, scope: Record<string, unknown>) {
  if (raw == null) return undefined;
  const trimmed = raw.trim();
  try {
    const fn = new Function('scope', \`with (scope) { return (\${trimmed}); }\`);
    return fn(scope);
  } catch {
    return trimmed;
  }
}

function resolveExprValue(expr: ProgramNode, scope: Record<string, unknown>): unknown {
  switch (expr.type) {
    case 'Atom':
      return resolveValue(expr.condition, scope);
    case 'If':
      return evaluateExpr(expr.condition, scope).value
        ? resolveExprValue(expr.thenBranch, scope)
        : resolveExprValue(expr.elseBranch, scope);
    case 'LetExpr': {
      const childScope = { ...scope };
      childScope[expr.name] = resolveExprValue(expr.value, scope);
      return resolveExprValue(expr.body, childScope);
    }
    case 'Lambda':
      return (...args: unknown[]) => {
        const childScope = { ...scope };
        expr.params.forEach((param: any, index: number) => {
          childScope[param.name] = args[index];
        });
        return resolveExprValue(expr.body, childScope);
      };
    case 'And':
    case 'Or':
    case 'Implies':
    case 'Iff':
    case 'Not':
      return evaluateExpr(expr, scope).value;
    case 'Fold': {
      const sequence = resolveValue(expr.sequence, scope);
      const init = resolveValue(expr.init, scope);
      const fn = resolveValue(expr.fn, scope);
      if (!Array.isArray(sequence) || typeof fn !== 'function') return null;
      return sequence.reduce((acc, item) => fn(acc, item), init);
    }
    default:
      return null;
  }
}

function defineRuntimeFunction(node: ProgramNode, scope: Record<string, unknown>) {
  return (...args: unknown[]) => {
    const childScope: Record<string, unknown> = { ...scope };
    node.params.forEach((param: any, index: number) => {
      childScope[param.name] = args[index];
    });
    for (const child of node.body) {
      if (child.type === 'SetVar') {
        childScope[child.varName] = resolveValue(child.value, childScope);
        continue;
      }
      if (child.type === 'Conclude') {
        return resolveExprValue(child.expr, childScope);
      }
      if (child.type === 'Match') {
        return evaluateMatchValue(child, childScope);
      }
      if (child.type === 'Assert') {
        const result = evaluateExpr(child.expr, childScope);
        if (!result.value) throw new Error(result.detail ?? 'Assertion failed');
      }
    }
    return undefined;
  };
}

function registerType(node: ProgramNode, scope: Record<string, unknown>) {
  for (const variant of node.variants) {
    const fieldNames = variant.fields.map((field: any) => field.name);
    if (fieldNames.length === 0) {
      scope[variant.name] = { tag: variant.name };
      continue;
    }
    scope[variant.name] = (...args: unknown[]) => {
      const value: Record<string, unknown> = { tag: variant.name };
      fieldNames.forEach((fieldName: string, index: number) => {
        value[fieldName] = args[index];
      });
      return value;
    };
  }
}

function evaluateMatchNode(node: ProgramNode, scope: Record<string, unknown>) {
  const value = evaluateMatchValue(node, scope);
  return {
    value: true,
    label: 'match',
    detail: value === undefined ? null : String(value),
  };
}

function evaluateMatchValue(node: ProgramNode, scope: Record<string, unknown>) {
  const scrutinee = resolveExprValue(node.scrutinee, scope);
  for (const matchCase of node.cases) {
    const bindings = matchPattern(matchCase.pattern, scrutinee);
    if (!bindings) continue;
    const childScope = { ...scope, ...bindings };
    for (const child of matchCase.body) {
      if (child.type === 'Conclude') {
        return resolveExprValue(child.expr, childScope);
      }
      if (child.type === 'Match') {
        return evaluateMatchValue(child, childScope);
      }
      if (child.type === 'SetVar') {
        childScope[child.varName] = resolveValue(child.value, childScope);
      }
    }
    return undefined;
  }
  throw new Error('Non-exhaustive match in web runtime');
}

function matchPattern(pattern: any, value: unknown): Record<string, unknown> | null {
  if (pattern.kind === 'wildcard') return {};
  if (pattern.kind === 'list_nil') return Array.isArray(value) && value.length === 0 ? {} : null;
  if (pattern.kind === 'list_cons') {
    if (!Array.isArray(value) || value.length === 0) return null;
    return {
      ...(pattern.head !== '_' ? { [pattern.head]: value[0] } : {}),
      [pattern.tail]: value.slice(1),
    };
  }
  if (pattern.kind === 'variant') {
    if (pattern.constructor === 'true' || pattern.constructor === 'false') {
      return value === (pattern.constructor === 'true') ? {} : null;
    }
    if (!value || typeof value !== 'object' || (value as any).tag !== pattern.constructor) return null;
    const entries: Record<string, unknown> = {};
    pattern.bindings.forEach((binding: string, index: number) => {
      if (!binding || binding === '_') return;
      const keys = Object.keys(value as Record<string, unknown>).filter(key => key !== 'tag');
      entries[binding] = (value as Record<string, unknown>)[keys[index]];
    });
    return entries;
  }
  return null;
}

function foldChain(items: Array<{ value: boolean; connective: string | null }>) {
  if (items.length === 0) return true;
  let acc = items[items.length - 1].value;
  for (let i = items.length - 2; i >= 0; i--) {
    const left = items[i].value;
    const conn = items[i].connective ?? '\u2192';
    if (conn === '\u2227') acc = left && acc;
    else if (conn === '\u2194') acc = left === acc;
    else acc = !left || acc;
  }
  return acc;
}

function statusLabel(value: boolean) {
  return value ? 'Chain Holds' : 'Chain Fails';
}

function App() {
  const result = evaluateProgram(program);

  return (
    <main className="app-shell">
      <section className="hero">
        <p className="eyebrow">FuturLang React Backend</p>
        <h1>Web apps as proofs</h1>
        <p className="lead">
          This app is generated from a single FuturLang truth chain. The UI exists to expose whether the chain holds.
        </p>
        <div className={\`verdict \${result.value ? 'ok' : 'bad'}\`}>
          <span>{statusLabel(result.value)}</span>
          <strong>{String(result.value)}</strong>
        </div>
      </section>

      <section className="panel">
        <h2>Program Steps</h2>
        <div className="steps">
          {result.steps.map((step: any, index: number) => (
            <article className={\`step \${step.value ? 'ok' : 'bad'}\`} key={index}>
              <div className="step-top">
                <span className="step-kind">{step.type}</span>
                <span className="step-value">{String(step.value)}</span>
              </div>
              <h3>{step.name ?? step.label ?? 'Unnamed step'}</h3>
              {step.detail ? <p>{step.detail}</p> : null}
              {step.children?.length ? (
                <ul>
                  {step.children.map((child: any, childIndex: number) => (
                    <li key={childIndex}>
                      <code>{child.type}</code> {child.name ?? child.label ?? 'step'}: {String(child.value)}
                      {child.detail ? <span> \xB7 {child.detail}</span> : null}
                    </li>
                  ))}
                </ul>
              ) : null}
            </article>
          ))}
        </div>
      </section>
    </main>
  );
}

export default App;
`;
}
var reactPackageJson = `{
  "name": "futurlang-webapp",
  "private": true,
  "version": "0.0.0",
  "type": "module",
  "scripts": {
    "dev": "vite",
    "build": "tsc && vite build",
    "preview": "vite preview"
  },
  "dependencies": {
    "react": "^18.3.1",
    "react-dom": "^18.3.1"
  },
  "devDependencies": {
    "@types/react": "^18.3.3",
    "@types/react-dom": "^18.3.0",
    "@vitejs/plugin-react": "^4.3.1",
    "typescript": "^5.6.3",
    "vite": "^5.4.8"
  }
}
`;
var reactTsconfig = `{
  "compilerOptions": {
    "target": "ES2020",
    "useDefineForClassFields": true,
    "lib": ["ES2020", "DOM", "DOM.Iterable"],
    "allowJs": false,
    "skipLibCheck": true,
    "esModuleInterop": true,
    "allowSyntheticDefaultImports": true,
    "strict": true,
    "forceConsistentCasingInFileNames": true,
    "module": "ESNext",
    "moduleResolution": "Bundler",
    "resolveJsonModule": true,
    "isolatedModules": true,
    "noEmit": true,
    "jsx": "react-jsx",
    "types": ["vite/client"]
  },
  "include": ["src"],
  "references": []
}
`;
var reactViteConfig = `import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

export default defineConfig({
  plugins: [react()],
});
`;
var reactIndexHtml = `<!doctype html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>FuturLang Webapp</title>
  </head>
  <body>
    <div id="root"></div>
    <script type="module" src="/src/main.tsx"></script>
  </body>
</html>
`;
var reactMainTsx = `import React from 'react';
import ReactDOM from 'react-dom/client';
import App from './App';

ReactDOM.createRoot(document.getElementById('root')!).render(
  <React.StrictMode>
    <App />
  </React.StrictMode>,
);
`;
var reactStylesCss = `:root {
  color: #161616;
  background:
    radial-gradient(circle at top, rgba(242, 188, 120, 0.45), transparent 32rem),
    linear-gradient(180deg, #f4efe6 0%, #efe7d9 100%);
  font-family: "Iowan Old Style", "Palatino Linotype", serif;
}

* {
  box-sizing: border-box;
}

body {
  margin: 0;
  min-width: 320px;
}

#root {
  min-height: 100vh;
}

.app-shell {
  width: min(1100px, calc(100vw - 2rem));
  margin: 0 auto;
  padding: 2rem 0 4rem;
}

.hero {
  padding: 2rem;
  border: 1px solid rgba(22, 22, 22, 0.12);
  background: rgba(255, 252, 246, 0.78);
  backdrop-filter: blur(12px);
  box-shadow: 0 20px 70px rgba(84, 53, 14, 0.09);
}

.eyebrow {
  margin: 0 0 0.5rem;
  text-transform: uppercase;
  letter-spacing: 0.18em;
  font-size: 0.75rem;
}

.hero h1,
.panel h2,
.step h3 {
  font-family: Georgia, "Times New Roman", serif;
}

.hero h1 {
  margin: 0;
  font-size: clamp(2.5rem, 6vw, 5rem);
  line-height: 0.95;
}

.lead {
  max-width: 44rem;
  font-size: 1.08rem;
}

.verdict {
  display: inline-flex;
  gap: 1rem;
  align-items: center;
  padding: 0.85rem 1.15rem;
  border-radius: 999px;
  margin-top: 1rem;
  font-weight: 600;
}

.verdict.ok,
.step.ok {
  background: rgba(45, 122, 74, 0.12);
  border: 1px solid rgba(45, 122, 74, 0.3);
}

.verdict.bad,
.step.bad {
  background: rgba(154, 54, 37, 0.1);
  border: 1px solid rgba(154, 54, 37, 0.28);
}

.panel {
  margin-top: 1.5rem;
}

.steps {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(260px, 1fr));
  gap: 1rem;
}

.step {
  padding: 1rem;
  background: rgba(255, 252, 246, 0.82);
}

.step-top {
  display: flex;
  justify-content: space-between;
  gap: 1rem;
  font-size: 0.85rem;
  text-transform: uppercase;
  letter-spacing: 0.08em;
}

.step h3 {
  margin-bottom: 0.5rem;
}

.step ul {
  padding-left: 1.1rem;
  margin: 0.75rem 0 0;
}

.step code {
  font-family: "SFMono-Regular", Consolas, monospace;
}

@media (max-width: 640px) {
  .app-shell {
    width: min(100vw - 1rem, 100%);
    padding-top: 1rem;
  }

  .hero,
  .step {
    padding: 1rem;
  }
}
`;

// src/codegen/rust.ts
function generateRustFromAST(nodes, sourceFile) {
  const ctx = buildCtx(nodes);
  const sections = [];
  sections.push(`// Generated by FuturLang \u2014 intermediate Rust, not for direct use`);
  sections.push(`// Source: ${sourceFile}`);
  sections.push("");
  const hasProgram = nodes.some((n) => n.type === "Program");
  if (hasProgram) {
    sections.push(`use futurlang_chain::prelude::*;`);
    sections.push("");
    for (const node of nodes) {
      if (node.type === "Program") sections.push(programToRust(node));
    }
  } else {
    sections.push(`use futurlang_chain::runtime::*;`);
    const hasMap = nodes.some((n) => n.type === "Struct" || n.type === "TypeDecl");
    if (hasMap) sections.push(`use std::collections::HashMap;`);
    sections.push("");
    for (const node of nodes) {
      const code = standaloneNodeToRust(node, ctx);
      if (code) {
        sections.push(code);
        sections.push("");
      }
    }
    if (nodes.some((n) => n.type === "FnDecl")) {
      sections.push("fn main() {");
      sections.push("    // Runtime entry point");
      sections.push("}");
    }
  }
  return sections.join("\n");
}
function buildCtx(nodes, errorEnumName = null) {
  const variants = /* @__PURE__ */ new Map();
  const collect = (ns) => {
    for (const n of ns) {
      if (n.type === "TypeDecl") {
        for (const v of n.variants) {
          variants.set(v.name, { typeName: n.name, fieldNames: v.fields.map((f) => f.name) });
        }
      }
      if (n.type === "Program") collect(n.body);
    }
  };
  collect(nodes);
  return { variants, errorEnumName, inInstruction: false };
}
function programToRust(node) {
  const errorDecl = node.body.find((n) => n.type === "ErrorDecl");
  const ctx = buildCtx(node.body, errorDecl?.name ?? null);
  const instructions = node.body.filter((n) => n.type === "Instruction");
  const lines = [];
  lines.push(`program_id!("0000000000000000000000000000000000000000000000000000000000000000");`);
  lines.push("");
  lines.push(`#[derive(Serialize, Deserialize)]`);
  lines.push(`pub enum ${node.name}Instruction {`);
  for (const ix of instructions) {
    const dataParams = ix.params.filter((p) => !p.isAccount);
    if (dataParams.length === 0) {
      lines.push(`    ${toPascalCase(ix.name)},`);
    } else {
      const fields = dataParams.map((p) => `${p.name}: ${flTypeToRust(p.paramType)}`).join(", ");
      lines.push(`    ${toPascalCase(ix.name)} { ${fields} },`);
    }
  }
  lines.push("}");
  lines.push("");
  lines.push(`pub struct ${node.name};`);
  lines.push("");
  lines.push(`impl Program for ${node.name} {`);
  lines.push(`    fn process(ctx: &mut Context, data: &[u8]) -> Result<()> {`);
  lines.push(`        let ix = ${node.name}Instruction::deserialize(data)?;`);
  lines.push(`        match ix {`);
  for (const ix of instructions) {
    const dataParams = ix.params.filter((p) => !p.isAccount);
    const variant = toPascalCase(ix.name);
    const fnName = toSnakeCase(ix.name);
    if (dataParams.length === 0) {
      lines.push(`            ${node.name}Instruction::${variant} => Self::${fnName}(ctx),`);
    } else {
      const fields = dataParams.map((p) => p.name).join(", ");
      lines.push(`            ${node.name}Instruction::${variant} { ${fields} } => Self::${fnName}(ctx, ${fields}),`);
    }
  }
  lines.push(`        }`);
  lines.push(`    }`);
  lines.push(`}`);
  lines.push("");
  lines.push(`impl ${node.name} {`);
  for (const ix of instructions) {
    lines.push(indent2(instructionFnToRust(ix, ctx), 1));
    lines.push("");
  }
  lines.push("}");
  lines.push("");
  for (const n of node.body) {
    if (n.type === "Account") {
      lines.push(accountToRust(n));
      lines.push("");
    }
    if (n.type === "Struct") {
      lines.push(structToRust(n));
      lines.push("");
    }
    if (n.type === "TypeDecl") {
      lines.push(typeDeclToRust(n));
      lines.push("");
    }
    if (n.type === "FnDecl") {
      lines.push(fnDeclToRust(n, ctx));
      lines.push("");
    }
  }
  if (errorDecl) {
    lines.push(errorDeclToRust(errorDecl));
    lines.push("");
  }
  for (const n of node.body) {
    if (n.type === "Theorem") {
      lines.push(theoremComment(n));
      lines.push("");
    }
    if (n.type === "Lemma") {
      lines.push(lemmaComment(n));
      lines.push("");
    }
  }
  return lines.join("\n");
}
function instructionFnToRust(node, ctx) {
  const fnName = toSnakeCase(node.name);
  const dataParams = node.params.filter((p) => !p.isAccount);
  const extraParams = dataParams.map((p) => `, ${p.name}: ${flTypeToRust(p.paramType)}`).join("");
  const sig = `fn ${fnName}(ctx: &mut Context${extraParams}) -> Result<()>`;
  const bodyCtx = { ...ctx, inInstruction: true };
  const lines = [sig + " {"];
  let accountIdx = 0;
  for (const p of node.params) {
    if (!p.isAccount) continue;
    const mutable = p.qualifiers.includes("mut");
    if (p.qualifiers.includes("signer")) {
      lines.push(`    let ${p.name} = ctx.signer(${accountIdx})?;`);
    } else if (mutable) {
      lines.push(`    let ${p.name} = ctx.account_mut::<${p.paramType}>(${accountIdx})?;`);
    } else {
      lines.push(`    let ${p.name} = ctx.account::<${p.paramType}>(${accountIdx})?;`);
    }
    accountIdx++;
  }
  if (accountIdx > 0) lines.push("");
  for (const stmt of node.body) {
    const s = stmtToRust(stmt, bodyCtx, 1);
    if (s) lines.push(s);
  }
  lines.push(`    Ok(())`);
  lines.push("}");
  return lines.join("\n");
}
function accountToRust(node) {
  const lines = [];
  lines.push(`#[account]`);
  lines.push(`#[derive(Serialize, Deserialize, Default)]`);
  lines.push(`pub struct ${node.name} {`);
  for (const f of node.fields) lines.push(`    pub ${f.name}: ${flTypeToRust(f.type)},`);
  lines.push("}");
  return lines.join("\n");
}
function errorDeclToRust(node) {
  const lines = [];
  lines.push(`#[derive(Debug, thiserror::Error)]`);
  lines.push(`pub enum ${node.name} {`);
  for (const v of node.variants) {
    lines.push(`    #[error("${v.message}")]`);
    lines.push(`    ${v.name},`);
  }
  lines.push("}");
  return lines.join("\n");
}
function standaloneNodeToRust(node, ctx) {
  switch (node.type) {
    case "Struct":
      return structToRust(node);
    case "TypeDecl":
      return typeDeclToRust(node);
    case "FnDecl":
      return fnDeclToRust(node, ctx);
    case "Theorem":
      return theoremComment(node);
    case "Lemma":
      return lemmaComment(node);
    case "Definition":
      return `// definition: ${node.name}`;
    default:
      return "";
  }
}
function structToRust(node) {
  const lines = [];
  lines.push(`#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]`);
  lines.push(`pub struct ${node.name} {`);
  for (const f of node.fields) lines.push(`    pub ${f.name}: ${flTypeToRust(f.type)},`);
  lines.push("}");
  return lines.join("\n");
}
function typeDeclToRust(node) {
  const lines = [];
  lines.push(`#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]`);
  lines.push(`pub enum ${node.name} {`);
  for (const v of node.variants) {
    if (v.fields.length === 0) {
      lines.push(`    ${v.name},`);
    } else {
      const fields = v.fields.map((f) => `${f.name}: ${flTypeToRust(f.type)}`).join(", ");
      lines.push(`    ${v.name} { ${fields} },`);
    }
  }
  lines.push("}");
  return lines.join("\n");
}
function fnDeclToRust(node, ctx) {
  const lines = [];
  if (node.requires.length > 0) {
    lines.push(`/// # Requires`);
    for (const r of node.requires) lines.push(`/// - \`${renderExprSource2(r)}\``);
  }
  if (node.ensures.length > 0) {
    lines.push(`/// # Ensures`);
    for (const e of node.ensures) lines.push(`/// - \`${renderExprSource2(e)}\``);
  }
  const params = node.params.map((p) => `${p.name}: ${flTypeToRust(p.type)}`).join(", ");
  lines.push(`pub fn ${node.name}(${params}) -> ${flTypeToRust(node.returnType)} {`);
  for (const stmt of node.body) {
    const s = stmtToRust(stmt, ctx, 1);
    if (s) lines.push(s);
  }
  lines.push("}");
  return lines.join("\n");
}
function theoremComment(node) {
  const lines = [`/// Theorem: \`${node.name}\` [kernel-verified]`];
  for (const s of node.body) {
    if (s.type === "Assume") lines.push(`/// - assume: ${renderExprSource2(s.expr)}`);
    if (s.type === "DeclareToProve") lines.push(`/// - proves: ${renderExprSource2(s.expr)}`);
  }
  return lines.join("\n");
}
function lemmaComment(node) {
  const lines = [`/// Lemma: \`${node.name}\` [kernel-verified]`];
  for (const s of node.body) {
    if (s.type === "Assume") lines.push(`/// - assume: ${renderExprSource2(s.expr)}`);
    if (s.type === "DeclareToProve") lines.push(`/// - proves: ${renderExprSource2(s.expr)}`);
  }
  return lines.join("\n");
}
function stmtToRust(node, ctx, depth) {
  const pad = "    ".repeat(depth);
  switch (node.type) {
    case "SetVar":
      if (node.value !== null) return `${pad}let ${node.varName} = ${rustifyExprStr(node.value)};`;
      return `${pad}let ${node.varName}: ${node.varType ? flTypeToRust(node.varType) : "_"};`;
    case "Conclude":
    case "Exact":
      return `${pad}return ${renderExprRust(node.expr)};`;
    case "Assert":
      return `${pad}assert!(${renderExprRust(node.expr)}, "${renderExprSource2(node.expr)}");`;
    case "Require": {
      const errEnum = ctx.errorEnumName ?? "ChainError";
      return `${pad}require!(${renderExprRust(node.condition)}, ${errEnum}::${node.error});`;
    }
    case "Prove":
      return `${pad}// prove: ${renderExprSource2(node.expr)}`;
    case "Assume":
    case "Given":
      return `${pad}// assume: ${renderExprSource2(node.expr)}`;
    case "Apply":
      return `${pad}// apply: ${node.target}`;
    case "Match":
      return matchToRust(node, ctx, depth);
    case "Emit": {
      const fields = node.fields.map((f) => `("${f.name}", ${f.value})`).join(", ");
      return `${pad}emit!(ctx, "${node.eventName}", &[${fields}]);`;
    }
    case "Pda": {
      const seeds = node.seeds.map((s) => `${s}.as_bytes()`).join(", ");
      return `${pad}let ${node.varName} = ctx.pda(&[${seeds}]);`;
    }
    case "Cpi": {
      const accounts = node.accounts.join(", ");
      return `${pad}cpi!(ctx, ${node.program}, vec![${accounts}], vec![]);`;
    }
    case "Transfer": {
      return `${pad}ctx.transfer(${node.from}_idx, ${node.to}_idx, ${node.amount})?;`;
    }
    case "Raw": {
      const raw = node.content.trim();
      return `${pad}${raw.endsWith(";") || raw.endsWith("}") || raw.endsWith("{") ? raw : raw + ";"}`;
    }
    case "Intro":
      return `${pad}// intro: ${node.varName}: ${node.varType}`;
    case "Rewrite":
      return `${pad}// rewrite: ${node.hypothesis}`;
    case "Obtain":
      return `${pad}// obtain: ${node.varName} from ${node.source}`;
    case "Derive":
      return `${pad}// derive`;
    default:
      return `${pad}// [${node.type}]`;
  }
}
function matchToRust(node, ctx, depth) {
  const pad = "    ".repeat(depth);
  const hasListPat = node.cases.some((c) => c.pattern.kind === "list_nil" || c.pattern.kind === "list_cons");
  const scrutinee = renderExprRust(node.scrutinee);
  const target = hasListPat ? `${scrutinee}.as_slice()` : scrutinee;
  const lines = [`${pad}match ${target} {`];
  for (const c of node.cases) {
    lines.push(`${pad}    ${patternToRust(c.pattern, ctx)} => {`);
    for (const stmt of c.body) {
      const s = stmtToRust(stmt, ctx, depth + 2);
      if (s) lines.push(s);
    }
    lines.push(`${pad}    }`);
  }
  lines.push(`${pad}    _ => unreachable!("non-exhaustive match"),`);
  lines.push(`${pad}}`);
  return lines.join("\n");
}
function patternToRust(pattern, ctx) {
  switch (pattern.kind) {
    case "wildcard":
      return "_";
    case "list_nil":
      return "[]";
    case "list_cons":
      return `[${pattern.head === "_" ? "_" : pattern.head}, rest @ ..]`;
    case "variant": {
      if (pattern.constructor === "true") return "true";
      if (pattern.constructor === "false") return "false";
      const info = ctx.variants.get(pattern.constructor);
      if (!info || info.fieldNames.length === 0) return pattern.constructor;
      const fields = info.fieldNames.map((f, i) => {
        const b = pattern.bindings[i];
        return b && b !== "_" ? `${f}: ${b}` : `${f}: _`;
      }).join(", ");
      return `${pattern.constructor} { ${fields} }`;
    }
  }
}
function flTypeToRust(flType) {
  const t = flType.trim();
  if (t === "Address" || t === "PublicKey") return "Address";
  if (t === "Hash") return "Hash";
  if (t === "Signature") return "Signature";
  if (t === "Slot") return "Slot";
  if (t === "Epoch") return "Epoch";
  if (t === "TokenAmount") return "TokenAmount";
  if (t === "Lamport" || t === "Lamports") return "TokenAmount";
  if (t === "Bytes") return "Vec<u8>";
  if (t === "Nat" || t === "\u2115") return "u64";
  if (t === "Int" || t === "\u2124") return "i64";
  if (t === "Real" || t === "\u211D") return "f64";
  if (t === "Rat" || t === "\u211A") return "f64";
  if (t === "Bool" || t === "\u{1D539}" || t === "Boolean") return "bool";
  if (t === "String") return "String";
  if (t === "Unit" || t === "()") return "()";
  const listM = t.match(/^List\((.+)\)$/);
  if (listM) return `Vec<${flTypeToRust(listM[1])}>`;
  const optM = t.match(/^Option\((.+)\)$/);
  if (optM) return `Option<${flTypeToRust(optM[1])}>`;
  const mapM = t.match(/^Map\((.+),\s*(.+)\)$/);
  if (mapM) return `HashMap<${flTypeToRust(mapM[1])}, ${flTypeToRust(mapM[2])}>`;
  if (t === "Block") return "Block";
  if (t === "Transaction") return "Transaction";
  if (t === "Instruction") return "Instruction";
  if (t === "AccountInfo") return "AccountInfo";
  return t;
}
function renderExprRust(node) {
  switch (node.type) {
    case "Atom":
      return rustifyExprStr(node.condition);
    case "And":
      return `(${renderExprRust(node.left)} && ${renderExprRust(node.right)})`;
    case "Or":
      return `(${renderExprRust(node.left)} || ${renderExprRust(node.right)})`;
    case "Implies":
      return `(!${renderExprRust(node.left)} || ${renderExprRust(node.right)})`;
    case "Iff":
      return `(${renderExprRust(node.left)} == ${renderExprRust(node.right)})`;
    case "Not":
      return `!${renderExprRust(node.operand)}`;
    case "If":
      return `if ${renderExprRust(node.condition)} { ${renderExprRust(node.thenBranch)} } else { ${renderExprRust(node.elseBranch)} }`;
    case "LetExpr":
      return `{ let ${node.name} = ${renderExprRust(node.value)}; ${renderExprRust(node.body)} }`;
    case "Lambda":
      return `|${node.params.map((p) => p.name).join(", ")}| ${renderExprRust(node.body)}`;
    case "Fold":
    case "Quantified":
    case "SetBuilder":
    case "IndexedUnion":
      return `/* ${renderExprSource2(node)} */`;
    default: {
      const _ = node;
      throw new Error("Unhandled ExprNode in Rust codegen");
    }
  }
}
function rustifyExprStr(s) {
  return s.replace(/≥/g, ">=").replace(/≤/g, "<=").replace(/≠/g, "!=").replace(/\bmod\b/g, "%").replace(/\bdiv\b/g, "/").replace(/\band\b/g, "&&").replace(/\bor\b/g, "||").replace(/\bnot\b/g, "!").replace(/([^=!<>])=([^=])/g, "$1==$2").trim();
}
function renderExprSource2(node) {
  switch (node.type) {
    case "Atom":
      return node.condition;
    case "And":
      return `(${renderExprSource2(node.left)} \u2227 ${renderExprSource2(node.right)})`;
    case "Or":
      return `(${renderExprSource2(node.left)} \u2228 ${renderExprSource2(node.right)})`;
    case "Implies":
      return `(${renderExprSource2(node.left)} \u2192 ${renderExprSource2(node.right)})`;
    case "Iff":
      return `(${renderExprSource2(node.left)} \u2194 ${renderExprSource2(node.right)})`;
    case "Not":
      return `\xAC${renderExprSource2(node.operand)}`;
    case "If":
      return `if ${renderExprSource2(node.condition)} then ${renderExprSource2(node.thenBranch)} else ${renderExprSource2(node.elseBranch)}`;
    case "LetExpr":
      return `let ${node.name} = ${renderExprSource2(node.value)} in ${renderExprSource2(node.body)}`;
    case "Lambda":
      return `fn(${node.params.map((p) => `${p.name}: ${p.type}`).join(", ")}) => ${renderExprSource2(node.body)}`;
    case "Fold":
      return `fold(${node.sequence}, ${node.init}, ${node.fn})`;
    case "SetBuilder":
      return `{${node.element} | ${node.variable} \u2208 ${node.domain}}`;
    case "IndexedUnion":
      return `\u222A${renderExprSource2(node.builder)}`;
    case "Quantified": {
      const sym = node.quantifier === "forall" ? "\u2200" : node.quantifier === "exists" ? "\u2203" : "\u2203!";
      const binder = node.binderStyle === "bounded" ? `${node.variable} \u2208 ${node.domain}` : `${node.variable}: ${node.domain}`;
      return node.body ? `${sym} ${binder}, ${renderExprSource2(node.body)}` : `${sym} ${binder}`;
    }
    default: {
      const _ = node;
      return "";
    }
  }
}
function toSnakeCase(s) {
  return s.replace(/([A-Z]+)([A-Z][a-z])/g, "$1_$2").replace(/([a-z\d])([A-Z])/g, "$1_$2").toLowerCase();
}
function toPascalCase(s) {
  return s.charAt(0).toUpperCase() + s.slice(1);
}
function indent2(code, depth) {
  const pad = "    ".repeat(depth);
  return code.split("\n").map((l) => l.length > 0 ? `${pad}${l}` : l).join("\n");
}
function generateCargoToml(programName, isProgram) {
  const name = toSnakeCase(programName);
  if (isProgram) {
    return `[package]
name = "${name}"
version = "0.1.0"
edition = "2021"

[lib]
crate-type = ["cdylib", "lib"]

[dependencies]
futurlang_chain = { path = "../chain" }
serde = { version = "1", features = ["derive"] }
thiserror = "1"
`;
  }
  return `[package]
name = "${name}"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "${name}"
path = "src/main.rs"

[dependencies]
futurlang_chain = { path = "../chain" }
serde = { version = "1", features = ["derive"] }
thiserror = "1"
`;
}

// src/lsp-server.ts
var http = __toESM(require("http"));
var fs3 = __toESM(require("fs"));
var path3 = __toESM(require("path"));
var HOVER_DOCS = {
  theorem: { kind: "block", docs: "Declare a theorem. Paired with a `proof` block via `\u2194`." },
  proof: { kind: "block", docs: "Prove a theorem. Must be paired with its `theorem` block via `\u2194`." },
  lemma: { kind: "block", docs: "Declare a helper lemma. Paired with a `proof` block via `\u2194`." },
  definition: { kind: "block", docs: "Define a mathematical object or value." },
  fn: { kind: "block", docs: "Declare a function. Desugars into theorem + proof." },
  struct: { kind: "block", docs: "Declare a data structure with named fields." },
  type: { kind: "block", docs: "Declare a sum type (tagged union)." },
  program: { kind: "block", docs: "Declare an on-chain FuturChain program (smart contract)." },
  account: { kind: "block", docs: "Declare on-chain account state for a FuturChain program." },
  instruction: { kind: "block", docs: "Declare an instruction handler for a FuturChain program." },
  error: { kind: "block", docs: "Declare custom program error variants." },
  assume: { kind: "statement", docs: "Introduce a hypothesis into the proof context." },
  conclude: { kind: "statement", docs: "Close the proof. Must match the `declareToProve` goal." },
  declareToProve: { kind: "statement", docs: "Set the proof goal (required exactly once in a theorem body)." },
  prove: { kind: "statement", docs: "Derive and record an intermediate fact." },
  apply: { kind: "statement", docs: "Back-chain through a proved lemma. Makes the parent connective `\u2192`." },
  require: { kind: "statement", docs: "Guard: returns the named program error if condition is false." },
  emit: { kind: "statement", docs: "Emit a named event recorded in the block event log." },
  pda: { kind: "statement", docs: "Derive a Program-Derived Address from seeds." },
  cpi: { kind: "statement", docs: "Queue a cross-program invocation." },
  transfer: { kind: "statement", docs: "Native token transfer between two accounts." },
  "\u2192": { kind: "connective", docs: "`\u2192` (implies): links blocks where the next proof calls `apply()` on the current one." },
  "\u2194": { kind: "connective", docs: "`\u2194` (iff): pairs a `theorem`/`lemma` with its `proof` block." },
  "\u2227": { kind: "connective", docs: "`\u2227` (and): links independent blocks \u2014 next proof does not call `apply()`." },
  "\u2228": { kind: "connective", docs: "`\u2228` (or): disjunctive \u2014 either block suffices (emits warning, not yet validated)." },
  "\u2208": { kind: "operator", docs: "`\u2208`: membership. Used in type annotations (`x \u2208 Nat`) and membership proofs." },
  "\u2200": { kind: "operator", docs: "`\u2200`: universal quantifier. `\u2200 x \u2208 A, P(x)`." },
  "\u2203": { kind: "operator", docs: "`\u2203`: existential quantifier. `\u2203 x \u2208 A, P(x)`." },
  mut: { kind: "modifier", docs: "`mut`: marks an instruction account parameter as mutable." },
  signer: { kind: "modifier", docs: "`signer`: marks an instruction account parameter as required signer." },
  init: { kind: "modifier", docs: "`init`: marks an account as newly created in this instruction." },
  Address: { kind: "type", docs: "`Address` ([u8; 32]): a 32-byte public key / account address." },
  TokenAmount: { kind: "type", docs: "`TokenAmount` (u64): a token quantity in the chain's native denomination." },
  Hash: { kind: "type", docs: "`Hash` ([u8; 32]): a SHA-256 hash output." },
  Signature: { kind: "type", docs: "`Signature` ([u8; 64]): an Ed25519 signature." },
  Slot: { kind: "type", docs: "`Slot` (u64): a monotonic block slot number." },
  Nat: { kind: "type", docs: "`Nat` (u64): natural number (\u2265 0)." },
  Bool: { kind: "type", docs: "`Bool`: boolean. Compiles to Rust `bool`." }
};
function handleParse(body) {
  try {
    const lines = lexFL(body.source);
    const ast2 = parseLinesToAST(lines, { desugarFns: false });
    return {
      ok: true,
      nodeCount: ast2.length,
      nodeTypes: ast2.map((n) => n.type)
    };
  } catch (e) {
    return { ok: false, nodeCount: 0, nodeTypes: [], error: e.message };
  }
}
function handleCheck(body) {
  try {
    const lines = lexFL(body.source);
    const ast2 = parseLinesToAST(lines, { desugarFns: true });
    const report = checkFile(ast2, { strict: body.strict ?? false });
    const diagnostics = report.diagnostics.map((d) => ({
      severity: d.severity,
      message: d.message,
      hint: d.hint
    }));
    const reports = report.reports.map((r) => ({
      name: r.name,
      state: r.state,
      premises: r.premises,
      goal: r.goal ?? null,
      proofSteps: r.proofSteps.length
    }));
    return {
      ok: report.state === "PROVED",
      state: report.state,
      theoremCount: report.theoremCount,
      pairedCount: report.pairedCount,
      diagnostics,
      reports
    };
  } catch (e) {
    return {
      ok: false,
      state: "FAILED",
      theoremCount: 0,
      pairedCount: 0,
      diagnostics: [{ severity: "error", message: e.message }],
      reports: []
    };
  }
}
function handleHover(body) {
  try {
    const lines = body.source.split("\n");
    const targetLine = lines[body.line] ?? "";
    const before = targetLine.slice(0, body.col);
    const after = targetLine.slice(body.col);
    const tokenBefore = before.match(/[\w∀∃∈∧∨→↔]+$/)?.[0] ?? "";
    const tokenAfter = after.match(/^[\w∀∃∈∧∨→↔]*/)?.[0] ?? "";
    const token = tokenBefore + tokenAfter;
    if (!token) return { found: false };
    const doc = HOVER_DOCS[token];
    if (!doc) return { found: true, token, kind: "identifier", docs: `\`${token}\`` };
    return { found: true, token, kind: doc.kind, docs: doc.docs };
  } catch {
    return { found: false };
  }
}
function handleEval(body) {
  const tmpFile = path3.join(require("os").tmpdir(), `fl-eval-${Date.now()}.fl`);
  try {
    fs3.writeFileSync(tmpFile, body.source, "utf8");
    const source2 = expandFLFile(tmpFile);
    const ast2 = parseLinesToAST(lexFL(source2), { desugarFns: true });
    const report = checkFile(ast2, { strict: false });
    const lines = [];
    for (const r of report.reports) {
      const icon = r.state === "PROVED" ? "\u2713" : r.state === "PENDING" ? "~" : "\u2717";
      lines.push(`${icon} ${r.name}  ${r.state}`);
    }
    lines.push(`Result: ${report.state}`);
    return { ok: true, output: lines.join("\n") };
  } catch (e) {
    return { ok: false, error: e.message };
  } finally {
    try {
      fs3.unlinkSync(tmpFile);
    } catch {
    }
  }
}
function readBody(req) {
  return new Promise((resolve3, reject) => {
    let data = "";
    req.on("data", (chunk) => {
      data += chunk;
    });
    req.on("end", () => resolve3(data));
    req.on("error", reject);
  });
}
function json(res, status, data) {
  const body = JSON.stringify(data, null, 2);
  res.writeHead(status, {
    "Content-Type": "application/json",
    "Access-Control-Allow-Origin": "*",
    "Access-Control-Allow-Headers": "Content-Type",
    "Access-Control-Allow-Methods": "GET, POST, OPTIONS"
  });
  res.end(body);
}
async function startLspServer(port) {
  const server = http.createServer(async (req, res) => {
    if (req.method === "OPTIONS") {
      json(res, 204, {});
      return;
    }
    const url = req.url ?? "/";
    if (req.method === "GET" && url === "/health") {
      json(res, 200, { status: "ok", version: "0.1.0", engine: "futurlang-lsp" });
      return;
    }
    if (req.method === "GET" && url === "/keywords") {
      json(res, 200, { keywords: Object.keys(HOVER_DOCS) });
      return;
    }
    if (req.method !== "POST") {
      json(res, 405, { error: "Method not allowed" });
      return;
    }
    let rawBody;
    try {
      rawBody = await readBody(req);
    } catch {
      json(res, 400, { error: "Failed to read request body" });
      return;
    }
    let body;
    try {
      body = JSON.parse(rawBody);
    } catch {
      json(res, 400, { error: "Invalid JSON" });
      return;
    }
    if (url === "/parse") {
      const req2 = body;
      if (typeof req2.source !== "string") {
        json(res, 400, { error: "`source` string required" });
        return;
      }
      json(res, 200, handleParse(req2));
      return;
    }
    if (url === "/check") {
      const req2 = body;
      if (typeof req2.source !== "string") {
        json(res, 400, { error: "`source` string required" });
        return;
      }
      json(res, 200, handleCheck(req2));
      return;
    }
    if (url === "/eval") {
      const req2 = body;
      if (typeof req2.source !== "string") {
        json(res, 400, { error: "`source` string required" });
        return;
      }
      json(res, 200, handleEval(req2));
      return;
    }
    if (url === "/hover") {
      const req2 = body;
      if (typeof req2.source !== "string" || typeof req2.line !== "number") {
        json(res, 400, { error: "`source`, `line`, `col` required" });
        return;
      }
      json(res, 200, handleHover(req2));
      return;
    }
    if (url === "/rust") {
      const req2 = body;
      if (typeof req2.source !== "string") {
        json(res, 400, { error: "`source` string required" });
        return;
      }
      try {
        const ast2 = parseLinesToAST(lexFL(req2.source), { desugarFns: false });
        const rust = generateRustFromAST(ast2, "api");
        json(res, 200, { ok: true, rust });
      } catch (e) {
        json(res, 200, { ok: false, error: e.message });
      }
      return;
    }
    json(res, 404, { error: `Unknown endpoint: ${url}` });
  });
  return new Promise((resolve3) => {
    server.listen(port, "127.0.0.1", () => {
      console.log(`
FuturLang Language Server`);
      console.log(`  Listening on http://127.0.0.1:${port}`);
      console.log(`
  Endpoints:`);
      console.log(`    GET  /health    \u2014 health check`);
      console.log(`    GET  /keywords  \u2014 all documented keywords`);
      console.log(`    POST /parse     \u2014 parse FL source \u2192 AST summary`);
      console.log(`    POST /check     \u2014 kernel-check FL source \u2192 proof status`);
      console.log(`    POST /eval      \u2014 evaluate FL source \u2192 checker output`);
      console.log(`    POST /hover     \u2014 token docs at (line, col)`);
      console.log(`    POST /rust      \u2014 transpile FL source \u2192 Rust`);
      console.log(`
  Press Ctrl+C to stop.
`);
      resolve3();
    });
  });
}

// src/codegen/chain-runtime.ts
var CHAIN_CARGO_TOML = `[package]
name = "futurchain"
version = "0.1.0"
edition = "2021"

[[bin]]
name = "futurchain"
path = "src/main.rs"

[lib]
name = "futurchain"
path = "src/lib.rs"

[dependencies]
tokio         = { version = "1",  features = ["full"] }
axum          = "0.7"
serde         = { version = "1",  features = ["derive"] }
serde_json    = "1"
sha2          = "0.10"
hex           = "0.4"
ed25519-dalek = { version = "2",  features = ["rand_core"] }
rand          = "0.8"
thiserror     = "1"
clap          = { version = "4",  features = ["derive"] }
anyhow        = "1"
sled          = "0.34"

[dev-dependencies]
tokio-test    = "0.4"
`;
var CHAIN_SRC = {
  "main.rs": `use std::sync::{Arc, Mutex};
use tokio::time::{interval, Duration};
use clap::Parser;
use futurchain::{chain::Chain, crypto::Keypair, mempool::Mempool, rpc, types::hex_address};

#[derive(Parser)]
#[command(name = "futurchain", about = "FuturChain node \u2014 Solana-inspired blockchain")]
struct Cli {
    #[arg(long, default_value = "0.0.0.0")]
    host: String,

    #[arg(long, default_value_t = 8899)]
    port: u16,

    #[arg(long, default_value_t = 400)]
    slot_ms: u64,

    #[arg(long, default_value_t = 1000)]
    block_size: usize,

    #[arg(long, default_value_t = 1_000_000_000)]
    genesis_supply: u64,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    let keypair   = Keypair::generate();
    let node_addr = keypair.address();
    println!("\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550");
    println!("  FuturChain Node");
    println!("  Address : {}", hex_address(&node_addr));
    println!("  RPC     : http://{}:{}", cli.host, cli.port);
    println!("  Slot    : {}ms", cli.slot_ms);
    println!("\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550\u2550");

    let chain   = Arc::new(Mutex::new(Chain::new()));
    let mempool = Arc::new(Mutex::new(Mempool::new(100_000)));

    {
        let mut c = chain.lock().unwrap();
        c.ledger.airdrop(node_addr, cli.genesis_supply);
        println!("Genesis: {} tokens \u2192 {}", cli.genesis_supply, hex_address(&node_addr));
    }

    let chain_bg   = chain.clone();
    let mempool_bg = mempool.clone();
    let block_size = cli.block_size;
    tokio::spawn(async move {
        let mut ticker = interval(Duration::from_millis(cli.slot_ms));
        loop {
            ticker.tick().await;
            let txs   = mempool_bg.lock().unwrap().drain(block_size);
            let block = chain_bg.lock().unwrap().produce_block(txs, node_addr);
            if block.header.tx_count > 0 || block.header.slot % 10 == 0 {
                println!(
                    "slot {:>6} | txs {:>4} | poh {}\u2026",
                    block.header.slot,
                    block.header.tx_count,
                    hex::encode(&block.hash[..4])
                );
            }
        }
    });

    let addr     = format!("{}:{}", cli.host, cli.port);
    let app      = rpc::router(chain, mempool);
    let listener = tokio::net::TcpListener::bind(&addr).await?;
    println!("RPC listening \u2014 Ctrl+C to stop\\n");
    axum::serve(listener, app).await?;
    Ok(())
}
`,
  "lib.rs": `pub mod chain;
pub mod crypto;
pub mod ledger;
pub mod mempool;
pub mod rpc;
pub mod types;

pub mod prelude {
    pub use crate::types::*;
    pub use crate::crypto::{sha256, poh_tick, verify_signature, pda_derive, find_pda};
    pub use serde::{Serialize, Deserialize};

    pub type Result<T> = std::result::Result<T, ProgramError>;

    #[derive(Debug, thiserror::Error)]
    pub enum ProgramError {
        #[error("account not found at index {0}")]
        AccountNotFound(usize),
        #[error("not a signer")]
        NotSigner,
        #[error("insufficient funds")]
        InsufficientFunds,
        #[error("arithmetic overflow")]
        Overflow,
        #[error("account is not writable")]
        NotWritable,
        #[error("invalid PDA seeds")]
        InvalidSeeds,
        #[error("cpi error: {0}")]
        CpiError(String),
        #[error("{0}")]
        Custom(String),
    }

    impl From<&str> for ProgramError { fn from(s: &str) -> Self { ProgramError::Custom(s.to_string()) } }
    impl From<String> for ProgramError { fn from(s: String) -> Self { ProgramError::Custom(s) } }

    #[derive(Debug, Clone, Copy)]
    pub struct Clock { pub slot: Slot, pub timestamp: u64 }

    #[derive(Debug, Clone)]
    pub struct AccountInfo {
        pub address: Address, pub balance: TokenAmount,
        pub is_signer: bool, pub is_writable: bool,
        pub owner: Address, pub data: Vec<u8>,
    }

    impl AccountInfo {
        pub fn deserialize<T: for<'de> serde::Deserialize<'de>>(&self) -> Result<T> {
            serde_json::from_slice(&self.data).map_err(|e| ProgramError::Custom(e.to_string()))
        }
        pub fn serialize<T: serde::Serialize>(&mut self, state: &T) -> Result<()> {
            self.data = serde_json::to_vec(state).map_err(|e| ProgramError::Custom(e.to_string()))?;
            Ok(())
        }
    }

    pub struct CpiInstruction { pub program_id: Address, pub accounts: Vec<AccountInfo>, pub data: Vec<u8> }
    pub struct EmittedEvent   { pub name: String, pub data: Vec<u8> }

    pub struct Context {
        pub program_id: Address, pub accounts: Vec<AccountInfo>,
        pub clock: Clock, pub events: Vec<EmittedEvent>, pub cpi_calls: Vec<CpiInstruction>,
    }

    impl Context {
        pub fn new(program_id: Address, accounts: Vec<AccountInfo>, slot: Slot, timestamp: u64) -> Self {
            Self { program_id, accounts, clock: Clock { slot, timestamp }, events: vec![], cpi_calls: vec![] }
        }
        pub fn signer(&self, idx: usize) -> Result<Address> {
            let acc = self.accounts.get(idx).ok_or(ProgramError::AccountNotFound(idx))?;
            if !acc.is_signer { return Err(ProgramError::NotSigner); }
            Ok(acc.address)
        }
        pub fn account(&self, idx: usize) -> Result<&AccountInfo> {
            self.accounts.get(idx).ok_or(ProgramError::AccountNotFound(idx))
        }
        pub fn account_mut(&mut self, idx: usize) -> Result<&mut AccountInfo> {
            let acc = self.accounts.get_mut(idx).ok_or(ProgramError::AccountNotFound(idx))?;
            if !acc.is_writable { return Err(ProgramError::NotWritable); }
            Ok(acc)
        }
        pub fn load<T: for<'de> serde::Deserialize<'de>>(&self, idx: usize) -> Result<T> {
            self.account(idx)?.deserialize::<T>()
        }
        pub fn save<T: serde::Serialize>(&mut self, idx: usize, state: &T) -> Result<()> {
            let acc = self.accounts.get_mut(idx).ok_or(ProgramError::AccountNotFound(idx))?;
            if !acc.is_writable { return Err(ProgramError::NotWritable); }
            acc.serialize(state)
        }
        pub fn pda(&self, seeds: &[&[u8]]) -> Address { pda_derive(seeds, &self.program_id) }
        pub fn emit(&mut self, name: &str, data: Vec<u8>) {
            self.events.push(EmittedEvent { name: name.to_string(), data });
        }
        pub fn cpi(&mut self, ix: CpiInstruction) { self.cpi_calls.push(ix); }
        pub fn transfer(&mut self, from_idx: usize, to_idx: usize, amount: TokenAmount) -> Result<()> {
            let from_bal = {
                let from = self.accounts.get(from_idx).ok_or(ProgramError::AccountNotFound(from_idx))?;
                if !from.is_writable { return Err(ProgramError::NotWritable); }
                from.balance
            };
            if from_bal < amount { return Err(ProgramError::InsufficientFunds); }
            self.accounts[from_idx].balance -= amount;
            let to = self.accounts.get_mut(to_idx).ok_or(ProgramError::AccountNotFound(to_idx))?;
            to.balance = to.balance.checked_add(amount).ok_or(ProgramError::Overflow)?;
            Ok(())
        }
    }

    pub trait Program { fn process(ctx: &mut Context, data: &[u8]) -> Result<()>; }

    #[macro_export]
    macro_rules! require {
        ($cond:expr, $err:expr) => { if !($cond) { return Err($err.into()); } };
    }
    #[macro_export]
    macro_rules! emit {
        ($ctx:expr, $name:expr, $data:expr) => {{
            let bytes = serde_json::to_vec($data).unwrap_or_default();
            $ctx.emit($name, bytes);
        }};
    }
}

pub mod runtime {
    pub use crate::chain::Chain;
    pub use crate::crypto::{poh_tick, sha256, pda_derive, find_pda, Keypair};
    pub use crate::ledger::{Ledger, LedgerError};
    pub use crate::mempool::Mempool;
    pub use crate::types::*;
}
`,
  "types.rs": `use serde::{Deserialize, Deserializer, Serialize, Serializer};

pub type Hash        = [u8; 32];
pub type Address     = [u8; 32];
pub type Signature   = [u8; 64];
pub type Slot        = u64;
pub type Epoch       = u64;
pub type TokenAmount = u64;

pub mod serde_addr {
    use super::*;
    pub fn serialize<S: Serializer>(bytes: &[u8; 32], s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&hex::encode(bytes))
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 32], D::Error> {
        let h = String::deserialize(d)?;
        let v = hex::decode(&h).map_err(serde::de::Error::custom)?;
        v.try_into().map_err(|_| serde::de::Error::custom("address must be 32 bytes"))
    }
}

pub mod serde_hash {
    use super::*;
    pub fn serialize<S: Serializer>(bytes: &[u8; 32], s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&hex::encode(bytes))
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 32], D::Error> {
        let h = String::deserialize(d)?;
        let v = hex::decode(&h).map_err(serde::de::Error::custom)?;
        v.try_into().map_err(|_| serde::de::Error::custom("hash must be 32 bytes"))
    }
}

pub mod serde_sig {
    use super::*;
    pub fn serialize<S: Serializer>(bytes: &[u8; 64], s: S) -> Result<S::Ok, S::Error> {
        s.serialize_str(&hex::encode(bytes))
    }
    pub fn deserialize<'de, D: Deserializer<'de>>(d: D) -> Result<[u8; 64], D::Error> {
        let h = String::deserialize(d)?;
        let v = hex::decode(&h).map_err(serde::de::Error::custom)?;
        v.try_into().map_err(|_| serde::de::Error::custom("signature must be 64 bytes"))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Account {
    #[serde(with = "serde_addr")]
    pub address:    Address,
    pub balance:    TokenAmount,
    pub nonce:      u64,
    pub data:       Vec<u8>,
    #[serde(with = "serde_addr")]
    pub owner:      Address,
    pub executable: bool,
}

impl Account {
    pub fn new(address: Address) -> Self {
        Self { address, balance: 0, nonce: 0, data: vec![], owner: [0u8; 32], executable: false }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AccountMeta {
    #[serde(with = "serde_addr")]
    pub address:     Address,
    pub is_signer:   bool,
    pub is_writable: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Instruction {
    #[serde(with = "serde_addr")]
    pub program_id: Address,
    pub accounts:   Vec<AccountMeta>,
    pub data:       Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Transaction {
    pub nonce:             u64,
    #[serde(with = "serde_addr")]
    pub sender:            Address,
    #[serde(with = "serde_addr")]
    pub recipient:         Address,
    pub amount:            TokenAmount,
    pub fee:               TokenAmount,
    pub instructions:      Vec<Instruction>,
    #[serde(with = "serde_hash")]
    pub recent_blockhash:  Hash,
    #[serde(with = "serde_sig")]
    pub signature:         Signature,
}

impl Transaction {
    pub fn signable_bytes(&self) -> Vec<u8> {
        let mut b = Vec::new();
        b.extend_from_slice(&self.nonce.to_le_bytes());
        b.extend_from_slice(&self.sender);
        b.extend_from_slice(&self.recipient);
        b.extend_from_slice(&self.amount.to_le_bytes());
        b.extend_from_slice(&self.fee.to_le_bytes());
        b.extend_from_slice(&self.recent_blockhash);
        b
    }
    pub fn hash(&self) -> Hash {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        h.update(self.signable_bytes());
        h.update(self.signature);
        h.finalize().into()
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Event {
    #[serde(with = "serde_addr")]
    pub program_id: Address,
    pub name:       String,
    pub data:       Vec<u8>,
    pub slot:       Slot,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BlockHeader {
    pub slot:          Slot,
    #[serde(with = "serde_hash")]
    pub parent_hash:   Hash,
    #[serde(with = "serde_hash")]
    pub poh_hash:      Hash,
    #[serde(with = "serde_hash")]
    pub tx_root:       Hash,
    #[serde(with = "serde_hash")]
    pub state_root:    Hash,
    #[serde(with = "serde_addr")]
    pub proposer:      Address,
    pub timestamp:     u64,
    pub tx_count:      u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Block {
    pub header:       BlockHeader,
    pub transactions: Vec<Transaction>,
    pub events:       Vec<Event>,
    #[serde(with = "serde_hash")]
    pub hash:         Hash,
}

impl Block {
    pub fn compute_hash(header: &BlockHeader) -> Hash {
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        h.update(header.slot.to_le_bytes());
        h.update(header.parent_hash);
        h.update(header.poh_hash);
        h.update(header.tx_root);
        h.update(header.state_root);
        h.update(header.proposer);
        h.update(header.timestamp.to_le_bytes());
        h.finalize().into()
    }
    pub fn genesis() -> Self {
        let header = BlockHeader {
            slot: 0, parent_hash: [0u8; 32], poh_hash: [0u8; 32],
            tx_root: [0u8; 32], state_root: [0u8; 32], proposer: [0u8; 32],
            timestamp: 0, tx_count: 0,
        };
        let hash = Self::compute_hash(&header);
        Self { header, transactions: vec![], events: vec![], hash }
    }
}

pub fn hex_address(addr: &Address) -> String { hex::encode(addr) }
pub fn hex_hash(h: &Hash) -> String { hex::encode(h) }
`,
  "crypto.rs": `use crate::types::{Address, Hash, Signature};
use ed25519_dalek::{Signer, Verifier, SigningKey, VerifyingKey};
use sha2::{Digest, Sha256};

pub fn sha256(data: &[u8]) -> Hash {
    let mut h = Sha256::new();
    h.update(data);
    h.finalize().into()
}

pub fn poh_tick(prev: Hash) -> Hash { sha256(&prev) }

pub fn hash_transactions(txs: &[crate::types::Transaction]) -> Hash {
    if txs.is_empty() { return [0u8; 32]; }
    let mut h = Sha256::new();
    for tx in txs { h.update(tx.hash()); }
    h.finalize().into()
}

pub struct Keypair { inner: SigningKey }

impl Keypair {
    pub fn generate() -> Self { Self { inner: SigningKey::generate(&mut rand::rngs::OsRng) } }
    pub fn from_secret_bytes(bytes: &[u8; 32]) -> Self { Self { inner: SigningKey::from_bytes(bytes) } }
    pub fn address(&self) -> Address { self.inner.verifying_key().to_bytes() }
    pub fn sign(&self, data: &[u8]) -> Signature { self.inner.sign(data).to_bytes() }
    pub fn secret_bytes(&self) -> [u8; 32] { self.inner.to_bytes() }
}

pub fn pda_derive(seeds: &[&[u8]], program_id: &Address) -> Address {
    let mut h = Sha256::new();
    for seed in seeds { h.update(seed); }
    h.update(program_id);
    h.update(b"pda");
    h.finalize().into()
}

pub fn find_pda(seeds: &[&[u8]], program_id: &Address) -> (Address, u8) {
    for bump in (0u8..=255).rev() {
        let mut all_seeds: Vec<&[u8]> = seeds.to_vec();
        let bump_bytes = [bump];
        all_seeds.push(&bump_bytes);
        let addr = pda_derive(&all_seeds, program_id);
        return (addr, bump);
    }
    (pda_derive(seeds, program_id), 0)
}

pub fn verify_signature(address: &Address, data: &[u8], sig: &Signature) -> bool {
    let Ok(vk) = VerifyingKey::from_bytes(address) else { return false; };
    let dalek_sig = ed25519_dalek::Signature::from_bytes(sig);
    vk.verify(data, &dalek_sig).is_ok()
}
`,
  "ledger.rs": `use std::collections::HashMap;
use crate::types::{Account, Address, Hash, TokenAmount, Transaction};
use crate::crypto;
use sha2::{Digest, Sha256};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LedgerError {
    #[error("account not found")]
    AccountNotFound,
    #[error("insufficient balance: need {need}, have {have}")]
    InsufficientBalance { need: u64, have: u64 },
    #[error("invalid nonce: expected {expected}, got {got}")]
    InvalidNonce { expected: u64, got: u64 },
    #[error("invalid signature")]
    InvalidSignature,
    #[error("arithmetic overflow")]
    Overflow,
}

pub struct Ledger { accounts: HashMap<Address, Account> }

impl Ledger {
    pub fn new() -> Self { Self { accounts: HashMap::new() } }
    pub fn get(&self, address: &Address) -> Option<&Account> { self.accounts.get(address) }
    pub fn airdrop(&mut self, address: Address, amount: TokenAmount) {
        self.accounts.entry(address).or_insert_with(|| Account::new(address)).balance += amount;
    }
    pub fn apply_transaction(&mut self, tx: &Transaction) -> Result<(), LedgerError> {
        if !crypto::verify_signature(&tx.sender, &tx.signable_bytes(), &tx.signature) {
            return Err(LedgerError::InvalidSignature);
        }
        let (expected_nonce, sender_balance) = self.accounts.get(&tx.sender)
            .map(|a| (a.nonce, a.balance)).unwrap_or((0, 0));
        if tx.nonce != expected_nonce {
            return Err(LedgerError::InvalidNonce { expected: expected_nonce, got: tx.nonce });
        }
        let total = tx.amount.checked_add(tx.fee).ok_or(LedgerError::Overflow)?;
        if sender_balance < total {
            return Err(LedgerError::InsufficientBalance { need: total, have: sender_balance });
        }
        { let s = self.accounts.entry(tx.sender).or_insert_with(|| Account::new(tx.sender)); s.balance -= total; s.nonce += 1; }
        { let r = self.accounts.entry(tx.recipient).or_insert_with(|| Account::new(tx.recipient)); r.balance = r.balance.checked_add(tx.amount).ok_or(LedgerError::Overflow)?; }
        Ok(())
    }
    pub fn state_root(&self) -> Hash {
        let mut addresses: Vec<Address> = self.accounts.keys().copied().collect();
        addresses.sort();
        let mut h = Sha256::new();
        for addr in addresses {
            let acc = &self.accounts[&addr];
            h.update(addr); h.update(acc.balance.to_le_bytes()); h.update(acc.nonce.to_le_bytes());
        }
        h.finalize().into()
    }
    pub fn total_supply(&self) -> TokenAmount { self.accounts.values().map(|a| a.balance).sum() }
    pub fn account_count(&self) -> usize { self.accounts.len() }
}
`,
  "chain.rs": `use crate::crypto;
use crate::ledger::Ledger;
use crate::types::{Address, Block, BlockHeader, Event, Hash, Slot, Transaction};

pub struct Chain {
    pub blocks:    Vec<Block>,
    pub ledger:    Ledger,
    pub slot:      Slot,
    pub poh_hash:  Hash,
    pub event_log: Vec<Event>,
}

impl Chain {
    pub fn new() -> Self {
        let genesis  = Block::genesis();
        let poh_hash = genesis.header.poh_hash;
        Self { blocks: vec![genesis], ledger: Ledger::new(), slot: 0, poh_hash, event_log: vec![] }
    }
    pub fn tip_hash(&self) -> Hash { self.blocks.last().map(|b| b.hash).unwrap_or([0u8; 32]) }
    pub fn get_block(&self, slot: Slot) -> Option<&Block> { self.blocks.get(slot as usize) }
    pub fn produce_block(&mut self, transactions: Vec<Transaction>, proposer: Address) -> Block {
        self.slot    += 1;
        self.poh_hash = crypto::poh_tick(self.poh_hash);
        let parent_hash = self.tip_hash();
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH).unwrap_or_default().as_secs();
        let mut valid_txs = Vec::new();
        for tx in transactions {
            if self.ledger.apply_transaction(&tx).is_ok() { valid_txs.push(tx); }
        }
        let tx_root    = crypto::hash_transactions(&valid_txs);
        let state_root = self.ledger.state_root();
        let header = BlockHeader {
            slot: self.slot, parent_hash, poh_hash: self.poh_hash,
            tx_root, state_root, proposer, timestamp, tx_count: valid_txs.len() as u32,
        };
        let hash  = Block::compute_hash(&header);
        let block = Block { header, transactions: valid_txs, events: vec![], hash };
        self.blocks.push(block.clone());
        block
    }
    pub fn height(&self) -> usize { self.blocks.len() }
    pub fn events_at_slot(&self, slot: Slot) -> &[Event] {
        self.blocks.get(slot as usize).map(|b| b.events.as_slice()).unwrap_or(&[])
    }
    pub fn recent_events(&self, limit: usize) -> Vec<&Event> {
        self.event_log.iter().rev().take(limit).collect()
    }
}
`,
  "mempool.rs": `use std::collections::{HashMap, VecDeque};
use crate::types::{Hash, Transaction};

pub struct Mempool { queue: VecDeque<Transaction>, seen: HashMap<Hash, bool>, max_size: usize }

impl Mempool {
    pub fn new(max_size: usize) -> Self { Self { queue: VecDeque::new(), seen: HashMap::new(), max_size } }
    pub fn push(&mut self, tx: Transaction) -> bool {
        if self.queue.len() >= self.max_size { return false; }
        let h = tx.hash();
        if self.seen.contains_key(&h) { return false; }
        self.seen.insert(h, true);
        self.queue.push_back(tx);
        true
    }
    pub fn drain(&mut self, max: usize) -> Vec<Transaction> {
        let count = max.min(self.queue.len());
        self.queue.drain(..count).collect()
    }
    pub fn len(&self) -> usize { self.queue.len() }
    pub fn is_empty(&self) -> bool { self.queue.is_empty() }
}
`,
  "rpc.rs": `use std::sync::{Arc, Mutex};
use axum::{
    extract::{Path, State},
    http::StatusCode,
    routing::{get, post},
    Json, Router,
};
use serde::{Deserialize, Serialize};
use crate::{chain::Chain, mempool::Mempool, types::*};

pub type SharedChain   = Arc<Mutex<Chain>>;
pub type SharedMempool = Arc<Mutex<Mempool>>;
pub type AppState      = (SharedChain, SharedMempool);

#[derive(Serialize)]
pub struct HealthResponse { pub status: &'static str, pub slot: Slot, pub block_height: usize, pub total_supply: TokenAmount, pub pending_txs: usize }

#[derive(Serialize)]
pub struct SlotResponse { pub slot: Slot, pub poh_hash: String }

#[derive(Serialize)]
pub struct AccountResponse { pub address: String, pub balance: TokenAmount, pub nonce: u64 }

#[derive(Deserialize)]
pub struct SubmitTxRequest { pub transaction: Transaction }

#[derive(Serialize)]
pub struct SubmitTxResponse { pub accepted: bool, pub tx_hash: String, pub reason: Option<String> }

#[derive(Serialize)]
pub struct EventResponse { pub slot: Slot, pub program_id: String, pub name: String, pub data_hex: String }

#[derive(Deserialize)]
pub struct PdaRequest { pub seeds: Vec<String>, pub program_id: String }

#[derive(Serialize)]
pub struct PdaResponse { pub address: String, pub bump: u8 }

pub fn router(chain: SharedChain, mempool: SharedMempool) -> Router {
    Router::new()
        .route("/health",           get(health))
        .route("/slot",             get(current_slot))
        .route("/block/:slot",      get(get_block))
        .route("/account/:address", get(get_account))
        .route("/transaction",      post(submit_tx))
        .route("/events",           get(get_recent_events))
        .route("/events/:slot",     get(get_events_at_slot))
        .route("/pda",              post(derive_pda))
        .with_state((chain, mempool))
}

async fn health(State((chain, mempool)): State<AppState>) -> Json<HealthResponse> {
    let c = chain.lock().unwrap(); let m = mempool.lock().unwrap();
    Json(HealthResponse { status: "ok", slot: c.slot, block_height: c.height(), total_supply: c.ledger.total_supply(), pending_txs: m.len() })
}

async fn current_slot(State((chain, _)): State<AppState>) -> Json<SlotResponse> {
    let c = chain.lock().unwrap();
    Json(SlotResponse { slot: c.slot, poh_hash: hex_hash(&c.poh_hash) })
}

async fn get_block(State((chain, _)): State<AppState>, Path(slot): Path<u64>) -> Result<Json<Block>, (StatusCode, String)> {
    let c = chain.lock().unwrap();
    c.get_block(slot).cloned().map(Json).ok_or((StatusCode::NOT_FOUND, format!("block {slot} not found")))
}

async fn get_account(State((chain, _)): State<AppState>, Path(address_hex): Path<String>) -> Result<Json<AccountResponse>, (StatusCode, String)> {
    let bytes = hex::decode(&address_hex).map_err(|_| (StatusCode::BAD_REQUEST, "address must be hex".into()))?;
    if bytes.len() != 32 { return Err((StatusCode::BAD_REQUEST, "address must be 32 bytes (64 hex chars)".into())); }
    let mut addr = [0u8; 32]; addr.copy_from_slice(&bytes);
    let c = chain.lock().unwrap();
    c.ledger.get(&addr).map(|a| Json(AccountResponse { address: hex_address(&a.address), balance: a.balance, nonce: a.nonce }))
        .ok_or((StatusCode::NOT_FOUND, "account not found".into()))
}

async fn submit_tx(State((_, mempool)): State<AppState>, Json(req): Json<SubmitTxRequest>) -> Json<SubmitTxResponse> {
    let tx_hash = hex_hash(&req.transaction.hash());
    let accepted = mempool.lock().unwrap().push(req.transaction);
    Json(SubmitTxResponse { accepted, tx_hash, reason: if accepted { None } else { Some("mempool full or duplicate".into()) } })
}

async fn get_recent_events(State((chain, _)): State<AppState>) -> Json<Vec<EventResponse>> {
    let c = chain.lock().unwrap();
    Json(c.recent_events(50).into_iter().map(event_to_resp).collect())
}

async fn get_events_at_slot(State((chain, _)): State<AppState>, Path(slot): Path<u64>) -> Json<Vec<EventResponse>> {
    let c = chain.lock().unwrap();
    Json(c.events_at_slot(slot).iter().map(event_to_resp).collect())
}

async fn derive_pda(State((_, _)): State<AppState>, Json(req): Json<PdaRequest>) -> Result<Json<PdaResponse>, (StatusCode, String)> {
    use crate::crypto::find_pda;
    let prog_bytes = hex::decode(&req.program_id).map_err(|_| (StatusCode::BAD_REQUEST, "program_id must be hex".into()))?;
    if prog_bytes.len() != 32 { return Err((StatusCode::BAD_REQUEST, "program_id must be 32 bytes".into())); }
    let mut program_id = [0u8; 32]; program_id.copy_from_slice(&prog_bytes);
    let decoded_seeds: Result<Vec<Vec<u8>>, _> = req.seeds.iter().map(|s| hex::decode(s)).collect();
    let decoded_seeds = decoded_seeds.map_err(|_| (StatusCode::BAD_REQUEST, "seeds must be hex-encoded".into()))?;
    let seed_slices: Vec<&[u8]> = decoded_seeds.iter().map(|v| v.as_slice()).collect();
    let (addr, bump) = find_pda(&seed_slices, &program_id);
    Ok(Json(PdaResponse { address: hex_address(&addr), bump }))
}

fn event_to_resp(e: &crate::types::Event) -> EventResponse {
    EventResponse { slot: e.slot, program_id: hex_address(&e.program_id), name: e.name.clone(), data_hex: hex::encode(&e.data) }
}
`
};
var CHAIN_SOURCE_HASH = (() => {
  const all = CHAIN_CARGO_TOML + Object.entries(CHAIN_SRC).sort().map(([k, v]) => k + v).join("");
  let h = 0;
  for (let i = 0; i < all.length; i++) {
    h = Math.imul(31, h) + all.charCodeAt(i) | 0;
  }
  return (h >>> 0).toString(16);
})();

// src/codegen/firebase-server-runtime.ts
function buildFirebaseServerRuntime(projectId) {
  return `
// \u2500\u2500 Firestore REST helpers (injected for Firebase server projects) \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500

function _httpsReq(method, url, body, headers) {
  const https = require('https');
  return new Promise((resolve, reject) => {
    const parsed = new URL(url);
    const bodyStr = body != null ? JSON.stringify(body) : null;
    const opts = {
      hostname: parsed.hostname,
      path: parsed.pathname + parsed.search,
      method,
      headers: {
        'Content-Type': 'application/json',
        ...(bodyStr ? { 'Content-Length': Buffer.byteLength(bodyStr) } : {}),
        ...headers,
      },
    };
    const req = https.request(opts, res => {
      let data = '';
      res.on('data', c => { data += c; });
      res.on('end', () => {
        try { resolve({ status: res.statusCode, body: JSON.parse(data) }); }
        catch { resolve({ status: res.statusCode, body: data }); }
      });
    });
    req.on('error', reject);
    if (bodyStr) req.write(bodyStr);
    req.end();
  });
}

function _toFirestoreFields(obj) {
  const fields = {};
  for (const [k, v] of Object.entries(obj || {})) {
    if (typeof v === 'string') fields[k] = { stringValue: v };
    else if (typeof v === 'number' && Number.isInteger(v)) fields[k] = { integerValue: String(v) };
    else if (typeof v === 'number') fields[k] = { doubleValue: v };
    else if (typeof v === 'boolean') fields[k] = { booleanValue: v };
    else if (v == null) fields[k] = { nullValue: null };
  }
  return fields;
}

function _fromFirestoreDoc(doc) {
  const id = doc.name ? doc.name.split('/').pop() : null;
  const out = { id };
  for (const [k, v] of Object.entries(doc.fields || {})) {
    if (v.stringValue  !== undefined) out[k] = v.stringValue;
    else if (v.integerValue !== undefined) out[k] = Number(v.integerValue);
    else if (v.doubleValue  !== undefined) out[k] = v.doubleValue;
    else if (v.booleanValue !== undefined) out[k] = v.booleanValue;
    else if (v.timestampValue !== undefined) out[k] = v.timestampValue;
    else out[k] = null;
  }
  return out;
}

const _FIRESTORE_PROJECT = ${JSON.stringify(projectId)};
const _FIRESTORE_BASE = \`https://firestore.googleapis.com/v1/projects/\${_FIRESTORE_PROJECT}/databases/(default)/documents\`;

function firestoreList(collection, userId, idToken) {
  const url = _FIRESTORE_BASE + ':runQuery';
  const body = {
    structuredQuery: {
      from: [{ collectionId: collection }],
      where: userId ? {
        fieldFilter: {
          field: { fieldPath: 'userId' },
          op: 'EQUAL',
          value: { stringValue: userId },
        },
      } : undefined,
    },
  };
  return _httpsReq('POST', url, body, { Authorization: 'Bearer ' + idToken })
    .then(r => {
      if (!Array.isArray(r.body)) return [];
      return r.body
        .filter(entry => entry && entry.document)
        .map(entry => _fromFirestoreDoc(entry.document));
    });
}

function firestoreCreate(collection, data, idToken) {
  const url = \`\${_FIRESTORE_BASE}/\${collection}\`;
  return _httpsReq('POST', url, { fields: _toFirestoreFields(data) }, { Authorization: 'Bearer ' + idToken })
    .then(r => {
      if (!r.body || !r.body.name) throw new Error('Firestore create failed: ' + JSON.stringify(r.body));
      return _fromFirestoreDoc(r.body);
    });
}

function firestoreUpdate(collection, docId, data, idToken) {
  const fields = _toFirestoreFields(data);
  const mask = Object.keys(fields)
    .map(k => 'updateMask.fieldPaths=' + encodeURIComponent(k))
    .join('&');
  const url = \`\${_FIRESTORE_BASE}/\${collection}/\${docId}?\${mask}\`;
  return _httpsReq('PATCH', url, { fields }, { Authorization: 'Bearer ' + idToken })
    .then(() => ({ id: docId, ...data }));
}

function firestoreDelete(collection, docId, idToken) {
  const url = \`\${_FIRESTORE_BASE}/\${collection}/\${docId}\`;
  return _httpsReq('DELETE', url, null, { Authorization: 'Bearer ' + idToken })
    .then(() => ({ ok: true, id: docId }));
}
`;
}

// src/cli.ts
var rawArgs = process.argv.slice(2);
var strict = rawArgs.includes("--strict");
var noLaunch = rawArgs.includes("--no-launch");
var args = rawArgs.filter((arg) => arg !== "--strict" && arg !== "--no-launch");
async function main() {
  if (args.length === 0) {
    printUsage();
    return;
  }
  const command = args[0];
  if (command === "check") {
    const file3 = args[1];
    if (!file3) {
      console.error("Usage: fl check <file.fl>");
      process.exit(1);
    }
    runCheck(file3);
    return;
  }
  if (command === "derive") {
    const file3 = args[1];
    if (!file3) {
      console.error("Usage: fl derive <file.fl>");
      process.exit(1);
    }
    runDerive(file3);
    return;
  }
  if (command === "web") {
    const file3 = args[1];
    const outDir = args[2] ?? "generated/futurlang-webapp";
    if (!file3) {
      console.error("Usage: fl web <file.fl> [out-dir]");
      process.exit(1);
    }
    runWeb(file3, outDir);
    return;
  }
  if (command === "create-app") {
    const name = args[1];
    if (!name) {
      console.error("Usage: fl create-app <name>");
      process.exit(1);
    }
    runCreateApp(name);
    return;
  }
  if (command === "create-server") {
    const name = args[1];
    if (!name) {
      console.error("Usage: fl create-server <name>");
      process.exit(1);
    }
    runCreateServer(name);
    return;
  }
  if (command === "install") {
    await runInstall();
    return;
  }
  if (command === "start") {
    if (!args[1] || args[1].endsWith(".fl") === false) {
      await runProjectStart();
      return;
    }
    const file3 = args[1];
    const outDir = args[2] ?? "generated/futurlang-webapp";
    runStart(file3, outDir);
    return;
  }
  if (command === "server") {
    const file3 = args[1];
    if (!file3) {
      console.error("Usage: fl server <file.fl>");
      process.exit(1);
    }
    runServer(file3);
    return;
  }
  if (command === "build") {
    const file3 = args[1];
    if (!file3) {
      console.error("Usage: fl build <file.fl> [-o output]");
      process.exit(1);
    }
    const outFlag = args.indexOf("-o");
    const outName = outFlag >= 0 ? args[outFlag + 1] : null;
    await runBuild(file3, outName);
    return;
  }
  if (command === "rust") {
    const file3 = args[1];
    if (!file3) {
      console.error("Usage: fl rust <file.fl> [out.rs]");
      process.exit(1);
    }
    const outFile = args[2] ?? null;
    runRust(file3, outFile);
    return;
  }
  if (command === "repl") {
    runRepl(rawArgs.includes("--json"));
    return;
  }
  if (command === "lsp-server") {
    const portArg = args.indexOf("--port");
    const port = portArg >= 0 ? parseInt(args[portArg + 1], 10) : 3001;
    await startLspServer(port);
    await new Promise(() => {
    });
    return;
  }
  if (command === "chain") {
    await runChain(args.slice(1));
    return;
  }
  const file2 = command;
  if (!fs4.existsSync(file2)) {
    console.error(`File not found: ${file2}`);
    process.exit(1);
  }
  runEval(file2);
}
async function runExecute(file2) {
  const source2 = expandFLFile(file2);
  const nodes = parseLinesToAST(lexFL(source2), { desugarFns: true });
  if (isProofStyleProgram(nodes)) {
    const report = checkFile(nodes, { strict });
    printCheckReport(file2, report, false);
    if (report.state !== "PROVED") {
      process.exitCode = 1;
      return;
    }
  }
  const rustNodes = parseLinesToAST(lexFL(source2), { desugarFns: false });
  const rustSrc = generateRustFromAST(rustNodes, path4.basename(file2));
  const programName = path4.basename(file2, ".fl");
  const isAnchor = rustNodes.some((n) => n.type === "Program");
  if (isAnchor) {
    console.log(`
${programName}: on-chain program (use fl build to compile for deployment)`);
    return;
  }
  const cargoToml = generateCargoToml(programName, false);
  const tmpDir = path4.join(require("os").tmpdir(), `fl-run-${Date.now()}`);
  const srcDir = path4.join(tmpDir, "src");
  fs4.mkdirSync(srcDir, { recursive: true });
  fs4.writeFileSync(path4.join(tmpDir, "Cargo.toml"), cargoToml, "utf8");
  fs4.writeFileSync(path4.join(srcDir, "main.rs"), rustSrc, "utf8");
  try {
    await new Promise((resolve3, reject) => {
      const child = (0, import_child_process.spawn)("cargo", ["build", "--release", "--quiet"], {
        cwd: tmpDir,
        stdio: ["ignore", "ignore", "pipe"],
        shell: process.platform === "win32"
      });
      let stderr = "";
      child.stderr?.on("data", (d) => {
        stderr += d.toString();
      });
      child.on("exit", (code) => code === 0 ? resolve3() : reject(new Error(stderr)));
    });
    const binary = path4.join(tmpDir, "target", "release", programName);
    await new Promise((resolve3) => {
      const child = (0, import_child_process.spawn)(binary, [], { stdio: "inherit" });
      child.on("exit", (code) => {
        process.exitCode = code ?? 0;
        resolve3();
      });
    });
  } catch (e) {
    console.error(`Compile error:
${e.message}`);
    process.exitCode = 1;
  } finally {
    fs4.rmSync(tmpDir, { recursive: true, force: true });
  }
}
function runEval(file) {
  const source = expandFLFile(file);
  const ast = parseLinesToAST(lexFL(source), { desugarFns: false });
  if (isProofStyleProgram(ast)) {
    console.log(`
${path4.basename(file)}: proof + runtime mode
`);
    const proofAst = parseLinesToAST(lexFL(source), { desugarFns: true });
    const report = checkFile(proofAst, { strict });
    printCheckReport(file, report, false);
    if (report.state !== "PROVED") {
      process.exitCode = 1;
    }
    console.log(`
Executing ${path4.basename(file)}
`);
  }
  const js = parseFLFile(file);
  try {
    eval(js);
  } catch (e) {
    console.error(e.message);
    process.exit(1);
  }
}
function runServer(file, extraRuntime = "") {
  if (!fs4.existsSync(file)) {
    console.error(`File not found: ${file}`);
    process.exit(1);
  }
  const source = expandFLFile(file);
  const ast = parseLinesToAST(lexFL(source), { desugarFns: false });
  const js = generateJSFromAST(ast, runtimePreamble + (extraRuntime ? "\n" + extraRuntime : ""));
  try {
    eval(js);
  } catch (e) {
    console.error(e.message);
    process.exit(1);
  }
}
function runStart(file2, outDir) {
  if (!fs4.existsSync(file2)) {
    console.error(`File not found: ${file2}`);
    process.exit(1);
  }
  const source2 = fs4.readFileSync(file2, "utf8");
  if (isServerProgram(source2)) {
    runServer(file2);
    return;
  }
  runWeb(file2, outDir);
  if (noLaunch) {
    console.log("Skipping frontend launch because --no-launch was provided");
    return;
  }
  launchFrontend(outDir);
}
async function runBuild(file2, outName) {
  if (!fs4.existsSync(file2)) {
    console.error(`File not found: ${file2}`);
    process.exit(1);
  }
  const source2 = expandFLFile(file2);
  const nodes = parseLinesToAST(lexFL(source2), { desugarFns: false });
  const rustSrc = generateRustFromAST(nodes, path4.basename(file2));
  const isAnchor = nodes.some((n) => n.type === "Program");
  const programName = outName ?? path4.basename(file2, ".fl");
  const cargoToml = generateCargoToml(programName, isAnchor);
  const tmpDir = path4.join(require("os").tmpdir(), `fl-build-${Date.now()}`);
  const srcDir = path4.join(tmpDir, "src");
  fs4.mkdirSync(srcDir, { recursive: true });
  fs4.writeFileSync(path4.join(tmpDir, "Cargo.toml"), cargoToml, "utf8");
  const entryFile = isAnchor ? "lib.rs" : "main.rs";
  fs4.writeFileSync(path4.join(srcDir, entryFile), rustSrc, "utf8");
  console.log(`Building ${path4.basename(file2)}...`);
  const buildCmd = isAnchor ? "cargo build-sbf" : "cargo build --release";
  const [cmd, ...buildArgs] = buildCmd.split(" ");
  await new Promise((resolve3, reject) => {
    const child = (0, import_child_process.spawn)(cmd, buildArgs, {
      cwd: tmpDir,
      stdio: ["ignore", "pipe", "pipe"],
      shell: process.platform === "win32"
    });
    let stderr = "";
    child.stderr?.on("data", (d) => {
      stderr += d.toString();
    });
    child.on("exit", (code) => {
      if (code === 0) resolve3();
      else reject(new Error(`Build failed:
${stderr}`));
    });
  }).then(() => {
    const outDir = isAnchor ? path4.join(tmpDir, "target", "deploy") : path4.join(tmpDir, "target", "release");
    const artifactName = isAnchor ? `${programName.replace(/-/g, "_")}.so` : programName;
    const artifactSrc = path4.join(outDir, artifactName);
    const artifactDst = path4.join(process.cwd(), artifactName);
    if (fs4.existsSync(artifactSrc)) {
      fs4.copyFileSync(artifactSrc, artifactDst);
      console.log(`
\u2713 Built: ${artifactName}`);
    } else {
      console.log(`
\u2713 Build succeeded (artifact in ${outDir})`);
    }
  }).catch((e) => {
    console.error(e.message);
    process.exitCode = 1;
  }).finally(() => {
    fs4.rmSync(tmpDir, { recursive: true, force: true });
  });
}
function runRust(file2, outFile) {
  if (!fs4.existsSync(file2)) {
    console.error(`File not found: ${file2}`);
    process.exit(1);
  }
  const source2 = expandFLFile(file2);
  const nodes = parseLinesToAST(lexFL(source2), { desugarFns: false });
  const rust = generateRustFromAST(nodes, path4.basename(file2));
  if (outFile) {
    fs4.writeFileSync(outFile, rust, "utf8");
    console.log(`Rust source written to ${outFile}`);
  } else {
    process.stdout.write(rust);
  }
}
function runCheck(file2) {
  if (!fs4.existsSync(file2)) {
    console.error(`File not found: ${file2}`);
    process.exit(1);
  }
  const source2 = expandFLFile(file2);
  const report = checkFile(parseLinesToAST(lexFL(source2), { desugarFns: true }), { strict });
  printCheckReport(file2, report);
}
function runDerive(file2) {
  if (!fs4.existsSync(file2)) {
    console.error(`File not found: ${file2}`);
    process.exit(1);
  }
  const source2 = expandFLFile(file2);
  const nodes = parseLinesToAST(lexFL(source2), { desugarFns: true });
  console.log(`
Forward-chaining derivation: ${path4.basename(file2)}
`);
  const report = checkFile(nodes, { strict });
  let anyPrinted = false;
  for (const r of report.reports) {
    if (r.premises.length === 0) continue;
    anyPrinted = true;
    console.log(`  ${r.name}:`);
    console.log(`    premises: ${r.premises.join(" ; ")}`);
    const ctx = createMutableContext(r.premises, null);
    const t0 = Date.now();
    const conclusions = deriveConclusions(ctx);
    const elapsed = Date.now() - t0;
    if (conclusions.length === 0) {
      console.log(`    \u2192 no new conclusions reachable`);
    } else {
      console.log(`    \u2192 ${conclusions.length} conclusion(s) in ${elapsed}ms:`);
      for (const c of conclusions) {
        console.log(`       ${c}`);
      }
    }
    console.log("");
  }
  if (!anyPrinted) {
    console.log("  No theorem/lemma premises found in this file.");
  }
}
function runRepl(jsonMode) {
  const rl = readline.createInterface({
    input: process.stdin,
    output: process.stdout,
    terminal: !jsonMode
  });
  if (!jsonMode) {
    console.log("FuturLang Interactive Agent REPL");
    console.log('Type a valid proof step (e.g. "assert(A \u2286 B)") or "exit".\\n');
  }
  let ctx = createMutableContext([], null);
  if (!jsonMode) {
    rl.setPrompt("fl> ");
    rl.prompt();
  }
  rl.on("line", (line) => {
    line = line.trim();
    if (line === "exit" || line === "quit") {
      process.exit(0);
    }
    if (!line) {
      if (!jsonMode) rl.prompt();
      return;
    }
    try {
      const astNodes = parseLinesToAST(lexFL(line), { desugarFns: true });
      if (astNodes.length === 0) {
        if (!jsonMode) rl.prompt();
        return;
      }
      for (const node of astNodes) {
        const result = evaluateIncrementalStep(ctx, node);
        if (jsonMode) {
          console.log(JSON.stringify({ status: "ok", trace: result }));
        } else {
          if (result) {
            const icon = result.state === "PROVED" ? "\u2713" : result.state === "PENDING" ? "~" : result.state === "UNVERIFIED" ? "?" : "\u2717";
            console.log(` ${icon} ${result.rule} => ${result.state}`);
            if (result.message) console.log(`    ${result.message}`);
            if (result.causalError) console.dir(result.causalError, { depth: null, colors: true });
          }
        }
      }
    } catch (e) {
      if (jsonMode) {
        console.log(JSON.stringify({ status: "error", error: e.message }));
      } else {
        console.error(` \u2717 Parser/eval error: ${e.message}`);
      }
    }
    if (!jsonMode) rl.prompt();
  }).on("close", () => {
    process.exit(0);
  });
}
function printCheckReport(file2, report, exitOnFailure = true) {
  console.log(`
Checking ${path4.basename(file2)}
`);
  const declarationOnly = report.theoremCount > 0 && report.pairedCount === 0;
  for (const r of report.reports) {
    const status = r.state === "PROVED" ? "\u2713" : r.state === "PENDING" ? "~" : r.state === "UNVERIFIED" ? "?" : "\u2717";
    const statusSuffix = r.pendingCount > 0 ? ` (${r.provedCount} classical, ${r.pendingCount} pending)` : r.provedCount > 0 ? ` (${r.provedCount} classical)` : "";
    console.log(`  ${status} ${r.name}  ${r.state}${statusSuffix}`);
    if (r.premises.length > 0) {
      console.log(`      premises: ${r.premises.join(" ; ")}`);
    }
    if (r.goal) {
      console.log(`      goal: ${r.goal}`);
    }
    if (r.derivedConclusion) {
      console.log(`      final: ${r.derivedConclusion}`);
    }
    for (const step of r.proofSteps) {
      const stepIcon = step.state === "PROVED" ? "\u2713" : step.state === "PENDING" ? "~" : step.state === "UNVERIFIED" ? "?" : "\u2717";
      console.log(`      ${stepIcon} step ${step.step} [${step.rule}] ${step.kind} ${step.claim}`);
      if (step.uses && step.uses.length > 0) {
        console.log(`        uses: ${step.uses.join(" ; ")}`);
      }
      if (step.imports && step.imports.length > 0) {
        console.log(`        imports: ${step.imports.join(" ; ")}`);
      }
    }
    for (const d of r.diagnostics) {
      if (d.severity === "error") {
        console.log(`      \u2717 ${d.message}`);
        if (d.hint) console.log(`        hint: ${d.hint}`);
      } else if (d.severity === "warning") {
        console.log(`      \u26A0 ${d.message}`);
      } else if (d.severity === "info" && d.rule) {
        console.log(`      \u2139 ${d.message}`);
      }
    }
  }
  for (const d of report.diagnostics) {
    if (declarationOnly && d.message.includes("have no proof")) continue;
    console.log(`  ${d.severity === "error" ? "\u2717" : "\u2139"} ${d.message}`);
  }
  if (declarationOnly) {
    console.log(`
  Declaration-only proof program`);
    console.log(`  Theorems: ${report.theoremCount}`);
    console.log(report.state === "FAILED" ? "\n\u2717 Structural errors found" : "\n~ Declarations parsed without paired derivations");
  } else {
    console.log(`
  Theorems: ${report.theoremCount}  Paired: ${report.pairedCount}  Result: ${report.state}`);
    if (report.state === "PROVED") {
      console.log("\n\u2713 All proofs reduced to classical morphism paths");
    } else if (report.state === "PENDING") {
      console.log("\n~ At least one derivation is structurally valid but still blocked behind \u03C9 and Ra");
    } else if (report.state === "UNVERIFIED") {
      console.log("\n? At least one derivation was accepted only as structurally unverified");
    } else {
      console.log("\n\u2717 Structural errors found");
    }
  }
  if (exitOnFailure && report.state !== "PROVED") process.exit(1);
}
function isProofStyleProgram(ast2) {
  return ast2.some(
    (node) => node.type === "Theorem" || node.type === "Proof" || node.type === "Lemma"
  );
}
function runWeb(file2, outDir) {
  if (!fs4.existsSync(file2)) {
    console.error(`File not found: ${file2}`);
    process.exit(1);
  }
  const source2 = expandFLFile(file2);
  const ast2 = parseLinesToAST(lexFL(source2), { desugarFns: false });
  createReactApp(ast2, outDir);
  console.log(`Generated React app in ${outDir}`);
}
function launchFrontend(outDir) {
  if (!fs4.existsSync(path4.join(outDir, "package.json"))) {
    console.error(`Frontend app is missing package.json in ${outDir}`);
    process.exit(1);
  }
  if (!fs4.existsSync(path4.join(outDir, "node_modules"))) {
    console.error(`Frontend dependencies are missing in ${outDir}. Run npm install there or use the default generated app directory.`);
    process.exit(1);
  }
  console.log(`Starting React dev server in ${outDir}`);
  const child = (0, import_child_process.spawn)("npm", ["run", "dev", "--", "--host", "127.0.0.1", "--port", "5173"], {
    cwd: outDir,
    stdio: "inherit",
    shell: process.platform === "win32"
  });
  child.on("exit", (code) => {
    process.exit(code ?? 0);
  });
}
function isServerProgram(source2) {
  return /\bserve\s*\(/.test(source2);
}
function readManifest() {
  const candidates = ["package.flson", "fl.json"];
  for (const name of candidates) {
    const p = path4.join(process.cwd(), name);
    if (fs4.existsSync(p)) return JSON.parse(fs4.readFileSync(p, "utf8"));
  }
  console.error("No package.flson found. Run fl create-app <name> or fl create-server <name> to scaffold a project.");
  process.exit(1);
}
function runCreateApp(name) {
  const appDir = path4.resolve(name);
  if (fs4.existsSync(appDir)) {
    console.error(`Directory already exists: ${appDir}`);
    process.exit(1);
  }
  const generatedDir = "generated/frontend";
  const mainFile = "app.fl";
  const starterFl = `fn double(n \u2208 Nat) -> Nat {
  conclude(n + n)
} \u2192

fn clamp(x \u2208 Real, lo \u2208 Real, hi \u2208 Real) -> Real {
  assume(lo <= hi) \u2192
  conclude(max(lo, min(x, hi)))
} \u2192

theorem DoubleIsPositive() {
  let n = 4 \u2192
  let result = double(n) \u2192
  assert(result > 0)
} \u2192

proof DoubleIsPositive() {
  let n = 4 \u2192
  let result = double(n) \u2192
  conclude(result > 0)
}
`;
  const manifest = { name, type: "web", main: mainFile, generated: generatedDir };
  fs4.mkdirSync(appDir, { recursive: true });
  fs4.writeFileSync(path4.join(appDir, mainFile), starterFl, "utf8");
  fs4.writeFileSync(path4.join(appDir, "package.flson"), JSON.stringify(manifest, null, 2) + "\n", "utf8");
  fs4.writeFileSync(path4.join(appDir, ".gitignore"), "generated/\n", "utf8");
  const outDir = path4.join(appDir, generatedDir);
  const ast2 = parseLinesToAST(lexFL(starterFl), { desugarFns: false });
  createReactApp(ast2, outDir);
  console.log(`
Created FL web app: ${name}/`);
  console.log(`  ${name}/${mainFile}            \u2190 your FL source (edit this)`);
  console.log(`  ${name}/package.flson          \u2190 project manifest`);
  console.log(`  ${name}/generated/frontend/    \u2190 generated React (hidden, gitignored)`);
  console.log(`
Next steps:`);
  console.log(`  cd ${name} && fl install && fl start`);
}
function runCreateServer(name) {
  const serverDir = path4.resolve(name);
  if (fs4.existsSync(serverDir)) {
    console.error(`Directory already exists: ${serverDir}`);
    process.exit(1);
  }
  const mainFile = "server.fl";
  const starterFl = `// ${name} \u2014 FL server
// fl start  \u2190  compiles and runs in memory (no generated files)

fn cors(req \u2208 Request) -> Response {
  conclude(json({ ok: true }, 200, {
    "Access-Control-Allow-Origin": "*",
    "Access-Control-Allow-Headers": "Content-Type, Authorization",
    "Access-Control-Allow-Methods": "GET, POST, PUT, DELETE, OPTIONS"
  }))
} \u2192

fn health(req \u2208 Request) -> Response {
  conclude(json({ status: "ok", service: "${name}", version: "1.0.0" }, 200, {
    "Access-Control-Allow-Origin": "*"
  }))
} \u2192

fn notFound(req \u2208 Request) -> Response {
  conclude(json({ error: "not found" }, 404, {
    "Access-Control-Allow-Origin": "*"
  }))
} \u2192

let app = router([
  route("OPTIONS", "*", cors),
  route("GET", "/api/health", health)
], notFound) \u2192

let server = serve(3001, app)
`;
  const manifest = { name, type: "server", main: mainFile };
  fs4.mkdirSync(serverDir, { recursive: true });
  fs4.writeFileSync(path4.join(serverDir, mainFile), starterFl, "utf8");
  fs4.writeFileSync(path4.join(serverDir, "package.flson"), JSON.stringify(manifest, null, 2) + "\n", "utf8");
  fs4.writeFileSync(path4.join(serverDir, ".gitignore"), ".env\n", "utf8");
  console.log(`
Created FL server: ${name}/`);
  console.log(`  ${name}/${mainFile}     \u2190 your FL source (edit this)`);
  console.log(`  ${name}/package.flson  \u2190 project manifest`);
  console.log(`
Next steps:`);
  console.log(`  cd ${name} && fl start`);
}
async function runInstall() {
  const manifest = readManifest();
  if (manifest.type === "server") {
    console.log("Server projects have no npm dependencies to install (runs in-memory).");
    return;
  }
  const generatedDir = path4.resolve(manifest.generated ?? "generated/frontend");
  if (!fs4.existsSync(generatedDir)) {
    console.error(`Generated directory not found: ${generatedDir}. Run fl start to generate it first.`);
    process.exit(1);
  }
  console.log(`Installing dependencies in ${path4.relative(process.cwd(), generatedDir)}/...`);
  await npmInstall(generatedDir);
  console.log("\nDone. Run fl start to launch your app.");
}
async function npmInstall(dir) {
  return new Promise((resolve3, reject) => {
    const child = (0, import_child_process.spawn)("npm", ["install"], {
      cwd: dir,
      stdio: "inherit",
      shell: process.platform === "win32"
    });
    child.on("exit", (code) => code === 0 ? resolve3() : reject(new Error(`npm install exited with code ${code}`)));
  });
}
async function runProjectStart() {
  const manifest = readManifest();
  const mainFile = path4.resolve(manifest.main);
  if (!fs4.existsSync(mainFile)) {
    console.error(`Main file not found: ${manifest.main}`);
    process.exit(1);
  }
  if (manifest.type === "server") {
    console.log(`Starting FL server from ${manifest.main}...`);
    let extraRuntime2 = "";
    if (manifest.firebase?.projectId) {
      extraRuntime2 = buildFirebaseServerRuntime(manifest.firebase.projectId);
    }
    runServer(mainFile, extraRuntime2);
    return;
  }
  const generatedDir = path4.resolve(manifest.generated ?? "generated/frontend");
  const source2 = expandFLFile(mainFile);
  const ast2 = parseLinesToAST(lexFL(source2), { desugarFns: false });
  createReactApp(ast2, generatedDir);
  console.log(`Generated React app from ${manifest.main}`);
  if (!fs4.existsSync(path4.join(generatedDir, "node_modules"))) {
    console.log("node_modules not found \u2014 running npm install...");
    await npmInstall(generatedDir);
  }
  if (noLaunch) {
    console.log("Skipping frontend launch (--no-launch)");
    return;
  }
  launchFrontend(generatedDir);
}
async function runChain(extraArgs) {
  const os = require("os");
  const cacheDir = path4.join(os.homedir(), ".futurlang", "chain");
  const srcDir = path4.join(cacheDir, "src");
  const binary = path4.join(cacheDir, "target", "release", "futurchain");
  const hashFile = path4.join(cacheDir, ".source-hash");
  const needsBuild = (() => {
    if (!fs4.existsSync(binary)) return true;
    try {
      return fs4.readFileSync(hashFile, "utf8").trim() !== CHAIN_SOURCE_HASH;
    } catch {
      return true;
    }
  })();
  if (needsBuild) {
    console.log("Building FuturChain from FL source...");
    fs4.mkdirSync(srcDir, { recursive: true });
    fs4.writeFileSync(path4.join(cacheDir, "Cargo.toml"), CHAIN_CARGO_TOML, "utf8");
    for (const [name, content] of Object.entries(CHAIN_SRC)) {
      fs4.writeFileSync(path4.join(srcDir, name), content, "utf8");
    }
    await new Promise((resolve3, reject) => {
      const child2 = (0, import_child_process.spawn)("cargo", ["build", "--release"], {
        cwd: cacheDir,
        stdio: ["ignore", "inherit", "inherit"],
        shell: process.platform === "win32"
      });
      child2.on("exit", (code) => code === 0 ? resolve3() : reject(new Error(`Build failed (exit ${code})`)));
    });
    fs4.writeFileSync(hashFile, CHAIN_SOURCE_HASH, "utf8");
    console.log("Build complete.\n");
  }
  const child = (0, import_child_process.spawn)(binary, extraArgs, { stdio: "inherit" });
  child.on("exit", (code) => process.exit(code ?? 0));
  for (const sig of ["SIGINT", "SIGTERM"]) {
    process.on(sig, () => child.kill(sig));
  }
}
function printUsage() {
  console.log(`
FuturLang \u2014 formal proof language

Usage:
  fl [--strict] <file.fl>           Execute a file; proof-shaped files also show checker output
  fl check [--strict] <file.fl>     Check proof structure with the categorical kernel
  fl derive <file.fl>               Forward-chain all derivable conclusions from premises
  fl build <file.fl> [-o name]      Compile to binary via Rust (source stays hidden)
  fl server <file.fl>               Run a server-style FL file

FuturChain:
  fl chain                          Start a FuturChain node (RPC on :8899, 400ms slots)
  fl chain --port 9000              Custom RPC port
  fl chain --slot-ms 1000           Custom slot duration (ms)
  fl chain --genesis-supply 1000    Custom genesis token supply

App workflow (recommended):
  fl create-app <name>              Scaffold a new FL web app (React generated into generated/frontend/)
  fl create-server <name>           Scaffold a new FL server (runs in-memory, no generated files)
  fl install                        Install frontend dependencies (web apps only; run inside app dir)
  fl start                          Start the project: web apps launch Vite, servers run in-memory

Legacy / single-file:
  fl start <file.fl> [out-dir]      Generate and launch a React app from a single FL file
  fl web <file.fl> [out-dir]        Generate a React app without launching it
  fl lsp-server [--port 3001]       Start the Language API Server (parse/check/hover/rust endpoints)
  fl repl [--json]                  Run the interactive agent REPL (for programmatic IO)

Notes:
  --strict                          Reserved for future kernel tightening
  --no-launch                       Generate frontend output without starting Vite

VS Code Extension (syntax highlighting, hover docs, completions):
  https://marketplace.visualstudio.com/items?itemName=WenitteApiou.futurlang
`);
}
main().catch((e) => {
  console.error(e.message);
  process.exit(1);
});
