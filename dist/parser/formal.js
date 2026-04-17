"use strict";
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
exports.parseFL = parseFL;
exports.parseFLFile = parseFLFile;
exports.expandFLFile = expandFLFile;
// src/parser/formal.ts
const lexer_1 = require("./lexer");
const parser_1 = require("./parser");
const codegen_1 = require("../codegen");
const runtime_1 = require("../codegen/runtime");
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
function parseFL(text) {
    const lines = (0, lexer_1.lexFL)(text);
    const ast = (0, parser_1.parseLinesToAST)(lines, { desugarFns: false });
    return (0, codegen_1.generateJSFromAST)(ast, runtime_1.runtimePreamble);
}
function parseFLFile(filePath) {
    const expanded = expandImports(filePath, new Set());
    return parseFL(expanded);
}
function expandFLFile(filePath) {
    return expandImports(filePath, new Set());
}
/**
 * Find the project root by walking up from `start` until we find a directory
 * that contains package.json, or return null if not found.
 */
function findProjectRoot(start) {
    let dir = path.resolve(start);
    while (true) {
        if (fs.existsSync(path.join(dir, 'package.json')))
            return dir;
        const parent = path.dirname(dir);
        if (parent === dir)
            return null;
        dir = parent;
    }
}
/**
 * Resolve a bare module name like "math" or "sets-basic" to a lib/*.fl path.
 * Searches lib/ relative to the project root, then relative to the importing file.
 */
function resolveStdlib(name, fromDir) {
    const candidates = [];
    // Walk up to project root and check lib/
    const root = findProjectRoot(fromDir);
    if (root)
        candidates.push(path.join(root, 'lib', `${name}.fl`));
    // Also check lib/ relative to the file (covers nested projects)
    for (let d = fromDir;; d = path.dirname(d)) {
        candidates.push(path.join(d, 'lib', `${name}.fl`));
        if (path.dirname(d) === d)
            break;
    }
    for (const c of candidates) {
        if (fs.existsSync(c))
            return c;
    }
    return null;
}
function expandImports(filePath, seen) {
    const absolute = path.resolve(filePath);
    if (seen.has(absolute))
        return '';
    seen.add(absolute);
    const source = fs.readFileSync(absolute, 'utf8');
    const dir = path.dirname(absolute);
    const chunks = [];
    for (const line of source.replace(/\r\n/g, '\n').split('\n')) {
        // Quoted path: import "./foo.fl" or import "../lib/math.fl"
        const quotedMatch = line.trim().match(/^import\s+["'](.+?\.fl)["']\s*;?\s*$/);
        if (quotedMatch) {
            const target = path.resolve(dir, quotedMatch[1]);
            const imported = expandImports(target, seen).trimEnd();
            if (imported.length > 0)
                chunks.push(ensureTrailingConnective(imported));
            continue;
        }
        // Bare name: import math  /  import sets-basic  /  import "math"
        const bareMatch = line.trim().match(/^import\s+["']?([A-Za-z][A-Za-z0-9_-]*)["']?\s*;?\s*$/);
        if (bareMatch) {
            const resolved = resolveStdlib(bareMatch[1], dir);
            if (resolved) {
                const imported = expandImports(resolved, seen).trimEnd();
                if (imported.length > 0)
                    chunks.push(ensureTrailingConnective(imported));
            }
            else {
                // Leave the line as-is so the parser can emit a useful error
                chunks.push(line);
            }
            continue;
        }
        chunks.push(line);
    }
    return chunks.join('\n');
}
function ensureTrailingConnective(source) {
    const lines = source.split('\n');
    for (let index = lines.length - 1; index >= 0; index--) {
        const trimmed = lines[index].trim();
        if (!trimmed)
            continue;
        if (/(→|∧|↔|->|&&|<->)\s*$/.test(trimmed))
            return source;
        // Use ∧ (independent) as the default: imported library blocks are always
        // independent of whatever follows them in the importing file.
        lines[index] = `${lines[index]} ∧`;
        return lines.join('\n');
    }
    return source;
}
