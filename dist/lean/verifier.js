"use strict";
// src/lean/verifier.ts
//
// Runs a .fl file through the Lean 4 backend and returns structured results.
// The .lean file is a temporary artefact — never shown to the user.
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
exports.verify = verify;
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const child_process_1 = require("child_process");
const transpiler_1 = require("./transpiler");
const setup_1 = require("./setup");
// ── Main entry point ──────────────────────────────────────────────────────────
function verify(nodes, sourceLines) {
    if (!(0, setup_1.isSetupComplete)()) {
        return {
            success: false,
            theorems: [],
            errors: [{
                    message: 'FuturLang backend not set up. Run: fl setup'
                }]
        };
    }
    // 1. Transpile FL AST → Lean source
    const { source, theoremNames } = (0, transpiler_1.transpileToLean)(nodes);
    // 2. Write to the verification workspace
    fs.writeFileSync(setup_1.VERIFY_FILE, source, 'utf8');
    // 3. Run lean directly on the file (faster than full lake build for single files)
    const env = {
        ...process.env,
        ELAN_HOME: setup_1.ELAN_HOME,
        PATH: `${setup_1.ELAN_HOME}/bin:${process.env.PATH}`,
    };
    const result = (0, child_process_1.spawnSync)(path.join(setup_1.ELAN_HOME, 'bin', 'lean'), ['--json', setup_1.VERIFY_FILE], { cwd: setup_1.PROJECT, env, encoding: 'utf8', maxBuffer: 10 * 1024 * 1024 });
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
    const theorems = theoremNames.map(name => {
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
    fs.writeFileSync(setup_1.VERIFY_FILE, '-- FuturLang verification workspace\nimport Mathlib\n');
    const success = errors.filter(e => !e.message.includes('sorry')).length === 0;
    return { success, theorems, errors };
}
function parseLeanOutput(raw) {
    const diagnostics = [];
    for (const line of raw.split('\n')) {
        const trimmed = line.trim();
        if (!trimmed.startsWith('{'))
            continue;
        try {
            const d = JSON.parse(trimmed);
            if (d.severity && d.message)
                diagnostics.push(d);
        }
        catch { /* skip non-JSON lines */ }
    }
    return diagnostics;
}
// ── Map Lean line numbers back to .fl source lines ───────────────────────────
// The .lean file has a comment like `-- fl:line:N` for key constructs.
// We use the theorem/proof structure to approximate the mapping.
function mapLeanLineToFL(leanLine, leanLines, flLines) {
    if (!leanLine)
        return undefined;
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
            if (count === theoremCount)
                return i + 1;
            count++;
        }
    }
    return undefined;
}
function isErrorInTheorem(name, leanLine, leanLines) {
    // Find where this theorem starts and ends in the lean file
    let start = -1, end = leanLines.length;
    for (let i = 0; i < leanLines.length; i++) {
        if (leanLines[i].startsWith(`theorem ${name}`) ||
            leanLines[i].startsWith(`lemma ${name}`)) {
            start = i;
        }
        else if (start >= 0 && i > start && leanLines[i].startsWith('theorem ')) {
            end = i;
            break;
        }
    }
    return leanLine >= start && leanLine < end;
}
function cleanLeanError(msg) {
    // Strip Lean internals from error messages, keep the meaningful part
    return msg
        .replace(/\n\s*\n/g, '\n')
        .replace(/Try this: /g, '')
        .trim()
        .split('\n')
        .slice(0, 4) // first 4 lines are usually enough
        .join('\n');
}
