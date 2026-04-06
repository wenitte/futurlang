"use strict";
// src/cli.ts — FuturLang command-line interface
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
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const formal_1 = require("./parser/formal");
const lexer_1 = require("./parser/lexer");
const parser_1 = require("./parser/parser");
const checker_1 = require("./checker/checker");
const transpiler_1 = require("./react/transpiler");
const rawArgs = process.argv.slice(2);
const strict = rawArgs.includes('--strict');
const args = rawArgs.filter(arg => arg !== '--strict');
async function main() {
    if (args.length === 0) {
        printUsage();
        return;
    }
    const command = args[0];
    if (command === 'check') {
        const file = args[1];
        if (!file) {
            console.error('Usage: fl check <file.fl>');
            process.exit(1);
        }
        runCheck(file);
        return;
    }
    if (command === 'web') {
        const file = args[1];
        const outDir = args[2] ?? 'generated/futurlang-webapp';
        if (!file) {
            console.error('Usage: fl web <file.fl> [out-dir]');
            process.exit(1);
        }
        runWeb(file, outDir);
        return;
    }
    // Default: evaluate
    const file = command;
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    runEval(file);
}
function runEval(file) {
    const source = fs.readFileSync(file, 'utf8');
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source));
    if (isProofStyleProgram(ast)) {
        console.log(`\n${path.basename(file)}: theorem-prover mode\n`);
        printCheckReport(file, (0, checker_1.checkFile)(ast, { strict }));
        return;
    }
    const js = (0, formal_1.parseFL)(source);
    try {
        eval(js);
    }
    catch (e) {
        console.error(e.message);
        process.exit(1);
    }
}
function runCheck(file) {
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    const source = fs.readFileSync(file, 'utf8');
    const report = (0, checker_1.checkFile)((0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source)), { strict });
    printCheckReport(file, report);
}
function printCheckReport(file, report) {
    console.log(`\nChecking ${path.basename(file)}\n`);
    const declarationOnly = report.theoremCount > 0 && report.pairedCount === 0;
    for (const r of report.reports) {
        const status = r.valid ? (r.unverifiedCount > 0 ? '~' : '✓') : '✗';
        const method = r.method !== 'unknown' ? ` [${r.method}]` : '';
        const statusSuffix = r.unverifiedCount > 0
            ? ` (${r.provedCount} PROVED, ${r.unverifiedCount} UNVERIFIED)`
            : r.provedCount > 0 ? ` (${r.provedCount} PROVED)` : '';
        console.log(`  ${status} ${r.name}${method}  (${r.stepCount} steps, depth ${r.metrics.dependencyDepth})${statusSuffix}`);
        if (r.premises.length > 0) {
            console.log(`      premises: ${r.premises.join(' ; ')}`);
        }
        if (r.goal) {
            console.log(`      goal: ${r.goal}`);
        }
        if (r.derivedConclusion) {
            console.log(`      final: ${r.derivedConclusion}`);
        }
        for (const step of r.proofSteps) {
            const stepIcon = step.valid ? (step.status === 'UNVERIFIED' ? '~' : '✓') : '✗';
            console.log(`      ${stepIcon} step ${step.step} [${step.rule}] ${step.kind} ${step.claim}`);
            if (step.uses && step.uses.length > 0) {
                console.log(`        uses: ${step.uses.join(' ; ')}`);
            }
            if (step.imports && step.imports.length > 0) {
                console.log(`        imports: ${step.imports.join(' ; ')}`);
            }
            if (step.establishesAs) {
                console.log(`        establishes-as: ${step.establishesAs}`);
            }
        }
        for (const d of r.diagnostics) {
            if (d.severity === 'error') {
                console.log(`      ✗ ${d.message}`);
                if (d.hint)
                    console.log(`        hint: ${d.hint}`);
            }
            else if (d.severity === 'warning') {
                console.log(`      ⚠ ${d.message}`);
            }
            else if (d.severity === 'info' && d.rule && d.rule !== 'THEOREM_PROOF') {
                console.log(`      ℹ ${d.message}`);
            }
        }
    }
    for (const d of report.diagnostics) {
        if (declarationOnly && d.message.includes('have no proof'))
            continue;
        console.log(`  ${d.severity === 'error' ? '✗' : 'ℹ'} ${d.message}`);
    }
    if (declarationOnly) {
        console.log(`\n  Declaration-only proof program`);
        console.log(`  Theorems: ${report.theoremCount}`);
        console.log(report.valid ? '\n✓ Declarations parsed cleanly' : '\n✗ Structural errors found');
    }
    else {
        console.log(`\n  Theorems: ${report.theoremCount}  Paired: ${report.pairedCount}  Score: ${report.score}/100`);
        if (report.valid) {
            const hasUnverified = report.reports.some(r => r.unverifiedCount > 0);
            if (hasUnverified) {
                console.log('\n~ Proof structure valid — some steps UNVERIFIED (accepted without derivation chain)');
            }
            else {
                console.log('\n✓ All proofs verified');
            }
        }
        else {
            console.log('\n✗ Structural errors found');
        }
    }
    if (!report.valid)
        process.exit(1);
}
function isProofStyleProgram(ast) {
    return ast.some(node => node.type === 'Theorem' ||
        node.type === 'Proof' ||
        node.type === 'Lemma' ||
        node.type === 'Given' ||
        node.type === 'Assume' ||
        node.type === 'Conclude' ||
        node.type === 'Apply');
}
function runWeb(file, outDir) {
    if (!fs.existsSync(file)) {
        console.error(`File not found: ${file}`);
        process.exit(1);
    }
    const source = fs.readFileSync(file, 'utf8');
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(source));
    (0, transpiler_1.createReactApp)(ast, outDir);
    console.log(`Generated React app in ${outDir}`);
}
function printUsage() {
    console.log(`
FuturLang — formal proof language

Usage:
  fl [--strict] <file.fl>           Auto-runs check mode for proof-shaped files, otherwise evaluates
  fl check [--strict] <file.fl>     Check proof structure (natural deduction, self-contained kernel)
  fl web <file.fl>                  Generate a React app from the program truth chain
`);
}
main().catch(e => { console.error(e.message); process.exit(1); });
