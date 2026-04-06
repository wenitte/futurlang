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
const assert_1 = require("assert");
const fs = __importStar(require("fs"));
const os = __importStar(require("os"));
const path = __importStar(require("path"));
const lexer_1 = require("../parser/lexer");
const expr_1 = require("../parser/expr");
const parser_1 = require("../parser/parser");
const checker_1 = require("../checker/checker");
const formal_1 = require("../parser/formal");
const transpiler_1 = require("../lean/transpiler");
const transpiler_2 = require("../react/transpiler");
function runTest(name, fn) {
    try {
        fn();
        console.log(`✓ ${name}`);
    }
    catch (error) {
        console.error(`✗ ${name}`);
        throw error;
    }
}
runTest('parseExpr marks quoted claims as string atoms', () => {
    const expr = (0, expr_1.parseExpr)('"hello world"');
    assert_1.strict.equal(expr.type, 'Atom');
    assert_1.strict.equal(expr.atomKind, 'string');
});
runTest('parseExpr builds logical AST for supported expressions', () => {
    const expr = (0, expr_1.parseExpr)('(p && q) -> r');
    assert_1.strict.equal(expr.type, 'Implies');
});
runTest('parser preserves malformed expressions as opaque atoms', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Broken() {
  assert(p && && q);
}
`));
    const theorem = ast[0];
    assert_1.strict.equal(theorem.type, 'Theorem');
    const claim = theorem.body[0];
    assert_1.strict.equal(claim.type, 'Assert');
    assert_1.strict.equal(claim.expr.type, 'Atom');
    assert_1.strict.equal(claim.expr.atomKind, 'opaque');
});
runTest('checker validates a paired theorem and proof', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Identity() {
  assert(p -> p)
} ↔

proof Identity() {
  assume(p) →
  conclude(p)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.pairedCount, 1);
    assert_1.strict.equal(report.reports[0].goal, 'p → p');
    assert_1.strict.equal(report.reports[0].derivedConclusion, 'p');
});
runTest('checker rejects proofs that do not establish theorem goal', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Identity() {
  assert(p -> p)
} ↔

proof Identity() {
  assume(p) →
  conclude(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
    assert_1.strict.match(report.reports[0].diagnostics.map(d => d.message).join('\n'), /does not establish theorem goal/);
});
runTest('checker accepts conjunction goals when both parts are established', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Pair() {
  assert(p && q)
} ↔

proof Pair() {
  assume(p) →
  assert(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
});
runTest('eval backend rejects unsupported mathematical notation', () => {
    assert_1.strict.throws(() => {
        const js = (0, formal_1.parseFL)(`
theorem AdvancedMath() {
  assert(∀(n: ℕ) ⇒ n = n)
}
`);
        eval(js);
    }, /Use 'fl verify'/);
});
runTest('Lean transpiler retains advanced mathematical claims', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem AdvancedMath() {
  assert(∀(n: ℕ) ⇒ n = n)
}
`));
    const output = (0, transpiler_1.transpileToLean)(ast);
    assert_1.strict.match(output.source, /theorem AdvancedMath/);
    assert_1.strict.match(output.source, /∀ n : ℕ,/);
    assert_1.strict.match(output.source, /n = n/);
});
runTest('React backend generates a webapp scaffold', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem Hello() {
  assert(true)
}
`));
    const outDir = fs.mkdtempSync(path.join(os.tmpdir(), 'futurlang-web-'));
    (0, transpiler_2.createReactApp)(ast, outDir);
    assert_1.strict.equal(fs.existsSync(path.join(outDir, 'package.json')), true);
    assert_1.strict.equal(fs.existsSync(path.join(outDir, 'src', 'App.tsx')), true);
    assert_1.strict.equal(fs.existsSync(path.join(outDir, 'src', 'styles.css')), true);
});
console.log('All unit tests passed.');
