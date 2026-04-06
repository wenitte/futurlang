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
    assert_1.strict.equal(report.reports[0].proofSteps[0].rule, 'ASSUMPTION');
    assert_1.strict.equal(report.reports[0].proofSteps[1].rule, 'IMPLIES_INTRO');
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
  assert(q) →
  conclude(p && q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].proofSteps[2].rule, 'AND_INTRO');
});
runTest('checker accepts modus ponens style derivations', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ModusPonens() {
  given(p -> q)
  assert(q)
} ↔

proof ModusPonens() {
  assume(p) →
  conclude(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].premises[0], 'p → q');
    assert_1.strict.equal(report.reports[0].proofSteps[1].rule, 'IMPLIES_ELIM');
});
runTest('checker accepts conjunction elimination derivations', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem LeftProjection() {
  assert((p && q) -> p)
} ↔

proof LeftProjection() {
  assume(p && q) →
  conclude(p)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    assert_1.strict.equal(report.reports[0].proofSteps[1].rule, 'AND_ELIM');
});
runTest('checker enforces lemma hypotheses before apply', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
lemma NeedsP() {
  given(p)
  assert(q)
} ↔

proof NeedsP() {
  conclude(q)
} →

theorem UsesLemma() {
  assert(q)
} ↔

proof UsesLemma() {
  apply(NeedsP)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, false);
    assert_1.strict.match(report.reports.map(r => r.diagnostics.map(d => d.message).join('\n')).join('\n'), /missing hypotheses p/);
});
runTest('checker accepts chained lemma application with satisfied hypotheses', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
lemma ForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof ForwardStep() {
  assume(p) →
  conclude(q)
} →

theorem UsesForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof UsesForwardStep() {
  assume(p) →
  apply(ForwardStep)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports.find(r => r.name === 'UsesForwardStep');
    assert_1.strict.ok(theoremReport);
    assert_1.strict.equal(theoremReport.proofSteps[1].rule, 'BY_LEMMA');
    assert_1.strict.equal(theoremReport.proofSteps[1].uses?.[0], 'p → q');
    assert_1.strict.equal(theoremReport.proofSteps[1].imports?.[0], 'q');
    const importedFact = theoremReport.proofObjects.find(object => object.source === 'lemma_application' && object.claim === 'q');
    assert_1.strict.ok(importedFact);
    assert_1.strict.equal(importedFact.dependsOn[0], 'p → q');
    assert_1.strict.equal(importedFact.imports?.[0], 'q');
});
runTest('checker accepts chained multi-premise implication demo', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ChainImplication() {
  given(p -> q) →
  given(q -> r) →
  assert(r)
} ↔

proof ChainImplication() {
  assume(p) →
  assert(q) →
  conclude(r)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
});
runTest('checker accepts chained conjunction premise demo', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem RightProjection() {
  given(p && q) →
  assert(q)
} ↔

proof RightProjection() {
  conclude(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
});
runTest('checker accepts contradiction discharge in the current demo subset', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ExplosionDemo() {
  given(p) →
  given(¬p) →
  assert(q)
} ↔

proof ExplosionDemo() {
  assume(¬q) →
  contradiction() →
  conclude(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    assert_1.strict.equal(report.valid, true);
    const theoremReport = report.reports[0];
    assert_1.strict.equal(theoremReport.method, 'contradiction');
    assert_1.strict.equal(theoremReport.proofSteps[1].rule, 'CONTRADICTION');
    assert_1.strict.equal(theoremReport.proofSteps[2].rule, 'CONTRADICTION');
    const contradictionFact = theoremReport.proofObjects.find(object => object.claim === 'contradiction');
    assert_1.strict.ok(contradictionFact);
    assert_1.strict.match(contradictionFact.dependsOn.join(' '), /p/);
    assert_1.strict.match(contradictionFact.dependsOn.join(' '), /¬p/);
});
runTest('checker records implication proof objects for derived facts', () => {
    const ast = (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
theorem ModusPonens() {
  given(p -> q) →
  assert(q)
} ↔

proof ModusPonens() {
  assume(p) →
  conclude(q)
}
`));
    const report = (0, checker_1.checkFile)(ast);
    const theoremReport = report.reports[0];
    const conclusionObject = theoremReport.proofObjects.find(object => object.source === 'conclusion' && object.claim === 'q');
    assert_1.strict.ok(conclusionObject);
    assert_1.strict.equal(conclusionObject.rule, 'IMPLIES_ELIM');
    assert_1.strict.equal(conclusionObject.dependsOn.length, 2);
    assert_1.strict.match(conclusionObject.dependsOn.join(' '), /p/);
    assert_1.strict.match(conclusionObject.dependsOn.join(' '), /q/);
});
runTest('parser rejects missing connective between top-level blocks', () => {
    assert_1.strict.throws(() => (0, parser_1.parseLinesToAST)((0, lexer_1.lexFL)(`
lemma ForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof ForwardStep() {
  assume(p) →
  conclude(q)
}

theorem UsesForwardStep() {
  given(p -> q) →
  assert(q)
} ↔

proof UsesForwardStep() {
  assume(p) →
  apply(ForwardStep)
}
`)), /Missing connective between top-level blocks/);
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
