"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
// test-lexer.ts
const lexer_1 = require("./src/parser/lexer");
console.log('=== Testing Extended Lexer ===\n');
// Test 1: Your original syntax (should still work)
console.log('Test 1: Original syntax');
const originalCode = `
theorem Hello_World() {
  assert("Hello World can be proven");
  let message = "Hello World";
  assert(message == "Hello World");
}
`;
const result1 = (0, lexer_1.lexFL)(originalCode);
console.log('Parsed lines:', result1.length);
result1.forEach((line) => {
    console.log(`  ${line.type}: ${line.content.substring(0, 50)}${line.content.length > 50 ? '...' : ''}`);
});
// Test 2: New syntax with math symbols
console.log('\n\nTest 2: Math symbols');
const mathCode = `
theorem Abel_Ruffini() {
  assert(∀(n: ℕ) ⇒ n ≥ 5)
}

lemma Test() {
  assert(x ∈ ℝ)
}

struct Field {
  carrier: Set
}
`;
const result2 = (0, lexer_1.lexFL)(mathCode);
console.log('Parsed lines:', result2.length);
result2.forEach((line) => {
    console.log(`  ${line.type}: ${line.content.substring(0, 50)}${line.content.length > 50 ? '...' : ''}`);
    const symbols = (0, lexer_1.extractMathSymbols)(line.content);
    if (symbols.length > 0) {
        console.log(`    Symbols found: ${symbols.join(', ')}`);
    }
});
// Test 3: Symbol info
console.log('\n\nTest 3: Symbol information');
const testSymbols = ['∀', 'ℕ', '⇒', '∈'];
testSymbols.forEach((symbol) => {
    const info = (0, lexer_1.getSymbolInfo)(symbol);
    console.log(`  ${symbol} -> ${info === null || info === void 0 ? void 0 : info.name} (${info === null || info === void 0 ? void 0 : info.category})`);
});
console.log('\n=== All Tests Complete ===');
