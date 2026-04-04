// test-lexer.ts
import { lexFL, extractMathSymbols, getSymbolInfo, ParsedLine } from './src/parser/lexer';

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

const result1: ParsedLine[] = lexFL(originalCode);
console.log('Parsed lines:', result1.length);
result1.forEach((line: ParsedLine) => {
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

const result2: ParsedLine[] = lexFL(mathCode);
console.log('Parsed lines:', result2.length);
result2.forEach((line: ParsedLine) => {
  console.log(`  ${line.type}: ${line.content.substring(0, 50)}${line.content.length > 50 ? '...' : ''}`);
  const symbols = extractMathSymbols(line.content);
  if (symbols.length > 0) {
    console.log(`    Symbols found: ${symbols.join(', ')}`);
  }
});

// Test 3: Symbol info
console.log('\n\nTest 3: Symbol information');
const testSymbols = ['∀', 'ℕ', '⇒', '∈'];
testSymbols.forEach((symbol: string) => {
  const info = getSymbolInfo(symbol);
  console.log(`  ${symbol} -> ${info?.name} (${info?.category})`);
});

console.log('\n=== All Tests Complete ===');
