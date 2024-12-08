"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.lexFL = lexFL;
const LOGICAL_CONNECTIVES = {
    forall: ['∀'],
    exists: ['∃'],
    and: ['∧', '&&'],
    or: ['∨'],
    not: ['¬'],
    implies: ['⇒', '->'],
    iff: ['↔', '<->']
};
const SET_SYMBOLS = [
    '∈', '∉', '⊆', '⊂', '∪', '∩', '∅'
];
const SINGLE_CHAR_TOKENS = {
    '{': 'LBRACE',
    '}': 'RBRACE',
    '=': 'EQUAL',
    ';': 'SEMICOLON',
    ':': 'COLON',
    '(': 'LPAREN',
    ')': 'RPAREN',
    ',': 'COMMA',
    '@': 'AT_SYMBOL'
};
function lexFL(text) {
    // First normalize line endings
    const normalizedText = text.replace(/\r\n/g, '\n').replace(/\r/g, '\n');
    let lines = normalizedText.split('\n');
    const parsed = [];
    let currentStatement = '';
    let parenCount = 0;
    let braceCount = 0;
    let currentBody = '';
    let collectingBody = false;
    let currentDeclaration = null;
    for (let i = 0; i < lines.length; i++) {
        let line = lines[i].trim();
        if (line.length === 0)
            continue;
        // If we're collecting a body, handle it specially
        if (collectingBody) {
            for (const char of line) {
                if (char === '{')
                    braceCount++;
                if (char === '}')
                    braceCount--;
            }
            if (braceCount === 0) {
                // End of body
                collectingBody = false;
                if (currentDeclaration) {
                    currentDeclaration.bodyContent = currentBody.trim();
                    parsed.push(currentDeclaration);
                    currentDeclaration = null;
                }
                currentBody = '';
            }
            else {
                currentBody += line + '\n';
            }
            continue;
        }
        // Count parentheses for assert statements
        for (let char of line) {
            if (char === '(')
                parenCount++;
            if (char === ')')
                parenCount--;
        }
        // If we're in the middle of an assert statement
        if (parenCount > 0 || currentStatement) {
            currentStatement += ' ' + line;
            continue;
        }
        // Check for declarations that should collect body
        const isDeclaration = line.match(/^(theorem|definition|proof|lemma)\s+\w*/i);
        if (isDeclaration) {
            currentDeclaration = classifyLine(line);
            currentDeclaration.tokens = tokenizeLine(line);
            // Start collecting body if we see a brace
            if (line.includes('{')) {
                collectingBody = true;
                braceCount = 1;
                currentBody = '';
            }
            continue;
        }
        // Handle && at the end of the line
        if (line.endsWith("&&")) {
            const lineWithoutAnd = line.slice(0, -2).trim();
            if (lineWithoutAnd) {
                const parsedLine = classifyLine(lineWithoutAnd);
                parsedLine.tokens = tokenizeLine(lineWithoutAnd);
                parsed.push(parsedLine);
            }
            parsed.push({
                type: 'raw',
                content: '&&',
                tokens: [{ type: 'LOGICAL_CONNECTIVE', value: '&&' }]
            });
        }
        else {
            // If we have a complete statement
            const completeStatement = currentStatement + ' ' + line;
            if (completeStatement.trim()) {
                const parsedLine = classifyLine(completeStatement.trim());
                parsedLine.tokens = tokenizeLine(completeStatement.trim());
                parsed.push(parsedLine);
            }
            currentStatement = '';
        }
    }
    // Handle any remaining statement
    if (currentStatement.trim()) {
        const parsedLine = classifyLine(currentStatement.trim());
        parsedLine.tokens = tokenizeLine(currentStatement.trim());
        parsed.push(parsedLine);
    }
    return parsed;
}
function classifyLine(line) {
    const lower = line.toLowerCase();
    let result;
    // Improve classification using regex
    if (line.match(/^theorem\s+\w+/i)) {
        const name = line.match(/theorem\s+(\w+)/i)[1];
        result = { type: 'TheoremDeclaration', content: line, name, tokens: [] };
    }
    else if (line.match(/^definition\s+\w+/i)) {
        const name = line.match(/definition\s+(\w+)/i)[1];
        result = { type: 'DefinitionDeclaration', content: line, name, tokens: [] };
    }
    else if (line.match(/^proof\s+\w*/i)) { // Allow proof with or without name
        const nameMatch = line.match(/proof\s+(\w+)/i);
        const name = nameMatch ? nameMatch[1] : undefined;
        result = { type: 'ProofDeclaration', content: line, name, tokens: [] };
    }
    else if (line.match(/^lemma\s+\w+/i)) {
        const name = line.match(/lemma\s+(\w+)/i)[1];
        result = { type: 'LemmaDeclaration', content: line, name, tokens: [] };
    }
    else if (lower.startsWith('let ')) {
        result = { type: 'let', content: line, tokens: [] };
    }
    else if (lower.startsWith('assert')) {
        result = { type: 'assert', content: line, tokens: [] };
    }
    else {
        result = { type: 'raw', content: line, tokens: [] };
    }
    return result;
}
function tokenizeLine(originalLine) {
    let line = originalLine;
    const tokens = [];
    const regex = /"([^"]*)"|(∀|∃|∧|∨|¬|⇒|↔|∈|∉|⊆|⊂|∪|∩|∅|->|<->|&&)|[{}=;():,@]|\s+/g;
    let match;
    while ((match = regex.exec(line)) !== null) {
        if (match[1] !== undefined) {
            tokens.push({ type: 'STRING', value: `"${match[1]}"` });
        }
        else if (match[2] !== undefined) {
            const symbol = match[2];
            if (Object.values(LOGICAL_CONNECTIVES).flat().includes(symbol)) {
                tokens.push({ type: 'LOGICAL_CONNECTIVE', value: symbol });
            }
            else {
                tokens.push({ type: 'SET_SYMBOL', value: symbol });
            }
        }
        else if (SINGLE_CHAR_TOKENS[match[0]]) {
            tokens.push({ type: SINGLE_CHAR_TOKENS[match[0]], value: match[0] });
        }
        else if (match[0].trim() !== "") { //identifier
            tokens.push({ type: 'IDENTIFIER', value: match[0].trim() });
        }
    }
    return tokens;
}
// Helper functions
function matchConnective(line, start) {
    for (const [name, symbols] of Object.entries(LOGICAL_CONNECTIVES)) {
        for (const sym of symbols) {
            if (line.startsWith(sym, start)) {
                return { symbol: sym, name };
            }
        }
    }
    return null;
}
function matchSetSymbol(line, start) {
    for (const sym of SET_SYMBOLS) {
        if (line.startsWith(sym, start)) {
            return sym;
        }
    }
    return null;
}
function readString(line, start) {
    let end = start + 1;
    while (end < line.length && line[end] !== '"') {
        end++;
    }
    const strVal = line.substring(start, Math.min(end + 1, line.length));
    return { value: strVal, nextIndex: end < line.length ? end + 1 : line.length };
}
function readIdentifier(line, start) {
    let end = start;
    while (end < line.length && !isDelimiter(line[end])) {
        end++;
    }
    const value = line.substring(start, end);
    return { value, nextIndex: end };
}
function isDelimiter(c) {
    return (c in SINGLE_CHAR_TOKENS) || isPartOfAnySymbol(c);
}
function isPartOfAnySymbol(c) {
    for (const arr of Object.values(LOGICAL_CONNECTIVES)) {
        for (const sym of arr) {
            if (sym.includes(c))
                return true;
        }
    }
    for (const sym of SET_SYMBOLS) {
        if (sym.includes(c))
            return true;
    }
    return false;
}
