"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.parseLinesToAST = parseLinesToAST;
const exprParser_1 = require("./exprParser");
function parseLinesToAST(lines) {
    console.log("Starting to parse lines...");
    let currentExpression = null;
    let index = 0;
    function parseBlock() {
        var _a, _b;
        let nodes = [];
        let blockExpression = null;
        let i = index + 1; // Start after the opening line
        let braceCount = 1;
        let blockContent = '';
        while (i < lines.length && braceCount > 0) {
            const line = lines[i];
            // Count braces
            for (const token of line.tokens) {
                if (token.value === '{')
                    braceCount++;
                if (token.value === '}')
                    braceCount--;
            }
            // Don't process the closing brace line
            if (braceCount === 0)
                break;
            // For declarations, use the preserved body content if available
            const preservedContent = (_b = (_a = lines[index]) === null || _a === void 0 ? void 0 : _a.bodyContent) !== null && _b !== void 0 ? _b : '';
            if (preservedContent) {
                blockContent = preservedContent;
                break;
            }
            else {
                let expr = parseStatement(line);
                if (expr) {
                    if (blockExpression === null) {
                        blockExpression = expr;
                    }
                    else {
                        blockExpression = {
                            type: 'And',
                            left: blockExpression,
                            right: expr
                        };
                    }
                }
            }
            i++;
        }
        // If we have preserved body content, use it instead of parsed nodes
        if (blockContent) {
            return {
                nodes: [{
                        type: 'Raw',
                        content: blockContent
                    }],
                endIndex: i
            };
        }
        return {
            nodes: blockExpression ? [blockExpression] : [],
            endIndex: i
        };
    }
    function parseStatement(line) {
        switch (line.type) {
            case 'TheoremDeclaration':
            case 'DefinitionDeclaration':
            case 'ProofDeclaration':
            case 'LemmaDeclaration': {
                const declarationName = line.name || '';
                console.log(`Found ${line.type}: ${declarationName}`);
                const { nodes, endIndex } = parseBlock();
                index = endIndex; // Update outer index
                const body = nodes.length === 1 ? nodes[0] :
                    nodes.length > 1 ? nodes.reduce((acc, curr) => ({
                        type: 'And',
                        left: acc,
                        right: curr
                    })) :
                        { type: 'Raw', content: '' };
                switch (line.type) {
                    case 'TheoremDeclaration':
                        return {
                            type: 'TheoremDeclaration',
                            name: declarationName,
                            body
                        };
                    case 'DefinitionDeclaration':
                        return {
                            type: 'DefinitionDeclaration',
                            name: declarationName,
                            body
                        };
                    case 'ProofDeclaration':
                        return {
                            type: 'ProofDeclaration',
                            name: declarationName,
                            body
                        };
                    case 'LemmaDeclaration':
                        return {
                            type: 'LemmaDeclaration',
                            name: declarationName,
                            body
                        };
                }
                break;
            }
            case 'assert': {
                let condition = line.content;
                if (condition.startsWith('assert(') && condition.endsWith(')')) {
                    condition = condition.slice(7, -1).trim();
                }
                // If it's a string literal, keep it as is
                if (condition.startsWith('"') && condition.endsWith('"')) {
                    return {
                        type: 'Assert',
                        condition
                    };
                }
                // Try to parse as logic expression
                try {
                    (0, exprParser_1.parseLogicExpression)(condition);
                    return {
                        type: 'Assert',
                        condition
                    };
                }
                catch (e) {
                    console.error("Failed to parse assert condition:", condition);
                    return {
                        type: 'Assert',
                        condition: `"${condition}"`
                    };
                }
            }
            case 'let': {
                const match = line.content.match(/let\s+(\w+)\s*=\s*(.+?);/);
                if (match) {
                    return {
                        type: 'Let',
                        varName: match[1],
                        value: match[2].trim()
                    };
                }
                return {
                    type: 'Raw',
                    content: line.content
                };
            }
            case 'raw': {
                if (line.content === '&&') {
                    return null; // Skip && tokens as they're handled by combination logic
                }
                if (!line.content.trim()) {
                    return null; // Skip empty lines
                }
                return {
                    type: 'Raw',
                    content: line.content
                };
            }
            default:
                return null;
        }
    }
    while (index < lines.length) {
        const line = lines[index];
        const expr = parseStatement(line);
        if (expr !== null) {
            if (currentExpression === null) {
                currentExpression = expr;
            }
            else {
                currentExpression = {
                    type: 'And',
                    left: currentExpression,
                    right: expr
                };
            }
        }
        index++;
    }
    if (currentExpression === null) {
        throw new Error("No top level expression");
    }
    return currentExpression;
}
