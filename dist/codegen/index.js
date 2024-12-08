"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.generateJSFromAST = generateJSFromAST;
const exprGen_1 = require("./exprGen");
const exprParser_1 = require("../parser/exprParser");
const runtime_1 = require("./runtime");
function generateJSFromAST(node, runtime = runtime_1.runtimePreamble) {
    let code = runtime + '\n';
    code += generateNode(node);
    return code;
}
function generateNode(node, isTheoremBody = false) {
    switch (node.type) {
        case 'TheoremDeclaration': {
            const theorem = node;
            const bodyContent = generateNode(theorem.body, true);
            return `theorem("${theorem.name}", () => {
  return ${bodyContent};
});`;
        }
        case 'DefinitionDeclaration': {
            const definition = node;
            return `// Definition: ${definition.name}\n${generateNode(definition.body)}`;
        }
        case 'ProofDeclaration': {
            const proof = node;
            return `(() => {
  // Proof ${proof.name ? `of ${proof.name}` : ''}
${generateNode(proof.body)};
  return true;
})()`;
        }
        case 'LemmaDeclaration': {
            const lemma = node;
            return `// Lemma: ${lemma.name}\n${generateNode(lemma.body)}`;
        }
        case 'Assert': {
            const assert = node;
            let assertArg = '';
            if (assert.condition.startsWith('"') && assert.condition.endsWith('"')) {
                assertArg = assert.condition;
            }
            else {
                try {
                    const exprAst = (0, exprParser_1.parseLogicExpression)(assert.condition);
                    assertArg = (0, exprGen_1.generateExprJS)(exprAst);
                }
                catch (e) {
                    console.error("Failed to parse assert condition:", assert.condition);
                    assertArg = `"${assert.condition}"`;
                }
            }
            return `assert(${assertArg})`;
        }
        case 'Let': {
            const letNode = node;
            let letValue = '';
            if (letNode.value.startsWith('"') && letNode.value.endsWith('"')) {
                letValue = letNode.value;
            }
            else {
                try {
                    const valAst = (0, exprParser_1.parseLogicExpression)(letNode.value);
                    letValue = (0, exprGen_1.generateExprJS)(valAst);
                }
                catch (e) {
                    console.error("Failed to parse let value:", letNode.value);
                    letValue = `"${letNode.value}"`;
                }
            }
            return `setVar("${letNode.varName}", ${letValue})`;
        }
        case 'Raw': {
            const rawNode = node;
            if (!rawNode.content.trim()) {
                return 'true';
            }
            // If it's a string literal, return it directly
            if (rawNode.content.startsWith('"') && rawNode.content.endsWith('"')) {
                return rawNode.content;
            }
            // For theorem bodies, don't wrap in return since we add it in the theorem case
            if (isTheoremBody) {
                // If content already has return, use it as is
                if (rawNode.content.includes('return')) {
                    return rawNode.content;
                }
                // Otherwise return the content directly
                return rawNode.content.trim();
            }
            // Otherwise wrap in a comment
            return `/* ${rawNode.content} */\ntrue`;
        }
        case 'And': {
            const andNode = node;
            const left = generateNode(andNode.left);
            const right = generateNode(andNode.right);
            // If either side contains statements (indicated by semicolons or returns),
            // wrap it in an IIFE to ensure proper execution
            const wrapIfNeeded = (code) => {
                if (code.includes(';') || code.includes('return')) {
                    return `(() => { ${code}; return true; })()`;
                }
                return code;
            };
            return `${wrapIfNeeded(left)} && ${wrapIfNeeded(right)}`;
        }
        default: {
            // Handle any remaining LogicExpr types
            try {
                return (0, exprGen_1.generateExprJS)(node);
            }
            catch (e) {
                console.error("Failed to generate expression:", e);
                return 'true';
            }
        }
    }
}
