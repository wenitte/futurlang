"use strict";
// src/codegen/exprGen.ts
Object.defineProperty(exports, "__esModule", { value: true });
exports.generateExprJS = generateExprJS;
function generateExprJS(expr) {
    switch (expr.type) {
        case 'Quantifier':
            return `${expr.quantifier}("${expr.variable}", inSet("${expr.variable}","${expr.set}"), ${generateExprJS(expr.body)})`;
        case 'Not':
            return `not(${generateExprJS(expr.expr)})`;
        case 'BinaryOp':
            return `${expr.op}(${generateExprJS(expr.left)}, ${generateExprJS(expr.right)})`;
        case 'InSet':
            return `inSet("${expr.element}","${expr.set}")`;
        case 'NotInSet':
            return `notInSet("${expr.element}","${expr.set}")`;
        case 'Subset':
            return `${expr.proper ? 'subset' : 'subseteq'}("${expr.left}", "${expr.right}")`;
        case 'SetOp':
            return `${expr.op}("${expr.left}", "${expr.right}")`;
        case 'EmptySet':
            return `emptySet()`;
        case 'Predicate':
            const args = expr.args.map(a => `"${a}"`).join(',');
            return `${expr.name}(${args})`;
        case 'Var':
            return `"${expr.name}"`;
        default:
            // Handle unknown/unhandled expression types gracefully
            const _exhaustiveCheck = expr; // Helps with type checking during development
            console.error("Unhandled LogicExpr type in generateExprJS:", expr); // Log the error for debugging
            return "/* Unhandled expression */"; // Or throw an error:  throw new Error(`Unhandled LogicExpr type: ${expr.type}`);
    }
}
