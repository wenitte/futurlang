"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.exprToProp = exprToProp;
exports.normalizeProp = normalizeProp;
exports.sameProp = sameProp;
exports.splitImplication = splitImplication;
exports.splitConjunction = splitConjunction;
exports.splitIff = splitIff;
exports.splitDisjunction = splitDisjunction;
function exprToProp(expr) {
    switch (expr.type) {
        case 'Atom': return expr.condition;
        case 'And': return `${exprToProp(expr.left)} ∧ ${exprToProp(expr.right)}`;
        case 'Or': return `${exprToProp(expr.left)} ∨ ${exprToProp(expr.right)}`;
        case 'Implies': return `${exprToProp(expr.left)} → ${exprToProp(expr.right)}`;
        case 'Iff': return `${exprToProp(expr.left)} ↔ ${exprToProp(expr.right)}`;
        case 'Not': return `¬${exprToProp(expr.operand)}`;
        case 'Quantified': {
            const symbol = expr.quantifier === 'forall' ? '∀' : expr.quantifier === 'exists' ? '∃' : '∃!';
            const binder = expr.binderStyle === 'bounded'
                ? `${expr.variable} ∈ ${expr.domain}`
                : `${expr.variable}: ${expr.domain}`;
            return expr.body ? `${symbol} ${binder}, ${exprToProp(expr.body)}` : `${symbol} ${binder}`;
        }
        default: return '';
    }
}
function normalizeProp(s) {
    return s.trim().toLowerCase().replace(/\s+/g, ' ');
}
function sameProp(a, b) {
    return normalizeProp(a) === normalizeProp(b);
}
function splitImplication(expr) {
    if (expr.type !== 'Implies')
        return null;
    return [exprToProp(expr.left), exprToProp(expr.right)];
}
function splitConjunction(expr) {
    if (expr.type !== 'And')
        return null;
    return [exprToProp(expr.left), exprToProp(expr.right)];
}
function splitIff(expr) {
    if (expr.type !== 'Iff')
        return null;
    return [exprToProp(expr.left), exprToProp(expr.right)];
}
function splitDisjunction(expr) {
    if (expr.type !== 'Or')
        return null;
    return [exprToProp(expr.left), exprToProp(expr.right)];
}
