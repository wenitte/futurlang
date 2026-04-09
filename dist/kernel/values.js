"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.WENITTAIN_VALUES = void 0;
exports.neg = neg;
exports.and = and;
exports.or = or;
exports.implies = implies;
exports.isClassical = isClassical;
exports.WENITTAIN_VALUES = ['0', '1', 'ω'];
const NEGATION_TABLE = {
    '0': '1',
    '1': '0',
    'ω': 'ω',
};
const AND_TABLE = {
    '0': { '0': '0', '1': '0', 'ω': '0' },
    '1': { '0': '0', '1': '1', 'ω': 'ω' },
    'ω': { '0': '0', '1': 'ω', 'ω': 'ω' },
};
const OR_TABLE = {
    '0': { '0': '0', '1': '1', 'ω': 'ω' },
    '1': { '0': '1', '1': '1', 'ω': '1' },
    'ω': { '0': 'ω', '1': '1', 'ω': 'ω' },
};
const IMPLIES_TABLE = {
    '0': { '0': '1', '1': '1', 'ω': '1' },
    '1': { '0': '0', '1': '1', 'ω': 'ω' },
    'ω': { '0': 'ω', '1': '1', 'ω': 'ω' },
};
function neg(value) {
    return NEGATION_TABLE[value];
}
function and(left, right) {
    return AND_TABLE[left][right];
}
function or(left, right) {
    return OR_TABLE[left][right];
}
function implies(left, right) {
    return IMPLIES_TABLE[left][right];
}
function isClassical(value) {
    return value === '0' || value === '1';
}
