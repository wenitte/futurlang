"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.evaluateForAll = evaluateForAll;
exports.evaluateExists = evaluateExists;
exports.evaluateNotForAllNot = evaluateNotForAllNot;
const values_1 = require("./values");
function evaluateForAll(frame) {
    let result = '1';
    for (const value of frame.denotingValues) {
        result = (0, values_1.and)(result, value);
    }
    return frame.unresolvedCount > 0 && result === '1' ? 'ω' : result;
}
function evaluateExists(frame) {
    let result = '0';
    for (const value of frame.denotingValues) {
        result = (0, values_1.or)(result, value);
    }
    if (result === '1')
        return '1';
    return frame.unresolvedCount > 0 ? 'ω' : '0';
}
function evaluateNotForAllNot(frame) {
    let result = '0';
    for (const value of frame.denotingValues) {
        result = (0, values_1.or)(result, value);
    }
    return result;
}
