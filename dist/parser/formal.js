"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.parseFL = parseFL;
// src/parser/formal.ts
const lexer_1 = require("./lexer");
const parser_1 = require("./parser");
const codegen_1 = require("../codegen");
const runtime_1 = require("../codegen/runtime");
function parseFL(text) {
    const lines = (0, lexer_1.lexFL)(text);
    const ast = (0, parser_1.parseLinesToAST)(lines);
    const output = (0, codegen_1.generateJSFromAST)(ast, runtime_1.runtimePreamble);
    return output;
}
