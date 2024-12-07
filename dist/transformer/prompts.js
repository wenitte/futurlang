"use strict";
var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.mathExtension = exports.basePrompt = exports.systemPrompt = void 0;
exports.translateToFuturLang = translateToFuturLang;
const sdk_1 = __importDefault(require("@anthropic-ai/sdk"));
const anthropic = new sdk_1.default({
    apiKey: process.env.ANTHROPIC_API_KEY,
});
exports.systemPrompt = "You are a precise translator that converts natural language into truth-evaluable forms while preserving meaning and logical relationships.";
exports.basePrompt = `Transform this natural language statement into a truth-evaluable form that:
1. Preserves original meaning exactly
2. Can be evaluated as true/false
3. Makes implicit logical relationships explicit
4. Maintains intentional ambiguity/subjectivity
5. Preserves temporal relationships and sequence
6. Maintains modal qualities (possibility/necessity/probability)
7. No added specificity
8. Preserves nested logical relationships
9. Maintains multiple time frames if present
10. Preserves probability gradients`;
exports.mathExtension = `For mathematical proofs:
1. State primary theorem/claim
2. List prerequisites and definitions
3. Specify proof method:
   - Induction: {base case, inductive step}
   - Contradiction: {assumption, contradiction}
   - Direct: {conditions → conclusion}
   - Construction: {procedure, verification}
4. Number and indent steps to show dependencies
5. Link conclusion back to original claim`;
function translateToFuturLang(text_1) {
    return __awaiter(this, arguments, void 0, function* (text, isMathProof = false) {
        const promptText = isMathProof
            ? `${exports.basePrompt}\n${exports.mathExtension}`
            : exports.basePrompt;
        const prompt = `${promptText}\n\nTransform this statement:\n${text}`;
        const response = yield anthropic.messages.create({
            model: "claude-3-sonnet-20240229",
            max_tokens: 1024,
            system: exports.systemPrompt,
            messages: [
                {
                    role: "user",
                    content: prompt
                }
            ]
        });
        const content = response.content[0];
        if ('text' in content) {
            return content.text;
        }
        throw new Error('Unexpected response type from API');
    });
}
