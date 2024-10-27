import Anthropic from '@anthropic-ai/sdk'

const anthropic = new Anthropic({
    apiKey: process.env.ANTHROPIC_API_KEY,
})

export const systemPrompt = "You are a precise translator that converts natural language into truth-evaluable forms while preserving meaning and logical relationships."

export const basePrompt = `Transform this natural language statement into a truth-evaluable form that:
1. Preserves original meaning exactly
2. Can be evaluated as true/false
3. Makes implicit logical relationships explicit
4. Maintains intentional ambiguity/subjectivity
5. Preserves temporal relationships and sequence
6. Maintains modal qualities (possibility/necessity/probability)
7. No added specificity
8. Preserves nested logical relationships
9. Maintains multiple time frames if present
10. Preserves probability gradients`

export const mathExtension = `For mathematical proofs:
1. State primary theorem/claim
2. List prerequisites and definitions
3. Specify proof method:
   - Induction: {base case, inductive step}
   - Contradiction: {assumption, contradiction}
   - Direct: {conditions → conclusion}
   - Construction: {procedure, verification}
4. Number and indent steps to show dependencies
5. Link conclusion back to original claim`

export async function translateToFuturLang(text: string, isMathProof: boolean = false): Promise<string> {
    const promptText = isMathProof 
        ? `${basePrompt}\n${mathExtension}`
        : basePrompt
    
    const prompt = `${promptText}\n\nTransform this statement:\n${text}`

    const response = await anthropic.messages.create({
        model: "claude-3-sonnet-20240229",
        max_tokens: 1024,
        system: systemPrompt,
        messages: [
            { 
                role: "user", 
                content: prompt 
            }
        ]
    })

    const content = response.content[0]
    if ('text' in content) {
        return content.text
    }
    throw new Error('Unexpected response type from API')
}
