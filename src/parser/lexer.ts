// src/parsing/lexer.ts

export interface ParsedLine {
    type: 'theorem' | 'definition' | 'proof' | 'assert' | 'let' | 'blockEnd' | 'raw';
    content: string;
    name?: string; // For theorem/definition names
  }
  
  export function lexFL(text: string): ParsedLine[] {
    const lines = text.split('\n').map(l => l.trim()).filter(l => l.length > 0);
    const parsed: ParsedLine[] = [];
  
    for (const line of lines) {
      if (line.includes('theorem') || line.includes('definition')) {
        const name = line.match(/(?:theorem|definition)\s+(\w+)/)?.[1];
        if (line.includes('theorem')) {
          parsed.push({ type: 'theorem', content: line, name });
        } else {
          parsed.push({ type: 'definition', content: line, name });
        }
      } else if (line.includes('proof')) {
        parsed.push({ type: 'proof', content: line });
      } else if (line.startsWith('let ')) {
        parsed.push({ type: 'let', content: line });
      } else if (line.includes('assert')) {
        parsed.push({ type: 'assert', content: line });
      } else if (line.includes('}')) {
        parsed.push({ type: 'blockEnd', content: line });
      } else {
        // If it doesn't match any known pattern, consider it 'raw'
        parsed.push({ type: 'raw', content: line });
      }
    }
  
    return parsed;
  }
  