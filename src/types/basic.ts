export type LogicalOperator = '∀' | '∃' | '∧' | '∨' | '¬' | '→' | '↔'

export type Statement = {
    id: number
    content: string
    dependencies?: number[]
    type: 'claim' | 'assumption' | 'step' | 'conclusion'
}

export type Proof = {
    statements: Statement[]
    method: 'induction' | 'contradiction' | 'direct' | 'construction'
    prerequisites?: string[]
}

