"use strict";
// src/checker/checker.ts
// Main proof checker — walks the AST and applies inference rules
Object.defineProperty(exports, "__esModule", { value: true });
exports.checkFile = checkFile;
const rules_1 = require("./rules");
const propositions_1 = require("./propositions");
// ── Public API ────────────────────────────────────────────────────────────────
function checkFile(nodes) {
    const diagnostics = [];
    const reports = [];
    const globalLemmas = new Map();
    // Pass 1: collect all theorem/lemma names into global scope
    collectLemmaNames(nodes, globalLemmas);
    // Pass 2: find and check theorem↔proof pairs
    const pairs = findPairs(nodes);
    let theoremCount = 0, proofCount = 0, pairedCount = 0;
    for (const node of nodes) {
        if (node.type === 'Theorem')
            theoremCount++;
        if (node.type === 'Proof')
            proofCount++;
        if (node.type === 'Lemma') {
            theoremCount++;
            const report = checkProofBlock(node.name, node.body, globalLemmas, 'unknown');
            reports.push(report);
        }
    }
    for (const pair of pairs) {
        pairedCount++;
        const report = checkPair(pair.theorem, pair.proof, globalLemmas);
        reports.push(report);
    }
    // File-level checks
    if (theoremCount === 0) {
        diagnostics.push({ severity: 'warning', message: 'File contains no theorems' });
    }
    if (pairedCount < theoremCount) {
        diagnostics.push({
            severity: 'info',
            message: `${theoremCount - pairedCount} theorem(s) have no proof`
        });
    }
    const allValid = reports.every(r => r.valid);
    const score = computeScore(reports, pairedCount, theoremCount);
    return { valid: allValid, theoremCount, proofCount, pairedCount, reports, diagnostics, score };
}
function findPairs(nodes) {
    const pairs = [];
    for (let i = 0; i < nodes.length; i++) {
        const node = nodes[i];
        if (node.type === 'Theorem' && node.connective === '↔') {
            // Look for matching proof
            for (let j = i + 1; j < nodes.length; j++) {
                if (nodes[j].type === 'Proof') {
                    const proof = nodes[j];
                    if (normalizeName(proof.name) === normalizeName(node.name)) {
                        pairs.push({ theorem: node, proof });
                        break;
                    }
                }
                // Stop looking if we hit another theorem
                if (nodes[j].type === 'Theorem')
                    break;
            }
        }
    }
    return pairs;
}
// ── Check a theorem↔proof pair ────────────────────────────────────────────────
function checkPair(thm, proof, globalLemmas) {
    const diagnostics = [];
    const theoremGoalExpr = thm.body.find((n) => n.type === 'Assert')?.expr ?? null;
    const theoremGoal = theoremGoalExpr ? (0, propositions_1.exprToProp)(theoremGoalExpr) : null;
    // Check the pairing itself
    const thmAsserts = thm.body.filter(n => n.type === 'Assert');
    const pairingCheck = (0, rules_1.checkTheoremProofPairing)(thm.name, proof.name, thmAsserts.length > 0, proof.body.length, proof.body.some(n => n.type === 'Conclude'));
    if (!pairingCheck.valid) {
        diagnostics.push({ severity: 'error', message: pairingCheck.message, hint: pairingCheck.hint, rule: pairingCheck.rule });
    }
    // Detect proof method
    const method = detectProofMethod(proof.body);
    // Check the proof body
    const proofReport = checkProofBlock(proof.name, proof.body, globalLemmas, method, theoremGoal);
    diagnostics.push(...proofReport.diagnostics);
    if (theoremGoalExpr) {
        if (!isCheckableGoal(theoremGoalExpr)) {
            diagnostics.push({
                severity: 'info',
                message: `Goal '${theoremGoal}' is outside the current checker subset; use 'fl verify' for semantic verification`,
                rule: 'THEOREM_PROOF',
            });
        }
        else if (!goalSatisfied(theoremGoalExpr, proofReport, proof.body)) {
            diagnostics.push({
                severity: 'error',
                message: `Proof '${proof.name}' does not establish theorem goal '${theoremGoal}'`,
                hint: theoremGoalHint(theoremGoalExpr),
                rule: 'THEOREM_PROOF',
            });
        }
    }
    return {
        name: thm.name,
        valid: pairingCheck.valid && proofReport.valid && !diagnostics.some(d => d.severity === 'error'),
        method,
        stepCount: proof.body.length,
        goal: theoremGoal,
        derivedConclusion: proofReport.derivedConclusion,
        diagnostics,
        metrics: proofReport.metrics,
    };
}
// ── Check a proof body ────────────────────────────────────────────────────────
function checkProofBlock(name, body, globalLemmas, method, goal = null) {
    const diagnostics = [];
    const ctx = {
        established: [],
        variables: [],
        lemmas: new Map(globalLemmas),
        method,
        inContradiction: false,
        goal,
    };
    let step = 0;
    let assumptionCount = 0, assertionCount = 0, lemmaCount = 0;
    let hasConclusion = false, hasSorry = false;
    let maxDepth = 0, currentDepth = 0;
    for (const node of body) {
        step++;
        switch (node.type) {
            case 'Assume': {
                const n = node;
                const claim = exprToString(n.expr);
                const result = (0, rules_1.checkAssumption)(claim);
                if (!result.valid) {
                    diagnostics.push({ severity: 'error', message: result.message, step, rule: result.rule });
                }
                ctx.established.push({ content: claim, source: 'assumption', step });
                // If assumption is negated something, we're in contradiction mode
                if (claim.startsWith('¬') || claim.startsWith('not ') ||
                    claim.includes('contradiction') || claim.toLowerCase().includes('bycontradiction')) {
                    ctx.inContradiction = true;
                }
                assumptionCount++;
                currentDepth++;
                maxDepth = Math.max(maxDepth, currentDepth);
                break;
            }
            case 'Assert': {
                const n = node;
                const claim = exprToString(n.expr);
                // Check for sorry (explicit gap)
                if (claim.toLowerCase().includes('sorry')) {
                    hasSorry = true;
                    diagnostics.push({ severity: 'info', message: `Step ${step}: sorry placeholder`, rule: 'SORRY' });
                    ctx.established.push({ content: claim, source: 'assertion', step });
                    break;
                }
                // Check and/intro: if claim is a conjunction, verify both sides
                if (isConjunction(n.expr)) {
                    const [left, right] = splitConjunction(n.expr);
                    const andResult = (0, rules_1.checkAndIntro)(left, right, ctx);
                    if (!andResult.valid) {
                        // Warning not error — the conjunction may be introducing new facts
                        diagnostics.push({ severity: 'info', message: andResult.message, step, hint: andResult.hint });
                    }
                }
                ctx.established.push({ content: claim, source: 'assertion', step });
                assertionCount++;
                // Each assert deepens the chain
                if (n.connective === '→')
                    currentDepth++;
                maxDepth = Math.max(maxDepth, currentDepth);
                break;
            }
            case 'Conclude': {
                const n = node;
                const claim = exprToString(n.expr);
                ctx.established.push({ content: claim, source: 'conclusion', step });
                hasConclusion = true;
                // If we're in a contradiction block, the contradiction result is valid
                if (claim.toLowerCase().includes('contradiction')) {
                    const result = (0, rules_1.checkContradiction)(ctx);
                    if (!result.valid) {
                        diagnostics.push({ severity: 'error', message: result.message, step, hint: result.hint });
                    }
                }
                break;
            }
            case 'Apply': {
                const n = node;
                const result = (0, rules_1.checkLemmaApplication)(n.target, ctx);
                const lemma = ctx.lemmas.get(normalizeName(n.target));
                if (lemma && lemma.conclusions.length > 0) {
                    for (const conclusion of lemma.conclusions) {
                        ctx.established.push({ content: conclusion, source: 'lemma_application', step });
                    }
                }
                else {
                    ctx.established.push({ content: `applied(${n.target})`, source: 'lemma_application', step });
                }
                if (!result.valid) {
                    diagnostics.push({ severity: 'warning', message: result.message, step, rule: result.rule });
                }
                lemmaCount++;
                break;
            }
            case 'SetVar': {
                const n = node;
                ctx.variables.push({ name: n.varName, type: n.varType, step });
                // Variables are always valid introductions
                if (n.varType) {
                    ctx.established.push({
                        content: `${n.varName}: ${n.varType}`,
                        source: 'variable', step
                    });
                }
                break;
            }
            case 'Raw': {
                const n = node;
                const content = n.content.trim().toLowerCase();
                // Detect contradiction marker in raw content
                if (content === 'contradiction()' || content === 'contradiction') {
                    const result = (0, rules_1.checkContradiction)(ctx);
                    if (!result.valid) {
                        diagnostics.push({ severity: 'error', message: result.message, step, hint: result.hint });
                    }
                    ctx.established.push({ content: 'contradiction', source: 'assertion', step });
                }
                break;
            }
            case 'Lemma': {
                // Inline lemma — recurse
                const n = node;
                const lemmaGoalExpr = n.body.find((child) => child.type === 'Assert')?.expr ?? null;
                const innerReport = checkProofBlock(n.name, n.body, ctx.lemmas, 'unknown', lemmaGoalExpr ? (0, propositions_1.exprToProp)(lemmaGoalExpr) : null);
                ctx.lemmas.set(normalizeName(n.name), {
                    hypotheses: [],
                    conclusions: innerReport.derivedConclusion ? [innerReport.derivedConclusion] : [],
                });
                diagnostics.push(...innerReport.diagnostics.map(d => ({ ...d, message: `[${n.name}] ${d.message}` })));
                ctx.established.push({ content: `lemma(${n.name})`, source: 'lemma_application', step });
                lemmaCount++;
                break;
            }
        }
    }
    // Induction-specific checks
    if (method === 'induction') {
        const content = body.map(n => nodeToString(n)).join(' ').toLowerCase();
        const result = (0, rules_1.checkInduction)(content.includes('base_case') || content.includes('base case') || content.includes('n = 0') || content.includes('n = 1'), content.includes('inductive_step') || content.includes('inductive step') || content.includes('k + 1') || content.includes('n + 1'), content.includes('inductive hypothesis') || content.includes('induction hypothesis') || content.includes('inductive_hypothesis'));
        if (!result.valid) {
            diagnostics.push({ severity: 'error', message: result.message, hint: result.hint, rule: result.rule });
        }
    }
    // Final check: does the proof establish anything at all?
    const hasAnyProgress = ctx.established.length > 0;
    if (!hasAnyProgress) {
        diagnostics.push({ severity: 'error', message: `Proof '${name}' establishes nothing`, rule: 'STRUCTURAL' });
    }
    const valid = !diagnostics.some(d => d.severity === 'error');
    const derivedConclusion = findDerivedConclusion(ctx.established);
    return {
        name,
        valid,
        method,
        stepCount: step,
        goal: ctx.goal,
        derivedConclusion,
        diagnostics,
        metrics: {
            assumptionCount,
            assertionCount,
            lemmaApplicationCount: lemmaCount,
            hasConclusion,
            hasSorry,
            dependencyDepth: maxDepth,
        },
    };
}
// ── Helpers ───────────────────────────────────────────────────────────────────
function detectProofMethod(body) {
    const content = body.map(n => nodeToString(n)).join(' ').toLowerCase();
    if (content.includes('bycontradiction') || content.includes('by_contradiction') ||
        content.includes('contradiction') || content.includes('assume(¬') ||
        content.includes('assume(not '))
        return 'contradiction';
    if (content.includes('induction') || content.includes('base_case') ||
        content.includes('inductive_step'))
        return 'induction';
    if (content.includes('construct') || content.includes('define(') ||
        content.includes('let '))
        return 'construction';
    return 'direct';
}
function collectLemmaNames(nodes, map) {
    for (const node of nodes) {
        if (node.type === 'Lemma' || node.type === 'Theorem') {
            const key = normalizeName(node.name);
            const statement = node.body.find((child) => child.type === 'Assert');
            map.set(key, { hypotheses: [], conclusions: statement ? [(0, propositions_1.exprToProp)(statement.expr)] : [] });
        }
        if (node.type === 'Definition') {
            const key = normalizeName(node.name);
            map.set(key, { hypotheses: [], conclusions: ['defined'] });
        }
    }
}
function exprToString(expr) {
    return (0, propositions_1.exprToProp)(expr);
}
function nodeToString(node) {
    switch (node.type) {
        case 'Assert': return exprToString(node.expr);
        case 'Assume': return exprToString(node.expr);
        case 'Conclude': return exprToString(node.expr);
        case 'Raw': return node.content;
        case 'Apply': return `apply(${node.target})`;
        default: return '';
    }
}
function isConjunction(expr) {
    return expr.type === 'And';
}
function splitConjunction(expr) {
    return (0, propositions_1.splitConjunction)(expr) ?? ['', ''];
}
function normalizeName(s) {
    return s.toLowerCase().replace(/[^a-z0-9]/g, '');
}
function computeScore(reports, paired, total) {
    if (total === 0)
        return 0;
    let score = 0;
    // 40 points for pairing ratio
    score += (paired / total) * 40;
    // 40 points for validity
    const validRatio = reports.filter(r => r.valid).length / Math.max(reports.length, 1);
    score += validRatio * 40;
    // 20 points for richness (has assumptions, conclusions, no sorry)
    const richRatio = reports.filter(r => r.metrics.assumptionCount > 0 &&
        r.metrics.hasConclusion &&
        !r.metrics.hasSorry).length / Math.max(reports.length, 1);
    score += richRatio * 20;
    return Math.round(score);
}
function goalSatisfied(goalExpr, report, body) {
    const established = report.derivedConclusion;
    if (!established)
        return false;
    const goal = (0, propositions_1.exprToProp)(goalExpr);
    if ((0, propositions_1.sameProp)(established, goal))
        return true;
    const implication = (0, propositions_1.splitImplication)(goalExpr);
    if (implication) {
        const [antecedent, consequent] = implication;
        const sawAssumption = body.some(node => node.type === 'Assume' && (0, propositions_1.sameProp)(exprToString(node.expr), antecedent));
        return sawAssumption && (0, propositions_1.sameProp)(established, consequent);
    }
    const conjunction = (0, propositions_1.splitConjunction)(goalExpr);
    if (conjunction) {
        const [left, right] = conjunction;
        const establishedClaims = collectEstablishedClaims(body);
        return establishedClaims.some(claim => (0, propositions_1.sameProp)(claim, left))
            && establishedClaims.some(claim => (0, propositions_1.sameProp)(claim, right));
    }
    const iff = (0, propositions_1.splitIff)(goalExpr);
    if (iff) {
        const [left, right] = iff;
        const establishedClaims = collectEstablishedClaims(body);
        return establishedClaims.some(claim => (0, propositions_1.sameProp)(claim, `${left} → ${right}`))
            && establishedClaims.some(claim => (0, propositions_1.sameProp)(claim, `${right} → ${left}`));
    }
    return false;
}
function collectEstablishedClaims(body) {
    const claims = [];
    for (const node of body) {
        if (node.type === 'Assert')
            claims.push(exprToString(node.expr));
        if (node.type === 'Assume')
            claims.push(exprToString(node.expr));
        if (node.type === 'Conclude')
            claims.push(exprToString(node.expr));
    }
    return claims;
}
function findDerivedConclusion(established) {
    for (let i = established.length - 1; i >= 0; i--) {
        const claim = established[i];
        if (claim.source === 'conclusion' || claim.source === 'assertion' || claim.source === 'lemma_application') {
            return claim.content;
        }
    }
    return null;
}
function theoremGoalHint(goalExpr) {
    const implication = (0, propositions_1.splitImplication)(goalExpr);
    if (implication) {
        const [antecedent, consequent] = implication;
        return `For a simple demo proof, start with assume(${antecedent}) and finish by concluding ${consequent}.`;
    }
    const conjunction = (0, propositions_1.splitConjunction)(goalExpr);
    if (conjunction) {
        const [left, right] = conjunction;
        return `Establish both '${left}' and '${right}', then conclude the conjunction or leave both as derived steps.`;
    }
    return 'Finish the proof with conclude(<theorem claim>) or an equivalent final asserted result.';
}
function isCheckableGoal(expr) {
    switch (expr.type) {
        case 'Atom':
            return expr.atomKind !== 'opaque';
        case 'And':
        case 'Or':
        case 'Implies':
        case 'Iff':
            return isCheckableGoal(expr.left) && isCheckableGoal(expr.right);
        case 'Not':
            return isCheckableGoal(expr.operand);
        default:
            return false;
    }
}
