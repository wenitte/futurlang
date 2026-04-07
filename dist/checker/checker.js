"use strict";
// src/checker/checker.ts
// Main proof checker — walks the AST and applies inference rules
Object.defineProperty(exports, "__esModule", { value: true });
exports.checkFile = checkFile;
const expr_1 = require("../parser/expr");
const rules_1 = require("./rules");
const sorts_1 = require("./sorts");
const propositions_1 = require("./propositions");
// ── Public API ────────────────────────────────────────────────────────────────
function checkFile(nodes, options = {}) {
    const diagnostics = [];
    const reports = [];
    const globalLemmas = new Map();
    // Pass 1: collect all theorem/lemma names into global scope
    collectLemmaNames(nodes, globalLemmas);
    // Pass 2: find and check theorem↔proof pairs
    const pairs = findPairs(nodes);
    const pairedNames = new Set(pairs.map(pair => normalizeName(pair.theorem.name)));
    let theoremCount = 0, proofCount = 0, pairedCount = 0;
    for (const node of nodes) {
        if (node.type === 'Theorem')
            theoremCount++;
        if (node.type === 'Proof')
            proofCount++;
        if (node.type === 'Lemma') {
            theoremCount++;
            if (!pairedNames.has(normalizeName(node.name))) {
                const report = checkProofBlock(node.name, node.body, globalLemmas, 'unknown', null, [], options);
                reports.push(report);
            }
        }
    }
    for (const pair of pairs) {
        pairedCount++;
        const report = checkPair(pair.theorem, pair.proof, globalLemmas, options);
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
        if ((node.type === 'Theorem' || node.type === 'Lemma') && node.connective === '↔') {
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
function checkPair(thm, proof, globalLemmas, options) {
    const diagnostics = [];
    const theoremPremises = thm.body
        .filter((n) => n.type === 'Given')
        .map(node => (0, propositions_1.exprToProp)(node.expr));
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
    const proofReport = checkProofBlock(proof.name, proof.body, globalLemmas, method, theoremGoal, theoremPremises, options);
    diagnostics.push(...proofReport.diagnostics);
    if (theoremGoalExpr) {
        const goalParseDiagnostic = parseFallbackDiagnostic(theoremGoalExpr, `Theorem goal '${theoremGoal}'`);
        if (goalParseDiagnostic)
            diagnostics.push(goalParseDiagnostic);
        const goalKernelDiagnostic = kernelSubsetDiagnostic(theoremGoalExpr, `Goal '${theoremGoal}'`);
        if (goalKernelDiagnostic)
            diagnostics.push(goalKernelDiagnostic);
        if (!isCheckableGoal(theoremGoalExpr)) {
            diagnostics.push({
                severity: 'info',
                message: `Goal '${theoremGoal}' is outside the current kernel subset; steps will be marked UNVERIFIED`,
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
        premises: theoremPremises,
        derivedConclusion: proofReport.derivedConclusion,
        proofSteps: proofReport.proofSteps,
        proofObjects: proofReport.proofObjects,
        derivations: proofReport.derivations,
        baseFactIds: proofReport.baseFactIds,
        derivedFactIds: proofReport.derivedFactIds,
        diagnostics,
        provedCount: proofReport.provedCount,
        unverifiedCount: proofReport.unverifiedCount,
        metrics: proofReport.metrics,
    };
}
// ── Check a proof body ────────────────────────────────────────────────────────
function checkProofBlock(name, body, globalLemmas, method, goal = null, premises = [], options = {}) {
    const diagnostics = [];
    const premiseClaims = premises.map((content, index) => ({
        content,
        source: 'premise',
        step: -(index + 1),
        scopeIds: [],
        proofObjectId: makeProofObjectId(-(index + 1), 'premise', content),
    }));
    // Build initial sort scope from premises (given() statements)
    const initialSortScope = new Map();
    for (const premise of premises) {
        extractSortScopeFromClaim(premise, initialSortScope);
    }
    const ctx = {
        established: premiseClaims,
        unverified: [],
        unverifiedContents: new Set(),
        proofObjects: premiseClaims.map(claim => ({
            id: claim.proofObjectId,
            claim: claim.content,
            rule: 'PREMISE',
            source: claim.source,
            step: claim.step,
            scopeIds: claim.scopeIds,
            dependsOn: [],
            dependsOnIds: [],
            status: 'PROVED',
        })),
        derivations: [],
        variables: [],
        sortScope: initialSortScope,
        currentScopes: [],
        lemmas: new Map(globalLemmas),
        method,
        inContradiction: false,
        goal,
    };
    let step = 0;
    let assumptionCount = 0, assertionCount = 0, lemmaCount = 0;
    let hasConclusion = false, hasSorry = false;
    let maxDepth = 0, currentDepth = 0;
    const proofSteps = [];
    for (const node of body) {
        step++;
        switch (node.type) {
            case 'Assume': {
                const n = node;
                const claim = exprToString(n.expr);
                const parseDiagnostic = parseFallbackDiagnostic(n.expr, `Step ${step} assumption '${claim}'`);
                if (parseDiagnostic)
                    diagnostics.push(parseDiagnostic);
                const kernelDiagnostic = kernelSubsetDiagnostic(n.expr, `Step ${step} assumption '${claim}'`, step);
                if (kernelDiagnostic)
                    diagnostics.push(kernelDiagnostic);
                // Sort check
                const sortErr = (0, sorts_1.sortCheckProposition)(claim);
                if (sortErr) {
                    diagnostics.push({ severity: 'error', message: sortErr.message, step, rule: 'ASSUMPTION' });
                }
                const result = (0, rules_1.checkAssumption)(claim);
                if (!result.valid) {
                    diagnostics.push({ severity: 'error', message: result.message, step, rule: result.rule });
                }
                // Introduce variables into sort scope
                extractSortScopeFromClaim(claim, ctx.sortScope);
                registerAssumptionClaim(ctx, claim, step, result.rule);
                proofSteps.push({
                    step,
                    kind: 'assume',
                    claim,
                    rule: result.rule,
                    valid: result.valid,
                    status: 'PROVED',
                    message: result.message,
                    establishesAs: 'assumption',
                });
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
                const parseDiagnostic = parseFallbackDiagnostic(n.expr, `Step ${step} assertion '${claim}'`);
                if (parseDiagnostic)
                    diagnostics.push(parseDiagnostic);
                const kernelDiagnostic = kernelSubsetDiagnostic(n.expr, `Step ${step} assertion '${claim}'`, step);
                if (kernelDiagnostic)
                    diagnostics.push(kernelDiagnostic);
                // Sort check — block derivation on sort error
                const assertSortErr = (0, sorts_1.sortCheckProposition)(claim);
                if (assertSortErr) {
                    diagnostics.push({ severity: 'error', message: assertSortErr.message, step, rule: 'STRUCTURAL' });
                    proofSteps.push({ step, kind: 'assert', claim, rule: 'STRUCTURAL', valid: false, status: 'UNVERIFIED', message: assertSortErr.message });
                    break;
                }
                // Check for sorry (explicit gap)
                if (claim.toLowerCase().includes('sorry')) {
                    hasSorry = true;
                    diagnostics.push({ severity: 'info', message: `Step ${step}: sorry placeholder`, rule: 'SORRY' });
                    registerUnverifiedClaim(ctx, claim, step, 'SORRY');
                    proofSteps.push({
                        step, kind: 'assert', claim, rule: 'SORRY', valid: true, status: 'UNVERIFIED',
                        message: 'sorry placeholder',
                    });
                    break;
                }
                // Check and/intro: if claim is a conjunction, verify both sides.
                // Failed derivations fall back to UNVERIFIED (no error here for assertions).
                let stepRule = null;
                if (isConjunction(n.expr)) {
                    const [left, right] = splitConjunction(n.expr);
                    const andResult = (0, rules_1.checkAndIntro)(left, right, ctx);
                    stepRule = andResult.valid ? andResult : null;
                }
                else if (isDisjunction(n.expr)) {
                    const premise = checkPremiseClaim(claim, ctx);
                    if (premise) {
                        stepRule = premise;
                    }
                    else {
                        const derivation = checkDerivedClaim(claim, ctx);
                        if (derivation?.valid) {
                            stepRule = derivation;
                        }
                        else {
                            const [left, right] = splitDisjunction(n.expr);
                            const orLeft = (0, rules_1.checkOrIntroLeft)(left, claim, ctx);
                            if (orLeft.valid) {
                                stepRule = orLeft;
                            }
                            else {
                                const orRight = (0, rules_1.checkOrIntroRight)(right, claim, ctx);
                                stepRule = orRight.valid ? orRight : null;
                            }
                        }
                    }
                }
                else {
                    const premise = checkPremiseClaim(claim, ctx);
                    if (premise) {
                        stepRule = premise;
                    }
                    else {
                        const derivation = checkDerivedClaim(claim, ctx);
                        if (derivation?.valid) {
                            stepRule = derivation;
                        }
                    }
                }
                const finalizedAssertion = registerDerivedClaim(ctx, {
                    content: claim,
                    source: 'assertion',
                    step,
                    derivation: stepRule,
                });
                if (finalizedAssertion.objectStatus === 'UNVERIFIED') {
                    diagnostics.push({
                        severity: 'info',
                        message: `Step ${step} assertion '${claim}' is UNVERIFIED and does not advance the trusted proof state`,
                        step,
                        rule: finalizedAssertion.result.rule,
                    });
                }
                // Only emit error for definitively-failed derivations, not UNVERIFIED
                if (!finalizedAssertion.result.valid && stepRule?.valid === false) {
                    diagnostics.push({
                        severity: 'error',
                        message: finalizedAssertion.result.message,
                        step,
                        hint: finalizedAssertion.result.hint,
                        rule: finalizedAssertion.result.rule,
                    });
                }
                proofSteps.push({
                    step,
                    kind: 'assert',
                    claim,
                    rule: finalizedAssertion.result.rule,
                    valid: finalizedAssertion.result.valid || finalizedAssertion.objectStatus === 'UNVERIFIED',
                    status: finalizedAssertion.objectStatus,
                    message: finalizedAssertion.result.message,
                    establishesAs: 'assertion',
                });
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
                const parseDiagnostic = parseFallbackDiagnostic(n.expr, `Step ${step} conclusion '${claim}'`);
                if (parseDiagnostic)
                    diagnostics.push(parseDiagnostic);
                const kernelDiagnostic = kernelSubsetDiagnostic(n.expr, `Step ${step} conclusion '${claim}'`, step);
                if (kernelDiagnostic)
                    diagnostics.push(kernelDiagnostic);
                // Sort check
                const concSortErr = (0, sorts_1.sortCheckProposition)(claim);
                if (concSortErr) {
                    diagnostics.push({ severity: 'error', message: concSortErr.message, step, rule: 'STRUCTURAL' });
                }
                // Scope check for set-theoretic conclusions
                const scopeErr = checkScopeForClaim(claim, ctx, step);
                if (scopeErr)
                    diagnostics.push(scopeErr);
                const contradictionDischarge = checkContradictionDischarge(claim, ctx);
                const forallDischarge = checkForallGoalDischarge(claim, ctx);
                let derivation;
                if (isConjunction(n.expr)) {
                    derivation = (0, rules_1.checkAndIntro)(...splitConjunction(n.expr), ctx);
                }
                else if (isDisjunction(n.expr)) {
                    derivation = contradictionDischarge ?? checkDerivedClaim(claim, ctx) ?? forallDischarge;
                    if (!derivation?.valid) {
                        const [left, right] = splitDisjunction(n.expr);
                        const orLeft = (0, rules_1.checkOrIntroLeft)(left, claim, ctx);
                        derivation = orLeft.valid ? orLeft : (0, rules_1.checkOrIntroRight)(right, claim, ctx);
                    }
                }
                else {
                    derivation = contradictionDischarge ?? checkDerivedClaim(claim, ctx) ?? forallDischarge ?? checkImplicationGoalDischarge(claim, ctx);
                }
                if (derivation && !derivation.valid) {
                    diagnostics.push({ severity: 'error', message: derivation.message, step, hint: derivation.hint, rule: derivation.rule });
                }
                const finalizedConclusion = registerDerivedClaim(ctx, {
                    content: claim,
                    source: 'conclusion',
                    step,
                    derivation,
                });
                if (finalizedConclusion.objectStatus === 'UNVERIFIED') {
                    diagnostics.push({
                        severity: 'info',
                        message: `Step ${step} conclusion '${claim}' is UNVERIFIED and does not discharge the trusted theorem goal`,
                        step,
                        rule: finalizedConclusion.result.rule,
                    });
                }
                if (!finalizedConclusion.result.valid && finalizedConclusion.objectStatus !== 'UNVERIFIED') {
                    diagnostics.push({ severity: 'error', message: finalizedConclusion.result.message, step, hint: finalizedConclusion.result.hint, rule: finalizedConclusion.result.rule });
                }
                proofSteps.push({
                    step,
                    kind: 'conclude',
                    claim,
                    rule: finalizedConclusion.result.rule,
                    valid: finalizedConclusion.result.valid || finalizedConclusion.objectStatus === 'UNVERIFIED',
                    status: finalizedConclusion.objectStatus,
                    message: finalizedConclusion.result.message,
                    establishesAs: 'conclusion',
                });
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
                if (result.valid && lemma && lemma.conclusions.length > 0) {
                    for (const conclusion of lemma.conclusions) {
                        registerLemmaImportClaim(ctx, conclusion, step, lemma.hypotheses, lemma.conclusions);
                    }
                }
                else if (result.valid) {
                    diagnostics.push({
                        severity: 'info',
                        message: `Step ${step} apply(${n.target}) is UNVERIFIED because '${n.target}' is not defined in this file`,
                        step,
                        rule: result.rule,
                    });
                    registerUnverifiedLemmaClaim(ctx, n.target, step);
                }
                if (!result.valid) {
                    diagnostics.push({ severity: 'error', message: result.message, step, rule: result.rule, hint: result.hint });
                }
                proofSteps.push({
                    step,
                    kind: 'apply',
                    claim: n.target,
                    rule: result.rule,
                    valid: result.valid,
                    status: result.valid && !lemma ? 'UNVERIFIED' : 'PROVED',
                    message: result.message,
                    uses: result.valid && lemma ? lemma.hypotheses : [],
                    imports: result.valid && lemma ? lemma.conclusions : [],
                    establishesAs: 'lemma_application',
                });
                lemmaCount++;
                break;
            }
            case 'SetVar': {
                const n = node;
                const scope = openScope(ctx, 'variable', n.varName, step);
                ctx.variables.push({ name: n.varName, type: n.varType, step, scopeId: scope.id });
                // Introduce into sort scope
                const varSort = resolveVarTypeSort(n.varType);
                if (varSort !== null) {
                    ctx.sortScope.set(n.varName, varSort);
                }
                else {
                    // Default: lowercase → Element, uppercase → Set
                    const inferredSort = (0, sorts_1.inferIdentifierSort)(n.varName);
                    if (inferredSort !== null)
                        ctx.sortScope.set(n.varName, inferredSort);
                }
                if (n.varType) {
                    registerVariableClaim(ctx, `${n.varName}: ${n.varType}`, step);
                }
                proofSteps.push({
                    step,
                    kind: 'setVar',
                    claim: n.varType ? `${n.varName}: ${n.varType}` : n.varName,
                    rule: 'VARIABLE',
                    valid: true,
                    status: 'PROVED',
                    message: 'Variable introduced into context',
                    establishesAs: 'variable',
                });
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
                    registerContradictionClaim(ctx, step, result.rule);
                    proofSteps.push({
                        step,
                        kind: 'raw',
                        claim: 'contradiction',
                        rule: result.rule,
                        valid: result.valid,
                        message: result.message,
                        establishesAs: 'assertion',
                    });
                }
                else {
                    proofSteps.push({
                        step,
                        kind: 'raw',
                        claim: n.content,
                        rule: 'STRUCTURAL',
                        valid: true,
                        message: 'Raw proof step preserved',
                    });
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
                registerLemmaImportClaim(ctx, `lemma(${n.name})`, step, innerReport.derivedConclusion ? [innerReport.derivedConclusion] : [], []);
                proofSteps.push({
                    step,
                    kind: 'lemma',
                    claim: n.name,
                    rule: 'BY_LEMMA',
                    valid: innerReport.valid,
                    message: innerReport.valid ? 'Inline lemma checked' : 'Inline lemma has errors',
                    establishesAs: 'lemma_application',
                });
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
    const baseFactIds = collectBaseFactIds(ctx.proofObjects, ctx.derivations);
    const derivedFactIds = collectDerivedFactIds(ctx.derivations);
    diagnostics.push(...validateDerivationGraph({
        goal: ctx.goal,
        proofObjects: ctx.proofObjects,
        derivations: ctx.derivations,
    }));
    const provedCount = ctx.proofObjects.filter(o => o.status === 'PROVED').length;
    const unverifiedCount = ctx.proofObjects.filter(o => o.status === 'UNVERIFIED').length;
    if (options.strict && unverifiedCount > 0) {
        diagnostics.push({
            severity: 'error',
            message: `Strict mode rejects ${unverifiedCount} UNVERIFIED step(s) in proof '${name}'`,
            hint: 'Derive each claim inside the kernel or rerun without --strict.',
            rule: 'STRUCTURAL',
        });
    }
    return {
        name,
        valid: !diagnostics.some(d => d.severity === 'error'),
        method,
        stepCount: step,
        goal: ctx.goal,
        premises,
        derivedConclusion,
        proofSteps,
        proofObjects: ctx.proofObjects,
        derivations: ctx.derivations,
        baseFactIds,
        derivedFactIds,
        diagnostics,
        provedCount,
        unverifiedCount,
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
            const hypotheses = node.body
                .filter((child) => child.type === 'Given')
                .map(child => (0, propositions_1.exprToProp)(child.expr));
            map.set(key, { name: node.name, hypotheses, conclusions: statement ? [(0, propositions_1.exprToProp)(statement.expr)] : [] });
        }
        if (node.type === 'Definition') {
            const key = normalizeName(node.name);
            map.set(key, { name: node.name, hypotheses: [], conclusions: ['defined'] });
        }
    }
}
function exprToString(expr) {
    return (0, propositions_1.exprToProp)(expr);
}
function nodeToString(node) {
    switch (node.type) {
        case 'Given': return exprToString(node.expr);
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
function isProvedConclusion(content, report) {
    return report.proofObjects.some(o => o.status === 'PROVED' &&
        (o.source === 'conclusion' || o.source === 'assertion' || o.source === 'lemma_application') &&
        (0, propositions_1.sameProp)(o.claim, content));
}
function collectProvedClaims(report) {
    return report.proofObjects
        .filter(o => o.status === 'PROVED')
        .map(o => o.claim);
}
function goalSatisfied(goalExpr, report, body) {
    const established = report.derivedConclusion;
    if (!established)
        return false;
    const goal = (0, propositions_1.exprToProp)(goalExpr);
    if ((0, propositions_1.sameProp)(established, goal) && isProvedConclusion(established, report))
        return true;
    if (goalExpr.type === 'Quantified' && goalExpr.quantifier === 'forall' && goalExpr.body) {
        const witnesses = goalExpr.binderStyle === 'typed'
            ? collectTypedGoalWitnesses(report, goalExpr.domain)
            : collectBoundedGoalWitnesses(report, goalExpr.domain);
        const bodySource = (0, propositions_1.exprToProp)(goalExpr.body);
        return witnesses.some(witness => {
            const instantiated = instantiateBoundedQuantifier({ variable: goalExpr.variable, body: bodySource }, witness);
            if (!instantiated)
                return false;
            try {
                return goalSatisfied((0, expr_1.parseExpr)(instantiated), report, body);
            }
            catch {
                return false;
            }
        });
    }
    const implication = (0, propositions_1.splitImplication)(goalExpr);
    if (implication) {
        const [antecedent, consequent] = implication;
        return hasProvedAssumption(report, antecedent) && collectProvedClaims(report).some(claim => (0, propositions_1.sameProp)(claim, consequent));
    }
    const conjunction = (0, propositions_1.splitConjunction)(goalExpr);
    if (conjunction) {
        const [left, right] = conjunction;
        const establishedClaims = collectProvedClaims(report);
        return establishedClaims.some(claim => (0, propositions_1.sameProp)(claim, left))
            && establishedClaims.some(claim => (0, propositions_1.sameProp)(claim, right));
    }
    const iff = (0, propositions_1.splitIff)(goalExpr);
    if (iff) {
        const [left, right] = iff;
        const establishedClaims = collectProvedClaims(report);
        return establishedClaims.some(claim => (0, propositions_1.sameProp)(claim, `${left} → ${right}`))
            && establishedClaims.some(claim => (0, propositions_1.sameProp)(claim, `${right} → ${left}`));
    }
    return false;
}
function hasProvedAssumption(report, claim) {
    return report.proofObjects.some(object => object.status === 'PROVED' &&
        object.source === 'assumption' &&
        (0, propositions_1.sameProp)(object.claim, claim));
}
function collectTypedGoalWitnesses(report, domain) {
    const matches = report.proofObjects
        .filter(object => object.status === 'PROVED' && object.source === 'variable')
        .map(object => parseTypedVariableProp(object.claim))
        .filter((typed) => Boolean(typed))
        .filter(typed => sameTypeDomain(typed.domain, domain))
        .map(typed => typed.variable);
    return [...new Set(matches)];
}
function collectBoundedGoalWitnesses(report, setName) {
    const matches = report.proofObjects
        .filter(object => object.status === 'PROVED' && (object.source === 'assumption' || object.source === 'premise'))
        .map(object => parseMembershipProp(object.claim))
        .filter((membership) => Boolean(membership))
        .filter(membership => (0, propositions_1.sameProp)(membership.set, setName))
        .map(membership => membership.element);
    return [...new Set(matches)];
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
function registerClaim(ctx, input) {
    const proofObjectId = makeProofObjectId(input.step, input.source, input.content);
    const status = input.objectStatus ?? 'PROVED';
    const claim = {
        content: input.content,
        source: input.source,
        step: input.step,
        scopeIds: input.scopeIds ?? currentScopeIds(ctx),
        proofObjectId,
    };
    // Only PROVED claims count as established facts. UNVERIFIED claims are
    // recorded separately so they remain visible in diagnostics but cannot
    // satisfy theorem goals or participate in derivations.
    if (status === 'PROVED') {
        ctx.established.push(claim);
    }
    else {
        ctx.unverified.push(claim);
        ctx.unverifiedContents.add((0, propositions_1.normalizeProp)(claim.content));
    }
    ctx.proofObjects.push({
        id: proofObjectId,
        claim: input.content,
        rule: input.rule,
        source: input.source,
        step: input.step,
        scopeIds: claim.scopeIds,
        dischargedScopeIds: input.dischargedScopeIds && input.dischargedScopeIds.length > 0 ? uniqueIds(input.dischargedScopeIds) : undefined,
        dependsOn: uniqueProps(input.dependsOn),
        dependsOnIds: uniqueIds(input.dependsOnIds ?? resolveClaimIds(ctx, input.dependsOn)),
        imports: input.imports && input.imports.length > 0 ? uniqueProps(input.imports) : undefined,
        status,
    });
    if (input.emitDerivation !== false && status === 'PROVED') {
        ctx.derivations.push(makeDerivationNode(input.step, input.rule, uniqueIds(input.dependsOnIds ?? resolveClaimIds(ctx, input.dependsOn)), proofObjectId, input.dischargedScopeIds));
    }
    return claim;
}
function registerAssumptionClaim(ctx, claim, step, rule) {
    openScope(ctx, 'assumption', claim, step);
    return registerClaim(ctx, {
        content: claim,
        source: 'assumption',
        step,
        rule,
        dependsOn: [],
        emitDerivation: false,
        objectStatus: 'PROVED',
    });
}
function registerAssertionClaim(ctx, claim, step, rule) {
    return registerClaim(ctx, {
        content: claim,
        source: 'assertion',
        step,
        rule,
        dependsOn: [],
        emitDerivation: false,
        objectStatus: 'PROVED',
    });
}
function registerVariableClaim(ctx, claim, step) {
    return registerClaim(ctx, {
        content: claim,
        source: 'variable',
        step,
        rule: 'VARIABLE',
        dependsOn: [],
        emitDerivation: false,
        objectStatus: 'PROVED',
    });
}
function registerLemmaImportClaim(ctx, claim, step, hypotheses, imports) {
    return registerClaim(ctx, {
        content: claim,
        source: 'lemma_application',
        step,
        rule: 'BY_LEMMA',
        dependsOn: hypotheses,
        dependsOnIds: resolveClaimIds(ctx, hypotheses),
        imports,
        objectStatus: 'PROVED',
    });
}
function registerUnverifiedLemmaClaim(ctx, lemmaName, step) {
    return registerClaim(ctx, {
        content: `applied(${lemmaName})`,
        source: 'lemma_application',
        step,
        rule: 'BY_LEMMA',
        dependsOn: [],
        imports: [lemmaName],
        emitDerivation: false,
        objectStatus: 'UNVERIFIED',
    });
}
function registerContradictionClaim(ctx, step, rule) {
    const dependency = findContradictionDependency(ctx);
    return registerClaim(ctx, {
        content: 'contradiction',
        source: 'assertion',
        step,
        rule,
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
        objectStatus: 'PROVED',
    });
}
function registerDerivedClaim(ctx, input) {
    const builder = buildProofObjectInput(input.content, input.source, input.step, input.derivation, ctx);
    const graphValidation = validateProofObjectInput(builder);
    // Determine whether this claim is PROVED or UNVERIFIED
    const hasDerivedRule = input.derivation?.valid === true && !graphValidation;
    const objectStatus = hasDerivedRule ? 'PROVED' : 'UNVERIFIED';
    const result = graphValidation ?? input.derivation ?? {
        valid: true,
        rule: builder.rule,
        message: objectStatus === 'UNVERIFIED'
            ? `UNVERIFIED: '${input.content}' accepted without a derivation chain`
            : `${builder.rule} accepted`,
    };
    const claim = registerClaim(ctx, {
        ...builder,
        emitDerivation: hasDerivedRule,
        objectStatus,
    });
    applyDischargedScopes(ctx, builder.dischargedScopeIds);
    return { claim, result, objectStatus };
}
// Register a claim that is explicitly UNVERIFIED (no derivation is expected).
// Used for sorry placeholders and claims outside the kernel.
function registerUnverifiedClaim(ctx, claim, step, rule) {
    return registerClaim(ctx, {
        content: claim,
        source: 'assertion',
        step,
        rule,
        dependsOn: [],
        emitDerivation: false,
        objectStatus: 'UNVERIFIED',
    });
}
function makeProofObjectId(step, source, claim) {
    return `${source}:${step}:${normalizeName(claim)}`;
}
function makeDerivationNode(step, rule, inputIds, outputId, dischargedScopeIds) {
    return {
        id: `derivation:${step}:${normalizeName(outputId)}`,
        step,
        rule,
        inputIds,
        outputId,
        dischargedScopeIds: dischargedScopeIds && dischargedScopeIds.length > 0 ? uniqueIds(dischargedScopeIds) : undefined,
    };
}
function collectBaseFactIds(proofObjects, derivations) {
    const derived = new Set(derivations.map(node => node.outputId));
    return proofObjects.filter(object => !derived.has(object.id)).map(object => object.id);
}
function collectDerivedFactIds(derivations) {
    return [...new Set(derivations.map(node => node.outputId))];
}
function validateDerivationGraph(input) {
    const diagnostics = [];
    const objectMap = new Map(input.proofObjects.map(object => [object.id, object]));
    for (const node of input.derivations) {
        const output = objectMap.get(node.outputId);
        if (!output) {
            diagnostics.push({
                severity: 'error',
                message: `Derivation '${node.id}' references missing output proof object '${node.outputId}'`,
                step: node.step,
                rule: node.rule,
            });
            continue;
        }
        const inputs = node.inputIds
            .map(id => objectMap.get(id))
            .filter((object) => Boolean(object));
        if (inputs.length !== node.inputIds.length) {
            diagnostics.push({
                severity: 'error',
                message: `Derivation '${node.id}' references missing input proof objects`,
                step: node.step,
                rule: node.rule,
            });
            continue;
        }
        const error = validateDerivationNode(node, inputs, output, input.goal);
        if (error)
            diagnostics.push(error);
    }
    return diagnostics;
}
function validateDerivationNode(node, inputs, output, goal) {
    switch (node.rule) {
        case 'IMPLIES_ELIM':
            return validateImpliesElimNode(node, inputs, output);
        case 'AND_INTRO':
            return validateAndIntroNode(node, inputs, output);
        case 'AND_ELIM':
            return validateAndElimNode(node, inputs, output);
        case 'IFF_INTRO':
            return validateIffIntroNode(node, inputs, output);
        case 'IFF_ELIM':
            return validateIffElimNode(node, inputs, output);
        case 'SUBSET_INTRO':
            return validateSubsetIntroNode(node, inputs, output);
        case 'SUBSET_ELIM':
            return validateSubsetElimNode(node, inputs, output);
        case 'SUBSET_TRANS':
            return validateSubsetTransNode(node, inputs, output);
        case 'SUBSET_ANTISYM':
            return validateSubsetAntisymNode(node, inputs, output);
        case 'EQUALITY_REFL':
            return validateEqualityReflNode(node, inputs, output);
        case 'EQUALITY_SYMM':
            return validateEqualitySymmNode(node, inputs, output);
        case 'EQUALITY_TRANS':
            return validateEqualityTransNode(node, inputs, output);
        case 'ARITHMETIC_COMM':
            return validateArithmeticCommNode(node, inputs, output);
        case 'EQUALITY_SUBST':
            return validateEqualitySubstNode(node, inputs, output);
        case 'IMAGE_INTRO':
            return validateImageIntroNode(node, inputs, output);
        case 'PREIMAGE_INTRO':
            return validatePreimageIntroNode(node, inputs, output);
        case 'PREIMAGE_ELIM':
            return validatePreimageElimNode(node, inputs, output);
        case 'UNION_INTRO':
            return validateUnionIntroNode(node, inputs, output);
        case 'UNION_ELIM':
            return validateUnionElimNode(node, inputs, output);
        case 'SET_BUILDER_INTRO':
            return validateSetBuilderIntroNode(node, inputs, output);
        case 'INDEXED_UNION_INTRO':
            return validateIndexedUnionIntroNode(node, inputs, output);
        case 'INDEXED_UNION_ELIM':
            return validateIndexedUnionElimNode(node, inputs, output);
        case 'SET_MEMBERSHIP_EQ':
            return validateSetMembershipEqualityNode(node, inputs, output);
        case 'INTERSECTION_INTRO':
            return validateIntersectionIntroNode(node, inputs, output);
        case 'INTERSECTION_ELIM':
            return validateIntersectionElimNode(node, inputs, output);
        case 'FORALL_TYPED_ELIM':
            return validateForallTypedElimNode(node, inputs, output);
        case 'FORALL_TYPED_INTRO':
            return validateForallTypedIntroNode(node, inputs, output);
        case 'EXISTS_TYPED_INTRO':
            return validateExistsTypedIntroNode(node, inputs, output);
        case 'EXISTS_TYPED_ELIM':
            return validateExistsTypedElimNode(node, inputs, output);
        case 'EXISTS_UNIQUE_INTRO':
            return validateExistsUniqueIntroNode(node, inputs, output);
        case 'EXISTS_UNIQUE_ELIM':
            return validateExistsUniqueElimNode(node, inputs, output);
        case 'DIVIDES_INTRO':
            return validateDividesIntroNode(node, inputs, output);
        case 'FORALL_IN_ELIM':
            return validateForallInElimNode(node, inputs, output);
        case 'FORALL_IN_INTRO':
            return validateForallInIntroNode(node, inputs, output);
        case 'EXISTS_IN_INTRO':
            return validateExistsInIntroNode(node, inputs, output);
        case 'EXISTS_IN_ELIM':
            return validateExistsInElimNode(node, inputs, output);
        case 'IMPLIES_INTRO':
            return validateImpliesIntroNode(node, inputs, output, goal);
        case 'CONTRADICTION':
            return validateContradictionNode(node, inputs);
        case 'OR_INTRO_LEFT':
            return validateOrIntroLeftNode(node, inputs, output);
        case 'OR_INTRO_RIGHT':
            return validateOrIntroRightNode(node, inputs, output);
        case 'OR_ELIM':
            return validateOrElimNode(node, inputs, output);
        case 'NOT_INTRO':
            return validateNotIntroNode(node, inputs, output);
        case 'NOT_ELIM':
            return validateNotElimNode(node, inputs, output);
        case 'EX_FALSO':
            return validateExFalsoNode(node, inputs);
        case 'BY_LEMMA':
            return inputs.length === 0 && output.dependsOnIds.length > 0
                ? {
                    severity: 'error',
                    message: `Lemma derivation '${node.id}' has no resolved inputs`,
                    step: node.step,
                    rule: node.rule,
                }
                : null;
        default:
            return null;
    }
}
function validateImpliesElimNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `IMPLIES_ELIM '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const implication = inputs.find(input => parseImplicationProp(input.claim));
    const antecedent = inputs.find(input => !parseImplicationProp(input.claim));
    if (!implication || !antecedent) {
        return { severity: 'error', message: `IMPLIES_ELIM '${node.id}' must reference an implication and its antecedent`, step: node.step, rule: node.rule };
    }
    const pair = parseImplicationProp(implication.claim);
    if (!pair || !(0, propositions_1.sameProp)(pair[0], antecedent.claim) || !(0, propositions_1.sameProp)(pair[1], output.claim)) {
        return { severity: 'error', message: `IMPLIES_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateAndIntroNode(node, inputs, output) {
    const conjunction = parseConjunctionProp(output.claim);
    if (!conjunction) {
        return { severity: 'error', message: `AND_INTRO '${node.id}' must produce a conjunction`, step: node.step, rule: node.rule };
    }
    if (inputs.length < 2) {
        return { severity: 'error', message: `AND_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const leftOk = inputs.some(input => (0, propositions_1.sameProp)(input.claim, conjunction[0]));
    const rightOk = inputs.some(input => (0, propositions_1.sameProp)(input.claim, conjunction[1]));
    if (!leftOk || !rightOk) {
        return { severity: 'error', message: `AND_INTRO '${node.id}' inputs do not match '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateAndElimNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `AND_ELIM '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    const conjunction = parseConjunctionProp(inputs[0].claim);
    if (!conjunction || (!(0, propositions_1.sameProp)(conjunction[0], output.claim) && !(0, propositions_1.sameProp)(conjunction[1], output.claim))) {
        return { severity: 'error', message: `AND_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateIffIntroNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `IFF_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const iff = parseIffProp(output.claim);
    if (!iff) {
        return { severity: 'error', message: `IFF_INTRO '${node.id}' must produce a biconditional`, step: node.step, rule: node.rule };
    }
    const leftImpl = `${iff[0]} → ${iff[1]}`;
    const rightImpl = `${iff[1]} → ${iff[0]}`;
    const hasLeft = inputs.some(input => (0, propositions_1.sameProp)(input.claim, leftImpl));
    const hasRight = inputs.some(input => (0, propositions_1.sameProp)(input.claim, rightImpl));
    if (!hasLeft || !hasRight) {
        return { severity: 'error', message: `IFF_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateIffElimNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `IFF_ELIM '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const iffObj = inputs.find(input => parseIffProp(input.claim));
    const sideObj = inputs.find(input => !parseIffProp(input.claim));
    if (!iffObj || !sideObj) {
        return { severity: 'error', message: `IFF_ELIM '${node.id}' must reference a biconditional and one side`, step: node.step, rule: node.rule };
    }
    const iff = parseIffProp(iffObj.claim);
    const valid = ((0, propositions_1.sameProp)(sideObj.claim, iff[0]) && (0, propositions_1.sameProp)(output.claim, iff[1]))
        || ((0, propositions_1.sameProp)(sideObj.claim, iff[1]) && (0, propositions_1.sameProp)(output.claim, iff[0]));
    if (!valid) {
        return { severity: 'error', message: `IFF_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateSubsetIntroNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `SUBSET_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const target = parseSubsetProp(output.claim);
    if (!target) {
        return { severity: 'error', message: `SUBSET_INTRO '${node.id}' must produce a subset claim`, step: node.step, rule: node.rule };
    }
    const membershipInput = inputs.find(input => {
        const membership = parseMembershipProp(input.claim);
        return membership !== null && (0, propositions_1.sameProp)(membership.set, target.left);
    });
    if (!membershipInput) {
        return { severity: 'error', message: `SUBSET_INTRO '${node.id}' must reference a witness membership assumption`, step: node.step, rule: node.rule };
    }
    const membership = parseMembershipProp(membershipInput.claim);
    if (!membership) {
        return { severity: 'error', message: `SUBSET_INTRO '${node.id}' has malformed witness membership`, step: node.step, rule: node.rule };
    }
    const bodyClaim = `${membership.element} ∈ ${target.right}`;
    const hasBody = inputs.some(input => (0, propositions_1.sameProp)(input.claim, bodyClaim));
    if (!hasBody) {
        return { severity: 'error', message: `SUBSET_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    if (!node.dischargedScopeIds || node.dischargedScopeIds.length === 0) {
        return { severity: 'error', message: `SUBSET_INTRO '${node.id}' does not discharge a witness scope`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateSubsetElimNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `SUBSET_ELIM '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const membership = inputs.find(input => parseMembershipProp(input.claim));
    const subset = inputs.find(input => parseSubsetProp(input.claim));
    if (!membership || !subset) {
        return { severity: 'error', message: `SUBSET_ELIM '${node.id}' must reference membership and subset inputs`, step: node.step, rule: node.rule };
    }
    const membershipParts = parseMembershipProp(membership.claim);
    const subsetParts = parseSubsetProp(subset.claim);
    const outputParts = parseMembershipProp(output.claim);
    if (!membershipParts || !subsetParts || !outputParts) {
        return { severity: 'error', message: `SUBSET_ELIM '${node.id}' has malformed set-theoretic inputs`, step: node.step, rule: node.rule };
    }
    if (!(0, propositions_1.sameProp)(membershipParts.element, outputParts.element) ||
        !(0, propositions_1.sameProp)(membershipParts.set, subsetParts.left) ||
        !(0, propositions_1.sameProp)(outputParts.set, subsetParts.right)) {
        return { severity: 'error', message: `SUBSET_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateSubsetTransNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `SUBSET_TRANS '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const left = parseSubsetProp(inputs[0].claim);
    const right = parseSubsetProp(inputs[1].claim);
    const target = parseSubsetProp(output.claim);
    if (!left || !right || !target) {
        return { severity: 'error', message: `SUBSET_TRANS '${node.id}' has malformed subset inputs`, step: node.step, rule: node.rule };
    }
    const valid = ((0, propositions_1.sameProp)(left.right, right.left)
        && (0, propositions_1.sameProp)(target.left, left.left)
        && (0, propositions_1.sameProp)(target.right, right.right)) || ((0, propositions_1.sameProp)(right.right, left.left)
        && (0, propositions_1.sameProp)(target.left, right.left)
        && (0, propositions_1.sameProp)(target.right, left.right));
    if (!valid) {
        return { severity: 'error', message: `SUBSET_TRANS '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateSubsetAntisymNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `SUBSET_ANTISYM '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const left = parseSubsetProp(inputs[0].claim);
    const right = parseSubsetProp(inputs[1].claim);
    const equality = parseEqualityProp(output.claim);
    if (!left || !right || !equality) {
        return { severity: 'error', message: `SUBSET_ANTISYM '${node.id}' has malformed subset/equality inputs`, step: node.step, rule: node.rule };
    }
    const valid = ((0, propositions_1.sameProp)(left.left, equality.left) &&
        (0, propositions_1.sameProp)(left.right, equality.right) &&
        (0, propositions_1.sameProp)(right.left, equality.right) &&
        (0, propositions_1.sameProp)(right.right, equality.left)) || ((0, propositions_1.sameProp)(left.left, equality.right) &&
        (0, propositions_1.sameProp)(left.right, equality.left) &&
        (0, propositions_1.sameProp)(right.left, equality.left) &&
        (0, propositions_1.sameProp)(right.right, equality.right));
    if (!valid) {
        return { severity: 'error', message: `SUBSET_ANTISYM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateEqualityReflNode(node, inputs, output) {
    if (inputs.length !== 0) {
        return { severity: 'error', message: `EQUALITY_REFL '${node.id}' requires 0 inputs`, step: node.step, rule: node.rule };
    }
    const equality = parseEqualityProp(output.claim);
    if (!equality || !(0, propositions_1.sameProp)(equality.left, equality.right)) {
        return { severity: 'error', message: `EQUALITY_REFL '${node.id}' must produce x = x`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateEqualitySymmNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `EQUALITY_SYMM '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    const source = parseEqualityProp(inputs[0].claim);
    const target = parseEqualityProp(output.claim);
    if (!source || !target ||
        !(0, propositions_1.sameProp)(source.left, target.right) ||
        !(0, propositions_1.sameProp)(source.right, target.left)) {
        return { severity: 'error', message: `EQUALITY_SYMM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateEqualityTransNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `EQUALITY_TRANS '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    if (!supportsEqualityTransitivity(inputs[0].claim, inputs[1].claim, output.claim)) {
        return { severity: 'error', message: `EQUALITY_TRANS '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateArithmeticCommNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `ARITHMETIC_COMM '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    if (!supportsArithmeticCommutativeEquality(inputs[0].claim, output.claim)) {
        return { severity: 'error', message: `ARITHMETIC_COMM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateEqualitySubstNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `EQUALITY_SUBST '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const equality = inputs.find(input => parseEqualityProp(input.claim));
    const membership = inputs.find(input => parseMembershipProp(input.claim));
    if (!equality || !membership) {
        return { severity: 'error', message: `EQUALITY_SUBST '${node.id}' must reference equality and membership inputs`, step: node.step, rule: node.rule };
    }
    if (!supportsEqualitySubstitution(equality.claim, membership.claim, output.claim)) {
        return { severity: 'error', message: `EQUALITY_SUBST '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateImageIntroNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `IMAGE_INTRO '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    const inputParts = parseMembershipProp(inputs[0].claim);
    const outputParts = parseMembershipProp(output.claim);
    if (!inputParts || !outputParts) {
        return { severity: 'error', message: `IMAGE_INTRO '${node.id}' has malformed membership inputs`, step: node.step, rule: node.rule };
    }
    const image = parseImageTerm(outputParts.set);
    const app = parseFunctionApplicationTerm(outputParts.element);
    if (!image || !app) {
        return { severity: 'error', message: `IMAGE_INTRO '${node.id}' must derive image membership from a source membership`, step: node.step, rule: node.rule };
    }
    if (!(0, propositions_1.sameProp)(inputParts.element, app.arg) || !(0, propositions_1.sameProp)(inputParts.set, image.set) || !(0, propositions_1.sameProp)(app.fn, image.fn)) {
        return { severity: 'error', message: `IMAGE_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validatePreimageIntroNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `PREIMAGE_INTRO '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    const inputParts = parseMembershipProp(inputs[0].claim);
    const outputParts = parseMembershipProp(output.claim);
    if (!inputParts || !outputParts) {
        return { severity: 'error', message: `PREIMAGE_INTRO '${node.id}' has malformed membership inputs`, step: node.step, rule: node.rule };
    }
    const app = parseFunctionApplicationTerm(inputParts.element);
    const preimage = parsePreimageTerm(outputParts.set);
    if (!app || !preimage) {
        return { severity: 'error', message: `PREIMAGE_INTRO '${node.id}' must derive preimage membership from function application membership`, step: node.step, rule: node.rule };
    }
    if (!(0, propositions_1.sameProp)(app.fn, preimage.fn) || !(0, propositions_1.sameProp)(app.arg, outputParts.element) || !(0, propositions_1.sameProp)(inputParts.set, preimage.set)) {
        return { severity: 'error', message: `PREIMAGE_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validatePreimageElimNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `PREIMAGE_ELIM '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    const inputParts = parseMembershipProp(inputs[0].claim);
    const outputParts = parseMembershipProp(output.claim);
    if (!inputParts || !outputParts) {
        return { severity: 'error', message: `PREIMAGE_ELIM '${node.id}' has malformed membership inputs`, step: node.step, rule: node.rule };
    }
    const preimage = parsePreimageTerm(inputParts.set);
    const app = parseFunctionApplicationTerm(outputParts.element);
    if (!preimage || !app) {
        return { severity: 'error', message: `PREIMAGE_ELIM '${node.id}' must consume preimage membership and produce function application membership`, step: node.step, rule: node.rule };
    }
    if (!(0, propositions_1.sameProp)(preimage.fn, app.fn) || !(0, propositions_1.sameProp)(inputParts.element, app.arg) || !(0, propositions_1.sameProp)(preimage.set, outputParts.set)) {
        return { severity: 'error', message: `PREIMAGE_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateUnionIntroNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `UNION_INTRO '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    const outputParts = parseMembershipProp(output.claim);
    const inputParts = parseMembershipProp(inputs[0].claim);
    if (!outputParts || !inputParts) {
        return { severity: 'error', message: `UNION_INTRO '${node.id}' has malformed membership inputs`, step: node.step, rule: node.rule };
    }
    const union = parseBinarySetProp(outputParts.set, '∪');
    if (!union) {
        return { severity: 'error', message: `UNION_INTRO '${node.id}' must produce union membership`, step: node.step, rule: node.rule };
    }
    if (!(0, propositions_1.sameProp)(outputParts.element, inputParts.element) ||
        !((0, propositions_1.sameProp)(inputParts.set, union[0]) || (0, propositions_1.sameProp)(inputParts.set, union[1]))) {
        return { severity: 'error', message: `UNION_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateUnionElimNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `UNION_ELIM '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    const inputParts = parseMembershipProp(inputs[0].claim);
    const outputDisjunction = parseDisjunctionProp(output.claim);
    if (!inputParts || !outputDisjunction) {
        return { severity: 'error', message: `UNION_ELIM '${node.id}' must reference union membership and produce a disjunction`, step: node.step, rule: node.rule };
    }
    const union = parseBinarySetProp(inputParts.set, '∪');
    const leftMembership = parseMembershipProp(outputDisjunction[0]);
    const rightMembership = parseMembershipProp(outputDisjunction[1]);
    if (!union || !leftMembership || !rightMembership) {
        return { severity: 'error', message: `UNION_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    if (!(0, propositions_1.sameProp)(inputParts.element, leftMembership.element)
        || !(0, propositions_1.sameProp)(inputParts.element, rightMembership.element)
        || !(0, propositions_1.sameProp)(leftMembership.set, union[0])
        || !(0, propositions_1.sameProp)(rightMembership.set, union[1])) {
        return { severity: 'error', message: `UNION_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateSetBuilderIntroNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `SET_BUILDER_INTRO '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    if (!resolveSetBuilderIntroDependency(output.claim, inputs.map(input => input.claim))) {
        return { severity: 'error', message: `SET_BUILDER_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateIndexedUnionIntroNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `INDEXED_UNION_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    if (!resolveIndexedUnionIntroDependency(output.claim, inputs.map(input => input.claim))) {
        return { severity: 'error', message: `INDEXED_UNION_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateIndexedUnionElimNode(node, inputs, output) {
    if (inputs.length !== 3) {
        return { severity: 'error', message: `INDEXED_UNION_ELIM '${node.id}' requires 3 inputs`, step: node.step, rule: node.rule };
    }
    const unionMembership = inputs.find(input => {
        const membership = parseMembershipProp(input.claim);
        return membership && parseIndexedUnionTerm(membership.set);
    });
    const assumptions = inputs.filter(input => parseMembershipProp(input.claim) && input.source === 'assumption');
    if (!unionMembership || assumptions.length < 2) {
        return { severity: 'error', message: `INDEXED_UNION_ELIM '${node.id}' must reference indexed-union membership plus witness assumptions`, step: node.step, rule: node.rule };
    }
    const unionProp = parseMembershipProp(unionMembership.claim);
    if (!unionProp) {
        return { severity: 'error', message: `INDEXED_UNION_ELIM '${node.id}' has malformed indexed-union membership`, step: node.step, rule: node.rule };
    }
    const indexedUnion = parseIndexedUnionTerm(unionProp.set);
    if (!indexedUnion) {
        return { severity: 'error', message: `INDEXED_UNION_ELIM '${node.id}' must consume indexed-union membership`, step: node.step, rule: node.rule };
    }
    const scope = resolveIndexedUnionElimScopeFromInputs(indexedUnion, unionProp.element, assumptions.map(input => input.claim), output.claim);
    if (!scope) {
        return { severity: 'error', message: `INDEXED_UNION_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateSetMembershipEqualityNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `SET_MEMBERSHIP_EQ '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    if (!resolveSetEqualityScopeFromInputs(output.claim, inputs.map(input => input.claim))) {
        return { severity: 'error', message: `SET_MEMBERSHIP_EQ '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateIntersectionIntroNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `INTERSECTION_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const outputParts = parseMembershipProp(output.claim);
    if (!outputParts) {
        return { severity: 'error', message: `INTERSECTION_INTRO '${node.id}' must produce membership`, step: node.step, rule: node.rule };
    }
    const intersection = parseBinarySetProp(outputParts.set, '∩');
    if (!intersection) {
        return { severity: 'error', message: `INTERSECTION_INTRO '${node.id}' must produce intersection membership`, step: node.step, rule: node.rule };
    }
    const memberships = inputs.map(input => parseMembershipProp(input.claim));
    if (memberships.some(item => !item)) {
        return { severity: 'error', message: `INTERSECTION_INTRO '${node.id}' has malformed membership inputs`, step: node.step, rule: node.rule };
    }
    const [left, right] = memberships;
    const okay = (0, propositions_1.sameProp)(left.element, outputParts.element)
        && (0, propositions_1.sameProp)(right.element, outputParts.element)
        && (((0, propositions_1.sameProp)(left.set, intersection[0]) && (0, propositions_1.sameProp)(right.set, intersection[1]))
            || ((0, propositions_1.sameProp)(left.set, intersection[1]) && (0, propositions_1.sameProp)(right.set, intersection[0])));
    if (!okay) {
        return { severity: 'error', message: `INTERSECTION_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateIntersectionElimNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `INTERSECTION_ELIM '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    const inputParts = parseMembershipProp(inputs[0].claim);
    const outputParts = parseMembershipProp(output.claim);
    if (!inputParts || !outputParts) {
        return { severity: 'error', message: `INTERSECTION_ELIM '${node.id}' has malformed membership inputs`, step: node.step, rule: node.rule };
    }
    const intersection = parseBinarySetProp(inputParts.set, '∩');
    if (!intersection) {
        return { severity: 'error', message: `INTERSECTION_ELIM '${node.id}' must consume intersection membership`, step: node.step, rule: node.rule };
    }
    if (!(0, propositions_1.sameProp)(inputParts.element, outputParts.element) ||
        !((0, propositions_1.sameProp)(outputParts.set, intersection[0]) || (0, propositions_1.sameProp)(outputParts.set, intersection[1]))) {
        return { severity: 'error', message: `INTERSECTION_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateForallTypedElimNode(node, inputs, output) {
    if (inputs.length < 2) {
        return { severity: 'error', message: `FORALL_TYPED_ELIM '${node.id}' requires at least 2 inputs`, step: node.step, rule: node.rule };
    }
    const quantified = inputs.find(input => parseTypedQuantifierProp(input.claim, 'forall'));
    const witnesses = inputs.filter(input => parseTypedVariableProp(input.claim));
    if (!quantified || witnesses.length === 0) {
        return { severity: 'error', message: `FORALL_TYPED_ELIM '${node.id}' must reference a typed universal claim and typed witness inputs`, step: node.step, rule: node.rule };
    }
    const path = resolveTypedForallElimPathFromInputs(quantified.claim, witnesses.map(witness => witness.claim), output.claim);
    if (!path) {
        return { severity: 'error', message: `FORALL_TYPED_ELIM '${node.id}' has malformed typed-quantifier inputs`, step: node.step, rule: node.rule };
    }
    if (!(0, propositions_1.sameProp)(path.result, output.claim)) {
        return { severity: 'error', message: `FORALL_TYPED_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateForallTypedIntroNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `FORALL_TYPED_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const quantifier = parseTypedQuantifierProp(output.claim, 'forall');
    const witness = inputs.find(input => parseTypedVariableProp(input.claim) && input.source === 'variable');
    const bodyInput = inputs.find(input => input.id !== witness?.id);
    if (!quantifier || !witness || !bodyInput) {
        return { severity: 'error', message: `FORALL_TYPED_INTRO '${node.id}' must produce a typed universal claim from a typed witness scope`, step: node.step, rule: node.rule };
    }
    const witnessProp = parseTypedVariableProp(witness.claim);
    if (!witnessProp) {
        return { severity: 'error', message: `FORALL_TYPED_INTRO '${node.id}' has malformed typed witness`, step: node.step, rule: node.rule };
    }
    const instantiated = instantiateBoundedQuantifier({ variable: quantifier.variable, body: quantifier.body }, witnessProp.variable);
    if (!sameTypeDomain(witnessProp.domain, quantifier.domain) || !instantiated || !(0, propositions_1.sameProp)(instantiated, bodyInput.claim)) {
        return { severity: 'error', message: `FORALL_TYPED_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    if (!isFreshScopedWitness(witnessProp.variable, quantifier, output.claim)) {
        return { severity: 'error', message: `FORALL_TYPED_INTRO '${node.id}' does not use a fresh typed witness scope`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateExistsTypedIntroNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `EXISTS_TYPED_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const quantifier = parseTypedQuantifierProp(output.claim, 'exists');
    const witness = inputs.find(input => parseTypedVariableProp(input.claim));
    const bodyInput = inputs.find(input => input.id !== witness?.id);
    if (!quantifier || !witness || !bodyInput) {
        return { severity: 'error', message: `EXISTS_TYPED_INTRO '${node.id}' must produce a typed existential claim from a typed witness`, step: node.step, rule: node.rule };
    }
    const witnessProp = parseTypedVariableProp(witness.claim);
    if (!witnessProp) {
        return { severity: 'error', message: `EXISTS_TYPED_INTRO '${node.id}' has malformed typed witness`, step: node.step, rule: node.rule };
    }
    const instantiated = instantiateBoundedQuantifier({ variable: quantifier.variable, body: quantifier.body }, witnessProp.variable);
    const matchesInstantiatedBody = instantiated
        && ((0, propositions_1.sameProp)(instantiated, bodyInput.claim) || supportsArithmeticCommutativeEquality(bodyInput.claim, instantiated));
    if (!sameTypeDomain(witnessProp.domain, quantifier.domain) || !matchesInstantiatedBody) {
        return { severity: 'error', message: `EXISTS_TYPED_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateExistsTypedElimNode(node, inputs, output) {
    if (inputs.length !== 3) {
        return { severity: 'error', message: `EXISTS_TYPED_ELIM '${node.id}' requires 3 inputs`, step: node.step, rule: node.rule };
    }
    const existential = inputs.find(input => parseTypedQuantifierProp(input.claim, 'exists'));
    const witnesses = inputs.filter(input => parseTypedVariableProp(input.claim) && input.source === 'variable');
    if (!existential || witnesses.length < 1) {
        return { severity: 'error', message: `EXISTS_TYPED_ELIM '${node.id}' must reference a typed existential claim plus typed witness scope`, step: node.step, rule: node.rule };
    }
    const quantifier = parseTypedQuantifierProp(existential.claim, 'exists');
    if (!quantifier) {
        return { severity: 'error', message: `EXISTS_TYPED_ELIM '${node.id}' has malformed typed existential input`, step: node.step, rule: node.rule };
    }
    const scope = resolveExistsTypedElimScopeFromInputs(quantifier, inputs.map(input => input.claim), output.claim);
    if (!scope) {
        return { severity: 'error', message: `EXISTS_TYPED_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateExistsUniqueIntroNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `EXISTS_UNIQUE_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const lowered = lowerUniqueExistenceClaim(output.claim);
    if (!lowered) {
        return { severity: 'error', message: `EXISTS_UNIQUE_INTRO '${node.id}' must produce a unique-existence claim`, step: node.step, rule: node.rule };
    }
    const hasExistence = inputs.some(input => (0, propositions_1.sameProp)(input.claim, lowered.existenceClaim));
    const hasUniqueness = inputs.some(input => (0, propositions_1.sameProp)(input.claim, lowered.uniquenessClaim));
    if (!hasExistence || !hasUniqueness) {
        return { severity: 'error', message: `EXISTS_UNIQUE_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateExistsUniqueElimNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `EXISTS_UNIQUE_ELIM '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    const lowered = lowerUniqueExistenceClaim(inputs[0].claim);
    if (!lowered || (!(0, propositions_1.sameProp)(output.claim, lowered.existenceClaim) && !(0, propositions_1.sameProp)(output.claim, lowered.uniquenessClaim))) {
        return { severity: 'error', message: `EXISTS_UNIQUE_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateDividesIntroNode(node, inputs, output) {
    if (inputs.length !== 1) {
        return { severity: 'error', message: `DIVIDES_INTRO '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    }
    if (!supportsDividesFromEquality(inputs[0].claim, output.claim)) {
        return { severity: 'error', message: `DIVIDES_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateForallInElimNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `FORALL_IN_ELIM '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const quantified = inputs.find(input => parseBoundedQuantifierProp(input.claim, 'forall'));
    const membership = inputs.find(input => parseMembershipProp(input.claim));
    if (!quantified || !membership) {
        return { severity: 'error', message: `FORALL_IN_ELIM '${node.id}' must reference a bounded universal claim and a witness membership`, step: node.step, rule: node.rule };
    }
    const quantifier = parseBoundedQuantifierProp(quantified.claim, 'forall');
    const witness = parseMembershipProp(membership.claim);
    if (!quantifier || !witness) {
        return { severity: 'error', message: `FORALL_IN_ELIM '${node.id}' has malformed bounded-quantifier inputs`, step: node.step, rule: node.rule };
    }
    const instantiated = instantiateBoundedQuantifier(quantifier, witness.element);
    if (!(0, propositions_1.sameProp)(quantifier.set, witness.set) || !instantiated || !(0, propositions_1.sameProp)(instantiated, output.claim)) {
        return { severity: 'error', message: `FORALL_IN_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateForallInIntroNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `FORALL_IN_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const quantifier = parseBoundedQuantifierProp(output.claim, 'forall');
    const membership = inputs.find(input => parseMembershipProp(input.claim) && input.source === 'assumption');
    const bodyInput = inputs.find(input => input.id !== membership?.id);
    if (!quantifier || !membership || !bodyInput) {
        return { severity: 'error', message: `FORALL_IN_INTRO '${node.id}' must produce a bounded universal claim from witness assumptions`, step: node.step, rule: node.rule };
    }
    const membershipProp = parseMembershipProp(membership.claim);
    if (!membershipProp) {
        return { severity: 'error', message: `FORALL_IN_INTRO '${node.id}' has malformed witness membership`, step: node.step, rule: node.rule };
    }
    const instantiated = instantiateBoundedQuantifier(quantifier, membershipProp.element);
    if (!(0, propositions_1.sameProp)(membershipProp.set, quantifier.set) || !instantiated || !(0, propositions_1.sameProp)(instantiated, bodyInput.claim)) {
        return { severity: 'error', message: `FORALL_IN_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    if (!isFreshScopedWitness(membershipProp.element, quantifier, output.claim)) {
        return { severity: 'error', message: `FORALL_IN_INTRO '${node.id}' does not use a fresh witness scope`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateExistsInIntroNode(node, inputs, output) {
    if (inputs.length !== 2) {
        return { severity: 'error', message: `EXISTS_IN_INTRO '${node.id}' requires 2 inputs`, step: node.step, rule: node.rule };
    }
    const quantified = parseBoundedQuantifierProp(output.claim, 'exists');
    const membership = inputs.find(input => parseMembershipProp(input.claim));
    if (!quantified || !membership) {
        return { severity: 'error', message: `EXISTS_IN_INTRO '${node.id}' must produce a bounded existential claim from witness inputs`, step: node.step, rule: node.rule };
    }
    const witness = parseMembershipProp(membership.claim);
    const bodyInput = inputs.find(input => input.id !== membership.id);
    if (!witness || !bodyInput) {
        return { severity: 'error', message: `EXISTS_IN_INTRO '${node.id}' has malformed witness inputs`, step: node.step, rule: node.rule };
    }
    const instantiated = instantiateBoundedQuantifier(quantified, witness.element);
    if (!(0, propositions_1.sameProp)(quantified.set, witness.set) || !instantiated || !(0, propositions_1.sameProp)(instantiated, bodyInput.claim)) {
        return { severity: 'error', message: `EXISTS_IN_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateExistsInElimNode(node, inputs, output) {
    if (inputs.length !== 3) {
        return { severity: 'error', message: `EXISTS_IN_ELIM '${node.id}' requires 3 inputs`, step: node.step, rule: node.rule };
    }
    const existential = inputs.find(input => parseBoundedQuantifierProp(input.claim, 'exists'));
    const memberships = inputs.filter(input => parseMembershipProp(input.claim) && input.source === 'assumption');
    if (!existential || memberships.length < 2) {
        return { severity: 'error', message: `EXISTS_IN_ELIM '${node.id}' must reference an existential claim plus witness membership and body assumptions`, step: node.step, rule: node.rule };
    }
    const quantifier = parseBoundedQuantifierProp(existential.claim, 'exists');
    if (!quantifier) {
        return { severity: 'error', message: `EXISTS_IN_ELIM '${node.id}' has malformed existential input`, step: node.step, rule: node.rule };
    }
    const scope = resolveExistsElimScopeFromInputs(quantifier, memberships.map(input => input.claim), output.claim);
    if (!scope) {
        return { severity: 'error', message: `EXISTS_IN_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateImpliesIntroNode(node, inputs, output, goal) {
    if (inputs.length < 1) {
        return { severity: 'error', message: `IMPLIES_INTRO '${node.id}' requires proof inputs`, step: node.step, rule: node.rule };
    }
    const implication = parseImplicationProp(output.claim) ?? (goal ? parseImplicationProp(goal) : null);
    if (!implication) {
        return { severity: 'error', message: `IMPLIES_INTRO '${node.id}' must produce an implication`, step: node.step, rule: node.rule };
    }
    const assumption = inputs.find(input => input.source === 'assumption' && (0, propositions_1.sameProp)(input.claim, implication[0]));
    const consequent = inputs.find(input => (0, propositions_1.sameProp)(input.claim, implication[1]));
    if (!assumption || !consequent) {
        return { severity: 'error', message: `IMPLIES_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateContradictionNode(node, inputs) {
    if (inputs.length < 2) {
        return { severity: 'error', message: `CONTRADICTION '${node.id}' requires conflicting inputs`, step: node.step, rule: node.rule };
    }
    const hasPair = inputs.some(input => inputs.some(other => input.id !== other.id && (0, propositions_1.sameProp)(negateProp(input.claim), other.claim)));
    if (!hasPair) {
        return { severity: 'error', message: `CONTRADICTION '${node.id}' has no contradictory input pair`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateOrIntroLeftNode(node, inputs, output) {
    if (inputs.length !== 1)
        return { severity: 'error', message: `OR_INTRO_LEFT '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    const disj = parseDisjunctionProp(output.claim);
    if (!disj)
        return { severity: 'error', message: `OR_INTRO_LEFT '${node.id}' must produce a disjunction`, step: node.step, rule: node.rule };
    if (!(0, propositions_1.sameProp)(inputs[0].claim, disj[0])) {
        return { severity: 'error', message: `OR_INTRO_LEFT '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateOrIntroRightNode(node, inputs, output) {
    if (inputs.length !== 1)
        return { severity: 'error', message: `OR_INTRO_RIGHT '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    const disj = parseDisjunctionProp(output.claim);
    if (!disj)
        return { severity: 'error', message: `OR_INTRO_RIGHT '${node.id}' must produce a disjunction`, step: node.step, rule: node.rule };
    if (!(0, propositions_1.sameProp)(inputs[0].claim, disj[1])) {
        return { severity: 'error', message: `OR_INTRO_RIGHT '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateOrElimNode(node, inputs, output) {
    if (inputs.length !== 3)
        return { severity: 'error', message: `OR_ELIM '${node.id}' requires 3 inputs`, step: node.step, rule: node.rule };
    const disjObj = inputs.find(i => parseDisjunctionProp(i.claim));
    if (!disjObj)
        return { severity: 'error', message: `OR_ELIM '${node.id}' must have a disjunction input`, step: node.step, rule: node.rule };
    const disj = parseDisjunctionProp(disjObj.claim);
    const leftImpl = inputs.find(i => { const p = parseImplicationProp(i.claim); return p && (0, propositions_1.sameProp)(p[0], disj[0]) && (0, propositions_1.sameProp)(p[1], output.claim); });
    const rightImpl = inputs.find(i => { const p = parseImplicationProp(i.claim); return p && (0, propositions_1.sameProp)(p[0], disj[1]) && (0, propositions_1.sameProp)(p[1], output.claim); });
    if (!leftImpl || !rightImpl) {
        return { severity: 'error', message: `OR_ELIM '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateNotIntroNode(node, inputs, output) {
    if (inputs.length < 2)
        return { severity: 'error', message: `NOT_INTRO '${node.id}' requires assumption and contradiction inputs`, step: node.step, rule: node.rule };
    const inner = extractNegand(output.claim);
    if (!inner)
        return { severity: 'error', message: `NOT_INTRO '${node.id}' must produce a negation`, step: node.step, rule: node.rule };
    const assumption = inputs.find(i => i.source === 'assumption' && (0, propositions_1.sameProp)(i.claim, inner));
    const falsum = inputs.find(i => (0, propositions_1.sameProp)(i.claim, '⊥') || (0, propositions_1.sameProp)(i.claim, 'contradiction'));
    if (!assumption || !falsum) {
        return { severity: 'error', message: `NOT_INTRO '${node.id}' does not justify '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateNotElimNode(node, inputs, output) {
    if (inputs.length !== 1)
        return { severity: 'error', message: `NOT_ELIM '${node.id}' requires 1 input`, step: node.step, rule: node.rule };
    const doubleNeg = inputs[0].claim;
    const inner = extractNegand(doubleNeg);
    const inner2 = inner ? extractNegand(inner) : null;
    if (!inner2 || !(0, propositions_1.sameProp)(inner2, output.claim)) {
        return { severity: 'error', message: `NOT_ELIM '${node.id}' input must be ¬¬P for output P, got '${doubleNeg}' ⊢ '${output.claim}'`, step: node.step, rule: node.rule };
    }
    return null;
}
function validateExFalsoNode(node, inputs) {
    if (inputs.length !== 1)
        return { severity: 'error', message: `EX_FALSO '${node.id}' requires 1 input (⊥)`, step: node.step, rule: node.rule };
    if (!(0, propositions_1.sameProp)(inputs[0].claim, '⊥') && !(0, propositions_1.sameProp)(inputs[0].claim, 'contradiction')) {
        return { severity: 'error', message: `EX_FALSO '${node.id}' input must be ⊥ (contradiction)`, step: node.step, rule: node.rule };
    }
    return null;
}
function buildProofObjectInput(claim, source, step, derivation, ctx) {
    if (!derivation?.valid) {
        return {
            content: claim,
            source,
            step,
            rule: derivation?.rule ?? 'STRUCTURAL',
            scopeIds: currentScopeIds(ctx),
            dependsOn: [],
        };
    }
    switch (derivation.rule) {
        case 'PREMISE':
            return buildPremiseProofObject(claim, source, step, ctx);
        case 'IMPLIES_ELIM':
            return buildImpliesElimProofObject(claim, source, step, ctx);
        case 'AND_INTRO':
            return buildAndIntroProofObject(claim, source, step, ctx);
        case 'AND_ELIM':
            return buildAndElimProofObject(claim, source, step, ctx);
        case 'IFF_INTRO':
            return buildIffIntroProofObject(claim, source, step, ctx);
        case 'IFF_ELIM':
            return buildIffElimProofObject(claim, source, step, ctx);
        case 'SUBSET_INTRO':
            return buildSubsetIntroProofObject(claim, source, step, ctx);
        case 'SUBSET_ELIM':
            return buildSubsetElimProofObject(claim, source, step, ctx);
        case 'SUBSET_TRANS':
            return buildSubsetTransProofObject(claim, source, step, ctx);
        case 'SUBSET_ANTISYM':
            return buildSubsetAntisymProofObject(claim, source, step, ctx);
        case 'EQUALITY_REFL':
            return buildEqualityReflProofObject(claim, source, step);
        case 'EQUALITY_SYMM':
            return buildEqualitySymmProofObject(claim, source, step, ctx);
        case 'EQUALITY_TRANS':
            return buildEqualityTransProofObject(claim, source, step, ctx);
        case 'ARITHMETIC_COMM':
            return buildArithmeticCommProofObject(claim, source, step, ctx);
        case 'EQUALITY_SUBST':
            return buildEqualitySubstProofObject(claim, source, step, ctx);
        case 'IMAGE_INTRO':
            return buildImageIntroProofObject(claim, source, step, ctx);
        case 'PREIMAGE_INTRO':
            return buildPreimageIntroProofObject(claim, source, step, ctx);
        case 'PREIMAGE_ELIM':
            return buildPreimageElimProofObject(claim, source, step, ctx);
        case 'UNION_INTRO':
            return buildUnionIntroProofObject(claim, source, step, ctx);
        case 'UNION_ELIM':
            return buildUnionElimProofObject(claim, source, step, ctx);
        case 'SET_BUILDER_INTRO':
            return buildSetBuilderIntroProofObject(claim, source, step, ctx);
        case 'INDEXED_UNION_INTRO':
            return buildIndexedUnionIntroProofObject(claim, source, step, ctx);
        case 'INDEXED_UNION_ELIM':
            return buildIndexedUnionElimProofObject(claim, source, step, ctx);
        case 'SET_MEMBERSHIP_EQ':
            return buildSetMembershipEqualityProofObject(claim, source, step, ctx);
        case 'INTERSECTION_INTRO':
            return buildIntersectionIntroProofObject(claim, source, step, ctx);
        case 'INTERSECTION_ELIM':
            return buildIntersectionElimProofObject(claim, source, step, ctx);
        case 'FORALL_TYPED_ELIM':
            return buildForallTypedElimProofObject(claim, source, step, ctx);
        case 'FORALL_TYPED_INTRO':
            return buildForallTypedIntroProofObject(claim, source, step, ctx);
        case 'EXISTS_TYPED_INTRO':
            return buildExistsTypedIntroProofObject(claim, source, step, ctx);
        case 'EXISTS_TYPED_ELIM':
            return buildExistsTypedElimProofObject(claim, source, step, ctx);
        case 'EXISTS_UNIQUE_INTRO':
            return buildExistsUniqueIntroProofObject(claim, source, step, ctx);
        case 'EXISTS_UNIQUE_ELIM':
            return buildExistsUniqueElimProofObject(claim, source, step, ctx);
        case 'DIVIDES_INTRO':
            return buildDividesIntroProofObject(claim, source, step, ctx);
        case 'FORALL_IN_ELIM':
            return buildForallInElimProofObject(claim, source, step, ctx);
        case 'FORALL_IN_INTRO':
            return buildForallInIntroProofObject(claim, source, step, ctx);
        case 'EXISTS_IN_INTRO':
            return buildExistsInIntroProofObject(claim, source, step, ctx);
        case 'EXISTS_IN_ELIM':
            return buildExistsInElimProofObject(claim, source, step, ctx);
        case 'IMPLIES_INTRO':
            return buildImpliesIntroProofObject(claim, source, step, ctx);
        case 'CONTRADICTION':
            return buildContradictionDischargeProofObject(claim, source, step, ctx);
        case 'OR_INTRO_LEFT':
            return buildOrIntroProofObject(claim, source, step, ctx, 'left');
        case 'OR_INTRO_RIGHT':
            return buildOrIntroProofObject(claim, source, step, ctx, 'right');
        case 'OR_ELIM':
            return buildOrElimProofObject(claim, source, step, ctx);
        case 'NOT_INTRO':
            return buildNotIntroProofObject(claim, source, step, ctx);
        case 'NOT_ELIM':
            return buildNotElimProofObject(claim, source, step, ctx);
        case 'EX_FALSO':
            return buildExFalsoProofObject(claim, source, step, ctx);
        default:
            return {
                content: claim,
                source,
                step,
                rule: derivation.rule,
                scopeIds: currentScopeIds(ctx),
                dependsOn: [],
            };
    }
}
function buildPremiseProofObject(claim, source, step, ctx) {
    const dependencyClaims = [claim];
    return {
        content: claim,
        source,
        step,
        rule: 'PREMISE',
        dependsOn: dependencyClaims,
        dependsOnIds: resolveClaimIds(ctx, dependencyClaims),
    };
}
function implicationOutputClaim(claim, ctx) {
    const implication = parseImplicationProp(claim) ?? (ctx.goal ? parseImplicationProp(ctx.goal) : null);
    if (!implication)
        return claim;
    return `${implication[0]} → ${implication[1]}`;
}
function forallOutputClaim(claim, ctx) {
    const quantifier = ctx.goal ? parseBoundedQuantifierProp(ctx.goal, 'forall') : parseBoundedQuantifierProp(claim, 'forall');
    if (!quantifier || !ctx.goal)
        return claim;
    return ctx.goal;
}
function buildImpliesElimProofObject(claim, source, step, ctx) {
    const dependency = findImplicationElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'IMPLIES_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildAndIntroProofObject(claim, source, step, ctx) {
    const dependency = findAndIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'AND_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildAndElimProofObject(claim, source, step, ctx) {
    const dependency = findAndElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'AND_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildIffIntroProofObject(claim, source, step, ctx) {
    const dependency = findIffIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'IFF_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildIffElimProofObject(claim, source, step, ctx) {
    const dependency = findIffElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'IFF_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildSubsetIntroProofObject(claim, source, step, ctx) {
    const dependency = findSubsetIntroDependency(claim, ctx);
    const dischargedScopeIds = dependency?.dischargedScopeIds ?? [];
    return {
        content: claim,
        source,
        step,
        rule: 'SUBSET_INTRO',
        scopeIds: dischargeScopeIds(ctx, dischargedScopeIds),
        dischargedScopeIds,
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildSubsetElimProofObject(claim, source, step, ctx) {
    const dependency = findSubsetElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'SUBSET_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildSubsetTransProofObject(claim, source, step, ctx) {
    const dependency = findSubsetTransDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'SUBSET_TRANS',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildSubsetAntisymProofObject(claim, source, step, ctx) {
    const dependency = findSubsetAntisymDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'SUBSET_ANTISYM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildEqualityReflProofObject(claim, source, step) {
    return {
        content: claim,
        source,
        step,
        rule: 'EQUALITY_REFL',
        dependsOn: [],
        dependsOnIds: [],
    };
}
function buildEqualitySymmProofObject(claim, source, step, ctx) {
    const dependency = findEqualitySymmDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'EQUALITY_SYMM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildEqualityTransProofObject(claim, source, step, ctx) {
    const dependency = findEqualityTransDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'EQUALITY_TRANS',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildArithmeticCommProofObject(claim, source, step, ctx) {
    const dependency = findArithmeticCommDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'ARITHMETIC_COMM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildEqualitySubstProofObject(claim, source, step, ctx) {
    const dependency = findEqualitySubstDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'EQUALITY_SUBST',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildImageIntroProofObject(claim, source, step, ctx) {
    const dependency = findImageIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'IMAGE_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildPreimageIntroProofObject(claim, source, step, ctx) {
    const dependency = findPreimageIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'PREIMAGE_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildPreimageElimProofObject(claim, source, step, ctx) {
    const dependency = findPreimageElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'PREIMAGE_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildUnionIntroProofObject(claim, source, step, ctx) {
    const dependency = findUnionIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'UNION_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildUnionElimProofObject(claim, source, step, ctx) {
    const dependency = findUnionElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'UNION_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildSetBuilderIntroProofObject(claim, source, step, ctx) {
    const dependency = findSetBuilderIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'SET_BUILDER_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildIndexedUnionIntroProofObject(claim, source, step, ctx) {
    const dependency = findIndexedUnionIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'INDEXED_UNION_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildSetMembershipEqualityProofObject(claim, source, step, ctx) {
    const dependency = findSetEqualityDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'SET_MEMBERSHIP_EQ',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildIndexedUnionElimProofObject(claim, source, step, ctx) {
    const dependency = findIndexedUnionElimDependency(claim, ctx);
    const dischargedScopeIds = dependency?.dischargedScopeIds ?? [];
    return {
        content: claim,
        source,
        step,
        rule: 'INDEXED_UNION_ELIM',
        scopeIds: dischargeScopeIds(ctx, dischargedScopeIds),
        dischargedScopeIds,
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildIntersectionIntroProofObject(claim, source, step, ctx) {
    const dependency = findIntersectionIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'INTERSECTION_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildIntersectionElimProofObject(claim, source, step, ctx) {
    const dependency = findIntersectionElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'INTERSECTION_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildForallTypedElimProofObject(claim, source, step, ctx) {
    const dependency = findForallTypedElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'FORALL_TYPED_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildForallTypedIntroProofObject(claim, source, step, ctx) {
    const dependency = findForallTypedIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'FORALL_TYPED_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
        dischargedScopeIds: dependency?.dischargedScopeIds,
    };
}
function buildExistsTypedIntroProofObject(claim, source, step, ctx) {
    const dependency = findExistsTypedIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'EXISTS_TYPED_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildExistsTypedElimProofObject(claim, source, step, ctx) {
    const dependency = findExistsTypedElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'EXISTS_TYPED_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
        dischargedScopeIds: dependency?.dischargedScopeIds,
    };
}
function buildExistsUniqueIntroProofObject(claim, source, step, ctx) {
    const dependency = findExistsUniqueIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'EXISTS_UNIQUE_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildExistsUniqueElimProofObject(claim, source, step, ctx) {
    const dependency = findExistsUniqueElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'EXISTS_UNIQUE_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildDividesIntroProofObject(claim, source, step, ctx) {
    const dependency = findDividesIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'DIVIDES_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildForallInElimProofObject(claim, source, step, ctx) {
    const dependency = findForallInElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'FORALL_IN_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildForallInIntroProofObject(claim, source, step, ctx) {
    const outputClaim = forallOutputClaim(claim, ctx);
    const dependency = findForallInIntroDependency(outputClaim, ctx);
    const dischargedScopeIds = dependency?.dischargedScopeIds ?? [];
    return {
        content: outputClaim,
        source,
        step,
        rule: 'FORALL_IN_INTRO',
        scopeIds: dischargeScopeIds(ctx, dischargedScopeIds),
        dischargedScopeIds,
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildExistsInIntroProofObject(claim, source, step, ctx) {
    const dependency = findExistsInIntroDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'EXISTS_IN_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildExistsInElimProofObject(claim, source, step, ctx) {
    const dependency = findExistsInElimDependency(claim, ctx);
    const dischargedScopeIds = dependency?.dischargedScopeIds ?? [];
    return {
        content: claim,
        source,
        step,
        rule: 'EXISTS_IN_ELIM',
        scopeIds: dischargeScopeIds(ctx, dischargedScopeIds),
        dischargedScopeIds,
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildImpliesIntroProofObject(claim, source, step, ctx) {
    const dependency = findImplicationIntroDependency(claim, ctx);
    const outputClaim = implicationOutputClaim(claim, ctx);
    const dischargedScopeIds = dependency?.dischargedScopeIds ?? [];
    return {
        content: outputClaim,
        source,
        step,
        rule: 'IMPLIES_INTRO',
        scopeIds: dischargeScopeIds(ctx, dischargedScopeIds),
        dischargedScopeIds,
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildContradictionDischargeProofObject(claim, source, step, ctx) {
    const dependency = findContradictionDependency(ctx);
    const dischargedScopeIds = dependency?.dischargedScopeIds ?? [];
    return {
        content: claim,
        source,
        step,
        rule: 'CONTRADICTION',
        scopeIds: dischargeScopeIds(ctx, dischargedScopeIds),
        dischargedScopeIds,
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildOrIntroProofObject(claim, source, step, ctx, side) {
    const ruleTag = side === 'left' ? 'OR_INTRO_LEFT' : 'OR_INTRO_RIGHT';
    const disjunction = parseDisjunctionProp(claim);
    if (!disjunction)
        return { content: claim, source, step, rule: ruleTag, dependsOn: [], dependsOnIds: [] };
    const sideClaim = side === 'left' ? disjunction[0] : disjunction[1];
    const obj = findLatestProofObjectByClaim(ctx, sideClaim);
    return {
        content: claim,
        source,
        step,
        rule: ruleTag,
        dependsOn: obj ? [obj.claim] : [],
        dependsOnIds: obj ? [obj.id] : [],
    };
}
function buildOrElimProofObject(claim, source, step, ctx) {
    const dep = findOrElimDependency(claim, ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'OR_ELIM',
        dependsOn: dep?.claims ?? [],
        dependsOnIds: dep?.ids ?? [],
    };
}
function buildNotIntroProofObject(claim, source, step, ctx) {
    // ¬P from: assume P (assumption), ⊥ (contradiction)
    const inner = extractNegand(claim);
    const assumptionObj = inner ? findLatestProofObjectByClaim(ctx, inner, o => o.source === 'assumption') : null;
    const contradictionObj = findLatestProofObjectByClaim(ctx, '⊥') ?? findLatestProofObjectByClaim(ctx, 'contradiction');
    return {
        content: claim,
        source,
        step,
        rule: 'NOT_INTRO',
        dependsOn: [assumptionObj?.claim, contradictionObj?.claim].filter(Boolean),
        dependsOnIds: [assumptionObj?.id, contradictionObj?.id].filter(Boolean),
    };
}
function buildNotElimProofObject(claim, source, step, ctx) {
    // P from ¬¬P
    const doubleNeg = `¬¬${claim}`;
    const obj = findLatestProofObjectByClaim(ctx, doubleNeg) ?? findLatestProofObjectByClaim(ctx, `¬${extractNegand(claim) ?? ''}`);
    return {
        content: claim,
        source,
        step,
        rule: 'NOT_ELIM',
        dependsOn: obj ? [obj.claim] : [],
        dependsOnIds: obj ? [obj.id] : [],
    };
}
function buildExFalsoProofObject(claim, source, step, ctx) {
    const falsum = findLatestProofObjectByClaim(ctx, '⊥') ?? findLatestProofObjectByClaim(ctx, 'contradiction');
    return {
        content: claim,
        source,
        step,
        rule: 'EX_FALSO',
        dependsOn: falsum ? [falsum.claim] : [],
        dependsOnIds: falsum ? [falsum.id] : [],
    };
}
function findImplicationElimDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const item = ctx.proofObjects[i];
        const implication = parseImplicationProp(item.claim);
        if (!implication)
            continue;
        const [antecedent, consequent] = implication;
        if (!(0, propositions_1.sameProp)(consequent, claim))
            continue;
        const antecedentObject = findLatestProofObjectByClaim(ctx, antecedent);
        if (antecedentObject) {
            return {
                claims: [antecedent, item.claim],
                ids: [antecedentObject.id, item.id],
            };
        }
    }
    return null;
}
function findAndIntroDependency(claim, ctx) {
    const conjunction = parseConjunctionProp(claim);
    if (!conjunction)
        return null;
    const left = findLatestProofObjectByClaim(ctx, conjunction[0]);
    const right = findLatestProofObjectByClaim(ctx, conjunction[1]);
    if (!left || !right)
        return null;
    return {
        claims: [conjunction[0], conjunction[1]],
        ids: uniqueIds([left.id, right.id]),
    };
}
function findAndElimDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const item = ctx.proofObjects[i];
        const conjunction = parseConjunctionProp(item.claim);
        if (!conjunction)
            continue;
        const [left, right] = conjunction;
        if ((0, propositions_1.sameProp)(left, claim) || (0, propositions_1.sameProp)(right, claim)) {
            return { claims: [item.claim], ids: [item.id] };
        }
    }
    return null;
}
function findSubsetIntroDependency(claim, ctx) {
    const target = parseSubsetProp(claim);
    if (!target)
        return null;
    const scope = findSubsetIntroScope(target, ctx);
    if (!scope)
        return null;
    return {
        claims: [scope.membership.claim, scope.body.claim],
        ids: uniqueIds([scope.membership.id, scope.body.id]),
        dischargedScopeIds: scope.dischargedScopeIds,
    };
}
function findSubsetElimDependency(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const subsetCandidate = findLatestProofObject(ctx, object => {
        const subset = parseSubsetProp(object.claim);
        return subset !== null && (0, propositions_1.sameProp)(subset.right, output.set);
    });
    if (!subsetCandidate)
        return null;
    const subset = parseSubsetProp(subsetCandidate.claim);
    if (!subset)
        return null;
    const membershipCandidate = findLatestProofObject(ctx, object => {
        const membership = parseMembershipProp(object.claim);
        return membership !== null &&
            (0, propositions_1.sameProp)(membership.element, output.element) &&
            (0, propositions_1.sameProp)(membership.set, subset.left);
    });
    if (!membershipCandidate)
        return null;
    return {
        claims: [membershipCandidate.claim, subsetCandidate.claim],
        ids: uniqueIds([membershipCandidate.id, subsetCandidate.id]),
    };
}
function findSubsetTransDependency(claim, ctx) {
    const target = parseSubsetProp(claim);
    if (!target)
        return null;
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const first = ctx.proofObjects[i];
        const left = parseSubsetProp(first.claim);
        if (!left || !(0, propositions_1.sameProp)(left.left, target.left))
            continue;
        for (let j = ctx.proofObjects.length - 1; j >= 0; j--) {
            const second = ctx.proofObjects[j];
            const right = parseSubsetProp(second.claim);
            if (!right)
                continue;
            if ((0, propositions_1.sameProp)(left.right, right.left) && (0, propositions_1.sameProp)(right.right, target.right)) {
                return {
                    claims: [first.claim, second.claim],
                    ids: uniqueIds([first.id, second.id]),
                };
            }
        }
    }
    return null;
}
function findSubsetAntisymDependency(claim, ctx) {
    const equality = parseEqualityProp(claim);
    if (!equality)
        return null;
    const leftSubset = `${equality.left} ⊆ ${equality.right}`;
    const rightSubset = `${equality.right} ⊆ ${equality.left}`;
    const leftObj = findLatestProofObjectByClaim(ctx, leftSubset);
    const rightObj = findLatestProofObjectByClaim(ctx, rightSubset);
    if (!leftObj || !rightObj)
        return null;
    return {
        claims: [leftSubset, rightSubset],
        ids: uniqueIds([leftObj.id, rightObj.id]),
    };
}
function findEqualitySymmDependency(claim, ctx) {
    const target = parseEqualityProp(claim);
    if (!target)
        return null;
    const sourceClaim = `${target.right} = ${target.left}`;
    const source = findLatestProofObjectByClaim(ctx, sourceClaim);
    if (!source)
        return null;
    return {
        claims: [source.claim],
        ids: [source.id],
    };
}
function findEqualityTransDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const left = ctx.proofObjects[i];
        if (!parseEqualityProp(left.claim))
            continue;
        for (let j = ctx.proofObjects.length - 1; j >= 0; j--) {
            const right = ctx.proofObjects[j];
            if (!parseEqualityProp(right.claim))
                continue;
            if (supportsEqualityTransitivity(left.claim, right.claim, claim)) {
                return {
                    claims: [left.claim, right.claim],
                    ids: uniqueIds([left.id, right.id]),
                };
            }
        }
    }
    return null;
}
function findArithmeticCommDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const source = ctx.proofObjects[i];
        if (supportsArithmeticCommutativeEquality(source.claim, claim)) {
            return {
                claims: [source.claim],
                ids: [source.id],
            };
        }
    }
    return null;
}
function findEqualitySubstDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const equality = ctx.proofObjects[i];
        if (!parseEqualityProp(equality.claim))
            continue;
        for (let j = ctx.proofObjects.length - 1; j >= 0; j--) {
            const membership = ctx.proofObjects[j];
            if (!parseMembershipProp(membership.claim))
                continue;
            if (supportsEqualitySubstitution(equality.claim, membership.claim, claim)) {
                return {
                    claims: [equality.claim, membership.claim],
                    ids: uniqueIds([equality.id, membership.id]),
                };
            }
        }
    }
    return null;
}
function findImageIntroDependency(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const image = parseImageTerm(output.set);
    const app = parseFunctionApplicationTerm(output.element);
    if (!image || !app)
        return null;
    if (!(0, propositions_1.sameProp)(image.fn, app.fn))
        return null;
    const sourceClaim = `${app.arg} ∈ ${image.set}`;
    const sourceObject = findLatestProofObjectByClaim(ctx, sourceClaim);
    if (!sourceObject)
        return null;
    return { claims: [sourceClaim], ids: [sourceObject.id] };
}
function findPreimageIntroDependency(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const preimage = parsePreimageTerm(output.set);
    if (!preimage)
        return null;
    const candidate = findLatestProofObject(ctx, object => {
        const membership = parseMembershipProp(object.claim);
        if (!membership || !(0, propositions_1.sameProp)(membership.set, preimage.set))
            return false;
        const app = parseFunctionApplicationTerm(membership.element);
        return app !== null && (0, propositions_1.sameProp)(app.fn, preimage.fn) && (0, propositions_1.sameProp)(app.arg, output.element);
    });
    if (!candidate)
        return null;
    return { claims: [candidate.claim], ids: [candidate.id] };
}
function findPreimageElimDependency(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const app = parseFunctionApplicationTerm(output.element);
    if (!app)
        return null;
    const candidate = findLatestProofObject(ctx, object => {
        const membership = parseMembershipProp(object.claim);
        if (!membership || !(0, propositions_1.sameProp)(membership.element, app.arg))
            return false;
        const preimage = parsePreimageTerm(membership.set);
        return preimage !== null && (0, propositions_1.sameProp)(preimage.fn, app.fn) && (0, propositions_1.sameProp)(preimage.set, output.set);
    });
    if (!candidate)
        return null;
    return { claims: [candidate.claim], ids: [candidate.id] };
}
function findUnionIntroDependency(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const union = parseBinarySetProp(output.set, '∪');
    if (!union)
        return null;
    for (const candidateSet of union) {
        const membershipClaim = `${output.element} ∈ ${candidateSet}`;
        const object = findLatestProofObjectByClaim(ctx, membershipClaim);
        if (object) {
            return { claims: [membershipClaim], ids: [object.id] };
        }
    }
    return null;
}
function findUnionElimDependency(claim, ctx) {
    const output = parseDisjunctionProp(claim);
    if (!output)
        return null;
    const leftMembership = parseMembershipProp(output[0]);
    const rightMembership = parseMembershipProp(output[1]);
    if (!leftMembership || !rightMembership)
        return null;
    if (!(0, propositions_1.sameProp)(leftMembership.element, rightMembership.element))
        return null;
    const unionClaim = `${leftMembership.element} ∈ ${leftMembership.set} ∪ ${rightMembership.set}`;
    const unionObject = findLatestProofObjectByClaim(ctx, unionClaim);
    if (!unionObject)
        return null;
    return { claims: [unionClaim], ids: [unionObject.id] };
}
function findSetBuilderIntroDependency(claim, ctx) {
    const dependency = resolveSetBuilderIntroDependency(claim, visibleEstablishedClaims(ctx).map(item => item.content));
    if (!dependency)
        return null;
    const witness = findLatestProofObjectByClaim(ctx, dependency.witnessMembership);
    if (!witness)
        return null;
    return {
        claims: [dependency.witnessMembership],
        ids: [witness.id],
    };
}
function findIndexedUnionIntroDependency(claim, ctx) {
    const dependency = resolveIndexedUnionIntroDependency(claim, visibleEstablishedClaims(ctx).map(item => item.content));
    if (!dependency)
        return null;
    const witness = findLatestProofObjectByClaim(ctx, dependency.witnessMembership);
    const body = findLatestProofObjectByClaim(ctx, dependency.bodyMembership);
    if (!witness || !body)
        return null;
    return {
        claims: [dependency.witnessMembership, dependency.bodyMembership],
        ids: uniqueIds([witness.id, body.id]),
    };
}
function findIndexedUnionElimDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const unionMembership = ctx.proofObjects[i];
        const membership = parseMembershipProp(unionMembership.claim);
        if (!membership)
            continue;
        const indexedUnion = parseIndexedUnionTerm(membership.set);
        if (!indexedUnion)
            continue;
        const scope = findIndexedUnionElimScope(unionMembership.claim, claim, ctx);
        if (!scope)
            continue;
        return {
            claims: [unionMembership.claim, scope.witnessMembership.claim, scope.bodyMembership.claim],
            ids: uniqueIds([unionMembership.id, scope.witnessMembership.id, scope.bodyMembership.id]),
            dischargedScopeIds: scope.dischargedScopeIds,
        };
    }
    return null;
}
function findSetEqualityDependency(claim, ctx) {
    const dependency = resolveSetEqualityDependency(claim, visibleEstablishedClaims(ctx).map(item => item.content));
    if (!dependency)
        return null;
    const left = findLatestProofObjectByClaim(ctx, dependency.leftQuantifier);
    const right = findLatestProofObjectByClaim(ctx, dependency.rightQuantifier);
    if (!left || !right)
        return null;
    return {
        claims: [dependency.leftQuantifier, dependency.rightQuantifier],
        ids: uniqueIds([left.id, right.id]),
    };
}
function findIntersectionIntroDependency(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const intersection = parseBinarySetProp(output.set, '∩');
    if (!intersection)
        return null;
    const leftClaim = `${output.element} ∈ ${intersection[0]}`;
    const rightClaim = `${output.element} ∈ ${intersection[1]}`;
    const left = findLatestProofObjectByClaim(ctx, leftClaim);
    const right = findLatestProofObjectByClaim(ctx, rightClaim);
    if (!left || !right)
        return null;
    return {
        claims: [leftClaim, rightClaim],
        ids: uniqueIds([left.id, right.id]),
    };
}
function findIntersectionElimDependency(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const candidate = findLatestProofObject(ctx, object => {
        const membership = parseMembershipProp(object.claim);
        if (!membership || !(0, propositions_1.sameProp)(membership.element, output.element))
            return false;
        const intersection = parseBinarySetProp(membership.set, '∩');
        return intersection !== null
            && ((0, propositions_1.sameProp)(output.set, intersection[0]) || (0, propositions_1.sameProp)(output.set, intersection[1]));
    });
    if (!candidate)
        return null;
    return { claims: [candidate.claim], ids: [candidate.id] };
}
function findIffIntroDependency(claim, ctx) {
    const iff = parseIffProp(claim);
    if (!iff)
        return null;
    const leftImpl = `${iff[0]} → ${iff[1]}`;
    const rightImpl = `${iff[1]} → ${iff[0]}`;
    const leftObj = findLatestProofObjectByClaim(ctx, leftImpl);
    const rightObj = findLatestProofObjectByClaim(ctx, rightImpl);
    if (!leftObj || !rightObj)
        return null;
    return {
        claims: [leftImpl, rightImpl],
        ids: uniqueIds([leftObj.id, rightObj.id]),
    };
}
function findIffElimDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const iffObj = ctx.proofObjects[i];
        const iff = parseIffProp(iffObj.claim);
        if (!iff)
            continue;
        const leftObj = findLatestProofObjectByClaim(ctx, iff[0]);
        if (leftObj && (0, propositions_1.sameProp)(claim, iff[1])) {
            return {
                claims: [iffObj.claim, leftObj.claim],
                ids: uniqueIds([iffObj.id, leftObj.id]),
            };
        }
        const rightObj = findLatestProofObjectByClaim(ctx, iff[1]);
        if (rightObj && (0, propositions_1.sameProp)(claim, iff[0])) {
            return {
                claims: [iffObj.claim, rightObj.claim],
                ids: uniqueIds([iffObj.id, rightObj.id]),
            };
        }
    }
    return null;
}
function findForallTypedElimDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const quantified = ctx.proofObjects[i];
        if (!parseTypedQuantifierProp(quantified.claim, 'forall'))
            continue;
        const witnessObjects = ctx.proofObjects.filter(object => parseTypedVariableProp(object.claim));
        const path = resolveTypedForallElimPathFromInputs(quantified.claim, witnessObjects.map(object => object.claim), claim);
        if (path) {
            const matchedWitnesses = witnessObjects.filter(object => path.witnessClaims.some(claimText => (0, propositions_1.sameProp)(object.claim, claimText)));
            return {
                claims: [quantified.claim, ...path.witnessClaims],
                ids: uniqueIds([quantified.id, ...matchedWitnesses.map(object => object.id)]),
            };
        }
    }
    return null;
}
function resolveTypedForallElimPathFromInputs(quantifiedClaim, witnessClaims, target) {
    const quantifier = parseTypedQuantifierProp(quantifiedClaim, 'forall');
    if (!quantifier)
        return null;
    for (const witnessClaim of witnessClaims) {
        const witness = parseTypedVariableProp(witnessClaim);
        if (!witness || !sameTypeDomain(witness.domain, quantifier.domain))
            continue;
        const instantiated = instantiateBoundedQuantifier({ variable: quantifier.variable, body: quantifier.body }, witness.variable);
        if (!instantiated)
            continue;
        if ((0, propositions_1.sameProp)(instantiated, target)) {
            return { result: instantiated, witnessClaims: [witnessClaim] };
        }
        if (parseTypedQuantifierProp(instantiated, 'forall')) {
            const remainingWitnesses = witnessClaims.filter(claimText => !(0, propositions_1.sameProp)(claimText, witnessClaim));
            const nested = resolveTypedForallElimPathFromInputs(instantiated, remainingWitnesses, target);
            if (nested) {
                return { result: nested.result, witnessClaims: [witnessClaim, ...nested.witnessClaims] };
            }
        }
    }
    return null;
}
function findForallTypedIntroDependency(claim, ctx) {
    const quantifier = parseTypedQuantifierProp(claim, 'forall');
    if (!quantifier)
        return null;
    const scope = findForallTypedIntroScope(quantifier, ctx);
    if (!scope)
        return null;
    return {
        claims: [scope.witness.claim, scope.body.claim],
        ids: uniqueIds([scope.witness.id, scope.body.id]),
        dischargedScopeIds: scope.dischargedScopeIds,
    };
}
function findExistsTypedIntroDependency(claim, ctx) {
    const quantifier = parseTypedQuantifierProp(claim, 'exists');
    if (!quantifier)
        return null;
    const resolved = resolveTypedExistentialIntroWitness(quantifier, ctx);
    if (!resolved)
        return null;
    return {
        claims: [resolved.witnessClaim, resolved.bodyClaim],
        ids: uniqueIds([resolved.witnessId, resolved.bodyId]),
    };
}
function resolveTypedExistentialIntroWitness(quantifier, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const witness = ctx.proofObjects[i];
        const witnessProp = parseTypedVariableProp(witness.claim);
        if (!witnessProp || !sameTypeDomain(witnessProp.domain, quantifier.domain))
            continue;
        const instantiated = instantiateBoundedQuantifier({ variable: quantifier.variable, body: quantifier.body }, witnessProp.variable);
        if (!instantiated)
            continue;
        const body = findLatestProofObjectByClaim(ctx, instantiated);
        if (body) {
            return {
                witnessClaim: witness.claim,
                bodyClaim: body.claim,
                witnessId: witness.id,
                bodyId: body.id,
            };
        }
        const arithmeticBody = findArithmeticWitnessedBody(ctx, quantifier.body, quantifier.variable, witnessProp.variable);
        if (arithmeticBody) {
            return {
                witnessClaim: witness.claim,
                bodyClaim: arithmeticBody.claim,
                witnessId: witness.id,
                bodyId: arithmeticBody.id,
            };
        }
    }
    return null;
}
function findExistsTypedElimDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const existential = ctx.proofObjects[i];
        const quantifier = parseTypedQuantifierProp(existential.claim, 'exists');
        if (!quantifier)
            continue;
        const scope = findExistsTypedElimScope(quantifier, claim, ctx);
        if (!scope)
            continue;
        return {
            claims: [existential.claim, scope.witness.claim, scope.body.claim],
            ids: uniqueIds([existential.id, scope.witness.id, scope.body.id]),
            dischargedScopeIds: scope.dischargedScopeIds,
        };
    }
    return null;
}
function findExistsUniqueIntroDependency(claim, ctx) {
    const lowered = lowerUniqueExistenceClaim(claim);
    if (!lowered)
        return null;
    const existence = findLatestProofObjectByClaim(ctx, lowered.existenceClaim);
    const uniqueness = findLatestProofObjectByClaim(ctx, lowered.uniquenessClaim);
    if (!existence || !uniqueness)
        return null;
    return {
        claims: [existence.claim, uniqueness.claim],
        ids: uniqueIds([existence.id, uniqueness.id]),
    };
}
function findExistsUniqueElimDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const unique = ctx.proofObjects[i];
        const lowered = lowerUniqueExistenceClaim(unique.claim);
        if (!lowered)
            continue;
        if ((0, propositions_1.sameProp)(claim, lowered.existenceClaim) || (0, propositions_1.sameProp)(claim, lowered.uniquenessClaim)) {
            return {
                claims: [unique.claim],
                ids: [unique.id],
            };
        }
    }
    return null;
}
function findDividesIntroDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const equality = ctx.proofObjects[i];
        if (supportsDividesFromEquality(equality.claim, claim)) {
            return {
                claims: [equality.claim],
                ids: [equality.id],
            };
        }
    }
    return null;
}
function findForallInElimDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const quantified = ctx.proofObjects[i];
        const quantifier = parseBoundedQuantifierProp(quantified.claim, 'forall');
        if (!quantifier)
            continue;
        for (let j = ctx.proofObjects.length - 1; j >= 0; j--) {
            const membership = ctx.proofObjects[j];
            const witness = parseMembershipProp(membership.claim);
            if (!witness || !(0, propositions_1.sameProp)(witness.set, quantifier.set))
                continue;
            const instantiated = instantiateBoundedQuantifier(quantifier, witness.element);
            if (instantiated && (0, propositions_1.sameProp)(instantiated, claim)) {
                return {
                    claims: [quantified.claim, membership.claim],
                    ids: uniqueIds([quantified.id, membership.id]),
                };
            }
        }
    }
    return null;
}
function findForallInIntroDependency(claim, ctx) {
    const quantifier = parseBoundedQuantifierProp(claim, 'forall');
    if (!quantifier)
        return null;
    const scope = findForallInIntroScope(quantifier, ctx);
    if (!scope)
        return null;
    return {
        claims: [scope.membership.claim, scope.body.claim],
        ids: uniqueIds([scope.membership.id, scope.body.id]),
        dischargedScopeIds: scope.dischargedScopeIds,
    };
}
function findExistsInIntroDependency(claim, ctx) {
    const quantifier = parseBoundedQuantifierProp(claim, 'exists');
    if (!quantifier)
        return null;
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const membership = ctx.proofObjects[i];
        const witness = parseMembershipProp(membership.claim);
        if (!witness || !(0, propositions_1.sameProp)(witness.set, quantifier.set))
            continue;
        const instantiated = instantiateBoundedQuantifier(quantifier, witness.element);
        if (!instantiated)
            continue;
        const body = findLatestProofObjectByClaim(ctx, instantiated);
        if (body) {
            return {
                claims: [membership.claim, body.claim],
                ids: uniqueIds([membership.id, body.id]),
            };
        }
    }
    return null;
}
function findExistsInElimDependency(claim, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const existential = ctx.proofObjects[i];
        const quantifier = parseBoundedQuantifierProp(existential.claim, 'exists');
        if (!quantifier)
            continue;
        const scope = findExistsElimScope(quantifier, claim, ctx);
        if (!scope)
            continue;
        return {
            claims: [existential.claim, scope.membership.claim, scope.body.claim],
            ids: uniqueIds([existential.id, scope.membership.id, scope.body.id]),
            dischargedScopeIds: scope.dischargedScopeIds,
        };
    }
    return null;
}
function findImplicationIntroDependency(claim, ctx) {
    const implication = parseImplicationProp(claim) ?? (ctx.goal ? parseImplicationProp(ctx.goal) : null);
    if (!implication)
        return null;
    const antecedentObject = findLatestProofObjectByClaim(ctx, implication[0], object => object.source === 'assumption');
    const consequentObject = findLatestProofObjectByClaim(ctx, implication[1]);
    if (!antecedentObject || !consequentObject)
        return null;
    const dischargedScopeIds = scopesThrough(ctx, antecedentObject.scopeIds[antecedentObject.scopeIds.length - 1]);
    return {
        claims: [implication[0], implication[1]],
        ids: uniqueIds([antecedentObject.id, consequentObject.id]),
        dischargedScopeIds,
    };
}
function findOrElimDependency(target, ctx) {
    for (const disjObj of ctx.proofObjects) {
        const disj = parseDisjunctionProp(disjObj.claim);
        if (!disj)
            continue;
        const [left, right] = disj;
        const leftImpl = `${left} → ${target}`;
        const rightImpl = `${right} → ${target}`;
        const leftObj = findLatestProofObjectByClaim(ctx, leftImpl);
        const rightObj = findLatestProofObjectByClaim(ctx, rightImpl);
        if (leftObj && rightObj) {
            return {
                claims: [disjObj.claim, leftImpl, rightImpl],
                ids: uniqueIds([disjObj.id, leftObj.id, rightObj.id]),
            };
        }
    }
    return null;
}
function findContradictionDependency(ctx) {
    const contradiction = findContradictionProofObjects(ctx);
    if (!contradiction)
        return null;
    const dischargedScopeIds = contradiction.a.source === 'assumption'
        ? scopesThrough(ctx, contradiction.a.scopeIds[contradiction.a.scopeIds.length - 1])
        : contradiction.b.source === 'assumption'
            ? scopesThrough(ctx, contradiction.b.scopeIds[contradiction.b.scopeIds.length - 1])
            : [];
    return {
        claims: [contradiction.a.claim, contradiction.b.claim],
        ids: uniqueIds([contradiction.a.id, contradiction.b.id]),
        dischargedScopeIds,
    };
}
function findContradictionPair(established) {
    for (const claim of established) {
        const negated = negateProp(claim.content);
        if (established.some(other => (0, propositions_1.sameProp)(other.content, negated))) {
            return { a: claim.content, b: negated };
        }
    }
    return null;
}
function findContradictionProofObjects(ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const candidate = ctx.proofObjects[i];
        const negated = negateProp(candidate.claim);
        const opposite = findLatestProofObjectByClaim(ctx, negated);
        if (opposite) {
            return { a: candidate, b: opposite };
        }
    }
    return null;
}
function negateProp(claim) {
    const value = claim.trim();
    if (value.startsWith('¬'))
        return value.slice(1).trim();
    if (value.startsWith('not '))
        return value.slice(4).trim();
    return `¬${value}`;
}
function uniqueProps(values) {
    const unique = [];
    for (const value of values) {
        if (!unique.some(existing => (0, propositions_1.sameProp)(existing, value))) {
            unique.push(value);
        }
    }
    return unique;
}
function uniqueIds(values) {
    return [...new Set(values.filter(Boolean))];
}
function openScope(ctx, kind, label, step) {
    const scope = {
        id: `scope:${kind}:${step}:${normalizeName(label)}`,
        kind,
        label,
        step,
    };
    ctx.currentScopes.push(scope);
    return scope;
}
function currentScopeIds(ctx) {
    return ctx.currentScopes.map(scope => scope.id);
}
function visibleEstablishedClaims(ctx) {
    return ctx.established.filter(claim => isVisibleInCurrentScope(claim.scopeIds, ctx));
}
function dischargeScopeIds(ctx, dischargedScopeIds) {
    const discharged = new Set(dischargedScopeIds);
    return currentScopeIds(ctx).filter(id => !discharged.has(id));
}
function applyDischargedScopes(ctx, dischargedScopeIds) {
    if (!dischargedScopeIds || dischargedScopeIds.length === 0)
        return;
    const discharged = new Set(dischargedScopeIds);
    ctx.currentScopes = ctx.currentScopes.filter(scope => !discharged.has(scope.id));
}
function scopesThrough(ctx, scopeId) {
    if (!scopeId)
        return [];
    const index = ctx.currentScopes.findIndex(scope => scope.id === scopeId);
    if (index === -1)
        return [];
    return ctx.currentScopes.slice(index).map(scope => scope.id);
}
function isVisibleInCurrentScope(scopeIds, ctx) {
    const active = currentScopeIds(ctx);
    if (scopeIds.length > active.length)
        return false;
    return scopeIds.every((id, index) => active[index] === id);
}
function resolveClaimIds(ctx, claims) {
    const resolved = [];
    for (const claim of claims) {
        const matches = ctx.established.filter(item => (0, propositions_1.sameProp)(item.content, claim) && item.proofObjectId && isVisibleInCurrentScope(item.scopeIds, ctx));
        if (matches.length > 0) {
            resolved.push(matches[matches.length - 1].proofObjectId);
        }
    }
    return uniqueIds(resolved);
}
function findLatestProofObjectByClaim(ctx, claim, predicate) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const object = ctx.proofObjects[i];
        if ((0, propositions_1.sameProp)(object.claim, claim) && isVisibleInCurrentScope(object.scopeIds, ctx) && (!predicate || predicate(object))) {
            return object;
        }
    }
    return null;
}
function findLatestProofObject(ctx, predicate) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const object = ctx.proofObjects[i];
        if (isVisibleInCurrentScope(object.scopeIds, ctx) && predicate(object))
            return object;
    }
    return null;
}
function validateProofObjectInput(input) {
    const dependsOnIds = input.dependsOnIds ?? [];
    const minimum = minimumDependencyCount(input.rule, input.dependsOn);
    if (dependsOnIds.length >= minimum)
        return null;
    if (minimum === 0)
        return null;
    return {
        valid: false,
        rule: input.rule,
        message: `Could not resolve proof-object references for '${input.content}' under ${input.rule}`,
        hint: `Expected ${minimum} dependency reference(s), resolved ${dependsOnIds.length}.`,
    };
}
function minimumDependencyCount(rule, dependsOn) {
    switch (rule) {
        case 'PREMISE':
            return 1;
        case 'IMPLIES_ELIM':
            return uniqueProps(dependsOn).length;
        case 'AND_INTRO':
            return uniqueProps(dependsOn).length;
        case 'AND_ELIM':
            return 1;
        case 'IFF_INTRO':
            return uniqueProps(dependsOn).length;
        case 'IFF_ELIM':
            return uniqueProps(dependsOn).length;
        case 'SUBSET_INTRO':
            return uniqueProps(dependsOn).length;
        case 'SUBSET_ELIM':
            return uniqueProps(dependsOn).length;
        case 'SUBSET_TRANS':
            return uniqueProps(dependsOn).length;
        case 'SUBSET_ANTISYM':
            return uniqueProps(dependsOn).length;
        case 'ARITHMETIC_COMM':
            return uniqueProps(dependsOn).length;
        case 'EQUALITY_SUBST':
            return uniqueProps(dependsOn).length;
        case 'IMAGE_INTRO':
            return uniqueProps(dependsOn).length;
        case 'PREIMAGE_INTRO':
            return uniqueProps(dependsOn).length;
        case 'PREIMAGE_ELIM':
            return uniqueProps(dependsOn).length;
        case 'UNION_INTRO':
            return uniqueProps(dependsOn).length;
        case 'UNION_ELIM':
            return uniqueProps(dependsOn).length;
        case 'SET_BUILDER_INTRO':
            return uniqueProps(dependsOn).length;
        case 'INDEXED_UNION_INTRO':
            return uniqueProps(dependsOn).length;
        case 'INDEXED_UNION_ELIM':
            return uniqueProps(dependsOn).length;
        case 'SET_MEMBERSHIP_EQ':
            return uniqueProps(dependsOn).length;
        case 'INTERSECTION_INTRO':
            return uniqueProps(dependsOn).length;
        case 'INTERSECTION_ELIM':
            return uniqueProps(dependsOn).length;
        case 'FORALL_TYPED_ELIM':
            return uniqueProps(dependsOn).length;
        case 'FORALL_TYPED_INTRO':
            return uniqueProps(dependsOn).length;
        case 'EXISTS_TYPED_INTRO':
            return uniqueProps(dependsOn).length;
        case 'EXISTS_TYPED_ELIM':
            return uniqueProps(dependsOn).length;
        case 'EXISTS_UNIQUE_INTRO':
            return uniqueProps(dependsOn).length;
        case 'EXISTS_UNIQUE_ELIM':
            return uniqueProps(dependsOn).length;
        case 'DIVIDES_INTRO':
            return uniqueProps(dependsOn).length;
        case 'FORALL_IN_ELIM':
            return uniqueProps(dependsOn).length;
        case 'FORALL_IN_INTRO':
            return uniqueProps(dependsOn).length;
        case 'EXISTS_IN_INTRO':
            return uniqueProps(dependsOn).length;
        case 'EXISTS_IN_ELIM':
            return uniqueProps(dependsOn).length;
        case 'IMPLIES_INTRO':
            return uniqueProps(dependsOn).length;
        case 'CONTRADICTION':
            return uniqueProps(dependsOn).length;
        case 'BY_LEMMA':
            return uniqueProps(dependsOn).length;
        default:
            return 0;
    }
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
            return isKernelCheckableAtom(expr.condition);
        case 'Quantified':
            return isKernelCheckableAtom(exprToString(expr));
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
function parseFallbackDiagnostic(expr, label) {
    if (expr.type !== 'Atom' || expr.atomKind !== 'opaque')
        return null;
    if (isKernelCheckableAtom(expr.condition))
        return null;
    const atom = expr;
    const reason = atom.parseError
        ? `The parser fell back to an opaque symbolic claim: ${atom.parseError}`
        : `The parser accepted this as an opaque symbolic claim.`;
    const mathHint = parserFallbackHint(atom.condition);
    return {
        severity: 'info',
        message: `${label} is outside the current parser/checker subset. ${reason}`,
        rule: 'STRUCTURAL',
        hint: mathHint,
    };
}
function containsMathNotation(value) {
    return /[∀∃∈∉⊆⊂≤≥≠ℕℤℚℝ∪∩]/.test(value);
}
function parserFallbackHint(value) {
    if (/[∀∃]/.test(value)) {
        return `This looks like quantified mathematics. Only bounded quantifiers in the form ∀x ∈ A, P(x) and ∃x ∈ A, P(x) are kernel-checked.`;
    }
    if (/[∈∉⊆⊂∪∩]/.test(value)) {
        return `This looks like set-theoretic notation. The kernel verifies membership, subset, equality-substitution, and union/intersection membership rules.`;
    }
    if (/:\s*[\wℕℤℚℝ]/.test(value) || /→|⇒/.test(value)) {
        return `This looks like typed or function-style mathematical notation outside the current kernel subset.`;
    }
    if (containsMathNotation(value)) {
        return `This looks like mathematical notation outside the current kernel subset.`;
    }
    return `Rewrite the expression into the current kernel subset.`;
}
function checkDerivedClaim(claim, ctx) {
    const established = visibleEstablishedClaims(ctx);
    if (established.some(item => (0, propositions_1.sameProp)(item.content, claim))) {
        return null;
    }
    const implicationIntro = checkImplicationIntroDerivedClaim(claim, ctx);
    if (implicationIntro?.valid)
        return implicationIntro;
    const subsetIntro = checkSubsetIntroDerivedClaim(claim, ctx);
    if (subsetIntro?.valid)
        return subsetIntro;
    for (const item of established) {
        const implication = parseImplicationProp(item.content);
        if (!implication)
            continue;
        const [antecedent, consequent] = implication;
        if (!(0, propositions_1.sameProp)(consequent, claim))
            continue;
        const result = (0, rules_1.checkModusPonens)(antecedent, consequent, ctx);
        if (result.valid)
            return result;
    }
    for (const item of established) {
        const conjunction = parseConjunctionProp(item.content);
        if (!conjunction)
            continue;
        const [left, right] = conjunction;
        if ((0, propositions_1.sameProp)(left, claim) || (0, propositions_1.sameProp)(right, claim)) {
            const result = (0, rules_1.checkAndElim)(claim, item.content, ctx);
            if (result.valid)
                return result;
        }
    }
    const subsetElim = checkSubsetDerivedClaim(claim, ctx);
    if (subsetElim?.valid)
        return subsetElim;
    const subsetTrans = checkSubsetTransDerivedClaim(claim, ctx);
    if (subsetTrans?.valid)
        return subsetTrans;
    const subsetAntisym = checkSubsetAntisymDerivedClaim(claim, ctx);
    if (subsetAntisym?.valid)
        return subsetAntisym;
    const iffIntro = checkIffIntroDerivedClaim(claim, ctx);
    if (iffIntro?.valid)
        return iffIntro;
    const iffElim = checkIffElimDerivedClaim(claim, ctx);
    if (iffElim?.valid)
        return iffElim;
    const equalityDirect = checkEqualityDerivedClaim(claim, ctx);
    if (equalityDirect?.valid)
        return equalityDirect;
    const equalitySubst = checkEqualitySubstDerivedClaim(claim, ctx);
    if (equalitySubst?.valid)
        return equalitySubst;
    const imageIntro = checkImageIntroDerivedClaim(claim, ctx);
    if (imageIntro?.valid)
        return imageIntro;
    const preimageIntro = checkPreimageIntroDerivedClaim(claim, ctx);
    if (preimageIntro?.valid)
        return preimageIntro;
    const preimageElim = checkPreimageElimDerivedClaim(claim, ctx);
    if (preimageElim?.valid)
        return preimageElim;
    const unionIntro = checkUnionIntroDerivedClaim(claim, ctx);
    if (unionIntro?.valid)
        return unionIntro;
    const unionElim = checkUnionElimDerivedClaim(claim, ctx);
    if (unionElim?.valid)
        return unionElim;
    const setBuilderIntro = checkSetBuilderIntroDerivedClaim(claim, ctx);
    if (setBuilderIntro?.valid)
        return setBuilderIntro;
    const indexedUnionIntro = checkIndexedUnionIntroDerivedClaim(claim, ctx);
    if (indexedUnionIntro?.valid)
        return indexedUnionIntro;
    const setEquality = checkSetEqualityDerivedClaim(claim, ctx);
    if (setEquality?.valid)
        return setEquality;
    const indexedUnionElim = checkIndexedUnionElimDerivedClaim(claim, ctx);
    if (indexedUnionElim?.valid)
        return indexedUnionElim;
    const intersectionIntro = checkIntersectionIntroDerivedClaim(claim, ctx);
    if (intersectionIntro?.valid)
        return intersectionIntro;
    const intersectionElim = checkIntersectionElimDerivedClaim(claim, ctx);
    if (intersectionElim?.valid)
        return intersectionElim;
    const forallTypedElim = checkForallTypedElimDerivedClaim(claim, ctx);
    if (forallTypedElim?.valid)
        return forallTypedElim;
    const forallTypedIntro = checkForallTypedIntroDerivedClaim(claim, ctx);
    if (forallTypedIntro?.valid)
        return forallTypedIntro;
    const existsTypedIntro = checkExistsTypedIntroDerivedClaim(claim, ctx);
    if (existsTypedIntro?.valid)
        return existsTypedIntro;
    const existsTypedElim = checkExistsTypedElimDerivedClaim(claim, ctx);
    if (existsTypedElim?.valid)
        return existsTypedElim;
    const existsUniqueIntro = checkExistsUniqueDerivedClaim(claim, ctx);
    if (existsUniqueIntro?.valid)
        return existsUniqueIntro;
    const existsUniqueElim = checkExistsUniqueComponentDerivedClaim(claim, ctx);
    if (existsUniqueElim?.valid)
        return existsUniqueElim;
    const dividesIntro = checkDividesDerivedClaim(claim, ctx);
    if (dividesIntro?.valid)
        return dividesIntro;
    const forallElim = checkForallInElimDerivedClaim(claim, ctx);
    if (forallElim?.valid)
        return forallElim;
    const forallIntro = checkForallInIntroDerivedClaim(claim, ctx);
    if (forallIntro?.valid)
        return forallIntro;
    const existsIntro = checkExistsInIntroDerivedClaim(claim, ctx);
    if (existsIntro?.valid)
        return existsIntro;
    const existsElim = checkExistsInElimDerivedClaim(claim, ctx);
    if (existsElim?.valid)
        return existsElim;
    // OR_ELIM: have P ∨ Q, P → R, Q → R → conclude R
    const orElimResult = checkOrElimDerivedClaim(claim, ctx);
    if (orElimResult?.valid)
        return orElimResult;
    // NOT_ELIM: have ¬¬P → conclude P
    const notElimResult = checkNotElimDerivedClaim(claim, ctx);
    if (notElimResult?.valid)
        return notElimResult;
    // NOT_INTRO: have P assumed + ⊥ → conclude ¬P
    const notIntroResult = checkNotIntroDerivedClaim(claim, ctx);
    if (notIntroResult?.valid)
        return notIntroResult;
    // EX_FALSO: have ⊥ → conclude anything
    const exFalsoResult = checkExFalsoDerivedClaim(claim, ctx);
    if (exFalsoResult?.valid)
        return exFalsoResult;
    if (ctx.goal && (0, propositions_1.sameProp)(ctx.goal, claim)) {
        return {
            valid: false,
            rule: 'STRUCTURAL',
            message: `Conclusion '${claim}' is not yet derived from the current context`,
            hint: `Add assumptions or intermediate proof steps that derive '${claim}' from earlier claims.`,
        };
    }
    return null;
}
function checkSubsetDerivedClaim(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    for (const item of visibleEstablishedClaims(ctx)) {
        const subset = parseSubsetProp(item.content);
        if (!subset || !(0, propositions_1.sameProp)(subset.right, output.set))
            continue;
        const membershipClaim = `${output.element} ∈ ${subset.left}`;
        const result = (0, rules_1.checkSubsetElim)(membershipClaim, item.content, claim, ctx);
        if (result.valid)
            return result;
    }
    return null;
}
function checkSubsetIntroDerivedClaim(claim, ctx) {
    const target = parseSubsetProp(claim);
    if (!target)
        return null;
    const scope = findSubsetIntroScope(target, ctx);
    if (!scope)
        return null;
    const bodyClaim = `${scope.witness} ∈ ${target.right}`;
    const result = (0, rules_1.checkSubsetIntro)(scope.membership.claim, bodyClaim, claim, ctx);
    return result.valid ? result : null;
}
function checkImplicationIntroDerivedClaim(claim, ctx) {
    const implication = parseImplicationProp(claim);
    if (!implication)
        return null;
    const dependency = findImplicationIntroDependency(claim, ctx);
    if (!dependency)
        return null;
    return (0, rules_1.checkImpliesIntro)(implication[0], implication[1], true, true);
}
function checkSubsetTransDerivedClaim(claim, ctx) {
    const target = parseSubsetProp(claim);
    if (!target)
        return null;
    const established = visibleEstablishedClaims(ctx);
    for (const item of established) {
        const left = parseSubsetProp(item.content);
        if (!left || !(0, propositions_1.sameProp)(left.left, target.left))
            continue;
        for (const next of established) {
            const right = parseSubsetProp(next.content);
            if (!right)
                continue;
            if ((0, propositions_1.sameProp)(left.right, right.left) && (0, propositions_1.sameProp)(right.right, target.right)) {
                const result = (0, rules_1.checkSubsetTrans)(item.content, next.content, claim, ctx);
                if (result.valid)
                    return result;
            }
        }
    }
    return null;
}
function checkSubsetAntisymDerivedClaim(claim, ctx) {
    const equality = parseEqualityProp(claim);
    if (!equality)
        return null;
    const leftSubset = `${equality.left} ⊆ ${equality.right}`;
    const rightSubset = `${equality.right} ⊆ ${equality.left}`;
    const result = (0, rules_1.checkSubsetAntisym)(leftSubset, rightSubset, claim, ctx);
    return result.valid ? result : null;
}
function checkIffIntroDerivedClaim(claim, ctx) {
    const iff = parseIffProp(claim);
    if (!iff)
        return null;
    const leftImpl = `${iff[0]} → ${iff[1]}`;
    const rightImpl = `${iff[1]} → ${iff[0]}`;
    const result = (0, rules_1.checkIffIntro)(leftImpl, rightImpl, claim, ctx);
    return result.valid ? result : null;
}
function checkIffElimDerivedClaim(claim, ctx) {
    const established = visibleEstablishedClaims(ctx);
    for (const item of established) {
        const iff = parseIffProp(item.content);
        if (!iff)
            continue;
        if (visibleEstablishedClaims(ctx).some(other => (0, propositions_1.sameProp)(other.content, iff[0])) && (0, propositions_1.sameProp)(claim, iff[1])) {
            const result = (0, rules_1.checkIffElim)(item.content, iff[0], claim, ctx);
            if (result.valid)
                return result;
        }
        if (visibleEstablishedClaims(ctx).some(other => (0, propositions_1.sameProp)(other.content, iff[1])) && (0, propositions_1.sameProp)(claim, iff[0])) {
            const result = (0, rules_1.checkIffElim)(item.content, iff[1], claim, ctx);
            if (result.valid)
                return result;
        }
    }
    return null;
}
function checkEqualityDerivedClaim(claim, ctx) {
    const equality = parseEqualityProp(claim);
    if (!equality)
        return null;
    if ((0, propositions_1.sameProp)(equality.left, equality.right)) {
        return (0, rules_1.checkEqualityRefl)(claim);
    }
    for (const item of visibleEstablishedClaims(ctx)) {
        if (supportsArithmeticCommutativeEquality(item.content, claim)) {
            const result = (0, rules_1.checkArithmeticComm)(item.content, claim, ctx);
            if (result.valid)
                return result;
        }
    }
    const symmetricSource = `${equality.right} = ${equality.left}`;
    if (visibleEstablishedClaims(ctx).some(item => (0, propositions_1.sameProp)(item.content, symmetricSource))) {
        const result = (0, rules_1.checkEqualitySymm)(symmetricSource, claim, ctx);
        if (result.valid)
            return result;
    }
    const established = visibleEstablishedClaims(ctx);
    for (const leftItem of established) {
        for (const rightItem of established) {
            if (supportsEqualityTransitivity(leftItem.content, rightItem.content, claim)) {
                const result = (0, rules_1.checkEqualityTrans)(leftItem.content, rightItem.content, claim, ctx);
                if (result.valid)
                    return result;
            }
        }
    }
    return null;
}
function checkEqualitySubstDerivedClaim(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const established = visibleEstablishedClaims(ctx);
    for (const equalityItem of established) {
        const equality = parseEqualityProp(equalityItem.content);
        if (!equality)
            continue;
        for (const membershipItem of established) {
            if (supportsEqualitySubstitution(equalityItem.content, membershipItem.content, claim)) {
                const result = (0, rules_1.checkEqualitySubst)(equalityItem.content, membershipItem.content, claim, ctx);
                if (result.valid)
                    return result;
            }
        }
    }
    return null;
}
function checkImageIntroDerivedClaim(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const image = parseImageTerm(output.set);
    const app = parseFunctionApplicationTerm(output.element);
    if (!image || !app)
        return null;
    if (!(0, propositions_1.sameProp)(image.fn, app.fn))
        return null;
    const sourceMembership = `${app.arg} ∈ ${image.set}`;
    const result = (0, rules_1.checkImageIntro)(sourceMembership, claim, ctx);
    return result.valid ? result : null;
}
function checkPreimageIntroDerivedClaim(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const preimage = parsePreimageTerm(output.set);
    if (!preimage)
        return null;
    for (const item of visibleEstablishedClaims(ctx)) {
        const membership = parseMembershipProp(item.content);
        if (!membership || !(0, propositions_1.sameProp)(membership.set, preimage.set))
            continue;
        const app = parseFunctionApplicationTerm(membership.element);
        if (!app)
            continue;
        if ((0, propositions_1.sameProp)(app.fn, preimage.fn) && (0, propositions_1.sameProp)(app.arg, output.element)) {
            const result = (0, rules_1.checkPreimageIntro)(item.content, claim, ctx);
            if (result.valid)
                return result;
        }
    }
    return null;
}
function checkPreimageElimDerivedClaim(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const app = parseFunctionApplicationTerm(output.element);
    if (!app)
        return null;
    for (const item of visibleEstablishedClaims(ctx)) {
        const membership = parseMembershipProp(item.content);
        if (!membership || !(0, propositions_1.sameProp)(membership.element, app.arg))
            continue;
        const preimage = parsePreimageTerm(membership.set);
        if (!preimage)
            continue;
        if ((0, propositions_1.sameProp)(preimage.fn, app.fn) && (0, propositions_1.sameProp)(preimage.set, output.set)) {
            const result = (0, rules_1.checkPreimageElim)(item.content, claim, ctx);
            if (result.valid)
                return result;
        }
    }
    return null;
}
function checkUnionIntroDerivedClaim(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const union = parseBinarySetProp(output.set, '∪');
    if (!union)
        return null;
    for (const candidateSet of union) {
        const membershipClaim = `${output.element} ∈ ${candidateSet}`;
        const result = (0, rules_1.checkUnionIntro)(membershipClaim, claim, ctx);
        if (result.valid)
            return result;
    }
    return null;
}
function checkUnionElimDerivedClaim(claim, ctx) {
    const output = parseDisjunctionProp(claim);
    if (!output)
        return null;
    const leftMembership = parseMembershipProp(output[0]);
    const rightMembership = parseMembershipProp(output[1]);
    if (!leftMembership || !rightMembership)
        return null;
    if (!(0, propositions_1.sameProp)(leftMembership.element, rightMembership.element))
        return null;
    const unionMembership = `${leftMembership.element} ∈ ${leftMembership.set} ∪ ${rightMembership.set}`;
    const result = (0, rules_1.checkUnionElim)(unionMembership, claim, ctx);
    return result.valid ? result : null;
}
function checkSetBuilderIntroDerivedClaim(claim, ctx) {
    const dependency = resolveSetBuilderIntroDependency(claim, visibleEstablishedClaims(ctx).map(item => item.content));
    if (!dependency)
        return null;
    const result = (0, rules_1.checkSetBuilderIntro)(dependency.witnessMembership, claim, ctx);
    return result.valid ? result : null;
}
function checkIndexedUnionIntroDerivedClaim(claim, ctx) {
    const dependency = resolveIndexedUnionIntroDependency(claim, visibleEstablishedClaims(ctx).map(item => item.content));
    if (!dependency)
        return null;
    const result = (0, rules_1.checkIndexedUnionIntro)(dependency.witnessMembership, dependency.bodyMembership, claim, ctx);
    return result.valid ? result : null;
}
function checkIndexedUnionElimDerivedClaim(claim, ctx) {
    for (const item of visibleEstablishedClaims(ctx)) {
        const membership = parseMembershipProp(item.content);
        if (!membership || !parseIndexedUnionTerm(membership.set))
            continue;
        const scope = findIndexedUnionElimScope(item.content, claim, ctx);
        if (!scope)
            continue;
        const result = (0, rules_1.checkIndexedUnionElim)(item.content, scope.witnessMembership.claim, scope.bodyMembership.claim, claim, ctx);
        if (result.valid)
            return result;
    }
    return null;
}
function checkSetEqualityDerivedClaim(claim, ctx) {
    const dependency = resolveSetEqualityDependency(claim, visibleEstablishedClaims(ctx).map(item => item.content));
    if (!dependency)
        return null;
    const result = (0, rules_1.checkSetEquality)(dependency.leftQuantifier, dependency.rightQuantifier, claim, ctx);
    return result.valid ? result : null;
}
function checkIntersectionIntroDerivedClaim(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const intersection = parseBinarySetProp(output.set, '∩');
    if (!intersection)
        return null;
    const leftClaim = `${output.element} ∈ ${intersection[0]}`;
    const rightClaim = `${output.element} ∈ ${intersection[1]}`;
    const result = (0, rules_1.checkIntersectionIntro)(leftClaim, rightClaim, claim, ctx);
    return result.valid ? result : null;
}
function checkIntersectionElimDerivedClaim(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    for (const item of visibleEstablishedClaims(ctx)) {
        const membership = parseMembershipProp(item.content);
        if (!membership || !(0, propositions_1.sameProp)(membership.element, output.element))
            continue;
        const intersection = parseBinarySetProp(membership.set, '∩');
        if (!intersection)
            continue;
        if ((0, propositions_1.sameProp)(output.set, intersection[0]) || (0, propositions_1.sameProp)(output.set, intersection[1])) {
            const result = (0, rules_1.checkIntersectionElim)(item.content, claim, ctx);
            if (result.valid)
                return result;
        }
    }
    return null;
}
function checkForallTypedElimDerivedClaim(claim, ctx) {
    const established = visibleEstablishedClaims(ctx);
    for (const quantifiedItem of established) {
        if (!parseTypedQuantifierProp(quantifiedItem.content, 'forall'))
            continue;
        const witnessDeclarations = ctx.variables
            .filter(variable => variable.type)
            .map(variable => `${variable.name}: ${variable.type}`);
        const path = resolveTypedForallElimPathFromInputs(quantifiedItem.content, witnessDeclarations, claim);
        if (path && path.witnessClaims.length > 0) {
            const result = (0, rules_1.checkForallTypedElim)(quantifiedItem.content, path.witnessClaims[0], claim, ctx);
            if (result.valid)
                return result;
        }
    }
    return null;
}
function checkForallTypedIntroDerivedClaim(claim, ctx) {
    const quantifier = parseTypedQuantifierProp(claim, 'forall');
    if (!quantifier)
        return null;
    const scope = findForallTypedIntroScope(quantifier, ctx);
    if (!scope)
        return null;
    const result = (0, rules_1.checkForallTypedIntro)(scope.witness.claim, scope.body.claim, claim, ctx);
    return result.valid ? result : null;
}
function checkExistsTypedIntroDerivedClaim(claim, ctx) {
    const quantifier = parseTypedQuantifierProp(claim, 'exists');
    if (!quantifier)
        return null;
    const resolved = resolveTypedExistentialIntroWitness(quantifier, ctx);
    if (!resolved)
        return null;
    const result = (0, rules_1.checkExistsTypedIntro)(resolved.witnessClaim, resolved.bodyClaim, claim, ctx);
    if (result.valid)
        return result;
    return null;
}
function checkExistsTypedElimDerivedClaim(claim, ctx) {
    for (const existentialItem of visibleEstablishedClaims(ctx)) {
        const quantifier = parseTypedQuantifierProp(existentialItem.content, 'exists');
        if (!quantifier)
            continue;
        const scope = findExistsTypedElimScope(quantifier, claim, ctx);
        if (!scope)
            continue;
        const result = (0, rules_1.checkExistsTypedElim)(existentialItem.content, scope.witness.claim, scope.body.claim, claim, ctx);
        if (result.valid)
            return result;
    }
    return null;
}
function checkExistsUniqueDerivedClaim(claim, ctx) {
    const lowered = lowerUniqueExistenceClaim(claim);
    if (!lowered)
        return null;
    const result = (0, rules_1.checkExistsUniqueIntro)(claim, lowered.existenceClaim, lowered.uniquenessClaim, ctx);
    return result.valid ? result : null;
}
function checkExistsUniqueComponentDerivedClaim(claim, ctx) {
    for (const item of visibleEstablishedClaims(ctx)) {
        const lowered = lowerUniqueExistenceClaim(item.content);
        if (!lowered)
            continue;
        if ((0, propositions_1.sameProp)(claim, lowered.existenceClaim) || (0, propositions_1.sameProp)(claim, lowered.uniquenessClaim)) {
            const result = (0, rules_1.checkExistsUniqueElim)(item.content, claim, ctx);
            if (result.valid)
                return result;
        }
    }
    return null;
}
function checkDividesDerivedClaim(claim, ctx) {
    for (const item of visibleEstablishedClaims(ctx)) {
        if (supportsDividesFromEquality(item.content, claim)) {
            const result = (0, rules_1.checkDividesIntro)(item.content, claim, ctx);
            if (result.valid)
                return result;
        }
    }
    return null;
}
function checkForallInElimDerivedClaim(claim, ctx) {
    const established = visibleEstablishedClaims(ctx);
    for (const quantifiedItem of established) {
        const quantifier = parseBoundedQuantifierProp(quantifiedItem.content, 'forall');
        if (!quantifier)
            continue;
        for (const membershipItem of established) {
            const witness = parseMembershipProp(membershipItem.content);
            if (!witness || !(0, propositions_1.sameProp)(witness.set, quantifier.set))
                continue;
            const instantiated = instantiateBoundedQuantifier(quantifier, witness.element);
            if (instantiated && (0, propositions_1.sameProp)(instantiated, claim)) {
                const result = (0, rules_1.checkForallInElim)(quantifiedItem.content, membershipItem.content, claim, ctx);
                if (result.valid)
                    return result;
            }
        }
    }
    return null;
}
function checkForallInIntroDerivedClaim(claim, ctx) {
    const quantifier = parseBoundedQuantifierProp(claim, 'forall');
    if (!quantifier)
        return null;
    const scope = findForallInIntroScope(quantifier, ctx);
    if (!scope)
        return null;
    const result = (0, rules_1.checkForallInIntro)(scope.membership.claim, scope.body.claim, claim, ctx);
    return result.valid ? result : null;
}
function checkExistsInIntroDerivedClaim(claim, ctx) {
    const quantifier = parseBoundedQuantifierProp(claim, 'exists');
    if (!quantifier)
        return null;
    const established = visibleEstablishedClaims(ctx);
    for (const membershipItem of established) {
        const witness = parseMembershipProp(membershipItem.content);
        if (!witness || !(0, propositions_1.sameProp)(witness.set, quantifier.set))
            continue;
        const instantiated = instantiateBoundedQuantifier(quantifier, witness.element);
        if (!instantiated)
            continue;
        if (established.some(item => (0, propositions_1.sameProp)(item.content, instantiated))) {
            const result = (0, rules_1.checkExistsInIntro)(membershipItem.content, instantiated, claim, ctx);
            if (result.valid)
                return result;
        }
    }
    return null;
}
function checkExistsInElimDerivedClaim(claim, ctx) {
    for (const existentialItem of visibleEstablishedClaims(ctx)) {
        const quantifier = parseBoundedQuantifierProp(existentialItem.content, 'exists');
        if (!quantifier)
            continue;
        const scope = findExistsElimScope(quantifier, claim, ctx);
        if (!scope)
            continue;
        const result = (0, rules_1.checkExistsInElim)(existentialItem.content, scope.membership.claim, scope.body.claim, claim, ctx);
        if (result.valid)
            return result;
    }
    return null;
}
function checkImplicationGoalDischarge(claim, ctx) {
    if (!ctx.goal)
        return null;
    const implication = parseImplicationProp(ctx.goal);
    if (!implication)
        return null;
    const [antecedent, consequent] = implication;
    if (!(0, propositions_1.sameProp)(consequent, claim))
        return null;
    const dependency = findImplicationIntroDependency(ctx.goal, ctx);
    if (!dependency)
        return null;
    return {
        valid: true,
        rule: 'IMPLIES_INTRO',
        message: `${antecedent} → ${consequent} ✓`,
    };
}
function checkForallGoalDischarge(claim, ctx) {
    if (!ctx.goal)
        return null;
    const typedQuantifier = parseTypedQuantifierProp(ctx.goal, 'forall');
    if (typedQuantifier) {
        const dependency = findForallTypedIntroDependency(ctx.goal, ctx);
        if (!dependency)
            return null;
        const scope = findForallTypedIntroScope(typedQuantifier, ctx);
        if (!scope || !(0, propositions_1.sameProp)(scope.body.claim, claim))
            return null;
        return {
            valid: true,
            rule: 'FORALL_TYPED_INTRO',
            message: `${ctx.goal} ✓`,
        };
    }
    const quantifier = parseBoundedQuantifierProp(ctx.goal, 'forall');
    if (!quantifier)
        return null;
    const dependency = findForallInIntroDependency(ctx.goal, ctx);
    if (!dependency)
        return null;
    const scope = findForallInIntroScope(quantifier, ctx);
    if (!scope)
        return null;
    if (!(0, propositions_1.sameProp)(scope.body.claim, claim))
        return null;
    return {
        valid: true,
        rule: 'FORALL_IN_INTRO',
        message: `${ctx.goal} ✓`,
    };
}
function checkContradictionDischarge(claim, ctx) {
    const dependency = findContradictionDependency(ctx);
    if (!dependency)
        return null;
    return {
        valid: true,
        rule: 'CONTRADICTION',
        message: `Contradiction discharges the current goal: ${claim}`,
    };
}
function checkPremiseClaim(claim, ctx) {
    if (!ctx.goal)
        return null;
    if (!(0, propositions_1.sameProp)(claim, ctx.goal) && !visibleEstablishedClaims(ctx).some(item => item.source === 'premise' && (0, propositions_1.sameProp)(item.content, claim))) {
        return null;
    }
    return {
        valid: true,
        rule: 'PREMISE',
        message: `Premise available in context: ${claim}`,
    };
}
function parseImplicationProp(prop) {
    return (0, propositions_1.parseImplicationCanonical)(prop);
}
function parseConjunctionProp(prop) {
    return (0, propositions_1.parseConjunctionCanonical)(prop);
}
function parseIffProp(prop) {
    return (0, propositions_1.parseIffCanonical)(prop);
}
function parseSubsetProp(prop) {
    const parsed = (0, propositions_1.parseSubsetCanonical)(prop);
    return parsed ? { left: parsed.left, right: parsed.right } : null;
}
function parseEqualityProp(prop) {
    if (/==/.test(prop))
        return null;
    return (0, propositions_1.parseEqualityCanonical)(prop);
}
function parseMembershipProp(prop) {
    const value = stripParens(prop);
    if (value.startsWith('∀') || value.startsWith('∃'))
        return null;
    return (0, propositions_1.parseMembershipCanonical)(value);
}
function parseFunctionApplicationTerm(term) {
    const value = stripParens(term);
    const match = value.match(/^([A-Za-z_][A-Za-z0-9_.]*)\((.+)\)$/);
    if (!match)
        return null;
    return {
        fn: stripParens(match[1]),
        arg: stripParens(match[2]),
    };
}
function parseImageTerm(term) {
    const value = stripParens(term);
    const wordForm = value.match(/^image\((.+)\)$/i);
    if (!wordForm)
        return null;
    const parts = splitTopLevel(wordForm[1], ',');
    if (!parts)
        return null;
    return {
        fn: stripParens(parts[0]),
        set: stripParens(parts[1]),
    };
}
function parsePreimageTerm(term) {
    const value = stripParens(term);
    const wordForm = value.match(/^preimage\((.+)\)$/i);
    if (wordForm) {
        const parts = splitTopLevel(wordForm[1], ',');
        if (!parts)
            return null;
        return {
            fn: stripParens(parts[0]),
            set: stripParens(parts[1]),
        };
    }
    const symbolic = value.match(/^([A-Za-z_][A-Za-z0-9_.]*)(\^-1|⁻¹)\((.+)\)$/);
    if (!symbolic)
        return null;
    return {
        fn: stripParens(symbolic[1]),
        set: stripParens(symbolic[3]),
    };
}
function parseSetBuilderTerm(term) {
    return (0, propositions_1.parseSetBuilderCanonical)(term);
}
function parseIndexedUnionTerm(term) {
    return (0, propositions_1.parseIndexedUnionCanonical)(term);
}
function parseMembershipQuantifier(claim) {
    const typed = parseTypedQuantifierProp(claim, 'forall');
    if (typed && typed.body) {
        const membership = parseMembershipProp(typed.body);
        if (membership && (0, propositions_1.sameProp)(membership.element, typed.variable)) {
            return { domain: typed.domain, membershipSet: membership.set };
        }
    }
    const bounded = parseBoundedQuantifierProp(claim, 'forall');
    if (bounded && bounded.body) {
        const membership = parseMembershipProp(bounded.body);
        if (membership && (0, propositions_1.sameProp)(membership.element, bounded.variable)) {
            return { domain: bounded.set, membershipSet: membership.set };
        }
    }
    return null;
}
function findMembershipQuantifierClaim(domain, targetSet, claims) {
    for (const claim of claims) {
        const info = parseMembershipQuantifier(claim);
        if (!info)
            continue;
        if (matchesDomainTerm(domain, info.domain) && (0, propositions_1.sameProp)(info.membershipSet, targetSet)) {
            return claim;
        }
    }
    return null;
}
function matchesDomainTerm(expected, actual) {
    return (0, propositions_1.sameProp)(expected, actual) || sameSetBuilderTerm(expected, actual) || sameSetBuilderTerm(actual, expected);
}
function sameSetBuilderTerm(left, right) {
    const leftBuilder = parseSetBuilderOrUnion(left);
    const rightBuilder = parseSetBuilderOrUnion(right);
    if (!leftBuilder || !rightBuilder)
        return false;
    if (!(0, propositions_1.sameProp)(leftBuilder.domain, rightBuilder.domain))
        return false;
    const leftNormalized = normalizeBuilderTemplate(leftBuilder.elementTemplate, leftBuilder.variable);
    const rightNormalized = normalizeBuilderTemplate(rightBuilder.elementTemplate, rightBuilder.variable);
    return (0, propositions_1.sameProp)(leftNormalized, rightNormalized);
}
function normalizeBuilderTemplate(template, variable) {
    return substitutePatternVariable(template, variable, '__MEMBER__');
}
function parseSetBuilderOrUnion(term) {
    return (0, propositions_1.parseSetBuilderOrUnionCanonical)(term);
}
function resolveSetEqualityDependency(claim, availableClaims) {
    const equality = parseEqualityProp(claim);
    if (!equality)
        return null;
    const leftQuantifier = findMembershipQuantifierClaim(equality.left, equality.right, availableClaims);
    const rightQuantifier = findMembershipQuantifierClaim(equality.right, equality.left, availableClaims);
    if (!leftQuantifier || !rightQuantifier)
        return null;
    return { leftQuantifier, rightQuantifier };
}
function resolveSetEqualityScopeFromInputs(claim, inputs) {
    return resolveSetEqualityDependency(claim, inputs);
}
function parseBinarySetProp(prop, operator) {
    return (0, propositions_1.parseBinarySetCanonical)(stripParens(prop), operator);
}
function parseBoundedQuantifierProp(prop, kind) {
    return (0, propositions_1.parseBoundedQuantifierCanonical)(prop, kind);
}
function parseTypedQuantifierProp(prop, kind) {
    return (0, propositions_1.parseTypedQuantifierCanonical)(prop, kind);
}
function parseStandaloneBoundedQuantifierProp(prop, kind) {
    return (0, propositions_1.parseStandaloneBoundedQuantifierCanonical)(prop, kind);
}
function parseStandaloneTypedQuantifierProp(prop, kind) {
    return (0, propositions_1.parseStandaloneTypedQuantifierCanonical)(prop, kind);
}
function parseTypedVariableProp(prop) {
    return (0, propositions_1.parseTypedVariableCanonical)(prop);
}
function parseProductExpression(value) {
    const parts = splitTopLevel(stripParens(value), '·');
    if (!parts)
        return null;
    return { left: stripParens(parts[0]), right: stripParens(parts[1]) };
}
function parseDividesProp(prop) {
    const match = stripParens(prop).match(/^(.+?)\s+divides\s+(.+)$/);
    if (!match)
        return null;
    return {
        divisor: stripParens(match[1].trim()),
        dividend: stripParens(match[2].trim()),
    };
}
function lowerUniqueExistenceClaim(claim) {
    const typed = parseTypedQuantifierProp(claim, 'exists_unique');
    if (typed) {
        const existenceClaim = `∃ ${typed.variable}: ${typed.domain}, ${typed.body}`;
        const uniquenessClaim = buildTypedUniquenessClaim(typed.variable, typed.domain, typed.body);
        return { existenceClaim, uniquenessClaim };
    }
    const bounded = parseBoundedQuantifierProp(claim, 'exists_unique');
    if (bounded) {
        const existenceClaim = `∃ ${bounded.variable} ∈ ${bounded.set}, ${bounded.body}`;
        const uniquenessClaim = buildBoundedUniquenessClaim(bounded.variable, bounded.set, bounded.body);
        return { existenceClaim, uniquenessClaim };
    }
    return null;
}
function buildTypedUniquenessClaim(variable, domain, body) {
    const yBody = instantiateBoundedQuantifier({ variable, body }, 'y') ?? body;
    const zBody = instantiateBoundedQuantifier({ variable, body }, 'z') ?? body;
    return `∀ y: ${domain}, ∀ z: ${domain}, ${yBody} ∧ ${zBody} → y = z`;
}
function buildBoundedUniquenessClaim(variable, set, body) {
    const yBody = instantiateBoundedQuantifier({ variable, body }, 'y') ?? body;
    const zBody = instantiateBoundedQuantifier({ variable, body }, 'z') ?? body;
    return `∀ y ∈ ${set}, ∀ z ∈ ${set}, ${yBody} ∧ ${zBody} → y = z`;
}
function normalizeTypeDomain(value) {
    return (0, propositions_1.normalizeProp)(value
        .replace(/\bNat\b/g, 'ℕ')
        .replace(/\bnat\b/g, 'ℕ')
        .replace(/\bInt\b/g, 'ℤ')
        .replace(/\bint\b/g, 'ℤ')
        .replace(/\bRat\b/g, 'ℚ')
        .replace(/\brat\b/g, 'ℚ')
        .replace(/\bReal\b/g, 'ℝ')
        .replace(/\breal\b/g, 'ℝ'));
}
function sameTypeDomain(left, right) {
    return normalizeTypeDomain(left) === normalizeTypeDomain(right);
}
function isSupportedArithmeticTerm(term) {
    const value = stripParens(term);
    const product = parseProductExpression(value);
    if (product) {
        return isSupportedArithmeticTerm(product.left) && isSupportedArithmeticTerm(product.right);
    }
    if (/^\|.+\|$/.test(value))
        return true;
    if (/^\[[^:\]]+:[^\]]+\]$/.test(value))
        return true;
    if (/^[A-Za-z_][\w₀-₉ₐ-ₙ]*$/.test(value))
        return true;
    if (/^\d+$/.test(value))
        return true;
    return false;
}
function isSetBuilderLikeTerm(term) {
    return (0, propositions_1.isSetBuilderLikeCanonical)(term);
}
function escapeRegExp(value) {
    return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}
function substitutePatternVariable(pattern, variable, witness) {
    const standalone = new RegExp(`(?<![\\w₀-₉ₐ-ₙ])${escapeRegExp(variable)}(?![\\w₀-₉ₐ-ₙ])`, 'g');
    const prefixed = new RegExp(`(?<![\\w₀-₉ₐ-ₙ])${escapeRegExp(variable)}(?=[A-Z])`, 'g');
    return pattern.replace(standalone, witness).replace(prefixed, witness);
}
function resolveSetBuilderIntroDependency(claim, availableClaims) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const builder = parseSetBuilderTerm(output.set);
    if (!builder)
        return null;
    for (const available of availableClaims) {
        const witness = parseMembershipProp(available);
        if (!witness || !(0, propositions_1.sameProp)(witness.set, builder.domain))
            continue;
        const expectedElement = substitutePatternVariable(builder.elementTemplate, builder.variable, witness.element);
        if ((0, propositions_1.sameProp)(output.element, expectedElement)) {
            return { witnessMembership: available };
        }
    }
    return null;
}
function resolveIndexedUnionIntroDependency(claim, availableClaims) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    const indexedUnion = parseIndexedUnionTerm(output.set);
    if (!indexedUnion)
        return null;
    for (const available of availableClaims) {
        const witness = parseMembershipProp(available);
        if (!witness || !(0, propositions_1.sameProp)(witness.set, indexedUnion.domain))
            continue;
        const instantiatedSet = substitutePatternVariable(indexedUnion.elementTemplate, indexedUnion.variable, witness.element);
        const bodyMembership = `${output.element} ∈ ${instantiatedSet}`;
        if (availableClaims.some(item => (0, propositions_1.sameProp)(item, bodyMembership))) {
            return { witnessMembership: available, bodyMembership };
        }
    }
    return null;
}
function splitTopLevel(prop, operator) {
    let depth = 0;
    for (let i = 0; i < prop.length; i++) {
        const ch = prop[i];
        if (ch === '(')
            depth++;
        else if (ch === ')')
            depth = Math.max(0, depth - 1);
        else if (depth === 0 && prop.slice(i, i + operator.length) === operator) {
            const left = stripParens(prop.slice(0, i).trim());
            const right = stripParens(prop.slice(i + operator.length).trim());
            if (left && right)
                return [left, right];
        }
    }
    return null;
}
function supportsEqualitySubstitution(equalityClaim, membershipClaim, target) {
    const equality = parseEqualityProp(equalityClaim);
    const membership = parseMembershipProp(membershipClaim);
    const output = parseMembershipProp(target);
    if (!equality || !membership || !output)
        return false;
    const equalityPairs = [
        [equality.left, equality.right],
        [equality.right, equality.left],
    ];
    return equalityPairs.some(([from, to]) => {
        const elementSubst = (0, propositions_1.sameProp)(membership.element, from)
            && (0, propositions_1.sameProp)(output.element, to)
            && (0, propositions_1.sameProp)(membership.set, output.set);
        const setSubst = (0, propositions_1.sameProp)(membership.set, from)
            && (0, propositions_1.sameProp)(output.set, to)
            && (0, propositions_1.sameProp)(membership.element, output.element);
        return elementSubst || setSubst;
    });
}
function supportsEqualityTransitivity(leftEqualityClaim, rightEqualityClaim, target) {
    const left = parseEqualityProp(leftEqualityClaim);
    const right = parseEqualityProp(rightEqualityClaim);
    const output = parseEqualityProp(target);
    if (!left || !right || !output)
        return false;
    const leftVariants = [
        [left.left, left.right],
        [left.right, left.left],
    ];
    const rightVariants = [
        [right.left, right.right],
        [right.right, right.left],
    ];
    for (const [a, b] of leftVariants) {
        for (const [c, d] of rightVariants) {
            if ((0, propositions_1.sameProp)(b, c) &&
                (0, propositions_1.sameProp)(output.left, a) &&
                (0, propositions_1.sameProp)(output.right, d)) {
                return true;
            }
        }
    }
    return false;
}
function supportsDividesFromEquality(equalityClaim, target) {
    const equality = parseEqualityProp(equalityClaim);
    const divides = parseDividesProp(target);
    if (!equality || !divides)
        return false;
    if (!(0, propositions_1.sameProp)(equality.left, divides.dividend))
        return false;
    const product = parseProductExpression(equality.right);
    if (!product)
        return false;
    return (0, propositions_1.sameProp)(product.left, divides.divisor) || (0, propositions_1.sameProp)(product.right, divides.divisor);
}
function supportsArithmeticCommutativeEquality(sourceClaim, target) {
    const source = parseEqualityProp(sourceClaim);
    const output = parseEqualityProp(target);
    if (!source || !output)
        return false;
    if (!(0, propositions_1.sameProp)(source.left, output.left))
        return false;
    const sourceProduct = parseProductExpression(source.right);
    const outputProduct = parseProductExpression(output.right);
    if (!sourceProduct || !outputProduct)
        return false;
    return (0, propositions_1.sameProp)(sourceProduct.left, outputProduct.right) && (0, propositions_1.sameProp)(sourceProduct.right, outputProduct.left);
}
function findArithmeticWitnessedBody(ctx, bodyPattern, placeholder, witness) {
    const instantiated = instantiateBoundedQuantifier({ variable: placeholder, body: bodyPattern }, witness);
    if (!instantiated)
        return null;
    const exact = findLatestProofObjectByClaim(ctx, instantiated);
    if (exact)
        return exact;
    return findLatestProofObject(ctx, object => supportsArithmeticCommutativeEquality(object.claim, instantiated));
}
function instantiateBoundedQuantifier(quantifier, witness) {
    const variablePattern = new RegExp(`(^|[^\\w₀-₉ₐ-ₙ])${escapeRegExp(quantifier.variable)}([^\\w₀-₉ₐ-ₙ]|$)`, 'g');
    if (!variablePattern.test(quantifier.body) && !(0, propositions_1.sameProp)(quantifier.body, quantifier.variable)) {
        return null;
    }
    variablePattern.lastIndex = 0;
    return quantifier.body.replace(variablePattern, (_, left, right) => `${left}${witness}${right}`);
}
function findExistsElimScope(quantifier, target, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const membership = ctx.proofObjects[i];
        const membershipProp = parseMembershipProp(membership.claim);
        if (!membershipProp || membership.source !== 'assumption' || !(0, propositions_1.sameProp)(membershipProp.set, quantifier.set))
            continue;
        const witness = membershipProp.element;
        if (!ctx.variables.some(variable => (0, propositions_1.sameProp)(variable.name, witness)))
            continue;
        const instantiatedBody = instantiateBoundedQuantifier(quantifier, witness);
        if (!instantiatedBody)
            continue;
        const body = findLatestProofObjectByClaim(ctx, instantiatedBody, object => object.source === 'assumption');
        if (!body)
            continue;
        if (!containsFreeLikeVariable(target, witness)) {
            return {
                witness,
                membership,
                body,
                dischargedScopeIds: scopesThrough(ctx, membership.scopeIds[membership.scopeIds.length - 1]),
            };
        }
    }
    return null;
}
function findForallInIntroScope(quantifier, ctx) {
    const target = `∀ ${quantifier.variable} ∈ ${quantifier.set}, ${quantifier.body}`;
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const membership = ctx.proofObjects[i];
        const membershipProp = parseMembershipProp(membership.claim);
        if (!membershipProp || membership.source !== 'assumption' || !(0, propositions_1.sameProp)(membershipProp.set, quantifier.set))
            continue;
        const witness = membershipProp.element;
        if (!ctx.variables.some(variable => (0, propositions_1.sameProp)(variable.name, witness)))
            continue;
        const instantiatedBody = instantiateBoundedQuantifier(quantifier, witness);
        if (!instantiatedBody)
            continue;
        const body = findLatestProofObjectByClaim(ctx, instantiatedBody);
        if (!body)
            continue;
        if (isFreshScopedWitness(witness, quantifier, target)) {
            return {
                witness,
                membership,
                body,
                dischargedScopeIds: scopesThrough(ctx, membership.scopeIds[membership.scopeIds.length - 1]),
            };
        }
    }
    return null;
}
function findSubsetIntroScope(target, ctx) {
    const targetClaim = `${target.left} ⊆ ${target.right}`;
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const membership = ctx.proofObjects[i];
        const membershipProp = parseMembershipProp(membership.claim);
        if (!membershipProp || membership.source !== 'assumption' || !(0, propositions_1.sameProp)(membershipProp.set, target.left))
            continue;
        const witness = membershipProp.element;
        if (!ctx.variables.some(variable => (0, propositions_1.sameProp)(variable.name, witness)))
            continue;
        const bodyClaim = `${witness} ∈ ${target.right}`;
        const body = findLatestProofObjectByClaim(ctx, bodyClaim);
        if (!body)
            continue;
        if (!containsFreeLikeVariable(targetClaim, witness)) {
            return {
                witness,
                membership,
                body,
                dischargedScopeIds: scopesThrough(ctx, membership.scopeIds[membership.scopeIds.length - 1]),
            };
        }
    }
    return null;
}
function findIndexedUnionElimScope(unionMembershipClaim, target, ctx) {
    const unionMembership = parseMembershipProp(unionMembershipClaim);
    if (!unionMembership)
        return null;
    const indexedUnion = parseIndexedUnionTerm(unionMembership.set);
    if (!indexedUnion)
        return null;
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const witnessMembership = ctx.proofObjects[i];
        const witnessProp = parseMembershipProp(witnessMembership.claim);
        if (!witnessProp || witnessMembership.source !== 'assumption' || !(0, propositions_1.sameProp)(witnessProp.set, indexedUnion.domain))
            continue;
        const witness = witnessProp.element;
        if (!ctx.variables.some(variable => (0, propositions_1.sameProp)(variable.name, witness)))
            continue;
        const instantiatedSet = substitutePatternVariable(indexedUnion.elementTemplate, indexedUnion.variable, witness);
        const bodyClaim = `${unionMembership.element} ∈ ${instantiatedSet}`;
        const bodyMembership = findLatestProofObjectByClaim(ctx, bodyClaim, object => object.source === 'assumption');
        if (!bodyMembership)
            continue;
        if (!containsFreeLikeVariable(target, witness)) {
            return {
                witness,
                witnessMembership,
                bodyMembership,
                dischargedScopeIds: scopesThrough(ctx, witnessMembership.scopeIds[witnessMembership.scopeIds.length - 1]),
            };
        }
    }
    return null;
}
function findForallTypedIntroScope(quantifier, ctx) {
    const target = `∀ ${quantifier.variable}: ${quantifier.domain}, ${quantifier.body}`;
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const witness = ctx.proofObjects[i];
        const typedWitness = parseTypedVariableProp(witness.claim);
        if (!typedWitness || witness.source !== 'variable' || !sameTypeDomain(typedWitness.domain, quantifier.domain))
            continue;
        const witnessName = typedWitness.variable;
        if (!ctx.variables.some(variable => (0, propositions_1.sameProp)(variable.name, witnessName)))
            continue;
        const instantiatedBody = instantiateBoundedQuantifier(quantifier, witnessName);
        if (!instantiatedBody)
            continue;
        const body = findLatestProofObjectByClaim(ctx, instantiatedBody);
        if (!body)
            continue;
        if (isFreshScopedWitness(witnessName, quantifier, target)) {
            return {
                witnessName,
                witness,
                body,
                dischargedScopeIds: scopesThrough(ctx, witness.scopeIds[witness.scopeIds.length - 1]),
            };
        }
    }
    return null;
}
function findExistsTypedElimScope(quantifier, target, ctx) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const witness = ctx.proofObjects[i];
        const typedWitness = parseTypedVariableProp(witness.claim);
        if (!typedWitness || witness.source !== 'variable' || !sameTypeDomain(typedWitness.domain, quantifier.domain))
            continue;
        const witnessName = typedWitness.variable;
        if (!ctx.variables.some(variable => (0, propositions_1.sameProp)(variable.name, witnessName)))
            continue;
        const instantiatedBody = instantiateBoundedQuantifier(quantifier, witnessName);
        if (!instantiatedBody)
            continue;
        const body = findLatestProofObjectByClaim(ctx, instantiatedBody);
        if (!body)
            continue;
        if (!containsFreeLikeVariable(target, witnessName)) {
            return {
                witnessName,
                witness,
                body,
                dischargedScopeIds: scopesThrough(ctx, witness.scopeIds[witness.scopeIds.length - 1]),
            };
        }
    }
    return null;
}
function resolveExistsElimScopeFromInputs(quantifier, claims, target) {
    for (const claim of claims) {
        const membership = parseMembershipProp(claim);
        if (!membership || !(0, propositions_1.sameProp)(membership.set, quantifier.set))
            continue;
        const instantiatedBody = instantiateBoundedQuantifier(quantifier, membership.element);
        if (!instantiatedBody)
            continue;
        if (claims.some(other => (0, propositions_1.sameProp)(other, instantiatedBody)) && !containsFreeLikeVariable(target, membership.element)) {
            return { witness: membership.element };
        }
    }
    return null;
}
function resolveIndexedUnionElimScopeFromInputs(indexedUnion, unionElement, claims, target) {
    for (const claim of claims) {
        const witness = parseMembershipProp(claim);
        if (!witness || !(0, propositions_1.sameProp)(witness.set, indexedUnion.domain))
            continue;
        const instantiatedSet = substitutePatternVariable(indexedUnion.elementTemplate, indexedUnion.variable, witness.element);
        const bodyMembership = `${unionElement} ∈ ${instantiatedSet}`;
        if (claims.some(other => (0, propositions_1.sameProp)(other, bodyMembership)) && !containsFreeLikeVariable(target, witness.element)) {
            return { witness: witness.element };
        }
    }
    return null;
}
function resolveExistsTypedElimScopeFromInputs(quantifier, claims, target) {
    for (const claim of claims) {
        const witness = parseTypedVariableProp(claim);
        if (!witness || !sameTypeDomain(witness.domain, quantifier.domain))
            continue;
        const instantiatedBody = instantiateBoundedQuantifier(quantifier, witness.variable);
        if (!instantiatedBody)
            continue;
        if (claims.some(other => (0, propositions_1.sameProp)(other, instantiatedBody)) && !containsFreeLikeVariable(target, witness.variable)) {
            return { witness: witness.variable };
        }
    }
    return null;
}
function containsFreeLikeVariable(value, variable) {
    const pattern = new RegExp(`(^|[^\\w₀-₉ₐ-ₙ])${escapeRegExp(variable)}([^\\w₀-₉ₐ-ₙ]|$)`);
    return pattern.test(value);
}
function isFreshScopedWitness(witness, quantifier, target) {
    if ((0, propositions_1.sameProp)(witness, quantifier.variable))
        return false;
    if (containsFreeLikeVariable(target, witness))
        return false;
    return instantiateBoundedQuantifier(quantifier, witness) !== null;
}
function isKernelCheckableAtom(value) {
    return kernelSubsetGap(value) === null;
}
function kernelSubsetDiagnostic(expr, label, step) {
    if (expr.type === 'Atom' && expr.atomKind === 'opaque')
        return null;
    const gap = kernelSubsetGap(exprToString(expr));
    if (!gap)
        return null;
    return {
        severity: 'info',
        message: `${label} needs kernel rule ${gap.rule}, which is outside the current self-contained kernel.`,
        step,
        rule: 'STRUCTURAL',
        hint: gap.hint,
    };
}
function kernelSubsetGap(value) {
    const implication = parseImplicationProp(value);
    if (implication) {
        return kernelSubsetGap(implication[0]) ?? kernelSubsetGap(implication[1]);
    }
    const conjunction = parseConjunctionProp(value);
    if (conjunction) {
        return kernelSubsetGap(conjunction[0]) ?? kernelSubsetGap(conjunction[1]);
    }
    const disjunction = parseDisjunctionProp(value);
    if (disjunction) {
        return kernelSubsetGap(disjunction[0]) ?? kernelSubsetGap(disjunction[1]);
    }
    const iff = parseIffProp(value);
    if (iff) {
        return kernelSubsetGap(iff[0]) ?? kernelSubsetGap(iff[1]);
    }
    if (value.startsWith('¬')) {
        return kernelSubsetGap(stripParens(value.slice(1)));
    }
    const forall = parseBoundedQuantifierProp(value, 'forall');
    if (forall) {
        return kernelSubsetGap(forall.body);
    }
    const typedForall = parseTypedQuantifierProp(value, 'forall');
    if (typedForall) {
        return kernelSubsetGap(typedForall.body);
    }
    const exists = parseBoundedQuantifierProp(value, 'exists');
    if (exists) {
        return kernelSubsetGap(exists.body);
    }
    const typedExists = parseTypedQuantifierProp(value, 'exists');
    if (typedExists) {
        return kernelSubsetGap(typedExists.body);
    }
    const typedExistsUnique = parseTypedQuantifierProp(value, 'exists_unique');
    if (typedExistsUnique) {
        return {
            rule: 'EXISTS_UNIQUE',
            hint: 'Unique existence is preserved and partially lowered, but nested ∃! goals are not fully kernel-checked yet.',
        };
    }
    const boundedExistsUnique = parseBoundedQuantifierProp(value, 'exists_unique');
    if (boundedExistsUnique) {
        return {
            rule: 'EXISTS_UNIQUE',
            hint: 'Unique existence is preserved and partially lowered, but nested ∃! goals are not fully kernel-checked yet.',
        };
    }
    const standaloneTypedExistsUnique = parseStandaloneTypedQuantifierProp(value, 'exists_unique');
    if (standaloneTypedExistsUnique) {
        return {
            rule: 'EXISTS_UNIQUE',
            hint: 'Standalone unique-existence binders are preserved, but they still need an explicit body or lowering rule to be fully checked.',
        };
    }
    const standaloneBoundedExistsUnique = parseStandaloneBoundedQuantifierProp(value, 'exists_unique');
    if (standaloneBoundedExistsUnique) {
        return {
            rule: 'EXISTS_UNIQUE',
            hint: 'Standalone unique-existence binders are preserved, but they still need an explicit body or lowering rule to be fully checked.',
        };
    }
    const equality = parseEqualityProp(value);
    if (equality && (isSetBuilderLikeTerm(equality.left) || isSetBuilderLikeTerm(equality.right))) {
        return {
            rule: 'SET_OPERATOR_REASONING',
            hint: 'Set-builder and indexed-union equalities are preserved structurally, but not fully kernel-checked yet.',
        };
    }
    const divides = parseDividesProp(value);
    if (divides) {
        if (isSupportedArithmeticTerm(divides.divisor) && isSupportedArithmeticTerm(divides.dividend)) {
            return null;
        }
        return {
            rule: 'ARITHMETIC_REASONING',
            hint: 'Only simple divisibility claims over identifier/cardinality/index terms are kernel-checked today.',
        };
    }
    if (equality && (/[|]|\[[^\]]+:[^\]]+\]|·/.test(equality.left) || /[|]|\[[^\]]+:[^\]]+\]|·/.test(equality.right))) {
        if (isSetBuilderLikeTerm(equality.left) || isSetBuilderLikeTerm(equality.right)) {
            return {
                rule: 'SET_OPERATOR_REASONING',
                hint: 'Set-builder and indexed-union equalities are preserved structurally, but not fully kernel-checked yet.',
            };
        }
        if (isSupportedArithmeticTerm(equality.left) && isSupportedArithmeticTerm(equality.right)) {
            return null;
        }
        return {
            rule: 'ARITHMETIC_REASONING',
            hint: 'Only simple equalities over identifier/cardinality/index/product terms are kernel-checked today.',
        };
    }
    if (/[|]|\[[^\]]+:[^\]]+\]|\bdivides\b|·/.test(value) && !isSetBuilderLikeTerm(value)) {
        return {
            rule: 'ARITHMETIC_REASONING',
            hint: 'Arithmetic/cardinality/index reasoning is outside the current self-contained kernel.',
        };
    }
    if (/∀\s*[^,]*∈/.test(value) || /^∀/.test(value)) {
        return {
            rule: 'FORALL_BINDER',
            hint: 'Only bounded universal quantifiers in the form `∀x ∈ A, P(x)` are kernel-checked today.',
        };
    }
    if (/∃\s*[^,]*∈/.test(value) || /^∃/.test(value)) {
        return {
            rule: 'EXISTS_BINDER',
            hint: 'Only bounded existential quantifiers in the form `∃x ∈ A, P(x)` are kernel-checked today.',
        };
    }
    const membership = parseMembershipProp(value);
    if (membership) {
        const union = parseBinarySetProp(membership.set, '∪');
        if (union)
            return null;
        const intersection = parseBinarySetProp(membership.set, '∩');
        if (intersection)
            return null;
        return null;
    }
    if (parseSubsetProp(value))
        return null;
    if (equality)
        return null;
    if (/[∪∩]/.test(value)) {
        return {
            rule: 'SET_OPERATOR_REASONING',
            hint: 'Only membership introduction/elimination over unions and intersections is kernel-checked today.',
        };
    }
    return null;
}
// ── New derived-claim checkers for Phase 4 rules ──────────────────────────────
function checkOrElimDerivedClaim(claim, ctx) {
    for (const item of visibleEstablishedClaims(ctx)) {
        const disj = parseDisjunctionProp(item.content);
        if (!disj)
            continue;
        const [left, right] = disj;
        const leftImpl = `${left} → ${claim}`;
        const rightImpl = `${right} → ${claim}`;
        const result = (0, rules_1.checkOrElim)(item.content, leftImpl, rightImpl, claim, ctx);
        if (result.valid)
            return result;
    }
    return null;
}
function checkNotElimDerivedClaim(claim, ctx) {
    const doubleNeg = `¬¬${claim}`;
    const result = (0, rules_1.checkNotElim)(doubleNeg, claim, ctx);
    return result.valid ? result : null;
}
function checkNotIntroDerivedClaim(claim, ctx) {
    const inner = extractNegand(claim);
    if (!inner)
        return null;
    const result = (0, rules_1.checkNotIntro)(inner, claim, ctx);
    return result.valid ? result : null;
}
function checkExFalsoDerivedClaim(claim, ctx) {
    const result = (0, rules_1.checkExFalso)(claim, ctx);
    return result.valid ? result : null;
}
// ── Disjunction helpers ───────────────────────────────────────────────────────
function parseDisjunctionProp(prop) {
    return (0, propositions_1.parseDisjunctionCanonical)(prop);
}
function isDisjunction(expr) {
    return expr.type === 'Or';
}
function splitDisjunction(expr) {
    return (0, propositions_1.splitDisjunction)(expr) ?? ['', ''];
}
// ── Negation helpers ──────────────────────────────────────────────────────────
// Extract the proposition P from ¬P (returns null if input is not a negation)
function extractNegand(claim) {
    const s = claim.trim();
    if (s.startsWith('¬'))
        return s.slice(1).trim();
    if (s.startsWith('not '))
        return s.slice(4).trim();
    return null;
}
// ── Sort scope helpers ────────────────────────────────────────────────────────
// Extract variables from a claim and add them to the sort scope.
// Handles membership claims like x ∈ A → x: Element, A: Set
// Handles subset claims like A ⊆ B → A: Set, B: Set
function extractSortScopeFromClaim(claim, sortScope) {
    const s = claim.trim();
    // Membership: x ∈ A
    const membershipMatch = s.match(/^(.+?)\s*∈\s*(.+)$/);
    if (membershipMatch) {
        const left = membershipMatch[1].trim();
        const right = membershipMatch[2].trim();
        const app = parseFunctionApplicationTerm(left);
        if (app) {
            if (/^[a-z][a-z0-9_]*$/.test(app.arg))
                sortScope.set(app.arg, 'Element');
        }
        else {
            const leftId = left.replace(/[()]/g, '').trim().split(/\s/)[0];
            if (/^[a-z][a-z0-9_]*$/.test(leftId))
                sortScope.set(leftId, 'Element');
        }
        const preimage = parsePreimageTerm(right);
        const rightIds = (preimage ? preimage.set : right).replace(/[()]/g, '').trim().match(/[A-Z][A-Za-z0-9_]*/g) || [];
        for (const id of rightIds)
            sortScope.set(id, 'Set');
        return;
    }
    // Subset: A ⊆ B (also handles compound expressions)
    const subsetMatch = s.match(/^(.+?)\s*[⊆⊂]\s*(.+)$/);
    if (subsetMatch) {
        const left = subsetMatch[1].trim().replace(/[()]/g, '').trim();
        const right = subsetMatch[2].trim().replace(/[()]/g, '').trim();
        const leftIds = left.match(/[A-Z][A-Za-z0-9_]*/g) || [];
        const rightIds = right.match(/[A-Z][A-Za-z0-9_]*/g) || [];
        for (const id of leftIds)
            sortScope.set(id, 'Set');
        for (const id of rightIds)
            sortScope.set(id, 'Set');
        return;
    }
    // Equality: x = y
    const equalityMatch = s.match(/^(.+?)\s*=\s*(.+)$/);
    if (equalityMatch && !s.includes('==')) {
        const left = equalityMatch[1].trim().replace(/[()]/g, '').trim();
        const right = equalityMatch[2].trim().replace(/[()]/g, '').trim();
        const leftSort = (0, sorts_1.inferIdentifierSort)(left);
        const rightSort = (0, sorts_1.inferIdentifierSort)(right);
        if (leftSort !== null)
            sortScope.set(left, leftSort);
        if (rightSort !== null)
            sortScope.set(right, rightSort);
    }
}
// Check scope for a set-theoretic claim: every identifier must be in sortScope with correct sort.
// Only checks top-level identifiers in set-theoretic expressions.
function checkScopeForClaim(claim, ctx, step) {
    const s = claim.trim();
    // Only check claims with set-theoretic operators
    if (!/[∈⊆⊂∪∩]/.test(s))
        return null;
    const membershipMatch = s.match(/^(.+?)\s*∈\s*(.+)$/);
    if (membershipMatch) {
        const left = membershipMatch[1].trim();
        const right = membershipMatch[2].trim();
        const app = parseFunctionApplicationTerm(left);
        const leftId = app ? app.arg : left.replace(/[()]/g, '').trim().split(/\s/)[0];
        const preimage = parsePreimageTerm(right);
        const rightId = (preimage ? preimage.set : right).replace(/[()]/g, '').trim().split(/\s/)[0].replace(/[^A-Za-z0-9_]/g, '');
        const leftSort = (0, sorts_1.inferIdentifierSort)(leftId);
        const rightSort = (0, sorts_1.inferIdentifierSort)(rightId);
        if (leftSort === 'Element' && !ctx.sortScope.has(leftId)) {
            return { severity: 'error', message: `Scope error: variable '${leftId}' used in '${claim}' but not introduced in any given/assume/setVar`, step, rule: 'STRUCTURAL' };
        }
        if (rightSort === 'Set' && rightId && !ctx.sortScope.has(rightId)) {
            return { severity: 'error', message: `Scope error: set '${rightId}' used in '${claim}' but not introduced in any given/assume/setVar`, step, rule: 'STRUCTURAL' };
        }
    }
    return null;
}
// Resolve a setVar type annotation to a sort
function resolveVarTypeSort(varType) {
    if (!varType)
        return null;
    const t = varType.trim().toLowerCase();
    if (t === 'element' || t === 'elem')
        return 'Element';
    if (t === 'set')
        return 'Set';
    return null;
}
function stripParens(value) {
    let result = value.trim();
    while (result.startsWith('(') && result.endsWith(')')) {
        const inner = result.slice(1, -1).trim();
        if (!inner)
            break;
        if (!hasBalancedParens(inner))
            break;
        result = inner;
    }
    return result;
}
function hasBalancedParens(value) {
    let depth = 0;
    for (const ch of value) {
        if (ch === '(')
            depth++;
        else if (ch === ')') {
            depth--;
            if (depth < 0)
                return false;
        }
    }
    return depth === 0;
}
