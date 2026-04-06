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
                const report = checkProofBlock(node.name, node.body, globalLemmas, 'unknown');
                reports.push(report);
            }
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
function checkPair(thm, proof, globalLemmas) {
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
    const proofReport = checkProofBlock(proof.name, proof.body, globalLemmas, method, theoremGoal, theoremPremises);
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
        premises: theoremPremises,
        derivedConclusion: proofReport.derivedConclusion,
        proofSteps: proofReport.proofSteps,
        proofObjects: proofReport.proofObjects,
        derivations: proofReport.derivations,
        baseFactIds: proofReport.baseFactIds,
        derivedFactIds: proofReport.derivedFactIds,
        diagnostics,
        metrics: proofReport.metrics,
    };
}
// ── Check a proof body ────────────────────────────────────────────────────────
function checkProofBlock(name, body, globalLemmas, method, goal = null, premises = []) {
    const diagnostics = [];
    const premiseClaims = premises.map((content, index) => ({
        content,
        source: 'premise',
        step: -(index + 1),
        proofObjectId: makeProofObjectId(-(index + 1), 'premise', content),
    }));
    const ctx = {
        established: premiseClaims,
        proofObjects: premiseClaims.map(claim => ({
            id: claim.proofObjectId,
            claim: claim.content,
            rule: 'PREMISE',
            source: claim.source,
            step: claim.step,
            dependsOn: [],
            dependsOnIds: [],
        })),
        derivations: [],
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
                const result = (0, rules_1.checkAssumption)(claim);
                if (!result.valid) {
                    diagnostics.push({ severity: 'error', message: result.message, step, rule: result.rule });
                }
                registerAssumptionClaim(ctx, claim, step, result.rule);
                proofSteps.push({
                    step,
                    kind: 'assume',
                    claim,
                    rule: result.rule,
                    valid: result.valid,
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
                // Check for sorry (explicit gap)
                if (claim.toLowerCase().includes('sorry')) {
                    hasSorry = true;
                    diagnostics.push({ severity: 'info', message: `Step ${step}: sorry placeholder`, rule: 'SORRY' });
                    registerAssertionClaim(ctx, claim, step, 'SORRY');
                    proofSteps.push({
                        step,
                        kind: 'assert',
                        claim,
                        rule: 'SORRY',
                        valid: true,
                        message: 'sorry placeholder',
                    });
                    break;
                }
                // Check and/intro: if claim is a conjunction, verify both sides
                let stepRule = null;
                if (isConjunction(n.expr)) {
                    const [left, right] = splitConjunction(n.expr);
                    const andResult = (0, rules_1.checkAndIntro)(left, right, ctx);
                    stepRule = andResult;
                    if (!andResult.valid) {
                        // Warning not error — the conjunction may be introducing new facts
                        diagnostics.push({ severity: 'info', message: andResult.message, step, hint: andResult.hint });
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
                if (!finalizedAssertion.result.valid && stepRule?.valid !== false) {
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
                    valid: finalizedAssertion.result.valid,
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
                const contradictionDischarge = checkContradictionDischarge(claim, ctx);
                const forallDischarge = checkForallGoalDischarge(claim, ctx);
                const derivation = isConjunction(n.expr)
                    ? (0, rules_1.checkAndIntro)(...splitConjunction(n.expr), ctx)
                    : contradictionDischarge ?? checkDerivedClaim(claim, ctx) ?? forallDischarge ?? checkImplicationGoalDischarge(claim, ctx);
                if (derivation && !derivation.valid) {
                    diagnostics.push({ severity: 'error', message: derivation.message, step, hint: derivation.hint, rule: derivation.rule });
                }
                const finalizedConclusion = registerDerivedClaim(ctx, {
                    content: claim,
                    source: 'conclusion',
                    step,
                    derivation,
                });
                if (!finalizedConclusion.result.valid) {
                    diagnostics.push({ severity: 'error', message: finalizedConclusion.result.message, step, hint: finalizedConclusion.result.hint, rule: finalizedConclusion.result.rule });
                }
                proofSteps.push({
                    step,
                    kind: 'conclude',
                    claim,
                    rule: finalizedConclusion.result.rule,
                    valid: finalizedConclusion.result.valid,
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
                    registerLemmaImportClaim(ctx, `applied(${n.target})`, step, [], []);
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
                ctx.variables.push({ name: n.varName, type: n.varType, step });
                // Variables are always valid introductions
                if (n.varType) {
                    registerVariableClaim(ctx, `${n.varName}: ${n.varType}`, step);
                }
                proofSteps.push({
                    step,
                    kind: 'setVar',
                    claim: n.varType ? `${n.varName}: ${n.varType}` : n.varName,
                    rule: 'VARIABLE',
                    valid: true,
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
function registerClaim(ctx, input) {
    const proofObjectId = makeProofObjectId(input.step, input.source, input.content);
    const claim = {
        content: input.content,
        source: input.source,
        step: input.step,
        proofObjectId,
    };
    ctx.established.push(claim);
    ctx.proofObjects.push({
        id: proofObjectId,
        claim: input.content,
        rule: input.rule,
        source: input.source,
        step: input.step,
        dependsOn: uniqueProps(input.dependsOn),
        dependsOnIds: uniqueIds(input.dependsOnIds ?? resolveClaimIds(ctx, input.dependsOn)),
        imports: input.imports && input.imports.length > 0 ? uniqueProps(input.imports) : undefined,
    });
    if (input.emitDerivation !== false) {
        ctx.derivations.push(makeDerivationNode(input.step, input.rule, uniqueIds(input.dependsOnIds ?? resolveClaimIds(ctx, input.dependsOn)), proofObjectId));
    }
    return claim;
}
function registerAssumptionClaim(ctx, claim, step, rule) {
    return registerClaim(ctx, {
        content: claim,
        source: 'assumption',
        step,
        rule,
        dependsOn: [],
        emitDerivation: false,
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
    });
}
function registerDerivedClaim(ctx, input) {
    const builder = buildProofObjectInput(input.content, input.source, input.step, input.derivation, ctx);
    const graphValidation = validateProofObjectInput(builder);
    const result = graphValidation ?? input.derivation ?? {
        valid: true,
        rule: builder.rule,
        message: builder.rule === 'STRUCTURAL' ? 'Assertion accepted' : `${builder.rule} accepted`,
    };
    const claim = registerClaim(ctx, {
        ...builder,
        emitDerivation: Boolean(input.derivation?.valid) && !graphValidation,
    });
    return { claim, result };
}
function makeProofObjectId(step, source, claim) {
    return `${source}:${step}:${normalizeName(claim)}`;
}
function makeDerivationNode(step, rule, inputIds, outputId) {
    return {
        id: `derivation:${step}:${normalizeName(outputId)}`,
        step,
        rule,
        inputIds,
        outputId,
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
        case 'SUBSET_ELIM':
            return validateSubsetElimNode(node, inputs, output);
        case 'SUBSET_TRANS':
            return validateSubsetTransNode(node, inputs, output);
        case 'EQUALITY_SUBST':
            return validateEqualitySubstNode(node, inputs, output);
        case 'UNION_INTRO':
            return validateUnionIntroNode(node, inputs, output);
        case 'INTERSECTION_INTRO':
            return validateIntersectionIntroNode(node, inputs, output);
        case 'INTERSECTION_ELIM':
            return validateIntersectionElimNode(node, inputs, output);
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
function buildProofObjectInput(claim, source, step, derivation, ctx) {
    if (!derivation?.valid) {
        return {
            content: claim,
            source,
            step,
            rule: derivation?.rule ?? 'STRUCTURAL',
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
        case 'SUBSET_ELIM':
            return buildSubsetElimProofObject(claim, source, step, ctx);
        case 'SUBSET_TRANS':
            return buildSubsetTransProofObject(claim, source, step, ctx);
        case 'EQUALITY_SUBST':
            return buildEqualitySubstProofObject(claim, source, step, ctx);
        case 'UNION_INTRO':
            return buildUnionIntroProofObject(claim, source, step, ctx);
        case 'INTERSECTION_INTRO':
            return buildIntersectionIntroProofObject(claim, source, step, ctx);
        case 'INTERSECTION_ELIM':
            return buildIntersectionElimProofObject(claim, source, step, ctx);
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
        default:
            return {
                content: claim,
                source,
                step,
                rule: derivation.rule,
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
    const implication = ctx.goal ? parseImplicationProp(ctx.goal) : parseImplicationProp(claim);
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
    return {
        content: outputClaim,
        source,
        step,
        rule: 'FORALL_IN_INTRO',
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
    return {
        content: claim,
        source,
        step,
        rule: 'EXISTS_IN_ELIM',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildImpliesIntroProofObject(claim, source, step, ctx) {
    const dependency = findImplicationIntroDependency(claim, ctx);
    const outputClaim = implicationOutputClaim(claim, ctx);
    return {
        content: outputClaim,
        source,
        step,
        rule: 'IMPLIES_INTRO',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
    };
}
function buildContradictionDischargeProofObject(claim, source, step, ctx) {
    const dependency = findContradictionDependency(ctx);
    return {
        content: claim,
        source,
        step,
        rule: 'CONTRADICTION',
        dependsOn: dependency?.claims ?? [],
        dependsOnIds: dependency?.ids ?? [],
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
        };
    }
    return null;
}
function findImplicationIntroDependency(claim, ctx) {
    const implication = ctx.goal ? parseImplicationProp(ctx.goal) : parseImplicationProp(claim);
    if (!implication)
        return null;
    const antecedentObject = findLatestProofObjectByClaim(ctx, implication[0], object => object.source === 'assumption');
    const consequentObject = findLatestProofObjectByClaim(ctx, implication[1]);
    if (!antecedentObject || !consequentObject)
        return null;
    return {
        claims: [implication[0], implication[1]],
        ids: uniqueIds([antecedentObject.id, consequentObject.id]),
    };
}
function findContradictionDependency(ctx) {
    const contradiction = findContradictionProofObjects(ctx);
    if (!contradiction)
        return null;
    return {
        claims: [contradiction.a.claim, contradiction.b.claim],
        ids: uniqueIds([contradiction.a.id, contradiction.b.id]),
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
function resolveClaimIds(ctx, claims) {
    const resolved = [];
    for (const claim of claims) {
        const matches = ctx.established.filter(item => (0, propositions_1.sameProp)(item.content, claim) && item.proofObjectId);
        if (matches.length > 0) {
            resolved.push(matches[matches.length - 1].proofObjectId);
        }
    }
    return uniqueIds(resolved);
}
function findLatestProofObjectByClaim(ctx, claim, predicate) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const object = ctx.proofObjects[i];
        if ((0, propositions_1.sameProp)(object.claim, claim) && (!predicate || predicate(object))) {
            return object;
        }
    }
    return null;
}
function findLatestProofObject(ctx, predicate) {
    for (let i = ctx.proofObjects.length - 1; i >= 0; i--) {
        const object = ctx.proofObjects[i];
        if (predicate(object))
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
        case 'SUBSET_ELIM':
            return uniqueProps(dependsOn).length;
        case 'SUBSET_TRANS':
            return uniqueProps(dependsOn).length;
        case 'EQUALITY_SUBST':
            return uniqueProps(dependsOn).length;
        case 'UNION_INTRO':
            return uniqueProps(dependsOn).length;
        case 'INTERSECTION_INTRO':
            return uniqueProps(dependsOn).length;
        case 'INTERSECTION_ELIM':
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
            return expr.atomKind !== 'opaque' && isKernelCheckableAtom(expr.condition);
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
        return `This looks like quantified mathematics. Keep the MI-style notation if you want, but use 'fl verify' until bounded quantifier rules are part of the fast checker subset.`;
    }
    if (/[∈∉⊆⊂∪∩]/.test(value)) {
        return `This looks like set-theoretic notation. The fast checker currently verifies only a small kernel subset of membership, subset, equality-substitution, and union/intersection membership rules; otherwise use 'fl verify'.`;
    }
    if (/:\s*[\wℕℤℚℝ]/.test(value) || /→|⇒/.test(value)) {
        return `This looks like typed or function-style mathematical notation. Keep the MI-style syntax if you want, but use 'fl verify' outside the fast checker subset.`;
    }
    if (containsMathNotation(value)) {
        return `This looks like mathematical notation. Keep the MI-style syntax if you want, but use 'fl verify' for richer semantics outside the fast checker subset.`;
    }
    return `Rewrite the expression into the current fast checker subset or use 'fl verify'.`;
}
function checkDerivedClaim(claim, ctx) {
    if (ctx.established.some(item => (0, propositions_1.sameProp)(item.content, claim))) {
        return null;
    }
    for (const item of ctx.established) {
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
    for (const item of ctx.established) {
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
    const equalitySubst = checkEqualitySubstDerivedClaim(claim, ctx);
    if (equalitySubst?.valid)
        return equalitySubst;
    const unionIntro = checkUnionIntroDerivedClaim(claim, ctx);
    if (unionIntro?.valid)
        return unionIntro;
    const intersectionIntro = checkIntersectionIntroDerivedClaim(claim, ctx);
    if (intersectionIntro?.valid)
        return intersectionIntro;
    const intersectionElim = checkIntersectionElimDerivedClaim(claim, ctx);
    if (intersectionElim?.valid)
        return intersectionElim;
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
    for (const item of ctx.established) {
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
function checkSubsetTransDerivedClaim(claim, ctx) {
    const target = parseSubsetProp(claim);
    if (!target)
        return null;
    for (const item of ctx.established) {
        const left = parseSubsetProp(item.content);
        if (!left || !(0, propositions_1.sameProp)(left.left, target.left))
            continue;
        for (const next of ctx.established) {
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
function checkEqualitySubstDerivedClaim(claim, ctx) {
    const output = parseMembershipProp(claim);
    if (!output)
        return null;
    for (const equalityItem of ctx.established) {
        const equality = parseEqualityProp(equalityItem.content);
        if (!equality)
            continue;
        for (const membershipItem of ctx.established) {
            if (supportsEqualitySubstitution(equalityItem.content, membershipItem.content, claim)) {
                const result = (0, rules_1.checkEqualitySubst)(equalityItem.content, membershipItem.content, claim, ctx);
                if (result.valid)
                    return result;
            }
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
    for (const item of ctx.established) {
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
function checkForallInElimDerivedClaim(claim, ctx) {
    for (const quantifiedItem of ctx.established) {
        const quantifier = parseBoundedQuantifierProp(quantifiedItem.content, 'forall');
        if (!quantifier)
            continue;
        for (const membershipItem of ctx.established) {
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
    for (const membershipItem of ctx.established) {
        const witness = parseMembershipProp(membershipItem.content);
        if (!witness || !(0, propositions_1.sameProp)(witness.set, quantifier.set))
            continue;
        const instantiated = instantiateBoundedQuantifier(quantifier, witness.element);
        if (!instantiated)
            continue;
        if (ctx.established.some(item => (0, propositions_1.sameProp)(item.content, instantiated))) {
            const result = (0, rules_1.checkExistsInIntro)(membershipItem.content, instantiated, claim, ctx);
            if (result.valid)
                return result;
        }
    }
    return null;
}
function checkExistsInElimDerivedClaim(claim, ctx) {
    for (const existentialItem of ctx.established) {
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
    const antecedentAssumed = ctx.established.some(item => item.source === 'assumption' && (0, propositions_1.sameProp)(item.content, antecedent));
    const consequentEstablished = ctx.established.some(item => (0, propositions_1.sameProp)(item.content, consequent));
    return (0, rules_1.checkImpliesIntro)(antecedent, consequent, antecedentAssumed, consequentEstablished);
}
function checkForallGoalDischarge(claim, ctx) {
    if (!ctx.goal)
        return null;
    const quantifier = parseBoundedQuantifierProp(ctx.goal, 'forall');
    if (!quantifier)
        return null;
    const scope = findForallInIntroScope(quantifier, ctx);
    if (!scope)
        return null;
    if (!(0, propositions_1.sameProp)(scope.body.claim, claim))
        return null;
    return (0, rules_1.checkForallInIntro)(scope.membership.claim, scope.body.claim, ctx.goal, ctx);
}
function checkContradictionDischarge(claim, ctx) {
    const contradictionEstablished = ctx.established.some(item => (0, propositions_1.sameProp)(item.content, 'contradiction'));
    if (!contradictionEstablished)
        return null;
    const contradiction = (0, rules_1.checkContradiction)(ctx);
    if (!contradiction.valid)
        return contradiction;
    return {
        valid: true,
        rule: 'CONTRADICTION',
        message: `Contradiction discharges the current goal: ${claim}`,
    };
}
function checkPremiseClaim(claim, ctx) {
    if (!ctx.goal)
        return null;
    if (!(0, propositions_1.sameProp)(claim, ctx.goal) && !ctx.established.some(item => item.source === 'premise' && (0, propositions_1.sameProp)(item.content, claim))) {
        return null;
    }
    return {
        valid: true,
        rule: 'PREMISE',
        message: `Premise available in context: ${claim}`,
    };
}
function parseImplicationProp(prop) {
    const parts = splitTopLevel(prop, '→');
    if (!parts)
        return null;
    return parts;
}
function parseConjunctionProp(prop) {
    const parts = splitTopLevel(prop, '∧');
    if (!parts)
        return null;
    return parts;
}
function parseSubsetProp(prop) {
    const match = stripParens(prop).match(/^(.+?)\s*(⊆|⊂)\s*(.+)$/);
    if (!match)
        return null;
    return { left: stripParens(match[1].trim()), right: stripParens(match[3].trim()) };
}
function parseEqualityProp(prop) {
    if (/==/.test(prop))
        return null;
    const match = stripParens(prop).match(/^(.+?)\s*=\s*(.+)$/);
    if (!match)
        return null;
    return { left: stripParens(match[1].trim()), right: stripParens(match[2].trim()) };
}
function parseMembershipProp(prop) {
    const value = stripParens(prop);
    if (value.startsWith('∀') || value.startsWith('∃'))
        return null;
    const match = value.match(/^(.+?)\s*(∈|∉)\s*(.+)$/);
    if (!match)
        return null;
    return { element: stripParens(match[1].trim()), set: stripParens(match[3].trim()) };
}
function parseBinarySetProp(prop, operator) {
    return splitTopLevel(stripParens(prop), operator);
}
function parseBoundedQuantifierProp(prop, kind) {
    const value = stripParens(prop);
    const symbol = kind === 'forall' ? '∀' : '∃';
    const match = value.match(new RegExp(`^${symbol}\\s*([A-Za-z_][\\w₀-₉ₐ-ₙ]*)\\s*∈\\s*(.+?)\\s*,\\s*(.+)$`));
    if (match) {
        return {
            kind,
            variable: match[1].trim(),
            set: stripParens(match[2].trim()),
            body: stripParens(match[3].trim()),
        };
    }
    const parenMatch = value.match(new RegExp(`^${symbol}\\s*\\(\\s*([A-Za-z_][\\w₀-₉ₐ-ₙ]*)\\s*∈\\s*([^)]+)\\)\\s*,\\s*(.+)$`));
    if (parenMatch) {
        return {
            kind,
            variable: parenMatch[1].trim(),
            set: stripParens(parenMatch[2].trim()),
            body: stripParens(parenMatch[3].trim()),
        };
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
            return { witness, membership, body };
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
            return { witness, membership, body };
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
function escapeRegExp(value) {
    return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}
function isKernelCheckableAtom(value) {
    return kernelSubsetGap(value) === null;
}
function kernelSubsetDiagnostic(expr, label, step) {
    if (expr.type !== 'Atom' || expr.atomKind === 'opaque')
        return null;
    const gap = kernelSubsetGap(expr.condition);
    if (!gap)
        return null;
    return {
        severity: 'info',
        message: `${label} needs kernel rule ${gap.rule}, which the fast checker does not implement yet.`,
        step,
        rule: 'STRUCTURAL',
        hint: `Use 'fl verify' for semantic verification. ${gap.hint}`,
    };
}
function kernelSubsetGap(value) {
    const forall = parseBoundedQuantifierProp(value, 'forall');
    if (forall) {
        return null;
    }
    const exists = parseBoundedQuantifierProp(value, 'exists');
    if (exists) {
        return null;
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
    if (parseEqualityProp(value)) {
        return {
            rule: 'EQUALITY_REASONING',
            hint: 'Direct equality claims can appear in source, but only membership substitution from an established equality is kernel-checked today.',
        };
    }
    if (/[∪∩]/.test(value)) {
        return {
            rule: 'SET_OPERATOR_REASONING',
            hint: 'Only membership introduction/elimination over unions and intersections is kernel-checked today.',
        };
    }
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
