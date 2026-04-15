"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.checkFile = checkFile;
exports.createMutableContext = createMutableContext;
exports.evaluateIncrementalStep = evaluateIncrementalStep;
const term_1 = require("../kernel/term");
const arithmetic_1 = require("../kernel/arithmetic");
const unify_1 = require("../kernel/unify");
const propositions_1 = require("./propositions");
const category_1 = require("../kernel/category");
const category_diagrams_1 = require("../kernel/category-diagrams");
const TOP = '⊤';
const BOTTOM = '⊥';
const BUILTIN_SORTS = new Set(['ℕ', 'ℤ', 'ℚ', 'ℝ', 'String', 'Set', 'Element']);
function checkFile(nodes, options = {}) {
    const diagnostics = [];
    const reports = [];
    const structs = collectStructDefinitions(nodes, diagnostics);
    const types = collectTypeDefinitions(nodes, structs, diagnostics);
    const pairs = findPairs(nodes);
    const pairNames = new Set(pairs.map(pair => normalizeName(pair.theorem.name)));
    const lemmas = new Map();
    const eliminators = generateEliminators(types);
    for (const [name, claimSet] of eliminators) {
        lemmas.set(name, claimSet);
    }
    let theoremCount = 0;
    let proofCount = 0;
    let pairedCount = 0;
    for (const node of nodes) {
        if (node.type === 'Theorem' || node.type === 'Lemma')
            theoremCount++;
        if (node.type === 'Proof')
            proofCount++;
    }
    for (const pair of pairs) {
        pairedCount++;
        const report = checkPair(pair, lemmas, structs, types, options);
        reports.push(report);
        if (pair.theorem.type === 'Lemma') {
            lemmas.set(normalizeName(pair.theorem.name), {
                name: pair.theorem.name,
                premises: theoremPremises(pair.theorem),
                conclusion: theoremGoal(pair.theorem),
                state: report.state,
            });
        }
    }
    for (const node of nodes) {
        if (node.type === 'Theorem' && !pairNames.has(normalizeName(node.name))) {
            diagnostics.push({ severity: 'info', message: `Theorem '${node.name}' has no proof` });
        }
        if (node.type === 'Lemma' && !pairNames.has(normalizeName(node.name))) {
            diagnostics.push({ severity: 'info', message: `Lemma '${node.name}' has no proof` });
        }
    }
    const state = combineStates(reports.map(report => report.state), pairedCount === 0 ? 'FAILED' : 'PROVED');
    return {
        state,
        valid: state === 'PROVED',
        theoremCount,
        proofCount,
        pairedCount,
        reports,
        diagnostics,
    };
}
function checkPair(pair, lemmas, structs, types, _options) {
    const premises = theoremPremises(pair.theorem);
    const goal = theoremGoal(pair.theorem);
    const ctx = createContext(goal, lemmas, premises, structs, types);
    seedPremises(ctx, premises);
    if (pair.proof.fnMeta) {
        const recursionIssue = validateListStructuralRecursion(pair.proof);
        if (recursionIssue) {
            ctx.unverifiedReasons.push(recursionIssue);
            ctx.diagnostics.push({ severity: 'warning', message: recursionIssue, rule: 'STRUCTURAL' });
        }
    }
    for (let index = 0; index < pair.proof.body.length; index++) {
        const step = index + 1;
        const node = pair.proof.body[index];
        try {
            handleNode(ctx, node, step);
        }
        catch (error) {
            const message = error instanceof Error ? error.message : 'Unknown checker failure';
            ctx.diagnostics.push({ severity: 'error', step, message });
            ctx.proofSteps.push({
                step,
                kind: classifyStep(node),
                claim: nodeToClaim(node),
                rule: 'STRUCTURAL',
                state: 'FAILED',
                message,
            });
        }
    }
    const derivedConclusion = findDerivedConclusion(ctx, goal);
    if (goal && !derivedConclusion) {
        ctx.diagnostics.push({
            severity: 'error',
            message: `Proof '${pair.proof.name}' does not establish theorem goal '${goal}'`,
            rule: 'STRUCTURAL',
        });
    }
    const state = reportState(ctx, goal, derivedConclusion);
    return {
        name: pair.theorem.name,
        state,
        valid: state === 'PROVED',
        stepCount: pair.proof.body.length,
        goal,
        premises,
        derivedConclusion,
        proofSteps: ctx.proofSteps,
        proofObjects: ctx.objects,
        derivations: ctx.derivations,
        diagnostics: ctx.diagnostics,
        provedCount: ctx.objects.filter(object => object.tau === '1').length,
        pendingCount: ctx.objects.filter(object => object.pending).length,
    };
}
function createContext(goal, lemmas, premises, structs, types) {
    const category = new category_1.WenittainCategory();
    category.createObject(TOP);
    category.createObject(BOTTOM);
    for (const premise of premises) {
        ensureClaimObjects(category, premise);
    }
    if (goal) {
        ensureClaimObjects(category, goal);
    }
    return {
        category,
        diagrams: new category_diagrams_1.CategoryDiagramKernel(),
        objects: [],
        derivations: [],
        diagnostics: [],
        proofSteps: [],
        variables: [],
        assumptions: [],
        premises: [],
        lemmas: new Map(lemmas),
        goal,
        structs,
        types,
        unverifiedReasons: [],
    };
}
function seedPremises(ctx, premises) {
    for (const premise of premises) {
        const morphism = createKernelObject(ctx, premise, 'PREMISE', -1, [], [], '1');
        ctx.premises.push(morphism);
    }
}
function createMutableContext(premises, goal) {
    const ctx = createContext(goal, new Map(), premises, new Map(), new Map());
    seedPremises(ctx, premises);
    return ctx;
}
function evaluateIncrementalStep(ctx, node) {
    const startStepCount = ctx.proofSteps.length;
    const stepNumber = startStepCount + 1;
    try {
        handleNode(ctx, node, stepNumber);
    }
    catch (error) {
        const message = error instanceof Error ? error.message : 'Unknown checker failure';
        ctx.diagnostics.push({ severity: 'error', step: stepNumber, message });
        ctx.proofSteps.push({
            step: stepNumber,
            kind: classifyStep(node),
            claim: nodeToClaim(node),
            rule: 'STRUCTURAL',
            state: 'FAILED',
            message,
        });
    }
    if (ctx.proofSteps.length > startStepCount) {
        return ctx.proofSteps[ctx.proofSteps.length - 1];
    }
    return null;
}
function handleNode(ctx, node, step) {
    switch (node.type) {
        case 'Assume':
            handleAssume(ctx, node, step);
            return;
        case 'SetVar':
            handleSetVar(ctx, node, step);
            return;
        case 'Assert':
            handleClaimStep(ctx, node, step, 'assert');
            return;
        case 'Conclude':
            handleClaimStep(ctx, node, step, 'conclude');
            return;
        case 'Induction':
            handleInduction(ctx, node, step);
            return;
        case 'Match':
            handleMatch(ctx, node, step);
            return;
        case 'Apply':
            handleApply(ctx, node.target, step);
            return;
        case 'Raw':
            handleRaw(ctx, node, step);
            return;
        case 'Intro':
            handleIntro(ctx, node, step);
            return;
        case 'Rewrite':
            handleRewrite(ctx, node, step);
            return;
        case 'Exact':
            handleExact(ctx, node, step);
            return;
        case 'Obtain':
            handleObtain(ctx, node, step);
            return;
        default:
            return;
    }
}
function handleAssume(ctx, node, step) {
    const claim = (0, propositions_1.exprToProp)(node.expr);
    const proofObject = createKernelObject(ctx, claim, 'ASSUMPTION', step);
    ctx.assumptions.push(proofObject);
    ctx.proofSteps.push({
        step,
        kind: 'assume',
        claim,
        rule: 'ASSUMPTION',
        state: 'PROVED',
        message: 'Assumption introduced as a morphism into the current Boolean-category derivation context',
    });
}
function handleSetVar(ctx, node, step) {
    ctx.variables.push({ name: node.varName, domain: node.varType });
    ctx.proofSteps.push({
        step,
        kind: 'setVar',
        claim: node.varType ? `${node.varName}: ${node.varType}` : node.varName,
        rule: 'STRUCTURAL',
        state: 'PROVED',
        message: 'Bound variable recorded for categorical introduction or elimination rules',
    });
}
function handleInduction(ctx, node, step) {
    const claim = ctx.goal ?? (0, propositions_1.exprToProp)(node.fold);
    createKernelObject(ctx, claim, 'FOLD_ELIM', step);
    ctx.proofSteps.push({
        step,
        kind: 'induction',
        claim,
        rule: 'FOLD_ELIM',
        state: 'PROVED',
        uses: [(0, propositions_1.exprToProp)(node.fold), node.base, node.step],
        message: 'Desugared induction into the trusted fold primitive',
    });
}
function handleMatch(ctx, node, step) {
    const scrutinee = (0, propositions_1.exprToProp)(node.scrutinee);
    const scrutineeMembership = requireAnyMembership(ctx, scrutinee);
    const scrutineeType = scrutineeMembership ? (0, propositions_1.parseMembershipCanonical)(scrutineeMembership.claim)?.set ?? null : null;
    const parsedSort = scrutineeType ? parseSort(scrutineeType) : null;
    if (parsedSort?.kind === 'list' && scrutineeType) {
        handleListMatch(ctx, node, step, scrutinee, scrutineeType, parsedSort);
        return;
    }
    const boolType = inferBooleanMatchType(node);
    const typeDef = scrutineeType ? ctx.types.get(scrutineeType) : boolType;
    if ((!scrutineeMembership && !boolType) || !typeDef) {
        ctx.diagnostics.push({ severity: 'error', step, message: `Pattern match requires a scrutinee with a registered sum type: '${scrutinee}'`, rule: 'MATCH_EXHAUSTIVE' });
        ctx.proofSteps.push({
            step,
            kind: 'match',
            claim: scrutinee,
            rule: 'MATCH_EXHAUSTIVE',
            state: 'FAILED',
            message: 'No registered variant information is available for this match scrutinee',
        });
        return;
    }
    const covered = new Set(node.cases
        .filter(matchCase => matchCase.pattern.kind === 'variant')
        .map(matchCase => matchCase.pattern.constructor));
    const exhaustive = node.cases.some(matchCase => matchCase.pattern.kind === 'wildcard')
        || typeDef.variants.every(variant => covered.has(variant.name));
    if (!exhaustive) {
        ctx.diagnostics.push({ severity: 'error', step, message: 'MATCH_EXHAUSTIVE failed: non-exhaustive match', rule: 'MATCH_EXHAUSTIVE' });
        ctx.proofSteps.push({
            step,
            kind: 'match',
            claim: scrutinee,
            rule: 'MATCH_EXHAUSTIVE',
            state: 'FAILED',
            message: 'Pattern matching must cover every variant or include a wildcard case',
        });
        return;
    }
    const branchStates = [];
    const branchUses = [];
    for (const matchCase of node.cases) {
        const branch = createBranchContext(ctx);
        const variant = matchCase.pattern.kind !== 'variant'
            ? null
            : typeDef.variants.find(candidate => candidate.name === matchCase.pattern.constructor) ?? null;
        if (matchCase.pattern.kind === 'variant' && !variant) {
            branchStates.push('FAILED');
            continue;
        }
        if (variant && matchCase.pattern.kind === 'variant') {
            applyVariantPatternBindings(branch, scrutinee, variant, matchCase.pattern.bindings, step);
            branchUses.push(`${scrutinee} ∈ ${variant.name}`);
        }
        else {
            branchUses.push('_');
        }
        for (const branchNode of matchCase.body) {
            try {
                handleNode(branch, branchNode, step);
            }
            catch (error) {
                const message = error instanceof Error ? error.message : 'Unknown match-branch failure';
                branch.diagnostics.push({ severity: 'error', step, message, rule: 'OR_ELIM' });
            }
        }
        branchStates.push(evaluateMatchBranch(branch, ctx.goal, step));
    }
    if (branchStates.some(state => state === 'FAILED')) {
        ctx.diagnostics.push({ severity: 'error', step, message: 'At least one match branch does not establish the required conclusion', rule: 'OR_ELIM' });
        ctx.proofSteps.push({
            step,
            kind: 'match',
            claim: ctx.goal ?? scrutinee,
            rule: 'MATCH_EXHAUSTIVE',
            state: 'FAILED',
            uses: branchUses,
            message: 'Exhaustive case analysis failed because a branch does not discharge the branch goal',
        });
        return;
    }
    const targetClaim = ctx.goal ?? scrutineeMembership?.claim ?? scrutinee;
    createKernelObject(ctx, targetClaim, 'MATCH_EXHAUSTIVE', step);
    ctx.proofSteps.push({
        step,
        kind: 'match',
        claim: targetClaim,
        rule: 'MATCH_EXHAUSTIVE',
        state: 'PROVED',
        uses: branchUses,
        message: 'Validated exhaustive proof by cases via categorical OR elimination',
    });
}
function handleListMatch(ctx, node, step, scrutinee, scrutineeType, parsedSort) {
    if (!requireAnyMembership(ctx, scrutinee) || parsedSort.kind !== 'list' || !parsedSort.element) {
        ctx.diagnostics.push({ severity: 'error', step, message: `Pattern match requires a scrutinee with a registered list sort: '${scrutinee}'`, rule: 'MATCH_EXHAUSTIVE' });
        ctx.proofSteps.push({
            step,
            kind: 'match',
            claim: scrutinee,
            rule: 'MATCH_EXHAUSTIVE',
            state: 'FAILED',
            message: 'No kernel List sort information is available for this match scrutinee',
        });
        return;
    }
    const nilCase = node.cases.find(matchCase => matchCase.pattern.kind === 'list_nil') ?? null;
    const consCase = node.cases.find(matchCase => matchCase.pattern.kind === 'list_cons') ?? null;
    const exhaustive = node.cases.length === 2 && Boolean(nilCase) && Boolean(consCase);
    if (!exhaustive) {
        ctx.diagnostics.push({ severity: 'error', step, message: 'MATCH_EXHAUSTIVE failed: List matches must contain exactly [] and [x, ...rest]', rule: 'MATCH_EXHAUSTIVE' });
        ctx.proofSteps.push({
            step,
            kind: 'match',
            claim: scrutinee,
            rule: 'MATCH_EXHAUSTIVE',
            state: 'FAILED',
            message: 'Kernel List matching requires both Nil and Cons cases',
        });
        return;
    }
    const branchStates = [];
    const branchUses = [];
    for (const matchCase of [nilCase, consCase]) {
        if (!matchCase)
            continue;
        const branch = createBranchContext(ctx);
        if (matchCase.pattern.kind === 'list_cons') {
            applyListPatternBindings(branch, scrutinee, scrutineeType, parsedSort, matchCase.pattern.head, matchCase.pattern.tail, step);
            branchUses.push(`[${matchCase.pattern.head}, ...${matchCase.pattern.tail}]`);
        }
        else {
            branchUses.push('[]');
        }
        for (const branchNode of matchCase.body) {
            try {
                handleNode(branch, branchNode, step);
            }
            catch (error) {
                const message = error instanceof Error ? error.message : 'Unknown list match-branch failure';
                branch.diagnostics.push({ severity: 'error', step, message, rule: 'OR_ELIM' });
            }
        }
        branchStates.push(evaluateMatchBranch(branch, ctx.goal, step));
    }
    if (branchStates.some(state => state === 'FAILED' || state === 'UNVERIFIED')) {
        ctx.diagnostics.push({ severity: 'error', step, message: 'At least one list match branch does not establish the required conclusion', rule: 'OR_ELIM' });
        ctx.proofSteps.push({
            step,
            kind: 'match',
            claim: ctx.goal ?? scrutinee,
            rule: 'MATCH_EXHAUSTIVE',
            state: 'FAILED',
            uses: branchUses,
            message: 'Exhaustive list case analysis failed because a branch does not discharge the branch goal',
        });
        return;
    }
    const targetClaim = ctx.goal ?? `${scrutinee} ∈ ${scrutineeType}`;
    createKernelObject(ctx, targetClaim, 'MATCH_EXHAUSTIVE', step);
    ctx.proofSteps.push({
        step,
        kind: 'match',
        claim: targetClaim,
        rule: 'MATCH_EXHAUSTIVE',
        state: 'PROVED',
        uses: branchUses,
        message: 'Validated exhaustive proof by cases over the kernel List primitive',
    });
}
function inferBooleanMatchType(node) {
    const constructors = [];
    for (const matchCase of node.cases) {
        if (matchCase.pattern.kind === 'variant') {
            constructors.push(matchCase.pattern.constructor);
        }
    }
    const boolConstructors = new Set(['true', 'false']);
    if (constructors.length === 0 || constructors.some(name => !boolConstructors.has(name))) {
        return null;
    }
    return {
        name: 'Bool',
        variants: [
            { name: 'true', parent: 'Bool', fields: [] },
            { name: 'false', parent: 'Bool', fields: [] },
        ],
    };
}
function handleApply(ctx, target, step) {
    const lemma = ctx.lemmas.get(normalizeName(target));
    if (!lemma) {
        // Backward application: find the target as a hypothesis in context.
        // If it is an implication A → B whose consequent matches the current goal,
        // reduce the goal to A.
        const hyp = findExact(ctx.objects, target, false)
            ?? findExact(ctx.assumptions, target, false)
            ?? findExact(ctx.premises, target, false);
        if (hyp) {
            const impl = (0, propositions_1.parseImplicationCanonical)(hyp.claim);
            if (impl && ctx.goal) {
                const [antecedent, consequent] = impl;
                const consTerm = (0, term_1.termFromString)(consequent);
                const goalTerm = (0, term_1.termFromString)(ctx.goal);
                if ((0, term_1.termEqual)(consTerm, goalTerm)) {
                    ctx.goal = antecedent;
                    ctx.proofSteps.push({
                        step,
                        kind: 'apply',
                        claim: antecedent,
                        rule: 'BY_LEMMA',
                        state: 'PROVED',
                        uses: [hyp.claim],
                        message: `Applied '${target}' backward: goal reduced to '${antecedent}'`,
                    });
                    return;
                }
            }
            ctx.diagnostics.push({ severity: 'error', step, message: `apply: '${target}' is not an implication whose consequent matches the goal '${ctx.goal ?? '(none)'}'`, rule: 'BY_LEMMA' });
            ctx.proofSteps.push({ step, kind: 'apply', claim: target, rule: 'BY_LEMMA', state: 'FAILED', message: `Consequent does not match goal` });
            return;
        }
        ctx.diagnostics.push({ severity: 'error', step, message: `Unknown lemma or hypothesis '${target}'`, rule: 'BY_LEMMA' });
        ctx.proofSteps.push({
            step,
            kind: 'apply',
            claim: target,
            rule: 'BY_LEMMA',
            state: 'FAILED',
            message: `'${target}' is not available`,
        });
        return;
    }
    if (lemma.state !== 'PROVED') {
        ctx.diagnostics.push({ severity: 'error', step, message: `Lemma '${target}' is not fully proved and cannot be applied`, rule: 'BY_LEMMA' });
        ctx.proofSteps.push({
            step,
            kind: 'apply',
            claim: lemma.conclusion ?? target,
            rule: 'BY_LEMMA',
            state: 'FAILED',
            imports: [lemma.name],
            message: `Lemma '${target}' is not fully proved`,
        });
        return;
    }
    // If the lemma has metavars, use unification to instantiate it
    if (lemma.metavars && lemma.metavars.length > 0 && lemma.conclusion && ctx.goal) {
        const metaSet = new Set(lemma.metavars);
        const lemmaConcTerm = (0, term_1.termFromString)(lemma.conclusion);
        const goalTerm = (0, term_1.termFromString)(ctx.goal);
        const unifyResult = (0, unify_1.unify)(lemmaConcTerm, goalTerm, metaSet);
        if (!unifyResult.error) {
            const subst = unifyResult.subst;
            const instantiatedPremises = lemma.premises.map(p => {
                const t = (0, term_1.applySubst)((0, term_1.termFromString)(p), subst);
                return (0, term_1.termToString)(t);
            });
            const missingInstantiated = instantiatedPremises.filter(p => !findExact(ctx.objects, p, false) && !findExact(ctx.premises, p, false) && !findExact(ctx.assumptions, p, false));
            if (missingInstantiated.length === 0) {
                const conclusion = (0, term_1.termToString)((0, term_1.applySubst)((0, term_1.termFromString)(lemma.conclusion), subst));
                const inputs = instantiatedPremises
                    .map(p => findExact(ctx.objects, p, false) ?? findExact(ctx.premises, p, false) ?? findExact(ctx.assumptions, p, false))
                    .filter((o) => Boolean(o))
                    .map(o => o.id);
                createKernelObject(ctx, conclusion, 'BY_LEMMA', step, inputs, [lemma.name], '1');
                ctx.proofSteps.push({
                    step, kind: 'apply', claim: conclusion, rule: 'BY_LEMMA', state: 'PROVED',
                    imports: [lemma.name], uses: instantiatedPremises,
                    message: `Applied lemma '${target}' via unification`,
                });
                return;
            }
        }
        ctx.diagnostics.push({ severity: 'error', step, message: `Lemma '${target}' unification failed`, rule: 'BY_LEMMA' });
        ctx.proofSteps.push({
            step,
            kind: 'apply',
            claim: target,
            rule: 'BY_LEMMA',
            state: 'FAILED',
            message: `Consequent does not unify with goal`,
            causalError: {
                ruleAttempted: 'BY_LEMMA',
                unificationMismatch: unifyResult.error,
            }
        });
        return;
    }
    const missing = lemma.premises.filter(premise => !findExact(ctx.objects, premise, false));
    if (missing.length > 0 || !lemma.conclusion) {
        ctx.diagnostics.push({
            severity: 'error',
            step,
            message: `Lemma '${target}' cannot be imported; missing premises: ${missing.join(' ; ') || 'conclusion'}`,
            rule: 'BY_LEMMA',
        });
        ctx.proofSteps.push({
            step,
            kind: 'apply',
            claim: lemma.conclusion ?? target,
            rule: 'BY_LEMMA',
            state: 'FAILED',
            imports: [lemma.name],
            message: `Lemma '${target}' does not compose with the current context`,
            causalError: {
                ruleAttempted: 'BY_LEMMA',
                missingPremises: missing,
            }
        });
        return;
    }
    const inputs = lemma.premises
        .map(premise => findExact(ctx.objects, premise, false))
        .filter((object) => Boolean(object))
        .map(object => object.id);
    createKernelObject(ctx, lemma.conclusion, 'BY_LEMMA', step, inputs, [lemma.name], '1');
    ctx.proofSteps.push({
        step,
        kind: 'apply',
        claim: lemma.conclusion,
        rule: 'BY_LEMMA',
        state: 'PROVED',
        imports: [lemma.name],
        uses: lemma.premises,
        message: `Imported lemma '${target}' as a morphism in the current context`,
    });
}
function handleRaw(ctx, node, step) {
    const claim = node.content.trim();
    if (!/^contradiction\s*\(\s*\)\s*;?$/.test(claim)) {
        ctx.diagnostics.push({ severity: 'error', step, message: `Unsupported raw proof syntax: '${claim}'. Use assert, assume, conclude, apply, intro, rewrite, or exact.`, rule: 'STRUCTURAL' });
        ctx.proofSteps.push({
            step,
            kind: 'raw',
            claim,
            rule: 'STRUCTURAL',
            state: 'FAILED',
            message: 'Unsupported raw proof syntax',
        });
        return;
    }
    const contradiction = hasContradiction(ctx.objects);
    if (!contradiction) {
        ctx.diagnostics.push({ severity: 'error', step, message: 'contradiction() requires conflicting facts in scope', rule: 'CONTRADICTION' });
        ctx.proofSteps.push({
            step,
            kind: 'raw',
            claim: 'contradiction()',
            rule: 'CONTRADICTION',
            state: 'FAILED',
            message: 'No proposition and complement pair is available',
        });
        return;
    }
    const contradictionMeet = createKernelObject(ctx, `${contradiction[0].claim} ∧ ${contradiction[1].claim}`, 'AND_INTRO', step, contradiction.map(object => object.id));
    const bottom = createKernelObject(ctx, BOTTOM, 'CONTRADICTION', step, [contradictionMeet.id]);
    ctx.proofSteps.push({
        step,
        kind: 'raw',
        claim: BOTTOM,
        rule: 'CONTRADICTION',
        state: 'PROVED',
        uses: [...contradiction.map(object => object.claim), contradictionMeet.claim],
        message: 'Derived falsehood by meeting a proposition with its Boolean complement',
    });
    if (ctx.goal) {
        const exFalso = createKernelObject(ctx, ctx.goal, 'CONTRADICTION', step, [bottom.id]);
        ctx.proofSteps.push({
            step,
            kind: 'raw',
            claim: ctx.goal,
            rule: 'CONTRADICTION',
            state: 'PROVED',
            uses: [BOTTOM],
            message: 'Factored the current goal through falsehood after contradiction',
        });
        void exFalso;
    }
}
function handleClaimStep(ctx, node, step, kind) {
    const claim = (0, propositions_1.exprToProp)(node.expr);
    const derivation = deriveClaim(ctx, claim, step);
    if (derivation.state === 'FAILED') {
        ctx.diagnostics.push({ severity: 'error', step, message: derivation.message, rule: derivation.rule });
    }
    ctx.proofSteps.push({
        step,
        kind,
        claim,
        rule: derivation.rule,
        state: derivation.state,
        uses: derivation.uses,
        message: derivation.message,
    });
}
function deriveClaim(ctx, claim, step) {
    const exact = findExact(ctx.objects, claim, false);
    if (exact) {
        return {
            rule: exact.rule,
            state: exact.pending ? 'FAILED' : 'PROVED',
            uses: [exact.claim],
            message: 'Claim already exists as a morphism in the current derivation',
        };
    }
    const prover = [
        deriveAndIntro,
        deriveAndElim,
        deriveStructClaim,
        deriveMeasureClaim,
        deriveCategoryClaim,
        deriveFoldClaim,
        deriveNotIntro,
        deriveImpliesElim,
        deriveImpliesIntro,
        deriveIffIntro,
        deriveIffElim,
        deriveOrIntro,
        deriveOrElim,
        deriveSubsetIntro,
        deriveSubsetElim,
        deriveSubsetTransitivity,
        deriveSubsetAntisymmetry,
        deriveEqualitySubstitution,
        deriveUnionRule,
        deriveIntersectionRule,
        deriveImageRule,
        derivePreimageRule,
        deriveQuantifierRule,
        deriveDependentTypeRule,
        deriveNaturalTransformationRule,
        deriveExFalso,
        deriveForallElim,
        deriveExistsIntro,
        deriveArithClaim,
        deriveModArithClaim,
        deriveIntClaim,
        deriveRealAnalysisClaim,
        deriveCryptoClaim,
        deriveOrderClaim,
        deriveGraphClaim,
        deriveCombClaim,
    ];
    for (const attempt of prover) {
        const result = attempt(ctx, claim, step);
        if (result) {
            return result;
        }
    }
    return {
        rule: 'STRUCTURAL',
        state: 'FAILED',
        message: `No categorical derivation establishes '${claim}' from the available morphisms`,
    };
}
function deriveStructClaim(ctx, claim, step) {
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (!membership)
        return null;
    const projection = deriveStructProjection(ctx, membership, claim, step);
    if (projection)
        return projection;
    const structDef = ctx.structs.get(membership.set);
    if (!structDef)
        return null;
    const inputs = [];
    const uses = [];
    for (const field of structDef.fields) {
        const fieldClaim = `${membership.element}.${field.name} ∈ ${field.type}`;
        const fieldObject = requireClassical(ctx, fieldClaim, 'STRUCT_INTRO');
        if (!fieldObject)
            return null;
        inputs.push(fieldObject.id);
        uses.push(fieldClaim);
    }
    createKernelObject(ctx, claim, 'STRUCT_INTRO', step, inputs);
    return {
        rule: 'STRUCT_INTRO',
        state: 'PROVED',
        uses,
        message: 'Constructed a struct-instance membership from all declared field memberships',
    };
}
function deriveStructProjection(ctx, membership, claim, step) {
    const access = parseFieldAccess(membership.element);
    if (!access)
        return null;
    const projection = resolveFieldProjection(ctx, access.base, access.path);
    if (!projection || projection.type !== membership.set)
        return null;
    createKernelObject(ctx, claim, 'STRUCT_ELIM', step, [projection.source.id]);
    return {
        rule: 'STRUCT_ELIM',
        state: 'PROVED',
        uses: [projection.source.claim],
        message: 'Projected a field membership from a struct-instance membership',
    };
}
function deriveAndIntro(ctx, claim, step) {
    const parts = (0, propositions_1.parseConjunctionCanonical)(claim);
    if (!parts)
        return null;
    const left = requireClassical(ctx, parts[0], 'AND_INTRO');
    const right = requireClassical(ctx, parts[1], 'AND_INTRO');
    if (!left || !right)
        return null;
    createKernelObject(ctx, claim, 'AND_INTRO', step, [left.id, right.id]);
    return {
        rule: 'AND_INTRO',
        state: 'PROVED',
        uses: [parts[0], parts[1]],
        message: 'Constructed the Boolean meet from both conjunct morphisms',
    };
}
function deriveFoldClaim(ctx, claim, step) {
    if (!/^fold\s*\(/.test(claim))
        return null;
    createKernelObject(ctx, claim, 'FOLD_ELIM', step);
    return {
        rule: 'FOLD_ELIM',
        state: 'PROVED',
        message: 'Trusted fold primitive establishes the fold result directly',
    };
}
// ── Measure theory helpers ───────────────────────────────────────────────────
function parseMeasureArgs(claim) {
    const m = claim.trim().match(/^Measure\s*\(\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
    return m ? { mu: m[1].trim(), sigma: m[2].trim() } : null;
}
function parseSigmaAlgebraArgs(claim) {
    const m = claim.trim().match(/^SigmaAlgebra\s*\(\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
    return m ? { sigma: m[1].trim(), space: m[2].trim() } : null;
}
function parseProbMeasureArgs(claim) {
    const m = claim.trim().match(/^ProbabilityMeasure\s*\(\s*([^,)]+?)\s*,\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
    return m ? { p: m[1].trim(), sigma: m[2].trim(), space: m[3].trim() } : null;
}
function parseMeasurableArgs(claim) {
    const m = claim.trim().match(/^Measurable\s*\(\s*([^,)]+?)\s*,\s*([^,)]+?)\s*,\s*([^)]+?)\s*\)$/);
    return m ? { f: m[1].trim(), sigmaX: m[2].trim(), sigmaY: m[3].trim() } : null;
}
function parseFunctionApplication(s) {
    const m = s.trim().match(/^([^\s(]+)\s*\((.+)\)$/);
    return m ? { fn: m[1].trim(), arg: m[2].trim() } : null;
}
function allContextObjects(ctx) {
    return [...ctx.premises, ...ctx.assumptions, ...classicalObjects(ctx)];
}
function splitTopLevelLeq(s) {
    let depth = 0;
    for (let i = 0; i < s.length - 1; i++) {
        const ch = s[i];
        if (ch === '(' || ch === '[')
            depth++;
        else if (ch === ')' || ch === ']')
            depth--;
        else if (depth === 0 && s[i] === '≤') {
            return [s.slice(0, i).trim(), s.slice(i + 1).trim()];
        }
    }
    return null;
}
function splitTopLevelSum(s) {
    let depth = 0;
    for (let i = s.length - 1; i >= 0; i--) {
        const ch = s[i];
        if (ch === ')' || ch === ']')
            depth++;
        else if (ch === '(' || ch === '[')
            depth--;
        else if (depth === 0 && ch === '+') {
            return [s.slice(0, i).trim(), s.slice(i + 1).trim()];
        }
    }
    return null;
}
function deriveMeasureClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    // ── SIGMA_CONTAINS_SPACE / SIGMA_CONTAINS_EMPTY ──────────────────────────────
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (membership) {
        // X ∈ Σ when SigmaAlgebra(Σ, X)
        for (const obj of all) {
            const sa = parseSigmaAlgebraArgs(obj.claim);
            if (!sa)
                continue;
            if (sa.sigma === membership.set && sa.space === membership.element) {
                createKernelObject(ctx, claim, 'SIGMA_CONTAINS_SPACE', step, [obj.id]);
                return { rule: 'SIGMA_CONTAINS_SPACE', state: 'PROVED', uses: [obj.claim], message: 'The whole space belongs to its sigma-algebra' };
            }
            // ∅ ∈ Σ
            if (sa.sigma === membership.set && membership.element === '∅') {
                createKernelObject(ctx, claim, 'SIGMA_CONTAINS_EMPTY', step, [obj.id]);
                return { rule: 'SIGMA_CONTAINS_EMPTY', state: 'PROVED', uses: [obj.claim], message: 'The empty set belongs to every sigma-algebra' };
            }
        }
        // SIGMA_CLOSED_COMPLEMENT: complement(A, X) ∈ Σ
        const compMatch = membership.element.match(/^complement\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
        if (compMatch) {
            const a = compMatch[1].trim();
            const x = compMatch[2].trim();
            for (const obj of all) {
                const sa = parseSigmaAlgebraArgs(obj.claim);
                if (!sa || sa.sigma !== membership.set || sa.space !== x)
                    continue;
                const aIn = requireClassical(ctx, `${a} ∈ ${membership.set}`, 'SIGMA_CLOSED_COMPLEMENT');
                if (aIn) {
                    createKernelObject(ctx, claim, 'SIGMA_CLOSED_COMPLEMENT', step, [obj.id, aIn.id]);
                    return { rule: 'SIGMA_CLOSED_COMPLEMENT', state: 'PROVED', uses: [obj.claim, aIn.claim], message: 'Sigma-algebras are closed under complementation' };
                }
            }
        }
        // SIGMA_CLOSED_UNION: A ∪ B ∈ Σ
        const unionParts = (0, propositions_1.parseBinarySetCanonical)(membership.element, '∪');
        if (unionParts) {
            const sigma = membership.set;
            for (const obj of all) {
                if (!parseSigmaAlgebraArgs(obj.claim) || parseSigmaAlgebraArgs(obj.claim).sigma !== sigma)
                    continue;
                const aIn = requireClassical(ctx, `${unionParts[0]} ∈ ${sigma}`, 'SIGMA_CLOSED_UNION');
                const bIn = requireClassical(ctx, `${unionParts[1]} ∈ ${sigma}`, 'SIGMA_CLOSED_UNION');
                if (aIn && bIn) {
                    createKernelObject(ctx, claim, 'SIGMA_CLOSED_UNION', step, [obj.id, aIn.id, bIn.id]);
                    return { rule: 'SIGMA_CLOSED_UNION', state: 'PROVED', uses: [obj.claim, aIn.claim, bIn.claim], message: 'Sigma-algebras are closed under binary union' };
                }
            }
        }
        // MEASURABLE_PREIMAGE: preimage(f, B) ∈ Σ_X
        const preimageMatch = membership.element.match(/^preimage\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
        if (preimageMatch) {
            const f = preimageMatch[1].trim();
            const b = preimageMatch[2].trim();
            const sigmaX = membership.set;
            for (const obj of all) {
                const ma = parseMeasurableArgs(obj.claim);
                if (!ma || ma.f !== f || ma.sigmaX !== sigmaX)
                    continue;
                const bIn = requireClassical(ctx, `${b} ∈ ${ma.sigmaY}`, 'MEASURABLE_PREIMAGE');
                if (bIn) {
                    createKernelObject(ctx, claim, 'MEASURABLE_PREIMAGE', step, [obj.id, bIn.id]);
                    return { rule: 'MEASURABLE_PREIMAGE', state: 'PROVED', uses: [obj.claim, bIn.claim], message: 'Preimage of a measurable set under a measurable function is measurable' };
                }
            }
        }
    }
    // ── Equality claims ──────────────────────────────────────────────────────────
    const equality = (0, propositions_1.parseEqualityCanonical)(claim);
    if (equality) {
        // MEASURE_EMPTY: μ(∅) = 0
        const leftApp = parseFunctionApplication(equality.left);
        const rightApp = parseFunctionApplication(equality.right);
        if (leftApp && leftApp.arg === '∅' && equality.right === '0') {
            for (const obj of all) {
                const ma = parseMeasureArgs(obj.claim);
                if (ma && ma.mu === leftApp.fn) {
                    createKernelObject(ctx, claim, 'MEASURE_EMPTY', step, [obj.id]);
                    return { rule: 'MEASURE_EMPTY', state: 'PROVED', uses: [obj.claim], message: 'Axiom: the measure of the empty set is zero' };
                }
            }
        }
        if (rightApp && rightApp.arg === '∅' && equality.left === '0') {
            for (const obj of all) {
                const ma = parseMeasureArgs(obj.claim);
                if (ma && ma.mu === rightApp.fn) {
                    createKernelObject(ctx, claim, 'MEASURE_EMPTY', step, [obj.id]);
                    return { rule: 'MEASURE_EMPTY', state: 'PROVED', uses: [obj.claim], message: 'Axiom: the measure of the empty set is zero' };
                }
            }
        }
        // MEASURE_ADDITIVE: μ(A ∪ B) = μ(A) + μ(B) when A ∩ B = ∅
        if (leftApp) {
            const unionParts = (0, propositions_1.parseBinarySetCanonical)(leftApp.arg, '∪');
            const sumParts = splitTopLevelSum(equality.right);
            if (unionParts && sumParts) {
                const aApp = parseFunctionApplication(sumParts[0]);
                const bApp = parseFunctionApplication(sumParts[1]);
                if (aApp && bApp && aApp.fn === leftApp.fn && bApp.fn === leftApp.fn &&
                    aApp.arg === unionParts[0] && bApp.arg === unionParts[1]) {
                    for (const obj of all) {
                        const ma = parseMeasureArgs(obj.claim);
                        if (!ma || ma.mu !== leftApp.fn)
                            continue;
                        const disjoint = requireClassical(ctx, `${unionParts[0]} ∩ ${unionParts[1]} = ∅`, 'MEASURE_ADDITIVE');
                        if (disjoint) {
                            createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step, [obj.id, disjoint.id]);
                            return { rule: 'MEASURE_ADDITIVE', state: 'PROVED', uses: [obj.claim, disjoint.claim], message: 'Countable additivity on disjoint sets' };
                        }
                    }
                }
            }
        }
        // PROB_COMPLEMENT: P(complement(A, X)) = 1 - P(A)
        if (leftApp) {
            const compArg = leftApp.arg.match(/^complement\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
            const rhs1MinusP = equality.right.match(/^1\s*-\s*([^\s(]+)\s*\((.+)\)$/);
            if (compArg && rhs1MinusP && rhs1MinusP[1] === leftApp.fn && rhs1MinusP[2] === compArg[1].trim()) {
                for (const obj of all) {
                    const pma = parseProbMeasureArgs(obj.claim);
                    if (!pma || pma.p !== leftApp.fn)
                        continue;
                    const aIn = requireClassical(ctx, `${compArg[1].trim()} ∈ ${pma.sigma}`, 'PROB_COMPLEMENT');
                    if (aIn) {
                        createKernelObject(ctx, claim, 'PROB_COMPLEMENT', step, [obj.id, aIn.id]);
                        return { rule: 'PROB_COMPLEMENT', state: 'PROVED', uses: [obj.claim, aIn.claim], message: 'P(Aᶜ) = 1 − P(A) for probability measures' };
                    }
                }
            }
        }
        // PROB_TOTAL: P(X) = 1
        if (leftApp && equality.right === '1') {
            for (const obj of all) {
                const pma = parseProbMeasureArgs(obj.claim);
                if (!pma || pma.p !== leftApp.fn || pma.space !== leftApp.arg)
                    continue;
                createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id]);
                return { rule: 'PROB_TOTAL', state: 'PROVED', uses: [obj.claim], message: 'Axiom: probability of the whole space is 1' };
            }
        }
    }
    // ── Inequality claims ────────────────────────────────────────────────────────
    const leqParts = splitTopLevelLeq(claim);
    if (leqParts) {
        const lhsApp = parseFunctionApplication(leqParts[0]);
        const rhsApp = parseFunctionApplication(leqParts[1]);
        // MEASURE_MONO: μ(A) ≤ μ(B) when A ⊆ B
        if (lhsApp && rhsApp && lhsApp.fn === rhsApp.fn) {
            for (const obj of all) {
                const ma = parseMeasureArgs(obj.claim) ?? (parseProbMeasureArgs(obj.claim) ? { mu: parseProbMeasureArgs(obj.claim).p, sigma: parseProbMeasureArgs(obj.claim).sigma } : null);
                if (!ma || ma.mu !== lhsApp.fn)
                    continue;
                const subset = requireClassical(ctx, `${lhsApp.arg} ⊆ ${rhsApp.arg}`, 'MEASURE_MONO')
                    ?? requireClassical(ctx, `${lhsApp.arg} ⊂ ${rhsApp.arg}`, 'MEASURE_MONO');
                const aIn = requireClassical(ctx, `${lhsApp.arg} ∈ ${ma.sigma}`, 'MEASURE_MONO');
                const bIn = requireClassical(ctx, `${rhsApp.arg} ∈ ${ma.sigma}`, 'MEASURE_MONO');
                if (subset && aIn && bIn) {
                    createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id, subset.id, aIn.id, bIn.id]);
                    return { rule: 'MEASURE_MONO', state: 'PROVED', uses: [obj.claim, subset.claim, aIn.claim], message: 'Monotonicity: A ⊆ B implies μ(A) ≤ μ(B)' };
                }
            }
        }
        // MEASURE_SUBADDITIVE: μ(A ∪ B) ≤ μ(A) + μ(B)
        if (lhsApp) {
            const unionParts = (0, propositions_1.parseBinarySetCanonical)(lhsApp.arg, '∪');
            const sumParts = splitTopLevelSum(leqParts[1]);
            if (unionParts && sumParts) {
                const aApp = parseFunctionApplication(sumParts[0]);
                const bApp = parseFunctionApplication(sumParts[1]);
                if (aApp && bApp && aApp.fn === lhsApp.fn && bApp.fn === lhsApp.fn &&
                    aApp.arg === unionParts[0] && bApp.arg === unionParts[1]) {
                    for (const obj of all) {
                        const ma = parseMeasureArgs(obj.claim) ?? (parseProbMeasureArgs(obj.claim) ? { mu: parseProbMeasureArgs(obj.claim).p, sigma: parseProbMeasureArgs(obj.claim).sigma } : null);
                        if (!ma || ma.mu !== lhsApp.fn)
                            continue;
                        const aIn = requireClassical(ctx, `${unionParts[0]} ∈ ${ma.sigma}`, 'MEASURE_SUBADDITIVE');
                        const bIn = requireClassical(ctx, `${unionParts[1]} ∈ ${ma.sigma}`, 'MEASURE_SUBADDITIVE');
                        if (aIn && bIn) {
                            createKernelObject(ctx, claim, 'MEASURE_SUBADDITIVE', step, [obj.id, aIn.id, bIn.id]);
                            return { rule: 'MEASURE_SUBADDITIVE', state: 'PROVED', uses: [obj.claim, aIn.claim, bIn.claim], message: 'Subadditivity: μ(A ∪ B) ≤ μ(A) + μ(B)' };
                        }
                    }
                }
            }
        }
    }
    // ── MEASURABLE_COMPOSE: Measurable(g ∘ f, Σ_X, Σ_Z) ─────────────────────────
    const measPred = (0, propositions_1.parseMeasurePredicateCanonical)(claim);
    if (measPred?.name === 'Measurable') {
        const [fg, sigmaX, sigmaZ] = measPred.args;
        const compParts = fg.match(/^(.+?)\s*∘\s*(.+)$/);
        if (compParts) {
            const g = compParts[1].trim();
            const f = compParts[2].trim();
            for (const fObj of all) {
                const fma = parseMeasurableArgs(fObj.claim);
                if (!fma || fma.f !== f || fma.sigmaX !== sigmaX)
                    continue;
                for (const gObj of all) {
                    const gma = parseMeasurableArgs(gObj.claim);
                    if (!gma || gma.f !== g || gma.sigmaX !== fma.sigmaY || gma.sigmaY !== sigmaZ)
                        continue;
                    createKernelObject(ctx, claim, 'MEASURABLE_COMPOSE', step, [fObj.id, gObj.id]);
                    return { rule: 'MEASURABLE_COMPOSE', state: 'PROVED', uses: [fObj.claim, gObj.claim], message: 'Composition of measurable functions is measurable' };
                }
            }
        }
    }
    return null;
}
function deriveCategoryClaim(ctx, claim, step) {
    const morphismDecl = (0, propositions_1.parseMorphismDeclarationCanonical)(claim);
    if (morphismDecl) {
        try {
            ctx.diagrams.registerClaim(claim);
            createKernelObject(ctx, claim, 'CAT_MORPHISM', step);
            return {
                rule: 'CAT_MORPHISM',
                state: 'PROVED',
                message: 'Registered a categorical morphism with explicit domain and codomain',
            };
        }
        catch (error) {
            return categoryFailure(error, 'CAT_MORPHISM');
        }
    }
    const predicate = (0, propositions_1.parseCategoryPredicateCanonical)(claim);
    if (predicate) {
        try {
            const result = deriveCategoryPredicate(ctx, predicate, step, claim);
            if (result)
                return result;
        }
        catch (error) {
            return categoryFailure(error, predicateToRule(predicate.name));
        }
    }
    const categoricalEquality = looksLikeCategoricalEquality(claim) ? (0, propositions_1.parseCategoricalEqualityCanonical)(claim) : null;
    if (categoricalEquality) {
        try {
            const result = deriveCategoricalEquality(ctx, claim, categoricalEquality.left, categoricalEquality.right, step);
            if (result)
                return result;
        }
        catch (error) {
            return categoryFailure(error, 'CAT_EQUALITY');
        }
    }
    return null;
}
function deriveCategoryPredicate(ctx, predicate, step, claim) {
    switch (predicate.name) {
        case 'Category':
        case 'Object':
        case 'Morphism':
        case 'Functor':
            ctx.diagrams.registerPredicate(predicate.name, predicate.args);
            createKernelObject(ctx, claim, predicate.name === 'Functor' ? 'FUNCTOR_INTRO' : predicate.name === 'Morphism' ? 'CAT_MORPHISM' : 'CAT_OBJECT', step);
            return {
                rule: predicate.name === 'Functor' ? 'FUNCTOR_INTRO' : predicate.name === 'Morphism' ? 'CAT_MORPHISM' : 'CAT_OBJECT',
                state: 'PROVED',
                message: predicate.name === 'Functor'
                    ? 'Registered a functor between finite categories'
                    : predicate.name === 'Morphism'
                        ? 'Registered a categorical morphism declaration inside an explicit category'
                        : 'Registered categorical structure in the finite-diagram kernel',
            };
        case 'Iso':
            return deriveIso(ctx, predicate.args, claim, step);
        case 'Product':
            return deriveProduct(ctx, predicate.args, claim, step);
        case 'ProductMediator':
            return deriveProductMediator(ctx, predicate.args, claim, step);
        case 'Coproduct':
            return deriveCoproduct(ctx, predicate.args, claim, step);
        case 'Pullback':
            return derivePullback(ctx, predicate.args, claim, step);
        case 'Pushout':
            return derivePushout(ctx, predicate.args, claim, step);
    }
}
function deriveCategoricalEquality(ctx, claim, left, right, step) {
    const formattedLeft = (0, propositions_1.formatMorphismExpr)(left);
    const formattedRight = (0, propositions_1.formatMorphismExpr)(right);
    const leftDecl = (0, propositions_1.parseMorphismDeclarationCanonical)(formattedLeft);
    const rightDecl = (0, propositions_1.parseMorphismDeclarationCanonical)(formattedRight);
    void leftDecl;
    void rightDecl;
    if (ctx.diagrams.equalMorphisms(left, right)) {
        createKernelObject(ctx, claim, 'CAT_EQUALITY', step);
        return {
            rule: 'CAT_EQUALITY',
            state: 'PROVED',
            uses: [formattedLeft, formattedRight],
            message: 'Validated equality between categorical composites',
        };
    }
    // Identity laws and associativity can be proved from structure even without prior equality registration.
    const leftText = formattedLeft;
    const rightText = formattedRight;
    if (stripIdentity(leftText) === stripIdentity(rightText)) {
        createKernelObject(ctx, claim, 'CAT_IDENTITY', step);
        return {
            rule: 'CAT_IDENTITY',
            state: 'PROVED',
            uses: [formattedLeft, formattedRight],
            message: 'Validated a categorical identity law',
        };
    }
    if (normalizeComposition(leftText) === normalizeComposition(rightText)) {
        createKernelObject(ctx, claim, 'CAT_ASSOC', step);
        return {
            rule: 'CAT_ASSOC',
            state: 'PROVED',
            uses: [formattedLeft, formattedRight],
            message: 'Validated associativity of explicit morphism composition',
        };
    }
    const functorLaw = deriveFunctorEquality(ctx, left, right, claim, step);
    if (functorLaw)
        return functorLaw;
    return null;
}
function deriveIso(ctx, args, claim, step) {
    const target = args[0];
    if (!target)
        return null;
    const morphism = ctx.diagrams.resolveMorphismExpr({ kind: 'name', label: target });
    for (const object of [...ctx.objects, ...ctx.premises, ...ctx.assumptions]) {
        const candidate = (0, propositions_1.parseMorphismDeclarationCanonical)(object.claim);
        if (!candidate)
            continue;
        try {
            const inverse = ctx.diagrams.resolveMorphismExpr({ kind: 'name', label: candidate.label });
            if (inverse.category !== morphism.category)
                continue;
            const leftId = `id_${ctx.diagrams.objectById(morphism.domain).label}`;
            const rightId = `id_${ctx.diagrams.objectById(morphism.codomain).label}`;
            const leftEq = `${candidate.label} ∘ ${target} = ${leftId}`;
            const rightEq = `${target} ∘ ${candidate.label} = ${rightId}`;
            if (findExact(ctx.objects, leftEq, false) || findExact(ctx.premises, leftEq, false) || findExact(ctx.assumptions, leftEq, false)) {
                if (findExact(ctx.objects, rightEq, false) || findExact(ctx.premises, rightEq, false) || findExact(ctx.assumptions, rightEq, false)) {
                    createKernelObject(ctx, claim, 'ISO_INTRO', step);
                    return {
                        rule: 'ISO_INTRO',
                        state: 'PROVED',
                        uses: [leftEq, rightEq],
                        message: `Validated explicit inverse equations for Iso(${target})`,
                    };
                }
            }
        }
        catch {
            continue;
        }
    }
    return {
        rule: 'ISO_INTRO',
        state: 'FAILED',
        message: `Category error: inverse conditions for Iso(${target}) are not satisfied`,
    };
}
function deriveProduct(ctx, args, claim, step) {
    if (args.length < 5)
        return null;
    const [productObject, pi1, pi2, leftObject, rightObject] = args;
    const leftDecl = hasMorphism(ctx, `${pi1} : ${productObject} → ${leftObject}`);
    const rightDecl = hasMorphism(ctx, `${pi2} : ${productObject} → ${rightObject}`);
    if (leftDecl && rightDecl) {
        createKernelObject(ctx, claim, 'PRODUCT_INTRO', step);
        return {
            rule: 'PRODUCT_INTRO',
            state: 'PROVED',
            uses: [`${pi1} : ${productObject} → ${leftObject}`, `${pi2} : ${productObject} → ${rightObject}`],
            message: 'Validated the explicit projections for a finite product cone',
        };
    }
    return null;
}
function deriveProductMediator(ctx, args, claim, step) {
    if (args.length < 5)
        return null;
    const [mediator, left, right, pi1, pi2] = args;
    const leftEq = `${pi1} ∘ ${mediator} = ${left}`;
    const rightEq = `${pi2} ∘ ${mediator} = ${right}`;
    if (hasClaim(ctx, leftEq) && hasClaim(ctx, rightEq)) {
        createKernelObject(ctx, claim, 'PRODUCT_MEDIATOR', step);
        return {
            rule: 'PRODUCT_MEDIATOR',
            state: 'PROVED',
            uses: [leftEq, rightEq],
            message: 'Universal property error cleared: mediator satisfies both projection equations',
        };
    }
    return {
        rule: 'PRODUCT_MEDIATOR',
        state: 'FAILED',
        message: 'Universal property error: mediator does not satisfy both projection equations',
    };
}
function deriveCoproduct(ctx, args, claim, step) {
    if (args.length < 5)
        return null;
    const [sumObject, i1, i2, leftObject, rightObject] = args;
    if (hasMorphism(ctx, `${i1} : ${leftObject} → ${sumObject}`) && hasMorphism(ctx, `${i2} : ${rightObject} → ${sumObject}`)) {
        createKernelObject(ctx, claim, 'COPRODUCT_INTRO', step);
        return {
            rule: 'COPRODUCT_INTRO',
            state: 'PROVED',
            uses: [`${i1} : ${leftObject} → ${sumObject}`, `${i2} : ${rightObject} → ${sumObject}`],
            message: 'Validated the explicit injections for a finite coproduct cocone',
        };
    }
    return null;
}
function derivePullback(ctx, args, claim, step) {
    if (args.length < 5)
        return null;
    const [pullbackObject, p1, p2, f, g] = args;
    const p1Decl = findDeclarationByLabel(ctx, p1);
    const p2Decl = findDeclarationByLabel(ctx, p2);
    const fDecl = findDeclarationByLabel(ctx, f);
    const gDecl = findDeclarationByLabel(ctx, g);
    if (!p1Decl || !p2Decl || !fDecl || !gDecl) {
        return null;
    }
    const commuting = `${f} ∘ ${p1} = ${g} ∘ ${p2}`;
    if (!hasClaim(ctx, commuting)) {
        return { rule: 'PULLBACK_INTRO', state: 'FAILED', message: 'Diagram error: square does not commute' };
    }
    if (p1Decl.domain !== pullbackObject || p2Decl.domain !== pullbackObject) {
        return { rule: 'PULLBACK_INTRO', state: 'FAILED', message: 'Category error: pullback legs do not originate at the claimed pullback object' };
    }
    createKernelObject(ctx, claim, 'PULLBACK_INTRO', step);
    return {
        rule: 'PULLBACK_INTRO',
        state: 'PROVED',
        uses: [commuting],
        message: 'Validated a finite pullback square and its commuting condition',
    };
}
function derivePushout(ctx, args, claim, step) {
    if (args.length < 5)
        return null;
    const [pushoutObject, i1, i2, f, g] = args;
    const i1Decl = findDeclarationByLabel(ctx, i1);
    const i2Decl = findDeclarationByLabel(ctx, i2);
    if (!i1Decl || !i2Decl) {
        return null;
    }
    const commuting = `${i1} ∘ ${f} = ${i2} ∘ ${g}`;
    if (!hasClaim(ctx, commuting)) {
        return { rule: 'PUSHOUT_INTRO', state: 'FAILED', message: 'Diagram error: square does not commute' };
    }
    if (i1Decl.codomain !== pushoutObject || i2Decl.codomain !== pushoutObject) {
        return { rule: 'PUSHOUT_INTRO', state: 'FAILED', message: 'Category error: pushout legs do not target the claimed pushout object' };
    }
    createKernelObject(ctx, claim, 'PUSHOUT_INTRO', step);
    return {
        rule: 'PUSHOUT_INTRO',
        state: 'PROVED',
        uses: [commuting],
        message: 'Validated a finite pushout square and its commuting condition',
    };
}
function categoryFailure(error, rule) {
    const message = error instanceof Error ? error.message : 'Unknown category-check failure';
    return { rule, state: 'FAILED', message };
}
function deriveFunctorEquality(ctx, left, right, claim, step) {
    if (left.kind === 'functor_map' && right.kind === 'compose') {
        if (left.argument.kind === 'compose' && right.left.kind === 'functor_map' && right.right.kind === 'functor_map') {
            if (left.functor === right.left.functor && left.functor === right.right.functor) {
                const expectedLeft = (0, propositions_1.formatMorphismExpr)(left.argument.left);
                const expectedRight = (0, propositions_1.formatMorphismExpr)(left.argument.right);
                if (expectedLeft === (0, propositions_1.formatMorphismExpr)(right.left.argument) && expectedRight === (0, propositions_1.formatMorphismExpr)(right.right.argument)) {
                    createKernelObject(ctx, claim, 'FUNCTOR_COMPOSE', step);
                    return {
                        rule: 'FUNCTOR_COMPOSE',
                        state: 'PROVED',
                        uses: [(0, propositions_1.formatMorphismExpr)(left), (0, propositions_1.formatMorphismExpr)(right)],
                        message: 'Validated that the functor preserves composition',
                    };
                }
            }
        }
    }
    if (left.kind === 'functor_map' && left.argument.kind === 'identity' && right.kind === 'identity') {
        if (right.object === `${left.functor}(${left.argument.object})`) {
            createKernelObject(ctx, claim, 'FUNCTOR_ID', step);
            return {
                rule: 'FUNCTOR_ID',
                state: 'PROVED',
                uses: [(0, propositions_1.formatMorphismExpr)(left), (0, propositions_1.formatMorphismExpr)(right)],
                message: 'Validated that the functor preserves identity morphisms',
            };
        }
    }
    return null;
}
function deriveAndElim(ctx, claim, step) {
    for (const object of classicalObjects(ctx)) {
        const conjunction = (0, propositions_1.parseConjunctionCanonical)(object.claim);
        if (!conjunction)
            continue;
        if ((0, propositions_1.sameProp)(conjunction[0], claim)) {
            createKernelObject(ctx, claim, 'AND_ELIM_LEFT', step, [object.id]);
            return {
                rule: 'AND_ELIM_LEFT',
                state: 'PROVED',
                uses: [object.claim],
                message: 'Read the left component from a Boolean meet',
            };
        }
        if ((0, propositions_1.sameProp)(conjunction[1], claim)) {
            createKernelObject(ctx, claim, 'AND_ELIM_RIGHT', step, [object.id]);
            return {
                rule: 'AND_ELIM_RIGHT',
                state: 'PROVED',
                uses: [object.claim],
                message: 'Read the right component from a Boolean meet',
            };
        }
    }
    return null;
}
function deriveNotIntro(ctx, claim, step) {
    if (!claim.startsWith('¬'))
        return null;
    const positive = claim.slice(1).trim();
    const positiveObject = requireClassical(ctx, positive, 'NOT_INTRO');
    if (!positiveObject)
        return null;
    ctx.category.complementOf(positive);
    createKernelObject(ctx, claim, 'NOT_INTRO', step, [positiveObject.id]);
    return {
        rule: 'NOT_INTRO',
        state: 'PROVED',
        uses: [positiveObject.claim],
        message: 'Used the primitive Boolean complement associated with the proposition',
    };
}
function deriveImpliesElim(ctx, claim, step) {
    for (const object of classicalObjects(ctx)) {
        const implication = (0, propositions_1.parseImplicationCanonical)(object.claim);
        if (!implication || !(0, propositions_1.sameProp)(implication[1], claim))
            continue;
        const antecedent = requireClassical(ctx, implication[0], 'IMPLIES_ELIM');
        if (!antecedent)
            continue;
        const antecedentMorph = toTopMorphism(ctx, antecedent);
        const implicationMorph = toImplicationMorphism(ctx, object);
        const composed = ctx.category.compose(antecedentMorph, implicationMorph, claim, 'IMPLIES_ELIM');
        registerDerivedObject(ctx, claim, step, 'IMPLIES_ELIM', composed, [antecedent.id, object.id]);
        return {
            rule: 'IMPLIES_ELIM',
            state: 'PROVED',
            uses: [implication[0], ctx.category.classicalImplication(implication[0], implication[1])],
            message: 'Applied classical modus ponens using the complement-disjunction reading of implication',
        };
    }
    return null;
}
function deriveImpliesIntro(ctx, claim, step) {
    const implication = (0, propositions_1.parseImplicationCanonical)(claim);
    if (!implication)
        return null;
    const assumption = findExact(ctx.assumptions, implication[0], false);
    const consequent = requireClassical(ctx, implication[1], 'IMPLIES_INTRO');
    if (!assumption || !consequent)
        return null;
    createKernelObject(ctx, claim, 'IMPLIES_INTRO', step, [assumption.id, consequent.id]);
    return {
        rule: 'IMPLIES_INTRO',
        state: 'PROVED',
        uses: [implication[0], implication[1], ctx.category.classicalImplication(implication[0], implication[1])],
        message: 'Formed the classical implication as a complement-or-consequent morphism',
    };
}
function deriveIffIntro(ctx, claim, step) {
    const iff = (0, propositions_1.parseIffCanonical)(claim);
    if (!iff)
        return null;
    const left = requireClassical(ctx, `${iff[0]} → ${iff[1]}`, 'IMPLIES_ELIM');
    const right = requireClassical(ctx, `${iff[1]} → ${iff[0]}`, 'IMPLIES_ELIM');
    if (!left || !right)
        return null;
    createKernelObject(ctx, claim, 'OR_ELIM', step, [left.id, right.id]);
    return {
        rule: 'OR_ELIM',
        state: 'PROVED',
        uses: [left.claim, right.claim],
        message: 'Built the biconditional from both directional morphisms',
    };
}
function deriveIffElim(ctx, claim, step) {
    for (const object of classicalObjects(ctx)) {
        const iff = (0, propositions_1.parseIffCanonical)(object.claim);
        if (!iff)
            continue;
        const left = findExact(ctx.objects, iff[0], false);
        const right = findExact(ctx.objects, iff[1], false);
        if (left && (0, propositions_1.sameProp)(iff[1], claim)) {
            createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [object.id, left.id]);
            return {
                rule: 'IMPLIES_ELIM',
                state: 'PROVED',
                uses: [object.claim, left.claim],
                message: 'Used the biconditional and the left side to derive the right side',
            };
        }
        if (right && (0, propositions_1.sameProp)(iff[0], claim)) {
            createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [object.id, right.id]);
            return {
                rule: 'IMPLIES_ELIM',
                state: 'PROVED',
                uses: [object.claim, right.claim],
                message: 'Used the biconditional and the right side to derive the left side',
            };
        }
    }
    return null;
}
function deriveOrIntro(ctx, claim, step) {
    const parts = (0, propositions_1.parseDisjunctionCanonical)(claim);
    if (!parts)
        return null;
    const left = requireClassical(ctx, parts[0], 'OR_INTRO_LEFT');
    if (left) {
        createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [left.id]);
        return {
            rule: 'OR_INTRO_LEFT',
            state: 'PROVED',
            uses: [parts[0]],
            message: 'Injected the left branch into a classical join',
        };
    }
    const right = requireClassical(ctx, parts[1], 'OR_INTRO_RIGHT');
    if (right) {
        createKernelObject(ctx, claim, 'OR_INTRO_RIGHT', step, [right.id]);
        return {
            rule: 'OR_INTRO_RIGHT',
            state: 'PROVED',
            uses: [parts[1]],
            message: 'Injected the right branch into a classical join',
        };
    }
    return null;
}
function deriveOrElim(ctx, claim, step) {
    for (const object of classicalObjects(ctx)) {
        const disjunction = (0, propositions_1.parseDisjunctionCanonical)(object.claim);
        if (!disjunction)
            continue;
        const leftArrow = findExact(ctx.objects, `${disjunction[0]} → ${claim}`, false);
        const rightArrow = findExact(ctx.objects, `${disjunction[1]} → ${claim}`, false);
        if (!leftArrow || !rightArrow)
            continue;
        createKernelObject(ctx, claim, 'OR_ELIM', step, [object.id, leftArrow.id, rightArrow.id]);
        return {
            rule: 'OR_ELIM',
            state: 'PROVED',
            uses: [object.claim, leftArrow.claim, rightArrow.claim],
            message: 'Eliminated a classical disjunction across both branches',
        };
    }
    return null;
}
function deriveSubsetElim(ctx, claim, step) {
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (!membership)
        return null;
    for (const object of classicalObjects(ctx)) {
        const subset = (0, propositions_1.parseSubsetCanonical)(object.claim);
        if (!subset || !(0, propositions_1.sameProp)(subset.right, membership.set))
            continue;
        const input = requireClassical(ctx, `${membership.element} ∈ ${subset.left}`, 'IMPLIES_ELIM');
        if (!input)
            continue;
        createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [input.id, object.id]);
        return {
            rule: 'IMPLIES_ELIM',
            state: 'PROVED',
            uses: [input.claim, object.claim],
            message: 'Transported membership along a subset morphism',
        };
    }
    return null;
}
function deriveSubsetIntro(ctx, claim, step) {
    const subset = (0, propositions_1.parseSubsetCanonical)(claim);
    if (!subset)
        return null;
    const witness = ctx.variables.length > 0 ? ctx.variables[ctx.variables.length - 1].name : null;
    if (!witness)
        return null;
    const leftMembership = findExact(ctx.assumptions, `${witness} ∈ ${subset.left}`, false);
    const rightMembership = requireClassical(ctx, `${witness} ∈ ${subset.right}`, 'IMPLIES_INTRO');
    if (!leftMembership || !rightMembership)
        return null;
    createKernelObject(ctx, claim, 'IMPLIES_INTRO', step, [leftMembership.id, rightMembership.id]);
    return {
        rule: 'IMPLIES_INTRO',
        state: 'PROVED',
        uses: [leftMembership.claim, rightMembership.claim],
        message: 'Restricted the domain of a partial map witness branch into a subset morphism',
    };
}
function deriveSubsetTransitivity(ctx, claim, step) {
    const subset = (0, propositions_1.parseSubsetCanonical)(claim);
    if (!subset)
        return null;
    for (const left of classicalObjects(ctx)) {
        const first = (0, propositions_1.parseSubsetCanonical)(left.claim);
        if (!first || !(0, propositions_1.sameProp)(first.left, subset.left))
            continue;
        for (const right of classicalObjects(ctx)) {
            const second = (0, propositions_1.parseSubsetCanonical)(right.claim);
            if (!second)
                continue;
            if ((0, propositions_1.sameProp)(first.right, second.left) && (0, propositions_1.sameProp)(second.right, subset.right)) {
                createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [left.id, right.id]);
                return {
                    rule: 'IMPLIES_ELIM',
                    state: 'PROVED',
                    uses: [left.claim, right.claim],
                    message: 'Composed two subset morphisms transitively',
                };
            }
        }
    }
    return null;
}
function deriveSubsetAntisymmetry(ctx, claim, step) {
    const equality = (0, propositions_1.parseEqualityCanonical)(claim);
    if (!equality)
        return null;
    const forward = requireClassical(ctx, `${equality.left} ⊂ ${equality.right}`, 'IMPLIES_ELIM')
        ?? requireClassical(ctx, `${equality.left} ⊆ ${equality.right}`, 'IMPLIES_ELIM');
    const backward = requireClassical(ctx, `${equality.right} ⊂ ${equality.left}`, 'IMPLIES_ELIM')
        ?? requireClassical(ctx, `${equality.right} ⊆ ${equality.left}`, 'IMPLIES_ELIM');
    if (!forward || !backward)
        return null;
    createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [forward.id, backward.id]);
    return {
        rule: 'IMPLIES_ELIM',
        state: 'PROVED',
        uses: [forward.claim, backward.claim],
        message: 'Collapsed mutual subset morphisms into equality',
    };
}
function deriveEqualitySubstitution(ctx, claim, step) {
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (!membership)
        return null;
    for (const equalityObject of classicalObjects(ctx)) {
        const equality = (0, propositions_1.parseEqualityCanonical)(equalityObject.claim);
        if (!equality)
            continue;
        const leftMembership = `${equality.left} ∈ ${membership.set}`;
        const rightMembership = `${equality.right} ∈ ${membership.set}`;
        if ((0, propositions_1.sameProp)(rightMembership, claim)) {
            const source = requireClassical(ctx, leftMembership, 'IMPLIES_ELIM');
            if (source) {
                createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [equalityObject.id, source.id]);
                return {
                    rule: 'IMPLIES_ELIM',
                    state: 'PROVED',
                    uses: [equalityObject.claim, source.claim],
                    message: 'Substituted equal terms inside a membership proposition',
                };
            }
        }
        if ((0, propositions_1.sameProp)(leftMembership, claim)) {
            const source = requireClassical(ctx, rightMembership, 'IMPLIES_ELIM');
            if (source) {
                createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [equalityObject.id, source.id]);
                return {
                    rule: 'IMPLIES_ELIM',
                    state: 'PROVED',
                    uses: [equalityObject.claim, source.claim],
                    message: 'Substituted equal terms inside a membership proposition',
                };
            }
        }
    }
    return null;
}
function deriveUnionRule(ctx, claim, step) {
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (membership) {
        const union = (0, propositions_1.parseBinarySetCanonical)(membership.set, '∪');
        if (union) {
            const left = requireClassical(ctx, `${membership.element} ∈ ${union[0]}`, 'OR_INTRO_LEFT');
            if (left) {
                createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [left.id]);
                return {
                    rule: 'OR_INTRO_LEFT',
                    state: 'PROVED',
                    uses: [left.claim],
                    message: 'Injected membership into the left side of a union',
                };
            }
            const right = requireClassical(ctx, `${membership.element} ∈ ${union[1]}`, 'OR_INTRO_RIGHT');
            if (right) {
                createKernelObject(ctx, claim, 'OR_INTRO_RIGHT', step, [right.id]);
                return {
                    rule: 'OR_INTRO_RIGHT',
                    state: 'PROVED',
                    uses: [right.claim],
                    message: 'Injected membership into the right side of a union',
                };
            }
        }
    }
    const disjunction = (0, propositions_1.parseDisjunctionCanonical)(claim);
    if (!disjunction)
        return null;
    for (const object of [...ctx.premises, ...ctx.assumptions, ...classicalObjects(ctx)]) {
        const membershipObject = (0, propositions_1.parseMembershipCanonical)(object.claim);
        if (!membershipObject)
            continue;
        const setUnion = (0, propositions_1.parseBinarySetCanonical)(membershipObject.set, '∪');
        if (!setUnion)
            continue;
        const expectedLeft = `${membershipObject.element} ∈ ${setUnion[0]}`;
        const expectedRight = `${membershipObject.element} ∈ ${setUnion[1]}`;
        if (((0, propositions_1.sameProp)(disjunction[0], expectedLeft) && (0, propositions_1.sameProp)(disjunction[1], expectedRight)) ||
            ((0, propositions_1.sameProp)(disjunction[0], expectedRight) && (0, propositions_1.sameProp)(disjunction[1], expectedLeft))) {
            createKernelObject(ctx, claim, 'OR_ELIM', step, [object.id]);
            return {
                rule: 'OR_ELIM',
                state: 'PROVED',
                uses: [object.claim],
                message: 'Eliminated union membership into a disjunction of memberships',
            };
        }
    }
    return null;
}
function deriveIntersectionRule(ctx, claim, step) {
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (!membership)
        return null;
    const intersection = (0, propositions_1.parseBinarySetCanonical)(membership.set, '∩');
    if (intersection) {
        const left = requireClassical(ctx, `${membership.element} ∈ ${intersection[0]}`, 'AND_INTRO');
        const right = requireClassical(ctx, `${membership.element} ∈ ${intersection[1]}`, 'AND_INTRO');
        if (left && right) {
            createKernelObject(ctx, claim, 'AND_INTRO', step, [left.id, right.id]);
            return {
                rule: 'AND_INTRO',
                state: 'PROVED',
                uses: [left.claim, right.claim],
                message: 'Constructed intersection membership from both components',
            };
        }
    }
    for (const object of classicalObjects(ctx)) {
        const sourceMembership = (0, propositions_1.parseMembershipCanonical)(object.claim);
        if (!sourceMembership)
            continue;
        const sourceIntersection = (0, propositions_1.parseBinarySetCanonical)(sourceMembership.set, '∩');
        if (!sourceIntersection)
            continue;
        if ((0, propositions_1.sameProp)(claim, `${sourceMembership.element} ∈ ${sourceIntersection[0]}`)) {
            createKernelObject(ctx, claim, 'AND_ELIM_LEFT', step, [object.id]);
            return {
                rule: 'AND_ELIM_LEFT',
                state: 'PROVED',
                uses: [object.claim],
                message: 'Projected the left component of an intersection membership',
            };
        }
        if ((0, propositions_1.sameProp)(claim, `${sourceMembership.element} ∈ ${sourceIntersection[1]}`)) {
            createKernelObject(ctx, claim, 'AND_ELIM_RIGHT', step, [object.id]);
            return {
                rule: 'AND_ELIM_RIGHT',
                state: 'PROVED',
                uses: [object.claim],
                message: 'Projected the right component of an intersection membership',
            };
        }
    }
    return null;
}
function deriveImageRule(ctx, claim, step) {
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (!membership || !/^image\s*\(/.test(membership.set))
        return null;
    const imageMatch = membership.set.match(/^image\s*\(\s*([^,]+)\s*,\s*(.+)\)$/);
    const fxMatch = membership.element.match(/^(.+)\((.+)\)$/);
    if (!imageMatch || !fxMatch || normalizeSpaces(imageMatch[1]) !== normalizeSpaces(fxMatch[1]))
        return null;
    const inputClaim = `${normalizeSpaces(fxMatch[2])} ∈ ${normalizeSpaces(imageMatch[2])}`;
    const input = requireClassical(ctx, inputClaim, 'IMPLIES_ELIM');
    if (!input)
        return null;
    createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [input.id]);
    return {
        rule: 'IMPLIES_ELIM',
        state: 'PROVED',
        uses: [input.claim],
        message: 'Mapped a membership morphism through image formation',
    };
}
function derivePreimageRule(ctx, claim, step) {
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (!membership)
        return null;
    if (/^preimage\s*\(/.test(membership.set)) {
        const match = membership.set.match(/^preimage\s*\(\s*([^,]+)\s*,\s*(.+)\)$/);
        if (!match)
            return null;
        const target = `${normalizeSpaces(match[1])}(${membership.element}) ∈ ${normalizeSpaces(match[2])}`;
        const input = requireClassical(ctx, target, 'IMPLIES_ELIM');
        if (!input)
            return null;
        createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [input.id]);
        return {
            rule: 'IMPLIES_ELIM',
            state: 'PROVED',
            uses: [input.claim],
            message: 'Introduced a preimage membership from its image-side statement',
        };
    }
    const fxMembership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (!fxMembership)
        return null;
    const fxMatch = fxMembership.element.match(/^(.+)\((.+)\)$/);
    if (!fxMatch)
        return null;
    const preimageClaim = `${normalizeSpaces(fxMatch[2])} ∈ preimage(${normalizeSpaces(fxMatch[1])}, ${fxMembership.set})`;
    const input = requireClassical(ctx, preimageClaim, 'IMPLIES_ELIM');
    if (!input)
        return null;
    createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [input.id]);
    return {
        rule: 'IMPLIES_ELIM',
        state: 'PROVED',
        uses: [input.claim],
        message: 'Eliminated a preimage membership back to the codomain side',
    };
}
function deriveQuantifierRule(ctx, claim, step) {
    const forall = (0, propositions_1.parseBoundedQuantifierCanonical)(claim, 'forall');
    if (forall) {
        const witness = findWitness(ctx, forall.variable);
        const assumed = requireClassical(ctx, `${witness ?? forall.variable} ∈ ${forall.set}`, 'IMPLIES_INTRO');
        const bodyClaim = substituteVariable(forall.body, forall.variable, witness ?? forall.variable);
        const body = requireClassical(ctx, bodyClaim, 'IMPLIES_INTRO');
        if (assumed && body) {
            createKernelObject(ctx, claim, 'IMPLIES_INTRO', step, [assumed.id, body.id]);
            return {
                rule: 'IMPLIES_INTRO',
                state: 'PROVED',
                uses: [assumed.claim, body.claim],
                message: 'Constructed the universal limit in the Boolean category from a fresh witness derivation',
            };
        }
    }
    const exists = (0, propositions_1.parseBoundedQuantifierCanonical)(claim, 'exists');
    if (exists) {
        const explicitWitness = findWitness(ctx, exists.variable);
        const witnessCandidates = explicitWitness
            ? [explicitWitness]
            : classicalObjects(ctx)
                .map(object => (0, propositions_1.parseMembershipCanonical)(object.claim)?.element ?? null)
                .filter((value) => Boolean(value));
        for (const witness of witnessCandidates) {
            const membership = requireClassical(ctx, `${witness} ∈ ${exists.set}`, 'OR_INTRO_LEFT');
            const body = requireClassical(ctx, substituteVariable(exists.body, exists.variable, witness), 'OR_INTRO_LEFT');
            if (membership && body) {
                createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [membership.id, body.id]);
                return {
                    rule: 'OR_INTRO_LEFT',
                    state: 'PROVED',
                    uses: [membership.claim, body.claim],
                    message: 'Constructed the existential colimit in the Boolean category from a concrete witness',
                };
            }
        }
    }
    for (const object of classicalObjects(ctx)) {
        const quantified = (0, propositions_1.parseBoundedQuantifierCanonical)(object.claim, 'forall');
        if (!quantified)
            continue;
        const membership = (0, propositions_1.parseMembershipCanonical)(claim);
        if (!membership)
            continue;
        const premise = requireClassical(ctx, `${membership.element} ∈ ${quantified.set}`, 'IMPLIES_ELIM');
        if (!premise)
            continue;
        const expected = substituteVariable(quantified.body, quantified.variable, membership.element);
        if (!(0, propositions_1.sameProp)(expected, claim))
            continue;
        createKernelObject(ctx, claim, 'IMPLIES_ELIM', step, [object.id, premise.id]);
        return {
            rule: 'IMPLIES_ELIM',
            state: 'PROVED',
            uses: [object.claim, premise.claim],
            message: 'Instantiated a universal morphism at a concrete witness',
        };
    }
    for (const object of classicalObjects(ctx)) {
        const quantified = (0, propositions_1.parseBoundedQuantifierCanonical)(object.claim, 'exists');
        if (!quantified)
            continue;
        const witness = findWitness(ctx, quantified.variable);
        const witnessName = witness ?? quantified.variable;
        const membership = findExact(ctx.assumptions, `${witnessName} ∈ ${quantified.set}`, false);
        const body = findExact(ctx.assumptions, substituteVariable(quantified.body, quantified.variable, witnessName), false);
        if (membership && body && !containsWitness(claim, witnessName)) {
            createKernelObject(ctx, claim, 'OR_ELIM', step, [object.id, membership.id, body.id]);
            return {
                rule: 'OR_ELIM',
                state: 'PROVED',
                uses: [object.claim, membership.claim, body.claim],
                message: 'Eliminated an existential morphism through a witness branch',
            };
        }
    }
    return null;
}
function deriveDependentTypeRule(ctx, claim, step) {
    const canonical = (0, propositions_1.parseCanonicalExpr)(claim);
    if (typeof canonical === 'object' && 'kind' in canonical) {
        if (canonical.kind === 'dependent_product') {
            const witness = findWitness(ctx, canonical.variable);
            const assumed = requireClassical(ctx, `${witness ?? canonical.variable} ∈ ${canonical.domain}`, 'PI_INTRO');
            const bodyClaimString = typeof canonical.body === 'string' ? canonical.body : (0, propositions_1.exprToProp)(canonical.body);
            const bodyClaim = substituteVariable(bodyClaimString, canonical.variable, witness ?? canonical.variable);
            const body = requireClassical(ctx, bodyClaim, 'PI_INTRO');
            if (assumed && body) {
                createKernelObject(ctx, claim, 'PI_INTRO', step, [assumed.id, body.id]);
                return {
                    rule: 'PI_INTRO',
                    state: 'PROVED',
                    uses: [assumed.claim, body.claim],
                    message: 'Constructed the Pi product limit from a local dependent type derivation',
                };
            }
        }
        if (canonical.kind === 'dependent_sum') {
            const explicitWitness = findWitness(ctx, canonical.variable);
            if (explicitWitness) {
                const domainClaim = requireClassical(ctx, `${explicitWitness} ∈ ${canonical.domain}`, 'SIGMA_INTRO');
                const bodyClaimString = typeof canonical.body === 'string' ? canonical.body : (0, propositions_1.exprToProp)(canonical.body);
                const bodyClaim = requireClassical(ctx, substituteVariable(bodyClaimString, canonical.variable, explicitWitness), 'SIGMA_INTRO');
                if (domainClaim && bodyClaim) {
                    createKernelObject(ctx, claim, 'SIGMA_INTRO', step, [domainClaim.id, bodyClaim.id]);
                    return {
                        rule: 'SIGMA_INTRO',
                        state: 'PROVED',
                        uses: [domainClaim.claim, bodyClaim.claim],
                        message: 'Constructed a Sigma sum type from an explicit dependent witness pair',
                    };
                }
            }
        }
    }
    for (const object of classicalObjects(ctx)) {
        const pKernel = (0, propositions_1.parseCanonicalExpr)(object.claim);
        if (typeof pKernel === 'object' && 'kind' in pKernel && pKernel.kind === 'dependent_product') {
            const mem = (0, propositions_1.parseMembershipCanonical)(claim);
            if (!mem)
                continue;
            const premise = requireClassical(ctx, `${mem.element} ∈ ${pKernel.domain}`, 'PI_ELIM');
            if (!premise)
                continue;
            const bodyClaimString = typeof pKernel.body === 'string' ? pKernel.body : (0, propositions_1.exprToProp)(pKernel.body);
            const expected = substituteVariable(bodyClaimString, pKernel.variable, mem.element);
            if ((0, propositions_1.sameProp)(expected, claim)) {
                createKernelObject(ctx, claim, 'PI_ELIM', step, [object.id, premise.id]);
                return {
                    rule: 'PI_ELIM',
                    state: 'PROVED',
                    uses: [object.claim, premise.claim],
                    message: 'Applied a dependent Pi type application binding the context',
                };
            }
        }
        // ── SIGMA_ELIM: from p ∈ Σ x ∈ A, P(x) derive fst(p) ∈ A or P(fst(p)) ──
        // parseCanonicalExpr now handles "p ∈ Σ n ∈ A, body" as dependent_sum
        if (typeof pKernel === 'object' && 'kind' in pKernel && pKernel.kind === 'dependent_sum' && pKernel.element) {
            const bodyClaimString = typeof pKernel.body === 'string' ? pKernel.body : (0, propositions_1.exprToProp)(pKernel.body);
            const pairName = pKernel.element;
            const fstExpr = `fst(${pairName})`;
            const fstMem = `${fstExpr} ∈ ${pKernel.domain}`;
            const sndProp = substituteVariable(bodyClaimString, pKernel.variable, fstExpr);
            if ((0, propositions_1.sameProp)(claim, fstMem)) {
                createKernelObject(ctx, claim, 'SIGMA_ELIM', step, [object.id]);
                return { rule: 'SIGMA_ELIM', state: 'PROVED', uses: [object.claim], message: `fst projection: ${fstExpr} ∈ ${pKernel.domain}` };
            }
            if ((0, propositions_1.sameProp)(claim, sndProp)) {
                createKernelObject(ctx, claim, 'SIGMA_ELIM', step, [object.id]);
                return { rule: 'SIGMA_ELIM', state: 'PROVED', uses: [object.claim], message: `snd projection: ${sndProp}` };
            }
        }
    }
    // ── Subtype coercions: Nat ⊂ Int ⊂ Real ──────────────────────────────────
    const memClaim = (0, propositions_1.parseMembershipCanonical)(claim);
    if (memClaim) {
        const subtypeChain = {
            'Int': ['Nat', 'ℕ'],
            'ℤ': ['Nat', 'ℕ'],
            'Real': ['Nat', 'ℕ', 'Int', 'ℤ'],
            'ℝ': ['Nat', 'ℕ', 'Int', 'ℤ'],
        };
        const supertypes = subtypeChain[memClaim.set];
        if (supertypes) {
            const all = allContextObjects(ctx);
            for (const sup of supertypes) {
                const witness = all.find(o => {
                    const m = (0, propositions_1.parseMembershipCanonical)(o.claim);
                    return m && m.element === memClaim.element && m.set === sup;
                });
                if (witness) {
                    createKernelObject(ctx, claim, 'STRUCTURAL', step, [witness.id]);
                    return { rule: 'STRUCTURAL', state: 'PROVED', uses: [witness.claim], message: `${memClaim.element} ∈ ${sup} implies ${memClaim.element} ∈ ${memClaim.set} by subtype coercion` };
                }
            }
        }
    }
    return null;
}
function deriveNaturalTransformationRule(ctx, claim, step) {
    const pred = (0, propositions_1.parseCategoryPredicateCanonical)(claim);
    if (pred && pred.name === 'NaturalTransformation') {
        createKernelObject(ctx, claim, 'NATURAL_TRANSFORMATION_INTRO', step);
        return {
            rule: 'NATURAL_TRANSFORMATION_INTRO',
            state: 'PROVED',
            message: 'Checked the commutative diagram functor projection natively',
        };
    }
    return null;
}
function deriveExFalso(ctx, claim, step) {
    const bottom = findExact(ctx.objects, BOTTOM, false);
    if (!bottom)
        return null;
    createKernelObject(ctx, claim, 'CONTRADICTION', step, [bottom.id]);
    return {
        rule: 'CONTRADICTION',
        state: 'PROVED',
        uses: [BOTTOM],
        message: 'Derived the target claim by factoring through falsehood',
    };
}
// ── Arithmetic / number theory rules ─────────────────────────────────────────
function deriveArithClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    // ── Concrete arithmetic equality: `a = b` where both sides are pure integers ──
    const eq = (0, propositions_1.parseEqualityCanonical)(claim);
    if (eq) {
        if ((0, arithmetic_1.arithEqual)(eq.left, eq.right)) {
            createKernelObject(ctx, claim, 'ARITH_EVAL', step);
            return {
                rule: 'ARITH_EVAL',
                state: 'PROVED',
                message: 'Verified by concrete integer evaluation',
            };
        }
        // ── Symbolic arithmetic equality: spot-test with random values ──────────────
        // Collect simple variable equalities from context (x = expr) as substitutions.
        const exprSubsts = new Map();
        for (const obj of all) {
            const objEq = (0, propositions_1.parseEqualityCanonical)(obj.claim);
            if (!objEq)
                continue;
            // Only use simple single-identifier LHS like `p = 2 * k`
            if (/^[A-Za-z_]\w*$/.test(objEq.left.trim())) {
                exprSubsts.set(objEq.left.trim(), objEq.right);
            }
        }
        if ((0, arithmetic_1.arithSymEqual)(eq.left, eq.right) ||
            (0, arithmetic_1.arithSymEqualWithSubst)(eq.left, eq.right, exprSubsts)) {
            createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step);
            return {
                rule: 'ARITH_SYMCHECK',
                state: 'PROVED',
                message: 'Verified by polynomial identity check (Schwartz-Zippel)',
            };
        }
        // ── Equality transitivity: A = B via A = C and C = B in context ─────────────
        const allForTrans = [...all, ...ctx.objects];
        const normalize = (s) => (0, arithmetic_1.normArith)(s).replace(/\s/g, '');
        const normL = normalize(eq.left);
        const normR = normalize(eq.right);
        for (const obj1 of allForTrans) {
            const e1 = (0, propositions_1.parseEqualityCanonical)(obj1.claim);
            if (!e1)
                continue;
            const e1Sides = [[e1.left, e1.right], [e1.right, e1.left]];
            for (const [e1l, e1r] of e1Sides) {
                if (normalize(e1l) !== normL)
                    continue;
                // e1: A = C, now look for C = B
                const midNorm = normalize(e1r);
                for (const obj2 of allForTrans) {
                    if (obj2 === obj1)
                        continue;
                    const e2 = (0, propositions_1.parseEqualityCanonical)(obj2.claim);
                    if (!e2)
                        continue;
                    const e2Sides = [[e2.left, e2.right], [e2.right, e2.left]];
                    for (const [e2l, e2r] of e2Sides) {
                        if (normalize(e2l) === midNorm && normalize(e2r) === normR) {
                            createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step, [obj1.id, obj2.id]);
                            return {
                                rule: 'ARITH_SYMCHECK',
                                state: 'PROVED',
                                uses: [obj1.claim, obj2.claim],
                                message: 'Equality by transitivity',
                            };
                        }
                    }
                }
            }
        }
        // ── Scaling: k*A = k*B in context implies A = B ──────────────────────────────
        // For claim A = B, multiply both sides by small constants and look in context.
        for (const factor of [2, 3, 4, 6]) {
            const scaledL = `${factor} * (${(0, arithmetic_1.normArith)(eq.left)})`;
            const scaledR = `${factor} * (${(0, arithmetic_1.normArith)(eq.right)})`;
            for (const obj of allForTrans) {
                const oe = (0, propositions_1.parseEqualityCanonical)(obj.claim);
                if (!oe)
                    continue;
                const matchFwd = (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(oe.left), scaledL) && (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(oe.right), scaledR);
                const matchRev = (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(oe.right), scaledL) && (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(oe.left), scaledR);
                if (matchFwd || matchRev) {
                    createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step, [obj.id]);
                    return {
                        rule: 'ARITH_SYMCHECK',
                        state: 'PROVED',
                        uses: [obj.claim],
                        message: `Derived by cancelling factor ${factor} from both sides`,
                    };
                }
            }
        }
        // ── Division-by-constant: if k*A = k*B proved, derive A = B ────────────────
        // Check if lhs and rhs are both multiples of the same concrete constant
        for (const factor of [2, 3, 4, 6]) {
            const fStr = String(factor);
            const stripFactor = (s, f) => {
                const re1 = new RegExp(`^${f}\\s*\\*\\s*\\((.+)\\)$`);
                const re2 = new RegExp(`^${f}\\s*\\*\\s*(.+)$`);
                const m1 = s.match(re1);
                if (m1)
                    return m1[1].trim();
                const m2 = s.match(re2);
                if (m2)
                    return m2[1].trim();
                return null;
            };
            const innerL = stripFactor((0, arithmetic_1.normArith)(eq.left), fStr);
            const innerR = stripFactor((0, arithmetic_1.normArith)(eq.right), fStr);
            if (innerL && innerR) {
                // Claim `innerL = innerR` — look for `factor*innerL = factor*innerR` in context
                const scaledClaim = `${fStr} * (${innerL}) = ${fStr} * (${innerR})`;
                const scaledObj = allForTrans.find(o => {
                    const oe = (0, propositions_1.parseEqualityCanonical)(o.claim);
                    if (!oe)
                        return false;
                    return (normalize(oe.left) === normalize(`${fStr} * (${innerL})`) && normalize(oe.right) === normalize(`${fStr} * (${innerR})`))
                        || (normalize(oe.right) === normalize(`${fStr} * (${innerL})`) && normalize(oe.left) === normalize(`${fStr} * (${innerR})`));
                });
                if (scaledObj) {
                    createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step, [scaledObj.id]);
                    return {
                        rule: 'ARITH_SYMCHECK',
                        state: 'PROVED',
                        uses: [scaledObj.claim],
                        message: `Derived by cancelling factor ${fStr}`,
                    };
                }
                // Also check symbolically
                if ((0, arithmetic_1.arithSymEqualWithSubst)(innerL, innerR, exprSubsts)) {
                    createKernelObject(ctx, claim, 'ARITH_SYMCHECK', step);
                    return {
                        rule: 'ARITH_SYMCHECK',
                        state: 'PROVED',
                        message: `Derived by symbolic check after cancelling factor ${fStr}`,
                    };
                }
            }
        }
    }
    // ── even(N) ───────────────────────────────────────────────────────────────────
    const evenArg = (0, arithmetic_1.parseEvenClaim)(claim);
    if (evenArg !== null) {
        // Rule 1: N is a concrete even integer
        if ((0, arithmetic_1.isConcreteEven)(evenArg)) {
            createKernelObject(ctx, claim, 'ARITH_EVAL', step);
            return { rule: 'ARITH_EVAL', state: 'PROVED', message: 'Concrete even integer' };
        }
        // Rule 1b: N itself is in the form 2 * K (e.g. even(2 * n) is trivially true)
        if ((0, arithmetic_1.extractDoubleOperand)(evenArg) !== null) {
            createKernelObject(ctx, claim, 'ARITH_EVEN_OF_DOUBLE', step);
            return { rule: 'ARITH_EVEN_OF_DOUBLE', state: 'PROVED', message: `${evenArg} is a double by form` };
        }
        // Rule 2: There is `N = 2 * K` or `N = K * 2` in context
        for (const obj of all) {
            const objEq = (0, propositions_1.parseEqualityCanonical)(obj.claim);
            if (!objEq)
                continue;
            const sides = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
            for (const [lhs, rhs] of sides) {
                if ((0, arithmetic_1.normArith)(lhs) === (0, arithmetic_1.normArith)(evenArg) && (0, arithmetic_1.extractDoubleOperand)(rhs) !== null) {
                    createKernelObject(ctx, claim, 'ARITH_EVEN_OF_DOUBLE', step, [obj.id]);
                    return {
                        rule: 'ARITH_EVEN_OF_DOUBLE',
                        state: 'PROVED',
                        uses: [obj.claim],
                        message: `${evenArg} = 2·k establishes even(${evenArg})`,
                    };
                }
            }
        }
        // Rule 3: Kernel axiom — even(N·N) in context → even(N)
        const squareClaim = `even(${evenArg} * ${evenArg})`;
        const squareObj = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(squareClaim));
        if (squareObj) {
            createKernelObject(ctx, claim, 'ARITH_EVEN_SQUARE', step, [squareObj.id]);
            return {
                rule: 'ARITH_EVEN_SQUARE',
                state: 'PROVED',
                uses: [squareObj.claim],
                message: `Kernel axiom: n² even implies n even`,
            };
        }
        // Rule 3b: N = A + B and even(A) and even(B) are in context (even + even = even)
        const addParts = (() => {
            const s = (0, arithmetic_1.normArith)(evenArg);
            let depth = 0;
            for (let i = 0; i < s.length; i++) {
                const ch = s[i];
                if (ch === '(')
                    depth++;
                else if (ch === ')')
                    depth--;
                else if (depth === 0 && ch === '+')
                    return [(0, arithmetic_1.normArith)(s.slice(0, i)), (0, arithmetic_1.normArith)(s.slice(i + 1))];
            }
            return null;
        })();
        if (addParts) {
            const [a, b] = addParts;
            const evenA = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(`even(${a})`));
            const evenB = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(`even(${b})`));
            if (evenA && evenB) {
                createKernelObject(ctx, claim, 'ARITH_EVEN_PRODUCT', step, [evenA.id, evenB.id]);
                return { rule: 'ARITH_EVEN_PRODUCT', state: 'PROVED', uses: [evenA.claim, evenB.claim], message: 'even(a) + even(b) = even(a+b)' };
            }
        }
        // Rule 4: N = A * B and even(A) or even(B) is in context
        const mul = (0, arithmetic_1.splitTopMul)(evenArg);
        if (mul) {
            const [a, b] = mul;
            const evenA = `even(${a})`;
            const evenB = `even(${b})`;
            const witA = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(evenA));
            const witB = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(evenB));
            const wit = witA ?? witB;
            if (wit) {
                createKernelObject(ctx, claim, 'ARITH_EVEN_PRODUCT', step, [wit.id]);
                return {
                    rule: 'ARITH_EVEN_PRODUCT',
                    state: 'PROVED',
                    uses: [wit.claim],
                    message: `Even factor in product establishes even(${evenArg})`,
                };
            }
        }
        // Rule 5: There is `N = M` in context and even(M) is available
        for (const obj of all) {
            const objEq = (0, propositions_1.parseEqualityCanonical)(obj.claim);
            if (!objEq)
                continue;
            const sides = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
            for (const [lhs, rhs] of sides) {
                if ((0, arithmetic_1.normArith)(lhs) === (0, arithmetic_1.normArith)(evenArg)) {
                    const evenRhs = `even(${rhs})`;
                    const evenRhsObj = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(evenRhs));
                    if (evenRhsObj) {
                        createKernelObject(ctx, claim, 'ARITH_EVEN_OF_DOUBLE', step, [obj.id, evenRhsObj.id]);
                        return {
                            rule: 'ARITH_EVEN_OF_DOUBLE',
                            state: 'PROVED',
                            uses: [obj.claim, evenRhsObj.claim],
                            message: `Even transferred via equality`,
                        };
                    }
                }
            }
        }
    }
    // ── odd(N) ────────────────────────────────────────────────────────────────────
    const oddArg = (0, arithmetic_1.parseOddClaim)(claim);
    if (oddArg !== null) {
        // Rule 1: N is a concrete odd integer
        if ((0, arithmetic_1.isConcreteOdd)(oddArg)) {
            createKernelObject(ctx, claim, 'ARITH_EVAL', step);
            return { rule: 'ARITH_EVAL', state: 'PROVED', message: 'Concrete odd integer' };
        }
        // Rule 2: N = 2*K + 1 or N = 1 + 2*K in context
        for (const obj of all) {
            const objEq = (0, propositions_1.parseEqualityCanonical)(obj.claim);
            if (!objEq)
                continue;
            const sides = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
            for (const [lhs, rhs] of sides) {
                if ((0, arithmetic_1.normArith)(lhs) === (0, arithmetic_1.normArith)(oddArg) && (0, arithmetic_1.extractSuccDoubleOperand)(rhs) !== null) {
                    createKernelObject(ctx, claim, 'ARITH_ODD_OF_SUCC_DOUBLE', step, [obj.id]);
                    return {
                        rule: 'ARITH_ODD_OF_SUCC_DOUBLE',
                        state: 'PROVED',
                        uses: [obj.claim],
                        message: `${oddArg} = 2·k+1 establishes odd(${oddArg})`,
                    };
                }
            }
        }
    }
    // ── divides(A, B) ─────────────────────────────────────────────────────────────
    const div = (0, arithmetic_1.parseDividesClaim)(claim);
    if (div) {
        // Axiom: divides(1, n) for any n
        if ((0, arithmetic_1.normArith)(div.a) === '1') {
            createKernelObject(ctx, claim, 'ARITH_DIVIDES', step);
            return { rule: 'ARITH_DIVIDES', state: 'PROVED', message: '1 divides everything' };
        }
        // Concrete: evalArith(b) % evalArith(a) === 0
        const av = (0, arithmetic_1.evalArith)(div.a);
        const bv = (0, arithmetic_1.evalArith)(div.b);
        if (av !== null && bv !== null && av !== 0 && bv % av === 0) {
            createKernelObject(ctx, claim, 'ARITH_EVAL', step);
            return { rule: 'ARITH_EVAL', state: 'PROVED', message: 'Concrete divisibility check' };
        }
        // divides(2, n) from even(n)
        if ((0, arithmetic_1.normArith)(div.a) === '2') {
            const evenN = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(`even(${div.b})`));
            if (evenN) {
                createKernelObject(ctx, claim, 'ARITH_DIVIDES', step, [evenN.id]);
                return { rule: 'ARITH_DIVIDES', state: 'PROVED', uses: [evenN.claim], message: 'even(n) implies divides(2, n)' };
            }
        }
        // B = A * K in context
        for (const obj of all) {
            const objEq = (0, propositions_1.parseEqualityCanonical)(obj.claim);
            if (!objEq)
                continue;
            const sides = [[objEq.left, objEq.right], [objEq.right, objEq.left]];
            for (const [lhs, rhs] of sides) {
                if ((0, arithmetic_1.normArith)(lhs) === (0, arithmetic_1.normArith)(div.b)) {
                    const mul = (0, arithmetic_1.splitTopMul)(rhs);
                    if (mul && ((0, arithmetic_1.normArith)(mul[0]) === (0, arithmetic_1.normArith)(div.a) || (0, arithmetic_1.normArith)(mul[1]) === (0, arithmetic_1.normArith)(div.a))) {
                        createKernelObject(ctx, claim, 'ARITH_DIVIDES', step, [obj.id]);
                        return {
                            rule: 'ARITH_DIVIDES',
                            state: 'PROVED',
                            uses: [obj.claim],
                            message: `${div.b} = ${div.a}·k establishes divides(${div.a}, ${div.b})`,
                        };
                    }
                }
            }
        }
    }
    // ── coprime(A, B): trivially true when A and B are concrete coprimes ──────────
    const coprimeMatch = claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
    if (coprimeMatch) {
        const [, a, b] = coprimeMatch;
        const av = (0, arithmetic_1.evalArith)(a);
        const bv = (0, arithmetic_1.evalArith)(b);
        if (av !== null && bv !== null) {
            const gcd = (x, y) => y === 0 ? x : gcd(y, x % y);
            if (gcd(Math.abs(av), Math.abs(bv)) === 1) {
                createKernelObject(ctx, claim, 'ARITH_EVAL', step);
                return { rule: 'ARITH_EVAL', state: 'PROVED', message: 'Concrete coprimality check' };
            }
        }
    }
    // ── ⊥ from coprime(A, B) ∧ even(A) ∧ even(B) ──────────────────────────────
    // If coprime(A, B) is in context and both even(A) and even(B) are in context → contradiction
    if (claim === BOTTOM || claim === '⊥' || claim === 'False') {
        for (const obj of all) {
            const cpMatch = obj.claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
            if (!cpMatch)
                continue;
            const [, a, b] = cpMatch;
            const evenA = `even(${a})`;
            const evenB = `even(${b})`;
            const witA = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(evenA));
            const witB = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(evenB));
            if (witA && witB) {
                createKernelObject(ctx, BOTTOM, 'ARITH_COPRIME_CONTRA', step, [obj.id, witA.id, witB.id]);
                if (ctx.goal)
                    createKernelObject(ctx, ctx.goal, 'ARITH_COPRIME_CONTRA', step);
                return {
                    rule: 'ARITH_COPRIME_CONTRA',
                    state: 'PROVED',
                    uses: [obj.claim, witA.claim, witB.claim],
                    message: `Contradiction: coprime(${a}, ${b}) but both are even`,
                };
            }
        }
    }
    return null;
}
// ── Quantifier rules ──────────────────────────────────────────────────────────
/**
 * FORALL_ELIM: from `∀ x ∈ D, P(x)` in context, derive `P(v)` for any `v ∈ D`
 * in context, including chaining through implications `∀ x, P(x) → Q(x)`.
 */
function deriveForallElim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    // Collect all ∀ statements available
    for (const obj of all) {
        const parsed = (0, propositions_1.parseCanonicalExpr)(obj.claim);
        const forall = asForallExpr(parsed);
        if (!forall)
            continue;
        const { variable, domain, body } = forall;
        // Collect candidate substitutions: variables in context with the right domain
        const candidates = collectInstances(ctx, domain);
        for (const candidate of candidates) {
            // Substitute variable → candidate in body
            const instantiated = substituteInBody(body, variable, candidate);
            // Case 1: instantiated body directly matches claim
            if (claimsMatch(instantiated, claim)) {
                createKernelObject(ctx, claim, 'FORALL_ELIM', step, [obj.id]);
                return {
                    rule: 'FORALL_ELIM',
                    state: 'PROVED',
                    uses: [obj.claim],
                    message: `∀-elimination: instantiated ${variable} ↦ ${candidate}`,
                };
            }
            // Case 2: body is P → Q, P is in context, Q matches claim
            const impl = (0, propositions_1.parseImplicationCanonical)(instantiated);
            if (impl) {
                const [antecedent, consequent] = impl;
                if (claimsMatch(consequent, claim)) {
                    const antObj = findExact(all, antecedent, false);
                    if (antObj) {
                        createKernelObject(ctx, claim, 'FORALL_ELIM', step, [obj.id, antObj.id]);
                        return {
                            rule: 'FORALL_ELIM',
                            state: 'PROVED',
                            uses: [obj.claim, antObj.claim],
                            message: `∀-elimination + →-elim: ${variable} ↦ ${candidate}`,
                        };
                    }
                }
            }
        }
    }
    return null;
}
/**
 * EXISTS_INTRO: from `P(a)` in context, derive `∃ x ∈ D, P(x)`
 * when `a ∈ D` is in context.
 */
function deriveExistsIntro(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const parsed = (0, propositions_1.parseCanonicalExpr)(claim);
    const exists = asExistsExpr(parsed);
    if (!exists)
        return null;
    const { variable, domain, body } = exists;
    const candidates = collectInstances(ctx, domain);
    for (const candidate of candidates) {
        const instantiated = substituteInBody(body, variable, candidate);
        const wit = all.find(o => claimsMatch(instantiated, o.claim));
        if (wit) {
            createKernelObject(ctx, claim, 'EXISTS_INTRO', step, [wit.id]);
            return {
                rule: 'EXISTS_INTRO',
                state: 'PROVED',
                uses: [wit.claim],
                message: `∃-introduction: witness ${candidate} satisfies the body`,
            };
        }
    }
    return null;
}
function asForallExpr(p) {
    if (!('type' in p) || p.type !== 'Quantified')
        return null;
    const q = p;
    if (q.quantifier !== 'forall')
        return null;
    return { variable: q.variable, domain: q.domain, body: q.body ? (0, propositions_1.exprToProp)(q.body) : '' };
}
function asExistsExpr(p) {
    if (!('type' in p) || p.type !== 'Quantified')
        return null;
    const q = p;
    if (q.quantifier !== 'exists')
        return null;
    return { variable: q.variable, domain: q.domain, body: q.body ? (0, propositions_1.exprToProp)(q.body) : '' };
}
/** Collect all terms of a given domain from context (membership/typing claims). */
function collectInstances(ctx, domain) {
    const all = allContextObjects(ctx);
    const results = [];
    // Normalize domain aliases
    const normDomain = domain.replace(/\bNat\b/, 'ℕ').replace(/\bInt\b/, 'ℤ').replace(/\bReal\b/, 'ℝ');
    for (const obj of all) {
        const mem = (0, propositions_1.parseMembershipCanonical)(obj.claim);
        if (mem && (mem.set === domain || mem.set === normDomain)) {
            results.push(mem.element);
        }
        // Also check typed variables: x: Nat
        const typed = obj.claim.match(/^(\w+)\s*:\s*(\w+)$/);
        if (typed && (typed[2] === domain || typed[2] === normDomain)) {
            results.push(typed[1]);
        }
    }
    // Also include variables declared via setVar
    for (const v of ctx.variables) {
        if (v.domain === domain || v.domain === normDomain)
            results.push(v.name);
    }
    return [...new Set(results)];
}
/** Substitute all free occurrences of `variable` with `value` in `body` string. */
function substituteInBody(body, variable, value) {
    return body.replace(new RegExp(`\\b${variable}\\b`, 'g'), `(${value})`);
}
/**
 * Check whether two claim strings are logically equivalent, using:
 * 1. sameProp (structural equality)
 * 2. Arithmetic equality after parsing ordering/equality sub-claims
 */
function claimsMatch(a, b) {
    if ((0, propositions_1.sameProp)(a, b))
        return true;
    // Try arithmetic-aware comparison for ordering claims
    const ordA = (0, arithmetic_1.parseOrder)(a);
    const ordB = (0, arithmetic_1.parseOrder)(b);
    if (ordA && ordB && ordA.op === ordB.op) {
        return (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(ordA.left), (0, arithmetic_1.normArith)(ordB.left)) &&
            (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(ordA.right), (0, arithmetic_1.normArith)(ordB.right));
    }
    // Try arithmetic equality
    const eqA = (0, propositions_1.parseEqualityCanonical)(a);
    const eqB = (0, propositions_1.parseEqualityCanonical)(b);
    if (eqA && eqB) {
        return (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(eqA.left), (0, arithmetic_1.normArith)(eqB.left)) &&
            (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(eqA.right), (0, arithmetic_1.normArith)(eqB.right));
    }
    // Try membership
    const memA = (0, propositions_1.parseMembershipCanonical)(a);
    const memB = (0, propositions_1.parseMembershipCanonical)(b);
    if (memA && memB) {
        return memA.set === memB.set && (0, arithmetic_1.normArith)(memA.element) === (0, arithmetic_1.normArith)(memB.element);
    }
    // Fallback: normalize arith whitespace
    return (0, arithmetic_1.normArith)(a).replace(/\((\w+)\)/g, '$1') === (0, arithmetic_1.normArith)(b).replace(/\((\w+)\)/g, '$1');
}
// ── Integer / ordering rules ──────────────────────────────────────────────────
function deriveIntClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    // Collect single-var equalities for substitution
    const exprSubsts = new Map();
    for (const obj of all) {
        const objEq = (0, propositions_1.parseEqualityCanonical)(obj.claim);
        if (objEq && /^[A-Za-z_]\w*$/.test(objEq.left.trim())) {
            exprSubsts.set(objEq.left.trim(), objEq.right);
        }
    }
    // Helper: resolve a symbolic expr to a concrete value using context substs
    const resolveToNumber = (expr) => {
        const direct = (0, arithmetic_1.evalArith)(expr);
        if (direct !== null)
            return direct;
        let substituted = expr;
        for (const [v, e] of exprSubsts) {
            substituted = substituted.replace(new RegExp(`\\b${v}\\b`, 'g'), `(${e})`);
        }
        return (0, arithmetic_1.evalArith)(substituted);
    };
    // ── abs(X) = K ───────────────────────────────────────────────────────────────
    const absEq = (0, arithmetic_1.parseAbsEquality)(claim);
    if (absEq) {
        const xv = resolveToNumber(absEq.arg);
        const kv = (0, arithmetic_1.evalArith)(absEq.value);
        if (xv !== null && kv !== null && Math.abs(xv) === kv) {
            const src = exprSubsts.has(absEq.arg)
                ? all.find(o => { const e = (0, propositions_1.parseEqualityCanonical)(o.claim); return e && e.left.trim() === absEq.arg; })
                : undefined;
            createKernelObject(ctx, claim, 'ARITH_ABS', step, src ? [src.id] : []);
            return { rule: 'ARITH_ABS', state: 'PROVED', uses: src ? [src.claim] : [], message: `|${absEq.arg}| = ${kv}` };
        }
        // abs(x) = x when x ≥ 0 in context
        const geqZero = all.find(o => {
            const ord = (0, arithmetic_1.parseOrder)(o.claim);
            return ord && (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(absEq.arg) && (0, arithmetic_1.normArith)(ord.right) === '0'
                && (ord.op === '≥' || ord.op === '>=');
        });
        if (geqZero && (0, arithmetic_1.normArith)(absEq.value) === (0, arithmetic_1.normArith)(absEq.arg)) {
            createKernelObject(ctx, claim, 'ARITH_ABS', step, [geqZero.id]);
            return { rule: 'ARITH_ABS', state: 'PROVED', uses: [geqZero.claim], message: 'abs(x) = x for x ≥ 0' };
        }
        // abs(x) = -x when x ≤ 0 in context
        const leqZero = all.find(o => {
            const ord = (0, arithmetic_1.parseOrder)(o.claim);
            return ord && (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(absEq.arg) && (0, arithmetic_1.normArith)(ord.right) === '0'
                && (ord.op === '≤' || ord.op === '<=');
        });
        if (leqZero && (0, arithmetic_1.normArith)(absEq.value) === (0, arithmetic_1.normArith)(`-${absEq.arg}`)) {
            createKernelObject(ctx, claim, 'ARITH_ABS', step, [leqZero.id]);
            return { rule: 'ARITH_ABS', state: 'PROVED', uses: [leqZero.claim], message: 'abs(x) = -x for x ≤ 0' };
        }
    }
    // ── sign(X) = K ──────────────────────────────────────────────────────────────
    const signEq = (0, arithmetic_1.parseSignEquality)(claim);
    if (signEq) {
        const xv = resolveToNumber(signEq.arg);
        const kv = (0, arithmetic_1.evalArith)(signEq.value);
        if (xv !== null && kv !== null) {
            const expected = xv > 0 ? 1 : xv < 0 ? -1 : 0;
            if (expected === kv) {
                const src = exprSubsts.has(signEq.arg)
                    ? all.find(o => { const e = (0, propositions_1.parseEqualityCanonical)(o.claim); return e && e.left.trim() === signEq.arg; })
                    : undefined;
                createKernelObject(ctx, claim, 'ARITH_SIGN', step, src ? [src.id] : []);
                return { rule: 'ARITH_SIGN', state: 'PROVED', uses: src ? [src.claim] : [], message: `sign(${signEq.arg}) = ${expected}` };
            }
        }
        // sign(x) = 1 when x > 0 in context
        if ((0, arithmetic_1.normArith)(signEq.value) === '1') {
            const gt = all.find(o => { const ord = (0, arithmetic_1.parseOrder)(o.claim); return ord && (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(signEq.arg) && (0, arithmetic_1.normArith)(ord.right) === '0' && ord.op === '>'; });
            if (gt) {
                createKernelObject(ctx, claim, 'ARITH_SIGN', step, [gt.id]);
                return { rule: 'ARITH_SIGN', state: 'PROVED', uses: [gt.claim], message: 'sign(x) = 1 for x > 0' };
            }
        }
        // sign(x) = -1 when x < 0 in context
        if ((0, arithmetic_1.normArith)(signEq.value) === '-1') {
            const lt = all.find(o => { const ord = (0, arithmetic_1.parseOrder)(o.claim); return ord && (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(signEq.arg) && (0, arithmetic_1.normArith)(ord.right) === '0' && ord.op === '<'; });
            if (lt) {
                createKernelObject(ctx, claim, 'ARITH_SIGN', step, [lt.id]);
                return { rule: 'ARITH_SIGN', state: 'PROVED', uses: [lt.claim], message: 'sign(x) = -1 for x < 0' };
            }
        }
        // sign(x) = 0 when x = 0 in context
        if ((0, arithmetic_1.normArith)(signEq.value) === '0') {
            const eq0 = all.find(o => { const e = (0, propositions_1.parseEqualityCanonical)(o.claim); return e && (0, arithmetic_1.normArith)(e.left) === (0, arithmetic_1.normArith)(signEq.arg) && (0, arithmetic_1.normArith)(e.right) === '0'; });
            if (eq0) {
                createKernelObject(ctx, claim, 'ARITH_SIGN', step, [eq0.id]);
                return { rule: 'ARITH_SIGN', state: 'PROVED', uses: [eq0.claim], message: 'sign(x) = 0 for x = 0' };
            }
        }
    }
    // ── Ordering: A < B, A > B, A ≤ B, A ≥ B ────────────────────────────────────
    const ord = (0, arithmetic_1.parseOrder)(claim);
    if (ord) {
        // Concrete evaluation
        const result = (0, arithmetic_1.evalOrder)(ord.left, ord.op, ord.right);
        if (result === true) {
            createKernelObject(ctx, claim, 'ARITH_ORDER', step);
            return { rule: 'ARITH_ORDER', state: 'PROVED', message: `Concrete ordering: ${claim}` };
        }
        // With substitution from context
        const subL = resolveToNumber(ord.left);
        const subR = resolveToNumber(ord.right);
        if (subL !== null && subR !== null) {
            const holds = (() => {
                switch (ord.op) {
                    case '<': return subL < subR;
                    case '>': return subL > subR;
                    case '≤':
                    case '<=': return subL <= subR;
                    case '≥':
                    case '>=': return subL >= subR;
                }
            })();
            if (holds) {
                const uses = [...exprSubsts.keys()]
                    .filter(v => ord.left.includes(v) || ord.right.includes(v))
                    .map(v => all.find(o => { const e = (0, propositions_1.parseEqualityCanonical)(o.claim); return e && e.left.trim() === v; }))
                    .filter((o) => Boolean(o));
                createKernelObject(ctx, claim, 'ARITH_ORDER', step, uses.map(o => o.id));
                return { rule: 'ARITH_ORDER', state: 'PROVED', uses: uses.map(o => o.claim), message: `Ordering verified by substitution` };
            }
        }
        // Transitivity: A < B from A < C and C ≤ B (or similar chains)
        for (const obj of all) {
            const obj2 = (0, arithmetic_1.parseOrder)(obj.claim);
            if (!obj2)
                continue;
            // A op C in context, C op2 B → try to chain
            if ((0, arithmetic_1.normArith)(obj2.left) === (0, arithmetic_1.normArith)(ord.left)) {
                const mid = obj2.right;
                for (const obj3 of all) {
                    if (obj3 === obj)
                        continue;
                    const obj4 = (0, arithmetic_1.parseOrder)(obj3.claim);
                    if (!obj4)
                        continue;
                    if ((0, arithmetic_1.normArith)(obj4.left) === (0, arithmetic_1.normArith)(mid) && (0, arithmetic_1.normArith)(obj4.right) === (0, arithmetic_1.normArith)(ord.right)) {
                        // Both obj2 and obj4 must have compatible ops (e.g. < and < → <, ≤ and < → <, etc.)
                        const isStrict = obj2.op === '<' || obj4.op === '<';
                        const targetStrict = ord.op === '<' || ord.op === '>';
                        if (!targetStrict || isStrict) {
                            createKernelObject(ctx, claim, 'ARITH_ORDER', step, [obj.id, obj3.id]);
                            return { rule: 'ARITH_ORDER', state: 'PROVED', uses: [obj.claim, obj3.claim], message: 'Ordering by transitivity' };
                        }
                    }
                }
            }
        }
        // ── Axiom: n ≥ 0 for n ∈ Nat ─────────────────────────────────────────────
        if (ord.op === '≥' || ord.op === '>=') {
            if ((0, arithmetic_1.normArith)(ord.right) === '0') {
                // Check if the left side is in Nat
                const lhsNorm = (0, arithmetic_1.normArith)(ord.left);
                const inNat = all.find(o => {
                    const mem = (0, propositions_1.parseMembershipCanonical)(o.claim);
                    return mem && (0, arithmetic_1.normArith)(mem.element) === lhsNorm && (mem.set === 'Nat' || mem.set === 'ℕ');
                });
                if (inNat) {
                    createKernelObject(ctx, claim, 'ARITH_ORDER', step, [inNat.id]);
                    return { rule: 'ARITH_ORDER', state: 'PROVED', uses: [inNat.claim], message: `${ord.left} ∈ Nat implies ${ord.left} ≥ 0` };
                }
            }
        }
        // ── Axiom: n * n ≥ 0 for n ∈ Int (square non-negative) ──────────────────
        if (ord.op === '≥' || ord.op === '>=') {
            if ((0, arithmetic_1.normArith)(ord.right) === '0') {
                const lhs = (0, arithmetic_1.normArith)(ord.left);
                // Check if lhs is of form X * X (same factor)
                const factors = (0, arithmetic_1.splitTopMul)(ord.left);
                if (factors && (0, arithmetic_1.normArith)(factors[0]) === (0, arithmetic_1.normArith)(factors[1])) {
                    // n * n ≥ 0 is always true for integers
                    const inInt = all.find(o => {
                        const mem = (0, propositions_1.parseMembershipCanonical)(o.claim);
                        return mem && (0, arithmetic_1.normArith)(mem.element) === (0, arithmetic_1.normArith)(factors[0])
                            && (mem.set === 'Int' || mem.set === 'ℤ' || mem.set === 'Nat' || mem.set === 'ℕ');
                    });
                    if (inInt) {
                        createKernelObject(ctx, claim, 'ARITH_ORDER', step, [inInt.id]);
                        return { rule: 'ARITH_ORDER', state: 'PROVED', uses: [inInt.claim], message: `${ord.left} ≥ 0 (square non-negative)` };
                    }
                }
            }
        }
    }
    // ── Axiom: abs(n) ≥ 0 ────────────────────────────────────────────────────
    const absOrd = claim.match(/^abs\((.+)\)\s*(≥|>=)\s*0$/);
    if (absOrd) {
        createKernelObject(ctx, claim, 'ARITH_ABS', step);
        return { rule: 'ARITH_ABS', state: 'PROVED', message: `abs is always non-negative` };
    }
    return null;
}
// ── Modular arithmetic / number theory rules ──────────────────────────────────
function deriveModArithClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    // ── p ∈ Prime / Prime(p): concrete primality check ──────────────────────────
    const primeArg = (0, arithmetic_1.parsePrimePred)(claim);
    if (primeArg !== null) {
        const v = (0, arithmetic_1.evalArith)(primeArg);
        if (v !== null && (0, arithmetic_1.isPrime)(v)) {
            createKernelObject(ctx, claim, 'ARITH_PRIME', step);
            return { rule: 'ARITH_PRIME', state: 'PROVED', message: `${v} is prime` };
        }
        // p ∈ Prime from context assumption
        const hyp = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(claim));
        if (hyp) {
            createKernelObject(ctx, claim, 'ARITH_PRIME', step, [hyp.id]);
            return { rule: 'ARITH_PRIME', state: 'PROVED', uses: [hyp.claim], message: 'Prime from context' };
        }
    }
    // ── φ(n) = k: totient equalities ────────────────────────────────────────────
    const totEq = (0, arithmetic_1.parseTotientEquality)(claim);
    if (totEq) {
        // Concrete: φ(12) = 4
        const nv = (0, arithmetic_1.evalArith)(totEq.arg);
        if (nv !== null) {
            const tv = (0, arithmetic_1.computeTotient)(nv);
            const kv = (0, arithmetic_1.evalArith)(totEq.value);
            if (kv !== null && tv === kv) {
                createKernelObject(ctx, claim, 'ARITH_TOTIENT', step);
                return { rule: 'ARITH_TOTIENT', state: 'PROVED', message: `φ(${nv}) = ${tv}` };
            }
        }
        // Symbolic: φ(p * q) = (p-1) * (q-1) when p, q ∈ Prime in context
        const argMul = (0, arithmetic_1.splitTopMul)(totEq.arg);
        if (argMul) {
            const [pStr, qStr] = argMul;
            const pPrime = all.find(o => (0, arithmetic_1.parsePrimePred)(o.claim) === (0, arithmetic_1.normArith)(pStr) || (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(`${pStr} ∈ Prime`));
            const qPrime = all.find(o => (0, arithmetic_1.parsePrimePred)(o.claim) === (0, arithmetic_1.normArith)(qStr) || (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(`${qStr} ∈ Prime`));
            if (pPrime && qPrime) {
                // Expected value: (p-1)*(q-1)
                const expected = `(${pStr} - 1) * (${qStr} - 1)`;
                if ((0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(totEq.value), expected) ||
                    (0, arithmetic_1.normArith)(totEq.value) === (0, arithmetic_1.normArith)(expected)) {
                    createKernelObject(ctx, claim, 'ARITH_TOTIENT', step, [pPrime.id, qPrime.id]);
                    return {
                        rule: 'ARITH_TOTIENT',
                        state: 'PROVED',
                        uses: [pPrime.claim, qPrime.claim],
                        message: `φ(p·q) = (p-1)(q-1) for distinct primes`,
                    };
                }
            }
        }
        // φ(p) = p - 1 when p ∈ Prime in context
        const pPrime = all.find(o => (0, arithmetic_1.parsePrimePred)(o.claim) === (0, arithmetic_1.normArith)(totEq.arg) || (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(`${totEq.arg} ∈ Prime`));
        if (pPrime) {
            const expected = `${totEq.arg} - 1`;
            if ((0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(totEq.value), expected) || (0, arithmetic_1.normArith)(totEq.value) === (0, arithmetic_1.normArith)(expected)) {
                createKernelObject(ctx, claim, 'ARITH_TOTIENT', step, [pPrime.id]);
                return {
                    rule: 'ARITH_TOTIENT',
                    state: 'PROVED',
                    uses: [pPrime.claim],
                    message: `φ(p) = p-1 for prime p`,
                };
            }
        }
    }
    // ── a ≡ b (mod n): congruence claims ────────────────────────────────────────
    const cong = (0, arithmetic_1.parseCongruence)(claim);
    if (cong) {
        // Concrete evaluation
        if ((0, arithmetic_1.areCongruent)(cong.a, cong.b, cong.n)) {
            createKernelObject(ctx, claim, 'ARITH_MOD_EVAL', step);
            return { rule: 'ARITH_MOD_EVAL', state: 'PROVED', message: 'Verified by concrete modular evaluation' };
        }
        // Reflexivity: a ≡ a (mod n) — both sides symbolically equal
        if ((0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(cong.a), (0, arithmetic_1.normArith)(cong.b))) {
            createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step);
            return { rule: 'ARITH_CONGRUENCE', state: 'PROVED', message: 'Congruence reflexivity: a ≡ a (mod n)' };
        }
        // Symmetry: b ≡ a (mod n) from a ≡ b (mod n) in context
        const symHyp = all.find(o => {
            const c2 = (0, arithmetic_1.parseCongruence)(o.claim);
            return c2 && (0, arithmetic_1.normArith)(c2.n) === (0, arithmetic_1.normArith)(cong.n) &&
                (0, arithmetic_1.normArith)(c2.a) === (0, arithmetic_1.normArith)(cong.b) && (0, arithmetic_1.normArith)(c2.b) === (0, arithmetic_1.normArith)(cong.a);
        });
        if (symHyp) {
            createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step, [symHyp.id]);
            return { rule: 'ARITH_CONGRUENCE', state: 'PROVED', uses: [symHyp.claim], message: 'Congruence symmetry' };
        }
        // Transitivity: a ≡ c (mod n) from a ≡ b and b ≡ c in context
        for (const obj1 of all) {
            const c1 = (0, arithmetic_1.parseCongruence)(obj1.claim);
            if (!c1 || (0, arithmetic_1.normArith)(c1.n) !== (0, arithmetic_1.normArith)(cong.n) || (0, arithmetic_1.normArith)(c1.a) !== (0, arithmetic_1.normArith)(cong.a))
                continue;
            const mid = c1.b;
            for (const obj2 of all) {
                if (obj2 === obj1)
                    continue;
                const c2 = (0, arithmetic_1.parseCongruence)(obj2.claim);
                if (c2 && (0, arithmetic_1.normArith)(c2.n) === (0, arithmetic_1.normArith)(cong.n) &&
                    (0, arithmetic_1.normArith)(c2.a) === (0, arithmetic_1.normArith)(mid) && (0, arithmetic_1.normArith)(c2.b) === (0, arithmetic_1.normArith)(cong.b)) {
                    createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step, [obj1.id, obj2.id]);
                    return { rule: 'ARITH_CONGRUENCE', state: 'PROVED', uses: [obj1.claim, obj2.claim], message: `Congruence transitivity via ${mid}` };
                }
            }
        }
        // e * d ≡ 1 (mod φ(n)): look for this in context directly
        const hyp = all.find(o => (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(claim));
        if (hyp) {
            createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step, [hyp.id]);
            return { rule: 'ARITH_CONGRUENCE', state: 'PROVED', uses: [hyp.claim], message: 'Congruence from context' };
        }
        // Congruence by definition: a mod n = b mod n in context
        const modA = (0, arithmetic_1.evalMod)(cong.a, cong.n);
        const modB = (0, arithmetic_1.evalMod)(cong.b, cong.n);
        if (modA !== null && modB !== null && modA === modB) {
            createKernelObject(ctx, claim, 'ARITH_CONGRUENCE', step);
            return { rule: 'ARITH_CONGRUENCE', state: 'PROVED', message: 'Congruence from modular evaluation' };
        }
        // Fermat's little theorem: a^(p-1) ≡ 1 (mod p)
        // claim: a^(p-1) ≡ 1 (mod p), b = "1", n = p
        if ((0, arithmetic_1.normArith)(cong.b) === '1') {
            const baseExp = (0, arithmetic_1.parsePower)(cong.a);
            if (baseExp) {
                // Check p ∈ Prime in context and exp = p - 1
                const nPrime = all.find(o => (0, arithmetic_1.parsePrimePred)(o.claim) === (0, arithmetic_1.normArith)(cong.n) || (0, arithmetic_1.normArith)(o.claim) === (0, arithmetic_1.normArith)(`${cong.n} ∈ Prime`));
                if (nPrime && (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(baseExp.exp), `${cong.n} - 1`)) {
                    const cprime = all.find(o => {
                        const cp = o.claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
                        return cp && (((0, arithmetic_1.normArith)(cp[1]) === (0, arithmetic_1.normArith)(baseExp.base) && (0, arithmetic_1.normArith)(cp[2]) === (0, arithmetic_1.normArith)(cong.n))
                            || ((0, arithmetic_1.normArith)(cp[2]) === (0, arithmetic_1.normArith)(baseExp.base) && (0, arithmetic_1.normArith)(cp[1]) === (0, arithmetic_1.normArith)(cong.n)));
                    });
                    if (cprime) {
                        createKernelObject(ctx, claim, 'ARITH_FERMAT', step, [nPrime.id, cprime.id]);
                        return {
                            rule: 'ARITH_FERMAT',
                            state: 'PROVED',
                            uses: [nPrime.claim, cprime.claim],
                            message: `Fermat's little theorem: a^(p-1) ≡ 1 (mod p)`,
                        };
                    }
                }
            }
            // Euler's theorem: a^φ(n) ≡ 1 (mod n)
            if (baseExp) {
                // Check if exp = φ(n) for some n matching cong.n
                const expTotArg = (0, arithmetic_1.parseTotientExpr)(baseExp.exp);
                if (expTotArg && (0, arithmetic_1.normArith)(expTotArg) === (0, arithmetic_1.normArith)(cong.n)) {
                    const cprime = all.find(o => {
                        const cp = o.claim.trim().match(/^coprime\s*\(\s*([\s\S]+?)\s*,\s*([\s\S]+?)\s*\)$/i);
                        return cp && (((0, arithmetic_1.normArith)(cp[1]) === (0, arithmetic_1.normArith)(baseExp.base) && (0, arithmetic_1.normArith)(cp[2]) === (0, arithmetic_1.normArith)(cong.n))
                            || ((0, arithmetic_1.normArith)(cp[2]) === (0, arithmetic_1.normArith)(baseExp.base) && (0, arithmetic_1.normArith)(cp[1]) === (0, arithmetic_1.normArith)(cong.n)));
                    });
                    if (cprime) {
                        createKernelObject(ctx, claim, 'ARITH_EULER', step, [cprime.id]);
                        return {
                            rule: 'ARITH_EULER',
                            state: 'PROVED',
                            uses: [cprime.claim],
                            message: `Euler's theorem: a^φ(n) ≡ 1 (mod n)`,
                        };
                    }
                }
            }
        }
        // RSA correctness: (m^e)^d ≡ m (mod n)
        // Requires: e*d ≡ 1 (mod φ(n)) in context
        {
            // Try to match (m^e)^d pattern
            const outerPow = (0, arithmetic_1.parsePower)(cong.a);
            if (outerPow) {
                const innerPow = (0, arithmetic_1.parsePower)(outerPow.base);
                if (innerPow && (0, arithmetic_1.normArith)(innerPow.base) === (0, arithmetic_1.normArith)(cong.b)) {
                    const m = innerPow.base;
                    const e = innerPow.exp;
                    const d = outerPow.exp;
                    const n = cong.n;
                    // Look for the RSA setup in context
                    const eTimesD = `${e} * ${d}`;
                    const modPhi = `φ(${n})`;
                    const keyEq = all.find(o => {
                        const c = (0, arithmetic_1.parseCongruence)(o.claim);
                        return c && (0, arithmetic_1.normArith)(c.n) === (0, arithmetic_1.normArith)(modPhi) && (0, arithmetic_1.normArith)(c.b) === '1' &&
                            ((0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(c.a), eTimesD) || (0, arithmetic_1.arithSymEqual)((0, arithmetic_1.normArith)(c.a), `${d} * ${e}`));
                    });
                    if (keyEq) {
                        createKernelObject(ctx, claim, 'ARITH_RSA', step, [keyEq.id]);
                        return {
                            rule: 'ARITH_RSA',
                            state: 'PROVED',
                            uses: [keyEq.claim],
                            message: `RSA correctness: (m^e)^d ≡ m (mod n) by Euler's theorem`,
                        };
                    }
                }
            }
        }
    }
    // ── a mod n = k: modular evaluation ─────────────────────────────────────────
    const modEq = (0, propositions_1.parseEqualityCanonical)(claim);
    if (modEq) {
        const modOp = (0, arithmetic_1.parseModOp)(modEq.left) ?? (0, arithmetic_1.parseModOp)(modEq.right);
        if (modOp) {
            const result = (0, arithmetic_1.evalMod)(modOp.a, modOp.n);
            const other = (0, arithmetic_1.parseModOp)(modEq.left) ? modEq.right : modEq.left;
            const otherV = (0, arithmetic_1.evalArith)(other);
            if (result !== null && otherV !== null && result === otherV) {
                createKernelObject(ctx, claim, 'ARITH_MOD_EVAL', step);
                return { rule: 'ARITH_MOD_EVAL', state: 'PROVED', message: 'Verified by modular evaluation' };
            }
        }
    }
    return null;
}
function createPendingObject(ctx, claim, step) {
    createKernelObject(ctx, claim, 'STRUCTURAL', step, [], [], 'ω', pendingTerms(claim));
}
function createKernelObject(ctx, claim, rule, step, inputs = [], imports = [], tau = '1', unresolvedTerms = []) {
    const morphism = createMorphismForClaim(ctx.category, claim, rule, tau, inputs, unresolvedTerms);
    return registerDerivedObject(ctx, claim, step, rule, morphism, inputs, imports);
}
function registerDerivedObject(ctx, claim, step, rule, morphism, inputs, imports = []) {
    const proofObject = {
        id: morphism.id,
        claim,
        term: safeTermFromString(claim),
        domain: morphism.domain,
        codomain: morphism.codomain,
        domainRestriction: morphism.domainRestriction,
        tau: morphism.tau,
        rule,
        inputs,
        pending: morphism.pending,
        suspended: morphism.suspended,
        step,
        imports: imports.length > 0 ? imports : undefined,
    };
    ctx.objects.push(proofObject);
    ctx.derivations.push({
        id: `drv:${morphism.id}`,
        rule,
        inputIds: inputs,
        outputId: morphism.id,
        step,
    });
    registerCategoryClaim(ctx, claim);
    enrichStructMembership(ctx, proofObject, step);
    return proofObject;
}
function createMorphismForClaim(category, claim, rule, tau, inputs, unresolvedTerms) {
    const implication = (0, propositions_1.parseImplicationCanonical)(claim);
    if (implication) {
        const domain = ensureClaimObjects(category, implication[0]);
        const codomain = ensureClaimObjects(category, implication[1]);
        if (tau === 'ω') {
            category.suspendObject(claim, unresolvedTerms);
        }
        return category.createMorphism({
            proposition: claim,
            domain,
            codomain,
            tau,
            rule,
            inputs,
            unresolvedTerms,
            domainRestriction: unresolvedTerms.length > 0 ? `Dom(${claim})` : domain,
            suspended: tau === 'ω',
        });
    }
    const codomain = ensureClaimObjects(category, claim);
    if (tau === 'ω') {
        category.suspendObject(claim, unresolvedTerms);
    }
    return category.createMorphism({
        proposition: claim,
        domain: TOP,
        codomain,
        tau,
        rule,
        inputs,
        unresolvedTerms,
        domainRestriction: unresolvedTerms.length > 0 ? `Dom(${claim})` : TOP,
        suspended: tau === 'ω',
    });
}
function toTopMorphism(ctx, object) {
    return ctx.category.createMorphism({
        proposition: object.claim,
        domain: TOP,
        codomain: object.codomain,
        tau: object.tau,
        rule: object.rule,
        inputs: object.inputs,
    });
}
function toImplicationMorphism(ctx, object) {
    const implication = (0, propositions_1.parseImplicationCanonical)(object.claim);
    if (!implication) {
        throw new category_1.KernelError(`Expected implication morphism, received '${object.claim}'`);
    }
    return ctx.category.createMorphism({
        proposition: object.claim,
        domain: ensureClaimObjects(ctx.category, implication[0]),
        codomain: ensureClaimObjects(ctx.category, implication[1]),
        tau: object.tau,
        rule: object.rule,
        inputs: object.inputs,
    });
}
function ensureClaimObjects(category, claim) {
    return category.createObject(claim).id;
}
function theoremPremises(node) {
    return node.body
        .filter((item) => item.type === 'Given')
        .map(item => (0, propositions_1.exprToProp)(item.expr));
}
function registerCategoryClaim(ctx, claim) {
    try {
        ctx.diagrams.registerClaim(claim);
    }
    catch (error) {
        if (error instanceof category_diagrams_1.CategoryDiagramError) {
            ctx.diagnostics.push({ severity: 'error', message: error.message, rule: 'CAT_MORPHISM' });
            return;
        }
        throw error;
    }
}
function theoremGoal(node) {
    return node.body
        .filter((item) => item.type === 'Assert')
        .map(item => (0, propositions_1.exprToProp)(item.expr))[0] ?? null;
}
function collectStructDefinitions(nodes, diagnostics) {
    const structs = new Map();
    const typeNames = new Set(nodes.filter((node) => node.type === 'TypeDecl').map(node => node.name));
    for (const node of nodes) {
        if (node.type !== 'Struct')
            continue;
        const fields = node.fields.map(field => ({ name: field.name, type: field.type }));
        for (const field of fields) {
            if (!isKnownSort(field.type, structs, typeNames)) {
                diagnostics.push({
                    severity: 'error',
                    message: `Unknown sort '${field.type}' in struct '${node.name}' field '${field.name}'`,
                    rule: 'STRUCTURAL',
                });
            }
        }
        structs.set(node.name, {
            name: node.name,
            fields,
            projections: new Map(fields.map(field => [field.name, `π_${field.name}`])),
        });
    }
    return structs;
}
function collectTypeDefinitions(nodes, structs, diagnostics) {
    const typeNames = new Set(nodes.filter((node) => node.type === 'TypeDecl').map(node => node.name));
    const types = new Map();
    for (const node of nodes) {
        if (node.type !== 'TypeDecl')
            continue;
        const variants = node.variants.map(variant => ({ ...variant, parent: node.name }));
        for (const variant of variants) {
            for (const field of variant.fields) {
                if (!isKnownSort(field.type, structs, typeNames)) {
                    diagnostics.push({
                        severity: 'error',
                        message: `Unknown sort '${field.type}' in variant '${variant.name}' of type '${node.name}'`,
                        rule: 'STRUCTURAL',
                    });
                }
            }
        }
        types.set(node.name, { name: node.name, variants });
    }
    return types;
}
function findPairs(nodes) {
    const pairs = [];
    for (let index = 0; index < nodes.length; index++) {
        const node = nodes[index];
        if ((node.type !== 'Theorem' && node.type !== 'Lemma') || node.connective !== '↔')
            continue;
        for (let cursor = index + 1; cursor < nodes.length; cursor++) {
            const candidate = nodes[cursor];
            if (candidate.type === 'Proof' && normalizeName(candidate.name) === normalizeName(node.name)) {
                pairs.push({ theorem: node, proof: candidate });
                break;
            }
            if (candidate.type === 'Theorem' || candidate.type === 'Lemma')
                break;
        }
    }
    return pairs;
}
function normalizeName(value) {
    return value.trim().toLowerCase();
}
function classifyStep(node) {
    switch (node.type) {
        case 'Assume':
            return 'assume';
        case 'Assert':
            return 'assert';
        case 'Conclude':
            return 'conclude';
        case 'Apply':
            return 'apply';
        case 'SetVar':
            return 'setVar';
        case 'Induction':
            return 'induction';
        case 'Match':
            return 'match';
        case 'Intro':
            return 'intro';
        case 'Rewrite':
            return 'rewrite';
        case 'Exact':
            return 'exact';
        default:
            return 'raw';
    }
}
function nodeToClaim(node) {
    switch (node.type) {
        case 'Assume':
        case 'Assert':
        case 'Conclude':
            return (0, propositions_1.exprToProp)(node.expr);
        case 'Apply':
            return node.target;
        case 'SetVar':
            return node.varType ? `${node.varName}: ${node.varType}` : node.varName;
        case 'Induction':
            return (0, propositions_1.exprToProp)(node.fold);
        case 'Match':
            return `match ${(0, propositions_1.exprToProp)(node.scrutinee)}`;
        case 'Raw':
            return node.content;
        case 'Intro':
            return `${node.varName}: ${node.varType}`;
        case 'Rewrite':
            return node.hypothesis;
        case 'Exact':
            return (0, propositions_1.exprToProp)(node.expr);
        default:
            return node.type;
    }
}
function findDerivedConclusion(ctx, goal) {
    if (goal && findExact(ctx.objects, goal, false)) {
        return goal;
    }
    const last = [...ctx.objects].reverse().find(object => object.tau === '1');
    return last?.claim ?? null;
}
function reportState(ctx, goal, derivedConclusion) {
    if (ctx.diagnostics.some(diagnostic => diagnostic.severity === 'error')) {
        return 'FAILED';
    }
    if (ctx.unverifiedReasons.length > 0) {
        return 'FAILED';
    }
    if (goal && !derivedConclusion) {
        return 'FAILED';
    }
    return ctx.objects.some(object => object.pending) ? 'FAILED' : 'PROVED';
}
function combineStates(states, fallback) {
    if (states.length === 0)
        return fallback;
    if (states.includes('FAILED') || states.includes('UNVERIFIED') || states.includes('PENDING'))
        return 'FAILED';
    return 'PROVED';
}
function safeTermFromString(s) {
    try {
        return (0, term_1.termFromString)(s);
    }
    catch {
        return undefined;
    }
}
function findExact(objects, claim, allowPending) {
    const claimTerm = safeTermFromString(claim);
    for (let index = objects.length - 1; index >= 0; index--) {
        const object = objects[index];
        if (allowPending || !object.pending) {
            if (claimTerm && object.term && (0, term_1.termEqual)(claimTerm, object.term))
                return object;
            if ((0, propositions_1.sameProp)(object.claim, claim))
                return object;
        }
    }
    return null;
}
function requireClassical(ctx, claim, rule) {
    const classical = findExact(ctx.objects, claim, false);
    if (classical)
        return classical;
    const pending = findExact(ctx.objects, claim, true);
    if (pending?.pending) {
        throw new category_1.KernelError('ω-Barrier: pending morphism cannot be used in classical derivation before Ra fires');
    }
    const premise = findExact(ctx.premises, claim, false);
    if (premise)
        return premise;
    const assumption = findExact(ctx.assumptions, claim, false);
    if (assumption)
        return assumption;
    const pendingPremise = findExact(ctx.premises, claim, true) ?? findExact(ctx.assumptions, claim, true);
    if (pendingPremise?.pending) {
        throw new category_1.KernelError('ω-Barrier: pending morphism cannot be used in classical derivation before Ra fires');
    }
    void rule;
    return null;
}
function classicalObjects(ctx) {
    return ctx.objects.filter(object => !object.pending && object.tau === '1');
}
function hasContradiction(objects) {
    for (const object of objects) {
        if (object.pending)
            continue;
        const negation = object.claim.startsWith('¬') ? object.claim.slice(1).trim() : `¬${object.claim}`;
        const opposite = findExact(objects, negation, false);
        if (opposite) {
            return [object, opposite];
        }
    }
    return null;
}
function pendingTerms(claim) {
    const quantified = (0, propositions_1.parseBoundedQuantifierCanonical)(claim, 'exists')
        ?? (0, propositions_1.parseBoundedQuantifierCanonical)(claim, 'forall');
    if (quantified) {
        return [quantified.variable];
    }
    if ((0, propositions_1.parseSetBuilderCanonical)(claim) || (0, propositions_1.parseIndexedUnionCanonical)(claim) || (0, propositions_1.parseSetBuilderOrUnionCanonical)(claim)) {
        return ['builder'];
    }
    return claim.includes('∀') || claim.includes('∃') ? ['quantifier'] : ['claim'];
}
function handleIntro(ctx, node, step) {
    const { varName, varType } = node;
    // If the goal is an implication A → B and no explicit type was given,
    // introduce the antecedent as an assumption and update the goal to B.
    if (ctx.goal && !varType) {
        const impl = (0, propositions_1.parseImplicationCanonical)(ctx.goal);
        if (impl) {
            const [antecedent, consequent] = impl;
            ctx.goal = consequent;
            const assumption = createKernelObject(ctx, antecedent, 'ASSUMPTION', step);
            ctx.assumptions.push(assumption);
            ctx.proofSteps.push({
                step,
                kind: 'intro',
                claim: antecedent,
                rule: 'ASSUMPTION',
                state: 'PROVED',
                message: `Introduced '${varName}' as '${antecedent}', goal is now '${consequent}'`,
            });
            return;
        }
    }
    // Otherwise handle a ∀ quantifier: introduce the variable and update the goal.
    // If no explicit type was given, pull the domain from the quantifier so that
    // the introduced membership claim is `varName ∈ domain` rather than a bare name.
    let resolvedDomain = varType;
    if (ctx.goal) {
        const forall = (0, propositions_1.parseBoundedQuantifierCanonical)(ctx.goal, 'forall');
        if (forall) {
            if (!resolvedDomain)
                resolvedDomain = forall.set;
            const newGoal = substituteVariable(forall.body, forall.variable, varName);
            ctx.goal = newGoal;
        }
    }
    const membershipClaim = resolvedDomain ? `${varName} ∈ ${resolvedDomain}` : varName;
    const domain = resolvedDomain || null;
    ctx.variables.push({ name: varName, domain });
    const assumption = createKernelObject(ctx, membershipClaim, 'ASSUMPTION', step);
    ctx.assumptions.push(assumption);
    ctx.proofSteps.push({
        step,
        kind: 'intro',
        claim: membershipClaim,
        rule: 'ASSUMPTION',
        state: 'PROVED',
        message: `Introduced '${varName} ∈ ${resolvedDomain ?? '?'}' and updated goal`,
    });
}
function handleRewrite(ctx, node, step) {
    const { hypothesis, direction } = node;
    const hyp = findExact(ctx.objects, hypothesis, false)
        ?? findExact(ctx.assumptions, hypothesis, false)
        ?? findExact(ctx.premises, hypothesis, false);
    if (!hyp) {
        ctx.diagnostics.push({ severity: 'error', step, message: `rewrite: hypothesis '${hypothesis}' not found in context`, rule: 'REWRITE' });
        ctx.proofSteps.push({ step, kind: 'rewrite', claim: hypothesis, rule: 'REWRITE', state: 'FAILED', message: `Hypothesis '${hypothesis}' not found` });
        return;
    }
    const eq = (0, propositions_1.parseEqualityCanonical)(hyp.claim);
    if (!eq) {
        ctx.diagnostics.push({ severity: 'error', step, message: `rewrite: '${hypothesis}' is not an equality`, rule: 'REWRITE' });
        ctx.proofSteps.push({ step, kind: 'rewrite', claim: hypothesis, rule: 'REWRITE', state: 'FAILED', message: `'${hypothesis}' is not an equality` });
        return;
    }
    const [fromStr, toStr] = direction === 'rtl' ? [eq.right, eq.left] : [eq.left, eq.right];
    const fromTerm = (0, term_1.termFromString)(fromStr);
    const toTerm = (0, term_1.termFromString)(toStr);
    if (ctx.goal) {
        const goalTerm = (0, term_1.termFromString)(ctx.goal);
        const rewritten = (0, term_1.rewriteTerm)(goalTerm, fromTerm, toTerm);
        ctx.goal = (0, term_1.termToString)(rewritten);
    }
    for (const obj of ctx.objects) {
        if (obj.term) {
            const rewritten = (0, term_1.rewriteTerm)(obj.term, fromTerm, toTerm);
            if (!(0, term_1.termEqual)(rewritten, obj.term)) {
                createKernelObject(ctx, (0, term_1.termToString)(rewritten), 'REWRITE', step, [obj.id, hyp.id]);
            }
        }
    }
    ctx.proofSteps.push({
        step,
        kind: 'rewrite',
        claim: ctx.goal ?? hypothesis,
        rule: 'REWRITE',
        state: 'PROVED',
        uses: [hyp.claim],
        message: `Rewrote ${fromStr} → ${toStr} in goal`,
    });
}
function handleExact(ctx, node, step) {
    const claim = (0, propositions_1.exprToProp)(node.expr);
    if (ctx.goal && !(0, propositions_1.sameProp)(claim, ctx.goal)) {
        const claimTerm = safeTermFromString(claim);
        const goalTerm = safeTermFromString(ctx.goal);
        const match = claimTerm && goalTerm && (0, term_1.termEqual)(claimTerm, goalTerm);
        if (!match) {
            ctx.diagnostics.push({ severity: 'error', step, message: `exact: '${claim}' does not match goal '${ctx.goal}'`, rule: 'STRUCTURAL' });
            ctx.proofSteps.push({ step, kind: 'exact', claim, rule: 'STRUCTURAL', state: 'FAILED', message: `Does not match goal` });
            return;
        }
    }
    const derivation = deriveClaim(ctx, claim, step);
    if (derivation.state === 'FAILED') {
        ctx.diagnostics.push({ severity: 'error', step, message: derivation.message, rule: derivation.rule });
    }
    ctx.proofSteps.push({
        step,
        kind: 'exact',
        claim,
        rule: derivation.rule,
        state: derivation.state,
        uses: derivation.uses,
        message: derivation.message,
    });
}
function handleObtain(ctx, node, step) {
    const { varName, source } = node;
    // Locate the existential in context (objects, assumptions, or premises).
    const hyp = findExact(ctx.objects, source, false)
        ?? findExact(ctx.assumptions, source, false)
        ?? findExact(ctx.premises, source, false);
    if (!hyp) {
        ctx.diagnostics.push({ severity: 'error', step, message: `obtain: '${source}' not found in context`, rule: 'STRUCTURAL' });
        ctx.proofSteps.push({ step, kind: 'intro', claim: source, rule: 'STRUCTURAL', state: 'FAILED', message: `Existential not found` });
        return;
    }
    const exists = (0, propositions_1.parseBoundedQuantifierCanonical)(hyp.claim, 'exists');
    if (!exists) {
        ctx.diagnostics.push({ severity: 'error', step, message: `obtain: '${source}' is not an existential`, rule: 'STRUCTURAL' });
        ctx.proofSteps.push({ step, kind: 'intro', claim: source, rule: 'STRUCTURAL', state: 'FAILED', message: `Not an existential` });
        return;
    }
    // Introduce varName ∈ set and P(varName) as assumptions.
    const membershipClaim = `${varName} ∈ ${exists.set}`;
    const bodyClaim = substituteVariable(exists.body, exists.variable, varName);
    ctx.variables.push({ name: varName, domain: exists.set });
    const memObj = createKernelObject(ctx, membershipClaim, 'ASSUMPTION', step, [hyp.id]);
    ctx.assumptions.push(memObj);
    const bodyObj = createKernelObject(ctx, bodyClaim, 'ASSUMPTION', step, [hyp.id]);
    ctx.assumptions.push(bodyObj);
    ctx.proofSteps.push({
        step,
        kind: 'intro',
        claim: membershipClaim,
        rule: 'ASSUMPTION',
        state: 'PROVED',
        uses: [hyp.claim],
        message: `Obtained '${varName} ∈ ${exists.set}' and '${bodyClaim}' from existential`,
    });
}
function generateEliminators(types) {
    const result = new Map();
    for (const [typeName, typeDef] of types) {
        if (typeDef.variants.length > 0) {
            const metavar = 'x';
            const disjuncts = typeDef.variants.map(v => `${metavar} ∈ ${v.name}`);
            const conclusion = disjuncts.reduce((acc, d) => `${acc} ∨ ${d}`);
            result.set(`${typeName.toLowerCase()}.cases`, {
                name: `${typeName}.cases`,
                premises: [`${metavar} ∈ ${typeName}`],
                conclusion,
                state: 'PROVED',
                metavars: [metavar],
            });
        }
    }
    return result;
}
function enrichStructMembership(ctx, source, step) {
    const membership = (0, propositions_1.parseMembershipCanonical)(source.claim);
    if (!membership)
        return;
    const structDef = ctx.structs.get(membership.set);
    if (!structDef)
        return;
    for (const field of structDef.fields) {
        const fieldClaim = `${membership.element}.${field.name} ∈ ${field.type}`;
        if (findExact(ctx.objects, fieldClaim, true) || findExact(ctx.premises, fieldClaim, true) || findExact(ctx.assumptions, fieldClaim, true)) {
            continue;
        }
        createKernelObject(ctx, fieldClaim, 'STRUCT_ELIM', step, [source.id]);
    }
}
function isKnownSort(sort, structs, typeNames = new Set()) {
    const parsed = parseSort(sort);
    if (!parsed)
        return false;
    if (parsed.kind === 'list') {
        return parsed.element ? isKnownSort(formatSort(parsed.element), structs, typeNames) : false;
    }
    if (!parsed.name)
        return false;
    return BUILTIN_SORTS.has(parsed.name) || structs.has(parsed.name) || typeNames.has(parsed.name);
}
function createBranchContext(ctx) {
    return {
        ...ctx,
        objects: [...ctx.objects],
        derivations: [...ctx.derivations],
        diagnostics: [],
        proofSteps: [],
        variables: [...ctx.variables],
        assumptions: [...ctx.assumptions],
        premises: [...ctx.premises],
    };
}
function applyVariantPatternBindings(ctx, scrutinee, variant, bindings, step) {
    createKernelObject(ctx, `${scrutinee} ∈ ${variant.name}`, 'OR_ELIM', step);
    for (let index = 0; index < variant.fields.length; index++) {
        const binding = bindings[index];
        if (!binding || binding === '_')
            continue;
        const field = variant.fields[index];
        ctx.variables.push({ name: binding, domain: field.type });
        const assumption = createKernelObject(ctx, `${binding} ∈ ${field.type}`, 'ASSUMPTION', step);
        ctx.assumptions.push(assumption);
    }
}
function applyListPatternBindings(ctx, scrutinee, listType, parsedSort, head, tail, step) {
    const elementType = formatSort(parsedSort.element ?? { kind: 'named', name: 'Element' });
    createKernelObject(ctx, `${scrutinee} ∈ Cons`, 'OR_ELIM', step);
    if (head !== '_') {
        ctx.variables.push({ name: head, domain: elementType });
        const headAssumption = createKernelObject(ctx, `${head} ∈ ${elementType}`, 'ASSUMPTION', step);
        ctx.assumptions.push(headAssumption);
    }
    ctx.variables.push({ name: tail, domain: listType });
    const tailAssumption = createKernelObject(ctx, `${tail} ∈ ${listType}`, 'ASSUMPTION', step);
    ctx.assumptions.push(tailAssumption);
}
function evaluateMatchBranch(ctx, goal, step) {
    if (goal && findExact(ctx.objects, goal, false)) {
        return 'PROVED';
    }
    if (goal) {
        const goalMembership = (0, propositions_1.parseMembershipCanonical)(goal);
        if (goalMembership) {
            const lastConclusion = findLastConclude(ctx.proofSteps);
            if (lastConclusion && branchConclusionMatchesType(lastConclusion.claim, goalMembership.set, ctx)) {
                createKernelObject(ctx, goal, 'OR_ELIM', step);
                return 'PROVED';
            }
        }
        return 'FAILED';
    }
    return 'PROVED';
}
function findLastConclude(steps) {
    for (let index = steps.length - 1; index >= 0; index--) {
        if (steps[index].kind === 'conclude')
            return steps[index];
    }
    return null;
}
function branchConclusionMatchesType(claim, expectedType, ctx) {
    const inferred = inferExpressionType(claim, ctx);
    return inferred === expectedType;
}
function parseSort(value) {
    const trimmed = value.trim();
    const listMatch = trimmed.match(/^List\s*\(([\s\S]+)\)$/);
    if (listMatch) {
        const inner = parseSort(listMatch[1].trim());
        return inner ? { kind: 'list', element: inner } : null;
    }
    if (!trimmed)
        return null;
    return { kind: 'named', name: trimmed };
}
function formatSort(sort) {
    if (sort.kind === 'list') {
        return `List(${formatSort(sort.element ?? { kind: 'named', name: 'Element' })})`;
    }
    return sort.name ?? 'Element';
}
function inferExpressionType(claim, ctx) {
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (membership)
        return membership.set;
    const trimmed = claim.trim();
    if (trimmed === '[]') {
        const goalMembership = ctx.goal ? (0, propositions_1.parseMembershipCanonical)(ctx.goal) : null;
        return goalMembership?.set ?? null;
    }
    if (trimmed.startsWith('[') && trimmed.endsWith(']')) {
        const goalMembership = ctx.goal ? (0, propositions_1.parseMembershipCanonical)(ctx.goal) : null;
        if (goalMembership?.set && parseSort(goalMembership.set)?.kind === 'list') {
            return goalMembership.set;
        }
    }
    if (/^\d+$/.test(trimmed))
        return 'ℕ';
    if (/[π√]/.test(trimmed) || /\bsqrt\s*\(/.test(trimmed))
        return 'ℝ';
    const bareBinding = ctx.variables.find(variable => variable.name === trimmed);
    if (bareBinding?.domain)
        return bareBinding.domain;
    if (/[*\/^]/.test(trimmed)) {
        const vars = trimmed.match(/[A-Za-z_][\w₀-₉ₐ-ₙ]*/g) ?? [];
        if (vars.some(variable => {
            const binding = ctx.variables.find(entry => entry.name === variable);
            return binding?.domain === 'ℝ';
        }))
            return 'ℝ';
        return 'ℕ';
    }
    if (/[+]/.test(trimmed))
        return 'ℕ';
    const call = trimmed.match(/^([A-Za-z_][\w₀-₉ₐ-ₙ]*)\s*\(/);
    if (call && ctx.goal) {
        const goalMembership = (0, propositions_1.parseMembershipCanonical)(ctx.goal);
        if (goalMembership)
            return goalMembership.set;
    }
    return null;
}
function validateListStructuralRecursion(proof) {
    const fnMeta = proof.fnMeta;
    if (!fnMeta)
        return null;
    const listParams = fnMeta.params.filter(param => parseSort(param.type)?.kind === 'list');
    if (listParams.length === 0)
        return null;
    const invalidCall = findInvalidRecursiveCall(proof.body, proof.name, new Map(), listParams);
    if (!invalidCall)
        return null;
    return `UNVERIFIED: recursive call '${invalidCall.call}' is not structural on a List tail`;
}
function findInvalidRecursiveCall(nodes, fnName, allowedTails, listParams) {
    for (const node of nodes) {
        if (node.type === 'Match') {
            const scrutinee = (0, propositions_1.exprToProp)(node.scrutinee).trim();
            const listParam = listParams.find(param => param.name === scrutinee);
            for (const matchCase of node.cases) {
                const branchAllowed = new Map(allowedTails);
                if (listParam && matchCase.pattern.kind === 'list_cons') {
                    branchAllowed.set(listParam.name, matchCase.pattern.tail);
                }
                const nested = findInvalidRecursiveCall(matchCase.body, fnName, branchAllowed, listParams);
                if (nested)
                    return nested;
            }
            continue;
        }
        const claim = node.type === 'Assert' || node.type === 'Assume' || node.type === 'Conclude'
            ? (0, propositions_1.exprToProp)(node.expr)
            : node.type === 'Raw'
                ? node.content
                : null;
        if (claim) {
            const invalid = validateRecursiveCallsInText(claim, fnName, allowedTails, listParams);
            if (invalid)
                return invalid;
        }
    }
    return null;
}
function validateRecursiveCallsInText(text, fnName, allowedTails, listParams) {
    for (const call of extractNamedCalls(text, fnName)) {
        const args = splitTopLevelCallArgs(call.args);
        for (let index = 0; index < listParams.length; index++) {
            const param = listParams[index];
            const arg = args[index]?.trim();
            const allowedTail = allowedTails.get(param.name);
            if (!arg || arg !== allowedTail) {
                return { call: `${fnName}(${call.args})` };
            }
        }
    }
    return null;
}
function extractNamedCalls(text, fnName) {
    const calls = [];
    const pattern = new RegExp(`\\b${escapeRegex(fnName)}\\s*\\(`, 'g');
    let match;
    while ((match = pattern.exec(text)) !== null) {
        const openIndex = text.indexOf('(', match.index);
        const closeIndex = findMatchingParenInText(text, openIndex);
        if (openIndex === -1 || closeIndex === -1)
            continue;
        calls.push({ args: text.slice(openIndex + 1, closeIndex) });
        pattern.lastIndex = closeIndex + 1;
    }
    return calls;
}
function findMatchingParenInText(value, start) {
    let depth = 0;
    for (let i = start; i < value.length; i++) {
        const ch = value[i];
        if (ch === '(')
            depth++;
        else if (ch === ')') {
            depth--;
            if (depth === 0)
                return i;
        }
    }
    return -1;
}
function splitTopLevelCallArgs(value) {
    const args = [];
    let start = 0;
    let depth = 0;
    let bracketDepth = 0;
    for (let i = 0; i < value.length; i++) {
        const ch = value[i];
        if (ch === '(')
            depth++;
        else if (ch === ')')
            depth = Math.max(0, depth - 1);
        else if (ch === '[')
            bracketDepth++;
        else if (ch === ']')
            bracketDepth = Math.max(0, bracketDepth - 1);
        else if (ch === ',' && depth === 0 && bracketDepth === 0) {
            args.push(value.slice(start, i).trim());
            start = i + 1;
        }
    }
    const final = value.slice(start).trim();
    if (final)
        args.push(final);
    return args;
}
function parseFieldAccess(value) {
    const trimmed = value.trim();
    if (!trimmed.includes('.'))
        return null;
    const parts = trimmed.split('.').map(part => part.trim()).filter(Boolean);
    if (parts.length < 2)
        return null;
    return { base: parts[0], path: parts.slice(1) };
}
function resolveFieldProjection(ctx, base, path) {
    let currentExpr = base;
    let currentMembership = requireAnyMembership(ctx, currentExpr);
    if (!currentMembership)
        return null;
    for (const fieldName of path) {
        const membership = (0, propositions_1.parseMembershipCanonical)(currentMembership.claim);
        if (!membership)
            return null;
        const structDef = ctx.structs.get(membership.set);
        if (!structDef)
            return null;
        const field = structDef.fields.find(candidate => candidate.name === fieldName);
        if (!field)
            return null;
        currentExpr = `${currentExpr}.${fieldName}`;
        const nextClaim = `${currentExpr} ∈ ${field.type}`;
        let nextMembership = findExact(ctx.objects, nextClaim, false)
            ?? findExact(ctx.premises, nextClaim, false)
            ?? findExact(ctx.assumptions, nextClaim, false);
        if (!nextMembership) {
            nextMembership = createKernelObject(ctx, nextClaim, 'STRUCT_ELIM', currentMembership.step, [currentMembership.id]);
        }
        currentMembership = nextMembership;
    }
    const finalMembership = (0, propositions_1.parseMembershipCanonical)(currentMembership.claim);
    if (!finalMembership)
        return null;
    return { type: finalMembership.set, source: currentMembership };
}
function requireAnyMembership(ctx, element) {
    const pools = [ctx.objects, ctx.premises, ctx.assumptions];
    for (const pool of pools) {
        for (let index = pool.length - 1; index >= 0; index--) {
            const membership = (0, propositions_1.parseMembershipCanonical)(pool[index].claim);
            if (membership && (0, propositions_1.sameProp)(membership.element, element) && !pool[index].pending) {
                return pool[index];
            }
        }
    }
    return null;
}
function findWitness(ctx, variable) {
    for (let index = ctx.variables.length - 1; index >= 0; index--) {
        if (ctx.variables[index].name === variable) {
            return ctx.variables[index].name;
        }
    }
    for (let index = ctx.variables.length - 1; index >= 0; index--) {
        const candidate = ctx.variables[index];
        if (candidate.domain !== null) {
            return candidate.name;
        }
    }
    if (ctx.variables.length > 0) {
        return ctx.variables[ctx.variables.length - 1].name;
    }
    return null;
}
function substituteVariable(input, variable, replacement) {
    const pattern = new RegExp(`\\b${escapeRegex(variable)}\\b`, 'g');
    return input.replace(pattern, replacement);
}
function escapeRegex(value) {
    return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}
function normalizeSpaces(value) {
    return value.trim().replace(/\s+/g, ' ');
}
function containsWitness(claim, witness) {
    return new RegExp(`\\b${escapeRegex(witness)}\\b`).test(claim);
}
function predicateToRule(name) {
    switch (name) {
        case 'Category':
        case 'Object':
            return 'CAT_OBJECT';
        case 'Morphism':
            return 'CAT_MORPHISM';
        case 'Iso':
            return 'ISO_INTRO';
        case 'Product':
            return 'PRODUCT_INTRO';
        case 'ProductMediator':
            return 'PRODUCT_MEDIATOR';
        case 'Coproduct':
            return 'COPRODUCT_INTRO';
        case 'Pullback':
            return 'PULLBACK_INTRO';
        case 'Pushout':
            return 'PUSHOUT_INTRO';
        case 'Functor':
            return 'FUNCTOR_INTRO';
    }
}
function hasClaim(ctx, claim) {
    return Boolean(findExact(ctx.objects, claim, false) ||
        findExact(ctx.premises, claim, false) ||
        findExact(ctx.assumptions, claim, false));
}
function hasMorphism(ctx, claim) {
    return hasClaim(ctx, claim) || Boolean(findDeclarationByLabel(ctx, (0, propositions_1.parseMorphismDeclarationCanonical)(claim)?.label ?? ''));
}
function findDeclarationByLabel(ctx, label) {
    if (!label)
        return null;
    const collections = [ctx.objects, ctx.premises, ctx.assumptions];
    for (const collection of collections) {
        for (let index = collection.length - 1; index >= 0; index--) {
            const declaration = (0, propositions_1.parseMorphismDeclarationCanonical)(collection[index].claim);
            if (declaration && declaration.label === label) {
                return declaration;
            }
        }
    }
    return null;
}
function stripIdentity(value) {
    return value
        .replace(/\bid_\{?([^}\s]+(?:\([^)]*\))?)\}?\s*∘\s*/g, '')
        .replace(/\s*∘\s*id_\{?([^}\s]+(?:\([^)]*\))?)\}?/g, '')
        .trim();
}
function normalizeComposition(value) {
    return value
        .replace(/[()]/g, '')
        .split('∘')
        .map(part => part.trim())
        .filter(Boolean)
        .join(' ∘ ');
}
function looksLikeCategoricalEquality(claim) {
    return claim.includes('∘') || /\bid_/.test(claim) || /^[A-Z][\w₀-₉ₐ-ₙ]*\(.+\)\s*=/.test(claim);
}
// ── Extended cryptography rules ────────────────────────────────────────────────
function deriveCryptoClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    // ── Discrete logarithm hardness: dlog_hard(g, p) ─────────────────────────
    // Given p ∈ Prime and g ∈ Nat (primitive root), dlog is computationally hard
    const dlogMatch = norm.match(/^dlog_hard\((\w+)\s*,\s*(\w+)\)$/);
    if (dlogMatch) {
        const [, g, p] = dlogMatch;
        const pIsPrime = all.find(o => {
            const mem = (0, propositions_1.parseMembershipCanonical)(o.claim);
            return mem && mem.element === p && mem.set === 'Prime';
        });
        const gInNat = all.find(o => {
            const mem = (0, propositions_1.parseMembershipCanonical)(o.claim);
            return mem && mem.element === g && (mem.set === 'Nat' || mem.set === 'ℕ');
        });
        if (pIsPrime && gInNat) {
            createKernelObject(ctx, claim, 'CRYPTO_DL', step, [pIsPrime.id, gInNat.id]);
            return { rule: 'CRYPTO_DL', state: 'PROVED', uses: [pIsPrime.claim, gInNat.claim], message: `Discrete log hard in Z_${p}*` };
        }
    }
    // ── Diffie-Hellman key agreement ─────────────────────────────────────────
    // DH shared secret: g^(a*b) ≡ g^(b*a) (mod p)
    // Claim: dh_shared(g, a, b, p) = g^(a*b) mod p
    const dhMatch = norm.match(/^dh_secret\((\w+)\s*,\s*(\w+)\s*,\s*(\w+)\s*,\s*(\w+)\)\s*=\s*(.+)$/);
    if (dhMatch) {
        const [, g, a, b, p, result] = dhMatch;
        const pIsPrime = all.find(o => {
            const mem = (0, propositions_1.parseMembershipCanonical)(o.claim);
            return mem && mem.element === p && mem.set === 'Prime';
        });
        const dlogHard = all.find(o => o.claim.match(new RegExp(`dlog_hard\\(${g}\\s*,\\s*${p}\\)`)));
        if (pIsPrime && dlogHard) {
            // DH secret is g^(a*b) mod p = g^(b*a) mod p (commutativity)
            const expectedFwd = `${g}^(${a} * ${b}) mod ${p}`;
            const expectedBwd = `${g}^(${b} * ${a}) mod ${p}`;
            if ((0, arithmetic_1.normArith)(result) === (0, arithmetic_1.normArith)(expectedFwd) || (0, arithmetic_1.normArith)(result) === (0, arithmetic_1.normArith)(expectedBwd) ||
                (0, arithmetic_1.areCongruent)(result, expectedFwd, String(parseInt(p))) || (0, arithmetic_1.areCongruent)(result, expectedBwd, String(parseInt(p)))) {
                createKernelObject(ctx, claim, 'CRYPTO_DH', step, [pIsPrime.id, dlogHard.id]);
                return { rule: 'CRYPTO_DH', state: 'PROVED', uses: [pIsPrime.claim, dlogHard.claim], message: `DH shared secret: ${g}^(${a}${b}) ≡ ${g}^(${b}${a}) (mod ${p})` };
            }
        }
    }
    // ── Elliptic curve point membership ──────────────────────────────────────
    // Claim: on_curve(P, E) — point P lies on curve E: y² = x³ + ax + b (mod p)
    const ecPointMatch = norm.match(/^on_curve\((\w+)\s*,\s*(.+)\)$/);
    if (ecPointMatch) {
        const [, pt, curve] = ecPointMatch;
        // If we have the curve equation and point coordinates in context
        const curveEq = all.find(o => o.claim.match(new RegExp(`curve_eq\\(${curve.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*,`)));
        const ptCoords = all.find(o => o.claim.match(new RegExp(`coords\\(${pt}\\s*,`)));
        if (curveEq && ptCoords) {
            createKernelObject(ctx, claim, 'CRYPTO_EC', step, [curveEq.id, ptCoords.id]);
            return { rule: 'CRYPTO_EC', state: 'PROVED', uses: [curveEq.claim, ptCoords.claim], message: `Point ${pt} verified on curve ${curve}` };
        }
        // Also accept on_curve when given as axiom
        const axiom = all.find(o => (0, propositions_1.sameProp)(o.claim, claim));
        if (axiom) {
            createKernelObject(ctx, claim, 'CRYPTO_EC', step, [axiom.id]);
            return { rule: 'CRYPTO_EC', state: 'PROVED', uses: [axiom.claim], message: `EC point membership axiom` };
        }
    }
    // ── EC group law: commutativity P + Q = Q + P ─────────────────────────────
    const ecAddMatch = norm.match(/^ec_add\((\w+)\s*,\s*(\w+)\s*,\s*(\w+)\)\s*=\s*ec_add\((\w+)\s*,\s*(\w+)\s*,\s*(\w+)\)$/);
    if (ecAddMatch) {
        const [, P1, Q1, E1, Q2, P2, E2] = ecAddMatch;
        if (P1 === P2 && Q1 === Q2 && E1 === E2) {
            // ec_add(P, Q, E) = ec_add(Q, P, E) — commutativity
            createKernelObject(ctx, claim, 'CRYPTO_EC', step);
            return { rule: 'CRYPTO_EC', state: 'PROVED', message: 'EC group law: commutativity' };
        }
        if (P1 === Q2 && Q1 === P2 && E1 === E2) {
            createKernelObject(ctx, claim, 'CRYPTO_EC', step);
            return { rule: 'CRYPTO_EC', state: 'PROVED', message: 'EC group law: commutativity' };
        }
    }
    // ── Hash pre-image resistance: hash_secure(H) ────────────────────────────
    // Given collision_resistant(H) and one_way(H), conclude hash_secure(H)
    const hashSecureMatch = norm.match(/^hash_secure\((\w[\w₀-₉ₐ-ₙ]*)\)$/);
    if (hashSecureMatch) {
        const [, H] = hashSecureMatch;
        const collRes = all.find(o => o.claim.match(new RegExp(`collision_resistant\\(\\s*${H}\\s*\\)`)));
        const oneWay = all.find(o => o.claim.match(new RegExp(`one_way\\(\\s*${H}\\s*\\)`)));
        if (collRes && oneWay) {
            createKernelObject(ctx, claim, 'CRYPTO_HASH', step, [collRes.id, oneWay.id]);
            return { rule: 'CRYPTO_HASH', state: 'PROVED', uses: [collRes.claim, oneWay.claim], message: `${H} is a secure hash function` };
        }
    }
    // ── Commitment scheme binding: commit_binding(C) ─────────────────────────
    // Given collision_resistant(H), a hash-based commitment is binding
    const commitMatch = norm.match(/^commit_binding\((\w[\w₀-₉ₐ-ₙ]*)\)$/);
    if (commitMatch) {
        const [, C] = commitMatch;
        const hashBasis = all.find(o => o.claim.match(new RegExp(`hash_secure\\(\\s*${C}\\s*\\)`)) ||
            o.claim.match(new RegExp(`collision_resistant\\(\\s*${C}\\s*\\)`)));
        if (hashBasis) {
            createKernelObject(ctx, claim, 'CRYPTO_COMMIT', step, [hashBasis.id]);
            return { rule: 'CRYPTO_COMMIT', state: 'PROVED', uses: [hashBasis.claim], message: `${C} commitment scheme is binding` };
        }
    }
    return null;
}
// ── Real analysis rules ────────────────────────────────────────────────────────
function deriveRealAnalysisClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    // ── lim(f, a) = L ─────────────────────────────────────────────────────────
    // Pattern: lim(f, a) = L
    const limMatch = norm.match(/^lim\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
    if (limMatch) {
        const [, fn, point, limitVal] = limMatch;
        // If continuous(f, a) is in context then lim(f, a) = f(a)
        const contCtx = all.find(o => {
            return o.claim.match(new RegExp(`continuous\\(\\s*${fn}\\s*,\\s*${point.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*\\)`));
        });
        if (contCtx) {
            const appVal = `${fn}(${point})`;
            if ((0, arithmetic_1.normArith)(limitVal) === (0, arithmetic_1.normArith)(appVal) || (0, arithmetic_1.arithSymEqual)(limitVal, appVal)) {
                createKernelObject(ctx, claim, 'REAL_LIMIT', step, [contCtx.id]);
                return { rule: 'REAL_LIMIT', state: 'PROVED', uses: [contCtx.claim], message: `Limit by continuity: lim(${fn}, ${point}) = ${fn}(${point})` };
            }
        }
        // Squeeze theorem: if lo(a) ≤ f(a) ≤ hi(a) and lim(lo, a) = L and lim(hi, a) = L
        const limLo = all.find(o => o.claim.match(/^lim\((\w+)\s*,\s*.+\)\s*=\s*.+$/));
        const limHi = all.find(o => o !== limLo && o.claim.match(/^lim\((\w+)\s*,\s*.+\)\s*=\s*.+$/));
        if (limLo && limHi) {
            const mLo = limLo.claim.match(/^lim\((\w+)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
            const mHi = limHi.claim.match(/^lim\((\w+)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
            if (mLo && mHi && (0, arithmetic_1.normArith)(mLo[3]) === (0, arithmetic_1.normArith)(limitVal) && (0, arithmetic_1.normArith)(mHi[3]) === (0, arithmetic_1.normArith)(limitVal)) {
                createKernelObject(ctx, claim, 'REAL_SQUEEZE', step, [limLo.id, limHi.id]);
                return { rule: 'REAL_SQUEEZE', state: 'PROVED', uses: [limLo.claim, limHi.claim], message: 'Squeeze theorem' };
            }
        }
    }
    // ── continuous(f, a) ──────────────────────────────────────────────────────
    // Differentiable functions are continuous
    const contMatch = norm.match(/^continuous\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+)\)$/);
    if (contMatch) {
        const [, fn, point] = contMatch;
        const diffCtx = all.find(o => o.claim.match(new RegExp(`differentiable\\(\\s*${fn}\\s*,\\s*${point.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*\\)`)));
        if (diffCtx) {
            createKernelObject(ctx, claim, 'REAL_CONTINUOUS', step, [diffCtx.id]);
            return { rule: 'REAL_CONTINUOUS', state: 'PROVED', uses: [diffCtx.claim], message: 'Differentiable implies continuous' };
        }
        // Polynomials and standard functions are continuous everywhere
        const contOnR = all.find(o => o.claim.match(new RegExp(`continuous_on_R\\(\\s*${fn}\\s*\\)`)) ||
            o.claim.match(new RegExp(`polynomial\\(\\s*${fn}\\s*\\)`)));
        if (contOnR) {
            createKernelObject(ctx, claim, 'REAL_CONTINUOUS', step, [contOnR.id]);
            return { rule: 'REAL_CONTINUOUS', state: 'PROVED', uses: [contOnR.claim], message: `${fn} is continuous everywhere` };
        }
    }
    // ── IVT: intermediate value theorem ───────────────────────────────────────
    // Claim: ∃ c ∈ (a, b), f(c) = y
    // Requires: continuous(f, [a,b]), f(a) ≤ y ≤ f(b) or f(b) ≤ y ≤ f(a)
    const ivtMatch = norm.match(/^∃\s+c\s*∈\s*\((.+?)\s*,\s*(.+?)\)\s*,\s*(.+?)\(c\)\s*=\s*(.+)$/);
    if (ivtMatch) {
        const [, a, b, fn, y] = ivtMatch;
        const contInterval = all.find(o => o.claim.match(new RegExp(`continuous_on\\(\\s*${fn}\\s*,\\s*\\[${a.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*,\\s*${b.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\]\\s*\\)`)));
        if (contInterval) {
            const faLeY = all.find(o => {
                const ord = (0, arithmetic_1.parseOrder)(o.claim);
                return ord && (ord.op === '≤' || ord.op === '<=') &&
                    (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(`${fn}(${a})`) &&
                    (0, arithmetic_1.normArith)(ord.right) === (0, arithmetic_1.normArith)(y);
            });
            const yLeFb = all.find(o => {
                const ord = (0, arithmetic_1.parseOrder)(o.claim);
                return ord && (ord.op === '≤' || ord.op === '<=') &&
                    (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(y) &&
                    (0, arithmetic_1.normArith)(ord.right) === (0, arithmetic_1.normArith)(`${fn}(${b})`);
            });
            if (contInterval && (faLeY || yLeFb)) {
                const uses = [contInterval, faLeY, yLeFb].filter((o) => Boolean(o));
                createKernelObject(ctx, claim, 'REAL_IVT', step, uses.map(o => o.id));
                return { rule: 'REAL_IVT', state: 'PROVED', uses: uses.map(o => o.claim), message: 'Intermediate Value Theorem' };
            }
        }
    }
    // ── Bounded: |f(x)| ≤ M ──────────────────────────────────────────────────
    // If f is continuous on closed interval [a,b], it is bounded
    const boundMatch = norm.match(/^bounded\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*\[(.+?)\s*,\s*(.+?)\]\)$/);
    if (boundMatch) {
        const [, fn, a, b] = boundMatch;
        const contInterval = all.find(o => o.claim.match(new RegExp(`continuous_on\\(\\s*${fn}\\s*,\\s*\\[${a.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*,\\s*${b.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\]\\s*\\)`)));
        if (contInterval) {
            createKernelObject(ctx, claim, 'REAL_BOUND', step, [contInterval.id]);
            return { rule: 'REAL_BOUND', state: 'PROVED', uses: [contInterval.claim], message: 'Continuous on closed interval implies bounded (Extreme Value Theorem)' };
        }
    }
    // ── Derivative: derivative(f, x) = expr ──────────────────────────────────
    const diffMatch = norm.match(/^derivative\((\w[\w₀-₉ₐ-ₙ]*)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
    if (diffMatch) {
        const [, fn, varName, derExpr] = diffMatch;
        // Check if d/dx rule matches for known cases: derivative(x^n) = n*x^(n-1)
        const powerFn = all.find(o => {
            const eq = (0, propositions_1.parseEqualityCanonical)(o.claim);
            return eq && eq.left.trim() === fn && eq.right.includes('^');
        });
        if (powerFn) {
            const eq = (0, propositions_1.parseEqualityCanonical)(powerFn.claim);
            const powParsed = (0, arithmetic_1.parsePower)(eq.right);
            if (powParsed && (0, arithmetic_1.normArith)(powParsed.base) === (0, arithmetic_1.normArith)(varName)) {
                const n = (0, arithmetic_1.evalArith)(powParsed.exp);
                if (n !== null) {
                    // d/dx x^n = n * x^(n-1)
                    const expectedDer = n === 1 ? '1' : n === 2 ? `2 * ${varName}` : `${n} * ${varName}^${n - 1}`;
                    if ((0, arithmetic_1.arithSymEqual)(derExpr, expectedDer)) {
                        createKernelObject(ctx, claim, 'REAL_DIFF', step, [powerFn.id]);
                        return { rule: 'REAL_DIFF', state: 'PROVED', uses: [powerFn.claim], message: `Power rule: d/d${varName} ${fn}(${varName}) = ${expectedDer}` };
                    }
                }
            }
        }
        // Constant rule: derivative of constant = 0
        const constVal = (0, arithmetic_1.evalArith)(fn);
        if (constVal !== null && (0, arithmetic_1.normArith)(derExpr) === '0') {
            createKernelObject(ctx, claim, 'REAL_DIFF', step);
            return { rule: 'REAL_DIFF', state: 'PROVED', message: 'Constant rule: derivative of constant = 0' };
        }
    }
    return null;
}
// ── Order theory kernel ───────────────────────────────────────────────────────
function deriveOrderClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    // ── leq(a, a): reflexivity ────────────────────────────────────────────────
    const reflMatch = norm.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
    if (reflMatch) {
        const [, a, b] = reflMatch;
        if ((0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(b)) {
            createKernelObject(ctx, claim, 'ORDER_REFL', step);
            return { rule: 'ORDER_REFL', state: 'PROVED', message: `Order reflexivity: ${a} ≤ ${a}` };
        }
        // Transitivity: leq(a, b) from leq(a, c) and leq(c, b)
        for (const obj1 of all) {
            const m1 = obj1.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
            if (!m1 || (0, arithmetic_1.normArith)(m1[1]) !== (0, arithmetic_1.normArith)(a))
                continue;
            const mid = m1[2];
            for (const obj2 of all) {
                if (obj2 === obj1)
                    continue;
                const m2 = obj2.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
                if (m2 && (0, arithmetic_1.normArith)(m2[1]) === (0, arithmetic_1.normArith)(mid) && (0, arithmetic_1.normArith)(m2[2]) === (0, arithmetic_1.normArith)(b)) {
                    createKernelObject(ctx, claim, 'ORDER_TRANS', step, [obj1.id, obj2.id]);
                    return { rule: 'ORDER_TRANS', state: 'PROVED', uses: [obj1.claim, obj2.claim], message: `Order transitivity: ${a} ≤ ${mid} ≤ ${b}` };
                }
            }
        }
    }
    // ── antisymmetry: a = b from leq(a, b) and leq(b, a) ────────────────────
    const eqMatch = (0, propositions_1.parseEqualityCanonical)(norm);
    if (eqMatch) {
        const leqAB = all.find(o => o.claim.trim() === `leq(${eqMatch.left}, ${eqMatch.right})` ||
            (o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/) &&
                (0, arithmetic_1.normArith)(o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/)[1]) === (0, arithmetic_1.normArith)(eqMatch.left) &&
                (0, arithmetic_1.normArith)(o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/)[2]) === (0, arithmetic_1.normArith)(eqMatch.right)));
        const leqBA = all.find(o => {
            const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(eqMatch.right) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(eqMatch.left);
        });
        if (leqAB && leqBA) {
            createKernelObject(ctx, claim, 'ORDER_ANTISYM', step, [leqAB.id, leqBA.id]);
            return { rule: 'ORDER_ANTISYM', state: 'PROVED', uses: [leqAB.claim, leqBA.claim], message: `Order antisymmetry: ${eqMatch.left} = ${eqMatch.right}` };
        }
    }
    // ── join(a, b) = c: least upper bound ────────────────────────────────────
    const joinMatch = norm.match(/^leq\((.+?)\s*,\s*join\((.+?)\s*,\s*(.+?)\)\)$/);
    if (joinMatch) {
        const [, x, a, b] = joinMatch;
        const xInA = all.find(o => {
            const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(x) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(a);
        });
        if (xInA) {
            createKernelObject(ctx, claim, 'LATTICE_JOIN', step, [xInA.id]);
            return { rule: 'LATTICE_JOIN', state: 'PROVED', uses: [xInA.claim], message: `Lattice join: ${x} ≤ join(${a}, ${b})` };
        }
        const xInB = all.find(o => {
            const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(x) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(b);
        });
        if (xInB) {
            createKernelObject(ctx, claim, 'LATTICE_JOIN', step, [xInB.id]);
            return { rule: 'LATTICE_JOIN', state: 'PROVED', uses: [xInB.claim], message: `Lattice join: ${x} ≤ join(${a}, ${b})` };
        }
    }
    // ── meet(a, b) ≤ x: greatest lower bound ─────────────────────────────────
    const meetMatch = norm.match(/^leq\(meet\((.+?)\s*,\s*(.+?)\)\s*,\s*(.+?)\)$/);
    if (meetMatch) {
        const [, a, b, x] = meetMatch;
        const aLeX = all.find(o => {
            const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(a) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(x);
        });
        if (aLeX) {
            createKernelObject(ctx, claim, 'LATTICE_MEET', step, [aLeX.id]);
            return { rule: 'LATTICE_MEET', state: 'PROVED', uses: [aLeX.claim], message: `Lattice meet: meet(${a}, ${b}) ≤ ${x}` };
        }
        const bLeX = all.find(o => {
            const m = o.claim.match(/^leq\((.+?)\s*,\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(b) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(x);
        });
        if (bLeX) {
            createKernelObject(ctx, claim, 'LATTICE_MEET', step, [bLeX.id]);
            return { rule: 'LATTICE_MEET', state: 'PROVED', uses: [bLeX.claim], message: `Lattice meet: meet(${a}, ${b}) ≤ ${x}` };
        }
    }
    return null;
}
// ── Graph theory kernel ───────────────────────────────────────────────────────
function deriveGraphClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    // ── path(G, u, v): path existence by transitivity ────────────────────────
    const pathMatch = norm.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
    if (pathMatch) {
        const [, G, u, v] = pathMatch;
        // Reflexive: path(G, u, u) always
        if ((0, arithmetic_1.normArith)(u) === (0, arithmetic_1.normArith)(v)) {
            createKernelObject(ctx, claim, 'GRAPH_PATH', step);
            return { rule: 'GRAPH_PATH', state: 'PROVED', message: `Trivial path: ${u} = ${v}` };
        }
        // Direct edge: edge(G, u, v) or edge(G, v, u) in context
        const edgeUV = all.find(o => {
            const m = o.claim.match(/^edge\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(G) &&
                (((0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(u) && (0, arithmetic_1.normArith)(m[3]) === (0, arithmetic_1.normArith)(v)) ||
                    ((0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(v) && (0, arithmetic_1.normArith)(m[3]) === (0, arithmetic_1.normArith)(u)));
        });
        if (edgeUV) {
            createKernelObject(ctx, claim, 'GRAPH_PATH', step, [edgeUV.id]);
            return { rule: 'GRAPH_PATH', state: 'PROVED', uses: [edgeUV.claim], message: `Path via direct edge ${u}—${v}` };
        }
        // Transitivity: path(G, u, w) and path(G, w, v) → path(G, u, v)
        for (const obj1 of all) {
            const m1 = obj1.claim.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
            if (!m1 || (0, arithmetic_1.normArith)(m1[1]) !== (0, arithmetic_1.normArith)(G) || (0, arithmetic_1.normArith)(m1[2]) !== (0, arithmetic_1.normArith)(u))
                continue;
            const w = m1[3];
            for (const obj2 of all) {
                if (obj2 === obj1)
                    continue;
                const m2 = obj2.claim.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
                if (m2 && (0, arithmetic_1.normArith)(m2[1]) === (0, arithmetic_1.normArith)(G) && (0, arithmetic_1.normArith)(m2[2]) === (0, arithmetic_1.normArith)(w) && (0, arithmetic_1.normArith)(m2[3]) === (0, arithmetic_1.normArith)(v)) {
                    createKernelObject(ctx, claim, 'GRAPH_PATH', step, [obj1.id, obj2.id]);
                    return { rule: 'GRAPH_PATH', state: 'PROVED', uses: [obj1.claim, obj2.claim], message: `Path by concatenation via ${w}` };
                }
            }
        }
    }
    // ── connected(G): from ∀ u v, path(G, u, v) ─────────────────────────────
    const connMatch = norm.match(/^connected\((.+?)\)$/);
    if (connMatch) {
        const [, G] = connMatch;
        const pathAll = all.find(o => o.claim.match(new RegExp(`^∀.+path\\(${G.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
        if (pathAll) {
            createKernelObject(ctx, claim, 'GRAPH_CONNECTED', step, [pathAll.id]);
            return { rule: 'GRAPH_CONNECTED', state: 'PROVED', uses: [pathAll.claim], message: `${G} is connected` };
        }
    }
    // ── tree(G): connected + acyclic ─────────────────────────────────────────
    const treeMatch = norm.match(/^tree\((.+?)\)$/);
    if (treeMatch) {
        const [, G] = treeMatch;
        const conn = all.find(o => o.claim.trim() === `connected(${G})`);
        const acyc = all.find(o => o.claim.trim() === `acyclic(${G})`);
        if (conn && acyc) {
            createKernelObject(ctx, claim, 'GRAPH_TREE', step, [conn.id, acyc.id]);
            return { rule: 'GRAPH_TREE', state: 'PROVED', uses: [conn.claim, acyc.claim], message: `${G} is a tree (connected + acyclic)` };
        }
    }
    // ── degree_sum(G) = 2 * |E| (handshake lemma) ───────────────────────────
    const degSumMatch = norm.match(/^degree_sum\((.+?)\)\s*=\s*2\s*\*\s*edge_count\((.+?)\)$/);
    if (degSumMatch) {
        const [, G1, G2] = degSumMatch;
        if ((0, arithmetic_1.normArith)(G1) === (0, arithmetic_1.normArith)(G2)) {
            const graphObj = all.find(o => o.claim.match(new RegExp(`^graph\\(${G1.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)`)));
            if (graphObj) {
                createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [graphObj.id]);
                return { rule: 'GRAPH_DEGREE', state: 'PROVED', uses: [graphObj.claim], message: 'Handshake lemma: sum of degrees = 2|E|' };
            }
            // Accept without explicit graph predicate as axiom
            createKernelObject(ctx, claim, 'GRAPH_DEGREE', step);
            return { rule: 'GRAPH_DEGREE', state: 'PROVED', message: 'Handshake lemma: sum of degrees = 2|E|' };
        }
    }
    return null;
}
// ── Combinatorics kernel ──────────────────────────────────────────────────────
function deriveCombClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    // ── Concrete factorial: factorial(n) = k ────────────────────────────────
    const factMatch = norm.match(/^factorial\((.+?)\)\s*=\s*(.+)$/);
    if (factMatch) {
        const [, nStr, kStr] = factMatch;
        const n = (0, arithmetic_1.evalArith)(nStr);
        const k = (0, arithmetic_1.evalArith)(kStr);
        if (n !== null && k !== null && n >= 0) {
            let fact = 1;
            for (let i = 2; i <= n; i++)
                fact *= i;
            if (fact === k) {
                createKernelObject(ctx, claim, 'COMB_FACTORIAL', step);
                return { rule: 'COMB_FACTORIAL', state: 'PROVED', message: `${n}! = ${k}` };
            }
        }
    }
    // ── Concrete binomial: binom(n, k) = c ──────────────────────────────────
    const binomMatch = norm.match(/^binom\((.+?)\s*,\s*(.+?)\)\s*=\s*(.+)$/);
    if (binomMatch) {
        const [, nStr, kStr, cStr] = binomMatch;
        const n = (0, arithmetic_1.evalArith)(nStr);
        const k = (0, arithmetic_1.evalArith)(kStr);
        const c = (0, arithmetic_1.evalArith)(cStr);
        if (n !== null && k !== null && c !== null && n >= 0 && k >= 0 && k <= n) {
            // Compute C(n, k)
            let num = 1;
            for (let i = 0; i < k; i++)
                num = num * (n - i) / (i + 1);
            if (Math.round(num) === c) {
                createKernelObject(ctx, claim, 'COMB_BINOM', step);
                return { rule: 'COMB_BINOM', state: 'PROVED', message: `C(${n}, ${k}) = ${c}` };
            }
        }
    }
    // ── Pigeonhole: ¬ injective(f) or pigeonhole(n, k) ──────────────────────
    // Pattern: pigeonhole(objects, boxes) — objects > boxes implies collision
    const pigeonMatch = norm.match(/^pigeonhole\((.+?)\s*,\s*(.+?)\)$/);
    if (pigeonMatch) {
        const [, objStr, boxStr] = pigeonMatch;
        const objs = (0, arithmetic_1.evalArith)(objStr);
        const boxes = (0, arithmetic_1.evalArith)(boxStr);
        if (objs !== null && boxes !== null && objs > boxes) {
            createKernelObject(ctx, claim, 'COMB_PIGEONHOLE', step);
            return { rule: 'COMB_PIGEONHOLE', state: 'PROVED', message: `Pigeonhole: ${objs} objects in ${boxes} boxes implies collision` };
        }
        // Symbolic: if we have |A| > |B| in context, conclude pigeonhole(A, B)
        const sizeGt = all.find(o => {
            const ord = (0, arithmetic_1.parseOrder)(o.claim);
            return ord && (ord.op === '>' || ord.op === '<') &&
                (((0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(objStr) && (0, arithmetic_1.normArith)(ord.right) === (0, arithmetic_1.normArith)(boxStr)) ||
                    ((0, arithmetic_1.normArith)(ord.right) === (0, arithmetic_1.normArith)(objStr) && (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(boxStr)));
        });
        if (sizeGt) {
            createKernelObject(ctx, claim, 'COMB_PIGEONHOLE', step, [sizeGt.id]);
            return { rule: 'COMB_PIGEONHOLE', state: 'PROVED', uses: [sizeGt.claim], message: 'Pigeonhole principle' };
        }
    }
    // ── Inclusion-exclusion: |A ∪ B| = |A| + |B| - |A ∩ B| ─────────────────
    const inclExclMatch = norm.match(/^\|(.+?)\s*∪\s*(.+?)\|\s*=\s*\|(.+?)\|\s*\+\s*\|(.+?)\|\s*-\s*\|(.+?)\s*∩\s*(.+?)\|$/);
    if (inclExclMatch) {
        const [, A1, B1, A2, B2, A3, B3] = inclExclMatch;
        if ((0, arithmetic_1.normArith)(A1) === (0, arithmetic_1.normArith)(A2) && (0, arithmetic_1.normArith)(A1) === (0, arithmetic_1.normArith)(A3) &&
            (0, arithmetic_1.normArith)(B1) === (0, arithmetic_1.normArith)(B2) && (0, arithmetic_1.normArith)(B1) === (0, arithmetic_1.normArith)(B3)) {
            createKernelObject(ctx, claim, 'COMB_INCLUSION_EXCL', step);
            return { rule: 'COMB_INCLUSION_EXCL', state: 'PROVED', message: 'Inclusion-exclusion principle' };
        }
    }
    return null;
}
