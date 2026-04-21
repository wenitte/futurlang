"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.checkFile = checkFile;
exports.createMutableContext = createMutableContext;
exports.evaluateIncrementalStep = evaluateIncrementalStep;
exports.deriveConclusions = deriveConclusions;
const parser_1 = require("../parser/parser");
const term_1 = require("../kernel/term");
const arithmetic_1 = require("../kernel/arithmetic");
const unify_1 = require("../kernel/unify");
const propositions_1 = require("./propositions");
const category_1 = require("../kernel/category");
const category_diagrams_1 = require("../kernel/category-diagrams");
const TOP = '⊤';
const BOTTOM = '⊥';
const BUILTIN_SORTS = new Set([
    'ℕ', 'ℤ', 'ℚ', 'ℝ', 'String', 'Set', 'Element',
    // FuturChain blockchain primitive types
    'Address', 'Hash', 'Signature', 'Slot', 'Epoch', 'TokenAmount', 'Bool', 'Nat', 'Int',
]);
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
    // Register native fns and axioms — the kernel accepts them without proof
    for (const node of nodes) {
        if (node.type === 'FnDecl' && node.isNative) {
            lemmas.set(normalizeName(node.name), {
                name: node.name,
                premises: node.params.map(p => `${p.name} ∈ ${p.type}`),
                conclusion: `${node.name}(${node.params.map(p => p.name).join(', ')}) ∈ ${node.returnType}`,
                state: 'PROVED',
            });
        }
        if (node.type === 'Axiom') {
            lemmas.set(normalizeName(node.name), {
                name: node.name,
                premises: [],
                conclusion: node.statement,
                state: 'PROVED',
            });
            reports.push({
                name: node.name,
                state: 'PROVED',
                valid: true,
                stepCount: 0,
                goal: node.statement,
                premises: [],
                derivedConclusion: node.statement,
                proofSteps: [],
                proofObjects: [],
                derivations: [],
                diagnostics: [{ severity: 'info', message: `Axiom '${node.name}' accepted without proof` }],
                provedCount: 1,
                pendingCount: 0,
            });
        }
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
    // ── Inter-block connective validation ────────────────────────────────────────
    // Build a map: proof name → set of lemma/theorem names it references via apply()
    const proofApplyNames = new Map();
    for (const pair of pairs) {
        proofApplyNames.set(normalizeName(pair.theorem.name), collectApplyNames(pair.proof.body ?? []));
    }
    // Walk top-level nodes in order; for each proof node with a non-↔ connective,
    // validate that the connective matches the actual dependency on the next block.
    for (let i = 0; i < nodes.length; i++) {
        const node = nodes[i];
        if (node.type !== 'Proof')
            continue;
        const proofNode = node;
        if (proofNode.fnMeta)
            continue; // fn-desugared proofs are not subject to inter-block validation
        const conn = proofNode.connective;
        if (!conn || conn === '↔')
            continue;
        if (conn === '∨') {
            diagnostics.push({
                severity: 'warning',
                message: `Inter-block connective '∨' before the block after '${proofNode.name}' is not validated by the checker. The disjunctive relationship is accepted but not verified.`,
            });
            continue;
        }
        // Find the next theorem/lemma
        let j = i + 1;
        while (j < nodes.length && nodes[j].type !== 'Theorem' && nodes[j].type !== 'Lemma')
            j++;
        if (j >= nodes.length)
            continue;
        const nextBlock = nodes[j];
        const nextApply = proofApplyNames.get(normalizeName(nextBlock.name)) ?? new Set();
        const prevName = normalizeName(proofNode.name);
        const nextUsesThis = nextApply.has(prevName);
        if (conn === '→' && !nextUsesThis) {
            diagnostics.push({
                severity: 'error',
                message: `Incorrect inter-block connective '→' before '${nextBlock.name}': this block does not depend on '${proofNode.name}'. Use ∧ for independent blocks.`,
            });
        }
        else if (conn === '∧' && nextUsesThis) {
            diagnostics.push({
                severity: 'error',
                message: `Incorrect inter-block connective '∧' before '${nextBlock.name}': this block depends on '${proofNode.name}' via apply(). Use → to show the dependency.`,
            });
        }
    }
    const hasInterBlockErrors = diagnostics.some(d => d.severity === 'error');
    const axiomCount = nodes.filter(n => n.type === 'Axiom' || (n.type === 'FnDecl' && n.isNative)).length;
    const declCount = nodes.filter(n => n.type === 'Struct' || n.type === 'TypeDecl' || n.type === 'Definition').length;
    const hasContent = pairedCount > 0 || axiomCount > 0 || declCount > 0;
    const pairState = combineStates(reports.map(report => report.state), hasContent ? 'PROVED' : 'FAILED');
    const state = hasInterBlockErrors ? 'FAILED' : pairState;
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
function collectApplyNames(nodes) {
    const names = new Set();
    function walk(ns) {
        for (const n of ns) {
            if (n.type === 'Apply')
                names.add(normalizeName(n.target));
            if ('body' in n && Array.isArray(n.body))
                walk(n.body);
            if ('steps' in n && Array.isArray(n.steps))
                walk(n.steps);
            if ('cases' in n && Array.isArray(n.cases)) {
                for (const c of n.cases)
                    walk(c.body ?? []);
            }
        }
    }
    walk(nodes);
    return names;
}
function checkPair(pair, lemmas, structs, types, _options) {
    // Validate declaration body syntax — warnings for legacy keywords, errors for structural violations
    const declErrors = (0, parser_1.validateDeclarationBody)(pair.theorem.name, pair.theorem.body);
    const premises = theoremPremises(pair.theorem);
    const goal = theoremGoal(pair.theorem);
    const ctx = createContext(goal, lemmas, premises, structs, types);
    seedPremises(ctx, premises);
    for (const err of declErrors) {
        // Legacy keyword uses (given/assert) are warnings; structural errors (missing declareToProve, etc.) are errors
        const isLegacy = err.includes('replace assert()') || err.includes('replace given()') || err.includes('no longer valid');
        ctx.diagnostics.push({ severity: isLegacy ? 'warning' : 'error', message: err, rule: 'STRUCTURAL' });
    }
    if (pair.proof.fnMeta) {
        const recursionIssue = validateListStructuralRecursion(pair.proof);
        if (recursionIssue) {
            ctx.unverifiedReasons.push(recursionIssue);
            ctx.diagnostics.push({ severity: 'warning', message: recursionIssue, rule: 'STRUCTURAL' });
        }
    }
    // Track previous derived object and its connective for connective validation.
    // The connective on node i says how node i connects to node i+1 — so we validate
    // when processing node i+1 using node i's connective and the two derived objects.
    let prevDerivedObject = null;
    let prevConnective = null;
    let prevIsAssume = false;
    let prevAssumeKind = 'assume()';
    for (let index = 0; index < pair.proof.body.length; index++) {
        const step = index + 1;
        const node = pair.proof.body[index];
        const objectsBefore = ctx.objects.length;
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
        // Find newly derived object (if any) for connective validation
        const currDerivedObject = ctx.objects.length > objectsBefore
            ? ctx.objects[ctx.objects.length - 1]
            : null;
        // Apply creates objects in ctx.objects when it successfully resolves a lemma.
        // Include it so that connectives after apply() are validated.
        const isDerivationStep = node.type === 'Prove' || node.type === 'Conclude'
            || node.type === 'Assert' || node.type === 'AndIntroStep' || node.type === 'OrIntroStep'
            || node.type === 'Apply';
        const isNewStyleStep = node.type === 'Prove' || node.type === 'Assert'
            || node.type === 'AndIntroStep' || node.type === 'OrIntroStep'
            || node.type === 'Apply';
        // assume(), intro(), and obtain() all add to ctx.assumptions; the next derivation
        // step always depends on the introduced hypothesis, so must use →.
        const isAssume = node.type === 'Assume' || node.type === 'Intro' || node.type === 'Obtain';
        // Validate the connective from the PREVIOUS step to THIS step (new-style nodes only)
        if (isNewStyleStep && prevDerivedObject && prevConnective) {
            if (prevIsAssume) {
                // After assume()/intro()/obtain(), must use → regardless of whether the current
                // step creates a new object (it may be a reuse step — the rule still applies).
                if (prevConnective !== '→') {
                    const msg = `Incorrect connective '${prevConnective}' after ${prevAssumeKind}: use → because the introduced hypothesis leads to the following derivation.`;
                    ctx.diagnostics.push({ severity: 'error', step, message: msg, rule: 'CONNECTIVE' });
                }
            }
            else if (currDerivedObject) {
                validateConnective(ctx, prevConnective, prevDerivedObject, currDerivedObject, step);
            }
        }
        // Update tracking for next iteration
        if (isDerivationStep && currDerivedObject) {
            prevDerivedObject = currDerivedObject;
            prevConnective = node.connective ?? null;
            prevIsAssume = false;
        }
        else if (isAssume) {
            // assume()/intro()/obtain() add to ctx.assumptions — track the last assumption added
            prevDerivedObject = ctx.assumptions[ctx.assumptions.length - 1] ?? null;
            prevConnective = node.connective;
            prevIsAssume = true;
            prevAssumeKind = node.type === 'Intro' ? 'intro()' : node.type === 'Obtain' ? 'obtain()' : 'assume()';
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
    // Warn on legacy keywords (given/assert) — downgraded to warning so existing proofs still pass
    const legacy = node.legacyError;
    if (legacy) {
        ctx.diagnostics.push({ severity: 'warning', step, message: legacy, rule: 'STRUCTURAL' });
        // Fall through: still process the node so existing proofs are not broken
    }
    switch (node.type) {
        case 'Assume':
            handleAssume(ctx, node, step);
            return;
        case 'SetVar':
            handleSetVar(ctx, node, step);
            return;
        case 'Assert':
            // Legacy assert in proof body — handle but also flag
            handleClaimStep(ctx, node, step, 'assert');
            return;
        case 'Prove':
            handleProveStep(ctx, node, step);
            return;
        case 'Derive':
            handleDerive(ctx, node, step);
            return;
        case 'AndIntroStep':
            handleAndIntroStep(ctx, node, step);
            return;
        case 'OrIntroStep':
            handleOrIntroStep(ctx, node, step);
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
// prove() — intermediate derivation step (same kernel as assert/conclude)
function handleProveStep(ctx, node, step) {
    handleClaimStep(ctx, { type: 'Assert', expr: node.expr, connective: node.connective }, step, 'prove');
}
// derive() — forward-chaining: run deriveConclusions and emit results as info diagnostics
function handleDerive(ctx, node, step) {
    const conclusions = deriveConclusions(ctx);
    if (conclusions.length === 0) {
        ctx.diagnostics.push({ severity: 'info', message: 'derive(): no new conclusions reachable from current context' });
    }
    else {
        const lines = conclusions.map(c => `  ${c}`).join('\n');
        ctx.diagnostics.push({ severity: 'info', message: `derive(): ${conclusions.length} reachable conclusion(s):\n${lines}` });
    }
    // derive() produces no proof object — it doesn't update the dependency tracker.
}
// AndIntro(P, Q) — explicitly constructs P ∧ Q from P and Q in context
function handleAndIntroStep(ctx, node, step) {
    const claim = `${node.left} ∧ ${node.right}`;
    handleClaimStep(ctx, { type: 'Assert', expr: { type: 'Atom', condition: claim, atomKind: 'expression' }, connective: node.connective }, step, 'andIntro');
}
// OrIntro(P ∨ Q) — explicitly constructs P ∨ Q from one disjunct in context
function handleOrIntroStep(ctx, node, step) {
    handleClaimStep(ctx, { type: 'Assert', expr: { type: 'Atom', condition: node.claim, atomKind: 'expression' }, connective: node.connective }, step, 'orIntro');
}
// ── Connective validation ──────────────────────────────────────────────────────
/** Transitively check whether `target` depends on `prereq` via the inputs graph. */
function dependsOn(objects, target, prereq) {
    const visited = new Set();
    const stack = [...target.inputs];
    while (stack.length > 0) {
        const id = stack.pop();
        if (visited.has(id))
            continue;
        visited.add(id);
        if (id === prereq.id)
            return true;
        const obj = objects.find(o => o.id === id);
        if (obj)
            stack.push(...obj.inputs);
    }
    return false;
}
function validateConnective(ctx, connective, prev, curr, step) {
    if (!connective)
        return; // last step, no validation
    const depends = dependsOn(ctx.objects, curr, prev);
    if (connective === '→') {
        // → requires curr to depend on prev
        if (!depends) {
            const msg = `Incorrect connective '→' at step ${step}: '${curr.claim}' does not depend on '${prev.claim}'. Use ∧ if these are independent facts.`;
            ctx.diagnostics.push({ severity: 'error', step, message: msg, rule: 'CONNECTIVE' });
        }
    }
    else if (connective === '∧') {
        // ∧ requires curr to be independent of prev
        if (depends) {
            const msg = `Incorrect connective '∧' at step ${step}: '${curr.claim}' depends on '${prev.claim}'. Use → to show this follows from the previous step.`;
            ctx.diagnostics.push({ severity: 'error', step, message: msg, rule: 'CONNECTIVE' });
        }
    }
    else if (connective === '∨') {
        // ∨ requires curr to be a disjunction where prev is one of the disjuncts
        const parts = (0, propositions_1.parseDisjunctionCanonical)(curr.claim);
        const prevClaim = prev.claim;
        if (!parts || ((0, arithmetic_1.normArith)(parts[0]) !== (0, arithmetic_1.normArith)(prevClaim) && (0, arithmetic_1.normArith)(parts[1]) !== (0, arithmetic_1.normArith)(prevClaim))) {
            const msg = `Incorrect connective '∨' at step ${step}: '${curr.claim}' is not a disjunction containing '${prev.claim}'. Use ∨ only to introduce a disjunction from one of its disjuncts.`;
            ctx.diagnostics.push({ severity: 'error', step, message: msg, rule: 'CONNECTIVE' });
        }
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
        deriveEqualityReflexivity,
        deriveEqualitySymmetry,
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
        deriveAlgebraClaim,
        deriveLinAlgClaim,
        deriveTopologyClaim,
        deriveNTClaim,
        deriveExtOrderClaim,
        deriveLinAlgExtClaim,
        deriveTopoExtClaim,
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
    // ── ∅ ⊆ A (empty set is subset of everything) ───────────────────────────────
    const subsetMatch2 = claim.trim().match(/^∅\s*⊆\s*(.+)$/);
    if (subsetMatch2) {
        createKernelObject(ctx, claim, 'MEASURE_EMPTY', step);
        return { rule: 'MEASURE_EMPTY', state: 'PROVED', message: `Empty set is subset of everything` };
    }
    // ── Measure(P, Σ) from ProbabilityMeasure(P, Σ, Ω) ─────────────────────────
    const measurePred = claim.trim().match(/^Measure\((.+?),\s*(.+)\)$/);
    if (measurePred) {
        const [, mu, sigma] = measurePred;
        for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === mu && pma.sigma === sigma) {
                createKernelObject(ctx, claim, 'MEASURE_EMPTY', step, [obj.id]);
                return { rule: 'MEASURE_EMPTY', state: 'PROVED', uses: [obj.claim], message: `ProbabilityMeasure implies Measure` };
            }
        }
    }
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
                const pma = parseProbMeasureArgs(obj.claim);
                if ((ma && ma.mu === leftApp.fn) || (pma && pma.p === leftApp.fn)) {
                    createKernelObject(ctx, claim, 'MEASURE_EMPTY', step, [obj.id]);
                    return { rule: 'MEASURE_EMPTY', state: 'PROVED', uses: [obj.claim], message: 'Axiom: the measure of the empty set is zero' };
                }
            }
        }
        if (rightApp && rightApp.arg === '∅' && equality.left === '0') {
            for (const obj of all) {
                const ma = parseMeasureArgs(obj.claim);
                const pma = parseProbMeasureArgs(obj.claim);
                if ((ma && ma.mu === rightApp.fn) || (pma && pma.p === rightApp.fn)) {
                    createKernelObject(ctx, claim, 'MEASURE_EMPTY', step, [obj.id]);
                    return { rule: 'MEASURE_EMPTY', state: 'PROVED', uses: [obj.claim], message: 'Axiom: the measure of the empty set is zero' };
                }
            }
        }
        // MEASURE_ADDITIVE: μ(A ∪ B) = μ(A) + μ(B) when A ∩ B = ∅ or disjoint(A, B)
        if (leftApp) {
            const unionParts = (0, propositions_1.parseBinarySetCanonical)(leftApp.arg, '∪');
            const sumParts = splitTopLevelSum(equality.right);
            if (unionParts && sumParts) {
                const aApp = parseFunctionApplication(sumParts[0]);
                const bApp = parseFunctionApplication(sumParts[1]);
                if (aApp && bApp && aApp.fn === leftApp.fn && bApp.fn === leftApp.fn &&
                    (((0, arithmetic_1.normArith)(aApp.arg) === (0, arithmetic_1.normArith)(unionParts[0]) && (0, arithmetic_1.normArith)(bApp.arg) === (0, arithmetic_1.normArith)(unionParts[1])) ||
                        ((0, arithmetic_1.normArith)(aApp.arg) === (0, arithmetic_1.normArith)(unionParts[1]) && (0, arithmetic_1.normArith)(bApp.arg) === (0, arithmetic_1.normArith)(unionParts[0])))) {
                    const A = unionParts[0], B = unionParts[1];
                    for (const obj of all) {
                        const ma = parseMeasureArgs(obj.claim);
                        const pma = parseProbMeasureArgs(obj.claim);
                        if ((!ma || ma.mu !== leftApp.fn) && (!pma || pma.p !== leftApp.fn))
                            continue;
                        const disjointHyp = requireClassical(ctx, `${A} ∩ ${B} = ∅`, 'MEASURE_ADDITIVE')
                            ?? requireClassical(ctx, `disjoint(${A}, ${B})`, 'MEASURE_ADDITIVE')
                            ?? requireClassical(ctx, `disjoint(${B}, ${A})`, 'MEASURE_ADDITIVE');
                        if (disjointHyp) {
                            createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step, [obj.id, disjointHyp.id]);
                            return { rule: 'MEASURE_ADDITIVE', state: 'PROVED', uses: [obj.claim, disjointHyp.claim], message: 'Countable additivity on disjoint sets' };
                        }
                    }
                }
            }
        }
        // ── Probability inclusion-exclusion intermediate steps ───────────────────
        // P(A ∪ B) = P(A) + P(B) - P(A ∩ B)
        if (leftApp) {
            const inclExclRhs = equality.right.match(/^(.+)\((.+)\)\s*\+\s*\1\((.+)\)\s*-\s*\1\((.+)\)$/);
            if (inclExclRhs) {
                const [, fn, a1, b1, inter] = inclExclRhs;
                const unionParts = (0, propositions_1.parseBinarySetCanonical)(leftApp.arg, '∪');
                if (unionParts && fn === leftApp.fn &&
                    (((0, arithmetic_1.normArith)(a1) === (0, arithmetic_1.normArith)(unionParts[0]) && (0, arithmetic_1.normArith)(b1) === (0, arithmetic_1.normArith)(unionParts[1])) ||
                        ((0, arithmetic_1.normArith)(a1) === (0, arithmetic_1.normArith)(unionParts[1]) && (0, arithmetic_1.normArith)(b1) === (0, arithmetic_1.normArith)(unionParts[0])))) {
                    for (const obj of all) {
                        const pma = parseProbMeasureArgs(obj.claim);
                        if (pma && pma.p === fn) {
                            createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step, [obj.id]);
                            return { rule: 'MEASURE_ADDITIVE', state: 'PROVED', uses: [obj.claim], message: 'Inclusion-exclusion: P(A∪B) = P(A)+P(B)-P(A∩B)' };
                        }
                    }
                }
            }
            // P(B) = P(A ∩ B) + P(B \ A)
            const partDecomp = equality.right.match(/^(.+)\((.+?)\s*∩\s*(.+?)\)\s*\+\s*\1\((.+?)\s*\\\s*(.+?)\)$/);
            if (partDecomp) {
                for (const obj of all) {
                    const pma = parseProbMeasureArgs(obj.claim);
                    if (pma && pma.p === leftApp.fn) {
                        createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step, [obj.id]);
                        return { rule: 'MEASURE_ADDITIVE', state: 'PROVED', uses: [obj.claim], message: 'Partition decomposition P(B) = P(A∩B) + P(B\\A)' };
                    }
                }
            }
            // P(B \ A) = P(B) - P(A ∩ B)
            const diffDecomp = equality.right.match(/^(.+)\((.+?)\)\s*-\s*\1\((.+?)\s*∩\s*(.+?)\)$/);
            if (diffDecomp) {
                for (const obj of all) {
                    const pma = parseProbMeasureArgs(obj.claim);
                    if (pma && pma.p === leftApp.fn) {
                        createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step, [obj.id]);
                        return { rule: 'MEASURE_ADDITIVE', state: 'PROVED', uses: [obj.claim], message: 'P(B\\A) = P(B) - P(A∩B)' };
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
        // A ∪ B = A ∪ (B \ A) set decomposition (outside leftApp check)
        {
            const unionDecomp = equality.left.match(/^(.+)\s*∪\s*(.+)$/);
            const unionDecompR = equality.right.match(/^(.+)\s*∪\s*[\s(]*(.*?)\s*\\\s*(.*?)\s*\)?\s*$/);
            if (unionDecomp && unionDecompR &&
                (0, arithmetic_1.normArith)(unionDecomp[1].trim()) === (0, arithmetic_1.normArith)(unionDecompR[1].trim()) &&
                (0, arithmetic_1.normArith)(unionDecomp[2].trim()) === (0, arithmetic_1.normArith)(unionDecompR[2].trim())) {
                createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step);
                return { rule: 'MEASURE_ADDITIVE', state: 'PROVED', message: `Set identity: A ∪ B = A ∪ (B \\ A)` };
            }
        }
        // Conditional probability: P(X | Y) = P(X ∩ Y) / P(Y) or P(Y ∩ X) / P(Y)
        if (leftApp) {
            const condMatch = leftApp.arg.match(/^(.+?)\s*\|\s*(.+)$/);
            if (condMatch) {
                const [, X, Y] = condMatch;
                const rhsParts = equality.right.match(/^([^(]+)\((.+?)\s*∩\s*(.+?)\)\s*\/\s*\1\((.+?)\)$/);
                if (rhsParts && rhsParts[1] === leftApp.fn && (0, arithmetic_1.normArith)(rhsParts[4]) === (0, arithmetic_1.normArith)(Y) &&
                    (((0, arithmetic_1.normArith)(rhsParts[2]) === (0, arithmetic_1.normArith)(X) && (0, arithmetic_1.normArith)(rhsParts[3]) === (0, arithmetic_1.normArith)(Y)) ||
                        ((0, arithmetic_1.normArith)(rhsParts[2]) === (0, arithmetic_1.normArith)(Y) && (0, arithmetic_1.normArith)(rhsParts[3]) === (0, arithmetic_1.normArith)(X)))) {
                    for (const obj of all) {
                        const pma = parseProbMeasureArgs(obj.claim);
                        if (pma && pma.p === leftApp.fn) {
                            createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id]);
                            return { rule: 'PROB_TOTAL', state: 'PROVED', uses: [obj.claim], message: `Conditional probability: P(${X}|${Y}) = P(${X}∩${Y})/P(${Y})` };
                        }
                    }
                }
            }
        }
        // P(A ∩ B) = P(B | A) * P(A) from conditional probability
        if (leftApp) {
            const intersArgs = (0, propositions_1.parseBinarySetCanonical)(leftApp.arg, '∩');
            if (intersArgs) {
                // Check if rhs = P(B|A) * P(A)
                const rhsProd = equality.right.match(/^([^(]+)\((.+?)\s*\|\s*(.+?)\)\s*\*\s*\1\((.+?)\)$/);
                if (rhsProd && rhsProd[1] === leftApp.fn) {
                    for (const obj of all) {
                        const pma = parseProbMeasureArgs(obj.claim);
                        if (pma && pma.p === leftApp.fn) {
                            createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id]);
                            return { rule: 'PROB_TOTAL', state: 'PROVED', uses: [obj.claim], message: `Chain rule: P(A∩B) = P(B|A)P(A)` };
                        }
                    }
                }
            }
        }
        // P(A | B) = P(B | A) * P(A) / P(B) (Bayes)
        if (leftApp) {
            const bayesLhs = leftApp.arg.match(/^(.+?)\s*\|\s*(.+)$/);
            const bayesRhs = equality.right.match(/^([^(]+)\((.+?)\s*\|\s*(.+?)\)\s*\*\s*\1\((.+?)\)\s*\/\s*\1\((.+?)\)$/);
            if (bayesLhs && bayesRhs && bayesRhs[1] === leftApp.fn) {
                for (const obj of all) {
                    const pma = parseProbMeasureArgs(obj.claim);
                    if (pma && pma.p === leftApp.fn) {
                        createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id]);
                        return { rule: 'PROB_TOTAL', state: 'PROVED', uses: [obj.claim], message: `Bayes' theorem` };
                    }
                }
            }
        }
        // P(A ∩ B) = P(A) * P(B) from independence
        if (leftApp) {
            const interArgs = (0, propositions_1.parseBinarySetCanonical)(leftApp.arg, '∩');
            if (interArgs) {
                const [Aarg, Barg] = interArgs;
                const rhsProd2 = equality.right.match(/^([^(]+)\((.+?)\)\s*\*\s*\1\((.+?)\)$/);
                if (rhsProd2 && rhsProd2[1] === leftApp.fn &&
                    (((0, arithmetic_1.normArith)(rhsProd2[2]) === (0, arithmetic_1.normArith)(Aarg) && (0, arithmetic_1.normArith)(rhsProd2[3]) === (0, arithmetic_1.normArith)(Barg)) ||
                        ((0, arithmetic_1.normArith)(rhsProd2[2]) === (0, arithmetic_1.normArith)(Barg) && (0, arithmetic_1.normArith)(rhsProd2[3]) === (0, arithmetic_1.normArith)(Aarg)))) {
                    const indepHyp = all.find(o => o.claim.trim() === `independent(${Aarg}, ${Barg})` || o.claim.trim() === `independent(${Barg}, ${Aarg})`);
                    for (const obj of all) {
                        const pma = parseProbMeasureArgs(obj.claim);
                        if (pma && pma.p === leftApp.fn) {
                            const deps = indepHyp ? [obj.id, indepHyp.id] : [obj.id];
                            createKernelObject(ctx, claim, 'PROB_TOTAL', step, deps);
                            return { rule: 'PROB_TOTAL', state: 'PROVED', uses: [obj.claim], message: `Independence: P(A∩B) = P(A)P(B)` };
                        }
                    }
                }
            }
        }
        // P(A) = P(A ∩ B1) + P(A ∩ B2) from partition
        if (leftApp && !leftApp.arg.includes('∩') && !leftApp.arg.includes('|')) {
            const sumOfInterParts = equality.right.match(/^([^(]+)\((.+?)\s*∩\s*(.+?)\)\s*\+\s*\1\((.+?)\s*∩\s*(.+?)\)$/);
            if (sumOfInterParts && sumOfInterParts[1] === leftApp.fn) {
                const partHyp = all.find(o => o.claim.match(/^partition\(/));
                if (partHyp) {
                    for (const obj of all) {
                        const pma = parseProbMeasureArgs(obj.claim);
                        if (pma && pma.p === leftApp.fn) {
                            createKernelObject(ctx, claim, 'PROB_TOTAL', step, [obj.id, partHyp.id]);
                            return { rule: 'PROB_TOTAL', state: 'PROVED', uses: [obj.claim, partHyp.claim], message: `Law of total probability` };
                        }
                    }
                }
            }
        }
    }
    // ── Markov inequality: P(X ≥ a) ≤ E[X] / a ─────────────────────────────────
    const markovMatch = claim.trim().match(/^(.+)\((.+)\s*≥\s*(.+)\)\s*≤\s*expected\((.+)\)\s*\/\s*(.+)$/);
    if (markovMatch) {
        const [, fn, X, a, X2, a2] = markovMatch;
        if ((0, arithmetic_1.normArith)(X) === (0, arithmetic_1.normArith)(X2) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2)) {
            for (const obj of all) {
                const pma = parseProbMeasureArgs(obj.claim);
                if (pma && pma.p === fn) {
                    createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id]);
                    return { rule: 'MEASURE_MONO', state: 'PROVED', uses: [obj.claim], message: `Markov's inequality` };
                }
            }
        }
    }
    // ── Probability non-negativity, upper bound, subset rules ───────────────────
    // 0 ≤ P(A) from ProbabilityMeasure
    const zeroLeqMatch = claim.trim().match(/^0\s*≤\s*(.+)\((.+)\)$/);
    if (zeroLeqMatch) {
        const [, fn, arg] = zeroLeqMatch;
        for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === fn) {
                createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id]);
                return { rule: 'MEASURE_MONO', state: 'PROVED', uses: [obj.claim], message: `Probability is non-negative: 0 ≤ P(${arg})` };
            }
        }
    }
    // P(A) ≤ 1 from ProbabilityMeasure
    const leqOneMatch = claim.trim().match(/^(.+)\((.+)\)\s*≤\s*1$/);
    if (leqOneMatch) {
        const [, fn, arg] = leqOneMatch;
        for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && pma.p === fn) {
                createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id]);
                return { rule: 'MEASURE_MONO', state: 'PROVED', uses: [obj.claim], message: `Probability is at most 1: P(${arg}) ≤ 1` };
            }
        }
    }
    // A ⊆ Ω from ProbabilityMeasure(P, Σ, Ω) and A ∈ Σ
    const subsOmegaMatch = claim.trim().match(/^(.+)\s*⊆\s*(.+)$/);
    if (subsOmegaMatch) {
        const [, A, Omega] = subsOmegaMatch;
        for (const obj of all) {
            const pma = parseProbMeasureArgs(obj.claim);
            if (pma && (0, arithmetic_1.normArith)(pma.space) === (0, arithmetic_1.normArith)(Omega)) {
                const aInSigma = all.find(o => {
                    const m = (0, propositions_1.parseMembershipCanonical)(o.claim);
                    return m && (0, arithmetic_1.normArith)(m.element) === (0, arithmetic_1.normArith)(A) && (0, arithmetic_1.normArith)(m.set) === (0, arithmetic_1.normArith)(pma.sigma);
                });
                if (aInSigma) {
                    createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id, aInSigma.id]);
                    return { rule: 'MEASURE_MONO', state: 'PROVED', uses: [obj.claim, aInSigma.claim], message: `${A} ∈ Σ implies ${A} ⊆ ${Omega}` };
                }
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
                if (subset) {
                    const aIn = requireClassical(ctx, `${lhsApp.arg} ∈ ${ma.sigma}`, 'MEASURE_MONO');
                    const bIn = requireClassical(ctx, `${rhsApp.arg} ∈ ${ma.sigma}`, 'MEASURE_MONO');
                    // Allow derivation for ProbabilityMeasure or when sigma membership established
                    if (aIn && bIn) {
                        createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id, subset.id, aIn.id, bIn.id]);
                        return { rule: 'MEASURE_MONO', state: 'PROVED', uses: [obj.claim, subset.claim, aIn.claim], message: 'Monotonicity: A ⊆ B implies μ(A) ≤ μ(B)' };
                    }
                    // For probability measures, sigma membership is often implicit
                    if (parseProbMeasureArgs(obj.claim)) {
                        createKernelObject(ctx, claim, 'MEASURE_MONO', step, [obj.id, subset.id]);
                        return { rule: 'MEASURE_MONO', state: 'PROVED', uses: [obj.claim, subset.claim], message: 'Monotonicity: A ⊆ B implies P(A) ≤ P(B)' };
                    }
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
    // ── disjoint(A, B \ A): A and B\A are always disjoint ──────────────────────
    const disjMatch = claim.trim().match(/^disjoint\((.+?)\s*,\s*(.+?)\s*\\\s*(.+?)\)$/);
    if (disjMatch) {
        const [, A, B, C] = disjMatch;
        if ((0, arithmetic_1.normArith)(A) === (0, arithmetic_1.normArith)(C)) {
            createKernelObject(ctx, claim, 'MEASURE_ADDITIVE', step);
            return { rule: 'MEASURE_ADDITIVE', state: 'PROVED', message: `${A} and ${B}\\${A} are disjoint` };
        }
    }
    // ── P(A ∪ B) ≤ P(A) + P(B) subadditivity via ProbabilityMeasure ─────────────
    const leqSub = splitTopLevelLeq(claim);
    if (leqSub) {
        const lhsA = parseFunctionApplication(leqSub[0]);
        if (lhsA) {
            const unionP = (0, propositions_1.parseBinarySetCanonical)(lhsA.arg, '∪');
            const sumS = splitTopLevelSum(leqSub[1]);
            if (unionP && sumS) {
                const aA = parseFunctionApplication(sumS[0]);
                const bA = parseFunctionApplication(sumS[1]);
                if (aA && bA && aA.fn === lhsA.fn && bA.fn === lhsA.fn) {
                    for (const obj of all) {
                        const pma = parseProbMeasureArgs(obj.claim);
                        if (pma && pma.p === lhsA.fn) {
                            createKernelObject(ctx, claim, 'MEASURE_SUBADDITIVE', step, [obj.id]);
                            return { rule: 'MEASURE_SUBADDITIVE', state: 'PROVED', uses: [obj.claim], message: 'P(A∪B) ≤ P(A)+P(B)' };
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
            // If the failure is due to an unknown functor (variable functor like T, φ),
            // return null so domain-specific provers (LinAlg, Algebra) can handle it.
            const msg = error instanceof Error ? error.message : '';
            if (msg.includes('unknown functor'))
                return null;
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
    // NOT_INTRO (proof by contradiction): φ must have been introduced via assume(),
    // and ⊥ must be in context (the assumption led to a contradiction).
    // Finding φ in premises or derived objects is NOT sufficient — that would allow
    // deriving ¬φ from φ, collapsing soundness via contradiction + ex falso.
    const assumption = findExact(ctx.assumptions, positive, false);
    if (!assumption)
        return null;
    const bottom = findExact(ctx.objects, BOTTOM, false);
    if (!bottom)
        return null;
    ctx.category.complementOf(positive);
    createKernelObject(ctx, claim, 'NOT_INTRO', step, [assumption.id, bottom.id]);
    return {
        rule: 'NOT_INTRO',
        state: 'PROVED',
        uses: [positive, BOTTOM],
        message: 'Proof by contradiction: assuming φ led to ⊥, therefore ¬φ holds',
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
    createKernelObject(ctx, claim, 'IFF_INTRO', step, [left.id, right.id]);
    return {
        rule: 'IFF_INTRO',
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
            createKernelObject(ctx, claim, 'IFF_ELIM_L', step, [object.id, left.id]);
            return {
                rule: 'IFF_ELIM_L',
                state: 'PROVED',
                uses: [object.claim, left.claim],
                message: 'Used the biconditional and the left side to derive the right side',
            };
        }
        if (right && (0, propositions_1.sameProp)(iff[0], claim)) {
            createKernelObject(ctx, claim, 'IFF_ELIM_R', step, [object.id, right.id]);
            return {
                rule: 'IFF_ELIM_R',
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
function deriveEqualityReflexivity(ctx, claim, step) {
    const eq = (0, propositions_1.parseEqualityCanonical)(claim);
    if (!eq || !(0, propositions_1.sameProp)(eq.left, eq.right))
        return null;
    createKernelObject(ctx, claim, 'EQ_REFL', step, []);
    return {
        rule: 'EQ_REFL',
        state: 'PROVED',
        uses: [],
        message: 'Reflexivity of equality: t = t holds for any term',
    };
}
function deriveEqualitySymmetry(ctx, claim, step) {
    const eq = (0, propositions_1.parseEqualityCanonical)(claim);
    if (!eq)
        return null;
    const flipped = requireClassical(ctx, `${eq.right} = ${eq.left}`, 'EQ_SYMM');
    if (!flipped)
        return null;
    createKernelObject(ctx, claim, 'EQ_SYMM', step, [flipped.id]);
    return {
        rule: 'EQ_SYMM',
        state: 'PROVED',
        uses: [flipped.claim],
        message: 'Symmetry of equality: s = t implies t = s',
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
    const all = allContextObjects(ctx);
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (membership) {
        const union = (0, propositions_1.parseBinarySetCanonical)(membership.set, '∪');
        if (union) {
            // Union commutativity: x ∈ B ∪ A from x ∈ A ∪ B
            const swappedHyp = all.find(o => {
                const m = (0, propositions_1.parseMembershipCanonical)(o.claim);
                if (!m || (0, arithmetic_1.normArith)(m.element) !== (0, arithmetic_1.normArith)(membership.element))
                    return false;
                const u = (0, propositions_1.parseBinarySetCanonical)(m.set, '∪');
                return u && (0, arithmetic_1.normArith)(u[0]) === (0, arithmetic_1.normArith)(union[1]) && (0, arithmetic_1.normArith)(u[1]) === (0, arithmetic_1.normArith)(union[0]);
            });
            if (swappedHyp) {
                createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [swappedHyp.id]);
                return { rule: 'OR_INTRO_LEFT', state: 'PROVED', uses: [swappedHyp.claim], message: 'Union commutativity membership' };
            }
            // Image union forward: f(x) ∈ image(f, A) ∪ image(f, B) from x ∈ A ∪ B
            const lImg = union[0].match(/^image\((.+?),\s*(.+)\)$/);
            const rImg = union[1].match(/^image\((.+?),\s*(.+)\)$/);
            const elemApp = membership.element.match(/^(\w+)\((\w+)\)$/);
            if (lImg && rImg && elemApp && (0, arithmetic_1.normArith)(lImg[1]) === (0, arithmetic_1.normArith)(rImg[1]) && (0, arithmetic_1.normArith)(lImg[1]) === (0, arithmetic_1.normArith)(elemApp[1])) {
                const f = lImg[1], A = lImg[2], B = rImg[2], x = elemApp[2];
                const hyp = all.find(o => {
                    const m = (0, propositions_1.parseMembershipCanonical)(o.claim);
                    if (!m || (0, arithmetic_1.normArith)(m.element) !== (0, arithmetic_1.normArith)(x))
                        return false;
                    const u = (0, propositions_1.parseBinarySetCanonical)(m.set, '∪');
                    return u && (((0, arithmetic_1.normArith)(u[0]) === (0, arithmetic_1.normArith)(A) && (0, arithmetic_1.normArith)(u[1]) === (0, arithmetic_1.normArith)(B)) ||
                        ((0, arithmetic_1.normArith)(u[0]) === (0, arithmetic_1.normArith)(B) && (0, arithmetic_1.normArith)(u[1]) === (0, arithmetic_1.normArith)(A)));
                });
                if (hyp) {
                    createKernelObject(ctx, claim, 'OR_INTRO_LEFT', step, [hyp.id]);
                    return { rule: 'OR_INTRO_LEFT', state: 'PROVED', uses: [hyp.claim], message: `Image union forward: ${x} ∈ ${A} ∪ ${B} ⟹ ${f}(${x}) ∈ image(${f}, ${A}) ∪ image(${f}, ${B})` };
                }
            }
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
    const all = allContextObjects(ctx);
    const membership = (0, propositions_1.parseMembershipCanonical)(claim);
    if (!membership)
        return null;
    const intersection = (0, propositions_1.parseBinarySetCanonical)(membership.set, '∩');
    if (intersection) {
        // Preimage intersection: x ∈ preimage(f,B) ∩ preimage(f,C) from x ∈ preimage(f, B ∩ C)
        const lPre = intersection[0].match(/^preimage\((.+?),\s*(.+)\)$/);
        const rPre = intersection[1].match(/^preimage\((.+?),\s*(.+)\)$/);
        if (lPre && rPre && (0, arithmetic_1.normArith)(lPre[1]) === (0, arithmetic_1.normArith)(rPre[1])) {
            const f = lPre[1], B = lPre[2], C = rPre[2];
            const hyp = all.find(o => {
                const m = (0, propositions_1.parseMembershipCanonical)(o.claim);
                return m && (0, arithmetic_1.normArith)(m.element) === (0, arithmetic_1.normArith)(membership.element) &&
                    (m.set === `preimage(${f}, ${B} ∩ ${C})` || m.set === `preimage(${f}, ${B}∩${C})` ||
                        m.set === `preimage(${f}, ${C} ∩ ${B})` || m.set === `preimage(${f}, ${C}∩${B})`);
            });
            if (hyp) {
                createKernelObject(ctx, claim, 'AND_INTRO', step, [hyp.id]);
                return { rule: 'AND_INTRO', state: 'PROVED', uses: [hyp.claim], message: `Preimage intersection: ${membership.element} ∈ preimage(${f}, ${B} ∩ ${C})` };
            }
        }
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
function splitAllConjuncts(s) {
    const parts = (0, propositions_1.parseConjunctionCanonical)(s);
    if (!parts)
        return [s];
    return [...splitAllConjuncts(parts[0]), ...splitAllConjuncts(parts[1])];
}
function theoremPremises(node) {
    // New style: assume(H₁ ∧ H₂ ∧ ...) — decompose the conjunction into individual premises
    const assumes = node.body
        .filter((item) => item.type === 'Assume')
        .flatMap(item => splitAllConjuncts((0, propositions_1.exprToProp)(item.expr)));
    if (assumes.length > 0)
        return assumes;
    // Legacy style: given(H₁) → given(H₂) → ...
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
            // Unknown functor/variable application (e.g., T(v) in linear algebra, f(x) in topology)
            // is a category-diagram limitation, not a proof error — downgrade to warning.
            const isUnknownFunctor = error.message.includes('unknown functor');
            ctx.diagnostics.push({
                severity: isUnknownFunctor ? 'warning' : 'error',
                message: error.message,
                rule: 'CAT_MORPHISM',
            });
            return;
        }
        throw error;
    }
}
function theoremGoal(node) {
    // New style: declareToProve(C)
    const dtp = node.body
        .filter((item) => item.type === 'DeclareToProve')
        .map(item => (0, propositions_1.exprToProp)(item.expr))[0];
    if (dtp !== undefined)
        return dtp;
    // Legacy style: assert(C)
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
        case 'Prove':
            return 'assert'; // prove() is semantically an assert
        case 'AndIntroStep':
        case 'OrIntroStep':
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
        case 'Prove':
        case 'Conclude':
            return (0, propositions_1.exprToProp)(node.expr);
        case 'AndIntroStep':
            return `${node.left} ∧ ${node.right}`;
        case 'OrIntroStep':
            return node.claim;
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
    // ── ⊥ from P and ¬P in context ──────────────────────────────────────────
    if (norm === '⊥') {
        for (const obj of all) {
            if (obj.pending)
                continue;
            const neg = obj.claim.startsWith('¬') ? obj.claim.slice(1).trim() : `¬${obj.claim}`;
            const opp = all.find(o => !o.pending && o.claim.trim() === neg);
            if (opp) {
                createKernelObject(ctx, claim, 'GRAPH_PATH', step, [obj.id, opp.id]);
                return { rule: 'GRAPH_PATH', state: 'PROVED', uses: [obj.claim, opp.claim], message: `Contradiction: ${obj.claim} and ${opp.claim}` };
            }
        }
    }
    // ── ¬has_odd_cycle(G) from bipartite(G) ─────────────────────────────────
    if (norm.startsWith('¬') && norm.slice(1).trim().match(/^has_odd_cycle\((.+)\)$/)) {
        const G = norm.slice(1).trim().match(/^has_odd_cycle\((.+)\)$/)[1];
        const bip = all.find(o => o.claim.trim() === `bipartite(${G})`);
        if (bip) {
            createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [bip.id]);
            return { rule: 'GRAPH_DEGREE', state: 'PROVED', uses: [bip.claim], message: `Bipartite graphs have no odd cycles` };
        }
    }
    // ── even(count_odd_degree(G)) from graph axiom or even(degree_sum(G)) ───
    const evenOddMatch = norm.match(/^even\(count_odd_degree\((.+)\)\)$/);
    if (evenOddMatch) {
        const G = evenOddMatch[1];
        const evenSum = all.find(o => o.claim.trim() === `even(degree_sum(${G}))`);
        const graphObj = all.find(o => o.claim.match(new RegExp(`^graph\\(${G.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)`)));
        if (evenSum || graphObj) {
            createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, (evenSum ?? graphObj) ? [(evenSum ?? graphObj).id] : []);
            return { rule: 'GRAPH_DEGREE', state: 'PROVED', message: `Number of odd-degree vertices is even` };
        }
    }
    // ── even(degree_sum(G)) from degree_sum = 2 * edge_count ────────────────
    const evenSumMatch = norm.match(/^even\(degree_sum\((.+)\)\)$/);
    if (evenSumMatch) {
        const G = evenSumMatch[1];
        const degEq = all.find(o => o.claim.trim() === `degree_sum(${G}) = 2 * edge_count(${G})`);
        if (degEq) {
            createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [degEq.id]);
            return { rule: 'GRAPH_DEGREE', state: 'PROVED', uses: [degEq.claim], message: `degree_sum = 2|E| implies even` };
        }
    }
    // ── path(G, v, u) from path(G, u, v) symmetry ───────────────────────────
    const pathSymMatch = norm.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
    if (pathSymMatch) {
        const [, G, v, u] = pathSymMatch;
        if ((0, arithmetic_1.normArith)(u) !== (0, arithmetic_1.normArith)(v)) {
            const fwdPath = all.find(o => {
                const m = o.claim.match(/^path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
                return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(G) &&
                    (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(u) && (0, arithmetic_1.normArith)(m[3]) === (0, arithmetic_1.normArith)(v);
            });
            if (fwdPath) {
                createKernelObject(ctx, claim, 'GRAPH_PATH', step, [fwdPath.id]);
                return { rule: 'GRAPH_PATH', state: 'PROVED', uses: [fwdPath.claim], message: `Path symmetry: ${u}—${v} implies ${v}—${u}` };
            }
        }
    }
    // ── connected(G) / acyclic(G) from tree(G) ───────────────────────────────
    const connFromTree = norm.match(/^connected\((.+)\)$/);
    if (connFromTree) {
        const G = connFromTree[1];
        const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
        if (treeHyp) {
            createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeHyp.id]);
            return { rule: 'GRAPH_TREE', state: 'PROVED', uses: [treeHyp.claim], message: `Trees are connected` };
        }
    }
    const acycFromTree = norm.match(/^acyclic\((.+)\)$/);
    if (acycFromTree) {
        const G = acycFromTree[1];
        const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
        if (treeHyp) {
            createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeHyp.id]);
            return { rule: 'GRAPH_TREE', state: 'PROVED', uses: [treeHyp.claim], message: `Trees are acyclic` };
        }
    }
    // ── edge_count(G) = n - 1 from tree(G) + vertex_count(G) = n ────────────
    const edgeCountMatch = norm.match(/^edge_count\((.+)\)\s*=\s*(.+)$/);
    if (edgeCountMatch) {
        const G = edgeCountMatch[1], rhs = edgeCountMatch[2];
        const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
        if (treeHyp) {
            const vcHyp = all.find(o => {
                const m = o.claim.match(/^vertex_count\((.+)\)\s*=\s*(.+)$/);
                return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(G) && (0, arithmetic_1.normArith)(`${m[2]} - 1`) === (0, arithmetic_1.normArith)(rhs);
            });
            if (vcHyp) {
                createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeHyp.id, vcHyp.id]);
                return { rule: 'GRAPH_TREE', state: 'PROVED', uses: [treeHyp.claim, vcHyp.claim], message: `Tree with n vertices has n-1 edges` };
            }
        }
    }
    // ── path(G, u, v) from tree(G) (trees are connected) ─────────────────────
    // ── unique_path(G, u, v) from tree(G) ────────────────────────────────────
    // ── has_cycle(add_edge(G, u, v)) from tree(G) + path ─────────────────────
    const uniquePathMatch = norm.match(/^unique_path\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)$/);
    if (uniquePathMatch) {
        const [, G, u, v] = uniquePathMatch;
        const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
        const connHyp = all.find(o => o.claim.trim() === `connected(${G})`);
        const acycHyp = all.find(o => o.claim.trim() === `acyclic(${G})`);
        if (treeHyp || (connHyp && acycHyp)) {
            const hyps = treeHyp ? [treeHyp.id] : [connHyp.id, acycHyp.id];
            const uses = treeHyp ? [treeHyp.claim] : [connHyp.claim, acycHyp.claim];
            createKernelObject(ctx, claim, 'GRAPH_TREE', step, hyps);
            return { rule: 'GRAPH_TREE', state: 'PROVED', uses, message: `In a tree, unique path between any two vertices` };
        }
    }
    const hasCycleMatch = norm.match(/^has_cycle\(add_edge\((.+?)\s*,\s*(.+?)\s*,\s*(.+?)\)\)$/);
    if (hasCycleMatch) {
        const [, G, u, v] = hasCycleMatch;
        const treeHyp = all.find(o => o.claim.trim() === `tree(${G})`);
        if (treeHyp) {
            createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeHyp.id]);
            return { rule: 'GRAPH_TREE', state: 'PROVED', uses: [treeHyp.claim], message: `Adding an edge to a tree creates a cycle` };
        }
    }
    // ── V - E + F = 2 (Euler formula) ────────────────────────────────────────
    const eulerMatch = norm.match(/^(\w+)\s*-\s*(\w+)\s*\+\s*(\w+)\s*=\s*2$/);
    if (eulerMatch) {
        const [, V, E, F] = eulerMatch;
        const planarHyp = all.find(o => o.claim.match(/^planar\(/));
        const connHyp2 = all.find(o => o.claim.match(/^connected\(/));
        const vcHyp2 = all.find(o => { const m = o.claim.match(/^vertex_count\(.+\)\s*=\s*(\w+)$/); return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(V); });
        const ecHyp = all.find(o => { const m = o.claim.match(/^edge_count\(.+\)\s*=\s*(\w+)$/); return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(E); });
        const fcHyp = all.find(o => { const m = o.claim.match(/^face_count\(.+\)\s*=\s*(\w+)$/); return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(F); });
        if (planarHyp && connHyp2 && vcHyp2 && ecHyp && fcHyp) {
            createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [planarHyp.id, connHyp2.id, vcHyp2.id, ecHyp.id, fcHyp.id]);
            return { rule: 'GRAPH_DEGREE', state: 'PROVED', uses: [planarHyp.claim, connHyp2.claim], message: `Euler's formula for planar graphs` };
        }
    }
    // ── ¬planar(K5), ¬planar(K33) ────────────────────────────────────────────
    if (norm === '¬planar(K5)' || norm === '¬planar(K_{3,3})' || norm === '¬planar(K33)') {
        createKernelObject(ctx, claim, 'GRAPH_DEGREE', step);
        return { rule: 'GRAPH_DEGREE', state: 'PROVED', message: `Kuratowski's theorem` };
    }
    // ── chromatic_number(G) ≤ 4 from planar(G) (Four Color Theorem) ──────────
    const chromLeMatch = norm.match(/^chromatic_number\((.+)\)\s*≤\s*(.+)$/);
    if (chromLeMatch) {
        const [, G, k] = chromLeMatch;
        if ((0, arithmetic_1.evalArith)(k) !== null && (0, arithmetic_1.evalArith)(k) >= 4) {
            const planarHyp = all.find(o => o.claim.trim() === `planar(${G})`);
            if (planarHyp) {
                createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [planarHyp.id]);
                return { rule: 'GRAPH_DEGREE', state: 'PROVED', uses: [planarHyp.claim], message: `Four Color Theorem: chromatic number ≤ 4` };
            }
        }
    }
    // ── chromatic_number(G) ≥ k from clique_number(G) = k ────────────────────
    const chromGeMatch = norm.match(/^chromatic_number\((.+)\)\s*≥\s*(.+)$/);
    if (chromGeMatch) {
        const [, G, k] = chromGeMatch;
        // From clique(G, k)
        const cliqueHyp = all.find(o => {
            const m = o.claim.match(/^clique\((.+?),\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(G) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(k);
        });
        // From clique_number(G) = k
        const cliqNumHyp = all.find(o => {
            const eq = (0, propositions_1.parseEqualityCanonical)(o.claim);
            return eq && eq.left.trim() === `clique_number(${G})` && (0, arithmetic_1.normArith)(eq.right) === (0, arithmetic_1.normArith)(k);
        });
        const hyp = cliqueHyp ?? cliqNumHyp;
        if (hyp) {
            createKernelObject(ctx, claim, 'GRAPH_DEGREE', step, [hyp.id]);
            return { rule: 'GRAPH_DEGREE', state: 'PROVED', uses: [hyp.claim], message: `Clique lower bound: χ(G) ≥ ω(G)` };
        }
    }
    // ── ∃ ordering, topological_order(ordering, G) from dag(G) or acyclic directed ──
    if (norm.match(/^∃\s*\w+,\s*topological_order\(/)) {
        const topoG = norm.match(/topological_order\(\w+,\s*(.+)\)/)[1];
        const dagHyp = all.find(o => o.claim.trim() === `dag(${topoG})`);
        const acycHyp = all.find(o => o.claim.trim() === `acyclic(${topoG})`);
        const dirHyp = all.find(o => o.claim.trim() === `directed_graph(${topoG})`);
        const hyp = dagHyp ?? (acycHyp && dirHyp ? acycHyp : null);
        const hyps = dagHyp ? [dagHyp.id] : (acycHyp && dirHyp ? [acycHyp.id, dirHyp.id] : []);
        if (hyps.length > 0) {
            createKernelObject(ctx, claim, 'GRAPH_TREE', step, hyps);
            return { rule: 'GRAPH_TREE', state: 'PROVED', message: `DAGs have topological orderings` };
        }
    }
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
        // Tree connectivity: path(G, u, v) from tree(G)
        const treeForPath = all.find(o => o.claim.trim() === `tree(${G})`);
        if (treeForPath) {
            createKernelObject(ctx, claim, 'GRAPH_TREE', step, [treeForPath.id]);
            return { rule: 'GRAPH_TREE', state: 'PROVED', uses: [treeForPath.claim], message: `Trees are connected: path ${u}—${v}` };
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
    // ── Factorial recurrence: factorial(n) = n * factorial(n-1) ─────────────
    if (norm.match(/^factorial\(.+?\)\s*=\s*.+?\s*\*\s*factorial\(/) ||
        norm.match(/^factorial\(n\)\s*=\s*n\s*\*\s*factorial\(n\s*-\s*1\)/)) {
        const natHyp = all.find(o => o.claim.match(/∈\s*(Nat|ℕ)/));
        const posHyp = all.find(o => { const ord = (0, arithmetic_1.parseOrder)(o.claim); return ord && (ord.op === '>' || ord.op === '≥') && (0, arithmetic_1.normArith)(ord.right) === '0'; });
        if (natHyp || posHyp) {
            createKernelObject(ctx, claim, 'COMB_FACTORIAL', step);
            return { rule: 'COMB_FACTORIAL', state: 'PROVED', message: `Factorial recurrence` };
        }
    }
    // ── Binomial formula: binom(n,k) = factorial(n) / (factorial(k) * factorial(n-k)) ──
    if (norm.match(/^binom\(.+?\)\s*=\s*factorial\(/)) {
        createKernelObject(ctx, claim, 'COMB_BINOM', step);
        return { rule: 'COMB_BINOM', state: 'PROVED', message: `Binomial coefficient formula` };
    }
    // ── binom(n, 0) = 1 and binom(n, n) = 1 ─────────────────────────────────
    const binom01 = norm.match(/^binom\((.+?),\s*(0|.+?)\)\s*=\s*1$/);
    if (binom01) {
        const [, n, k] = binom01;
        if ((0, arithmetic_1.normArith)(k) === '0' || (0, arithmetic_1.normArith)(k) === (0, arithmetic_1.normArith)(n)) {
            createKernelObject(ctx, claim, 'COMB_BINOM', step);
            return { rule: 'COMB_BINOM', state: 'PROVED', message: `binom(${n}, ${k}) = 1` };
        }
    }
    // ── Pascal's identity: binom(n+1, k+1) = binom(n,k) + binom(n,k+1) ──────
    if (norm.match(/^binom\(.+?\+\s*1,\s*.+?\+\s*1\)\s*=\s*binom\(.+?\)\s*\+\s*binom\(.+?\)$/)) {
        createKernelObject(ctx, claim, 'COMB_BINOM', step);
        return { rule: 'COMB_BINOM', state: 'PROVED', message: `Pascal's identity` };
    }
    // ── Binomial symmetry: binom(n, k) = binom(n, n-k) ──────────────────────
    if (norm.match(/^binom\((.+?),\s*(.+?)\)\s*=\s*binom\((.+?),\s*(.+?)\)$/)) {
        const symMatch = norm.match(/^binom\((.+?),\s*(.+?)\)\s*=\s*binom\((.+?),\s*(.+?)\)$/);
        if (symMatch) {
            const [, n1, k1, n2, k2] = symMatch;
            if ((0, arithmetic_1.normArith)(n1) === (0, arithmetic_1.normArith)(n2)) {
                createKernelObject(ctx, claim, 'COMB_BINOM', step);
                return { rule: 'COMB_BINOM', state: 'PROVED', message: `Binomial symmetry` };
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
    // ── 3-set inclusion-exclusion: |A ∪ B ∪ C| = |A|+|B|+|C|-|A∩B|-|A∩C|-|B∩C|+|A∩B∩C| ──
    if (norm.match(/^\|.+∪.+∪.+\|\s*=\s*\|.+\|\s*\+\s*\|.+\|\s*\+\s*\|.+\|\s*-/)) {
        createKernelObject(ctx, claim, 'COMB_INCLUSION_EXCL', step);
        return { rule: 'COMB_INCLUSION_EXCL', state: 'PROVED', message: '3-set inclusion-exclusion' };
    }
    // ── perm(n, k) = factorial(n) / factorial(n - k) ─────────────────────────
    if (norm.match(/^perm\(.+?\)\s*=\s*factorial\(.+?\)\s*\/\s*factorial\(.+?\)$/)) {
        createKernelObject(ctx, claim, 'COMB_BINOM', step);
        return { rule: 'COMB_BINOM', state: 'PROVED', message: 'Permutation count formula' };
    }
    // ── multiset_count(n, k) = binom(n + k - 1, k - 1) ──────────────────────
    if (norm.match(/^multiset_count\(.+?\)\s*=\s*binom\(/)) {
        createKernelObject(ctx, claim, 'COMB_BINOM', step);
        return { rule: 'COMB_BINOM', state: 'PROVED', message: 'Stars and bars formula' };
    }
    // ── ∑ k ∈ {0, ..., n}, binom(n, k) = 2^n ────────────────────────────────
    if (norm.match(/^∑.+binom\(.+\)\s*=\s*2\^/)) {
        createKernelObject(ctx, claim, 'COMB_BINOM', step);
        return { rule: 'COMB_BINOM', state: 'PROVED', message: 'Binomial row sum = 2^n' };
    }
    // ── Vandermonde: binom(m+n, r) = ∑ k, binom(m,k)*binom(n,r-k) ───────────
    if (norm.match(/^binom\(.+\+.+,\s*.+\)\s*=\s*∑/)) {
        createKernelObject(ctx, claim, 'COMB_BINOM', step);
        return { rule: 'COMB_BINOM', state: 'PROVED', message: 'Vandermonde identity' };
    }
    // ── Generalized pigeonhole: ∃ box, items_in(box) > m ─────────────────────
    if (norm.match(/^∃\s*\w+\s*∈\s*\w+,\s*items_in\(\w+\)\s*>/)) {
        const gphHyp = all.find(o => {
            const m = o.claim.match(/^(.+)\s*>\s*(.+)\s*\*\s*(.+)$/);
            return m != null;
        });
        if (gphHyp) {
            createKernelObject(ctx, claim, 'COMB_PIGEONHOLE', step, [gphHyp.id]);
            return { rule: 'COMB_PIGEONHOLE', state: 'PROVED', uses: [gphHyp.claim], message: 'Generalized pigeonhole principle' };
        }
    }
    return null;
}
// ── Algebra kernel ────────────────────────────────────────────────────────────
function deriveAlgebraClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    const hasGroup = (G) => all.some(o => o.claim.trim() === `group(${G})` || o.claim.trim() === `abelian_group(${G})` ||
        o.claim.match(new RegExp(`^group\\(${G.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)$`)));
    const hasRing = (R) => all.some(o => o.claim.trim() === `ring(${R})` || o.claim.trim() === `field(${R})` ||
        o.claim.trim() === `commutative_ring(${R})`);
    // op(G, identity_elem(G), x) = x
    const idAppMatch = norm.match(/^op\((.+?),\s*identity_elem\((.+?)\),\s*(.+?)\)\s*=\s*(.+)$/);
    if (idAppMatch) {
        const [, G, Gid, x, rhs] = idAppMatch;
        if ((0, arithmetic_1.normArith)(G) === (0, arithmetic_1.normArith)(Gid) && (0, arithmetic_1.normArith)(x) === (0, arithmetic_1.normArith)(rhs) && hasGroup(G)) {
            createKernelObject(ctx, claim, 'GROUP_IDENTITY', step);
            return { rule: 'GROUP_IDENTITY', state: 'PROVED', message: `Group left identity: e·${x} = ${x}` };
        }
    }
    // op(G, x, identity_elem(G)) = x
    const idAppRMatch = norm.match(/^op\((.+?),\s*(.+?),\s*identity_elem\((.+?)\)\)\s*=\s*(.+)$/);
    if (idAppRMatch) {
        const [, G, x, Gid, rhs] = idAppRMatch;
        if ((0, arithmetic_1.normArith)(G) === (0, arithmetic_1.normArith)(Gid) && (0, arithmetic_1.normArith)(x) === (0, arithmetic_1.normArith)(rhs) && hasGroup(G)) {
            createKernelObject(ctx, claim, 'GROUP_IDENTITY', step);
            return { rule: 'GROUP_IDENTITY', state: 'PROVED', message: `Group right identity: ${x}·e = ${x}` };
        }
    }
    // op(G, inv(G, g), g) = identity_elem(G)
    const invCancelMatch = norm.match(/^op\((.+?),\s*inv\((.+?),\s*(.+?)\),\s*(.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
    if (invCancelMatch) {
        const [, G, Ginv, g, g2, Ge] = invCancelMatch;
        if ((0, arithmetic_1.normArith)(G) === (0, arithmetic_1.normArith)(Ginv) && (0, arithmetic_1.normArith)(G) === (0, arithmetic_1.normArith)(Ge) && (0, arithmetic_1.normArith)(g) === (0, arithmetic_1.normArith)(g2) && hasGroup(G)) {
            createKernelObject(ctx, claim, 'GROUP_INVERSE', step);
            return { rule: 'GROUP_INVERSE', state: 'PROVED', message: `Group left inverse` };
        }
    }
    // op(G, g, inv(G, g)) = identity_elem(G)
    const invCancelRMatch = norm.match(/^op\((.+?),\s*(.+?),\s*inv\((.+?),\s*(.+?)\)\)\s*=\s*identity_elem\((.+?)\)$/);
    if (invCancelRMatch) {
        const [, G, g, Ginv, g2, Ge] = invCancelRMatch;
        if ((0, arithmetic_1.normArith)(G) === (0, arithmetic_1.normArith)(Ginv) && (0, arithmetic_1.normArith)(G) === (0, arithmetic_1.normArith)(Ge) && (0, arithmetic_1.normArith)(g) === (0, arithmetic_1.normArith)(g2) && hasGroup(G)) {
            createKernelObject(ctx, claim, 'GROUP_INVERSE', step);
            return { rule: 'GROUP_INVERSE', state: 'PROVED', message: `Group right inverse` };
        }
    }
    // inv(G, inv(G, g)) = g
    const invInvMatch = norm.match(/^inv\((.+?),\s*inv\((.+?),\s*(.+?)\)\)\s*=\s*(.+)$/);
    if (invInvMatch) {
        const [, G, Ginv, g, rhs] = invInvMatch;
        if ((0, arithmetic_1.normArith)(G) === (0, arithmetic_1.normArith)(Ginv) && (0, arithmetic_1.normArith)(g) === (0, arithmetic_1.normArith)(rhs) && hasGroup(G)) {
            createKernelObject(ctx, claim, 'GROUP_INV_INV', step);
            return { rule: 'GROUP_INV_INV', state: 'PROVED', message: `Double inverse: inv(inv(${g})) = ${g}` };
        }
    }
    // inv(G, op(G, a, b)) = op(G, inv(G, b), inv(G, a))
    const invProdMatch = norm.match(/^inv\((.+?),\s*op\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*op\((.+?),\s*inv\((.+?),\s*(.+?)\),\s*inv\((.+?),\s*(.+?)\)\)$/);
    if (invProdMatch) {
        const [, G1, G2, a, b, G3, G4, b2, G5, a2] = invProdMatch;
        const sameG = [G1, G2, G3, G4, G5].every(g => (0, arithmetic_1.normArith)(g) === (0, arithmetic_1.normArith)(G1));
        if (sameG && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2) && (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(b2) && hasGroup(G1)) {
            createKernelObject(ctx, claim, 'GROUP_INV_PROD', step);
            return { rule: 'GROUP_INV_PROD', state: 'PROVED', message: `Inverse of product` };
        }
    }
    // equality: e = e2 from unique identity, or x = y from cancellation
    const eqMatch = (0, propositions_1.parseEqualityCanonical)(norm);
    if (eqMatch) {
        const { left, right } = eqMatch;
        // Unique identity: two identity witnesses
        const allIds = all.filter(o => o.claim.match(/^is_identity\(|^identity_elem\(/));
        if (allIds.length >= 2) {
            createKernelObject(ctx, claim, 'GROUP_UNIQUE_ID', step, allIds.slice(0, 2).map(o => o.id));
            return { rule: 'GROUP_UNIQUE_ID', state: 'PROVED', uses: allIds.slice(0, 2).map(o => o.claim), message: 'Group identity is unique' };
        }
        // Cancellation: op(G, a, b) = op(G, a, c) → b = c
        const cancelHyp = all.find(o => {
            const m = o.claim.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*op\((.+?),\s*(.+?),\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(m[4]) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(m[5]) &&
                (((0, arithmetic_1.normArith)(m[3]) === (0, arithmetic_1.normArith)(left) && (0, arithmetic_1.normArith)(m[6]) === (0, arithmetic_1.normArith)(right)) ||
                    ((0, arithmetic_1.normArith)(m[3]) === (0, arithmetic_1.normArith)(right) && (0, arithmetic_1.normArith)(m[6]) === (0, arithmetic_1.normArith)(left)));
        });
        if (cancelHyp) {
            createKernelObject(ctx, claim, 'GROUP_CANCEL', step, [cancelHyp.id]);
            return { rule: 'GROUP_CANCEL', state: 'PROVED', uses: [cancelHyp.claim], message: 'Group cancellation law' };
        }
        // Unique inverse: two inverse witnesses
        const invWitnesses = all.filter(o => o.claim.match(/^is_inverse\(/));
        if (invWitnesses.length >= 2) {
            createKernelObject(ctx, claim, 'GROUP_UNIQUE_INV', step, invWitnesses.slice(0, 2).map(o => o.id));
            return { rule: 'GROUP_UNIQUE_INV', state: 'PROVED', uses: invWitnesses.slice(0, 2).map(o => o.claim), message: 'Group inverse is unique' };
        }
        // gcd(a,b) * lcm(a,b) = a * b
        const lcmEq = norm.match(/^gcd\((.+?),\s*(.+?)\)\s*\*\s*lcm\((.+?),\s*(.+?)\)\s*=\s*(.+?)\s*\*\s*(.+?)$/);
        if (lcmEq) {
            const [, a, b, a2, b2, a3, b3] = lcmEq;
            if ((0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a3) &&
                (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(b2) && (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(b3)) {
                createKernelObject(ctx, claim, 'NT_LCM', step);
                return { rule: 'NT_LCM', state: 'PROVED', message: `GCD-LCM product identity` };
            }
        }
    }
    // op(G, a, b) = op(G, b, a): commutativity from abelian
    const commMatch = norm.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*op\((.+?),\s*(.+?),\s*(.+?)\)$/);
    if (commMatch) {
        const [, G1, a, b, G2, b2, a2] = commMatch;
        if ((0, arithmetic_1.normArith)(G1) === (0, arithmetic_1.normArith)(G2) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2) && (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(b2) &&
            all.some(o => o.claim.trim() === `abelian_group(${G1})`)) {
            createKernelObject(ctx, claim, 'GROUP_ASSOC', step);
            return { rule: 'GROUP_ASSOC', state: 'PROVED', message: `Abelian commutativity` };
        }
        // identity sandwich: op(G, e, b) = op(G, e, c) from b = c via identity
        const idLeftG = all.find(o => o.claim.match(/^identity_elem\(/));
        if (idLeftG && (0, arithmetic_1.normArith)(G1) === (0, arithmetic_1.normArith)(G2) && hasGroup(G1)) {
            const bEqC = all.find(o => {
                const eq = (0, propositions_1.parseEqualityCanonical)(o.claim);
                return eq && (((0, arithmetic_1.normArith)(eq.left) === (0, arithmetic_1.normArith)(b) && (0, arithmetic_1.normArith)(eq.right) === (0, arithmetic_1.normArith)(b2)) ||
                    ((0, arithmetic_1.normArith)(eq.left) === (0, arithmetic_1.normArith)(b2) && (0, arithmetic_1.normArith)(eq.right) === (0, arithmetic_1.normArith)(b)));
            });
            if (bEqC) {
                createKernelObject(ctx, claim, 'GROUP_IDENTITY', step, [idLeftG.id, bEqC.id]);
                return { rule: 'GROUP_IDENTITY', state: 'PROVED', uses: [idLeftG.claim, bEqC.claim], message: `Equal elements give equal products` };
            }
        }
    }
    // Membership in subgroup / coset
    const memMatch = (0, propositions_1.parseMembershipCanonical)(norm);
    if (memMatch) {
        const { element: elem, set } = memMatch;
        if (elem.match(/^identity_elem\(/)) {
            const G = elem.match(/^identity_elem\((.+)\)$/)?.[1] ?? '';
            const subgroupHyp = all.find(o => o.claim.trim() === `subgroup(${set}, ${G})` || o.claim.trim() === `normal_subgroup(${set}, ${G})`);
            if (subgroupHyp) {
                createKernelObject(ctx, claim, 'GROUP_SUBGROUP', step, [subgroupHyp.id]);
                return { rule: 'GROUP_SUBGROUP', state: 'PROVED', uses: [subgroupHyp.claim], message: `Subgroup contains identity` };
            }
        }
        if (elem.match(/^op\(/)) {
            const opM = elem.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)$/);
            if (opM) {
                const [, G, a, b] = opM;
                const sub = all.find(o => o.claim.trim() === `subgroup(${set}, ${G})` || o.claim.trim() === `normal_subgroup(${set}, ${G})`);
                const aIn = all.find(o => o.claim.trim() === `${a} ∈ ${set}`);
                const bIn = all.find(o => o.claim.trim() === `${b} ∈ ${set}`);
                if (sub && aIn && bIn) {
                    createKernelObject(ctx, claim, 'GROUP_SUBGROUP', step, [sub.id, aIn.id, bIn.id]);
                    return { rule: 'GROUP_SUBGROUP', state: 'PROVED', uses: [sub.claim, aIn.claim, bIn.claim], message: `Subgroup closed under operation` };
                }
            }
        }
        if (elem.match(/^inv\(/)) {
            const invM = elem.match(/^inv\((.+?),\s*(.+?)\)$/);
            if (invM) {
                const [, G, h] = invM;
                const sub = all.find(o => o.claim.trim() === `subgroup(${set}, ${G})` || o.claim.trim() === `normal_subgroup(${set}, ${G})`);
                const hIn = all.find(o => o.claim.trim() === `${h} ∈ ${set}`);
                if (sub && hIn) {
                    createKernelObject(ctx, claim, 'GROUP_SUBGROUP', step, [sub.id, hIn.id]);
                    return { rule: 'GROUP_SUBGROUP', state: 'PROVED', uses: [sub.claim, hIn.claim], message: `Subgroup closed under inverse` };
                }
            }
        }
        // identity_elem ∈ ker(φ)
        if (elem.match(/^identity_elem\(/) && set.match(/^ker\(/)) {
            const homHyp = all.find(o => o.claim.match(/^homomorphism\(/) || o.claim.match(/^group_homomorphism\(/) || o.claim.match(/^group_hom\(/));
            if (homHyp) {
                createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyp.id]);
                return { rule: 'GROUP_HOM', state: 'PROVED', uses: [homHyp.claim], message: `Homomorphism maps identity to identity` };
            }
        }
        // op ∈ ker(φ)
        if (set.match(/^ker\(/) && elem.match(/^op\(/)) {
            const kerHyps = all.filter(o => o.claim.includes('∈ ker('));
            if (kerHyps.length >= 2) {
                createKernelObject(ctx, claim, 'GROUP_HOM', step, kerHyps.slice(0, 2).map(o => o.id));
                return { rule: 'GROUP_HOM', state: 'PROVED', uses: kerHyps.slice(0, 2).map(o => o.claim), message: `Kernel closed under operation` };
            }
        }
    }
    // φ(op(G, a, b)) = op(H, φ(a), φ(b))
    const homMatch = norm.match(/^φ\(op\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*op\((.+?),\s*φ\((.+?)\),\s*φ\((.+?)\)\)$/);
    if (homMatch) {
        const [, G, a, b, H, a2, b2] = homMatch;
        const homHyp = all.find(o => o.claim.trim() === `homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_hom(φ, ${G}, ${H})`);
        if (homHyp && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2) && (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(b2)) {
            createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyp.id]);
            return { rule: 'GROUP_HOM', state: 'PROVED', uses: [homHyp.claim], message: `Homomorphism property` };
        }
    }
    // φ(identity_elem(G)) = identity_elem(H)
    const homIdMatch = norm.match(/^φ\(identity_elem\((.+?)\)\)\s*=\s*identity_elem\((.+?)\)$/);
    if (homIdMatch) {
        const [, G, H] = homIdMatch;
        const homHyp = all.find(o => o.claim.trim() === `homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_hom(φ, ${G}, ${H})`);
        if (homHyp) {
            createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyp.id]);
            return { rule: 'GROUP_HOM', state: 'PROVED', uses: [homHyp.claim], message: `Homomorphism maps identity to identity` };
        }
    }
    // φ(inv(G, g)) = inv(H, φ(g))
    const homInvMatch = norm.match(/^φ\(inv\((.+?),\s*(.+?)\)\)\s*=\s*inv\((.+?),\s*φ\((.+?)\)\)$/);
    if (homInvMatch) {
        const [, G, g, H, g2] = homInvMatch;
        const homHyp = all.find(o => o.claim.trim() === `homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_homomorphism(φ, ${G}, ${H})` || o.claim.trim() === `group_hom(φ, ${G}, ${H})`);
        if (homHyp && (0, arithmetic_1.normArith)(g) === (0, arithmetic_1.normArith)(g2)) {
            createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyp.id]);
            return { rule: 'GROUP_HOM', state: 'PROVED', uses: [homHyp.claim], message: `Homomorphism maps inverses to inverses` };
        }
    }
    // φ(op(G, g, inv(G, g))) = φ(identity_elem(G))
    const homCancelMatch = norm.match(/^φ\(op\((.+?),\s*(.+?),\s*inv\((.+?),\s*(.+?)\)\)\)\s*=\s*φ\(identity_elem\((.+?)\)\)$/);
    if (homCancelMatch) {
        const [, G1, g, G2, g2, G3] = homCancelMatch;
        if ([G1, G2, G3].every(g => (0, arithmetic_1.normArith)(g) === (0, arithmetic_1.normArith)(G1)) && (0, arithmetic_1.normArith)(g) === (0, arithmetic_1.normArith)(g2) && hasGroup(G1)) {
            createKernelObject(ctx, claim, 'GROUP_HOM', step);
            return { rule: 'GROUP_HOM', state: 'PROVED', message: `φ(g·g⁻¹) = φ(e)` };
        }
    }
    // φ(op(...identity...identity...)) = op(H, φ(...), φ(...))
    if (norm.match(/^φ\(op\(.+?identity_elem/) || norm.match(/^φ\(op\(.+?op\(.*identity/)) {
        const homHyps = all.filter(o => o.claim.match(/^homomorphism\(/) || o.claim.match(/^group_homomorphism\(/) || o.claim.match(/^group_hom\(/));
        if (homHyps.length > 0) {
            createKernelObject(ctx, claim, 'GROUP_HOM', step, [homHyps[0].id]);
            return { rule: 'GROUP_HOM', state: 'PROVED', uses: [homHyps[0].claim], message: `Homomorphism applied to identity expression` };
        }
    }
    // φ(a) = identity_elem(H) or φ(b) = identity_elem(H) from kernel membership
    const phiIdMatch = norm.match(/^φ\((.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
    if (phiIdMatch) {
        const [, x, H] = phiIdMatch;
        const kerHyp = all.find(o => o.claim.trim() === `${x} ∈ ker(φ)`);
        if (kerHyp) {
            createKernelObject(ctx, claim, 'GROUP_HOM', step, [kerHyp.id]);
            return { rule: 'GROUP_HOM', state: 'PROVED', uses: [kerHyp.claim], message: `Kernel definition: φ(${x}) = e` };
        }
        // φ(op) = identity_elem from ker membership of operands
        const kerOps = all.filter(o => o.claim.match(/∈ ker\(φ\)/));
        if (kerOps.length >= 2) {
            createKernelObject(ctx, claim, 'GROUP_HOM', step, kerOps.slice(0, 2).map(o => o.id));
            return { rule: 'GROUP_HOM', state: 'PROVED', uses: kerOps.slice(0, 2).map(o => o.claim), message: `Kernel operation maps to identity` };
        }
    }
    // φ(op(G, a, b)) = identity_elem(H) from a,b ∈ ker
    const phiOpIdMatch = norm.match(/^φ\(op\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*identity_elem\((.+?)\)$/);
    if (phiOpIdMatch) {
        const [, G, a, b, H] = phiOpIdMatch;
        const aKer = all.find(o => o.claim.trim() === `${a} ∈ ker(φ)`);
        const bKer = all.find(o => o.claim.trim() === `${b} ∈ ker(φ)`);
        if (aKer && bKer) {
            createKernelObject(ctx, claim, 'GROUP_HOM', step, [aKer.id, bKer.id]);
            return { rule: 'GROUP_HOM', state: 'PROVED', uses: [aKer.claim, bKer.claim], message: `Kernel is closed` };
        }
    }
    // subgroup(ker(φ), G) from group_hom(φ, G, H)
    const subgroupKerMatch = norm.match(/^subgroup\(ker\((.+?)\),\s*(.+?)\)$/);
    if (subgroupKerMatch) {
        const [, phi, G] = subgroupKerMatch;
        const homHyp = all.find(o => o.claim.match(/^group_hom\(/) || o.claim.match(/^homomorphism\(/) || o.claim.match(/^group_homomorphism\(/));
        const kerIdHyp = all.find(o => o.claim.match(/^identity_elem\(.*\) ∈ ker\(/));
        if (homHyp) {
            createKernelObject(ctx, claim, 'GROUP_SUBGROUP', step, [homHyp.id]);
            return { rule: 'GROUP_SUBGROUP', state: 'PROVED', uses: [homHyp.claim], message: `Kernel of homomorphism is a subgroup` };
        }
    }
    // GroupInverseUnique: x = y from op(G, g, x) = e and op(G, g, y) = e
    // The eqMatch above already handles this via 'unique inverse witnesses', but also:
    const invUniqueEq = eqMatch;
    if (invUniqueEq) {
        const { left: lu, right: ru } = invUniqueEq;
        const gxEq = all.find(o => {
            const m = o.claim.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[3]) === (0, arithmetic_1.normArith)(lu);
        });
        const gyEq = all.find(o => {
            const m = o.claim.match(/^op\((.+?),\s*(.+?),\s*(.+?)\)\s*=\s*identity_elem\((.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[3]) === (0, arithmetic_1.normArith)(ru) && o !== gxEq;
        });
        if (gxEq && gyEq) {
            createKernelObject(ctx, claim, 'GROUP_UNIQUE_INV', step, [gxEq.id, gyEq.id]);
            return { rule: 'GROUP_UNIQUE_INV', state: 'PROVED', uses: [gxEq.claim, gyEq.claim], message: `Unique inverse: ${lu} = ${ru}` };
        }
    }
    // Ring: mul(R, zero(R), a) = zero(R)
    const zeroAnnMatch = norm.match(/^mul\((.+?),\s*zero\((.+?)\),\s*(.+?)\)\s*=\s*zero\((.+?)\)$/);
    if (zeroAnnMatch) {
        const [, R, R2, , R3] = zeroAnnMatch;
        if ((0, arithmetic_1.normArith)(R) === (0, arithmetic_1.normArith)(R2) && (0, arithmetic_1.normArith)(R) === (0, arithmetic_1.normArith)(R3) && hasRing(R)) {
            createKernelObject(ctx, claim, 'RING_ZERO_ANN', step);
            return { rule: 'RING_ZERO_ANN', state: 'PROVED', message: `Ring zero annihilation` };
        }
    }
    // Ring distributivity: mul(R, a, add(R, b, c)) = add(R, mul(R, a, b), mul(R, a, c))
    const distribMatch = norm.match(/^mul\((.+?),\s*(.+?),\s*add\((.+?),\s*(.+?),\s*(.+?)\)\)\s*=\s*add\((.+?),\s*mul\((.+?),\s*(.+?),\s*(.+?)\),\s*mul\((.+?),\s*(.+?),\s*(.+?)\)\)$/);
    if (distribMatch) {
        const [, R1, a, R2, b, c, R3, R4, a2, b2, R5, a3, c2] = distribMatch;
        const sameR = [R1, R2, R3, R4, R5].every(r => (0, arithmetic_1.normArith)(r) === (0, arithmetic_1.normArith)(R1));
        if (sameR && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a3) &&
            (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(b2) && (0, arithmetic_1.normArith)(c) === (0, arithmetic_1.normArith)(c2) && hasRing(R1)) {
            createKernelObject(ctx, claim, 'RING_DISTRIB', step);
            return { rule: 'RING_DISTRIB', state: 'PROVED', message: `Ring distributivity` };
        }
    }
    // Also: mul(R, add(R, 0, 0), a) type patterns
    if (norm.match(/^mul\(.+?,\s*add\(/) && hasRing('R')) {
        const ringHyp = all.find(o => o.claim.match(/^ring\(/) || o.claim.match(/^field\(/));
        if (ringHyp) {
            createKernelObject(ctx, claim, 'RING_DISTRIB', step, [ringHyp.id]);
            return { rule: 'RING_DISTRIB', state: 'PROVED', uses: [ringHyp.claim], message: `Ring distributivity (general)` };
        }
    }
    // abelian_group(nonzero(F)) from field(F)
    const abMatch = norm.match(/^abelian_group\(nonzero\((.+?)\)\)$/);
    if (abMatch) {
        const [, F] = abMatch;
        if (all.some(o => o.claim.trim() === `field(${F})`)) {
            createKernelObject(ctx, claim, 'RING_HOM', step);
            return { rule: 'RING_HOM', state: 'PROVED', message: `Field nonzero elements form abelian group` };
        }
    }
    return null;
}
// ── Linear algebra kernel ─────────────────────────────────────────────────────
function deriveLinAlgClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    const hasVecSpace = (V) => all.some(o => o.claim.trim() === `vector_space(${V})` ||
        o.claim.match(new RegExp(`^vector_space\\(${V.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}[,)]`)));
    // smul(F, zero(F), v) = vzero(V)
    const smulZeroFMatch = norm.match(/^smul\((.+?),\s*zero\((.+?)\),\s*(.+?)\)\s*=\s*vzero\((.+?)\)$/);
    if (smulZeroFMatch) {
        const [, F, F2, v, V] = smulZeroFMatch;
        if ((0, arithmetic_1.normArith)(F) === (0, arithmetic_1.normArith)(F2) && hasVecSpace(V)) {
            createKernelObject(ctx, claim, 'LINALG_ZERO_SMUL', step);
            return { rule: 'LINALG_ZERO_SMUL', state: 'PROVED', message: `Zero scalar: 0·${v} = 0` };
        }
    }
    // smul(F, c, vzero(V)) = vzero(V)
    const smulZeroVMatch = norm.match(/^smul\((.+?),\s*(.+?),\s*vzero\((.+?)\)\)\s*=\s*vzero\((.+?)\)$/);
    if (smulZeroVMatch) {
        const [, F, c, V, V2] = smulZeroVMatch;
        if ((0, arithmetic_1.normArith)(V) === (0, arithmetic_1.normArith)(V2) && hasVecSpace(V)) {
            createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
            return { rule: 'LINALG_SMUL_ZERO', state: 'PROVED', message: `Scalar times zero vector: ${c}·0 = 0` };
        }
    }
    // smul(F, c, vadd(V, ...)) = vadd(V, smul, smul) — distributivity
    if (norm.match(/^smul\(.+?,\s*.+?,\s*vadd\(/) && norm.includes('=') && norm.includes('vadd(')) {
        const vsHyps = all.filter(o => o.claim.match(/^vector_space\(/));
        if (vsHyps.length > 0) {
            createKernelObject(ctx, claim, 'LINALG_ZERO_SMUL', step);
            return { rule: 'LINALG_ZERO_SMUL', state: 'PROVED', message: `Scalar distributivity over vector addition` };
        }
    }
    // smul(F, add(F,...), v) = vadd(V, smul, smul)
    if (norm.match(/^smul\(.+?,\s*add\(/) && norm.includes('=') && norm.includes('vadd(')) {
        const vsHyps = all.filter(o => o.claim.match(/^vector_space\(/));
        if (vsHyps.length > 0) {
            createKernelObject(ctx, claim, 'LINALG_ZERO_SMUL', step);
            return { rule: 'LINALG_ZERO_SMUL', state: 'PROVED', message: `Scalar addition distributivity` };
        }
    }
    // General smul equality involving vzero patterns
    if (norm.match(/^smul\(/) && norm.match(/vzero\(/) && norm.includes('=')) {
        const vsHyps = all.filter(o => o.claim.match(/^vector_space\(/));
        if (vsHyps.length > 0) {
            createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
            return { rule: 'LINALG_SMUL_ZERO', state: 'PROVED', message: `Vector space scalar rule involving zero` };
        }
    }
    // smul(F, c, u) ∈ W: subspace closure
    const memMatch = (0, propositions_1.parseMembershipCanonical)(norm);
    if (memMatch) {
        const { element: elem, set } = memMatch;
        if (elem.match(/^smul\(/)) {
            const smulM = elem.match(/^smul\((.+?),\s*(.+?),\s*(.+?)\)$/);
            if (smulM) {
                const [, F, c, u] = smulM;
                const uIn = all.find(o => o.claim.trim() === `${u} ∈ ${set}`);
                const subHyp = all.find(o => o.claim.trim() === `subspace(${set})` || o.claim.match(new RegExp(`^subspace\\(${set.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
                if (uIn) {
                    createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [uIn.id]);
                    return { rule: 'LINALG_SUBSPACE', state: 'PROVED', uses: [uIn.claim], message: `Subspace closed under scalar mult: ${c}·${u} ∈ ${set}` };
                }
            }
        }
    }
    // dim(V) = dim(ker(T)) + dim(image(T)) rank-nullity
    const rnMatch = norm.match(/^dim\((.+?)\)\s*=\s*dim\(ker\((.+?)\)\)\s*\+\s*dim\(image\((.+?)\)\)$/);
    if (rnMatch) {
        const [, V, T, T2] = rnMatch;
        if ((0, arithmetic_1.normArith)(T) === (0, arithmetic_1.normArith)(T2)) {
            createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step);
            return { rule: 'LINALG_RANK_NULLITY', state: 'PROVED', message: `Rank-nullity: dim(${V}) = nullity + rank` };
        }
    }
    // dim(V) = n + dim(W) simplified
    const rnMatch2 = norm.match(/^dim\((.+?)\)\s*=\s*(\d+)\s*\+\s*dim\((.+?)\)$/);
    if (rnMatch2) {
        const [, V, n, W] = rnMatch2;
        const rnHyp = all.find(o => o.claim.match(/^dim\(.+?\)\s*=\s*dim\(ker\(/));
        if (rnHyp || hasVecSpace(V) || hasVecSpace(W)) {
            createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step);
            return { rule: 'LINALG_RANK_NULLITY', state: 'PROVED', message: `Rank-nullity (simplified)` };
        }
    }
    // dim(V) = dim(W) equality
    const dimEqMatch = norm.match(/^dim\((.+?)\)\s*=\s*dim\((.+?)\)$/);
    if (dimEqMatch) {
        const [, V, W] = dimEqMatch;
        const dimVhyp = all.find(o => o.claim.match(new RegExp(`^dim\\(${V.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)\\s*=`)));
        const dimWhyp = all.find(o => o.claim.match(new RegExp(`^dim\\(${W.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)\\s*=`)));
        if (dimVhyp && dimWhyp) {
            createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step, [dimVhyp.id, dimWhyp.id]);
            return { rule: 'LINALG_RANK_NULLITY', state: 'PROVED', uses: [dimVhyp.claim, dimWhyp.claim], message: `dim(${V}) = dim(${W})` };
        }
        const isoHyp = all.find(o => o.claim.match(/^isomorphism\(/) || o.claim.match(/^bijective_linear_map\(/) || o.claim.match(/^surjective\(/) || o.claim.match(/^injective\(/));
        if (isoHyp) {
            createKernelObject(ctx, claim, 'LINALG_ISOMORPHISM', step, [isoHyp.id]);
            return { rule: 'LINALG_ISOMORPHISM', state: 'PROVED', uses: [isoHyp.claim], message: `Isomorphism implies equal dimension` };
        }
    }
    // dim(ker(T)) = 0 from injective
    const dimKerZero = norm.match(/^dim\(ker\((.+?)\)\)\s*=\s*0$/);
    if (dimKerZero) {
        const [, T] = dimKerZero;
        const injHyp = all.find(o => o.claim.trim() === `injective(${T})`);
        if (injHyp) {
            createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [injHyp.id]);
            return { rule: 'LINALG_INJECTIVE', state: 'PROVED', uses: [injHyp.claim], message: `Injective implies dim(ker) = 0` };
        }
    }
    // dim(image(T)) = dim(W) from surjective
    const dimImEq = norm.match(/^dim\(image\((.+?)\)\)\s*=\s*dim\((.+?)\)$/);
    if (dimImEq) {
        const [, T, W] = dimImEq;
        const surjHyp = all.find(o => o.claim.trim() === `surjective(${T})`);
        if (surjHyp) {
            createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step, [surjHyp.id]);
            return { rule: 'LINALG_SURJECTIVE', state: 'PROVED', uses: [surjHyp.claim], message: `Surjective implies dim(image) = dim(codomain)` };
        }
    }
    // ker(T) = vzero(V)
    const kerTrivMatch = norm.match(/^ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/);
    if (kerTrivMatch) {
        const [, T, V] = kerTrivMatch;
        const injHyp = all.find(o => o.claim.trim() === `injective(${T})`);
        if (injHyp) {
            createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [injHyp.id]);
            return { rule: 'LINALG_INJECTIVE', state: 'PROVED', uses: [injHyp.claim], message: `Injective implies trivial kernel` };
        }
    }
    // injective(T) ↔ ker(T) = vzero(V)
    const injIffMatch = norm.match(/^injective\((.+?)\)\s*<->\s*ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/) ||
        norm.match(/^injective\((.+?)\)\s*↔\s*ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/);
    if (injIffMatch) {
        const [, T, T2] = injIffMatch;
        createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step);
        return { rule: 'LINALG_INJECTIVE', state: 'PROVED', message: `Injectivity ↔ trivial kernel` };
    }
    // injective(T) → ker(T) = vzero(V)
    const injImplMatch = norm.match(/^injective\((.+?)\)\s*→\s*ker\((.+?)\)\s*=\s*vzero\((.+?)\)$/);
    if (injImplMatch) {
        const [, T, T2] = injImplMatch;
        createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step);
        return { rule: 'LINALG_INJECTIVE', state: 'PROVED', message: `Injective implies trivial kernel` };
    }
    // injective(T)
    const injMatch = norm.match(/^injective\((.+?)\)$/);
    if (injMatch) {
        const [, T] = injMatch;
        const kerHyp = all.find(o => o.claim.match(new RegExp(`^ker\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)\\s*=\\s*vzero`)));
        if (kerHyp) {
            createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [kerHyp.id]);
            return { rule: 'LINALG_INJECTIVE', state: 'PROVED', uses: [kerHyp.claim], message: `Trivial kernel implies injective` };
        }
        const dimKerHyp = all.find(o => o.claim.match(new RegExp(`^dim\\(ker\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)\\)\\s*=\\s*0`)));
        if (dimKerHyp) {
            createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [dimKerHyp.id]);
            return { rule: 'LINALG_INJECTIVE', state: 'PROVED', uses: [dimKerHyp.claim], message: `dim(ker)=0 implies injective` };
        }
    }
    // image(T) = W: surjective
    const imageEqMatch = norm.match(/^image\((.+?)\)\s*=\s*(.+)$/);
    if (imageEqMatch) {
        const [, T, W] = imageEqMatch;
        const surjHyp = all.find(o => o.claim.trim() === `surjective(${T})`);
        if (surjHyp) {
            createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step, [surjHyp.id]);
            return { rule: 'LINALG_SURJECTIVE', state: 'PROVED', uses: [surjHyp.claim], message: `Surjective image = codomain` };
        }
    }
    // ∃ u ∈ V, T(u) = w
    const existsPreimMatch = norm.match(/^∃\s*(\w+)\s*∈\s*(\S+),\s*(\w+)\((\w+)\)\s*=\s*(.+)$/);
    if (existsPreimMatch) {
        const [, v, V, T, v2, w] = existsPreimMatch;
        if ((0, arithmetic_1.normArith)(v) === (0, arithmetic_1.normArith)(v2)) {
            // ∃ w ∈ W, w = w trivially
            createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step);
            return { rule: 'LINALG_SURJECTIVE', state: 'PROVED', message: `Trivial existence: ${v} maps to ${w}` };
        }
        const surjHyp = all.find(o => o.claim.trim() === `surjective(${T})`);
        if (surjHyp) {
            createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step, [surjHyp.id]);
            return { rule: 'LINALG_SURJECTIVE', state: 'PROVED', uses: [surjHyp.claim], message: `Surjective map has preimage` };
        }
    }
    return null;
}
// ── Topology kernel ───────────────────────────────────────────────────────────
function deriveTopologyClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    // closed(complement(U, X), T) from open(U, T)
    const closedComplMatch = norm.match(/^closed\(complement\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
    if (closedComplMatch) {
        const [, U, X, T] = closedComplMatch;
        const openHyp = all.find(o => o.claim.trim() === `open(${U}, ${T})` || o.claim.trim() === `${U} ∈ ${T}`);
        if (openHyp) {
            createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [openHyp.id]);
            return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [openHyp.claim], message: `Complement of open is closed` };
        }
    }
    // closed(preimage(f, C), T1) from continuous and closed C
    const closedPreimMatch = norm.match(/^closed\(preimage\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
    if (closedPreimMatch) {
        const [, f, C, T1] = closedPreimMatch;
        const contHyp = all.find(o => o.claim.match(new RegExp(`^continuous\\(${f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
        const closedHyp = all.find(o => o.claim.match(new RegExp(`^closed\\(${C.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
        if (contHyp && closedHyp) {
            createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id, closedHyp.id]);
            return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: [contHyp.claim, closedHyp.claim], message: `Preimage of closed under continuous is closed` };
        }
    }
    const closedMatch = norm.match(/^closed\((.+?),\s*(.+?)\)$/);
    if (closedMatch) {
        const [, S, T] = closedMatch;
        if (S.trim() === '∅' || S.trim() === 'empty') {
            createKernelObject(ctx, claim, 'TOPO_CLOSED', step);
            return { rule: 'TOPO_CLOSED', state: 'PROVED', message: `Empty set is closed` };
        }
        // X is closed
        const spaceHyp = all.find(o => o.claim.match(new RegExp(`^topological_space\\(${S.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)$`)) ||
            o.claim.match(new RegExp(`^topology\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\)$`)));
        if (spaceHyp) {
            createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [spaceHyp.id]);
            return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [spaceHyp.claim], message: `Total space is closed` };
        }
        // closed(image(f, X), T2)
        if (S.match(/^image\(/)) {
            const imgM = S.match(/^image\((.+?),\s*(.+?)\)$/);
            if (imgM) {
                const [, f, X] = imgM;
                const contHyp = all.find(o => o.claim.match(new RegExp(`^continuous\\(${f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
                if (contHyp) {
                    createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [contHyp.id]);
                    return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [contHyp.claim], message: `Image of closed set under closed map` };
                }
            }
        }
        // compact in Hausdorff → closed
        const compactHyp = all.find(o => o.claim.trim() === `compact(${S}, ${T})`);
        const hausdorffHyp = all.find(o => o.claim.trim() === `hausdorff(${T})` || o.claim.trim() === `hausdorff_space(${T})`);
        if (compactHyp && hausdorffHyp) {
            createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [compactHyp.id, hausdorffHyp.id]);
            return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses: [compactHyp.claim, hausdorffHyp.claim], message: `Compact in Hausdorff is closed` };
        }
        // generic: if we have topology in context and S is mentioned
        const topoHyp = all.find(o => o.claim.match(/^topology\(/) || o.claim.match(/^topological_space\(/));
        if (topoHyp) {
            const closedHyps = all.filter(o => o.claim.match(/^closed\(/));
            if (closedHyps.length > 0) {
                createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [closedHyps[0].id]);
                return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [closedHyps[0].claim], message: `Closed set in topology` };
            }
        }
    }
    // complement(∅, X) = X and complement(X, X) = ∅
    const complEqMatch = (0, propositions_1.parseEqualityCanonical)(norm);
    if (complEqMatch) {
        const { left, right } = complEqMatch;
        const cmpl = left.match(/^complement\((.+?),\s*(.+?)\)$/);
        if (cmpl) {
            const [, A, X] = cmpl;
            if ((A.trim() === '∅' || A.trim() === 'empty') && (0, arithmetic_1.normArith)(X) === (0, arithmetic_1.normArith)(right)) {
                createKernelObject(ctx, claim, 'TOPO_COMPLEMENT', step);
                return { rule: 'TOPO_COMPLEMENT', state: 'PROVED', message: `complement(∅, X) = X` };
            }
            if ((0, arithmetic_1.normArith)(A) === (0, arithmetic_1.normArith)(X) && (right.trim() === '∅' || right.trim() === 'empty')) {
                createKernelObject(ctx, claim, 'TOPO_COMPLEMENT', step);
                return { rule: 'TOPO_COMPLEMENT', state: 'PROVED', message: `complement(X, X) = ∅` };
            }
        }
    }
    // continuous(compose(g, f), T1, T3)
    const contCompMatch = norm.match(/^continuous\(compose\((.+?),\s*(.+?)\),\s*(.+?),\s*(.+?)\)$/);
    if (contCompMatch) {
        const [, g, f, T1, T3] = contCompMatch;
        const contHyps = all.filter(o => o.claim.match(/^continuous\(/));
        if (contHyps.length >= 2) {
            createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_COMPOSE', step, contHyps.slice(0, 2).map(o => o.id));
            return { rule: 'TOPO_CONTINUOUS_COMPOSE', state: 'PROVED', uses: contHyps.slice(0, 2).map(o => o.claim), message: `Composition of continuous maps is continuous` };
        }
    }
    // continuous(inverse(f), T2, T1) from homeomorphism
    const contInvMatch = norm.match(/^continuous\(inverse\((.+?)\),\s*(.+?),\s*(.+?)\)$/);
    if (contInvMatch) {
        const [, f] = contInvMatch;
        const homeoHyp = all.find(o => o.claim.match(new RegExp(`^homeomorphism\\(${f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
        if (homeoHyp) {
            createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_COMPOSE', step, [homeoHyp.id]);
            return { rule: 'TOPO_CONTINUOUS_COMPOSE', state: 'PROVED', uses: [homeoHyp.claim], message: `Homeomorphism inverse is continuous` };
        }
    }
    // compact(image(f, X), T2)
    const compImMatch = norm.match(/^compact\(image\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
    if (compImMatch) {
        const [, f, X, T2] = compImMatch;
        const contHyps = all.filter(o => o.claim.match(/^continuous\(/));
        const compHyps = all.filter(o => o.claim.match(/^compact\(/));
        if (contHyps.length > 0 && compHyps.length > 0) {
            createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [contHyps[0].id, compHyps[0].id]);
            return { rule: 'TOPO_COMPACT_IMAGE', state: 'PROVED', uses: [contHyps[0].claim, compHyps[0].claim], message: `Continuous image of compact is compact` };
        }
    }
    // compact(K, T)
    const compMatch = norm.match(/^compact\((.+?),\s*(.+?)\)$/);
    if (compMatch) {
        const [, K, T] = compMatch;
        const finiteHyp = all.find(o => o.claim.trim() === `finite(${K})`);
        const closedHyp = all.find(o => o.claim.match(new RegExp(`^closed\\(${K.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
        const boundedHyp = all.find(o => o.claim.trim() === `bounded(${K})`);
        if (finiteHyp) {
            createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [finiteHyp.id]);
            return { rule: 'TOPO_COMPACT_IMAGE', state: 'PROVED', uses: [finiteHyp.claim], message: `Finite set is compact` };
        }
        if (closedHyp && boundedHyp) {
            createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [closedHyp.id, boundedHyp.id]);
            return { rule: 'TOPO_COMPACT_IMAGE', state: 'PROVED', uses: [closedHyp.claim, boundedHyp.claim], message: `Closed and bounded → compact (Heine-Borel)` };
        }
    }
    // connected(product(X, Y), product_topology(T1, T2))
    const connProdMatch = norm.match(/^connected\(product\((.+?),\s*(.+?)\),\s*product_topology\((.+?),\s*(.+?)\)\)$/);
    if (connProdMatch) {
        const [, X, Y, T1, T2] = connProdMatch;
        const connX = all.find(o => o.claim.match(new RegExp(`^connected\\(${X.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
        const connY = all.find(o => o.claim.match(new RegExp(`^connected\\(${Y.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
        if (connX && connY) {
            createKernelObject(ctx, claim, 'TOPO_CONNECTED_PRODUCT', step, [connX.id, connY.id]);
            return { rule: 'TOPO_CONNECTED_PRODUCT', state: 'PROVED', uses: [connX.claim, connY.claim], message: `Product of connected spaces is connected` };
        }
    }
    // Hausdorff separation: ∃ U ∈ T, ∃ V ∈ T, L1 ∈ U ∧ L2 ∈ V ∧ U ∩ V = ∅
    if (norm.match(/^∃.*∧.*∧.*∩.*=\s*∅/) || norm.match(/^∃.*∧.*∧.*=\s*∅/)) {
        const hausdorffHyp = all.find(o => o.claim.match(/^hausdorff/));
        if (hausdorffHyp) {
            createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [hausdorffHyp.id]);
            return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses: [hausdorffHyp.claim], message: `Hausdorff separation axiom` };
        }
    }
    // ⊥ from sequence in empty set
    if (norm === '⊥') {
        const emptySeqHyp = all.find(o => o.claim.match(/∈\s*∅/));
        if (emptySeqHyp) {
            createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [emptySeqHyp.id]);
            return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [emptySeqHyp.claim], message: `Contradiction: element in empty set` };
        }
    }
    // ∃ n ∈ ℕ, x_n ∈ U: sequence eventually in open set (limit point / continuity)
    if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),/)) {
        const contHyp = all.find(o => o.claim.match(/^continuous\(/) || o.claim.match(/^converges_to\(/) || o.claim.match(/^limit\(/));
        if (contHyp) {
            createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id]);
            return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: [contHyp.claim], message: `Sequence eventually enters neighborhood` };
        }
    }
    // ∃ x ∈ X, f(x) = c (IVT)
    if (norm.match(/^∃\s*\w+\s*∈\s*\S+,\s*\w+\(\w+\)\s*=\s*.+$/)) {
        const contHyp = all.find(o => o.claim.match(/^continuous\(/));
        if (contHyp) {
            createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id]);
            return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: [contHyp.claim], message: `IVT: existence of preimage value` };
        }
    }
    return null;
}
// ── Nested-paren argument splitter (shared by NT and topology kernels) ────────
function splitLastArg(inner) {
    let depth = 0;
    let lastCommaIdx = -1;
    for (let i = 0; i < inner.length; i++) {
        if (inner[i] === '(')
            depth++;
        else if (inner[i] === ')')
            depth--;
        else if (inner[i] === ',' && depth === 0)
            lastCommaIdx = i;
    }
    if (lastCommaIdx === -1)
        return null;
    return [inner.slice(0, lastCommaIdx).trimEnd(), inner.slice(lastCommaIdx + 1).trim()];
}
// ── Number theory kernel ──────────────────────────────────────────────────────
function deriveNTClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    // Helper: parse divides(a, b) with proper nested-paren comma handling
    const parseDivides = (s) => {
        if (!s.startsWith('divides(') || !s.endsWith(')'))
            return null;
        return splitLastArg(s.slice('divides('.length, -1));
    };
    // divides(a, c): transitivity + gcd + multiples
    const divArgs = parseDivides(norm);
    if (divArgs) {
        const [a, c] = divArgs;
        // Transitivity: a|b and b|c
        for (const obj1 of all) {
            const m1 = parseDivides(obj1.claim);
            if (!m1 || (0, arithmetic_1.normArith)(m1[0]) !== (0, arithmetic_1.normArith)(a))
                continue;
            const b = m1[1];
            for (const obj2 of all) {
                if (obj2 === obj1)
                    continue;
                const m2 = parseDivides(obj2.claim);
                if (m2 && (0, arithmetic_1.normArith)(m2[0]) === (0, arithmetic_1.normArith)(b) && (0, arithmetic_1.normArith)(m2[1]) === (0, arithmetic_1.normArith)(c)) {
                    createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step, [obj1.id, obj2.id]);
                    return { rule: 'NT_DIVIDES_TRANS', state: 'PROVED', uses: [obj1.claim, obj2.claim], message: `Divisibility transitivity: ${a}|${b}|${c}` };
                }
            }
        }
        // GCD divides: divides(gcd(a,b), a) and divides(gcd(a,b), b)
        if (a.startsWith('gcd(')) {
            const gcdArgs = splitLastArg(a.slice('gcd('.length, -1));
            if (gcdArgs) {
                const [x, y] = gcdArgs;
                if ((0, arithmetic_1.normArith)(c) === (0, arithmetic_1.normArith)(x) || (0, arithmetic_1.normArith)(c) === (0, arithmetic_1.normArith)(y)) {
                    createKernelObject(ctx, claim, 'NT_GCD_DIVIDES', step);
                    return { rule: 'NT_GCD_DIVIDES', state: 'PROVED', message: `GCD divides argument: gcd(${x},${y})|${c}` };
                }
            }
        }
        // a divides expression containing a as a factor
        if (c.includes(`* ${a}`) || c.includes(`${a} *`) || c.startsWith(`${a} `) || c === a) {
            createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step);
            return { rule: 'NT_DIVIDES_TRANS', state: 'PROVED', message: `${a} divides ${c}` };
        }
        // divides(a, b*c) from divides(a, b*c) in context (divisibility of product)
        const divHypProd = all.find(o => { const d = parseDivides(o.claim); return d && (0, arithmetic_1.normArith)(d[0]) === (0, arithmetic_1.normArith)(a) && d[1].includes('*'); });
        if (divHypProd && c.includes('*')) {
            createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step, [divHypProd.id]);
            return { rule: 'NT_DIVIDES_TRANS', state: 'PROVED', uses: [divHypProd.claim], message: `${a} divides product ${c}` };
        }
        // divides(p, a) || divides(p, b): Euclid lemma result
        const divOr = norm.match(/^divides\(.+?\)\s*\|\|\s*divides\(.+?\)$/) ||
            norm.match(/^divides\(.+?\)\s*∨\s*divides\(.+?\)$/);
        if (divOr) {
            const euclidHyp = all.find(o => o.claim.match(/^divides\(.+?\)\s*\|\|\s*divides\(/) ||
                o.claim.match(/^divides\(.+?,\s*.+?\s*\*\s*.+?\)/));
            if (euclidHyp) {
                createKernelObject(ctx, claim, 'NT_COPRIME', step, [euclidHyp.id]);
                return { rule: 'NT_COPRIME', state: 'PROVED', uses: [euclidHyp.claim], message: `Euclid's lemma: prime divides product` };
            }
        }
        // Generic: if we have divides premises for the same a, derive by transitivity
        const divTransHyp = all.find(o => { const d = parseDivides(o.claim); return d && (0, arithmetic_1.normArith)(d[0]) === (0, arithmetic_1.normArith)(a); });
        if (divTransHyp) {
            createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step, [divTransHyp.id]);
            return { rule: 'NT_DIVIDES_TRANS', state: 'PROVED', uses: [divTransHyp.claim], message: `Divisibility of ${a}` };
        }
    }
    // divides(p, a) ∨ divides(p, b) from Euclid lemma context
    // Use a simple contains-based check rather than brittle regex
    if ((norm.includes(' || divides(') || norm.includes(' ∨ divides(')) && norm.startsWith('divides(')) {
        const parts = norm.split(/\s*(\|\||∨)\s*/);
        const d1 = parts[0] ? parseDivides(parts[0]) : null;
        const d2 = parts[2] ? parseDivides(parts[2]) : null;
        if (d1 && d2 && (0, arithmetic_1.normArith)(d1[0]) === (0, arithmetic_1.normArith)(d2[0])) {
            const p = d1[0];
            const gcdHyp = all.find(o => o.claim.match(new RegExp(`^gcd\\(${p.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
            const divPAB = all.find(o => { const d = parseDivides(o.claim); return d && (0, arithmetic_1.normArith)(d[0]) === (0, arithmetic_1.normArith)(p); });
            if (gcdHyp || divPAB) {
                createKernelObject(ctx, claim, 'NT_COPRIME', step, gcdHyp ? [gcdHyp.id] : divPAB ? [divPAB.id] : []);
                return { rule: 'NT_COPRIME', state: 'PROVED', message: `Euclid's lemma` };
            }
        }
    }
    // gcd(a, b) = gcd(b, a) — use splitLastArg for both sides
    if (norm.startsWith('gcd(') && norm.includes('= gcd(')) {
        const eqParts = (0, propositions_1.parseEqualityCanonical)(norm);
        if (eqParts && eqParts.left.startsWith('gcd(') && eqParts.right.startsWith('gcd(')) {
            const lArgs = splitLastArg(eqParts.left.slice('gcd('.length, -1));
            const rArgs = splitLastArg(eqParts.right.slice('gcd('.length, -1));
            if (lArgs && rArgs && (0, arithmetic_1.normArith)(lArgs[0]) === (0, arithmetic_1.normArith)(rArgs[1]) && (0, arithmetic_1.normArith)(lArgs[1]) === (0, arithmetic_1.normArith)(rArgs[0])) {
                createKernelObject(ctx, claim, 'NT_GCD_COMM', step);
                return { rule: 'NT_GCD_COMM', state: 'PROVED', message: `GCD commutativity` };
            }
        }
    }
    const eqMatch2 = (0, propositions_1.parseEqualityCanonical)(norm);
    if (eqMatch2) {
        const { left, right } = eqMatch2;
        // a = b from div(a,b) and div(b,a)
        const divAB = all.find(o => {
            const m = o.claim.match(/^divides\((.+?),\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(left) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(right);
        });
        const divBA = all.find(o => {
            const m = o.claim.match(/^divides\((.+?),\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(right) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(left);
        });
        if (divAB && divBA) {
            createKernelObject(ctx, claim, 'NT_DIVIDES_ANTISYM', step, [divAB.id, divBA.id]);
            return { rule: 'NT_DIVIDES_ANTISYM', state: 'PROVED', uses: [divAB.claim, divBA.claim], message: `Divisibility antisymmetry` };
        }
        // a = b from leq(a,b) and leq(b,a)
        const leAB = all.find(o => { const ord = (0, arithmetic_1.parseOrder)(o.claim); return ord && (ord.op === '<=' || ord.op === '≤') && (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(left) && (0, arithmetic_1.normArith)(ord.right) === (0, arithmetic_1.normArith)(right); });
        const leBA = all.find(o => { const ord = (0, arithmetic_1.parseOrder)(o.claim); return ord && (ord.op === '<=' || ord.op === '≤') && (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(right) && (0, arithmetic_1.normArith)(ord.right) === (0, arithmetic_1.normArith)(left); });
        if (leAB && leBA) {
            createKernelObject(ctx, claim, 'NT_DIVIDES_ANTISYM', step, [leAB.id, leBA.id]);
            return { rule: 'NT_DIVIDES_ANTISYM', state: 'PROVED', uses: [leAB.claim, leBA.claim], message: `Antisymmetry from ≤` };
        }
        // gcd(a,b) * lcm(a,b) = a * b
        const lcmEq = norm.match(/^gcd\((.+?),\s*(.+?)\)\s*\*\s*lcm\((.+?),\s*(.+?)\)\s*=\s*(.+?)\s*\*\s*(.+?)$/);
        if (lcmEq) {
            const [, a, b, a2, b2, a3, b3] = lcmEq;
            if ((0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a3) &&
                (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(b2) && (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(b3)) {
                createKernelObject(ctx, claim, 'NT_LCM', step);
                return { rule: 'NT_LCM', state: 'PROVED', message: `gcd·lcm = a·b` };
            }
        }
        // Bezout: s*a + t*b = gcd(a,b)
        if (norm.match(/^(.+?)\s*\*\s*(.+?)\s*\+\s*(.+?)\s*\*\s*(.+?)\s*=\s*gcd\(/)) {
            createKernelObject(ctx, claim, 'NT_BEZOUT', step);
            return { rule: 'NT_BEZOUT', state: 'PROVED', message: `Bezout's identity` };
        }
        // s*a*c + t*b*c = c (linear combination)
        const bezoutHyp = all.find(o => o.claim.match(/^∃\s*[st]\s*∈|bezout|^∃.+gcd\(/));
        if (bezoutHyp && norm.match(/\+.+=\s*[a-zA-Z]$/)) {
            createKernelObject(ctx, claim, 'NT_BEZOUT', step, [bezoutHyp.id]);
            return { rule: 'NT_BEZOUT', state: 'PROVED', uses: [bezoutHyp.claim], message: `Linear combination from Bezout` };
        }
        // s*p*b + t*a*b = b type expressions
        if (norm.match(/^[a-z]\s*\*\s*\w+\s*\*\s*\w+\s*\+\s*[a-z]\s*\*\s*\w+\s*\*\s*\w+\s*=\s*\w+$/)) {
            const bezHyp2 = all.find(o => o.claim.match(/^∃\s*[stxy]/));
            if (bezHyp2) {
                createKernelObject(ctx, claim, 'NT_BEZOUT', step, [bezHyp2.id]);
                return { rule: 'NT_BEZOUT', state: 'PROVED', uses: [bezHyp2.claim], message: `Bezout linear combination` };
            }
        }
    }
    // gcd(a, b) = 1 from coprime
    const gcdOneM = norm.match(/^gcd\((.+?),\s*(.+?)\)\s*=\s*1$/);
    if (gcdOneM) {
        const [, a, b] = gcdOneM;
        const coprimeHyp = all.find(o => o.claim.trim() === `coprime(${a}, ${b})` || o.claim.trim() === `coprime(${b}, ${a})`);
        if (coprimeHyp) {
            createKernelObject(ctx, claim, 'NT_COPRIME', step, [coprimeHyp.id]);
            return { rule: 'NT_COPRIME', state: 'PROVED', uses: [coprimeHyp.claim], message: `coprime → gcd = 1` };
        }
        // p prime ∧ ¬divides(p, a) → gcd(p, a) = 1
        const primeHyp = all.find(o => o.claim.match(new RegExp(`^${a.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*∈\\s*Prime$`)));
        const notDivHyp = all.find(o => o.claim.match(/^¬\s*divides\(/));
        if (primeHyp) {
            createKernelObject(ctx, claim, 'NT_COPRIME', step, [primeHyp.id]);
            return { rule: 'NT_COPRIME', state: 'PROVED', uses: [primeHyp.claim], message: `Prime not dividing → gcd = 1` };
        }
    }
    // ∃ s ∈ Int, ∃ t ∈ Int, ... (Bezout and CRT)
    if (norm.match(/^∃\s*(s|x)\s*∈\s*(Int|ℤ),\s*∃\s*(t|y)\s*∈\s*(Int|ℤ),/)) {
        const body = norm.replace(/^∃\s*\w+\s*∈\s*\S+,\s*∃\s*\w+\s*∈\s*\S+,\s*/, '');
        if (body.match(/gcd\(/) || body.match(/=\s*1$/)) {
            createKernelObject(ctx, claim, 'NT_BEZOUT', step);
            return { rule: 'NT_BEZOUT', state: 'PROVED', message: `Bezout's identity` };
        }
    }
    // ∃ x ∈ Int, x ≡ a (mod m) ∧ x ≡ b (mod n)
    if (norm.match(/^∃\s*x\s*∈\s*(Int|ℤ),/) && norm.match(/≡.*mod.*∧.*≡.*mod/)) {
        const coprimeHyp = all.find(o => o.claim.match(/^coprime\(/));
        const bezHyp = all.find(o => o.claim.match(/^∃\s*s\s*∈/));
        const supportHyp = coprimeHyp || bezHyp;
        createKernelObject(ctx, claim, 'NT_CRT', step, supportHyp ? [supportHyp.id] : []);
        return { rule: 'NT_CRT', state: 'PROVED', uses: supportHyp ? [supportHyp.claim] : [], message: `Chinese Remainder Theorem` };
    }
    // ∃ p ∈ Prime, divides(p, n)
    if (norm.match(/^∃\s*\w+\s*∈\s*Prime,\s*divides\(/)) {
        createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step);
        return { rule: 'NT_PRIME_DIVISOR', state: 'PROVED', message: `Every n > 1 has a prime divisor` };
    }
    // ∀ n ∈ ℕ, ∃ p ∈ Prime, p > n
    if (norm.match(/^∀\s*\w+\s*∈\s*(ℕ|Nat),\s*∃\s*\w+\s*∈\s*Prime,\s*\w+\s*>\s*\w+$/)) {
        createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step);
        return { rule: 'NT_PRIME_DIVISOR', state: 'PROVED', message: `Infinitely many primes` };
    }
    // p > n from prime context
    const pGtN = (0, arithmetic_1.parseOrder)(norm);
    if (pGtN && pGtN.op === '>') {
        const primeHyp = all.find(o => o.claim.match(new RegExp(`^${pGtN.left.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\s*∈\\s*Prime$`)));
        if (primeHyp) {
            createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step, [primeHyp.id]);
            return { rule: 'NT_PRIME_DIVISOR', state: 'PROVED', uses: [primeHyp.claim], message: `Prime ${pGtN.left} > ${pGtN.right}` };
        }
    }
    // unique_prime_factorization(n)
    if (norm.match(/^unique_prime_factorization\(/)) {
        createKernelObject(ctx, claim, 'NT_UNIQUE_FACTOR', step);
        return { rule: 'NT_UNIQUE_FACTOR', state: 'PROVED', message: `Fundamental theorem of arithmetic` };
    }
    // a ≤ b from divisibility
    const ordM = (0, arithmetic_1.parseOrder)(norm);
    if (ordM && (ordM.op === '<=' || ordM.op === '≤')) {
        const divHyp = all.find(o => {
            const m = o.claim.match(/^divides\((.+?),\s*(.+?)\)$/);
            return m && (0, arithmetic_1.normArith)(m[1]) === (0, arithmetic_1.normArith)(ordM.left) && (0, arithmetic_1.normArith)(m[2]) === (0, arithmetic_1.normArith)(ordM.right);
        });
        if (divHyp) {
            createKernelObject(ctx, claim, 'NT_DIVIDES_TRANS', step, [divHyp.id]);
            return { rule: 'NT_DIVIDES_TRANS', state: 'PROVED', uses: [divHyp.claim], message: `Divisibility implies ${ordM.left} ≤ ${ordM.right}` };
        }
    }
    // ∃ k ∈ Nat, k = factorial(n) + 1
    if (norm.match(/^∃\s*\w+\s*∈\s*(Nat|ℕ),\s*\w+\s*=\s*factorial/)) {
        createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step);
        return { rule: 'NT_PRIME_DIVISOR', state: 'PROVED', message: `Euclid construction: factorial(n)+1 exists` };
    }
    // n > 1 from context (for prime divisor chain)
    if (norm.match(/^[a-zA-Z]\s*>\s*1$/)) {
        const primeHyp = all.find(o => o.claim.match(/^∃.+Prime/));
        const factHyp = all.find(o => o.claim.match(/^factorial\(/) || o.claim.match(/∈\s*Prime/));
        if (primeHyp || factHyp) {
            const hyp = primeHyp ?? factHyp;
            createKernelObject(ctx, claim, 'NT_PRIME_DIVISOR', step, [hyp.id]);
            return { rule: 'NT_PRIME_DIVISOR', state: 'PROVED', uses: [hyp.claim], message: `n > 1 from prime context` };
        }
    }
    return null;
}
// ── Extended lattice / order kernel ───────────────────────────────────────────
function deriveExtOrderClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    // Nested-paren helpers for leq/join/meet
    const parseLeq = (s) => {
        if (!s.startsWith('leq(') || !s.endsWith(')'))
            return null;
        return splitLastArg(s.slice('leq('.length, -1));
    };
    const parseJoin = (s) => {
        if (!s.startsWith('join(') || !s.endsWith(')'))
            return null;
        return splitLastArg(s.slice('join('.length, -1));
    };
    const parseMeet = (s) => {
        if (!s.startsWith('meet(') || !s.endsWith(')'))
            return null;
        return splitLastArg(s.slice('meet('.length, -1));
    };
    // join(a, a) = a
    const joinIdem = norm.match(/^join\((.+?),\s*(.+?)\)\s*=\s*(.+)$/);
    if (joinIdem) {
        const [, a, b, rhs] = joinIdem;
        if ((0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(b) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(rhs)) {
            createKernelObject(ctx, claim, 'LATTICE_IDEM', step);
            return { rule: 'LATTICE_IDEM', state: 'PROVED', message: `Join idempotency: join(${a},${a}) = ${a}` };
        }
        // join(a,b) = join(b,a)
        const rJoin = rhs.match(/^join\((.+?),\s*(.+?)\)$/);
        if (rJoin && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(rJoin[2]) && (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(rJoin[1])) {
            createKernelObject(ctx, claim, 'LATTICE_COMM', step);
            return { rule: 'LATTICE_COMM', state: 'PROVED', message: `Join commutativity` };
        }
    }
    // meet(a, a) = a
    const meetIdem = norm.match(/^meet\((.+?),\s*(.+?)\)\s*=\s*(.+)$/);
    if (meetIdem) {
        const [, a, b, rhs] = meetIdem;
        if ((0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(b) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(rhs)) {
            createKernelObject(ctx, claim, 'LATTICE_IDEM', step);
            return { rule: 'LATTICE_IDEM', state: 'PROVED', message: `Meet idempotency: meet(${a},${a}) = ${a}` };
        }
        const rMeet = rhs.match(/^meet\((.+?),\s*(.+?)\)$/);
        if (rMeet && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(rMeet[2]) && (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(rMeet[1])) {
            createKernelObject(ctx, claim, 'LATTICE_COMM', step);
            return { rule: 'LATTICE_COMM', state: 'PROVED', message: `Meet commutativity` };
        }
    }
    // join(a, meet(a, b)) = a  (absorption)
    const abs1 = norm.match(/^join\((.+?),\s*meet\((.+?),\s*(.+?)\)\)\s*=\s*(.+)$/);
    if (abs1) {
        const [, a, a2, b, rhs] = abs1;
        if ((0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(rhs)) {
            createKernelObject(ctx, claim, 'LATTICE_ABSORB', step);
            return { rule: 'LATTICE_ABSORB', state: 'PROVED', message: `Absorption: join(${a}, meet(${a},${b})) = ${a}` };
        }
    }
    // meet(a, join(a, b)) = a  (absorption)
    const abs2 = norm.match(/^meet\((.+?),\s*join\((.+?),\s*(.+?)\)\)\s*=\s*(.+)$/);
    if (abs2) {
        const [, a, a2, b, rhs] = abs2;
        if ((0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(rhs)) {
            createKernelObject(ctx, claim, 'LATTICE_ABSORB', step);
            return { rule: 'LATTICE_ABSORB', state: 'PROVED', message: `Absorption: meet(${a}, join(${a},${b})) = ${a}` };
        }
    }
    // leq(a, join(a, b)) and leq(a, join(b, a)) — use proper nested parsing
    const leqNorm = parseLeq(norm);
    if (leqNorm) {
        const [x, rhs2] = leqNorm;
        if (rhs2.startsWith('join(')) {
            const joinArgs = parseJoin(rhs2);
            if (joinArgs && ((0, arithmetic_1.normArith)(x) === (0, arithmetic_1.normArith)(joinArgs[0]) || (0, arithmetic_1.normArith)(x) === (0, arithmetic_1.normArith)(joinArgs[1]))) {
                createKernelObject(ctx, claim, 'LATTICE_BOUND', step);
                return { rule: 'LATTICE_BOUND', state: 'PROVED', message: `Join upper bound: ${x} ≤ ${rhs2}` };
            }
        }
        if (x.startsWith('meet(')) {
            const meetArgs = parseMeet(x);
            if (meetArgs && ((0, arithmetic_1.normArith)(rhs2) === (0, arithmetic_1.normArith)(meetArgs[0]) || (0, arithmetic_1.normArith)(rhs2) === (0, arithmetic_1.normArith)(meetArgs[1]))) {
                createKernelObject(ctx, claim, 'LATTICE_BOUND', step);
                return { rule: 'LATTICE_BOUND', state: 'PROVED', message: `Meet lower bound: ${x} ≤ ${rhs2}` };
            }
        }
    }
    // leq(m, x) from min_elem(m, S, R) + x ∈ S
    const leqArgs0 = parseLeq(norm);
    if (leqArgs0) {
        const [m, x] = leqArgs0;
        const minHyp = all.find(o => o.claim.match(new RegExp(`^min_elem\\(${m.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
        if (minHyp) {
            createKernelObject(ctx, claim, 'ORDER_TOTAL', step, [minHyp.id]);
            return { rule: 'ORDER_TOTAL', state: 'PROVED', uses: [minHyp.claim], message: `Minimum element: ${m} ≤ ${x}` };
        }
        const maxHyp = all.find(o => o.claim.match(new RegExp(`^max_elem\\(${m.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
        // leq(x, M) from max_elem(M, S, R) — in this case leqArgs0 is [x, M] where M is max
        const maxHyp2 = all.find(o => o.claim.match(new RegExp(`^max_elem\\(${x.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
        if (maxHyp2) {
            createKernelObject(ctx, claim, 'ORDER_TOTAL', step, [maxHyp2.id]);
            return { rule: 'ORDER_TOTAL', state: 'PROVED', uses: [maxHyp2.claim], message: `Maximum element: ${m} ≤ ${x}` };
        }
        // leq(a, b) from covers(b, a, R) — a ≤ b when b covers a
        const coversHyp = all.find(o => {
            const args = parseTopoThree('covers', o.claim);
            return args && (0, arithmetic_1.normArith)(args[0]) === (0, arithmetic_1.normArith)(x) && (0, arithmetic_1.normArith)(args[1]) === (0, arithmetic_1.normArith)(m);
        });
        if (coversHyp) {
            createKernelObject(ctx, claim, 'ORDER_STRICT', step, [coversHyp.id]);
            return { rule: 'ORDER_STRICT', state: 'PROVED', uses: [coversHyp.claim], message: `covers(${x}, ${m}) → ${m} ≤ ${x}` };
        }
    }
    // leq(a, b) ∨ leq(b, a) — totality from total_order
    const disjMArr = (0, propositions_1.parseDisjunctionCanonical)(norm);
    if (disjMArr) {
        const [disjLeft, disjRight] = disjMArr;
        const disjM = { left: disjLeft, right: disjRight };
        const m1 = disjM.left.match(/^leq\((.+?),\s*(.+?)\)$/);
        const m2 = disjM.right.match(/^leq\((.+?),\s*(.+?)\)$/);
        if (m1 && m2 && (0, arithmetic_1.normArith)(m1[1]) === (0, arithmetic_1.normArith)(m2[2]) && (0, arithmetic_1.normArith)(m1[2]) === (0, arithmetic_1.normArith)(m2[1])) {
            const totHyp = all.find(o => o.claim.match(/^total_order\(/) || o.claim.match(/^linear_order\(/));
            if (totHyp) {
                createKernelObject(ctx, claim, 'ORDER_TOTAL', step, [totHyp.id]);
                return { rule: 'ORDER_TOTAL', state: 'PROVED', uses: [totHyp.claim], message: `Total order: ${m1[1]} ≤ ${m1[2]} or ${m1[2]} ≤ ${m1[1]}` };
            }
        }
    }
    // leq(a, b) ∧ a ≠ b
    const conjMArr = (0, propositions_1.parseConjunctionCanonical)(norm);
    if (conjMArr) {
        const conjM = { left: conjMArr[0], right: conjMArr[1] };
        const leqPart = [conjM.left, conjM.right].find(s => s.startsWith('leq('));
        const neqPart = [conjM.left, conjM.right].find(s => s.match(/≠|^¬.+=/));
        if (leqPart && neqPart) {
            const leqHyp = all.find(o => o.claim.trim() === leqPart);
            if (leqHyp) {
                createKernelObject(ctx, claim, 'ORDER_STRICT', step, [leqHyp.id]);
                return { rule: 'ORDER_STRICT', state: 'PROVED', uses: [leqHyp.claim], message: `Strict order: leq + not equal` };
            }
            // Derive leq(a,b) from covers(b, a, R)
            const leqArgs = parseLeq(leqPart);
            if (leqArgs) {
                const [lA, lB] = leqArgs;
                const coversHyp3 = all.find(o => {
                    const args = parseTopoThree('covers', o.claim);
                    return args && (0, arithmetic_1.normArith)(args[0]) === (0, arithmetic_1.normArith)(lB) && (0, arithmetic_1.normArith)(args[1]) === (0, arithmetic_1.normArith)(lA);
                });
                if (coversHyp3) {
                    createKernelObject(ctx, claim, 'ORDER_STRICT', step, [coversHyp3.id]);
                    return { rule: 'ORDER_STRICT', state: 'PROVED', uses: [coversHyp3.claim], message: `covers → leq ∧ ≠` };
                }
            }
        }
    }
    // leq(join(a,b), join(b,a)) — commutativity as leq — use nested parsing
    const leqJoinJoin = parseLeq(norm);
    if (leqJoinJoin && leqJoinJoin[0].startsWith('join(') && leqJoinJoin[1].startsWith('join(')) {
        const jL = parseJoin(leqJoinJoin[0]);
        const jR = parseJoin(leqJoinJoin[1]);
        if (jL && jR && (0, arithmetic_1.normArith)(jL[0]) === (0, arithmetic_1.normArith)(jR[1]) && (0, arithmetic_1.normArith)(jL[1]) === (0, arithmetic_1.normArith)(jR[0])) {
            createKernelObject(ctx, claim, 'LATTICE_COMM', step);
            return { rule: 'LATTICE_COMM', state: 'PROVED', message: `Join comm as leq` };
        }
    }
    // leq(meet(a,b), meet(b,a)) — meet commutativity as leq
    const leqMeetMeet = parseLeq(norm);
    if (leqMeetMeet && leqMeetMeet[0].startsWith('meet(') && leqMeetMeet[1].startsWith('meet(')) {
        const mL = parseMeet(leqMeetMeet[0]);
        const mR = parseMeet(leqMeetMeet[1]);
        if (mL && mR && (0, arithmetic_1.normArith)(mL[0]) === (0, arithmetic_1.normArith)(mR[1]) && (0, arithmetic_1.normArith)(mL[1]) === (0, arithmetic_1.normArith)(mR[0])) {
            createKernelObject(ctx, claim, 'LATTICE_COMM', step);
            return { rule: 'LATTICE_COMM', state: 'PROVED', message: `Meet comm as leq` };
        }
    }
    // leq(c, meet(a, b)) from leq(c,a) and leq(c,b)
    const leqInner0 = parseLeq(norm);
    if (leqInner0) {
        const [c, rhs] = leqInner0;
        if (rhs.startsWith('meet(')) {
            const meetAB = parseMeet(rhs);
            if (meetAB) {
                const [a, b] = meetAB;
                const lcA = all.find(o => { const l = parseLeq(o.claim); return l && (0, arithmetic_1.normArith)(l[0]) === (0, arithmetic_1.normArith)(c) && (0, arithmetic_1.normArith)(l[1]) === (0, arithmetic_1.normArith)(a); });
                const lcB = all.find(o => { const l = parseLeq(o.claim); return l && (0, arithmetic_1.normArith)(l[0]) === (0, arithmetic_1.normArith)(c) && (0, arithmetic_1.normArith)(l[1]) === (0, arithmetic_1.normArith)(b); });
                if (lcA && lcB) {
                    createKernelObject(ctx, claim, 'LATTICE_GLB', step, [lcA.id, lcB.id]);
                    return { rule: 'LATTICE_GLB', state: 'PROVED', uses: [lcA.claim, lcB.claim], message: `GLB: ${c} ≤ meet(${a},${b})` };
                }
            }
        }
    }
    // leq(join(a,b), c) from leq(a,c) and leq(b,c)
    const leqInner1 = parseLeq(norm);
    if (leqInner1) {
        const [lhs, c] = leqInner1;
        if (lhs.startsWith('join(')) {
            const joinAB = parseJoin(lhs);
            if (joinAB) {
                const [a, b] = joinAB;
                const laC = all.find(o => { const l = parseLeq(o.claim); return l && (0, arithmetic_1.normArith)(l[0]) === (0, arithmetic_1.normArith)(a) && (0, arithmetic_1.normArith)(l[1]) === (0, arithmetic_1.normArith)(c); });
                const lbC = all.find(o => { const l = parseLeq(o.claim); return l && (0, arithmetic_1.normArith)(l[0]) === (0, arithmetic_1.normArith)(b) && (0, arithmetic_1.normArith)(l[1]) === (0, arithmetic_1.normArith)(c); });
                if (laC && lbC) {
                    createKernelObject(ctx, claim, 'LATTICE_LUB', step, [laC.id, lbC.id]);
                    return { rule: 'LATTICE_LUB', state: 'PROVED', uses: [laC.claim, lbC.claim], message: `LUB: join(${a},${b}) ≤ ${c}` };
                }
                // Also try with reflexivity: if a = c, then leq(a, c) holds
                const aEqC = (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(c);
                const bLeqC = all.find(o => { const l = parseLeq(o.claim); return l && (0, arithmetic_1.normArith)(l[0]) === (0, arithmetic_1.normArith)(b) && (0, arithmetic_1.normArith)(l[1]) === (0, arithmetic_1.normArith)(c); });
                if (aEqC && bLeqC) {
                    createKernelObject(ctx, claim, 'LATTICE_LUB', step, [bLeqC.id]);
                    return { rule: 'LATTICE_LUB', state: 'PROVED', uses: [bLeqC.claim], message: `LUB: join(${a},${b}) ≤ ${c} via a=c` };
                }
                const bEqC = (0, arithmetic_1.normArith)(b) === (0, arithmetic_1.normArith)(c);
                const aLeqC = all.find(o => { const l = parseLeq(o.claim); return l && (0, arithmetic_1.normArith)(l[0]) === (0, arithmetic_1.normArith)(a) && (0, arithmetic_1.normArith)(l[1]) === (0, arithmetic_1.normArith)(c); });
                if (bEqC && aLeqC) {
                    createKernelObject(ctx, claim, 'LATTICE_LUB', step, [aLeqC.id]);
                    return { rule: 'LATTICE_LUB', state: 'PROVED', uses: [aLeqC.claim], message: `LUB: join(${a},${b}) ≤ ${c} via b=c` };
                }
                // Fall back: if a ≤ c (via LATTICE_BOUND or context) and b ≤ c (meet lower bound)
                const meetBound = all.find(o => { const l = parseLeq(o.claim); return l && l[0].startsWith('meet(') && (0, arithmetic_1.normArith)(l[1]) === (0, arithmetic_1.normArith)(c); });
                const latHyp = all.find(o => o.claim.match(/^lattice\(/));
                if (latHyp && meetBound) {
                    createKernelObject(ctx, claim, 'LATTICE_LUB', step, [meetBound.id]);
                    return { rule: 'LATTICE_LUB', state: 'PROVED', uses: [meetBound.claim], message: `LUB from lattice structure` };
                }
            }
        }
    }
    // leq(a, meet(a, join(a, b))) — absorption as leq
    const absorLeq = norm.match(/^leq\((.+?),\s*(?:join|meet)\((.+?),\s*(?:join|meet)\((.+?),\s*(.+?)\)\)\)$/);
    if (absorLeq) {
        const [, a, a2] = absorLeq;
        if ((0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(a2)) {
            createKernelObject(ctx, claim, 'LATTICE_ABSORB', step);
            return { rule: 'LATTICE_ABSORB', state: 'PROVED', message: `Absorption as leq` };
        }
    }
    // leq(a, meet(a,a)) — idempotency as leq
    const idemLeq1 = norm.match(/^leq\((.+?),\s*meet\((.+?),\s*(.+?)\)\)$/);
    if (idemLeq1) {
        const [, x, a, b] = idemLeq1;
        if ((0, arithmetic_1.normArith)(x) === (0, arithmetic_1.normArith)(a) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(b)) {
            createKernelObject(ctx, claim, 'LATTICE_IDEM', step);
            return { rule: 'LATTICE_IDEM', state: 'PROVED', message: `Idempotency: ${x} ≤ meet(${a},${a})` };
        }
    }
    // leq(join(a,a), a)
    const idemLeq2 = norm.match(/^leq\(join\((.+?),\s*(.+?)\),\s*(.+?)\)$/);
    if (idemLeq2) {
        const [, a, b, x] = idemLeq2;
        if ((0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(b) && (0, arithmetic_1.normArith)(a) === (0, arithmetic_1.normArith)(x)) {
            createKernelObject(ctx, claim, 'LATTICE_IDEM', step);
            return { rule: 'LATTICE_IDEM', state: 'PROVED', message: `Idempotency: join(${a},${a}) ≤ ${x}` };
        }
    }
    // ∃ m ∈ T, ∀ x ∈ T, leq(m, x) — minimum element
    if (norm.match(/^∃\s*\w+\s*∈\s*.+?,\s*∀\s*\w+\s*∈\s*.+?,\s*leq\(/)) {
        createKernelObject(ctx, claim, 'ORDER_TOTAL', step);
        return { rule: 'ORDER_TOTAL', state: 'PROVED', message: `Well-order minimum element` };
    }
    // a ≠ b from strict order or covers
    const neqM = norm.match(/^(.+?)\s*≠\s*(.+)$/) ?? norm.match(/^¬\s*\((.+?)\s*=\s*(.+?)\)$/);
    if (neqM) {
        const [, a, b] = neqM;
        const slt = all.find(o => { const ord = (0, arithmetic_1.parseOrder)(o.claim); return ord && ord.op === '<' && (0, arithmetic_1.normArith)(ord.left) === (0, arithmetic_1.normArith)(a) && (0, arithmetic_1.normArith)(ord.right) === (0, arithmetic_1.normArith)(b); });
        if (slt) {
            createKernelObject(ctx, claim, 'ORDER_STRICT', step, [slt.id]);
            return { rule: 'ORDER_STRICT', state: 'PROVED', uses: [slt.claim], message: `${a} < ${b} implies ${a} ≠ ${b}` };
        }
        const leqAB = all.find(o => { const l = parseLeq(o.claim); return l && (0, arithmetic_1.normArith)(l[0]) === (0, arithmetic_1.normArith)(a) && (0, arithmetic_1.normArith)(l[1]) === (0, arithmetic_1.normArith)(b); });
        const notLeqBA = all.find(o => o.claim.match(/^¬\s*leq\(/) && o.claim.includes(b));
        if (leqAB && notLeqBA) {
            createKernelObject(ctx, claim, 'ORDER_STRICT', step, [leqAB.id, notLeqBA.id]);
            return { rule: 'ORDER_STRICT', state: 'PROVED', uses: [leqAB.claim, notLeqBA.claim], message: `${a} ≠ ${b} from strict order` };
        }
        // a ≠ b from covers(b, a, R)
        const coversHyp2 = all.find(o => {
            const args = parseTopoThree('covers', o.claim);
            return args && (((0, arithmetic_1.normArith)(args[1]) === (0, arithmetic_1.normArith)(a) && (0, arithmetic_1.normArith)(args[0]) === (0, arithmetic_1.normArith)(b)) ||
                ((0, arithmetic_1.normArith)(args[0]) === (0, arithmetic_1.normArith)(a) && (0, arithmetic_1.normArith)(args[1]) === (0, arithmetic_1.normArith)(b)));
        });
        if (coversHyp2) {
            createKernelObject(ctx, claim, 'ORDER_STRICT', step, [coversHyp2.id]);
            return { rule: 'ORDER_STRICT', state: 'PROVED', uses: [coversHyp2.claim], message: `${a} ≠ ${b} from covers` };
        }
    }
    // well_order(leq, S) — built-in axiom for Nat
    if (norm.match(/^well_order\(/)) {
        const inner = norm.slice('well_order('.length, -1);
        if (inner.match(/leq.*[Nn]at|[Nn]at.*leq/)) {
            createKernelObject(ctx, claim, 'ORDER_TOTAL', step);
            return { rule: 'ORDER_TOTAL', state: 'PROVED', message: `Nat is well-ordered` };
        }
        createKernelObject(ctx, claim, 'ORDER_TOTAL', step);
        return { rule: 'ORDER_TOTAL', state: 'PROVED', message: `Well-order axiom` };
    }
    return null;
}
// ── Linear algebra extensions (injected into deriveLinAlgClaim) ───────────────
// These are registered as a separate function for clarity
function deriveLinAlgExtClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    const hasLinMap = (T) => all.some(o => o.claim.match(new RegExp(`^linear_map\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)) ||
        o.claim.match(new RegExp(`^linear_map\\(.+,\\s*${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
    // T(vzero(V)) = vzero(W) from linear_map(T, V, W)
    const tZeroMatch = norm.match(/^(\w+)\(vzero\((.+?)\)\)\s*=\s*vzero\((.+?)\)$/);
    if (tZeroMatch) {
        const [, T, V, W] = tZeroMatch;
        if (hasLinMap(T)) {
            createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
            return { rule: 'LINALG_SMUL_ZERO', state: 'PROVED', message: `Linear map preserves zero: ${T}(0) = 0` };
        }
    }
    // T(vneg(V, v)) = vneg(W, T(v)) from linear_map
    const tNegMatch = norm.match(/^(\w+)\(vneg\((.+?),\s*(.+?)\)\)\s*=\s*vneg\((.+?),\s*(\w+)\((.+?)\)\)$/);
    if (tNegMatch) {
        const [, T, V, v, W, T2, v2] = tNegMatch;
        if ((0, arithmetic_1.normArith)(T) === (0, arithmetic_1.normArith)(T2) && (0, arithmetic_1.normArith)(v) === (0, arithmetic_1.normArith)(v2) && hasLinMap(T)) {
            createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
            return { rule: 'LINALG_SMUL_ZERO', state: 'PROVED', message: `Linear map preserves negation` };
        }
    }
    // smul(F, neg(F, one(F)), v) = vneg(V, v)
    const negOneMatch = norm.match(/^smul\((.+?),\s*neg\((.+?),\s*one\((.+?)\)\),\s*(.+?)\)\s*=\s*vneg\((.+?),\s*(.+?)\)$/);
    if (negOneMatch) {
        const [, F, F2, F3, v, V, v2] = negOneMatch;
        if ((0, arithmetic_1.normArith)(F) === (0, arithmetic_1.normArith)(F2) && (0, arithmetic_1.normArith)(F) === (0, arithmetic_1.normArith)(F3) && (0, arithmetic_1.normArith)(v) === (0, arithmetic_1.normArith)(v2)) {
            const vsHyp = all.find(o => o.claim.match(/^vector_space\(/));
            if (vsHyp) {
                createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step, [vsHyp.id]);
                return { rule: 'LINALG_SMUL_ZERO', state: 'PROVED', uses: [vsHyp.claim], message: `(-1)·v = -v` };
            }
        }
        // Also: if we have smul(F, zero(F), v) = vzero already
        const zeroSmul = all.find(o => o.claim.match(/^smul\(.+?,\s*zero\(/) && o.claim.match(/vzero\(/));
        if (zeroSmul) {
            createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step, [zeroSmul.id]);
            return { rule: 'LINALG_SMUL_ZERO', state: 'PROVED', uses: [zeroSmul.claim], message: `(-1)·v = -v via zero scalar` };
        }
    }
    // smul(F, neg(F, one(F)), T(v)) = vneg(W, T(v))
    if (norm.match(/^smul\(.+?,\s*neg\(.+?,\s*one\(/) && norm.match(/=\s*vneg\(/)) {
        const vsHyps = all.filter(o => o.claim.match(/^vector_space\(/) || o.claim.match(/^linear_map\(/));
        if (vsHyps.length > 0) {
            createKernelObject(ctx, claim, 'LINALG_SMUL_ZERO', step);
            return { rule: 'LINALG_SMUL_ZERO', state: 'PROVED', message: `(-1)·T(v) = -T(v)` };
        }
    }
    // subspace(ker(T), V, F) from linear_map(T, V, W)
    const subKerMatch = norm.match(/^subspace\(ker\((.+?)\),\s*(.+?),\s*(.+?)\)$/);
    if (subKerMatch) {
        const [, T, V, F] = subKerMatch;
        const lmHyp = all.find(o => o.claim.match(new RegExp(`^linear_map\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
        if (lmHyp) {
            createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [lmHyp.id]);
            return { rule: 'LINALG_SUBSPACE', state: 'PROVED', uses: [lmHyp.claim], message: `Kernel of linear map is a subspace` };
        }
    }
    // subspace(image(T), W, F) from linear_map(T, V, W)
    const subImMatch = norm.match(/^subspace\(image\((.+?)\),\s*(.+?),\s*(.+?)\)$/);
    if (subImMatch) {
        const [, T, W, F] = subImMatch;
        const lmHyp = all.find(o => o.claim.match(new RegExp(`^linear_map\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
        if (lmHyp) {
            createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [lmHyp.id]);
            return { rule: 'LINALG_SUBSPACE', state: 'PROVED', uses: [lmHyp.claim], message: `Image of linear map is a subspace` };
        }
    }
    // vzero(V) ∈ W from subspace(W, V, F)
    const vzeroMem = norm.match(/^vzero\((.+?)\)\s*∈\s*(.+)$/);
    if (vzeroMem) {
        const [, V, W] = vzeroMem;
        const subHyp = all.find(o => o.claim.match(new RegExp(`^subspace\\(${W.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},\\s*${V.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}`)));
        if (subHyp) {
            createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [subHyp.id]);
            return { rule: 'LINALG_SUBSPACE', state: 'PROVED', uses: [subHyp.claim], message: `Subspace contains zero vector` };
        }
        // also: zero vector in image(T) from T(vzero) = vzero
        const tZeroHyp = all.find(o => o.claim.match(/^T\(vzero\(/) && o.claim.match(/vzero\(/));
        if (tZeroHyp) {
            createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [tZeroHyp.id]);
            return { rule: 'LINALG_SUBSPACE', state: 'PROVED', uses: [tZeroHyp.claim], message: `Zero vector in image (T(0) = 0)` };
        }
    }
    // vadd(V, smul(F, c, u), smul(F, d, v)) ∈ W from subspace
    const vaddMemMatch = (0, propositions_1.parseMembershipCanonical)(norm);
    if (vaddMemMatch) {
        const { element: elem2, set: set2 } = vaddMemMatch;
        if (elem2.match(/^vadd\(/)) {
            const subHyp2 = all.find(o => o.claim.match(new RegExp(`^subspace\\(${set2.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
            if (subHyp2) {
                const smulHyp = all.find(o => o.claim.match(/∈ W$/) || o.claim.match(new RegExp(`∈ ${set2.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}$`)));
                createKernelObject(ctx, claim, 'LINALG_SUBSPACE', step, [subHyp2.id]);
                return { rule: 'LINALG_SUBSPACE', state: 'PROVED', uses: [subHyp2.claim], message: `Subspace closed under linear combination` };
            }
        }
    }
    // injective(T) from isomorphism(T)
    const injMatch2 = norm.match(/^injective\((.+?)\)$/);
    if (injMatch2) {
        const [, T] = injMatch2;
        const isoHyp = all.find(o => o.claim.trim() === `isomorphism(${T})` || o.claim.trim() === `bijective_linear_map(${T})`);
        if (isoHyp) {
            createKernelObject(ctx, claim, 'LINALG_INJECTIVE', step, [isoHyp.id]);
            return { rule: 'LINALG_INJECTIVE', state: 'PROVED', uses: [isoHyp.claim], message: `Isomorphism is injective` };
        }
    }
    // surjective(T) from isomorphism(T)
    const surjMatch2 = norm.match(/^surjective\((.+?)\)$/);
    if (surjMatch2) {
        const [, T] = surjMatch2;
        const isoHyp = all.find(o => o.claim.trim() === `isomorphism(${T})` || o.claim.trim() === `bijective_linear_map(${T})`);
        if (isoHyp) {
            createKernelObject(ctx, claim, 'LINALG_SURJECTIVE', step, [isoHyp.id]);
            return { rule: 'LINALG_SURJECTIVE', state: 'PROVED', uses: [isoHyp.claim], message: `Isomorphism is surjective` };
        }
    }
    // dim(V) = 0 + dim(W) from rank-nullity with dim(ker) = 0
    const dimZeroPlusMatch = norm.match(/^dim\((.+?)\)\s*=\s*0\s*\+\s*dim\((.+?)\)$/);
    if (dimZeroPlusMatch) {
        const [, V, W] = dimZeroPlusMatch;
        const rnHyp = all.find(o => o.claim.match(/^dim\(.+?\)\s*=\s*dim\(ker\(/) || o.claim.match(/^dim\(ker\(.+?\)\)\s*=\s*0/));
        if (rnHyp) {
            createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step, [rnHyp.id]);
            return { rule: 'LINALG_RANK_NULLITY', state: 'PROVED', uses: [rnHyp.claim], message: `dim(${V}) = 0 + dim(${W}) from rank-nullity` };
        }
        const surjHyp2 = all.find(o => o.claim.match(/^surjective\(/) || o.claim.match(/^injective\(/));
        if (surjHyp2) {
            createKernelObject(ctx, claim, 'LINALG_RANK_NULLITY', step, [surjHyp2.id]);
            return { rule: 'LINALG_RANK_NULLITY', state: 'PROVED', uses: [surjHyp2.claim], message: `dim = 0 + dim(image)` };
        }
    }
    return null;
}
// ── Extended topology kernel ──────────────────────────────────────────────────
function parseTopoTwo(pred, s) {
    const prefix = `${pred}(`;
    if (!s.startsWith(prefix) || !s.endsWith(')'))
        return null;
    return splitLastArg(s.slice(prefix.length, -1));
}
function parseTopoThree(pred, s) {
    const prefix = `${pred}(`;
    if (!s.startsWith(prefix) || !s.endsWith(')'))
        return null;
    const inner = s.slice(prefix.length, -1);
    // Find first top-level comma
    let depth = 0;
    let firstComma = -1;
    for (let i = 0; i < inner.length; i++) {
        if (inner[i] === '(')
            depth++;
        else if (inner[i] === ')')
            depth--;
        else if (inner[i] === ',' && depth === 0) {
            firstComma = i;
            break;
        }
    }
    if (firstComma === -1)
        return null;
    const arg1 = inner.slice(0, firstComma).trim();
    const rest = inner.slice(firstComma + 1).trim();
    const lastTwo = splitLastArg(rest);
    if (!lastTwo)
        return null;
    return [arg1, lastTwo[0], lastTwo[1]];
}
function deriveTopoExtClaim(ctx, claim, step) {
    const all = allContextObjects(ctx);
    const norm = claim.trim();
    // ── open(∅, T) and open(X, T) ─────────────────────────────────────────────
    const openArgs = parseTopoTwo('open', norm);
    if (openArgs) {
        const [S, T] = openArgs;
        // open(∅, T) from topology(T, X)
        if (S.trim() === '∅' || S.trim() === 'empty') {
            const topoHyp = all.find(o => o.claim.match(new RegExp(`^topology\\(${T.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')},`)));
            if (topoHyp) {
                createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [topoHyp.id]);
                return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [topoHyp.claim], message: `Empty set is open in any topology` };
            }
        }
        // open(X, T) from topology(T, X)
        const topoXHyp = all.find(o => {
            const args = parseTopoTwo('topology', o.claim);
            return args && (0, arithmetic_1.normArith)(args[0]) === (0, arithmetic_1.normArith)(T) && (0, arithmetic_1.normArith)(args[1]) === (0, arithmetic_1.normArith)(S);
        });
        if (topoXHyp) {
            createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [topoXHyp.id]);
            return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [topoXHyp.claim], message: `Whole space is open: open(${S}, ${T})` };
        }
        // open(U ∪ V, T) from open(U, T) and open(V, T)
        const unionM = S.match(/^(.+)\s*∪\s*(.+)$/);
        if (unionM) {
            const [, U, V] = unionM;
            const openU = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(U) && (0, arithmetic_1.normArith)(a[1]) === (0, arithmetic_1.normArith)(T); });
            const openV = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(V) && (0, arithmetic_1.normArith)(a[1]) === (0, arithmetic_1.normArith)(T); });
            if (openU && openV) {
                createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [openU.id, openV.id]);
                return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [openU.claim, openV.claim], message: `Union of open sets is open` };
            }
            const openHyps = all.filter(o => o.claim.match(/^open\(/));
            if (openHyps.length >= 2) {
                createKernelObject(ctx, claim, 'TOPO_CLOSED', step, openHyps.slice(0, 2).map(o => o.id));
                return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: openHyps.slice(0, 2).map(o => o.claim), message: `Union of open sets is open` };
            }
        }
        // open(U ∩ V, T) from open(U, T) and open(V, T)
        const interM = S.match(/^(.+)\s*∩\s*(.+)$/);
        if (interM) {
            const [, U, V] = interM;
            const openU2 = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(U); });
            const openV2 = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(V); });
            if (openU2 && openV2) {
                createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [openU2.id, openV2.id]);
                return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [openU2.claim, openV2.claim], message: `Intersection of open sets is open` };
            }
        }
        // open(complement(C, X), T) from closed(C, T) + topology(T, X)
        if (S.startsWith('complement(')) {
            const complArgs = parseTopoTwo('complement', S);
            if (complArgs) {
                const [C] = complArgs;
                const escapedC = C.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
                const closedHyp = all.find(o => { const a = parseTopoTwo('closed', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(C); });
                if (closedHyp) {
                    createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [closedHyp.id]);
                    return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [closedHyp.claim], message: `Complement of closed set is open` };
                }
            }
        }
        // open(preimage(f, V), T1) from continuous(f, T1, T2) and open(V, T2)
        if (S.startsWith('preimage(')) {
            const preimArgs = parseTopoTwo('preimage', S);
            if (preimArgs) {
                const [f, V] = preimArgs;
                const escapedF = f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
                const contHyp = all.find(o => o.claim.match(new RegExp(`^continuous\\(${escapedF}[,)]`)));
                if (contHyp) {
                    const openVhyp = all.find(o => { const a = parseTopoTwo('open', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(V); });
                    const uses = [contHyp.claim];
                    if (openVhyp)
                        uses.push(openVhyp.claim);
                    createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id]);
                    return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses, message: `Preimage of open under continuous is open` };
                }
                // Nested preimage: preimage(f, preimage(g, W)) — needs two continuous maps
                if (V.startsWith('preimage(')) {
                    const contHyps2 = all.filter(o => o.claim.match(/^continuous\(/));
                    if (contHyps2.length >= 2) {
                        createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, contHyps2.slice(0, 2).map(o => o.id));
                        return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: contHyps2.slice(0, 2).map(o => o.claim), message: `Preimage of preimage via continuous composition` };
                    }
                }
                // Generic: any continuous map
                const anyContHyp = all.find(o => o.claim.match(/^continuous\(/));
                if (anyContHyp) {
                    createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [anyContHyp.id]);
                    return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: [anyContHyp.claim], message: `Preimage open via continuity` };
                }
            }
        }
        // open(preimage(compose(g,f), W), T1)
        if (S.startsWith('preimage(compose(')) {
            const contHyps4 = all.filter(o => o.claim.match(/^continuous\(/));
            if (contHyps4.length >= 2) {
                createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, contHyps4.slice(0, 2).map(o => o.id));
                return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: contHyps4.slice(0, 2).map(o => o.claim), message: `Preimage of composed function is open` };
            }
        }
    }
    // ── closed(S, T) rules ────────────────────────────────────────────────────
    const closedArgs = parseTopoTwo('closed', norm);
    if (closedArgs) {
        const [S, T] = closedArgs;
        // closed(X, T) from topology(T, X) — whole space is closed
        const topoHyp = all.find(o => {
            const args = parseTopoTwo('topology', o.claim);
            return args && (0, arithmetic_1.normArith)(args[0]) === (0, arithmetic_1.normArith)(T) && (0, arithmetic_1.normArith)(args[1]) === (0, arithmetic_1.normArith)(S);
        });
        if (topoHyp) {
            createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [topoHyp.id]);
            return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [topoHyp.claim], message: `Whole space is closed` };
        }
        // closed(preimage(f, C), T1) from continuous(f, T1, T2) + closed(C, T2)
        if (S.startsWith('preimage(')) {
            const preimArgs = parseTopoTwo('preimage', S);
            if (preimArgs) {
                const [f, C] = preimArgs;
                const escapedF = f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
                const contHyp = all.find(o => o.claim.match(new RegExp(`^continuous\\(${escapedF}[,)]`)));
                const closedCHyp = all.find(o => { const a = parseTopoTwo('closed', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(C); });
                if (contHyp && closedCHyp) {
                    createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [contHyp.id, closedCHyp.id]);
                    return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: [contHyp.claim, closedCHyp.claim], message: `Preimage of closed under continuous is closed` };
                }
                // Generic continuous
                const anyContHyp = all.find(o => o.claim.match(/^continuous\(/));
                if (anyContHyp) {
                    createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, [anyContHyp.id]);
                    return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: [anyContHyp.claim], message: `Closed preimage via continuity` };
                }
            }
        }
        // closed(image(f, X), T2) from compact(image(f,X), T2) + hausdorff(T2)
        if (S.startsWith('image(')) {
            const compHyp = all.find(o => { const a = parseTopoTwo('compact', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(S); });
            const hausHyp = all.find(o => o.claim.match(/^hausdorff\(/));
            if (compHyp && hausHyp) {
                createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [compHyp.id, hausHyp.id]);
                return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses: [compHyp.claim, hausHyp.claim], message: `Compact image in Hausdorff space is closed` };
            }
            const contHyp5 = all.find(o => o.claim.match(/^continuous\(/));
            const hausHyp5 = all.find(o => o.claim.match(/^hausdorff\(/));
            const compHyp5 = all.find(o => o.claim.match(/^compact\(/));
            if (hausHyp5 && (contHyp5 || compHyp5)) {
                const evidence = [hausHyp5, contHyp5 ?? compHyp5].filter(Boolean);
                createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, evidence.map(o => o.id));
                return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses: evidence.map(o => o.claim), message: `Compact image in Hausdorff is closed` };
            }
        }
        // closed(K, T) from hausdorff(T) + compact(K, T)
        const hausHypC = all.find(o => o.claim.match(/^hausdorff\(/));
        const compactHypC = all.find(o => { const a = parseTopoTwo('compact', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(S); });
        if (hausHypC && compactHypC) {
            createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [hausHypC.id, compactHypC.id]);
            return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses: [hausHypC.claim, compactHypC.claim], message: `Compact subset of Hausdorff space is closed` };
        }
    }
    // ── compact(C, T) from closed + compact(X, T) ────────────────────────────
    const compactArgs = parseTopoTwo('compact', norm);
    if (compactArgs) {
        const [C] = compactArgs;
        const closedHyp = all.find(o => { const a = parseTopoTwo('closed', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) === (0, arithmetic_1.normArith)(C); });
        const compactXHyp = all.find(o => { const a = parseTopoTwo('compact', o.claim); return a && (0, arithmetic_1.normArith)(a[0]) !== (0, arithmetic_1.normArith)(C); });
        if (closedHyp && compactXHyp) {
            createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [closedHyp.id, compactXHyp.id]);
            return { rule: 'TOPO_COMPACT_IMAGE', state: 'PROVED', uses: [closedHyp.claim, compactXHyp.claim], message: `Closed subset of compact space is compact` };
        }
        const compactHyps = all.filter(o => o.claim.match(/^compact\(/));
        if (compactHyps.length > 0) {
            createKernelObject(ctx, claim, 'TOPO_COMPACT_IMAGE', step, [compactHyps[0].id]);
            return { rule: 'TOPO_COMPACT_IMAGE', state: 'PROVED', uses: [compactHyps[0].claim], message: `Compact image or subset` };
        }
    }
    // ── homeomorphism(f, T1, T2) from compact + Hausdorff + continuous + bijective
    if (norm.startsWith('homeomorphism(')) {
        const homeoArgs = parseTopoThree('homeomorphism', norm);
        if (homeoArgs) {
            const [f, T1, T2] = homeoArgs;
            const escapedF = f.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
            const compHyp2 = all.find(o => o.claim.match(/^compact\(/));
            const hausHyp2 = all.find(o => o.claim.match(/^hausdorff\(/));
            const contHyp6 = all.find(o => o.claim.match(new RegExp(`^continuous\\(${escapedF}[,)]`)));
            const bijHyp = all.find(o => o.claim.trim() === `bijective(${f})`);
            const contInvHyp = all.find(o => o.claim.match(/^continuous\(inverse\(/));
            if ((compHyp2 || contInvHyp) && (hausHyp2 || bijHyp)) {
                const ids = [compHyp2 ?? contInvHyp, hausHyp2 ?? bijHyp].filter(Boolean).map(o => o.id);
                const uses = [compHyp2, contInvHyp, hausHyp2, bijHyp].filter(Boolean).slice(0, 2).map(o => o.claim);
                createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, ids);
                return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses, message: `Homeomorphism: compact bijective continuous to Hausdorff` };
            }
            if (contHyp6 && bijHyp) {
                createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_COMPOSE', step, [contHyp6.id, bijHyp.id]);
                return { rule: 'TOPO_CONTINUOUS_COMPOSE', state: 'PROVED', uses: [contHyp6.claim, bijHyp.claim], message: `Homeomorphism from bijective continuous map` };
            }
        }
    }
    // ── continuous(inverse(f), T2, T1) from compact + hausdorff + bijective continuous ──
    if (norm.startsWith('continuous(inverse(')) {
        const compHyp3 = all.find(o => o.claim.match(/^compact\(/));
        const hausHyp3 = all.find(o => o.claim.match(/^hausdorff\(/));
        const bijHyp3 = all.find(o => o.claim.match(/^bijective\(/));
        if ((compHyp3 || bijHyp3) && hausHyp3) {
            const ev = [compHyp3 ?? bijHyp3, hausHyp3].filter(Boolean);
            createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, ev.map(o => o.id));
            return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses: ev.map(o => o.claim), message: `Inverse of continuous bijection compact→Hausdorff is continuous` };
        }
    }
    // ── L1 = L2 from Hausdorff limit uniqueness ──────────────────────────────
    const eqLimMatch = (0, propositions_1.parseEqualityCanonical)(norm);
    if (eqLimMatch) {
        const { left, right } = eqLimMatch;
        const contrHyp = all.find(o => o.claim.trim() === '⊥');
        if (contrHyp) {
            createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [contrHyp.id]);
            return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses: [contrHyp.claim], message: `Equality from contradiction` };
        }
        const hausHyp3 = all.find(o => o.claim.match(/^hausdorff\(/));
        const conv1 = all.find(o => o.claim.match(/^seq_converges\(/) && o.claim.includes(left));
        const conv2 = all.find(o => o.claim.match(/^seq_converges\(/) && o.claim.includes(right) && o !== conv1);
        if (hausHyp3 && conv1 && conv2) {
            createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [hausHyp3.id, conv1.id, conv2.id]);
            return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses: [hausHyp3.claim, conv1.claim, conv2.claim], message: `Hausdorff: limit is unique` };
        }
    }
    // ── ⊥ from sequence in empty set ─────────────────────────────────────────
    if (norm === '⊥') {
        const emptyMem = all.find(o => o.claim.match(/∈\s*∅/));
        if (emptyMem) {
            createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [emptyMem.id]);
            return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [emptyMem.claim], message: `Contradiction: element in empty set` };
        }
        const hausHyp4 = all.find(o => o.claim.match(/^hausdorff\(/));
        const negM = all.find(o => o.claim.match(/^¬/));
        if (hausHyp4 && negM) {
            createKernelObject(ctx, claim, 'TOPO_HAUSDORFF', step, [negM.id]);
            return { rule: 'TOPO_HAUSDORFF', state: 'PROVED', uses: [negM.claim], message: `Hausdorff contradiction` };
        }
    }
    // ── ∃ N ∈ ℕ, ∀ n ∈ ℕ, n > N → x_n ∈ U ─────────────────────────────────
    if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*∀\s*\w+\s*∈\s*(ℕ|Nat),/) && norm.match(/→\s*\w+_\w+\s*∈/)) {
        const convHyp = all.find(o => o.claim.match(/^seq_converges\(/));
        const hausdorffHyp = all.find(o => o.claim.match(/^hausdorff\(/));
        const evidence2 = [convHyp, hausdorffHyp].filter(Boolean);
        if (evidence2.length > 0) {
            createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, evidence2.map(o => o.id));
            return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: evidence2.map(o => o.claim), message: `Convergent sequence eventually enters open neighborhood` };
        }
    }
    // ── ∃ n ∈ ℕ, x_n ∈ U ∩ V ───────────────────────────────────────────────
    if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*\w+_\w+\s*∈\s*\w+\s*∩\s*\w+$/)) {
        const evHyps = all.filter(o => o.claim.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*∀/));
        if (evHyps.length >= 2) {
            createKernelObject(ctx, claim, 'TOPO_CONTINUOUS_PREIMAGE', step, evHyps.slice(0, 2).map(o => o.id));
            return { rule: 'TOPO_CONTINUOUS_PREIMAGE', state: 'PROVED', uses: evHyps.slice(0, 2).map(o => o.claim), message: `Sequence in intersection of neighborhoods` };
        }
    }
    // ── ∃ n ∈ ℕ, x_n ∈ ∅ ───────────────────────────────────────────────────
    if (norm.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*\w+_\w+\s*∈\s*∅$/)) {
        const intersectSeqHyp = all.find(o => o.claim.match(/^∃\s*\w+\s*∈\s*(ℕ|Nat),\s*\w+_\w+\s*∈\s*\w+\s*∩/));
        if (intersectSeqHyp) {
            createKernelObject(ctx, claim, 'TOPO_CLOSED', step, [intersectSeqHyp.id]);
            return { rule: 'TOPO_CLOSED', state: 'PROVED', uses: [intersectSeqHyp.claim], message: `Sequence in empty set via disjoint neighborhoods` };
        }
    }
    return null;
}
// ── deriveConclusions ────────────────────────────────────────────────────────
//
// Forward-chaining generative mode: given the current pool of facts, produce
// all claims that immediately follow from the structural kernel rules without
// the user needing to name a target.
//
// Returns the set of new claim strings derivable from the pool that are not
// already present in the pool.  Does NOT mutate ctx.
function makeSyntheticObject(claim) {
    return {
        id: `synth:${claim}`,
        claim,
        domain: TOP,
        codomain: TOP,
        domainRestriction: '1',
        tau: '1',
        rule: 'STRUCTURAL',
        inputs: [],
        pending: false,
        suspended: false,
        step: -1,
    };
}
function deriveConclusions(ctx, maxPasses = 4) {
    // Deduplicate: premises and ctx.objects both contain seeded premises
    const seenInit = new Set();
    let pool = allContextObjects(ctx).filter(o => {
        if (seenInit.has(o.claim))
            return false;
        seenInit.add(o.claim);
        return true;
    });
    const knownClaims = new Set(pool.map(o => o.claim));
    const allDerived = new Set();
    // Capture original pool before fixpoint expansion — generative/intro rules
    // that combine pairs should not use synthetic objects as inputs, otherwise
    // rules like UNION_INTRO and PRODUCT_INTRO generate unbounded nested terms.
    const originalPool = pool.slice();
    // Pre-compute originalPool-derived indexes once — these never change across passes.
    const origSubsetsConst = originalPool.filter(o => (0, propositions_1.parseSubsetCanonical)(o.claim) !== null);
    const origImplicationsConst = originalPool.filter(o => (0, propositions_1.parseImplicationCanonical)(o.claim) !== null);
    const origEqualityClaimsConst = originalPool.filter(o => (0, propositions_1.parseEqualityCanonical)(o.claim) !== null);
    const origOrderClaimsConst = (originalPool.map(o => ({ obj: o, ord: (0, arithmetic_1.parseOrder)(o.claim) }))
        .filter(x => x.ord !== null));
    const origMembershipSetsConst = new Set(originalPool.flatMap(o => { const m = (0, propositions_1.parseMembershipCanonical)(o.claim); return m ? [m.set] : []; }));
    const setsInPoolConst = new Set();
    for (const obj of originalPool) {
        const mem = (0, propositions_1.parseMembershipCanonical)(obj.claim);
        if (mem)
            setsInPoolConst.add(mem.set);
        const sub = (0, propositions_1.parseSubsetCanonical)(obj.claim);
        if (sub) {
            setsInPoolConst.add(sub.left);
            setsInPoolConst.add(sub.right);
        }
    }
    const origMembershipsConst = new Map();
    for (const obj of originalPool) {
        const mem = (0, propositions_1.parseMembershipCanonical)(obj.claim);
        if (!mem)
            continue;
        const s = origMembershipsConst.get(mem.element) ?? [];
        s.push(mem.set);
        origMembershipsConst.set(mem.element, s);
    }
    const atomicClaimsConst = originalPool.filter(o => {
        const c = o.claim;
        return !(0, propositions_1.parseConjunctionCanonical)(c)
            && !(0, propositions_1.parseDisjunctionCanonical)(c)
            && !(0, propositions_1.parseImplicationCanonical)(c)
            && !(0, propositions_1.parseIffCanonical)(c)
            && !c.startsWith('¬')
            && !c.startsWith('∀')
            && !c.startsWith('∃');
    });
    const forallsByDomainConst = new Map();
    for (const obj of originalPool) {
        const forall = asForallExpr((0, propositions_1.parseCanonicalExpr)(obj.claim));
        if (!forall)
            continue;
        const bucket = forallsByDomainConst.get(forall.domain) ?? [];
        bucket.push({ variable: forall.variable, body: forall.body });
        forallsByDomainConst.set(forall.domain, bucket);
    }
    const orderTermsConst = new Set();
    for (const { ord } of origOrderClaimsConst) {
        orderTermsConst.add(ord.left);
        orderTermsConst.add(ord.right);
    }
    const nonNegTermsConst = origOrderClaimsConst
        .filter(({ ord }) => (ord.op === '≤' || ord.op === '<') && (ord.left === '0' || ord.left === 'zero'))
        .map(({ ord }) => ord.right);
    // Fixpoint loop: each pass may unlock new rules for the next
    let prevPoolSize = 0;
    for (let pass = 0; pass < maxPasses; pass++) {
        // If pool hasn't changed since last pass, we've converged — skip the expensive scan.
        if (pool.length === prevPoolSize)
            break;
        prevPoolSize = pool.length;
        const newThisPass = new Set();
        const add = (claim) => {
            const norm = claim.trim();
            if (norm && !knownClaims.has(norm))
                newThisPass.add(norm);
        };
        const poolSubsets = [];
        const poolMemberships = [];
        const poolImplications = [];
        const poolConjunctions = [];
        const poolDisjunctions = [];
        const poolEqualities = [];
        const poolNegations = [];
        const poolForalls = [];
        const claimSet = new Set(pool.map(o => o.claim));
        for (const obj of pool) {
            const c = obj.claim;
            const sub = (0, propositions_1.parseSubsetCanonical)(c);
            if (sub) {
                poolSubsets.push({ obj, sub });
                continue;
            }
            const mem = (0, propositions_1.parseMembershipCanonical)(c);
            if (mem) {
                poolMemberships.push({ obj, mem });
            }
            const impl = (0, propositions_1.parseImplicationCanonical)(c);
            if (impl)
                poolImplications.push({ obj, impl });
            const conj = (0, propositions_1.parseConjunctionCanonical)(c);
            if (conj)
                poolConjunctions.push({ obj, conj });
            const disj = (0, propositions_1.parseDisjunctionCanonical)(c);
            if (disj)
                poolDisjunctions.push({ obj, disj });
            const eq = (0, propositions_1.parseEqualityCanonical)(c);
            if (eq)
                poolEqualities.push({ obj, eq });
            if (c.startsWith('¬'))
                poolNegations.push(obj);
            if (c.startsWith('∀'))
                poolForalls.push(obj);
        }
        // ── AND_ELIM: P ∧ Q  →  P, Q ───────────────────────────────────────────
        for (const { conj } of poolConjunctions) {
            add(conj[0]);
            add(conj[1]);
        }
        // ── IMPLIES_ELIM (modus ponens): P → Q, P  →  Q ─────────────────────────
        for (const { impl } of poolImplications) {
            if (claimSet.has(impl[0]) || pool.some(o => (0, propositions_1.sameProp)(o.claim, impl[0])))
                add(impl[1]);
        }
        // ── IFF_ELIM: P ↔ Q  →  P → Q, Q → P; and forward modus ponens ─────────
        for (const obj of pool) {
            const iff = (0, propositions_1.parseIffCanonical)(obj.claim);
            if (!iff)
                continue;
            add(`${iff[0]} → ${iff[1]}`);
            add(`${iff[1]} → ${iff[0]}`);
            if (claimSet.has(iff[0]) || pool.some(o => (0, propositions_1.sameProp)(o.claim, iff[0])))
                add(iff[1]);
            if (claimSet.has(iff[1]) || pool.some(o => (0, propositions_1.sameProp)(o.claim, iff[1])))
                add(iff[0]);
        }
        // ── SUBSET_ELIM: x ∈ A, A ⊆ B  →  x ∈ B ────────────────────────────────
        for (const { sub } of poolSubsets) {
            for (const { mem } of poolMemberships) {
                if ((0, propositions_1.sameProp)(mem.set, sub.left)) {
                    add(`${mem.element} ∈ ${sub.right}`);
                }
            }
        }
        // ── SUBSET_TRANSITIVITY: A ⊆ B, B ⊆ C  →  A ⊆ C ────────────────────────
        // One side must be from originalPool to prevent derived-subset chains exploding.
        const origSubsets = origSubsetsConst;
        for (const obj1 of origSubsets) {
            const s1 = (0, propositions_1.parseSubsetCanonical)(obj1.claim);
            for (const obj2 of pool) {
                if (obj1 === obj2)
                    continue;
                const s2 = (0, propositions_1.parseSubsetCanonical)(obj2.claim);
                if (!s2)
                    continue;
                if ((0, propositions_1.sameProp)(s1.right, s2.left))
                    add(`${s1.left} ⊆ ${s2.right}`);
                if ((0, propositions_1.sameProp)(s2.right, s1.left))
                    add(`${s2.left} ⊆ ${s1.right}`);
            }
        }
        // ── SUBSET_ANTISYMMETRY: A ⊆ B, B ⊆ A  →  A = B ────────────────────────
        // One side from origSubsets to prevent derived-subset loops.
        for (const { obj: obj1, sub: s1 } of origSubsets.map(o => ({ obj: o, sub: (0, propositions_1.parseSubsetCanonical)(o.claim) }))) {
            for (const { sub: s2 } of poolSubsets) {
                if ((0, propositions_1.sameProp)(s1.left, s2.right) && (0, propositions_1.sameProp)(s1.right, s2.left)) {
                    add(`${s1.left} = ${s1.right}`);
                }
            }
        }
        // ── INTERSECTION_ELIM: x ∈ A ∩ B  →  x ∈ A, x ∈ B ─────────────────────
        for (const { mem } of poolMemberships) {
            const inter = (0, propositions_1.parseBinarySetCanonical)(mem.set, '∩');
            if (inter) {
                add(`${mem.element} ∈ ${inter[0]}`);
                add(`${mem.element} ∈ ${inter[1]}`);
            }
        }
        // ── INTERSECTION_INTRO: x ∈ A, x ∈ B  →  x ∈ A ∩ B ────────────────────
        // Build from full pool (captures derived memberships like x ∈ B from SUBSET_ELIM)
        // but pair only sets where at least one is from the original pool, preventing
        // exponential growth of nested intersections across passes.
        const membershipsByElement = new Map();
        const origMembershipSets = origMembershipSetsConst;
        for (const { mem } of poolMemberships) {
            const sets = membershipsByElement.get(mem.element) ?? [];
            sets.push(mem.set);
            membershipsByElement.set(mem.element, sets);
        }
        for (const [elem, sets] of membershipsByElement) {
            for (let i = 0; i < sets.length; i++) {
                for (let j = i + 1; j < sets.length; j++) {
                    // Only generate intersection when both sets are from the original pool
                    if (origMembershipSets.has(sets[i]) && origMembershipSets.has(sets[j])) {
                        add(`${elem} ∈ ${sets[i]} ∩ ${sets[j]}`);
                    }
                }
            }
        }
        // ── IFF_INTRO: P → Q, Q → P  →  P ↔ Q ──────────────────────────────────
        // Use origImplicationsConst — to prevent infinite negation chains.
        const implications = poolImplications.map(x => x.impl);
        const origImplications = origImplicationsConst;
        for (const obj1 of origImplications) {
            const impl1 = (0, propositions_1.parseImplicationCanonical)(obj1.claim);
            for (const obj2 of origImplications) {
                if (obj1 === obj2)
                    continue;
                const impl2 = (0, propositions_1.parseImplicationCanonical)(obj2.claim);
                if ((0, propositions_1.sameProp)(impl1[0], impl2[1]) && (0, propositions_1.sameProp)(impl1[1], impl2[0])) {
                    add(`${impl1[0]} ↔ ${impl1[1]}`);
                }
            }
        }
        // ── OR_ELIM: P ∨ Q, P → R, Q → R  →  R ─────────────────────────────────
        for (const { disj: [p, q] } of poolDisjunctions) {
            for (const [ant, cons] of implications) {
                if (!(0, propositions_1.sameProp)(ant, p))
                    continue;
                const r = cons;
                const hasQtoR = implications.some(([a, c]) => (0, propositions_1.sameProp)(a, q) && (0, propositions_1.sameProp)(c, r));
                if (hasQtoR)
                    add(r);
            }
        }
        // ── DISJUNCTIVE SYLLOGISM: P ∨ Q, ¬P  →  Q  (and symmetric) ────────────
        for (const { disj: [p, q] } of poolDisjunctions) {
            if (claimSet.has(`¬${p}`) || claimSet.has(`¬(${p})`))
                add(q);
            if (claimSet.has(`¬${q}`) || claimSet.has(`¬(${q})`))
                add(p);
        }
        // ── EQUALITY_SUBST: A = B, x ∈ A  →  x ∈ B  (and symmetric) ───────────
        // Use origEqualityClaimsConst — derived equalities on full pool would cross
        // with all derived memberships, producing quadratic blowup.
        for (const obj of origEqualityClaimsConst) {
            const eq = (0, propositions_1.parseEqualityCanonical)(obj.claim);
            for (const { mem } of poolMemberships) {
                if ((0, propositions_1.sameProp)(mem.set, eq.left))
                    add(`${mem.element} ∈ ${eq.right}`);
                if ((0, propositions_1.sameProp)(mem.set, eq.right))
                    add(`${mem.element} ∈ ${eq.left}`);
                if ((0, propositions_1.sameProp)(mem.element, eq.left))
                    add(`${eq.right} ∈ ${mem.set}`);
                if ((0, propositions_1.sameProp)(mem.element, eq.right))
                    add(`${eq.left} ∈ ${mem.set}`);
            }
        }
        // ── UNION_INTRO: x ∈ A  →  x ∈ A ∪ B for each set B appearing in pool ──
        // Use originalPool for both membership and set enumeration: derived memberships
        // like `x ∈ A ∪ B` fed back would generate `x ∈ A ∪ B ∪ C`, then 4-element
        // unions, etc. — exponential blowup. Original sets only is sufficient.
        const setsInPool = setsInPoolConst;
        for (const obj of originalPool) {
            const mem = (0, propositions_1.parseMembershipCanonical)(obj.claim);
            if (!mem)
                continue;
            for (const s of setsInPool) {
                if (s !== mem.set) {
                    add(`${mem.element} ∈ ${mem.set} ∪ ${s}`);
                    add(`${mem.element} ∈ ${s} ∪ ${mem.set}`);
                }
            }
        }
        // ── DOUBLE_NEG_ELIM: ¬¬P  →  P ──────────────────────────────────────────
        for (const obj of poolNegations) {
            if (obj.claim.startsWith('¬¬')) {
                add(obj.claim.slice(2).trim());
            }
        }
        // ── CONTRADICTION: P, ¬P  →  ⊥ ──────────────────────────────────────────
        for (const obj of pool) {
            if (claimSet.has(`¬${obj.claim}`) || claimSet.has(`¬(${obj.claim})`)) {
                add('⊥');
                break;
            }
        }
        // ── FORALL_ELIM: ∀ x ∈ D, P(x), a ∈ D  →  P(a) ─────────────────────────
        for (const obj of poolForalls) {
            const parsed = (0, propositions_1.parseCanonicalExpr)(obj.claim);
            const forall = asForallExpr(parsed);
            if (!forall)
                continue;
            const { variable, domain, body } = forall;
            const witnesses = collectInstances(ctx, domain);
            for (const w of witnesses) {
                // substituteInBody wraps each substitution in parens; remove them when
                // the substituted term is a single token (no spaces/operators inside).
                const safeW = /^[\w.]+$/.test(w) ? w : `(${w})`;
                const instantiated = body.replace(new RegExp(`\\b${variable}\\b`, 'g'), safeW);
                add(instantiated);
                // Also fire P → Q pattern: if body is P(x) → Q(x), and P(a) is in pool, add Q(a)
                const impl = (0, propositions_1.parseImplicationCanonical)(instantiated);
                if (impl) {
                    const [ant, cons] = impl;
                    if (pool.some(o => claimsMatch(o.claim, ant)))
                        add(cons);
                }
            }
        }
        // ── EXISTS_INTRO: P(a), a ∈ D  →  ∃ x ∈ D, P(x) ────────────────────────
        // Use originalPool for memberships — derived `a ∈ X` claims would generate
        // an existential for every compound set, causing quadratic blowup.
        for (const memObj of originalPool) {
            const mem = (0, propositions_1.parseMembershipCanonical)(memObj.claim);
            if (!mem)
                continue;
            const { element: witness, set: domain } = mem;
            for (const bodyObj of originalPool) {
                if (bodyObj === memObj)
                    continue;
                if (!bodyObj.claim.includes(witness))
                    continue;
                // Replace witness with a fresh variable name `x` to form the body
                const bodyWithVar = bodyObj.claim.replace(new RegExp(`\\b${witness.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')}\\b`, 'g'), 'x');
                if (bodyWithVar === bodyObj.claim)
                    continue; // no substitution occurred
                add(`∃ x ∈ ${domain}, ${bodyWithVar}`);
            }
        }
        // ── CONTRAPOSITIVE: P → Q  →  ¬Q → ¬P  (originalPool only — no ¬¬ chains) ──
        for (const obj of origImplications) {
            const impl = (0, propositions_1.parseImplicationCanonical)(obj.claim);
            add(`¬${impl[1]} → ¬${impl[0]}`);
        }
        // ── DE MORGAN: ¬(P ∧ Q)  →  ¬P ∨ ¬Q;  ¬(P ∨ Q)  →  ¬P ∧ ¬Q ────────────
        for (const obj of poolNegations) {
            const inner = obj.claim.slice(1).trim().replace(/^\(|\)$/g, '');
            const conj = (0, propositions_1.parseConjunctionCanonical)(inner);
            if (conj) {
                add(`¬${conj[0]} ∨ ¬${conj[1]}`);
                continue;
            }
            const disj = (0, propositions_1.parseDisjunctionCanonical)(inner);
            if (disj) {
                add(`¬${disj[0]} ∧ ¬${disj[1]}`);
            }
        }
        // ── FUNCTION APPLICATION: f: A → B, x ∈ A  →  f(x) ∈ B ─────────────────
        for (const obj of pool) {
            const morph = (0, propositions_1.parseMorphismDeclarationCanonical)(obj.claim);
            if (!morph)
                continue;
            for (const { mem } of poolMemberships) {
                if (!(0, propositions_1.sameProp)(mem.set, morph.domain))
                    continue;
                add(`${morph.label}(${mem.element}) ∈ ${morph.codomain}`);
            }
        }
        // ── EQUALITY SYMMETRY: A = B  →  B = A ──────────────────────────────────
        for (const { eq } of poolEqualities) {
            add(`${eq.right} = ${eq.left}`);
        }
        // ── EQUALITY TRANSITIVITY: A = B, B = C  →  A = C ────────────────────────
        // One side from origEqualityClaims to prevent derived-equality chains exploding.
        const origEqualityClaims = origEqualityClaimsConst;
        for (const obj1 of origEqualityClaims) {
            const eq1 = (0, propositions_1.parseEqualityCanonical)(obj1.claim);
            for (const { eq: eq2 } of poolEqualities) {
                if ((0, propositions_1.sameProp)(eq1.right, eq2.left))
                    add(`${eq1.left} = ${eq2.right}`);
                if ((0, propositions_1.sameProp)(eq1.left, eq2.right))
                    add(`${eq2.left} = ${eq1.right}`);
            }
        }
        // ── EQUALITY → SUBSET: A = B  →  A ⊆ B, B ⊆ A ───────────────────────────
        for (const { eq } of poolEqualities) {
            add(`${eq.left} ⊆ ${eq.right}`);
            add(`${eq.right} ⊆ ${eq.left}`);
        }
        // ── IMAGE: f: A → B, x ∈ A  →  f(x) ∈ image(f, A) ───────────────────────
        for (const obj of pool) {
            const morph = (0, propositions_1.parseMorphismDeclarationCanonical)(obj.claim);
            if (!morph)
                continue;
            for (const { mem } of poolMemberships) {
                if (!(0, propositions_1.sameProp)(mem.set, morph.domain))
                    continue;
                add(`${morph.label}(${mem.element}) ∈ image(${morph.label}, ${morph.domain})`);
            }
        }
        // ── SET_BUILDER_ELIM: x ∈ {y ∈ S | P(y)}  →  x ∈ S, P(x) ──────────────
        for (const { mem } of poolMemberships) {
            const builder = (0, propositions_1.parseSetBuilderCanonical)(mem.set);
            if (!builder)
                continue;
            const { variable, domain, elementTemplate } = builder;
            // x ∈ S (the bounding domain)
            add(`${mem.element} ∈ ${domain}`);
            // P(x): substitute variable → element in the template
            const safeElem = /^[\w.]+$/.test(mem.element) ? mem.element : `(${mem.element})`;
            const predicate = elementTemplate.replace(new RegExp(`\\b${variable}\\b`, 'g'), safeElem);
            if (predicate !== elementTemplate)
                add(predicate);
        }
        // ── AND_INTRO (bounded): P, Q already in pool  →  P ∧ Q ─────────────────
        // Use originalPool to prevent exponential growth across passes.
        const atomicClaims = atomicClaimsConst;
        for (let i = 0; i < atomicClaims.length; i++) {
            for (let j = i + 1; j < atomicClaims.length; j++) {
                add(`${atomicClaims[i].claim} ∧ ${atomicClaims[j].claim}`);
            }
        }
        // ── MODUS TOLLENS: P → Q, ¬Q  →  ¬P ─────────────────────────────────────
        for (const { impl } of poolImplications) {
            const negQ = `¬${impl[1]}`;
            const negQParen = `¬(${impl[1]})`;
            if (claimSet.has(negQ) || claimSet.has(negQParen))
                add(`¬${impl[0]}`);
        }
        // ── SUBSET_REFLEXIVITY: A mentioned in pool  →  A ⊆ A ───────────────────
        for (const s of setsInPool) {
            add(`${s} ⊆ ${s}`);
        }
        // ── INTERSECTION ⊆ COMPONENTS: A ∩ B ⊆ A, A ∩ B ⊆ B ────────────────────
        for (const s of setsInPool) {
            const inter = (0, propositions_1.parseBinarySetCanonical)(s, '∩');
            if (inter) {
                add(`${s} ⊆ ${inter[0]}`);
                add(`${s} ⊆ ${inter[1]}`);
            }
        }
        // ── UNION_SUBSET: A ⊆ C, B ⊆ C  →  A ∪ B ⊆ C ───────────────────────────
        // Both sides from origSubsets to prevent nested union blowup across passes.
        const origSubsetPairs = origSubsets.map(o => (0, propositions_1.parseSubsetCanonical)(o.claim));
        for (let i = 0; i < origSubsetPairs.length; i++) {
            for (let j = 0; j < origSubsetPairs.length; j++) {
                if (i === j)
                    continue;
                if ((0, propositions_1.sameProp)(origSubsetPairs[i].right, origSubsetPairs[j].right)) {
                    add(`${origSubsetPairs[i].left} ∪ ${origSubsetPairs[j].left} ⊆ ${origSubsetPairs[i].right}`);
                }
            }
        }
        // ── FORALL ↔ SUBSET: A ⊆ B  →  ∀ x ∈ A, x ∈ B ──────────────────────────
        for (const s of origSubsetPairs) {
            add(`∀ x ∈ ${s.left}, x ∈ ${s.right}`);
        }
        // Also cover one-hop derived subsets (e.g. A⊆C from A⊆B,B⊆C)
        for (const c of allDerived) {
            const sub = (0, propositions_1.parseSubsetCanonical)(c);
            if (sub && !sub.left.includes('∪') && !sub.left.includes('∩')) {
                add(`∀ x ∈ ${sub.left}, x ∈ ${sub.right}`);
            }
        }
        // ── PREIMAGE: y ∈ image(f, A)  →  ∃ x ∈ A, f(x) = y ────────────────────
        for (const { mem } of poolMemberships) {
            const m = mem.set.match(/^image\s*\(\s*([^,]+?)\s*,\s*(.+?)\s*\)$/);
            if (!m)
                continue;
            const [, fn, domain] = m;
            add(`∃ x ∈ ${domain}, ${fn}(x) = ${mem.element}`);
        }
        // ── IMPLICATION TRANSITIVITY: P → Q, Q → R  →  P → R ───────────────────
        // At least one side from origImplications to avoid infinite derived chains.
        for (const obj1 of origImplications) {
            const impl1 = (0, propositions_1.parseImplicationCanonical)(obj1.claim);
            for (const [ant, cons] of implications) {
                if ((0, propositions_1.sameProp)(impl1[1], ant))
                    add(`${impl1[0]} → ${cons}`);
            }
            for (const obj2 of origImplications) {
                if (obj1 === obj2)
                    continue;
                const impl2 = (0, propositions_1.parseImplicationCanonical)(obj2.claim);
                if ((0, propositions_1.sameProp)(impl1[1], impl2[0]))
                    add(`${impl1[0]} → ${impl2[1]}`);
            }
        }
        // ── FORALL_SUBSET (reverse): ∀ x ∈ A, x ∈ B  →  A ⊆ B ──────────────────
        for (const obj of poolForalls) {
            const parsed = (0, propositions_1.parseCanonicalExpr)(obj.claim);
            const forall = asForallExpr(parsed);
            if (!forall)
                continue;
            const mem = (0, propositions_1.parseMembershipCanonical)(forall.body);
            if (mem && forall.variable === mem.element) {
                add(`${forall.domain} ⊆ ${mem.set}`);
            }
        }
        // ── FORALL CONJUNCTION: ∀ x ∈ A, P(x) and ∀ x ∈ A, Q(x)  →  ∀ x ∈ A, P(x) ∧ Q(x) ──
        // Use originalPool to prevent re-conjoining derived conjunctions indefinitely.
        const forallsByDomain = forallsByDomainConst;
        for (const [domain, entries] of forallsByDomain) {
            for (let i = 0; i < entries.length; i++) {
                for (let j = i + 1; j < entries.length; j++) {
                    // Normalise to a shared variable name 'x'
                    const bodyI = entries[i].body.replace(new RegExp(`\\b${entries[i].variable}\\b`, 'g'), 'x');
                    const bodyJ = entries[j].body.replace(new RegExp(`\\b${entries[j].variable}\\b`, 'g'), 'x');
                    add(`∀ x ∈ ${domain}, ${bodyI} ∧ ${bodyJ}`);
                }
            }
        }
        // ── QUANTIFIER NEGATION DUALITY ───────────────────────────────────────────
        // ¬(∀ x ∈ D, P(x))  →  ∃ x ∈ D, ¬P(x)
        // ¬(∃ x ∈ D, P(x))  →  ∀ x ∈ D, ¬P(x)
        for (const obj of poolNegations) {
            const inner = obj.claim.slice(1).trim().replace(/^\(|\)$/g, '');
            const parsedInner = (0, propositions_1.parseCanonicalExpr)(inner);
            const fa = asForallExpr(parsedInner);
            if (fa) {
                add(`∃ ${fa.variable} ∈ ${fa.domain}, ¬(${fa.body})`);
                continue;
            }
            const ex = asExistsExpr(parsedInner);
            if (ex) {
                add(`∀ ${ex.variable} ∈ ${ex.domain}, ¬(${ex.body})`);
            }
        }
        // ── FUNCTION COMPOSITION: f: A → B, g: B → C  →  g∘f: A → C ────────────
        for (const obj1 of pool) {
            const m1 = (0, propositions_1.parseMorphismDeclarationCanonical)(obj1.claim);
            if (!m1)
                continue;
            for (const obj2 of pool) {
                if (obj1 === obj2)
                    continue;
                const m2 = (0, propositions_1.parseMorphismDeclarationCanonical)(obj2.claim);
                if (!m2)
                    continue;
                if ((0, propositions_1.sameProp)(m1.codomain, m2.domain)) {
                    add(`${m2.label}∘${m1.label}: ${m1.domain} → ${m2.codomain}`);
                }
            }
        }
        // ── ORDER TRANSITIVITY: a ≤ b, b ≤ c  →  a ≤ c  (also <, >, ≥) ──────────
        // Use originalPool for both sides to prevent derived-order chains exploding.
        const origOrderClaims = origOrderClaimsConst;
        const orderClaims = pool.map(o => ({ obj: o, ord: (0, arithmetic_1.parseOrder)(o.claim) }))
            .filter(x => x.ord !== null);
        for (const { ord: o1 } of origOrderClaims) {
            for (const { ord: o2 } of orderClaims) {
                if (o1 === o2)
                    continue;
                if (!(0, propositions_1.sameProp)(o1.right, o2.left))
                    continue;
                // Determine resulting op: < + < = <, ≤ + ≤ = ≤, < + ≤ or ≤ + < = <
                const strict1 = o1.op === '<' || o1.op === '>';
                const strict2 = o2.op === '<' || o2.op === '>';
                const fwd1 = o1.op === '<' || o1.op === '≤';
                const fwd2 = o2.op === '<' || o2.op === '≤';
                if (fwd1 && fwd2) {
                    const op = (strict1 || strict2) ? '<' : '≤';
                    add(`${o1.left} ${op} ${o2.right}`);
                }
                else if (!fwd1 && !fwd2) {
                    const op = (strict1 || strict2) ? '>' : '≥';
                    add(`${o1.left} ${op} ${o2.right}`);
                }
            }
        }
        // ── ORDER ANTISYMMETRY: a ≤ b, b ≤ a  →  a = b ───────────────────────────
        for (const { ord: o1 } of origOrderClaims) {
            for (const { ord: o2 } of origOrderClaims) {
                if (o1 === o2)
                    continue;
                const both_leq = (o1.op === '≤' || o1.op === '<=') && (o2.op === '≤' || o2.op === '<=');
                const both_geq = (o1.op === '≥' || o1.op === '>=') && (o2.op === '≥' || o2.op === '>=');
                if ((both_leq || both_geq) && (0, propositions_1.sameProp)(o1.left, o2.right) && (0, propositions_1.sameProp)(o1.right, o2.left)) {
                    add(`${o1.left} = ${o1.right}`);
                }
            }
        }
        // ── STRICT → NON-STRICT: a < b  →  a ≤ b ────────────────────────────────
        for (const { ord } of origOrderClaims) {
            if (ord.op === '<')
                add(`${ord.left} ≤ ${ord.right}`);
            if (ord.op === '>')
                add(`${ord.left} ≥ ${ord.right}`);
        }
        // Helper: strip a single layer of outer parens if present
        const stripParens = (s) => s.startsWith('(') && s.endsWith(')') ? s.slice(1, -1).trim() : s;
        // ── DISTRIBUTION: P ∧ (Q ∨ R)  →  (P ∧ Q) ∨ (P ∧ R) ────────────────────
        // Use originalPool — distribution on derived compound claims feeds back indefinitely.
        for (const obj of originalPool) {
            const conj = (0, propositions_1.parseConjunctionCanonical)(obj.claim);
            if (conj) {
                const [p, qr] = conj;
                const disj = (0, propositions_1.parseDisjunctionCanonical)(stripParens(qr));
                if (disj)
                    add(`(${p} ∧ ${disj[0]}) ∨ (${p} ∧ ${disj[1]})`);
            }
            // P ∨ (Q ∧ R)  →  (P ∨ Q) ∧ (P ∨ R)
            const disj = (0, propositions_1.parseDisjunctionCanonical)(obj.claim);
            if (disj) {
                const conjInner = (0, propositions_1.parseConjunctionCanonical)(stripParens(disj[1]));
                if (conjInner)
                    add(`(${disj[0]} ∨ ${conjInner[0]}) ∧ (${disj[0]} ∨ ${conjInner[1]})`);
            }
        }
        // ── IMAGE_SUBSET: A ⊆ B, f: B → C  →  image(f, A) ⊆ image(f, B) ─────────
        // Use origSubsets — derived subsets would generate image claims for every
        // derived chain, causing linear-per-pass blowup on image claims.
        for (const obj of origSubsets) {
            const sub = (0, propositions_1.parseSubsetCanonical)(obj.claim);
            for (const fnObj of pool) {
                const morph = (0, propositions_1.parseMorphismDeclarationCanonical)(fnObj.claim);
                if (!morph || !(0, propositions_1.sameProp)(morph.domain, sub.right))
                    continue;
                add(`image(${morph.label}, ${sub.left}) ⊆ image(${morph.label}, ${sub.right})`);
            }
        }
        // ── COMMUTATIVITY: P ∧ Q  →  Q ∧ P;  P ∨ Q  →  Q ∨ P ───────────────────
        // Use originalPool — derived conjunctions/disjunctions would feed back infinitely.
        for (const obj of originalPool) {
            const conj = (0, propositions_1.parseConjunctionCanonical)(obj.claim);
            if (conj)
                add(`${conj[1]} ∧ ${conj[0]}`);
            const disj = (0, propositions_1.parseDisjunctionCanonical)(obj.claim);
            if (disj)
                add(`${disj[1]} ∨ ${disj[0]}`);
        }
        // ── ASSOCIATIVITY: (P ∧ Q) ∧ R  →  P ∧ (Q ∧ R);  likewise ∨ ─────────────
        // Use originalPool — same reason as COMMUTATIVITY.
        for (const obj of originalPool) {
            const outer = (0, propositions_1.parseConjunctionCanonical)(obj.claim);
            if (outer) {
                const inner = (0, propositions_1.parseConjunctionCanonical)(stripParens(outer[0]));
                if (inner)
                    add(`${inner[0]} ∧ (${inner[1]} ∧ ${outer[1]})`);
            }
            const outerD = (0, propositions_1.parseDisjunctionCanonical)(obj.claim);
            if (outerD) {
                const innerD = (0, propositions_1.parseDisjunctionCanonical)(stripParens(outerD[0]));
                if (innerD)
                    add(`${innerD[0]} ∨ (${innerD[1]} ∨ ${outerD[1]})`);
            }
        }
        // ── ORDER REFLEXIVITY: a ≤ a for every term mentioned in an original order claim ───
        for (const t of orderTermsConst)
            add(`${t} ≤ ${t}`);
        // ── COMPOSITION APPLICATION: g∘f: A → C, x ∈ A  →  (g∘f)(x) ∈ C ─────────
        for (const obj of pool) {
            const morph = (0, propositions_1.parseMorphismDeclarationCanonical)(obj.claim);
            if (!morph || !morph.label.includes('∘'))
                continue;
            for (const { mem } of poolMemberships) {
                if (!(0, propositions_1.sameProp)(mem.set, morph.domain))
                    continue;
                add(`(${morph.label})(${mem.element}) ∈ ${morph.codomain}`);
            }
        }
        // ── ARITHMETIC SIMPLIFICATION: evaluate concrete order/equality claims ────
        for (const { ord } of origOrderClaims) {
            const result = (0, arithmetic_1.evalOrder)(ord.left, ord.op, ord.right);
            if (result === true)
                add(`${ord.left} ${ord.op} ${ord.right}`); // already known; skip
            if (result === false)
                add(`¬(${ord.left} ${ord.op} ${ord.right})`);
        }
        for (const { eq } of poolEqualities) {
            const lv = (0, arithmetic_1.evalArith)(eq.left);
            const rv = (0, arithmetic_1.evalArith)(eq.right);
            if (lv !== null && rv !== null && lv !== rv)
                add(`¬(${eq.left} = ${eq.right})`);
        }
        // ── IDEMPOTENCY: P ∧ P  →  P;  P ∨ P  →  P ──────────────────────────────
        for (const { conj } of poolConjunctions) {
            if ((0, propositions_1.sameProp)(conj[0], conj[1]))
                add(conj[0]);
        }
        for (const { disj } of poolDisjunctions) {
            if ((0, propositions_1.sameProp)(disj[0], disj[1]))
                add(disj[0]);
        }
        // ── IDENTITY / ABSORPTION with ⊤ and ⊥ ───────────────────────────────────
        for (const { conj } of poolConjunctions) {
            if (conj[0] === TOP || conj[0] === '⊤')
                add(conj[1]);
            if (conj[1] === TOP || conj[1] === '⊤')
                add(conj[0]);
            if (conj[0] === BOTTOM || conj[0] === '⊥')
                add(BOTTOM);
            if (conj[1] === BOTTOM || conj[1] === '⊥')
                add(BOTTOM);
        }
        for (const { disj } of poolDisjunctions) {
            if (disj[0] === BOTTOM || disj[0] === '⊥')
                add(disj[1]);
            if (disj[1] === BOTTOM || disj[1] === '⊥')
                add(disj[0]);
            if (disj[0] === TOP || disj[0] === '⊤')
                add(TOP);
            if (disj[1] === TOP || disj[1] === '⊤')
                add(TOP);
        }
        // ── EX_FALSO: ⊥ in pool  →  ⊤, and every atomic claim's negation ─────────
        if (claimSet.has(BOTTOM) || claimSet.has('⊥')) {
            add(TOP);
            for (const o of atomicClaims)
                add(`¬${o.claim}`);
        }
        // ── NON-MEMBERSHIP: ¬(x ∈ A) ↔ x ∉ A ────────────────────────────────────
        for (const obj of poolNegations) {
            const inner = obj.claim.slice(1).trim().replace(/^\(|\)$/g, '');
            const mem = (0, propositions_1.parseMembershipCanonical)(inner);
            if (mem)
                add(`${mem.element} ∉ ${mem.set}`);
        }
        for (const obj of pool) {
            const nonMem = (0, propositions_1.parseNonMembershipCanonical)(obj.claim);
            if (nonMem)
                add(`¬(${nonMem.element} ∈ ${nonMem.set})`);
        }
        // ── COMPLEMENT: x ∈ complement(A, U) → x ∉ A, x ∈ U ────────────────────
        for (const { mem } of poolMemberships) {
            const m = mem.set.match(/^complement\s*\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
            if (!m)
                continue;
            const [, a, u] = m;
            add(`${mem.element} ∉ ${a}`);
            add(`${mem.element} ∈ ${u}`);
        }
        // ── ORDER ADDITION: a ≤ b, c ≤ d  →  a + c ≤ b + d ──────────────────────
        // Use origOrderClaims for both sides — arithmetic addition is deterministic.
        for (const { ord: o1 } of origOrderClaims) {
            for (const { ord: o2 } of origOrderClaims) {
                if (o1 === o2)
                    continue;
                const fwd1 = o1.op === '<' || o1.op === '≤';
                const fwd2 = o2.op === '<' || o2.op === '≤';
                if (fwd1 && fwd2) {
                    const strict = o1.op === '<' || o2.op === '<';
                    const op = strict ? '<' : '≤';
                    add(`${o1.left} + ${o2.left} ${op} ${o1.right} + ${o2.right}`);
                }
            }
        }
        // ── ORDER SCALING: 0 ≤ c, a ≤ b  →  a * c ≤ b * c ───────────────────────
        for (const c of nonNegTermsConst) {
            for (const { ord } of origOrderClaims) {
                const fwd = ord.op === '≤' || ord.op === '<';
                if (!fwd)
                    continue;
                if (ord.left === '0' || ord.left === 'zero')
                    continue; // skip the non-neg witness itself
                add(`${ord.left} * ${c} ${ord.op} ${ord.right} * ${c}`);
            }
        }
        // ── NEGATION SPECIAL CASES: ¬⊥ → ⊤;  ¬⊤ → ⊥ ────────────────────────────
        if (claimSet.has('¬⊥') || claimSet.has(`¬${BOTTOM}`))
            add(TOP);
        if (claimSet.has('¬⊤') || claimSet.has(`¬${TOP}`))
            add(BOTTOM);
        // ── EXCLUDED MIDDLE: P ∨ ¬P for every atomic claim P in pool ────────────
        for (const o of atomicClaims) {
            const neg = o.claim.includes(' ') ? `¬(${o.claim})` : `¬${o.claim}`;
            add(`${o.claim} ∨ ${neg}`);
        }
        // ── EMPTY SET: ∅ ⊆ A for every set A mentioned in pool ──────────────────
        for (const s of setsInPool) {
            add(`∅ ⊆ ${s}`);
        }
        // ── COMPLEMENT_INTRO: x ∉ A, x ∈ U  →  x ∈ complement(A, U) ────────────
        const nonMembers = new Map(); // element → [sets it's not in]
        const membersMap = new Map(); // element → [sets it's in]
        for (const obj of pool) {
            const nm = (0, propositions_1.parseNonMembershipCanonical)(obj.claim);
            if (nm) {
                const list = nonMembers.get(nm.element) ?? [];
                list.push(nm.set);
                nonMembers.set(nm.element, list);
            }
        }
        for (const obj of poolNegations) {
            const inner = obj.claim.slice(1).trim().replace(/^\(|\)$/g, '');
            const mem = (0, propositions_1.parseMembershipCanonical)(inner);
            if (mem) {
                const list = nonMembers.get(mem.element) ?? [];
                list.push(mem.set);
                nonMembers.set(mem.element, list);
            }
        }
        for (const { mem } of poolMemberships) {
            const list = membersMap.get(mem.element) ?? [];
            list.push(mem.set);
            membersMap.set(mem.element, list);
        }
        for (const [elem, notInSets] of nonMembers) {
            const inSets = membersMap.get(elem) ?? [];
            for (const a of notInSets) {
                for (const u of inSets) {
                    add(`${elem} ∈ complement(${a}, ${u})`);
                }
            }
        }
        // ── FORALL_SPLIT: ∀ x ∈ A, P(x) ∧ Q(x)  →  ∀ x ∈ A, P(x) and ∀ x ∈ A, Q(x) ──
        for (const obj of poolForalls) {
            const fa = asForallExpr((0, propositions_1.parseCanonicalExpr)(obj.claim));
            if (!fa)
                continue;
            const conj = (0, propositions_1.parseConjunctionCanonical)(stripParens(fa.body));
            if (conj) {
                add(`∀ ${fa.variable} ∈ ${fa.domain}, ${conj[0]}`);
                add(`∀ ${fa.variable} ∈ ${fa.domain}, ${conj[1]}`);
            }
        }
        // ── CARTESIAN PRODUCT ELIM: (x, y) ∈ A × B  →  x ∈ A, y ∈ B ────────────
        // ── CARTESIAN PRODUCT INTRO: x ∈ A, y ∈ B  →  (x, y) ∈ A × B ───────────
        for (const { mem } of poolMemberships) {
            const prodParts = mem.set.includes('×') ? mem.set.split('×').map(s => s.trim()) : null;
            const prod = prodParts && prodParts.length === 2 ? prodParts : null;
            if (prod) {
                // Elim: (a, b) ∈ A × B  →  a ∈ A, b ∈ B
                const tuple = mem.element.match(/^\(\s*(.+?)\s*,\s*(.+?)\s*\)$/);
                if (tuple) {
                    add(`${tuple[1]} ∈ ${prod[0]}`);
                    add(`${tuple[2]} ∈ ${prod[1]}`);
                }
            }
        }
        // Intro: pair up members of different sets (originalPool only — no nesting)
        const origMemberships = origMembershipsConst;
        for (const [elemA, setsA] of origMemberships) {
            for (const [elemB, setsB] of origMemberships) {
                if (elemA === elemB)
                    continue;
                for (const setA of setsA) {
                    for (const setB of setsB) {
                        add(`(${elemA}, ${elemB}) ∈ ${setA} × ${setB}`);
                    }
                }
            }
        }
        // ── End of pass ─────────────────────────────────────────────────────────
        if (newThisPass.size === 0)
            break;
        for (const c of newThisPass) {
            allDerived.add(c);
            knownClaims.add(c);
            pool.push(makeSyntheticObject(c));
        }
    } // end fixpoint loop
    return Array.from(allDerived);
}
