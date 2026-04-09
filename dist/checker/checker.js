"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
exports.checkFile = checkFile;
const propositions_1 = require("./propositions");
const category_1 = require("../kernel/category");
const TOP = '⊤';
const BOTTOM = '⊥';
function checkFile(nodes, options = {}) {
    const diagnostics = [];
    const reports = [];
    const pairs = findPairs(nodes);
    const pairNames = new Set(pairs.map(pair => normalizeName(pair.theorem.name)));
    const lemmas = new Map();
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
        const report = checkPair(pair, lemmas, options);
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
    const state = combineStates(reports.map(report => report.state), pairedCount === 0 ? 'PENDING' : 'PROVED');
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
function checkPair(pair, lemmas, _options) {
    const premises = theoremPremises(pair.theorem);
    const goal = theoremGoal(pair.theorem);
    const ctx = createContext(goal, lemmas, premises);
    seedPremises(ctx, premises);
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
        const pendingGoal = findExact(ctx.objects, goal, true);
        ctx.diagnostics.push({
            severity: pendingGoal ? 'warning' : 'error',
            message: pendingGoal
                ? `Goal '${goal}' remains pending until Ra resolves its ω-valued morphisms`
                : `Proof '${pair.proof.name}' does not establish theorem goal '${goal}'`,
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
function createContext(goal, lemmas, premises) {
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
        objects: [],
        derivations: [],
        diagnostics: [],
        proofSteps: [],
        variables: [],
        assumptions: [],
        premises: [],
        lemmas: new Map(lemmas),
        goal,
    };
}
function seedPremises(ctx, premises) {
    for (const premise of premises) {
        const morphism = createKernelObject(ctx, premise, 'PREMISE', -1, [], [], '1');
        ctx.premises.push(morphism);
    }
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
        case 'Apply':
            handleApply(ctx, node.target, step);
            return;
        case 'Raw':
            handleRaw(ctx, node, step);
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
function handleApply(ctx, target, step) {
    const lemma = ctx.lemmas.get(normalizeName(target));
    if (!lemma) {
        ctx.diagnostics.push({ severity: 'error', step, message: `Unknown lemma '${target}'`, rule: 'BY_LEMMA' });
        ctx.proofSteps.push({
            step,
            kind: 'apply',
            claim: target,
            rule: 'BY_LEMMA',
            state: 'FAILED',
            message: `Lemma '${target}' is not available`,
        });
        return;
    }
    if (lemma.state === 'PENDING') {
        const claim = lemma.conclusion ?? target;
        createKernelObject(ctx, claim, 'BY_LEMMA', step, [], [lemma.name], 'ω', ['lemma']);
        ctx.proofSteps.push({
            step,
            kind: 'apply',
            claim,
            rule: 'BY_LEMMA',
            state: 'PENDING',
            imports: [lemma.name],
            message: `Lemma '${target}' imports a pending morphism`,
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
        createPendingObject(ctx, claim, step);
        ctx.proofSteps.push({
            step,
            kind: 'raw',
            claim,
            rule: 'STRUCTURAL',
            state: 'PENDING',
            message: 'Unsupported raw proof syntax is preserved as a pending morphism',
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
            state: exact.pending ? 'PENDING' : 'PROVED',
            uses: [exact.claim],
            message: 'Claim already exists as a morphism in the current derivation',
        };
    }
    const prover = [
        deriveAndIntro,
        deriveAndElim,
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
        deriveExFalso,
    ];
    for (const attempt of prover) {
        const result = attempt(ctx, claim, step);
        if (result) {
            return result;
        }
    }
    if (shouldRemainPending(claim)) {
        createPendingObject(ctx, claim, step);
        return {
            rule: 'STRUCTURAL',
            state: 'PENDING',
            message: 'Claim is structurally present but remains pending until supported morphisms are supplied or Ra resolves it',
        };
    }
    return {
        rule: 'STRUCTURAL',
        state: 'FAILED',
        message: `No categorical derivation establishes '${claim}' from the available morphisms`,
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
function theoremGoal(node) {
    return node.body
        .filter((item) => item.type === 'Assert')
        .map(item => (0, propositions_1.exprToProp)(item.expr))[0] ?? null;
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
        case 'Raw':
            return node.content;
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
    if (goal && !derivedConclusion) {
        return findExact(ctx.objects, goal, true) ? 'PENDING' : 'FAILED';
    }
    return ctx.objects.some(object => object.pending) ? 'PENDING' : 'PROVED';
}
function combineStates(states, fallback) {
    if (states.length === 0)
        return fallback;
    if (states.includes('FAILED'))
        return 'FAILED';
    if (states.includes('PENDING'))
        return 'PENDING';
    return 'PROVED';
}
function findExact(objects, claim, allowPending) {
    for (let index = objects.length - 1; index >= 0; index--) {
        const object = objects[index];
        if ((0, propositions_1.sameProp)(object.claim, claim) && (allowPending || !object.pending)) {
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
function shouldRemainPending(claim) {
    return Boolean((0, propositions_1.parseBoundedQuantifierCanonical)(claim, 'forall') ||
        (0, propositions_1.parseBoundedQuantifierCanonical)(claim, 'exists') ||
        (0, propositions_1.parseSetBuilderCanonical)(claim) ||
        (0, propositions_1.parseIndexedUnionCanonical)(claim) ||
        claim.includes('∀') ||
        claim.includes('∃'));
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
