import './styles.css';

type ProgramNode = any;
type EvalResult = { value: boolean; label: string; detail?: string | null };

const program: ProgramNode[] = [
  {
    "type": "FnDecl",
    "name": "double",
    "connective": "→",
    "params": [
      {
        "name": "n",
        "type": "ℕ"
      }
    ],
    "returnType": "Nat",
    "body": [
      {
        "type": "Conclude",
        "connective": null,
        "expr": {
          "type": "Atom",
          "condition": "n + n",
          "atomKind": "expression",
          "unsupported": false,
          "reason": null
        }
      }
    ]
  },
  {
    "type": "FnDecl",
    "name": "clamp",
    "connective": "→",
    "params": [
      {
        "name": "x",
        "type": "ℝ"
      },
      {
        "name": "lo",
        "type": "ℝ"
      },
      {
        "name": "hi",
        "type": "ℝ"
      }
    ],
    "returnType": "Real",
    "body": [
      {
        "type": "Assume",
        "connective": "→",
        "expr": {
          "type": "Atom",
          "condition": "lo ≤ hi",
          "atomKind": "expression",
          "unsupported": true,
          "reason": "This claim is outside the strict executable subset. Use fl check for categorical proof checking."
        }
      },
      {
        "type": "Conclude",
        "connective": null,
        "expr": {
          "type": "Atom",
          "condition": "max(lo, min(x, hi))",
          "atomKind": "expression",
          "unsupported": false,
          "reason": null
        }
      }
    ]
  },
  {
    "type": "Theorem",
    "name": "DoubleIsPositive",
    "connective": "→",
    "body": [
      {
        "type": "SetVar",
        "connective": "→",
        "varName": "n",
        "varType": null,
        "value": "4"
      },
      {
        "type": "SetVar",
        "connective": "→",
        "varName": "result",
        "varType": null,
        "value": "double(n)"
      },
      {
        "type": "Assert",
        "connective": null,
        "expr": {
          "type": "Atom",
          "condition": "result > 0",
          "atomKind": "expression",
          "unsupported": false,
          "reason": null
        }
      }
    ]
  },
  {
    "type": "Proof",
    "name": "DoubleIsPositive",
    "connective": null,
    "body": [
      {
        "type": "SetVar",
        "connective": "→",
        "varName": "n",
        "varType": null,
        "value": "4"
      },
      {
        "type": "SetVar",
        "connective": "→",
        "varName": "result",
        "varType": null,
        "value": "double(n)"
      },
      {
        "type": "Conclude",
        "connective": null,
        "expr": {
          "type": "Atom",
          "condition": "result > 0",
          "atomKind": "expression",
          "unsupported": false,
          "reason": null
        }
      }
    ]
  }
];

function evaluateProgram(nodes: ProgramNode[]) {
  const scope: Record<string, unknown> = {};
  const steps = nodes.map(node => evaluateNode(node, scope));
  const value = foldChain(steps.map(step => ({ value: step.value, connective: step.connective })));
  return { value, steps };
}

function evaluateNode(node: ProgramNode, scope: Record<string, unknown>) {
  switch (node.type) {
    case 'Theorem':
    case 'Proof':
    case 'Lemma':
    case 'Definition': {
      const childScope = { ...scope };
      const children = node.body.map((child: ProgramNode) => evaluateNode(child, childScope));
      const value = foldChain(children.map((child: any) => ({ value: child.value, connective: child.connective })));
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        value,
        detail: value ? null : `${node.type} failed`,
        children,
      };
    }
    case 'Struct':
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        value: true,
        detail: null,
        fields: node.fields,
      };
    case 'TypeDecl':
      registerType(node, scope);
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        value: true,
        detail: null,
        fields: node.variants,
      };
    case 'FnDecl': {
      const fn = defineRuntimeFunction(node, scope);
      scope[node.name] = fn;
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        value: true,
        detail: `fn ${node.name}`,
        label: node.name,
      };
    }
    case 'Assert':
    case 'Assume':
    case 'Conclude': {
      const result = evaluateExpr(node.expr, scope);
      return {
        type: node.type,
        connective: node.connective,
        value: node.type === 'Assume' ? true : result.value,
        detail: result.detail ?? null,
        label: result.label,
      };
    }
    case 'Apply':
      return {
        type: node.type,
        connective: node.connective,
        value: true,
        detail: `Applied ${node.target}`,
        label: node.target,
      };
    case 'SetVar': {
      const value = resolveValue(node.value, scope);
      scope[node.varName] = value;
      return {
        type: node.type,
        connective: node.connective,
        value: true,
        detail: node.varType ? `${node.varName}: ${node.varType}` : null,
        label: node.value == null ? node.varName : `${node.varName} = ${String(value)}`,
      };
    }
    case 'Raw':
      return {
        type: node.type,
        connective: node.connective,
        value: true,
        detail: node.content,
        label: node.content,
      };
    case 'Match':
      try {
        const matched = evaluateMatchNode(node, scope);
        return {
          type: node.type,
          connective: node.connective,
          value: matched.value,
          detail: matched.detail ?? null,
          label: matched.label,
        };
      } catch (error) {
        return {
          type: node.type,
          connective: node.connective,
          value: false,
          detail: error instanceof Error ? error.message : 'Match failed',
          label: 'match',
        };
      }
    default:
      return {
        type: 'Unknown',
        connective: null,
        value: false,
        detail: 'Unknown node',
        label: 'unknown',
      };
  }
}

function evaluateExpr(expr: ProgramNode, scope: Record<string, unknown>): EvalResult {
  switch (expr.type) {
    case 'Atom':
      return evaluateAtom(expr, scope);
    case 'SetBuilder':
    case 'IndexedUnion':
      return {
        value: false,
        label: renderExprLabel(expr),
        detail: 'Set-builder and indexed-union expressions are outside the executable subset.',
      };
    case 'Quantified':
      return {
        value: false,
        label: renderExprLabel(expr),
        detail: 'Quantified expressions are outside the executable subset.',
      };
    case 'If': {
      const condition = evaluateExpr(expr.condition, scope);
      return condition.value
        ? evaluateExpr(expr.thenBranch, scope)
        : evaluateExpr(expr.elseBranch, scope);
    }
    case 'LetExpr': {
      const childScope = { ...scope };
      childScope[expr.name] = resolveExprValue(expr.value, scope);
      return evaluateExpr(expr.body, childScope);
    }
    case 'Lambda':
      return {
        value: true,
        label: renderExprLabel(expr),
        detail: null,
      };
    case 'And': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: left.value && right.value, label: `(${left.label} ∧ ${right.label})`, detail: left.detail ?? right.detail };
    }
    case 'Or': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: left.value || right.value, label: `(${left.label} ∨ ${right.label})`, detail: left.detail ?? right.detail };
    }
    case 'Implies': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: !left.value || right.value, label: `(${left.label} → ${right.label})`, detail: left.detail ?? right.detail };
    }
    case 'Iff': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: left.value === right.value, label: `(${left.label} ↔ ${right.label})`, detail: left.detail ?? right.detail };
    }
    case 'Not': {
      const inner = evaluateExpr(expr.operand, scope);
      return { value: !inner.value, label: `¬${inner.label}`, detail: inner.detail };
    }
    default:
      return { value: false, label: 'unsupported expression', detail: 'Unsupported expression node' };
  }
}

function renderExprLabel(expr: ProgramNode): string {
  switch (expr.type) {
    case 'Atom':
      return expr.condition;
    case 'SetBuilder':
      return '{' + expr.element + ' | ' + expr.variable + ' ∈ ' + expr.domain + '}';
    case 'IndexedUnion':
      return '∪' + renderExprLabel(expr.builder);
    case 'Quantified': {
      const symbol = expr.quantifier === 'forall' ? '∀' : expr.quantifier === 'exists' ? '∃' : '∃!';
      const binder = expr.binderStyle === 'bounded'
        ? expr.variable + ' ∈ ' + expr.domain
        : expr.variable + ': ' + expr.domain;
      return expr.body ? symbol + ' ' + binder + ', ' + renderExprLabel(expr.body) : symbol + ' ' + binder;
    }
    case 'And':
      return '(' + renderExprLabel(expr.left) + ' ∧ ' + renderExprLabel(expr.right) + ')';
    case 'Or':
      return '(' + renderExprLabel(expr.left) + ' ∨ ' + renderExprLabel(expr.right) + ')';
    case 'Implies':
      return '(' + renderExprLabel(expr.left) + ' → ' + renderExprLabel(expr.right) + ')';
    case 'Iff':
      return '(' + renderExprLabel(expr.left) + ' ↔ ' + renderExprLabel(expr.right) + ')';
    case 'Not':
      return '¬' + renderExprLabel(expr.operand);
    case 'If':
      return 'if ' + renderExprLabel(expr.condition) + ' then ' + renderExprLabel(expr.thenBranch) + ' else ' + renderExprLabel(expr.elseBranch);
    case 'LetExpr':
      return 'let ' + expr.name + ' = ' + renderExprLabel(expr.value) + ' in ' + renderExprLabel(expr.body);
    case 'Lambda':
      return 'fn(' + expr.params.map((param: any) => param.name + ': ' + param.type).join(', ') + ') => ' + renderExprLabel(expr.body);
    default:
      return 'unsupported expression';
  }
}

function evaluateAtom(atom: ProgramNode, scope: Record<string, unknown>): EvalResult {
  const label = atom.condition.trim();
  if (atom.atomKind === 'string') {
    return { value: true, label };
  }
  if (atom.unsupported) {
    return { value: false, label, detail: atom.reason };
  }
  if (label === 'true') return { value: true, label };
  if (label === 'false') return { value: false, label };

  try {
    const safe = label.replace(/(?<![=!<>])=(?!=)/g, '==');
    const fn = new Function('scope', `with (scope) { return !!(${safe}); }`);
    return { value: !!fn(scope), label };
  } catch {
    return { value: false, label, detail: 'Expression could not be executed in the web backend' };
  }
}

function resolveValue(raw: string | null, scope: Record<string, unknown>) {
  if (raw == null) return undefined;
  const trimmed = raw.trim();
  try {
    const fn = new Function('scope', `with (scope) { return (${trimmed}); }`);
    return fn(scope);
  } catch {
    return trimmed;
  }
}

function resolveExprValue(expr: ProgramNode, scope: Record<string, unknown>): unknown {
  switch (expr.type) {
    case 'Atom':
      return resolveValue(expr.condition, scope);
    case 'If':
      return evaluateExpr(expr.condition, scope).value
        ? resolveExprValue(expr.thenBranch, scope)
        : resolveExprValue(expr.elseBranch, scope);
    case 'LetExpr': {
      const childScope = { ...scope };
      childScope[expr.name] = resolveExprValue(expr.value, scope);
      return resolveExprValue(expr.body, childScope);
    }
    case 'Lambda':
      return (...args: unknown[]) => {
        const childScope = { ...scope };
        expr.params.forEach((param: any, index: number) => {
          childScope[param.name] = args[index];
        });
        return resolveExprValue(expr.body, childScope);
      };
    case 'And':
    case 'Or':
    case 'Implies':
    case 'Iff':
    case 'Not':
      return evaluateExpr(expr, scope).value;
    case 'Fold': {
      const sequence = resolveValue(expr.sequence, scope);
      const init = resolveValue(expr.init, scope);
      const fn = resolveValue(expr.fn, scope);
      if (!Array.isArray(sequence) || typeof fn !== 'function') return null;
      return sequence.reduce((acc, item) => fn(acc, item), init);
    }
    default:
      return null;
  }
}

function defineRuntimeFunction(node: ProgramNode, scope: Record<string, unknown>) {
  return (...args: unknown[]) => {
    const childScope: Record<string, unknown> = { ...scope };
    node.params.forEach((param: any, index: number) => {
      childScope[param.name] = args[index];
    });
    for (const child of node.body) {
      if (child.type === 'SetVar') {
        childScope[child.varName] = resolveValue(child.value, childScope);
        continue;
      }
      if (child.type === 'Conclude') {
        return resolveExprValue(child.expr, childScope);
      }
      if (child.type === 'Match') {
        return evaluateMatchValue(child, childScope);
      }
      if (child.type === 'Assert') {
        const result = evaluateExpr(child.expr, childScope);
        if (!result.value) throw new Error(result.detail ?? 'Assertion failed');
      }
    }
    return undefined;
  };
}

function registerType(node: ProgramNode, scope: Record<string, unknown>) {
  for (const variant of node.variants) {
    const fieldNames = variant.fields.map((field: any) => field.name);
    if (fieldNames.length === 0) {
      scope[variant.name] = { tag: variant.name };
      continue;
    }
    scope[variant.name] = (...args: unknown[]) => {
      const value: Record<string, unknown> = { tag: variant.name };
      fieldNames.forEach((fieldName: string, index: number) => {
        value[fieldName] = args[index];
      });
      return value;
    };
  }
}

function evaluateMatchNode(node: ProgramNode, scope: Record<string, unknown>) {
  const value = evaluateMatchValue(node, scope);
  return {
    value: true,
    label: 'match',
    detail: value === undefined ? null : String(value),
  };
}

function evaluateMatchValue(node: ProgramNode, scope: Record<string, unknown>) {
  const scrutinee = resolveExprValue(node.scrutinee, scope);
  for (const matchCase of node.cases) {
    const bindings = matchPattern(matchCase.pattern, scrutinee);
    if (!bindings) continue;
    const childScope = { ...scope, ...bindings };
    for (const child of matchCase.body) {
      if (child.type === 'Conclude') {
        return resolveExprValue(child.expr, childScope);
      }
      if (child.type === 'Match') {
        return evaluateMatchValue(child, childScope);
      }
      if (child.type === 'SetVar') {
        childScope[child.varName] = resolveValue(child.value, childScope);
      }
    }
    return undefined;
  }
  throw new Error('Non-exhaustive match in web runtime');
}

function matchPattern(pattern: any, value: unknown): Record<string, unknown> | null {
  if (pattern.kind === 'wildcard') return {};
  if (pattern.kind === 'list_nil') return Array.isArray(value) && value.length === 0 ? {} : null;
  if (pattern.kind === 'list_cons') {
    if (!Array.isArray(value) || value.length === 0) return null;
    return {
      ...(pattern.head !== '_' ? { [pattern.head]: value[0] } : {}),
      [pattern.tail]: value.slice(1),
    };
  }
  if (pattern.kind === 'variant') {
    if (pattern.constructor === 'true' || pattern.constructor === 'false') {
      return value === (pattern.constructor === 'true') ? {} : null;
    }
    if (!value || typeof value !== 'object' || (value as any).tag !== pattern.constructor) return null;
    const entries: Record<string, unknown> = {};
    pattern.bindings.forEach((binding: string, index: number) => {
      if (!binding || binding === '_') return;
      const keys = Object.keys(value as Record<string, unknown>).filter(key => key !== 'tag');
      entries[binding] = (value as Record<string, unknown>)[keys[index]];
    });
    return entries;
  }
  return null;
}

function foldChain(items: Array<{ value: boolean; connective: string | null }>) {
  if (items.length === 0) return true;
  let acc = items[items.length - 1].value;
  for (let i = items.length - 2; i >= 0; i--) {
    const left = items[i].value;
    const conn = items[i].connective ?? '→';
    if (conn === '∧') acc = left && acc;
    else if (conn === '↔') acc = left === acc;
    else acc = !left || acc;
  }
  return acc;
}

function statusLabel(value: boolean) {
  return value ? 'Chain Holds' : 'Chain Fails';
}

function App() {
  const result = evaluateProgram(program);

  return (
    <main className="app-shell">
      <section className="hero">
        <p className="eyebrow">FuturLang React Backend</p>
        <h1>Web apps as proofs</h1>
        <p className="lead">
          This app is generated from a single FuturLang truth chain. The UI exists to expose whether the chain holds.
        </p>
        <div className={`verdict ${result.value ? 'ok' : 'bad'}`}>
          <span>{statusLabel(result.value)}</span>
          <strong>{String(result.value)}</strong>
        </div>
      </section>

      <section className="panel">
        <h2>Program Steps</h2>
        <div className="steps">
          {result.steps.map((step: any, index: number) => (
            <article className={`step ${step.value ? 'ok' : 'bad'}`} key={index}>
              <div className="step-top">
                <span className="step-kind">{step.type}</span>
                <span className="step-value">{String(step.value)}</span>
              </div>
              <h3>{step.name ?? step.label ?? 'Unnamed step'}</h3>
              {step.detail ? <p>{step.detail}</p> : null}
              {step.children?.length ? (
                <ul>
                  {step.children.map((child: any, childIndex: number) => (
                    <li key={childIndex}>
                      <code>{child.type}</code> {child.name ?? child.label ?? 'step'}: {String(child.value)}
                      {child.detail ? <span> · {child.detail}</span> : null}
                    </li>
                  ))}
                </ul>
              ) : null}
            </article>
          ))}
        </div>
      </section>
    </main>
  );
}

export default App;
