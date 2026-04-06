import './styles.css';

type ProgramNode = any;
type EvalResult = { value: boolean; label: string; detail?: string | null };

const program: ProgramNode[] = [
  {
    "type": "Theorem",
    "name": "Hello_World",
    "connective": null,
    "body": [
      {
        "type": "Assert",
        "connective": "∧",
        "expr": {
          "type": "Atom",
          "condition": "\"Hello World can be proven\"",
          "atomKind": "string",
          "unsupported": false,
          "reason": null
        }
      },
      {
        "type": "Proof",
        "name": "Hello_World",
        "connective": null,
        "body": [
          {
            "type": "SetVar",
            "connective": null,
            "varName": "message",
            "varType": null,
            "value": "\"Hello World\""
          },
          {
            "type": "Assert",
            "connective": null,
            "expr": {
              "type": "Atom",
              "condition": "message ==\"Hello World\"",
              "atomKind": "expression",
              "unsupported": false,
              "reason": null
            }
          }
        ]
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
