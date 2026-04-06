"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.createReactApp = createReactApp;
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const MATH_CHARS = /[∀∃⇒≥≤≠∈∉⊆⊇∪∩∧∨¬→↔λΣ∑∏√∞·]/;
const MATH_NOTATION = /\|[^|]|\bmod\b|divides|\{.*\|/;
function createReactApp(nodes, outDir) {
    fs.mkdirSync(outDir, { recursive: true });
    fs.mkdirSync(path.join(outDir, 'src'), { recursive: true });
    const program = serializeNodes(nodes);
    fs.writeFileSync(path.join(outDir, 'package.json'), reactPackageJson, 'utf8');
    fs.writeFileSync(path.join(outDir, 'tsconfig.json'), reactTsconfig, 'utf8');
    fs.writeFileSync(path.join(outDir, 'vite.config.ts'), reactViteConfig, 'utf8');
    fs.writeFileSync(path.join(outDir, 'index.html'), reactIndexHtml, 'utf8');
    fs.writeFileSync(path.join(outDir, 'src', 'main.tsx'), reactMainTsx, 'utf8');
    fs.writeFileSync(path.join(outDir, 'src', 'App.tsx'), renderReactApp(program), 'utf8');
    fs.writeFileSync(path.join(outDir, 'src', 'styles.css'), reactStylesCss, 'utf8');
}
function serializeNodes(nodes) {
    return nodes.map(serializeNode);
}
function serializeNode(node) {
    switch (node.type) {
        case 'Theorem':
        case 'Proof':
        case 'Lemma':
        case 'Definition':
            return {
                type: node.type,
                name: node.name,
                connective: node.connective,
                body: node.body.map(serializeNode),
            };
        case 'Struct':
            return {
                type: node.type,
                name: node.name,
                connective: node.connective,
                fields: node.fields,
            };
        case 'Assert':
        case 'Assume':
        case 'Conclude':
            return {
                type: node.type,
                connective: node.connective,
                expr: serializeExpr(node.expr),
            };
        case 'Apply':
            return { type: node.type, connective: node.connective, target: node.target };
        case 'SetVar':
            return {
                type: node.type,
                connective: node.connective,
                varName: node.varName,
                varType: node.varType,
                value: node.value,
            };
        case 'Raw':
            return { type: node.type, connective: node.connective, content: node.content };
        default:
            return node;
    }
}
function serializeExpr(expr) {
    switch (expr.type) {
        case 'Atom':
            return serializeAtom(expr);
        case 'And':
        case 'Or':
        case 'Implies':
        case 'Iff':
            return {
                type: expr.type,
                left: serializeExpr(expr.left),
                right: serializeExpr(expr.right),
            };
        case 'Not':
            return {
                type: expr.type,
                operand: serializeExpr(expr.operand),
            };
        default:
            return expr;
    }
}
function serializeAtom(atom) {
    const trimmed = atom.condition.trim();
    const unsupported = atom.atomKind === 'opaque' ||
        (atom.atomKind !== 'string' && (MATH_CHARS.test(trimmed) || MATH_NOTATION.test(trimmed)));
    return {
        type: atom.type,
        condition: atom.condition,
        atomKind: atom.atomKind,
        unsupported,
        reason: unsupported
            ? 'This claim is outside the strict executable subset. Use Lean verification for formal support.'
            : null,
    };
}
function renderReactApp(program) {
    return `import './styles.css';

type ProgramNode = any;
type EvalResult = { value: boolean; label: string; detail?: string | null };

const program: ProgramNode[] = ${JSON.stringify(program, null, 2)};

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
        detail: value ? null : \`\${node.type} failed\`,
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
        detail: \`Applied \${node.target}\`,
        label: node.target,
      };
    case 'SetVar': {
      const value = resolveValue(node.value, scope);
      scope[node.varName] = value;
      return {
        type: node.type,
        connective: node.connective,
        value: true,
        detail: node.varType ? \`\${node.varName}: \${node.varType}\` : null,
        label: node.value == null ? node.varName : \`\${node.varName} = \${String(value)}\`,
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
      return { value: left.value && right.value, label: \`(\${left.label} ∧ \${right.label})\`, detail: left.detail ?? right.detail };
    }
    case 'Or': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: left.value || right.value, label: \`(\${left.label} ∨ \${right.label})\`, detail: left.detail ?? right.detail };
    }
    case 'Implies': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: !left.value || right.value, label: \`(\${left.label} → \${right.label})\`, detail: left.detail ?? right.detail };
    }
    case 'Iff': {
      const left = evaluateExpr(expr.left, scope);
      const right = evaluateExpr(expr.right, scope);
      return { value: left.value === right.value, label: \`(\${left.label} ↔ \${right.label})\`, detail: left.detail ?? right.detail };
    }
    case 'Not': {
      const inner = evaluateExpr(expr.operand, scope);
      return { value: !inner.value, label: \`¬\${inner.label}\`, detail: inner.detail };
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
    const fn = new Function('scope', \`with (scope) { return !!(\${safe}); }\`);
    return { value: !!fn(scope), label };
  } catch {
    return { value: false, label, detail: 'Expression could not be executed in the web backend' };
  }
}

function resolveValue(raw: string | null, scope: Record<string, unknown>) {
  if (raw == null) return undefined;
  const trimmed = raw.trim();
  try {
    const fn = new Function('scope', \`with (scope) { return (\${trimmed}); }\`);
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
        <div className={\`verdict \${result.value ? 'ok' : 'bad'}\`}>
          <span>{statusLabel(result.value)}</span>
          <strong>{String(result.value)}</strong>
        </div>
      </section>

      <section className="panel">
        <h2>Program Steps</h2>
        <div className="steps">
          {result.steps.map((step: any, index: number) => (
            <article className={\`step \${step.value ? 'ok' : 'bad'}\`} key={index}>
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
`;
}
const reactPackageJson = `{
  "name": "futurlang-webapp",
  "private": true,
  "version": "0.0.0",
  "type": "module",
  "scripts": {
    "dev": "vite",
    "build": "tsc && vite build",
    "preview": "vite preview"
  },
  "dependencies": {
    "react": "^18.3.1",
    "react-dom": "^18.3.1"
  },
  "devDependencies": {
    "@types/react": "^18.3.3",
    "@types/react-dom": "^18.3.0",
    "@vitejs/plugin-react": "^4.3.1",
    "typescript": "^5.6.3",
    "vite": "^5.4.8"
  }
}
`;
const reactTsconfig = `{
  "compilerOptions": {
    "target": "ES2020",
    "useDefineForClassFields": true,
    "lib": ["ES2020", "DOM", "DOM.Iterable"],
    "allowJs": false,
    "skipLibCheck": true,
    "esModuleInterop": true,
    "allowSyntheticDefaultImports": true,
    "strict": true,
    "forceConsistentCasingInFileNames": true,
    "module": "ESNext",
    "moduleResolution": "Node",
    "resolveJsonModule": true,
    "isolatedModules": true,
    "noEmit": true,
    "jsx": "react-jsx"
  },
  "include": ["src"],
  "references": []
}
`;
const reactViteConfig = `import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

export default defineConfig({
  plugins: [react()],
});
`;
const reactIndexHtml = `<!doctype html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>FuturLang Webapp</title>
  </head>
  <body>
    <div id="root"></div>
    <script type="module" src="/src/main.tsx"></script>
  </body>
</html>
`;
const reactMainTsx = `import React from 'react';
import ReactDOM from 'react-dom/client';
import App from './App';

ReactDOM.createRoot(document.getElementById('root')!).render(
  <React.StrictMode>
    <App />
  </React.StrictMode>,
);
`;
const reactStylesCss = `:root {
  color: #161616;
  background:
    radial-gradient(circle at top, rgba(242, 188, 120, 0.45), transparent 32rem),
    linear-gradient(180deg, #f4efe6 0%, #efe7d9 100%);
  font-family: "Iowan Old Style", "Palatino Linotype", serif;
}

* {
  box-sizing: border-box;
}

body {
  margin: 0;
  min-width: 320px;
}

#root {
  min-height: 100vh;
}

.app-shell {
  width: min(1100px, calc(100vw - 2rem));
  margin: 0 auto;
  padding: 2rem 0 4rem;
}

.hero {
  padding: 2rem;
  border: 1px solid rgba(22, 22, 22, 0.12);
  background: rgba(255, 252, 246, 0.78);
  backdrop-filter: blur(12px);
  box-shadow: 0 20px 70px rgba(84, 53, 14, 0.09);
}

.eyebrow {
  margin: 0 0 0.5rem;
  text-transform: uppercase;
  letter-spacing: 0.18em;
  font-size: 0.75rem;
}

.hero h1,
.panel h2,
.step h3 {
  font-family: Georgia, "Times New Roman", serif;
}

.hero h1 {
  margin: 0;
  font-size: clamp(2.5rem, 6vw, 5rem);
  line-height: 0.95;
}

.lead {
  max-width: 44rem;
  font-size: 1.08rem;
}

.verdict {
  display: inline-flex;
  gap: 1rem;
  align-items: center;
  padding: 0.85rem 1.15rem;
  border-radius: 999px;
  margin-top: 1rem;
  font-weight: 600;
}

.verdict.ok,
.step.ok {
  background: rgba(45, 122, 74, 0.12);
  border: 1px solid rgba(45, 122, 74, 0.3);
}

.verdict.bad,
.step.bad {
  background: rgba(154, 54, 37, 0.1);
  border: 1px solid rgba(154, 54, 37, 0.28);
}

.panel {
  margin-top: 1.5rem;
}

.steps {
  display: grid;
  grid-template-columns: repeat(auto-fit, minmax(260px, 1fr));
  gap: 1rem;
}

.step {
  padding: 1rem;
  background: rgba(255, 252, 246, 0.82);
}

.step-top {
  display: flex;
  justify-content: space-between;
  gap: 1rem;
  font-size: 0.85rem;
  text-transform: uppercase;
  letter-spacing: 0.08em;
}

.step h3 {
  margin-bottom: 0.5rem;
}

.step ul {
  padding-left: 1.1rem;
  margin: 0.75rem 0 0;
}

.step code {
  font-family: "SFMono-Regular", Consolas, monospace;
}

@media (max-width: 640px) {
  .app-shell {
    width: min(100vw - 1rem, 100%);
    padding-top: 1rem;
  }

  .hero,
  .step {
    padding: 1rem;
  }
}
`;
