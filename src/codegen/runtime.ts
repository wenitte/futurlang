// src/codegen/runtime.ts

export const runtimePreamble = `
// ── FuturLang Runtime ─────────────────────────────────────────────────────────

const _usedNames  = new Set();
const _lemmaCache = new Map();
const _vars       = new Map();
const _fnMeta     = new Map();
const _typeMeta   = new Map();
const _nodeHttp   = typeof require === 'function' ? require('http') : null;

// Resolve a result object or raw value to boolean
function _resolve(v) {
  if (v && typeof v === 'object' && 'value' in v) return !!v.value;
  if (typeof v === 'function') return !!v();
  return !!v;
}

// ── Atom ──────────────────────────────────────────────────────────────────────
function atom(v, label) {
  const value = typeof v === 'function' ? !!v() : !!v;
  return { kind: 'atom', value, label: label ?? String(v) };
}

function unsupportedExpr(label, reason) {
  throw new Error(reason + ': ' + label);
}

function execExpr(fn, label) {
  return atom(() => fn(), label);
}

// ── Connectives ───────────────────────────────────────────────────────────────
function and(a, b) {
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'and', value: lv && rv, left: a, right: b };
}
function or(a, b) {
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'or', value: lv || rv, left: a, right: b };
}
function seq(aFn, bFn) {
  // Evaluate left side first (runs setVar side-effects, etc.)
  const a  = aFn();
  const lv = _resolve(a);
  // Only evaluate right side if left holds (short-circuit like →)
  const b  = bFn();
  const rv = _resolve(b);
  return { kind: 'implies', value: !lv || rv, antecedent: a, consequent: b };
}

function implies(a, b) {
  // P → Q  ≡  ¬P ∨ Q  (logical connective inside expressions)
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'implies', value: !lv || rv, antecedent: a, consequent: b };
}

function iff(a, b) {
  const lv = _resolve(a), rv = _resolve(b);
  return { kind: 'iff', value: lv === rv, left: a, right: b };
}
function not(a) {
  const v = _resolve(a);
  return { kind: 'not', value: !v, operand: a };
}

// ── Describe ──────────────────────────────────────────────────────────────────
function _describe(r) {
  if (typeof r !== 'object' || r === null) return String(r);
  switch (r.kind) {
    case 'atom':    return r.label ?? '(expr)';
    case 'and':     return '(' + _describe(r.left)       + ' ∧ ' + _describe(r.right)      + ')';
    case 'or':      return '(' + _describe(r.left)       + ' ∨ ' + _describe(r.right)      + ')';
    case 'implies': return '(' + _describe(r.antecedent) + ' → ' + _describe(r.consequent) + ')';
    case 'iff':     return '(' + _describe(r.left)       + ' ↔ ' + _describe(r.right)      + ')';
    case 'not':     return '(¬' + _describe(r.operand)   + ')';
    default:        return JSON.stringify(r);
  }
}

// ── Statement evaluators ──────────────────────────────────────────────────────

function assertExpr(result) {
  const val = _resolve(result);
  if (!val) throw new Error('Assertion failed: ' + _describe(result));
  console.log('  assert ✓', _describe(result));
  return result;
}

function _runtimeAssert(value, label) {
  if (!value) throw new Error('Assertion failed: ' + label);
  return value;
}

function assumeExpr(result) {
  // Assumptions are axioms — always accepted, establish the proof context
  const desc = typeof result === 'object' ? _describe(result) : String(result);
  console.log('  assume  ', desc);
  return atom(true, 'assume(' + desc + ')');
}

function concludeExpr(result) {
  const val = _resolve(result);
  console.log('  conclude' + (val ? ' ✓' : ' ✗'), _describe(result));
  return result;
}

function applyLemma(name) {
  const result = _lemmaCache.get(name.toLowerCase());
  if (result === undefined) {
    console.log('  apply   ', name, '(not yet registered, assuming true)');
    return atom(true, 'apply(' + name + ')');
  }
  console.log('  apply ✓ ', name);
  return result;
}

function setVar(name, value, label) {
  // Execute immediately — variable must exist before right-hand side evaluates
  const resolved = typeof value === 'function' ? value() : value;
  globalThis[name] = resolved;
  _vars.set(name, globalThis[name]);
  console.log('  let     ', label ?? name, value !== undefined ? '= ' + String(globalThis[name]) : '');
  return atom(true, label ?? name);
}

function defineFn(name, fn, meta) {
  globalThis[name] = fn;
  _fnMeta.set(name, meta ?? null);
  console.log('\\nfn ' + name);
  return atom(true, 'fn(' + name + ')');
}

function defineType(name, variants) {
  _typeMeta.set(name, variants);
  for (const [variant, fields] of Object.entries(variants)) {
    if (!Array.isArray(fields) || fields.length === 0) {
      globalThis[variant] = { tag: variant };
      continue;
    }
    globalThis[variant] = (...args) => {
      const value = { tag: variant };
      fields.forEach((field, index) => { value[field] = args[index]; });
      return value;
    };
  }
  console.log('\\nType ' + name);
  return atom(true, 'type(' + name + ')');
}

function _fold(sequence, init, fn) {
  if (!Array.isArray(sequence)) throw new Error('fold expects a list/array');
  return sequence.reduce((acc, item) => fn(acc, item), init);
}

function request(method, url, body = null, headers = {}) {
  const parsed = _parseUrl(url);
  return {
    method: String(method).toUpperCase(),
    url: parsed.url,
    path: parsed.path,
    query: parsed.query,
    headers: headers ?? {},
    body,
  };
}

function text(body, status = 200, headers = {}) {
  return _response(status, { 'content-type': 'text/plain; charset=utf-8', ...headers }, String(body));
}

function html(body, status = 200, headers = {}) {
  return _response(status, { 'content-type': 'text/html; charset=utf-8', ...headers }, String(body));
}

function json(body, status = 200, headers = {}) {
  return _response(status, { 'content-type': 'application/json; charset=utf-8', ...headers }, JSON.stringify(body));
}

function route(method, path, handler) {
  return {
    method: String(method).toUpperCase(),
    path: String(path),
    handler,
  };
}

function router(routes, fallback) {
  return (req) => {
    for (const entry of routes) {
      if (!entry) continue;
      if (String(req.method).toUpperCase() !== entry.method) continue;
      if (req.path !== entry.path) continue;
      return dispatch(entry.handler, req);
    }
    if (fallback) return dispatch(fallback, req);
    return text('Not Found', 404);
  };
}

function dispatch(handler, req) {
  return _normalizeResponse(handler(req));
}

function serve(port, handler, host = '127.0.0.1') {
  if (!_nodeHttp) throw new Error('Node http runtime is unavailable');
  const server = _nodeHttp.createServer((req, res) => {
    const chunks = [];
    req.on('data', chunk => chunks.push(chunk));
    req.on('end', () => {
      const body = chunks.length > 0 ? Buffer.concat(chunks).toString('utf8') : null;
      const incoming = request(req.method ?? 'GET', req.url ?? '/', body, req.headers ?? {});
      const result = dispatch(handler, incoming);
      res.statusCode = result.status;
      for (const [name, value] of Object.entries(result.headers)) {
        res.setHeader(name, value);
      }
      res.end(result.body);
    });
  });
  console.log('  server … starting on http://' + host + ':' + port);
  server.on('error', (error) => {
    const message = error && typeof error === 'object' && 'message' in error
      ? String(error.message)
      : String(error);
    console.error('  server ✗ ' + message);
  });
  server.listen(port, host, () => {
    console.log('  server ✓ listening on http://' + host + ':' + port);
  });
  return server;
}

function _response(status, headers, body) {
  return {
    status: Number(status),
    headers: headers ?? {},
    body: body ?? '',
  };
}

function _normalizeResponse(value) {
  if (value && typeof value === 'object' && typeof value.status === 'number' && 'headers' in value && 'body' in value) {
    return {
      status: value.status,
      headers: value.headers ?? {},
      body: value.body ?? '',
    };
  }
  if (typeof value === 'string') return text(value);
  return json(value);
}

function _parseUrl(raw) {
  const parsed = new URL(String(raw), 'http://futurlang.local');
  const query = Object.fromEntries(parsed.searchParams.entries());
  return {
    url: parsed.pathname + parsed.search,
    path: parsed.pathname,
    query,
  };
}

// ── Block evaluators ──────────────────────────────────────────────────────────

function theorem(name, fn) {
  const key = name.toLowerCase();
  if (_usedNames.has(key)) throw new Error('Duplicate theorem: ' + name);
  _usedNames.add(key);
  console.log('\\nTheorem ' + name);
  const result = fn();
  const val = _resolve(result);
  console.log(val ? '  ✓ QED' : '  ✗ FAILED');
  return atom(val, 'theorem(' + name + ')');
}

function proof(name, fn) {
  console.log('\\nProof ' + name);
  const result = fn();
  const val = _resolve(result);
  console.log(val ? '  ✓ proof holds' : '  ✗ proof failed');
  return atom(val, 'proof(' + name + ')');
}

function lemma(name, fn) {
  console.log('\\nLemma ' + name);
  const result = fn();
  const val = _resolve(result);
  _lemmaCache.set(name.toLowerCase(), result);
  console.log(val ? '  ✓ lemma holds' : '  ✗ lemma failed');
  return atom(val, 'lemma(' + name + ')');
}

function definition(name, fn) {
  console.log('\\nDefinition ' + name);
  const result = fn();
  _lemmaCache.set(name.toLowerCase(), atom(true, name));
  return atom(true, 'definition(' + name + ')');
}

function struct_(name, fields) {
  console.log('\\nStruct ' + name);
  return atom(true, 'struct(' + name + ')');
}
`;
