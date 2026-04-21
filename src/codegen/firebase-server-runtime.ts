// src/codegen/firebase-server-runtime.ts
//
// Injected by the CLI on top of runtimePreamble when running a Firebase server project.
// Only included when package.flson has a "firebase" key — never baked into the base runtime.

export function buildFirebaseServerRuntime(projectId: string): string {
  return `
// ── Firestore REST helpers (injected for Firebase server projects) ─────────────

function _httpsReq(method, url, body, headers) {
  const https = require('https');
  return new Promise((resolve, reject) => {
    const parsed = new URL(url);
    const bodyStr = body != null ? JSON.stringify(body) : null;
    const opts = {
      hostname: parsed.hostname,
      path: parsed.pathname + parsed.search,
      method,
      headers: {
        'Content-Type': 'application/json',
        ...(bodyStr ? { 'Content-Length': Buffer.byteLength(bodyStr) } : {}),
        ...headers,
      },
    };
    const req = https.request(opts, res => {
      let data = '';
      res.on('data', c => { data += c; });
      res.on('end', () => {
        try { resolve({ status: res.statusCode, body: JSON.parse(data) }); }
        catch { resolve({ status: res.statusCode, body: data }); }
      });
    });
    req.on('error', reject);
    if (bodyStr) req.write(bodyStr);
    req.end();
  });
}

function _toFirestoreFields(obj) {
  const fields = {};
  for (const [k, v] of Object.entries(obj || {})) {
    if (typeof v === 'string') fields[k] = { stringValue: v };
    else if (typeof v === 'number' && Number.isInteger(v)) fields[k] = { integerValue: String(v) };
    else if (typeof v === 'number') fields[k] = { doubleValue: v };
    else if (typeof v === 'boolean') fields[k] = { booleanValue: v };
    else if (v == null) fields[k] = { nullValue: null };
  }
  return fields;
}

function _fromFirestoreDoc(doc) {
  const id = doc.name ? doc.name.split('/').pop() : null;
  const out = { id };
  for (const [k, v] of Object.entries(doc.fields || {})) {
    if (v.stringValue  !== undefined) out[k] = v.stringValue;
    else if (v.integerValue !== undefined) out[k] = Number(v.integerValue);
    else if (v.doubleValue  !== undefined) out[k] = v.doubleValue;
    else if (v.booleanValue !== undefined) out[k] = v.booleanValue;
    else if (v.timestampValue !== undefined) out[k] = v.timestampValue;
    else out[k] = null;
  }
  return out;
}

const _FIRESTORE_PROJECT = ${JSON.stringify(projectId)};
const _FIRESTORE_BASE = \`https://firestore.googleapis.com/v1/projects/\${_FIRESTORE_PROJECT}/databases/(default)/documents\`;

function firestoreList(collection, userId, idToken) {
  const url = _FIRESTORE_BASE + ':runQuery';
  const body = {
    structuredQuery: {
      from: [{ collectionId: collection }],
      where: userId ? {
        fieldFilter: {
          field: { fieldPath: 'userId' },
          op: 'EQUAL',
          value: { stringValue: userId },
        },
      } : undefined,
    },
  };
  return _httpsReq('POST', url, body, { Authorization: 'Bearer ' + idToken })
    .then(r => {
      if (!Array.isArray(r.body)) return [];
      return r.body
        .filter(entry => entry && entry.document)
        .map(entry => _fromFirestoreDoc(entry.document));
    });
}

function firestoreCreate(collection, data, idToken) {
  const url = \`\${_FIRESTORE_BASE}/\${collection}\`;
  return _httpsReq('POST', url, { fields: _toFirestoreFields(data) }, { Authorization: 'Bearer ' + idToken })
    .then(r => {
      if (!r.body || !r.body.name) throw new Error('Firestore create failed: ' + JSON.stringify(r.body));
      return _fromFirestoreDoc(r.body);
    });
}

function firestoreUpdate(collection, docId, data, idToken) {
  const fields = _toFirestoreFields(data);
  const mask = Object.keys(fields)
    .map(k => 'updateMask.fieldPaths=' + encodeURIComponent(k))
    .join('&');
  const url = \`\${_FIRESTORE_BASE}/\${collection}/\${docId}?\${mask}\`;
  return _httpsReq('PATCH', url, { fields }, { Authorization: 'Bearer ' + idToken })
    .then(() => ({ id: docId, ...data }));
}

function firestoreDelete(collection, docId, idToken) {
  const url = \`\${_FIRESTORE_BASE}/\${collection}/\${docId}\`;
  return _httpsReq('DELETE', url, null, { Authorization: 'Bearer ' + idToken })
    .then(() => ({ ok: true, id: docId }));
}
`;
}
