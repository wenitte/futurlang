import * as fs from 'fs';
import * as path from 'path';
import { ASTNode, AtomNode, ExprNode } from '../parser/ast';

const MATH_CHARS = /[∀∃⇒≥≤≠∈∉⊆⊇∪∩∧∨¬→↔λΣ∑∏√∞·]/;
const MATH_NOTATION = /\|[^|]|\bmod\b|divides|\{.*\|/;

// ── Firebase detection ────────────────────────────────────────────────────────

interface FirebaseConfig {
  apiKey: string;
  authDomain: string;
  projectId: string;
  storageBucket: string;
  messagingSenderId: string;
  appId: string;
}

interface NoteField { name: string; type: string }

function stripQuotes(s: string): string {
  return s.trim().replace(/^["']|["']$/g, '');
}

function detectFirebaseConfig(nodes: ASTNode[]): FirebaseConfig | null {
  const vars: Record<string, string> = {};
  for (const node of nodes) {
    if (node.type === 'SetVar' && node.varName.startsWith('FIREBASE_') && node.value) {
      vars[node.varName] = stripQuotes(node.value);
    }
  }
  if (!vars['FIREBASE_API_KEY']) return null;
  return {
    apiKey:            vars['FIREBASE_API_KEY']            ?? '',
    authDomain:        vars['FIREBASE_AUTH_DOMAIN']        ?? '',
    projectId:         vars['FIREBASE_PROJECT_ID']         ?? '',
    storageBucket:     vars['FIREBASE_STORAGE_BUCKET']     ?? '',
    messagingSenderId: vars['FIREBASE_MESSAGING_SENDER_ID'] ?? '',
    appId:             vars['FIREBASE_APP_ID']             ?? '',
  };
}

function extractNoteFields(nodes: ASTNode[]): NoteField[] {
  for (const node of nodes) {
    if (node.type === 'Struct' && node.name === 'Note') {
      return node.fields.filter(f => f.name !== 'id');
    }
  }
  return [{ name: 'title', type: 'String' }, { name: 'body', type: 'String' }];
}

export function createReactApp(nodes: ASTNode[], outDir: string) {
  const fbConfig = detectFirebaseConfig(nodes);
  if (fbConfig) {
    const noteFields = extractNoteFields(nodes);
    createFirebaseNotesApp(fbConfig, noteFields, outDir);
    return;
  }
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

// ── Firebase Notes App Generator ──────────────────────────────────────────────

function createFirebaseNotesApp(config: FirebaseConfig, noteFields: NoteField[], outDir: string) {
  const srcDir = path.join(outDir, 'src');
  const componentsDir = path.join(srcDir, 'components');
  fs.mkdirSync(componentsDir, { recursive: true });

  fs.writeFileSync(path.join(outDir, 'package.json'),    firebasePackageJson, 'utf8');
  fs.writeFileSync(path.join(outDir, 'tsconfig.json'),   reactTsconfig,       'utf8');
  fs.writeFileSync(path.join(outDir, 'vite.config.ts'),  reactViteConfig,     'utf8');
  fs.writeFileSync(path.join(outDir, 'index.html'),      firebaseIndexHtml,   'utf8');
  fs.writeFileSync(path.join(outDir, '.env'),             buildEnvFile(config),'utf8');
  fs.writeFileSync(path.join(srcDir, 'main.tsx'),         reactMainTsx,        'utf8');
  fs.writeFileSync(path.join(srcDir, 'firebase.ts'),      buildFirebaseTs(config), 'utf8');
  fs.writeFileSync(path.join(srcDir, 'App.tsx'),          buildAppTsx(),       'utf8');
  fs.writeFileSync(path.join(srcDir, 'styles.css'),       firebaseStylesCss,  'utf8');
  fs.writeFileSync(path.join(componentsDir, 'Auth.tsx'),  buildAuthTsx(),      'utf8');
  fs.writeFileSync(path.join(componentsDir, 'Notes.tsx'), buildNotesTsx(noteFields), 'utf8');
}

function buildEnvFile(config: FirebaseConfig): string {
  return [
    `VITE_FIREBASE_API_KEY=${config.apiKey}`,
    `VITE_FIREBASE_AUTH_DOMAIN=${config.authDomain}`,
    `VITE_FIREBASE_PROJECT_ID=${config.projectId}`,
    `VITE_FIREBASE_STORAGE_BUCKET=${config.storageBucket}`,
    `VITE_FIREBASE_MESSAGING_SENDER_ID=${config.messagingSenderId}`,
    `VITE_FIREBASE_APP_ID=${config.appId}`,
  ].join('\n') + '\n';
}

function buildFirebaseTs(config: FirebaseConfig): string {
  return `import { initializeApp } from 'firebase/app';
import { getAuth, GoogleAuthProvider } from 'firebase/auth';
import { getFirestore } from 'firebase/firestore';

const firebaseConfig = {
  apiKey:            ${JSON.stringify(config.apiKey)},
  authDomain:        ${JSON.stringify(config.authDomain)},
  projectId:         ${JSON.stringify(config.projectId)},
  storageBucket:     ${JSON.stringify(config.storageBucket)},
  messagingSenderId: ${JSON.stringify(config.messagingSenderId)},
  appId:             ${JSON.stringify(config.appId)},
};

export const app      = initializeApp(firebaseConfig);
export const auth     = getAuth(app);
export const db       = getFirestore(app);
export const google   = new GoogleAuthProvider();
`;
}

function buildAppTsx(): string {
  return `import { useEffect, useState } from 'react';
import { onAuthStateChanged, User } from 'firebase/auth';
import { auth } from './firebase';
import Auth from './components/Auth';
import Notes from './components/Notes';
import './styles.css';

export default function App() {
  const [user, setUser] = useState<User | null>(null);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    return onAuthStateChanged(auth, (u) => { setUser(u); setLoading(false); });
  }, []);

  if (loading) return <div className="splash"><div className="spinner" /></div>;

  return user ? <Notes user={user} /> : <Auth />;
}
`;
}

function buildAuthTsx(): string {
  return `import { useState } from 'react';
import {
  createUserWithEmailAndPassword,
  signInWithEmailAndPassword,
  signInWithPopup,
} from 'firebase/auth';
import { auth, google } from '../firebase';

export default function Auth() {
  const [mode, setMode]       = useState<'login' | 'signup'>('login');
  const [email, setEmail]     = useState('');
  const [password, setPass]   = useState('');
  const [error, setError]     = useState('');
  const [busy, setBusy]       = useState(false);

  async function handleSubmit(e: React.FormEvent) {
    e.preventDefault();
    setError(''); setBusy(true);
    try {
      if (mode === 'signup') {
        await createUserWithEmailAndPassword(auth, email, password);
      } else {
        await signInWithEmailAndPassword(auth, email, password);
      }
    } catch (err: any) {
      setError(err.message ?? 'Authentication failed');
    } finally {
      setBusy(false);
    }
  }

  async function handleGoogle() {
    setError(''); setBusy(true);
    try {
      await signInWithPopup(auth, google);
    } catch (err: any) {
      setError(err.message ?? 'Google sign-in failed');
    } finally {
      setBusy(false);
    }
  }

  return (
    <div className="auth-shell">
      <div className="auth-card">
        <h1>Notes</h1>
        <p className="auth-sub">Powered by FuturLang</p>

        <div className="tab-row">
          <button className={mode === 'login'  ? 'tab active' : 'tab'} onClick={() => setMode('login')}>Sign in</button>
          <button className={mode === 'signup' ? 'tab active' : 'tab'} onClick={() => setMode('signup')}>Create account</button>
        </div>

        <form onSubmit={handleSubmit} className="auth-form">
          <label>
            Email
            <input type="email" value={email} onChange={e => setEmail(e.target.value)} required autoFocus />
          </label>
          <label>
            Password
            <input type="password" value={password} onChange={e => setPass(e.target.value)} required minLength={6} />
          </label>
          {error && <p className="error">{error}</p>}
          <button type="submit" className="btn-primary" disabled={busy}>
            {busy ? '…' : mode === 'login' ? 'Sign in' : 'Create account'}
          </button>
        </form>

        <div className="divider"><span>or</span></div>

        <button className="btn-google" onClick={handleGoogle} disabled={busy}>
          <svg width="18" height="18" viewBox="0 0 48 48"><path fill="#EA4335" d="M24 9.5c3.54 0 6.71 1.22 9.21 3.6l6.85-6.85C35.9 2.38 30.47 0 24 0 14.62 0 6.51 5.38 2.56 13.22l7.98 6.19C12.43 13.72 17.74 9.5 24 9.5z"/><path fill="#4285F4" d="M46.98 24.55c0-1.57-.15-3.09-.38-4.55H24v9.02h12.94c-.58 2.96-2.26 5.48-4.78 7.18l7.73 6c4.51-4.18 7.09-10.36 7.09-17.65z"/><path fill="#FBBC05" d="M10.53 28.59c-.48-1.45-.76-2.99-.76-4.59s.27-3.14.76-4.59l-7.98-6.19C.92 16.46 0 20.12 0 24c0 3.88.92 7.54 2.56 10.78l7.97-6.19z"/><path fill="#34A853" d="M24 48c6.48 0 11.93-2.13 15.89-5.81l-7.73-6c-2.15 1.45-4.92 2.3-8.16 2.3-6.26 0-11.57-4.22-13.47-9.91l-7.98 6.19C6.51 42.62 14.62 48 24 48z"/></svg>
          Continue with Google
        </button>
      </div>
    </div>
  );
}
`;
}

function buildNotesTsx(noteFields: NoteField[]): string {
  const hasBody = noteFields.some(f => f.name === 'body');
  return `import { useEffect, useState, useCallback } from 'react';
import {
  collection, query, where, onSnapshot,
  addDoc, updateDoc, deleteDoc, doc, serverTimestamp,
} from 'firebase/firestore';
import { signOut, User } from 'firebase/auth';
import { auth, db } from '../firebase';

interface Note {
  id: string;
  title: string;
  body: string;
  createdAt: any;
  userId: string;
}

type Mode = 'sdk' | 'api';
const API_BASE = 'http://localhost:3001';

export default function Notes({ user }: { user: User }) {
  const [notes, setNotes]   = useState<Note[]>([]);
  const [active, setActive] = useState<Note | null>(null);
  const [title, setTitle]   = useState('');
  const [body, setBody]     = useState('');
  const [saving, setSaving] = useState(false);
  const [search, setSearch] = useState('');
  const [mode, setMode]     = useState<Mode>('sdk');

  // ── SDK mode: real-time Firestore listener ──────────────────────────────────
  useEffect(() => {
    if (mode !== 'sdk') return;
    const q = query(collection(db, 'notes'), where('userId', '==', user.uid));
    return onSnapshot(q, snap => {
      const docs = snap.docs.map(d => ({ id: d.id, ...d.data() } as Note));
      // Sort client-side — avoids needing a composite Firestore index
      docs.sort((a, b) => {
        const ta = (a.createdAt as any)?.toMillis?.() ?? 0;
        const tb = (b.createdAt as any)?.toMillis?.() ?? 0;
        return tb - ta;
      });
      setNotes(docs);
    });
  }, [user.uid, mode]);

  // ── API mode: fetch from FL backend ────────────────────────────────────────
  const fetchApiNotes = useCallback(async () => {
    const token = await user.getIdToken();
    const res = await fetch(API_BASE + '/api/notes', {
      headers: { Authorization: 'Bearer ' + token },
    });
    if (!res.ok) return;
    const data: Note[] = await res.json();
    data.sort((a: any, b: any) => {
      const ta = new Date(a.createdAt || 0).getTime();
      const tb = new Date(b.createdAt || 0).getTime();
      return tb - ta;
    });
    setNotes(data);
  }, [user]);

  useEffect(() => {
    if (mode !== 'api') return;
    fetchApiNotes();
  }, [mode, fetchApiNotes]);

  function selectNote(note: Note) {
    setActive(note);
    setTitle(note.title);
    setBody(note.body ?? '');
  }

  function newNote() { setActive(null); setTitle(''); setBody(''); }

  // ── Save (create or update) ─────────────────────────────────────────────────
  async function save() {
    if (!title.trim()) return;
    setSaving(true);
    try {
      if (mode === 'sdk') {
        if (active) {
          await updateDoc(doc(db, 'notes', active.id), { title: title.trim(), body });
          setActive(prev => prev ? { ...prev, title: title.trim(), body } : null);
        } else {
          const ref = await addDoc(collection(db, 'notes'), {
            title: title.trim(), body, userId: user.uid, createdAt: serverTimestamp(),
          });
          setActive({ id: ref.id, title: title.trim(), body, userId: user.uid, createdAt: null });
        }
      } else {
        const token = await user.getIdToken();
        if (active) {
          await fetch(API_BASE + '/api/notes/' + active.id, {
            method: 'PUT',
            headers: { 'Content-Type': 'application/json', Authorization: 'Bearer ' + token },
            body: JSON.stringify({ title: title.trim(), body }),
          });
        } else {
          await fetch(API_BASE + '/api/notes', {
            method: 'POST',
            headers: { 'Content-Type': 'application/json', Authorization: 'Bearer ' + token },
            body: JSON.stringify({
              title: title.trim(), body,
              userId: user.uid,
              createdAt: new Date().toISOString(),
            }),
          });
        }
        await fetchApiNotes();
      }
    } finally {
      setSaving(false);
    }
  }

  // ── Delete ──────────────────────────────────────────────────────────────────
  async function remove(id: string) {
    if (mode === 'sdk') {
      await deleteDoc(doc(db, 'notes', id));
    } else {
      const token = await user.getIdToken();
      await fetch(API_BASE + '/api/notes/' + id, {
        method: 'DELETE',
        headers: { Authorization: 'Bearer ' + token },
      });
      setNotes(prev => prev.filter(n => n.id !== id));
    }
    if (active?.id === id) newNote();
  }

  const filtered = notes.filter(n =>
    n.title.toLowerCase().includes(search.toLowerCase()) ||
    (n.body ?? '').toLowerCase().includes(search.toLowerCase())
  );

  return (
    <div className="notes-shell">
      {/* Sidebar */}
      <aside className="sidebar">
        <div className="sidebar-top">
          <span className="brand">Notes</span>
          <button className="btn-icon" title="New note" onClick={newNote}>+</button>
        </div>
        <input
          className="search"
          placeholder="Search…"
          value={search}
          onChange={e => setSearch(e.target.value)}
        />
        <ul className="note-list">
          {filtered.map(n => (
            <li
              key={n.id}
              className={active?.id === n.id ? 'note-item active' : 'note-item'}
              onClick={() => selectNote(n)}
            >
              <span className="note-title">{n.title}</span>
              <button
                className="btn-delete"
                onClick={e => { e.stopPropagation(); remove(n.id); }}
                title="Delete"
              >×</button>
            </li>
          ))}
          {filtered.length === 0 && (
            <li className="empty">{search ? 'No matches' : 'No notes yet'}</li>
          )}
        </ul>
        <div className="sidebar-bottom">
          <span className="user-email">{user.email}</span>
          <button className="btn-signout" onClick={() => signOut(auth)}>Sign out</button>
        </div>
      </aside>

      {/* Editor */}
      <main className="editor">
        <div className="editor-header">
          <input
            className="title-input"
            placeholder="Note title…"
            value={title}
            onChange={e => setTitle(e.target.value)}
          />
          <button className="btn-save" onClick={save} disabled={saving || !title.trim()}>
            {saving ? 'Saving…' : active ? 'Save' : 'Create'}
          </button>
        </div>
        ${hasBody ? `<textarea
          className="body-input"
          placeholder="Start writing…"
          value={body}
          onChange={e => setBody(e.target.value)}
        />` : `<p className="no-body">Body field not defined in Note struct.</p>`}
        {/* Mode toggle */}
        <div className="mode-bar">
          <span className="mode-label">
            {mode === 'sdk' ? 'Firebase SDK (direct)' : 'FL Backend API (via server)'}
          </span>
          <button
            className={\`mode-toggle \${mode === 'api' ? 'active' : ''}\`}
            onClick={() => { newNote(); setMode(m => m === 'sdk' ? 'api' : 'sdk'); }}
            title="Toggle between Firebase SDK and FL backend"
          >
            {mode === 'sdk' ? 'Switch to FL Backend' : 'Switch to Firebase SDK'}
          </button>
        </div>
      </main>
    </div>
  );
}
`;
}

const firebasePackageJson = `{
  "name": "fl-notes-app",
  "private": true,
  "version": "0.0.0",
  "type": "module",
  "scripts": {
    "dev": "vite",
    "build": "tsc && vite build",
    "preview": "vite preview"
  },
  "dependencies": {
    "firebase": "^10.14.1",
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

const firebaseIndexHtml = `<!doctype html>
<html lang="en">
  <head>
    <meta charset="UTF-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1.0" />
    <title>Notes — FuturLang</title>
  </head>
  <body>
    <div id="root"></div>
    <script type="module" src="/src/main.tsx"></script>
  </body>
</html>
`;

const firebaseStylesCss = `/* ── Reset ─────────────────────────────────────────────────────────────── */
*, *::before, *::after { box-sizing: border-box; margin: 0; padding: 0; }
body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; background: #f5f5f5; color: #1a1a1a; }
button { cursor: pointer; font-family: inherit; }
input, textarea { font-family: inherit; }

/* ── Splash ─────────────────────────────────────────────────────────────── */
.splash { display: flex; align-items: center; justify-content: center; height: 100vh; }
.spinner { width: 32px; height: 32px; border: 3px solid #ddd; border-top-color: #333; border-radius: 50%; animation: spin .7s linear infinite; }
@keyframes spin { to { transform: rotate(360deg); } }

/* ── Auth ─────────────────────────────────────────────────────────────── */
.auth-shell { display: flex; align-items: center; justify-content: center; min-height: 100vh; padding: 1rem; background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); }
.auth-card { background: white; border-radius: 12px; padding: 2rem; width: min(400px, 100%); box-shadow: 0 20px 60px rgba(0,0,0,.2); }
.auth-card h1 { font-size: 2rem; font-weight: 700; margin-bottom: .25rem; }
.auth-sub { color: #888; font-size: .9rem; margin-bottom: 1.5rem; }
.tab-row { display: flex; border-bottom: 2px solid #eee; margin-bottom: 1.5rem; }
.tab { background: none; border: none; padding: .5rem 1rem; font-size: .95rem; color: #888; border-bottom: 2px solid transparent; margin-bottom: -2px; transition: all .15s; }
.tab.active { color: #333; border-bottom-color: #333; font-weight: 600; }
.auth-form { display: flex; flex-direction: column; gap: .75rem; }
.auth-form label { display: flex; flex-direction: column; gap: .3rem; font-size: .85rem; font-weight: 500; color: #444; }
.auth-form input { border: 1.5px solid #ddd; border-radius: 8px; padding: .6rem .75rem; font-size: .95rem; transition: border-color .15s; }
.auth-form input:focus { outline: none; border-color: #667eea; }
.error { color: #c0392b; font-size: .85rem; padding: .5rem; background: #fde8e8; border-radius: 6px; }
.btn-primary { background: #333; color: white; border: none; border-radius: 8px; padding: .75rem; font-size: 1rem; font-weight: 600; transition: background .15s; }
.btn-primary:hover:not(:disabled) { background: #555; }
.btn-primary:disabled { opacity: .6; }
.divider { text-align: center; position: relative; margin: 1rem 0; color: #bbb; font-size: .85rem; }
.divider::before, .divider::after { content: ''; position: absolute; top: 50%; width: 43%; height: 1px; background: #eee; }
.divider::before { left: 0; } .divider::after { right: 0; }
.btn-google { display: flex; align-items: center; justify-content: center; gap: .6rem; width: 100%; background: white; border: 1.5px solid #ddd; border-radius: 8px; padding: .7rem; font-size: .95rem; font-weight: 500; transition: background .15s; }
.btn-google:hover:not(:disabled) { background: #f8f8f8; }

/* ── Notes shell ──────────────────────────────────────────────────────── */
.notes-shell { display: grid; grid-template-columns: 260px 1fr; height: 100vh; }

/* ── Sidebar ──────────────────────────────────────────────────────────── */
.sidebar { display: flex; flex-direction: column; background: #1e1e1e; color: white; border-right: 1px solid #2a2a2a; }
.sidebar-top { display: flex; align-items: center; justify-content: space-between; padding: 1rem; border-bottom: 1px solid #2a2a2a; }
.brand { font-size: 1.1rem; font-weight: 700; letter-spacing: -.01em; }
.btn-icon { background: #333; color: white; border: none; width: 28px; height: 28px; border-radius: 6px; font-size: 1.2rem; line-height: 1; display: flex; align-items: center; justify-content: center; transition: background .15s; }
.btn-icon:hover { background: #444; }
.search { background: #2a2a2a; border: none; color: white; padding: .6rem 1rem; font-size: .9rem; outline: none; }
.search::placeholder { color: #666; }
.note-list { flex: 1; overflow-y: auto; list-style: none; }
.note-item { display: flex; align-items: center; justify-content: space-between; padding: .75rem 1rem; cursor: pointer; border-bottom: 1px solid #2a2a2a; transition: background .1s; }
.note-item:hover { background: #2a2a2a; }
.note-item.active { background: #333; }
.note-title { font-size: .9rem; flex: 1; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.btn-delete { background: none; border: none; color: #666; font-size: 1.1rem; padding: 0 .25rem; transition: color .15s; flex-shrink: 0; }
.btn-delete:hover { color: #e74c3c; }
.empty { color: #555; font-size: .85rem; padding: 1rem; text-align: center; }
.sidebar-bottom { padding: .75rem 1rem; border-top: 1px solid #2a2a2a; display: flex; flex-direction: column; gap: .5rem; }
.user-email { font-size: .75rem; color: #666; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.btn-signout { background: none; border: 1px solid #333; color: #888; border-radius: 6px; padding: .4rem; font-size: .8rem; transition: all .15s; }
.btn-signout:hover { border-color: #555; color: #ccc; }

/* ── Editor ──────────────────────────────────────────────────────────── */
.editor { display: flex; flex-direction: column; background: white; }
.editor-header { display: flex; gap: .75rem; align-items: center; padding: 1rem 1.5rem; border-bottom: 1px solid #eee; }
.title-input { flex: 1; border: none; font-size: 1.25rem; font-weight: 600; outline: none; color: #1a1a1a; }
.title-input::placeholder { color: #ccc; }
.btn-save { background: #1a1a1a; color: white; border: none; border-radius: 8px; padding: .5rem 1.25rem; font-size: .9rem; font-weight: 600; transition: background .15s; }
.btn-save:hover:not(:disabled) { background: #333; }
.btn-save:disabled { opacity: .4; }
.body-input { flex: 1; border: none; padding: 1.5rem; font-size: 1rem; line-height: 1.7; resize: none; outline: none; color: #333; }
.body-input::placeholder { color: #ccc; }
.no-body { color: #999; padding: 2rem; font-style: italic; }

/* ── Mode toggle bar ────────────────────────────────────────────────────── */
.mode-bar { display: flex; align-items: center; justify-content: space-between; padding: .6rem 1.5rem; border-top: 1px solid #eee; background: #fafafa; flex-shrink: 0; }
.mode-label { font-size: .8rem; color: #888; font-family: "SFMono-Regular", Consolas, monospace; }
.mode-toggle { background: #eee; border: none; border-radius: 6px; padding: .35rem .9rem; font-size: .8rem; font-weight: 600; color: #555; transition: all .15s; }
.mode-toggle:hover { background: #ddd; }
.mode-toggle.active { background: #1a1a1a; color: white; }

@media (max-width: 600px) {
  .notes-shell { grid-template-columns: 1fr; }
  .sidebar { height: 40vh; }
  .editor { height: 60vh; }
}
`;

function serializeNodes(nodes: ASTNode[]) {
  return nodes.map(serializeNode);
}

function serializeNode(node: ASTNode): unknown {
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
    case 'TypeDecl':
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        variants: node.variants,
      };
    case 'FnDecl':
      return {
        type: node.type,
        name: node.name,
        connective: node.connective,
        params: node.params,
        returnType: node.returnType,
        body: node.body.map(serializeNode),
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
    case 'Match':
      return {
        type: node.type,
        connective: node.connective,
        scrutinee: serializeExpr(node.scrutinee),
        cases: node.cases.map(matchCase => ({
          pattern: matchCase.pattern,
          body: matchCase.body.map(serializeNode),
        })),
      };
    default:
      return node;
  }
}

function serializeExpr(expr: ExprNode): unknown {
  switch (expr.type) {
    case 'Atom':
      return serializeAtom(expr);
    case 'SetBuilder':
      return {
        type: expr.type,
        element: expr.element,
        variable: expr.variable,
        domain: expr.domain,
      };
    case 'IndexedUnion':
      return {
        type: expr.type,
        builder: serializeExpr(expr.builder),
      };
    case 'Quantified':
      return {
        type: expr.type,
        quantifier: expr.quantifier,
        binderStyle: expr.binderStyle,
        variable: expr.variable,
        domain: expr.domain,
        body: expr.body ? serializeExpr(expr.body) : null,
      };
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
    case 'If':
      return {
        type: expr.type,
        condition: serializeExpr(expr.condition),
        thenBranch: serializeExpr(expr.thenBranch),
        elseBranch: serializeExpr(expr.elseBranch),
      };
    case 'LetExpr':
      return {
        type: expr.type,
        name: expr.name,
        value: serializeExpr(expr.value),
        body: serializeExpr(expr.body),
      };
    case 'Lambda':
      return {
        type: expr.type,
        params: expr.params,
        body: serializeExpr(expr.body),
      };
    default:
      return expr;
  }
}

function serializeAtom(atom: AtomNode) {
  const trimmed = atom.condition.trim();
  const unsupported =
    atom.atomKind === 'opaque' ||
    (atom.atomKind !== 'string' && (MATH_CHARS.test(trimmed) || MATH_NOTATION.test(trimmed)));

  return {
    type: atom.type,
    condition: atom.condition,
    atomKind: atom.atomKind,
    unsupported,
    reason: unsupported
      ? 'This claim is outside the strict executable subset. Use fl check for categorical proof checking.'
      : null,
  };
}

function renderReactApp(program: unknown): string {
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
        detail: \`fn \${node.name}\`,
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
    "moduleResolution": "Bundler",
    "resolveJsonModule": true,
    "isolatedModules": true,
    "noEmit": true,
    "jsx": "react-jsx",
    "types": ["vite/client"]
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
