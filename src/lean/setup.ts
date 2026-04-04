// src/lean/setup.ts
//
// Manages the FuturLang-local Lean 4 + Mathlib installation.
// Everything lives in ~/.futurlang/ — fully isolated from any system Lean.

import * as fs from 'fs';
import * as path from 'path';
import * as os from 'os';
import { execSync, spawnSync } from 'child_process';

export const FL_HOME    = path.join(os.homedir(), '.futurlang');
export const ELAN_HOME  = path.join(FL_HOME, 'elan');
export const PROJECT    = path.join(FL_HOME, 'project');
export const VERIFY_FILE = path.join(PROJECT, 'FLVerify.lean');

// Lean toolchain version — pinned for reproducibility
const LEAN_TOOLCHAIN = 'leanprover/lean4:v4.14.0';

// ── Public API ────────────────────────────────────────────────────────────────

export function isSetupComplete(): boolean {
  const lakeFile = path.join(PROJECT, 'lakefile.toml');
  const toolchain = path.join(PROJECT, 'lean-toolchain');
  const elanBin = elanBinary();
  return fs.existsSync(elanBin) && fs.existsSync(lakeFile) && fs.existsSync(toolchain);
}

export async function setup(log: (msg: string) => void): Promise<void> {
  log('Setting up FuturLang verification backend...');
  fs.mkdirSync(FL_HOME, { recursive: true });

  // Step 1: Install elan
  await installElan(log);

  // Step 2: Create the Lake project with Mathlib
  await createProject(log);

  // Step 3: Download Mathlib cache (precompiled .olean files)
  await downloadMathlibCache(log);

  log('\n✓ Setup complete. FuturLang can now verify proofs against Mathlib.');
}

// ── Elan installation ─────────────────────────────────────────────────────────

function elanBinary(): string {
  const platform = process.platform;
  const bin = platform === 'win32' ? 'elan.exe' : 'elan';
  return path.join(ELAN_HOME, 'bin', bin);
}

export function leanBinary(): string {
  // After elan install, lean is at ~/.futurlang/elan/bin/lean
  return path.join(ELAN_HOME, 'bin', 'lean');
}

export function lakeBinary(): string {
  return path.join(ELAN_HOME, 'bin', 'lake');
}

async function installElan(log: (msg: string) => void): Promise<void> {
  if (fs.existsSync(elanBinary())) {
    log('  ✓ elan already installed');
    return;
  }

  log('  Installing elan (Lean version manager)...');

  const platform = process.platform;
  const env = {
    ...process.env,
    ELAN_HOME,
    ELAN_HOME_TMP: path.join(FL_HOME, 'elan-tmp'),
  };

  if (platform === 'win32') {
    // Windows: download elan-init.ps1
    const script = path.join(FL_HOME, 'elan-init.ps1');
    execSync(
      `powershell -Command "Invoke-WebRequest -Uri https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 -OutFile '${script}'"`,
      { env }
    );
    execSync(
      `powershell -ExecutionPolicy Bypass -File "${script}" --no-modify-path --default-toolchain none -y`,
      { env, stdio: 'pipe' }
    );
  } else {
    // Unix: curl | sh
    execSync(
      `curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | ` +
      `ELAN_HOME='${ELAN_HOME}' sh -s -- --no-modify-path --default-toolchain none -y`,
      { env, stdio: 'pipe', shell: '/bin/sh' }
    );
  }

  log('  ✓ elan installed');
}

// ── Lake project creation ─────────────────────────────────────────────────────

async function createProject(log: (msg: string) => void): Promise<void> {
  const lakeFile = path.join(PROJECT, 'lakefile.toml');
  if (fs.existsSync(lakeFile)) {
    log('  ✓ Lean project already exists');
    return;
  }

  log('  Creating Lean 4 project with Mathlib...');
  fs.mkdirSync(PROJECT, { recursive: true });

  // Write lean-toolchain
  fs.writeFileSync(path.join(PROJECT, 'lean-toolchain'), LEAN_TOOLCHAIN + '\n');

  // Write lakefile.toml
  const lakefile = `
[package]
name = "FLVerify"
version = "0.1.0"
defaultTargets = ["FLVerify"]

[[require]]
name = "mathlib"
from = "https://github.com/leanprover-community/mathlib4"
rev = "v4.14.0"

[[lean_lib]]
name = "FLVerify"
`.trim();
  fs.writeFileSync(lakeFile, lakefile + '\n');

  // Write an empty source file
  fs.writeFileSync(VERIFY_FILE, '-- FuturLang verification workspace\nimport Mathlib\n');

  // Run lake update to fetch manifest
  log('  Fetching Mathlib package manifest...');
  const env = { ...process.env, ELAN_HOME, PATH: `${ELAN_HOME}/bin:${process.env.PATH}` };
  const result = spawnSync(lakeBinary(), ['update'], {
    cwd: PROJECT, env, encoding: 'utf8',
  });
  if (result.status !== 0) {
    throw new Error(`lake update failed:\n${result.stderr}`);
  }

  log('  ✓ Project created');
}

// ── Mathlib cache download ────────────────────────────────────────────────────

async function downloadMathlibCache(log: (msg: string) => void): Promise<void> {
  log('  Downloading Mathlib precompiled cache (~4GB, one-time)...');
  log('  This may take 10-30 minutes depending on your connection.');

  const env = { ...process.env, ELAN_HOME, PATH: `${ELAN_HOME}/bin:${process.env.PATH}` };
  const result = spawnSync(lakeBinary(), ['exe', 'cache', 'get'], {
    cwd: PROJECT, env, encoding: 'utf8',
    stdio: ['inherit', 'pipe', 'pipe'],
    maxBuffer: 100 * 1024 * 1024,
  });

  if (result.status !== 0) {
    throw new Error(`Mathlib cache download failed:\n${result.stderr}`);
  }

  log('  ✓ Mathlib cache downloaded');
}
