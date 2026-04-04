"use strict";
// src/lean/setup.ts
//
// Manages the FuturLang-local Lean 4 + Mathlib installation.
// Everything lives in ~/.futurlang/ — fully isolated from any system Lean.
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
exports.VERIFY_FILE = exports.PROJECT = exports.ELAN_HOME = exports.FL_HOME = void 0;
exports.isSetupComplete = isSetupComplete;
exports.setup = setup;
exports.leanBinary = leanBinary;
exports.lakeBinary = lakeBinary;
const fs = __importStar(require("fs"));
const path = __importStar(require("path"));
const os = __importStar(require("os"));
const child_process_1 = require("child_process");
exports.FL_HOME = path.join(os.homedir(), '.futurlang');
exports.ELAN_HOME = path.join(exports.FL_HOME, 'elan');
exports.PROJECT = path.join(exports.FL_HOME, 'project');
exports.VERIFY_FILE = path.join(exports.PROJECT, 'FLVerify.lean');
// Lean toolchain version — pinned for reproducibility
const LEAN_TOOLCHAIN = 'leanprover/lean4:v4.14.0';
// ── Public API ────────────────────────────────────────────────────────────────
function isSetupComplete() {
    const lakeFile = path.join(exports.PROJECT, 'lakefile.toml');
    const toolchain = path.join(exports.PROJECT, 'lean-toolchain');
    const elanBin = elanBinary();
    return fs.existsSync(elanBin) && fs.existsSync(lakeFile) && fs.existsSync(toolchain);
}
async function setup(log) {
    log('Setting up FuturLang verification backend...');
    fs.mkdirSync(exports.FL_HOME, { recursive: true });
    // Step 1: Install elan
    await installElan(log);
    // Step 2: Create the Lake project with Mathlib
    await createProject(log);
    // Step 3: Download Mathlib cache (precompiled .olean files)
    await downloadMathlibCache(log);
    log('\n✓ Setup complete. FuturLang can now verify proofs against Mathlib.');
}
// ── Elan installation ─────────────────────────────────────────────────────────
function elanBinary() {
    const platform = process.platform;
    const bin = platform === 'win32' ? 'elan.exe' : 'elan';
    return path.join(exports.ELAN_HOME, 'bin', bin);
}
function leanBinary() {
    // After elan install, lean is at ~/.futurlang/elan/bin/lean
    return path.join(exports.ELAN_HOME, 'bin', 'lean');
}
function lakeBinary() {
    return path.join(exports.ELAN_HOME, 'bin', 'lake');
}
async function installElan(log) {
    if (fs.existsSync(elanBinary())) {
        log('  ✓ elan already installed');
        return;
    }
    log('  Installing elan (Lean version manager)...');
    const platform = process.platform;
    const env = {
        ...process.env,
        ELAN_HOME: exports.ELAN_HOME,
        ELAN_HOME_TMP: path.join(exports.FL_HOME, 'elan-tmp'),
    };
    if (platform === 'win32') {
        // Windows: download elan-init.ps1
        const script = path.join(exports.FL_HOME, 'elan-init.ps1');
        (0, child_process_1.execSync)(`powershell -Command "Invoke-WebRequest -Uri https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 -OutFile '${script}'"`, { env });
        (0, child_process_1.execSync)(`powershell -ExecutionPolicy Bypass -File "${script}" --no-modify-path --default-toolchain none -y`, { env, stdio: 'pipe' });
    }
    else {
        // Unix: curl | sh
        (0, child_process_1.execSync)(`curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | ` +
            `ELAN_HOME='${exports.ELAN_HOME}' sh -s -- --no-modify-path --default-toolchain none -y`, { env, stdio: 'pipe', shell: '/bin/sh' });
    }
    log('  ✓ elan installed');
}
// ── Lake project creation ─────────────────────────────────────────────────────
async function createProject(log) {
    const lakeFile = path.join(exports.PROJECT, 'lakefile.toml');
    if (fs.existsSync(lakeFile)) {
        log('  ✓ Lean project already exists');
        return;
    }
    log('  Creating Lean 4 project with Mathlib...');
    fs.mkdirSync(exports.PROJECT, { recursive: true });
    // Write lean-toolchain
    fs.writeFileSync(path.join(exports.PROJECT, 'lean-toolchain'), LEAN_TOOLCHAIN + '\n');
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
    fs.writeFileSync(exports.VERIFY_FILE, '-- FuturLang verification workspace\nimport Mathlib\n');
    // Run lake update to fetch manifest
    log('  Fetching Mathlib package manifest...');
    const env = { ...process.env, ELAN_HOME: exports.ELAN_HOME, PATH: `${exports.ELAN_HOME}/bin:${process.env.PATH}` };
    const result = (0, child_process_1.spawnSync)(lakeBinary(), ['update'], {
        cwd: exports.PROJECT, env, encoding: 'utf8',
    });
    if (result.status !== 0) {
        throw new Error(`lake update failed:\n${result.stderr}`);
    }
    log('  ✓ Project created');
}
// ── Mathlib cache download ────────────────────────────────────────────────────
async function downloadMathlibCache(log) {
    log('  Downloading Mathlib precompiled cache (~4GB, one-time)...');
    log('  This may take 10-30 minutes depending on your connection.');
    const env = { ...process.env, ELAN_HOME: exports.ELAN_HOME, PATH: `${exports.ELAN_HOME}/bin:${process.env.PATH}` };
    const result = (0, child_process_1.spawnSync)(lakeBinary(), ['exe', 'cache', 'get'], {
        cwd: exports.PROJECT, env, encoding: 'utf8',
        stdio: ['inherit', 'pipe', 'pipe'],
        maxBuffer: 100 * 1024 * 1024,
    });
    if (result.status !== 0) {
        throw new Error(`Mathlib cache download failed:\n${result.stderr}`);
    }
    log('  ✓ Mathlib cache downloaded');
}
