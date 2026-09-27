// All praise to the National Security Agency 
// architecture.js — computer architecture schematic: DatapathExecutesAddStore
//
// This proof block's body is exactly `apply(AddStoreCorrect)`, so per the
// FuturLang rule the connective FROM AddStoreCorrect's proof TO this
// theorem is \u2192 (see assembly.js). Within this file, theorem and proof
// are paired with the required \u2194.

import { FL_SOURCE as ASSEMBLY_SOURCE, steps, createMachine } from './assembly.js';

export const FL_SOURCE = `theorem DatapathExecutesAddStore() {
  assume(pc == 0) \u2192
  declareToProve(MEM[2] == MEM[0] + MEM[1])
} \u2194

proof DatapathExecutesAddStore() {
  apply(AddStoreCorrect)
}`;

// Which schematic wires + blocks light up for each assembly step.
// Ids refer to elements expected in the host page's SVG (see below).
const DATAPATH_MAP = [
  { wires: ['w-mem-r1'], hot: ['b-mem', 'b-r1'] },                       // load R1
  { wires: ['w-mem-r2'], hot: ['b-mem', 'b-r2'] },                       // load R2
  { wires: ['w-r1-alu', 'w-r2-alu', 'w-alu-r3'], hot: ['b-r1', 'b-r2', 'b-alu', 'b-r3'] }, // add
  { wires: ['w-r3-mem'], hot: ['b-r3', 'b-mem'] },                       // store
  { wires: [], hot: ['b-r3'] },                                          // conclude
];

// Expected host-page element ids (create these in whatever HTML loads
// this module as <script type="module" src="architecture.js">):
//   #chainSrc, #statusDot, #statusLabel, #stepBtn, #resetBtn, #log,
//   #v-mem0, #v-mem1, #v-r1, #v-r2, #v-r3, #v-pc, #v-ir,
//   svg paths/rects with the ids referenced in DATAPATH_MAP above.

export function mount(root = document) {
  const machine = createMachine();

  const chainSrc = root.getElementById('chainSrc');
  const statusDot = root.getElementById('statusDot');
  const statusLabel = root.getElementById('statusLabel');
  const stepBtn = root.getElementById('stepBtn');
  const resetBtn = root.getElementById('resetBtn');
  const log = root.getElementById('log');

  function renderSource() {
    if (!chainSrc) return;
    const i = machine.cursor;
    chainSrc.innerHTML = steps.map((s, idx) => {
      let cls = 'step';
      if (idx < i) cls += ' done';
      if (idx === i) cls += ' active';
      const connSpan = s.conn ? ` <span class="conn">${s.conn}</span>` : '';
      return `<span class="${cls}" id="ln-${idx}">${s.code}</span>${connSpan}`;
    }).join('\n');
  }

  function clearWires() {
    root.querySelectorAll('.wire').forEach(w => w.classList.remove('hot'));
    root.querySelectorAll('.block').forEach(b => b.classList.remove('hot'));
  }

  function updateValues() {
    const { mem, regs, cursor } = machine;
    const set = (id, val) => { const el = root.getElementById(id); if (el) el.textContent = val; };
    set('v-mem0', '[0] ' + (mem[0] ?? '\u2014'));
    set('v-mem1', '[1] ' + (mem[1] ?? '\u2014'));
    set('v-r1', regs.R1 ?? '\u2014');
    set('v-r2', regs.R2 ?? '\u2014');
    set('v-r3', regs.R3 ?? '\u2014');
    set('v-pc', Math.max(cursor, 0));
    set('v-ir', cursor >= 0 ? steps[cursor].code : '\u2014');
  }

  function addLog(text, isFinal) {
    if (!log) return;
    const line = document.createElement('div');
    if (isFinal) line.className = 'new';
    line.textContent = '> ' + text;
    log.appendChild(line);
    log.scrollTop = log.scrollHeight;
  }

  function step() {
    const result = machine.step();
    if (!result) return;
    clearWires();
    const { index, step: s } = result;
    const map = DATAPATH_MAP[index];
    map.wires.forEach(id => root.getElementById(id)?.classList.add('hot'));
    map.hot.forEach(id => root.getElementById(id)?.classList.add('hot'));
    updateValues();
    renderSource();
    addLog(s.note, machine.done);

    if (machine.done) {
      if (statusDot) statusDot.className = 'dot proved';
      if (statusLabel) statusLabel.textContent = 'PROVED';
      if (stepBtn) stepBtn.disabled = true;
    } else {
      if (statusDot) statusDot.className = 'dot pending';
      if (statusLabel) statusLabel.textContent = 'PENDING';
    }
  }

  function reset() {
    machine.reset();
    clearWires();
    updateValues();
    renderSource();
    if (log) log.innerHTML = '';
    if (statusDot) statusDot.className = 'dot';
    if (statusLabel) statusLabel.textContent = 'PENDING';
    if (stepBtn) stepBtn.disabled = false;
  }

  stepBtn?.addEventListener('click', step);
  resetBtn?.addEventListener('click', reset);
  reset();

  return { step, reset, machine };
}

// Auto-mount when loaded directly in a browser with the expected DOM.
if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', () => mount(document));
}
