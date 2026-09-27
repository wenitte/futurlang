// assembly.js — FuturLang-ized assembly: AddStoreCorrect
//
// Per the FuturLang connective rules:
//   ↔  pairs a theorem/lemma with its proof (required)
//   ∧  the following block does NOT apply() the current one
//   →  the following block calls apply(CurrentName)
//   ∨  disjunctive — either block suffices
//
// AddStoreCorrect's proof is applied by architecture.js's
// DatapathExecutesAddStore proof, so the connective after this
// proof block is →, not ∧.

export const FL_SOURCE = `theorem AddStoreCorrect() {
  assume(R1 == MEM[0] \u2227 R2 == MEM[1]) \u2192
  declareToProve(MEM[2] == MEM[0] + MEM[1])
} \u2194

proof AddStoreCorrect() {
  load(R1, MEM[0]) \u2192
  load(R2, MEM[1]) \u2192
  prove(R3 == R1 + R2) \u2192
  store(MEM[2], R3) \u2192
  conclude(MEM[2] == MEM[0] + MEM[1])
} \u2192   // \u2192 because DatapathExecutesAddStore applies AddStoreCorrect`;

// Chain of proof-body steps, in source order, each mapped to a
// runtime action against machine state.
export const steps = [
  {
    code: 'load(R1, MEM[0])',
    conn: '\u2192',
    run: (mem, regs) => { regs.R1 = mem[0]; },
    note: 'load \u2014 MEM[0] transported into R1',
  },
  {
    code: 'load(R2, MEM[1])',
    conn: '\u2192',
    run: (mem, regs) => { regs.R2 = mem[1]; },
    note: 'load \u2014 MEM[1] transported into R2',
  },
  {
    code: 'prove(R3 == R1 + R2)',
    conn: '\u2192',
    run: (mem, regs) => { regs.R3 = regs.R1 + regs.R2; },
    note: 'prove \u2014 R3 derived as R1 + R2, added to the fact pool',
  },
  {
    code: 'store(MEM[2], R3)',
    conn: '\u2192',
    run: (mem, regs) => { mem[2] = regs.R3; },
    note: 'store \u2014 R3 transported back into MEM[2]',
  },
  {
    code: 'conclude(MEM[2] == MEM[0] + MEM[1])',
    conn: null,
    run: () => {},
    note: 'conclude \u2014 goal matches declareToProve: PROVED',
  },
];

// Minimal machine state + stepper. architecture.js drives this and
// renders each transition onto the datapath schematic.
export function createMachine() {
  const mem = [12, 30, null];
  const regs = { R1: null, R2: null, R3: null };
  let cursor = -1;

  return {
    get mem() { return mem; },
    get regs() { return regs; },
    get cursor() { return cursor; },
    get done() { return cursor >= steps.length - 1; },
    step() {
      if (this.done) return null;
      cursor++;
      const s = steps[cursor];
      s.run(mem, regs);
      return { index: cursor, step: s };
    },
    reset() {
      cursor = -1;
      mem[2] = null;
      regs.R1 = regs.R2 = regs.R3 = null;
    },
  };
}
