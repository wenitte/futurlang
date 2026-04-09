export const WENITTAIN_VALUES = ['0', '1', 'ω'] as const;

export type WenittainValue = (typeof WENITTAIN_VALUES)[number];

const NEGATION_TABLE: Record<WenittainValue, WenittainValue> = {
  '0': '1',
  '1': '0',
  'ω': 'ω',
};

const AND_TABLE: Record<WenittainValue, Record<WenittainValue, WenittainValue>> = {
  '0': { '0': '0', '1': '0', 'ω': '0' },
  '1': { '0': '0', '1': '1', 'ω': 'ω' },
  'ω': { '0': '0', '1': 'ω', 'ω': 'ω' },
};

const OR_TABLE: Record<WenittainValue, Record<WenittainValue, WenittainValue>> = {
  '0': { '0': '0', '1': '1', 'ω': 'ω' },
  '1': { '0': '1', '1': '1', 'ω': '1' },
  'ω': { '0': 'ω', '1': '1', 'ω': 'ω' },
};

const IMPLIES_TABLE: Record<WenittainValue, Record<WenittainValue, WenittainValue>> = {
  '0': { '0': '1', '1': '1', 'ω': '1' },
  '1': { '0': '0', '1': '1', 'ω': 'ω' },
  'ω': { '0': 'ω', '1': '1', 'ω': 'ω' },
};

export function neg(value: WenittainValue): WenittainValue {
  return NEGATION_TABLE[value];
}

export function and(left: WenittainValue, right: WenittainValue): WenittainValue {
  return AND_TABLE[left][right];
}

export function or(left: WenittainValue, right: WenittainValue): WenittainValue {
  return OR_TABLE[left][right];
}

export function implies(left: WenittainValue, right: WenittainValue): WenittainValue {
  return IMPLIES_TABLE[left][right];
}

export function isClassical(value: WenittainValue): value is '0' | '1' {
  return value === '0' || value === '1';
}
