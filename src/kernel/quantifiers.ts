import { and, or, neg, WenittainValue } from './values';

export interface QuantifierFrame {
  denotingValues: WenittainValue[];
  unresolvedCount: number;
}

export function evaluateForAll(frame: QuantifierFrame): WenittainValue {
  let result: WenittainValue = '1';
  for (const value of frame.denotingValues) {
    result = and(result, value);
  }
  return frame.unresolvedCount > 0 && result === '1' ? 'ω' : result;
}

export function evaluateExists(frame: QuantifierFrame): WenittainValue {
  let result: WenittainValue = '0';
  for (const value of frame.denotingValues) {
    result = or(result, value);
  }
  if (result === '1') return '1';
  return frame.unresolvedCount > 0 ? 'ω' : '0';
}

export function evaluateNotForAllNot(frame: QuantifierFrame): WenittainValue {
  let result: WenittainValue = '0';
  for (const value of frame.denotingValues) {
    result = or(result, value);
  }
  return result;
}
