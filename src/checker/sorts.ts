// src/checker/sorts.ts
// Sort system for the FuturLang kernel: two base sorts, Set and Element.

export type Sort = 'Set' | 'Element';

export interface SortError {
  kind: 'sort_error';
  message: string;
}

// Infer the sort of a simple identifier.
//   bare lowercase (x, y, z, ...)  → Element
//   bare uppercase (A, B, C, ...)  → Set
//   multi-word or complex term     → null (unknown)
export function inferIdentifierSort(term: string): Sort | null {
  const t = term.trim();
  if (/^[a-z][a-z0-9_]*$/.test(t)) return 'Element';
  if (/^[A-Z][A-Za-z0-9_]*$/.test(t)) return 'Set';
  return null;
}

// Check sort of a membership claim:  left ∈ right
//   left  must be Element (not Set)
//   right must be Set     (not Element)
export function sortCheckMembership(left: string, right: string): SortError | null {
  const leftSort  = inferIdentifierSort(left);
  const rightSort = inferIdentifierSort(right);
  if (leftSort === 'Set') {
    return {
      kind: 'sort_error',
      message: `Sort error: left side of ∈ must be an Element, but '${left}' looks like a Set`,
    };
  }
  if (rightSort === 'Element') {
    return {
      kind: 'sort_error',
      message: `Sort error: right side of ∈ must be a Set, but '${right}' looks like an Element`,
    };
  }
  return null;
}

// Check sort of a subset claim:  left ⊆ right
//   both must be Set (not Element)
export function sortCheckSubset(left: string, right: string): SortError | null {
  const leftSort  = inferIdentifierSort(left);
  const rightSort = inferIdentifierSort(right);
  if (leftSort === 'Element') {
    return {
      kind: 'sort_error',
      message: `Sort error: left side of ⊆ must be a Set, but '${left}' looks like an Element`,
    };
  }
  if (rightSort === 'Element') {
    return {
      kind: 'sort_error',
      message: `Sort error: right side of ⊆ must be a Set, but '${right}' looks like an Element`,
    };
  }
  return null;
}

// Check sort of a binary set operation:  left ∪ right  or  left ∩ right
//   both operands must be Set (not Element)
export function sortCheckBinarySet(left: string, right: string, op: '∪' | '∩'): SortError | null {
  const leftSort  = inferIdentifierSort(left);
  const rightSort = inferIdentifierSort(right);
  if (leftSort === 'Element') {
    return {
      kind: 'sort_error',
      message: `Sort error: left operand of ${op} must be a Set, but '${left}' looks like an Element`,
    };
  }
  if (rightSort === 'Element') {
    return {
      kind: 'sort_error',
      message: `Sort error: right operand of ${op} must be a Set, but '${right}' looks like an Element`,
    };
  }
  return null;
}

// Top-level sort checker for a proposition string.
// Returns the first sort error found, or null if the proposition is sort-correct.
// Only checks propositions whose top-level structure is a set-theoretic operator.
export function sortCheckProposition(prop: string): SortError | null {
  const s = prop.trim();

  // Membership:  x ∈ A
  const membershipMatch = s.match(/^(.+?)\s*∈\s*(.+)$/);
  if (membershipMatch) {
    const left  = membershipMatch[1].trim();
    const right = membershipMatch[2].trim();
    // Strip trailing complexity from the right side (e.g. "A ∪ B")
    const rightId = right.split(/\s/)[0].replace(/[^A-Za-z0-9_]$/, '').trim();
    return sortCheckMembership(left, rightId || right);
  }

  // Subset:  A ⊆ B  or  A ⊂ B
  const subsetMatch = s.match(/^(.+?)\s*[⊆⊂]\s*(.+)$/);
  if (subsetMatch) {
    const left  = subsetMatch[1].trim();
    const right = subsetMatch[2].trim();
    return sortCheckSubset(left, right);
  }

  // Union:  A ∪ B
  const unionMatch = s.match(/^(.+?)\s*∪\s*(.+)$/);
  if (unionMatch) {
    return sortCheckBinarySet(unionMatch[1].trim(), unionMatch[2].trim(), '∪');
  }

  // Intersection:  A ∩ B
  const intersectionMatch = s.match(/^(.+?)\s*∩\s*(.+)$/);
  if (intersectionMatch) {
    return sortCheckBinarySet(intersectionMatch[1].trim(), intersectionMatch[2].trim(), '∩');
  }

  return null;
}

// Extract set-theoretic variable names and their inferred sorts from a proposition.
// Used for scope checking: all variables in a set-theoretic conclusion must be in scope.
export function extractSetTheoreticVars(prop: string): Map<string, Sort> {
  const result = new Map<string, Sort>();
  // Match all simple identifiers in the proposition
  const tokens = prop.match(/[A-Za-z][A-Za-z0-9_]*/g) ?? [];
  for (const tok of tokens) {
    const sort = inferIdentifierSort(tok);
    if (sort !== null) result.set(tok, sort);
  }
  return result;
}
