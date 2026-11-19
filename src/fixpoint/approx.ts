import type { Program } from '../ast.js';
import { EvalStep, Undefined, traceValue } from '../semantics/evaluate.js';
import { printTerm } from '../semantics/print.js';
import { Term, buildFunctional } from '../semantics/term.js';
import { State } from '../values.js';

const BOTTOM: Term = { t: 'BOTTOM' };

/**
 * Kleene approximations f0 = ⊥, f(i+1) = φ(fi) of function `name`, for i = 0..k.
 * All functions of the program are approximated simultaneously, so helpers called by `name`
 * are replaced by their own approximations of the same index. Terms are simplified by strictness
 * of superposition: S(…, ⊥, …) = ⊥, S^[…](⊥, …) = ⊥, IF(b, ⊥, ⊥) = ⊥.
 * The returned terms share subterms (fi occurs by reference inside f(i+1)), so their size in memory stays linear.
 */
export function approximationTerms(program: Program, name: string, k: number): Term[] {
  if (!program.functions.some((f) => f.name === name)) throw new Error(`no function ${name} in the program`);
  const phis = new Map(program.functions.map((f) => [f.name, buildFunctional(program, f.name)]));
  let current = new Map([...phis.keys()].map((n) => [n, BOTTOM]));
  const chain: Term[] = [BOTTOM];
  for (let i = 1; i <= k; i++) {
    const prev = current;
    current = new Map([...phis].map(([n, phi]) => [n, substitute(phi, prev)]));
    chain.push(current.get(name)!);
  }
  return chain;
}

/** φ[g ↦ approx(g)] with strictness simplification; substituted callees are already simplified and are not traversed. */
function substitute(t: Term, approx: Map<string, Term>): Term {
  const sub = (x: Term) => substitute(x, approx);
  switch (t.t) {
    case 'S': {
      const args = t.args.map(sub);
      return args.some(isBottom) ? BOTTOM : { ...t, args };
    }
    case 'CALL': {
      const callee = t.callee.t === 'FN' ? approx.get(t.callee.name) ?? t.callee : t.callee;
      const args = t.args.map(sub);
      return isBottom(callee) || args.some(isBottom) ? BOTTOM : { ...t, callee, args };
    }
    case 'IF': {
      const cond = sub(t.cond);
      const then = sub(t.then);
      const other = sub(t.else);
      return isBottom(cond) || (isBottom(then) && isBottom(other)) ? BOTTOM : { ...t, cond, then, else: other };
    }
    default:
      return t;
  }
}

function isBottom(t: Term): boolean {
  return t.t === 'BOTTOM';
}

/** Number of nodes of the term as a tree (shared subterms counted at every occurrence). */
export function treeSize(t: Term, memo = new WeakMap<Term, number>()): number {
  const known = memo.get(t);
  if (known !== undefined) return known;
  let size = 1;
  switch (t.t) {
    case 'S':
      for (const a of t.args) size += treeSize(a, memo);
      break;
    case 'CALL':
      size += treeSize(t.callee, memo);
      for (const a of t.args) size += treeSize(a, memo);
      break;
    case 'IF':
      size += treeSize(t.cond, memo) + treeSize(t.then, memo) + treeSize(t.else, memo);
      break;
  }
  memo.set(t, size);
  return size;
}

/** `fi` in course notation, or `φ(f(i-1))` when the expanded term would be longer than about `maxLength` characters. */
export function printApproximation(chain: Term[], i: number, name: string, maxLength = 2_000): string {
  const size = treeSize(chain[i]);
  // A node prints as at least ~4 characters; skip the expansion when it is certainly too long.
  if (size * 4 > maxLength) return `φ(${name}${i - 1}) (expanded term has ${size} nodes; not printed)`;
  const text = printTerm(chain[i]);
  return text.length > maxLength ? `φ(${name}${i - 1}) (expanded term has ${text.length} characters; not printed)` : text;
}

export type ApproxValue = ({ ok: true; value: number } | { ok: false; undef: Undefined }) & {
  steps: EvalStep[];
  truncated: boolean;
};

/** fk(st): applies the k-th approximation term to a state, recording the applied formulas. */
export function applyApproximation(program: Program, name: string, k: number, st: State, maxSteps = 5_000): ApproxValue {
  const chain = approximationTerms(program, name, k);
  return traceValue(chain[k], st, {}, { maxSteps });
}

export interface ApproxRow {
  state: State;
  /** values[i] = fi(state), or null when undefined. */
  values: (number | null)[];
  /** Smallest i with fi(state) defined, or null when none of f0..fk is defined. */
  firstDefined: number | null;
}

export interface ApproxTable {
  fn: string;
  k: number;
  /** Printed f0..fk (long ones abbreviated). */
  terms: string[];
  rows: ApproxRow[];
  /** definedCount[i] = number of states on which fi is defined. */
  definedCount: number[];
}

/** Evaluates f0..fk on every state: the domain of definedness of each approximation on the test states. */
export function describeApproximations(program: Program, name: string, k: number, states: State[]): ApproxTable {
  const chain = approximationTerms(program, name, k);
  const rows = states.map((state) => {
    const values = chain.map((t) => {
      const r = traceValue(t, state, {}, { record: false });
      return r.ok ? r.value : null;
    });
    const first = values.findIndex((v) => v !== null);
    return { state, values, firstDefined: first < 0 ? null : first };
  });
  return {
    fn: name,
    k,
    terms: chain.map((_, i) => printApproximation(chain, i, name)),
    rows,
    definedCount: chain.map((_, i) => rows.filter((r) => r.values[i] !== null).length),
  };
}
