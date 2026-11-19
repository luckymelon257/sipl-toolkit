import type { Expr, Program } from '../ast.js';
import { evalAssertion } from '../assertion.js';
import { State } from '../values.js';
import { ApproxRow, ApproxTable, describeApproximations } from './approx.js';

const MAX_STATES = 10_000;

/** Test states from a grid such as `X=0..9,Y=1..5` (ranges inclusive; a single value is allowed). */
export function gridStates(spec: string): State[] {
  const axes = spec.split(',').map((part) => {
    const m = /^\s*([A-Za-z][A-Za-z0-9_]*)\s*=\s*(-?\d+)(?:\s*\.\.\s*(-?\d+))?\s*$/.exec(part);
    if (!m) throw new Error(`bad grid '${part.trim()}', expected NAME=FROM..TO or NAME=VALUE`);
    const from = Number(m[2]);
    const to = m[3] === undefined ? from : Number(m[3]);
    if (to < from) throw new Error(`empty range ${m[1]}=${from}..${to}`);
    return { name: m[1], from, to };
  });
  const total = axes.reduce((n, a) => n * (a.to - a.from + 1), 1);
  if (total > MAX_STATES) throw new Error(`grid has ${total} states; too many (limit ${MAX_STATES})`);
  let states: State[] = [{}];
  for (const a of axes) {
    const next: State[] = [];
    for (const st of states) for (let v = a.from; v <= a.to; v++) next.push({ ...st, [a.name]: v });
    states = next;
  }
  return states;
}

export interface Mismatch {
  state: State;
  /** First approximation index at which the value is defined. */
  k: number;
  actual: number;
  expected: number;
}

export interface ReportRow extends ApproxRow {
  /** Value of the expected function, or null when it is not given or not defined on this state. */
  expected: number | null;
}

export interface ApproxReport {
  table: ApproxTable;
  rows: ReportRow[];
  expect?: string;
  checks: {
    /** fi ⊑ f(i+1) on every test state: once defined, the value never changes or disappears. */
    monotone: boolean;
    mismatches: Mismatch[];
    /** f_k is defined on every test state. */
    allDefined: boolean;
    /** Smallest i such that fi is defined on as many test states as f_k. */
    stabilizedAt: number;
  };
}

export interface ApproxTestOptions {
  k: number;
  states: State[];
  /** The function the approximations should converge to, e.g. `X div Y`. */
  expect?: Expr;
  /** Keeps only the states on which this assertion is true (e.g. `X ≥ 0 ∧ Y > 0`). */
  where?: Expr;
  /** Source text of `expect`, for display. */
  expectText?: string;
}

/** Evaluates f0..fk on the test states and checks the chain against the theory and the expected function. */
export function testApproximations(program: Program, name: string, opts: ApproxTestOptions): ApproxReport {
  const states = opts.where ? opts.states.filter((st) => evalAssertion(opts.where!, st) === true) : opts.states;
  const table = describeApproximations(program, name, opts.k, states);
  const rows: ReportRow[] = table.rows.map((row) => {
    const v = opts.expect ? evalAssertion(opts.expect, row.state) : undefined;
    return { ...row, expected: typeof v === 'number' ? v : null };
  });
  const mismatches: Mismatch[] = [];
  for (const row of rows) {
    if (row.firstDefined === null || row.expected === null) continue;
    const actual = row.values[row.firstDefined]!;
    if (actual !== row.expected) mismatches.push({ state: row.state, k: row.firstDefined, actual, expected: row.expected });
  }
  const last = table.definedCount[opts.k];
  return {
    table,
    rows,
    expect: opts.expect ? (opts.expectText ?? 'values') : undefined,
    checks: {
      monotone: checkMonotone(table.rows),
      mismatches,
      allDefined: last === rows.length,
      stabilizedAt: table.definedCount.findIndex((c) => c === last),
    },
  };
}

/** True when every row is defined from its first defined index on, always with the same value. */
export function checkMonotone(rows: ApproxRow[]): boolean {
  return rows.every((row) => {
    const first = row.values.findIndex((v) => v !== null);
    return first < 0 || row.values.slice(first).every((v) => v === row.values[first]);
  });
}
