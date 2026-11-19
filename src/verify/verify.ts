import type { Program, While } from '../ast.js';
import { freeVars, walk } from '../ast.js';
import { evalAssertion, printExpr } from '../assertion.js';
import { programInputs } from '../check.js';
import { evalState, runProgram } from '../semantics/evaluate.js';
import { semS } from '../semantics/term.js';
import { Diagnostic } from '../span.js';
import { State, formatState } from '../values.js';
import { VC, generateVCs } from './wp.js';

export interface BoundsOptions {
  /** Every free variable ranges over [lo, hi] (default [-3, 8]). */
  range?: [number, number];
  /** Maximum number of states examined per condition; larger boxes are sampled (default 250 000). */
  maxCases?: number;
}

export type VCResult =
  | {
      status: 'refuted';
      counterexample: State;
      /** The goal is false, or not defined (e.g. a negative exponent). */
      goalValue: 'false' | 'undefined';
      /** For an induction step: the state after one execution of the loop body. */
      afterBody?: State;
    }
  | {
      status: 'checked';
      mode: 'exhaustive' | 'sampled';
      cases: number;
      /** States on which the hypothesis was true; 0 means the check was vacuous. */
      relevant: number;
    };

export interface RunViolation {
  kind: 'invariant' | 'post' | 'non-termination' | 'undefined';
  input: State;
  /** State at the violation (the loop head, or the final state). */
  state: State;
  loopId?: number;
  iteration?: number;
  message: string;
}

export interface VerifyReport {
  diagnostics: Diagnostic[];
  vcs: (VC & { result: VCResult })[];
  runs: { count: number; mode: 'exhaustive' | 'sampled'; violations: RunViolation[] };
  /**
   * refuted: a real execution from a state satisfying pre violates an annotation;
   * unproven: some condition fails (annotations too weak or missing) though no run in bounds fails;
   * checked-in-bounds: every condition holds for all states in the box — evidence, not a proof.
   */
  verdict: 'refuted' | 'unproven' | 'checked-in-bounds';
  /** Every loop has a checked variant, so termination is covered as well (total correctness). */
  total: boolean;
  range: [number, number];
  summary: string;
}

/** Deterministic pseudo-random generator (mulberry32), so sampled checks are reproducible. */
function rng(seed: number): () => number {
  return () => {
    seed = (seed + 0x6d2b79f5) | 0;
    let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** States over `vars` with values in [lo, hi]: all of them, or `max` samples when the box is larger. */
function* box(vars: string[], [lo, hi]: [number, number], max: number): Generator<State, 'exhaustive' | 'sampled'> {
  const size = hi - lo + 1;
  if (Math.pow(size, vars.length) <= max) {
    const digits = vars.map(() => lo);
    for (;;) {
      yield Object.fromEntries(vars.map((v, i) => [v, digits[i]]));
      let i = vars.length - 1;
      while (i >= 0 && digits[i] === hi) digits[i--] = lo;
      if (i < 0) return 'exhaustive';
      digits[i]++;
    }
  }
  const next = rng(1);
  for (let n = 0; n < max; n++) yield Object.fromEntries(vars.map((v) => [v, lo + Math.floor(next() * size)]));
  return 'sampled';
}

function boxVars(...exprs: Parameters<typeof freeVars>[0][]): string[] {
  const vars: string[] = [];
  for (const e of exprs) freeVars(e, vars);
  return vars.sort();
}

/** Looks for a state in the box where the hypothesis holds and the goal does not. */
export function checkVC(vc: VC, opts: BoundsOptions = {}): VCResult {
  const range = opts.range ?? [-3, 8];
  const it = box(boxVars(vc.hypothesis, vc.goal), range, opts.maxCases ?? 250_000);
  let cases = 0;
  let relevant = 0;
  for (let r = it.next(); ; r = it.next()) {
    if (r.done) return { status: 'checked', mode: r.value, cases, relevant };
    const st = r.value;
    cases++;
    if (evalAssertion(vc.hypothesis, st) !== true) continue;
    relevant++;
    const g = evalAssertion(vc.goal, st);
    if (g === true) continue;
    const result: VCResult = { status: 'refuted', counterexample: st, goalValue: g === false ? 'false' : 'undefined' };
    if (vc.kind === 'preserve' && vc.loop) {
      const after = evalState(semS(vc.loop.body, new Map()), st, {}, { maxIterations: 10_000 });
      if (after.ok) result.afterBody = after.state;
    }
    return result;
  }
}

class StopRun extends Error {
  constructor(readonly violation: RunViolation) {
    super(violation.message);
  }
}

/**
 * Correctness assistant: generates the verification conditions of an annotated program, checks each one
 * on a bounded box of states (with counterexamples), and runs the program from every state of the box that
 * satisfies the precondition, checking invariants at each loop head and the postcondition at the end.
 */
export function verifyProgram(program: Program, opts: BoundsOptions & { maxRuns?: number } = {}): VerifyReport {
  const range = opts.range ?? [-3, 8];
  const loops = [...walk(program.body)].filter((n): n is While => n.kind === 'while');
  const diagnostics: Diagnostic[] = [];
  if (program.functions.length > 0 || [...walk(program.body)].some((n) => n.kind === 'call')) {
    diagnostics.push({
      severity: 'error', code: 'V002', span: program.span,
      message: 'the correctness assistant supports SIPL programs without function calls; use `sipl approx` for recursive functions',
    });
  }
  for (const w of loops) {
    if (!w.invariant) {
      diagnostics.push({
        severity: 'error', code: 'V001', span: w.span,
        message: 'this loop has no invariant; add a line `//@ invariant: <assertion>` before it',
      });
    }
  }
  if (diagnostics.length > 0) {
    return {
      diagnostics, vcs: [], runs: { count: 0, mode: 'exhaustive', violations: [] }, verdict: 'unproven', total: false, range,
      summary: 'nothing was checked: ' + diagnostics.map((d) => d.message).join('; '),
    };
  }

  const vcs = generateVCs(program).map((vc) => ({ ...vc, result: checkVC(vc, { ...opts, range }) }));
  const runs = runAll(program, loops, range, opts.maxRuns ?? 5_000);
  const failed = vcs.filter((v) => v.result.status === 'refuted');
  const verdict = runs.violations.length > 0 ? 'refuted' : failed.length > 0 ? 'unproven' : 'checked-in-bounds';
  const total = verdict === 'checked-in-bounds' && loops.every((w) => w.variant);
  return { diagnostics, vcs, runs, verdict, total, range, summary: summarize(verdict, total, failed, runs, range) };
}

function runAll(program: Program, loops: While[], range: [number, number], maxRuns: number): VerifyReport['runs'] {
  const pre = program.pre;
  const vars = [...new Set([...programInputs(program), ...(pre ? freeVars(pre) : [])])].sort();
  const invariants = new Map(loops.map((w) => [w.id, w.invariant!]));
  const violations: RunViolation[] = [];
  let count = 0;
  const it = box(vars, range, maxRuns);
  for (let r = it.next(); ; r = it.next()) {
    if (r.done) return { count, mode: r.value, violations };
    const input = r.value;
    if (pre && evalAssertion(pre, input) !== true) continue;
    count++;
    const violation = runOne(program, input, invariants, loops.every((w) => w.variant));
    if (violation) violations.push(violation);
    if (violations.length >= 5) return { count, mode: 'sampled', violations };
  }
}

function runOne(program: Program, input: State, invariants: Map<number, Program['pre'] & object>, totalClaimed: boolean): RunViolation | undefined {
  try {
    const run = runProgram(program, input, {
      maxIterations: 10_000,
      onLoopHead: (loopId, iteration, state) => {
        const inv = invariants.get(loopId);
        if (inv && evalAssertion(inv, state) !== true) {
          throw new StopRun({
            kind: 'invariant', input, state, loopId, iteration,
            message: `invariant ${printExpr(inv)} does not hold before iteration ${iteration} in ${formatState(state)}`,
          });
        }
      },
    });
    if (run.status === 'undefined') {
      if (run.undef!.reason === 'iteration-limit' && !totalClaimed) return undefined; // partial correctness only
      return {
        kind: run.undef!.reason === 'iteration-limit' ? 'non-termination' : 'undefined', input, state: input,
        message: run.undef!.message,
      };
    }
    if (program.post && evalAssertion(program.post, run.state!) !== true) {
      return {
        kind: 'post', input, state: run.state!,
        message: `postcondition ${printExpr(program.post)} does not hold in the final state ${formatState(run.state!)}`,
      };
    }
    return undefined;
  } catch (e) {
    if (e instanceof StopRun) return e.violation;
    throw e;
  }
}

function summarize(
  verdict: VerifyReport['verdict'], total: boolean, failed: VC[], runs: VerifyReport['runs'], [lo, hi]: [number, number],
): string {
  const box = `all variables in [${lo}, ${hi}]`;
  if (verdict === 'refuted') {
    return `REFUTED: a real execution violates an annotation (${runs.violations[0].message}).`;
  }
  if (verdict === 'unproven') {
    const steps = failed.filter((v) => v.kind === 'preserve');
    const hint = steps.length > 0
      ? ' The invariant is not inductive: it holds in every run tried but one iteration can break it from some state; strengthen it.'
      : '';
    return `UNPROVEN: ${failed.length} condition(s) fail with ${box}, yet no execution of ${runs.count} tried violates the annotations.${hint}`;
  }
  return `All conditions hold for ${box} and all ${runs.count} executions satisfy the annotations: ` +
    `${total ? 'total' : 'partial'} correctness is supported by bounded checking (this is evidence, not a proof).`;
}
