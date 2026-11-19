import type { Expr, Program, While } from '../ast.js';
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
      /** States on which the hypothesis was true and the goal could be evaluated; 0 means the check was vacuous. */
      relevant: number;
    };

export interface RunViolation {
  kind: 'invariant' | 'variant' | 'post' | 'undefined';
  input: State;
  /** State at the violation (the loop head, or the final state). */
  state: State;
  loopId?: number;
  iteration?: number;
  message: string;
}

export interface RunsReport {
  /** Executions started from states of the box that satisfy pre. */
  count: number;
  /** exhaustive: every such state; sampled: the box was sampled; truncated: stopped at the run limit. */
  mode: 'exhaustive' | 'sampled' | 'truncated';
  violations: RunViolation[];
  /** Executions that could not be judged (neither a pass nor a violation): a loop exceeded the iteration budget or a value left the integer range. */
  inconclusive: number;
}

export interface VerifyReport {
  diagnostics: Diagnostic[];
  vcs: (VC & { result: VCResult })[];
  runs: RunsReport;
  /**
   * refuted: a real execution from a state satisfying pre violates an annotation;
   * unproven: some condition fails (annotations too weak or missing) though no run in bounds fails;
   * checked-in-bounds: every condition holds for every state of the box and every run passed;
   * inconclusive: nothing failed, but some condition never had a true hypothesis or no run could be judged;
   * checked-in-bounds: every condition holds for every state of the box and every run passed;
   * checked-in-sample: nothing failed, but some condition or the runs covered only a sample of the box.
   * Both "checked" verdicts are evidence, not a proof.
   */
  verdict: 'refuted' | 'unproven' | 'inconclusive' | 'checked-in-bounds' | 'checked-in-sample';
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

/** Value of an assertion, or 'overflow' when it is undefined because a value left the safe integer range. */
function judge(e: Expr, st: State): number | boolean | undefined | 'overflow' {
  const ctx = { overflow: false };
  const v = evalAssertion(e, st, ctx);
  return v === undefined && ctx.overflow ? 'overflow' : v;
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
    const g = judge(vc.goal, st);
    if (g === 'overflow') continue; // the goal cannot be evaluated here: neither a pass nor a counterexample
    relevant++;
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
  constructor(readonly outcome: RunViolation | 'inconclusive') {
    super(outcome === 'inconclusive' ? outcome : outcome.message);
  }
}

/**
 * Correctness assistant: generates the verification conditions of an annotated program, checks each one
 * on a bounded box of states (with counterexamples), and runs the program from every state of the box that
 * satisfies the precondition, checking invariants at each loop head and the postcondition at the end.
 */
export function verifyProgram(
  program: Program, opts: BoundsOptions & { maxRuns?: number; maxIterations?: number } = {},
): VerifyReport {
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
      diagnostics, vcs: [], runs: { count: 0, mode: 'exhaustive', violations: [], inconclusive: 0 },
      verdict: 'unproven', total: false, range,
      summary: 'nothing was checked: ' + diagnostics.map((d) => d.message).join('; '),
    };
  }

  const vcs = generateVCs(program, diagnostics).map((vc) => ({ ...vc, result: checkVC(vc, { ...opts, range }) }));
  const runs = runAll(program, loops, range, opts.maxCases ?? 250_000, opts.maxRuns ?? 5_000, opts.maxIterations ?? 10_000);
  const failed = vcs.filter((v) => v.result.status === 'refuted');
  const vacuous = vcs.filter((v) => v.result.status === 'checked' && v.result.relevant === 0).map((v) => v.id);
  const judged = runs.count - runs.inconclusive;
  const complete = runs.mode === 'exhaustive' && vcs.every((v) => v.result.status !== 'checked' || v.result.mode === 'exhaustive');
  const verdict = runs.violations.length > 0 ? 'refuted'
    : failed.length > 0 ? 'unproven'
    : vacuous.length > 0 || judged === 0 ? 'inconclusive'
    : complete ? 'checked-in-bounds' : 'checked-in-sample';
  const total = verdict.startsWith('checked') && loops.every((w) => w.variant) && !diagnostics.some((d) => d.code === 'V003');
  const notes: string[] = [];
  const sampled = vcs.filter((v) => v.result.status === 'checked' && v.result.mode === 'sampled').map((v) => v.id);
  if (sampled.length > 0) notes.push(`condition(s) ${sampled.join(', ')} were checked on a random sample of the box only (raise --max-cases to check every state).`);
  if (runs.mode === 'truncated') notes.push(`runs stopped at ${runs.count}; not every state satisfying the precondition was run.`);
  if (runs.mode === 'sampled') notes.push('runs started from a random sample of the box only.');
  if (runs.count === 0) notes.push('the program was never run: no examined state of the box satisfies the precondition; widen the range.');
  if (runs.inconclusive > 0) notes.push(`${runs.inconclusive} run(s) could not be judged: a loop did not finish within the iteration budget (raise --max-iterations) or a value left the integer range; they count neither as passed nor as failed.`);
  if (vacuous.length > 0) notes.push(`condition(s) ${vacuous.join(', ')} never had a true hypothesis in the box, so they were not really tested; widen the range.`);
  const summary = [summarize(verdict, total, failed, runs, range), ...notes.map((n) => `Note: ${n}`)].join(' ');
  return { diagnostics, vcs, runs, verdict, total, range, summary };
}

/** Runs the program from the states of the box that satisfy pre (at most `maxRuns` runs). */
function runAll(
  program: Program, loops: While[], range: [number, number], maxCases: number, maxRuns: number, maxIterations: number,
): RunsReport {
  const pre = program.pre;
  // Variables that occur only in annotations (ghosts) are universally quantified, so the runs range over them too.
  const programVars = new Set([...walk(program.body)].flatMap((n) => (n.kind === 'var' ? [n.name] : n.kind === 'assign' ? [n.target] : [])));
  const others = [program.post, ...loops.flatMap((w) => [w.invariant, w.variant])].filter((e): e is Expr => e !== undefined);
  const ghosts = boxVars(...others).filter((v) => !programVars.has(v));
  const vars = [...new Set([...programInputs(program), ...(pre ? freeVars(pre) : []), ...ghosts])].sort();
  const byId = new Map(loops.map((w) => [w.id, w]));
  const report: RunsReport = { count: 0, mode: 'exhaustive', violations: [], inconclusive: 0 };
  const it = box(vars, range, maxCases);
  for (let r = it.next(); ; r = it.next()) {
    if (r.done) return { ...report, mode: r.value };
    const input = r.value;
    if (pre && evalAssertion(pre, input) !== true) continue;
    if (report.count === maxRuns) return { ...report, mode: 'truncated' };
    report.count++;
    const outcome = runOne(program, input, byId, maxIterations);
    if (outcome === 'inconclusive') report.inconclusive++;
    else if (outcome) report.violations.push(outcome);
    if (report.violations.length >= 5) return { ...report, mode: 'truncated' };
  }
}

function runOne(program: Program, input: State, loops: Map<number, While>, maxIterations: number): RunViolation | 'inconclusive' | undefined {
  const lastVariant = new Map<number, number>();
  const stop = (v: RunViolation | 'inconclusive') => {
    throw new StopRun(v);
  };
  try {
    const run = runProgram(program, input, {
      maxIterations,
      onLoopHead: (loopId, iteration, state) => {
        const w = loops.get(loopId);
        if (!w) return;
        const at = { input, state, loopId, iteration };
        const inv = judge(w.invariant!, state);
        if (inv === 'overflow') stop('inconclusive');
        if (inv !== true) {
          stop({ kind: 'invariant', ...at, message: `invariant ${printExpr(w.invariant!)} does not hold before iteration ${iteration} in ${formatState(state)}` });
        }
        if (!w.variant) return;
        const t = judge(w.variant, state);
        if (t === 'overflow') stop('inconclusive');
        const name = printExpr(w.variant);
        if (iteration > 0 && typeof t === 'number' && t >= lastVariant.get(loopId)!) {
          stop({ kind: 'variant', ...at, message: `variant ${name} did not decrease in iteration ${iteration}: ${lastVariant.get(loopId)} before, ${t} after` });
        }
        if (evalAssertion(w.cond, state) === true && (typeof t !== 'number' || t < 0)) {
          stop({ kind: 'variant', ...at, message: `variant ${name} is ${t ?? 'undefined'} while the loop still runs, in ${formatState(state)}` });
        }
        if (typeof t === 'number') lastVariant.set(loopId, t);
      },
    });
    if (run.status === 'undefined') {
      if (run.undef!.reason === 'iteration-limit' || run.undef!.reason === 'overflow') return 'inconclusive';
      return { kind: 'undefined', input, state: input, message: run.undef!.message };
    }
    const post = program.post && judge(program.post, run.state!);
    if (post === 'overflow') return 'inconclusive';
    if (program.post && post !== true) {
      return {
        kind: 'post', input, state: run.state!,
        message: `postcondition ${printExpr(program.post)} does not hold in the final state ${formatState(run.state!)}`,
      };
    }
    return undefined;
  } catch (e) {
    if (e instanceof StopRun) return e.outcome;
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
  if (verdict === 'inconclusive') {
    return 'INCONCLUSIVE: nothing failed, but part of the check tested nothing (see the notes), so it says nothing about correctness.';
  }
  if (verdict === 'checked-in-sample') {
    return `No condition failed on the sampled states and none of ${runs.count - runs.inconclusive} finished executions violates the annotations: ` +
      `${total ? 'total' : 'partial'} correctness is supported by a sample of the box only (evidence, not a proof).`;
  }
  return `All conditions hold for ${box} and all ${runs.count - runs.inconclusive} finished executions satisfy the annotations: ` +
    `${total ? 'total' : 'partial'} correctness is supported by bounded checking (this is evidence, not a proof).`;
}
