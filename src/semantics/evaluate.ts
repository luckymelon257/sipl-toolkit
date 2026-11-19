import type { Program } from '../ast.js';
import { isStackOverflow } from '../span.js';
import { State, checkedInt, formatState } from '../values.js';
import { printTermLimited } from './print.js';
import { BaseFn, Term, buildFunctional, buildTerm } from './term.js';

/** Why a value is undefined (↑). */
export type UndefinedReason =
  | 'unbound-variable' // x⇒ is partial: st(x) does not exist
  | 'overflow' // the result is outside the safe integer range
  | 'iteration-limit' // WH did not finish within the iteration budget (probably does not terminate)
  | 'call-depth' // recursion did not finish within the call-depth budget
  | 'stack-limit' // the interpreter ran out of stack before the call-depth budget (the term is too deeply nested)
  | 'bottom' // ⊥ was applied: an approximation f_k is undefined here
  | 'unknown-function';

export interface Undefined {
  reason: UndefinedReason;
  message: string;
}

/** Interpretation of function symbols: f ↦ (formal parameters, φ-body). */
export type Env = Record<string, { params: string[]; body: Term }>;

export interface EvalOptions {
  /** Calls refer to the approximation f_level; `Infinity` (default) means the least fixed point. */
  level?: number;
  /** Total WH iterations allowed (default 100 000). */
  maxIterations?: number;
  /** Nested calls allowed (default 500). */
  maxCallDepth?: number;
  /** Record the applied formulas (default false). */
  record?: boolean;
  /** Maximum number of recorded steps (default 5 000). */
  maxSteps?: number;
  /** Called before each test of a loop condition: `loopId` is the AST id of the while, `iteration` counts from 0. */
  onLoopHead?: (loopId: number, iteration: number, state: State) => void;
}

export type Formula = 'AF_S' | 'AF_AS' | 'AF_SEQ' | 'AF_IF' | 'AF_WH' | 'AF_ID' | 'AF_CALL' | 'AF_BOT';

/** One application of a computation formula (Nikitchenko 2020, table 1.5). */
export interface EvalStep {
  formula: Formula;
  depth: number;
  term: string;
  detail: string;
}

export type ValueResult = { ok: true; value: number } | { ok: false; undef: Undefined };
export type StateResult = { ok: true; state: State } | { ok: false; undef: Undefined };

export interface RunResult {
  status: 'defined' | 'undefined';
  state?: State;
  undef?: Undefined;
  steps: EvalStep[];
  truncated: boolean;
}

class Undef extends Error {
  constructor(readonly undef: Undefined) {
    super(undef.message);
  }
}

const OPS: Record<BaseFn, (a: number, b: number) => number | boolean> = {
  add: (a, b) => a + b,
  sub: (a, b) => a - b,
  mult: (a, b) => a * b,
  eq: (a, b) => a === b,
  gr: (a, b) => a > b,
  less: (a, b) => a < b,
  or: (a, b) => Boolean(a) || Boolean(b),
  neg: (a) => !a,
};

class Evaluator {
  readonly steps: EvalStep[] = [];
  truncated = false;
  private iterations = 0;
  private depth = 0;
  private readonly maxIterations: number;
  private readonly maxCallDepth: number;
  private readonly maxSteps: number;

  constructor(
    private readonly env: Env,
    private readonly opts: EvalOptions,
  ) {
    this.maxIterations = opts.maxIterations ?? 100_000;
    this.maxCallDepth = opts.maxCallDepth ?? 500;
    this.maxSteps = opts.maxSteps ?? 5_000;
  }

  private log(formula: Formula, term: Term, detail: () => string): void {
    if (!this.opts.record) return;
    if (this.steps.length >= this.maxSteps) {
      this.truncated = true;
      return;
    }
    this.steps.push({ formula, depth: this.depth, term: printTermLimited(term, 300), detail: detail() });
  }

  /** Applies a state transformer term (FS). */
  state(t: Term, st: State, level: number): State {
    switch (t.t) {
      case 'AS': {
        const v = this.int(t.arg, st, level);
        const next = { ...st, [t.variable]: v };
        this.log('AF_AS', t, () => `${formatState(st)} ∇ [${t.variable} ↦ ${v}] = ${formatState(next)}`);
        return next;
      }
      case 'SEQ':
        this.log('AF_SEQ', t, () => `(fs1 · fs2)(${formatState(st)}) = fs2(fs1(${formatState(st)}))`);
        return this.state(t.right, this.state(t.left, st, level), level);
      case 'IF': {
        const c = this.bool(t.cond, st, level);
        this.log('AF_IF', t, () => `condition is ${c}, apply the ${c ? 'first' : 'second'} branch`);
        return this.state(c ? t.then : t.else, st, level);
      }
      case 'WH': {
        let cur = st;
        for (let k = 0; ; k++) {
          this.opts.onLoopHead?.(t.ref?.nodeId ?? -1, k, cur);
          const c = this.bool(t.cond, cur, level);
          const at = cur;
          this.log('AF_WH', t, () => `st${k} = ${formatState(at)}, ${printTermLimited(t.cond, 300)}(st${k}) = ${c}${c ? '' : `, result st${k}`}`);
          if (!c) return cur;
          if (++this.iterations > this.maxIterations) {
            throw new Undef({
              reason: 'iteration-limit',
              message: `loop did not finish within ${this.maxIterations} iterations (it may not terminate)`,
            });
          }
          cur = this.state(t.body, cur, level);
        }
      }
      case 'ID':
        this.log('AF_ID', t, () => `id(${formatState(st)}) = ${formatState(st)}`);
        return st;
      case 'PAREN':
        return this.state(t.inner, st, level);
      default:
        throw new Error(`${t.t} is not a state transformer`);
    }
  }

  value(t: Term, st: State, level: number): number | boolean {
    switch (t.t) {
      case 'CONST':
        return t.value;
      case 'DNM': {
        if (!Object.hasOwn(st, t.variable)) {
          throw new Undef({ reason: 'unbound-variable', message: `${t.variable}⇒ is undefined: ${t.variable} has no value in ${formatState(st)}` });
        }
        return st[t.variable];
      }
      case 'S': {
        const args = t.args.map((a) => this.value(a, st, level));
        let r = OPS[t.fn](args[0] as number, args[1] as number);
        if (typeof r === 'number') {
          const checked = checkedInt(r);
          if (checked === undefined) {
            throw new Undef({ reason: 'overflow', message: `${t.fn}(${args.join(', ')}) is outside the integer range` });
          }
          r = checked;
        }
        this.log('AF_S', t, () => `${t.fn}(${args.join(', ')}) = ${r}`);
        return r;
      }
      case 'IF': {
        const c = this.bool(t.cond, st, level);
        this.log('AF_IF', t, () => `condition is ${c}, take the ${c ? 'first' : 'second'} value`);
        return this.value(c ? t.then : t.else, st, level);
      }
      case 'CALL': {
        const args = t.args.map((a) => this.int(a, st, level));
        const bind = Object.fromEntries(t.params.map((p, i) => [p, args[i]]));
        this.log('AF_CALL', t, () => args.length === 0
          ? `${printTermLimited(t.callee, 300)}(${formatState(st)})`
          : `${printTermLimited(t.callee, 300)}(${formatState(st)} ∇ ${formatState(bind)})`);
        return this.apply(t.callee, { ...st, ...bind }, level);
      }
      case 'BOTTOM':
        this.log('AF_BOT', t, () => `⊥(${formatState(st)}) is undefined`);
        throw new Undef({ reason: 'bottom', message: `⊥ is undefined on ${formatState(st)}` });
      default:
        throw new Error(`${t.t} is not a value term`);
    }
  }

  /** Applies a function term: a symbol of the environment, ⊥, or an inlined approximation. */
  private apply(callee: Term, st: State, level: number): number | boolean {
    if (callee.t !== 'FN') return this.value(callee, st, level);
    if (level <= 0) {
      this.log('AF_BOT', callee, () => `${callee.name}0 = ⊥ is undefined on ${formatState(st)}`);
      throw new Undef({ reason: 'bottom', message: `${callee.name} is undefined at approximation level 0 (${callee.name}0 = ⊥)` });
    }
    const def = this.env[callee.name];
    if (!def) throw new Undef({ reason: 'unknown-function', message: `unknown function ${callee.name}` });
    if (this.depth >= this.maxCallDepth) {
      throw new Undef({
        reason: 'call-depth',
        message: `recursion deeper than ${this.maxCallDepth} calls: either it does not terminate or it needs a larger depth budget`,
      });
    }
    this.depth++;
    try {
      return this.value(def.body, st, level - 1);
    } finally {
      this.depth--;
    }
  }

  int(t: Term, st: State, level: number): number {
    return this.value(t, st, level) as number;
  }

  bool(t: Term, st: State, level: number): boolean {
    return this.value(t, st, level) as boolean;
  }
}

function attempt<T>(f: () => T): { ok: true; result: T } | { ok: false; undef: Undefined } {
  try {
    return { ok: true, result: f() };
  } catch (e) {
    if (e instanceof Undef) return { ok: false, undef: e.undef };
    if (isStackOverflow(e)) {
      return {
        ok: false,
        undef: {
          reason: 'stack-limit',
          message: 'the interpreter ran out of stack: the computation is nested too deeply for this implementation (this says nothing about termination)',
        },
      };
    }
    throw e;
  }
}

/** The environment of a SIPL-R program: every function symbol with its φ-body. */
export function envOf(program: Program): Env {
  return Object.fromEntries(program.functions.map((f) => [f.name, { params: f.params, body: buildFunctional(program, f.name) }]));
}

/** Applies a state-transformer term to a state. */
export function evalState(term: Term, st: State, env: Env, opts: EvalOptions = {}): StateResult {
  const ev = new Evaluator(env, opts);
  const r = attempt(() => ev.state(term, st, opts.level ?? Infinity));
  return r.ok ? { ok: true, state: r.result } : r;
}

/** Applies an arithmetic term (e.g. a functional φ or an approximation f_k) to a state. */
export function evalValue(term: Term, st: State, env: Env, opts: EvalOptions = {}): ValueResult {
  const ev = new Evaluator(env, opts);
  const r = attempt(() => ev.int(term, st, opts.level ?? Infinity));
  return r.ok ? { ok: true, value: r.result } : r;
}

/** Same as `evalValue`, also returning the recorded steps. */
export function traceValue(term: Term, st: State, env: Env, opts: EvalOptions = {}): ValueResult & { steps: EvalStep[]; truncated: boolean } {
  const ev = new Evaluator(env, { record: true, ...opts });
  const r = attempt(() => ev.int(term, st, opts.level ?? Infinity));
  return { ...(r.ok ? { ok: true as const, value: r.result } : r), steps: ev.steps, truncated: ev.truncated };
}

/** Runs a program: applies sem_P(program) to `st` in the environment of its functions. */
export function runProgram(program: Program, st: State, opts: EvalOptions = {}): RunResult {
  const ev = new Evaluator(envOf(program), opts);
  const r = attempt(() => ev.state(buildTerm(program), st, opts.level ?? Infinity));
  return r.ok
    ? { status: 'defined', state: r.result, steps: ev.steps, truncated: ev.truncated }
    : { status: 'undefined', undef: r.undef, steps: ev.steps, truncated: ev.truncated };
}
