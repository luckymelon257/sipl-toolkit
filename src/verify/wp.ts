import type { Expr, Program, Stm, While } from '../ast.js';
import { freeVars, walk } from '../ast.js';
import { printExpr } from '../assertion.js';
import type { Diagnostic } from '../span.js';

export type VCKind = 'entry' | 'preserve' | 'exit' | 'variant-bound' | 'variant-decrease';

/** A verification condition `hypothesis → goal`, valid for all values of its free variables. */
export interface VC {
  id: number;
  kind: VCKind;
  title: string;
  hypothesis: Expr;
  goal: Expr;
  /** The loop the condition belongs to (absent for the entry condition). */
  loop?: While;
  /** How the goal was obtained: the weakest-precondition steps. */
  derivation: string[];
}

// ---- building expressions ----

type DistOmit<T, K extends PropertyKey> = T extends unknown ? Omit<T, K> : never;

function mk(fields: DistOmit<Expr, 'id' | 'span'>, like: Expr): Expr {
  return { ...fields, id: -1, span: like.span } as Expr;
}
const and = (a: Expr, b: Expr): Expr => mk({ kind: 'logic', op: 'and', left: a, right: b }, a);
const implies = (a: Expr, b: Expr): Expr => mk({ kind: 'logic', op: 'implies', left: a, right: b }, a);
const not = (a: Expr): Expr => mk({ kind: 'not', operand: a }, a);
const compare = (op: '=' | '<' | '>=', a: Expr, b: Expr): Expr => mk({ kind: 'compare', op, left: a, right: b }, a);
const num = (value: number, like: Expr): Expr => mk({ kind: 'num', value }, like);
const variable = (name: string, like: Expr): Expr => mk({ kind: 'var', name }, like);
const TRUE: Expr = { kind: 'bool', value: true, id: -1, span: { start: { line: 1, column: 1, offset: 0 }, end: { line: 1, column: 1, offset: 0 } } };

/** Q[x ↦ a]: replaces every occurrence of variable x (there are no binders in the assertion language). */
export function substitute(q: Expr, x: string, a: Expr): Expr {
  const sub = (e: Expr) => substitute(e, x, a);
  switch (q.kind) {
    case 'var':
      return q.name === x ? a : q;
    case 'num':
    case 'bool':
      return q;
    case 'binary':
    case 'compare':
    case 'logic':
      return { ...q, left: sub(q.left), right: sub(q.right) } as Expr;
    case 'not':
      return { ...q, operand: sub(q.operand) };
    case 'cond':
      return { ...q, cond: sub(q.cond), then: sub(q.then), else: sub(q.else) };
    case 'call':
      return { ...q, args: q.args.map(sub) };
  }
}

// ---- weakest preconditions ----

function stmText(s: Stm): string {
  switch (s.kind) {
    case 'assign': return `${s.target} := ${printExpr(s.value)}`;
    case 'seq': return `${stmText(s.first)}; ${stmText(s.second)}`;
    case 'if': return `if ${printExpr(s.cond)} then … else …`;
    case 'while': return `while ${printExpr(s.cond)} do …`;
    case 'block': return `begin ${stmText(s.body)} end`;
    case 'skip': return 'skip';
  }
}

const at = (w: While) => `${w.span.start.line}:${w.span.start.column}`;

/** Thrown when the frame rule cannot carry a variant obligation through an inner loop. */
class FrameError extends Error {
  constructor(readonly inner: While) {
    super('inner loop changes the variant');
  }
}

/** Variables assigned anywhere in a statement. */
function assigned(s: Stm): Set<string> {
  return new Set([...walk(s)].flatMap((n) => (n.kind === 'assign' ? [n.target] : [])));
}

class VCGen {
  readonly vcs: VC[] = [];
  readonly warnings: Diagnostic[] = [];
  private readonly seen = new Set<string>();
  private readonly used: Set<string>;

  constructor(program: Program) {
    this.used = new Set<string>();
    for (const n of walk(program)) if (n.kind === 'var' || n.kind === 'assign') this.used.add(n.kind === 'var' ? n.name : n.target);
    for (const e of [program.pre, program.post]) if (e) freeVars(e).forEach((v) => this.used.add(v));
    for (const n of walk(program)) {
      if (n.kind === 'while') for (const e of [n.invariant, n.variant]) if (e) freeVars(e).forEach((v) => this.used.add(v));
    }
  }

  private fresh(base: string): string {
    for (let i = 0; ; i++) if (!this.used.has(`${base}${i}`)) return `${base}${i}`;
  }

  add(vc: Omit<VC, 'id'>): void {
    const key = `${printExpr(vc.hypothesis)} ⊢ ${printExpr(vc.goal)}`;
    if (this.seen.has(key)) return;
    this.seen.add(key);
    this.vcs.push({ ...vc, id: this.vcs.length + 1 });
  }

  /**
   * wp(s, q); loops contribute their side conditions to `vcs`; `log` collects the derivation.
   * In `frame` mode (used for variant obligations) an inner loop is passed only when it assigns no variable
   * of `q`: then `q` holds after it (frame rule) and no further conditions are generated.
   */
  wp(s: Stm, q: Expr, log: string[], frame = false): Expr {
    switch (s.kind) {
      case 'assign': {
        const r = substitute(q, s.target, s.value);
        log.push(`wp(${stmText(s)}, ${printExpr(q)}) = ${printExpr(r)}`);
        return r;
      }
      case 'seq':
        return this.wp(s.first, this.wp(s.second, q, log, frame), log, frame);
      case 'block':
        return this.wp(s.body, q, log, frame);
      case 'skip':
        log.push(`wp(skip, ${printExpr(q)}) = ${printExpr(q)}`);
        return q;
      case 'if': {
        const a = this.wp(s.then, q, log, frame);
        const b = this.wp(s.else, q, log, frame);
        const r = and(implies(s.cond, a), implies(not(s.cond), b));
        log.push(`wp(${stmText(s)}, ${printExpr(q)}) = ${printExpr(r)}`);
        return r;
      }
      case 'while': {
        if (!frame) return this.loop(s, q, log);
        const changed = assigned(s);
        const touched = freeVars(q).filter((v) => changed.has(v));
        if (touched.length > 0) throw new FrameError(s);
        log.push(`wp(${stmText(s)}, ${printExpr(q)}) = ${printExpr(q)}   [frame: the loop at ${at(s)} does not change ${freeVars(q).join(', ')}]`);
        return q;
      }
    }
  }

  private loop(w: While, q: Expr, log: string[]): Expr {
    const inv = w.invariant;
    if (!inv) throw new Error(`loop at ${at(w)} has no invariant`);
    const where = `loop at ${at(w)}`;

    const stepLog: string[] = [];
    this.add({
      kind: 'preserve', loop: w,
      title: `${where}: one iteration preserves the invariant (induction step)`,
      hypothesis: and(inv, w.cond), goal: this.wp(w.body, inv, stepLog), derivation: stepLog,
    });
    this.add({
      kind: 'exit', loop: w,
      title: `${where}: on exit the invariant and the negated condition give what follows the loop`,
      hypothesis: and(inv, not(w.cond)), goal: q, derivation: [],
    });
    if (w.variant) {
      const t = w.variant;
      this.add({
        kind: 'variant-bound', loop: w,
        title: `${where}: the variant ${printExpr(t)} is non-negative while the loop runs`,
        hypothesis: and(inv, w.cond), goal: compare('>=', t, num(0, t)), derivation: [],
      });
      const t0name = this.fresh('t');
      const decLog: string[] = [];
      try {
        const raw = this.wp(w.body, compare('<', t, variable(t0name, t)), decLog, true);
        const goal = substitute(raw, t0name, t);
        decLog.push(`${t0name} ↦ ${printExpr(t)} (the value of the variant before the iteration): ${printExpr(goal)}`);
        this.add({
          kind: 'variant-decrease', loop: w,
          title: `${where}: every iteration decreases the variant ${printExpr(t)} (termination)`,
          hypothesis: and(inv, w.cond), goal, derivation: decLog,
        });
      } catch (e) {
        if (!(e instanceof FrameError)) throw e;
        this.warnings.push({
          severity: 'warning', code: 'V003', span: w.span,
          message: `cannot check that the variant ${printExpr(t)} decreases: the inner loop at ${at(e.inner)} ` +
            'changes variables it depends on; termination of this loop is not checked',
        });
      }
    }
    log.push(`wp(${stmText(w)}, ${printExpr(q)}) = ${printExpr(inv)}   [invariant of the ${where}]`);
    return inv;
  }
}

/**
 * Verification conditions of an annotated program (Hoare logic with weakest preconditions):
 * entry `pre → wp(S, post)`; for each loop with invariant I, condition b and variant t:
 * `I ∧ b → wp(body, I)`, `I ∧ ¬b → Q`, and with a variant `I ∧ b → t ≥ 0`, `I ∧ b → wp(body, t < t0)[t0 ↦ t]`.
 * Throws when a loop has no invariant. Conditions that cannot be generated are reported in `warnings`.
 */
export function generateVCs(program: Program, warnings: Diagnostic[] = []): VC[] {
  const gen = new VCGen(program);
  const pre = program.pre ?? TRUE;
  const post = program.post ?? TRUE;
  const log: string[] = [];
  const goal = gen.wp(program.body, post, log);
  const hasLoops = [...walk(program.body)].some((n) => n.kind === 'while');
  const entry: VC = {
    id: 0, kind: 'entry', hypothesis: pre, goal, derivation: log,
    title: hasLoops
      ? 'the precondition establishes the weakest precondition of the program (induction base of the first loop)'
      : 'the precondition implies the weakest precondition of the program',
  };
  warnings.push(...gen.warnings);
  return [entry, ...gen.vcs].map((vc, i) => ({ ...vc, id: i + 1 }));
}
