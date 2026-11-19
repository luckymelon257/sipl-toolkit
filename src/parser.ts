import type { CompareOp, Expr, FuncDecl, Node, Program, Stm, While } from './ast.js';
import { walk } from './ast.js';
import { Annotation, LexMode, Token, TokenKind, tokenize } from './lexer.js';
import { Position, SiplError, SourceSpan } from './span.js';

/** Distributes `Omit` over the members of a union. */
type DistOmit<T, K extends PropertyKey> = T extends unknown ? Omit<T, K> : never;

const COMPARE_OPS: Partial<Record<TokenKind, CompareOp>> = {
  '=': '=', '>': '>', '<': '<', '>=': '>=', '<=': '<=', '!=': '!=',
};

/** Functions of the assertion language and their arity. */
const ASSERTION_FUNCTIONS: Record<string, number> = { gcd: 2, abs: 1 };

function describe(tok: Token): string {
  return tok.kind === 'eof' ? 'end of input' : `'${tok.text}'`;
}

class Parser {
  private pos = 0;
  /** Set when a SIPL-R construct is parsed. */
  extended = false;
  /** Outcome of `atom` at each token position: without it, nested '(' backtracking takes exponential time. */
  private readonly atoms = new Map<number, { expr: Expr; end: number; extended: boolean } | { error: unknown }>();

  constructor(
    private readonly tokens: Token[],
    private readonly mode: LexMode,
  ) {}

  private peek(k = 0): Token {
    return this.tokens[Math.min(this.pos + k, this.tokens.length - 1)];
  }

  private at(kind: TokenKind): boolean {
    return this.peek().kind === kind;
  }

  private next(): Token {
    const tok = this.peek();
    if (tok.kind !== 'eof') this.pos++;
    return tok;
  }

  private get prevEnd(): Position {
    return this.tokens[Math.max(this.pos - 1, 0)].span.end;
  }

  private error(expected: string, tok = this.peek()): SiplError {
    return new SiplError('E100', `expected ${expected}, found ${describe(tok)}`, tok.span);
  }

  private expect(kind: TokenKind, what = `'${kind}'`): Token {
    if (!this.at(kind)) throw this.error(what);
    return this.next();
  }

  private node<T extends DistOmit<Node, 'id' | 'span'>>(start: Position, fields: T): T & { id: number; span: SourceSpan } {
    return { ...fields, id: -1, span: { start, end: this.prevEnd } };
  }

  // ---- programs and statements ----

  program(): Program {
    const start = this.peek().span.start;
    const functions: FuncDecl[] = [];
    if (this.at('program')) {
      this.next();
      this.extended = true;
      if (!this.at('begin')) {
        functions.push(this.decl());
        while (this.at(';')) {
          if (this.peek(1).kind === 'begin') {
            throw new SiplError(
              'E100',
              "unexpected ';' before 'begin': declarations are separated by ';', the last one is followed directly by 'begin'",
              this.peek().span,
            );
          }
          this.next();
          functions.push(this.decl());
        }
      }
    }
    this.expect('begin');
    const body = this.stms();
    this.expect('end');
    this.expect('eof', 'end of input');
    return this.node(start, { kind: 'program', functions, body, extended: this.extended, annotations: [] }) as Program;
  }

  private decl(): FuncDecl {
    const start = this.expect('func', "'func' declaration").span.start;
    const name = this.expect('ident', 'function name');
    const params: string[] = [];
    const paramSpans: SourceSpan[] = [];
    if (this.at('(')) {
      this.next();
      do {
        const p = this.expect('ident', 'parameter name');
        params.push(p.text);
        paramSpans.push(p.span);
      } while (this.at(',') && this.next());
      this.expect(')', "',' or ')'");
    }
    this.expect('=', "'='");
    const body = this.aexp();
    return this.node(start, { kind: 'func', name: name.text, nameSpan: name.span, params, paramSpans, body }) as FuncDecl;
  }

  private stms(): Stm {
    let s = this.stm();
    while (this.at(';')) {
      this.next();
      if (this.at('end')) {
        throw new SiplError(
          'E100',
          "unexpected 'end' after ';': SIPL has no empty statement, so ';' separates statements and may not precede 'end'",
          this.peek().span,
        );
      }
      const second = this.stm();
      s = { kind: 'seq', first: s, second, id: -1, span: { start: s.span.start, end: second.span.end } };
    }
    return s;
  }

  private stm(): Stm {
    const tok = this.peek();
    const start = tok.span.start;
    switch (tok.kind) {
      case 'ident': {
        this.next();
        this.expect(':=', "':='");
        const value = this.aexp();
        return this.node(start, { kind: 'assign', target: tok.text, targetSpan: tok.span, value }) as Stm;
      }
      case 'if': {
        this.next();
        const cond = this.bexp();
        this.expect('then');
        const then = this.stm();
        this.expect('else');
        return this.node(start, { kind: 'if', cond, then, else: this.stm() }) as Stm;
      }
      case 'while': {
        this.next();
        const cond = this.bexp();
        this.expect('do');
        return this.node(start, { kind: 'while', cond, body: this.stm() }) as Stm;
      }
      case 'begin': {
        this.next();
        const body = this.stms();
        this.expect('end', "';' or 'end'");
        return this.node(start, { kind: 'block', body }) as Stm;
      }
      case 'skip':
        this.next();
        return this.node(start, { kind: 'skip' }) as Stm;
      default:
        throw this.error('a statement');
    }
  }

  // ---- arithmetic expressions ----

  aexp(): Expr {
    const start = this.peek().span.start;
    let left = this.term();
    while (this.at('+') || this.at('-')) {
      const op = this.next().kind as '+' | '-';
      left = this.node(start, { kind: 'binary', op, left, right: this.term() }) as Expr;
    }
    return left;
  }

  private term(): Expr {
    const start = this.peek().span.start;
    let left = this.power();
    while (this.at('*') || this.at('div') || this.at('mod')) {
      const op = this.next().kind as '*' | 'div' | 'mod';
      left = this.node(start, { kind: 'binary', op, left, right: this.power() }) as Expr;
    }
    return left;
  }

  private power(): Expr {
    const start = this.peek().span.start;
    const base = this.primary();
    if (!this.at('^')) return base;
    this.next();
    return this.node(start, { kind: 'binary', op: '^', left: base, right: this.power() }) as Expr;
  }

  private primary(): Expr {
    const tok = this.peek();
    const start = tok.span.start;
    switch (tok.kind) {
      case 'number':
        this.next();
        return this.node(start, { kind: 'num', value: this.literal(tok.text, tok) }) as Expr;
      case '-': {
        this.next();
        const num = this.peek();
        if (num.kind !== 'number') throw this.error("a number after '-' (there is no unary minus; write 0 - x)");
        this.next();
        return this.node(start, { kind: 'num', value: -this.literal(num.text, num) }) as Expr;
      }
      case 'ident': {
        this.next();
        if (!this.at('(')) return this.node(start, { kind: 'var', name: tok.text }) as Expr;
        this.next();
        const args: Expr[] = [this.aexp()];
        while (this.at(',')) {
          this.next();
          args.push(this.aexp());
        }
        this.expect(')', "',' or ')'");
        if (this.mode === 'program') this.extended = true;
        else if (ASSERTION_FUNCTIONS[tok.text] !== args.length) {
          throw new SiplError(
            'E006',
            ASSERTION_FUNCTIONS[tok.text] === undefined
              ? `unknown function ${tok.text} in an assertion; available: gcd(a, b), abs(a)`
              : `${tok.text} expects ${ASSERTION_FUNCTIONS[tok.text]} argument(s), got ${args.length}`,
            { start, end: this.prevEnd },
          );
        }
        return this.node(start, { kind: 'call', name: tok.text, args }) as Expr;
      }
      case '(': {
        this.next();
        const inner = this.aexp();
        this.expect(')', "')'");
        return inner;
      }
      case 'if': {
        this.next();
        this.extended ||= this.mode === 'program';
        const cond = this.bexp();
        this.expect('then');
        const then = this.aexp();
        this.expect('else');
        return this.node(start, { kind: 'cond', cond, then, else: this.aexp() }) as Expr;
      }
      default:
        throw this.error('an expression');
    }
  }

  private literal(text: string, tok: Token): number {
    const value = Number(text);
    if (!Number.isSafeInteger(value)) throw new SiplError('E101', `integer literal ${text} is out of range`, tok.span);
    return value;
  }

  // ---- conditions ----

  bexp(): Expr {
    const start = this.peek().span.start;
    const left = this.disjunction();
    if (!this.at('implies')) return left;
    this.next();
    return this.node(start, { kind: 'logic', op: 'implies', left, right: this.bexp() }) as Expr;
  }

  private disjunction(): Expr {
    const start = this.peek().span.start;
    let left = this.conjunction();
    while (this.at('or')) {
      this.next();
      left = this.node(start, { kind: 'logic', op: 'or', left, right: this.conjunction() }) as Expr;
    }
    return left;
  }

  private conjunction(): Expr {
    const start = this.peek().span.start;
    let left = this.negation();
    while (this.at('and')) {
      this.next();
      left = this.node(start, { kind: 'logic', op: 'and', left, right: this.negation() }) as Expr;
    }
    return left;
  }

  private negation(): Expr {
    const start = this.peek().span.start;
    if (!this.at('not')) return this.atom();
    this.next();
    return this.node(start, { kind: 'not', operand: this.negation() }) as Expr;
  }

  private atom(): Expr {
    const from = this.pos;
    const outer = this.extended;
    let memo = this.atoms.get(from);
    if (!memo) {
      this.extended = false;
      try {
        memo = { expr: this.parseAtom(), end: this.pos, extended: this.extended };
      } catch (error) {
        memo = { error };
      }
      this.atoms.set(from, memo);
    }
    this.extended = outer;
    if ('error' in memo) throw memo.error;
    this.pos = memo.end;
    this.extended ||= memo.extended;
    return memo.expr;
  }

  private parseAtom(): Expr {
    const tok = this.peek();
    if (this.mode === 'assertion' && tok.kind === 'ident' && (tok.text === 'true' || tok.text === 'false')) {
      this.next();
      return this.node(tok.span.start, { kind: 'bool', value: tok.text === 'true' }) as Expr;
    }
    if (!this.at('(')) return this.comparison();
    // '(' opens either an arithmetic operand of a comparison or a parenthesised condition.
    const saved = { pos: this.pos, extended: this.extended };
    try {
      return this.comparison();
    } catch (asComparison) {
      Object.assign(this, saved);
      try {
        this.next();
        const inner = this.bexp();
        this.expect(')', "')'");
        return inner;
      } catch (asCondition) {
        throw farther(asComparison, asCondition);
      }
    }
  }

  private comparison(): Expr {
    const start = this.peek().span.start;
    const left = this.aexp();
    const op = COMPARE_OPS[this.peek().kind];
    if (!op) throw this.error(this.mode === 'program' ? "a comparison '=', '>' or '<'" : 'a comparison operator');
    this.next();
    if (op === '<' && this.mode === 'program') this.extended = true;
    return this.node(start, { kind: 'compare', op, left, right: this.aexp() }) as Expr;
  }

  finish(): void {
    this.expect('eof', 'end of input');
  }
}

function farther(a: unknown, b: unknown): unknown {
  if (a instanceof SiplError && b instanceof SiplError) {
    return b.diagnostic.span.start.offset > a.diagnostic.span.start.offset ? b : a;
  }
  return b;
}

function shiftPosition(p: Position, base: Position): Position {
  return {
    line: base.line + p.line - 1,
    column: p.line === 1 ? base.column + p.column - 1 : p.column,
    offset: base.offset + p.offset,
  };
}

/**
 * Parses an annotation: a condition (`kind = 'bool'`) or, for loop variants, an integer expression.
 * `base` places positions inside the enclosing source.
 */
export function parseAssertion(text: string, base?: Position, kind: 'bool' | 'int' = 'bool'): Expr {
  const shiftSpan = (s: SourceSpan): SourceSpan =>
    base ? { start: shiftPosition(s.start, base), end: shiftPosition(s.end, base) } : s;
  let tokens: Token[];
  try {
    tokens = tokenize(text, 'assertion').tokens.map((t) => ({ ...t, span: shiftSpan(t.span) }));
  } catch (e) {
    if (e instanceof SiplError) throw new SiplError(e.diagnostic.code, e.diagnostic.message, shiftSpan(e.diagnostic.span));
    throw e;
  }
  const parser = new Parser(tokens, 'assertion');
  const e = kind === 'bool' ? parser.bexp() : parser.aexp();
  parser.finish();
  number(e, 0);
  return e;
}

/** Assigns preorder ids starting at `from`; returns the next free id. */
function number(root: Node, from: number): number {
  let id = from;
  for (const n of walk(root)) n.id = id++;
  return id;
}

/** Parses a SIPL or SIPL-R program, including its `//@` annotations. Throws `SiplError`. */
export function parseProgram(source: string): Program {
  const { tokens, annotations } = tokenize(source, 'program');
  const program = new Parser(tokens, 'program').program();
  program.annotations = annotations;
  resolveZeroArgCalls(program);
  let nextId = number(program, 0);

  const loops = [...walk(program)].filter((n): n is While => n.kind === 'while');
  for (const a of annotations) {
    const e = parseAssertion(a.text, a.span.start, a.key === 'variant' ? 'int' : 'bool');
    nextId = number(e, nextId);
    if (a.key === 'pre' || a.key === 'post') {
      if (program[a.key]) throw duplicate(a);
      program[a.key] = e;
      continue;
    }
    const loop = loops.find((w) => w.span.start.offset > a.span.start.offset);
    if (!loop) {
      throw new SiplError('E005', `'//@ ${a.key}' must come before the while loop it describes`, a.span);
    }
    if (loop[a.key]) throw duplicate(a);
    loop[a.key] = e;
  }
  return program;
}

function duplicate(a: Annotation): SiplError {
  return new SiplError('E004', `duplicate '//@ ${a.key}' annotation`, a.span);
}

/** A bare name that is a declared function is a call without arguments (rule CF1). */
function resolveZeroArgCalls(program: Program): void {
  const names = new Set(program.functions.map((f) => f.name));
  if (names.size === 0) return;
  for (const n of walk(program)) {
    if (n.kind === 'var' && names.has(n.name)) {
      Object.assign(n, { kind: 'call', args: [] });
    }
  }
}
