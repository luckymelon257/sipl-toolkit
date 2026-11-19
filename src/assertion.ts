import type { Expr } from './ast.js';
import { State, checkedInt } from './values.js';

/**
 * Value of an assertion-language expression on a state, or `undefined` when it is not defined
 * (unbound variable, division by zero, negative exponent, overflow, unknown function).
 * Connectives are evaluated left to right: `false ∧ ⊥ = false`, `true ∨ ⊥ = true`, `false → ⊥ = true`,
 * so a guard such as `Y ≥ 0 ∧ X ^ Y = 1` is defined for every Y.
 */
export function evalAssertion(e: Expr, st: State): number | boolean | undefined {
  const num = (x: Expr) => {
    const v = evalAssertion(x, st);
    return typeof v === 'number' ? v : undefined;
  };
  const bool = (x: Expr) => {
    const v = evalAssertion(x, st);
    return typeof v === 'boolean' ? v : undefined;
  };
  switch (e.kind) {
    case 'num':
      return e.value;
    case 'bool':
      return e.value;
    case 'var':
      return Object.hasOwn(st, e.name) ? st[e.name] : undefined;
    case 'binary': {
      const l = num(e.left);
      const r = num(e.right);
      if (l === undefined || r === undefined) return undefined;
      return arith(e.op, l, r);
    }
    case 'cond': {
      const c = bool(e.cond);
      return c === undefined ? undefined : evalAssertion(c ? e.then : e.else, st);
    }
    case 'call': {
      const args = e.args.map(num);
      if (args.some((x) => x === undefined)) return undefined;
      const [x, y] = args as number[];
      if (e.name === 'abs' && args.length === 1) return Math.abs(x);
      if (e.name === 'gcd' && args.length === 2) return gcd(x, y);
      return undefined;
    }
    case 'compare': {
      const l = num(e.left);
      const r = num(e.right);
      if (l === undefined || r === undefined) return undefined;
      switch (e.op) {
        case '=': return l === r;
        case '!=': return l !== r;
        case '>': return l > r;
        case '<': return l < r;
        case '>=': return l >= r;
        case '<=': return l <= r;
      }
      return undefined;
    }
    case 'logic': {
      // Left-to-right (McCarthy) evaluation: the left operand may decide the result alone.
      const l = bool(e.left);
      if (l === undefined) return undefined;
      if (e.op === 'and' && !l) return false;
      if (e.op === 'or' && l) return true;
      if (e.op === 'implies' && !l) return true;
      return bool(e.right);
    }
    case 'not': {
      const v = bool(e.operand);
      return v === undefined ? undefined : !v;
    }
  }
}

function arith(op: string, a: number, b: number): number | undefined {
  switch (op) {
    case '+': return checkedInt(a + b);
    case '-': return checkedInt(a - b);
    case '*': return checkedInt(a * b);
    case 'div': return b === 0 ? undefined : checkedInt(Math.floor(a / b));
    case 'mod': return b === 0 ? undefined : checkedInt(a - b * Math.floor(a / b));
    case '^': return power(a, b);
  }
  return undefined;
}

function power(base: number, exp: number): number | undefined {
  if (exp < 0) return undefined;
  let r = 1;
  for (let i = 0; i < exp; i++) {
    r *= base;
    if (!Number.isSafeInteger(r)) return undefined;
    if (r === 0 || r === 1) return r; // 0^n and 1^n stay fixed
    if (r === -1) return exp % 2 === 0 ? 1 : -1;
  }
  return r;
}

function gcd(a: number, b: number): number {
  a = Math.abs(a);
  b = Math.abs(b);
  while (b !== 0) [a, b] = [b, a % b];
  return a;
}

const PREC: Record<string, number> = {
  implies: 1, or: 2, and: 3, not: 4, compare: 5, '+': 6, '-': 6, '*': 7, div: 7, mod: 7, '^': 8,
};
const SHOW: Record<string, string> = { and: '∧', or: '∨', implies: '→', '>=': '≥', '<=': '≤', '!=': '≠' };

function precedence(e: Expr): number {
  switch (e.kind) {
    case 'logic': return PREC[e.op];
    case 'not': return PREC.not;
    case 'compare': return PREC.compare;
    case 'binary': return PREC[e.op];
    case 'cond': return 0;
    default: return 10;
  }
}

/** Prints an expression in assertion syntax (Unicode connectives) with the fewest parentheses. */
export function printExpr(e: Expr): string {
  const wrap = (child: Expr, needs: boolean) => (needs ? `(${printExpr(child)})` : printExpr(child));
  const p = precedence(e);
  switch (e.kind) {
    case 'num': return String(e.value);
    case 'var': return e.name;
    case 'bool': return String(e.value);
    case 'call': return `${e.name}(${e.args.map(printExpr).join(', ')})`;
    case 'not': return `¬${wrap(e.operand, precedence(e.operand) < p)}`;
    case 'cond': return `if ${printExpr(e.cond)} then ${printExpr(e.then)} else ${printExpr(e.else)}`;
    case 'compare':
      return `${wrap(e.left, precedence(e.left) <= p)} ${SHOW[e.op] ?? e.op} ${wrap(e.right, precedence(e.right) <= p)}`;
    case 'logic':
    case 'binary': {
      const rightAssoc = e.op === 'implies' || e.op === '^';
      const l = wrap(e.left, rightAssoc ? precedence(e.left) <= p : precedence(e.left) < p);
      const r = wrap(e.right, rightAssoc ? precedence(e.right) < p : precedence(e.right) <= p);
      return `${l} ${SHOW[e.op] ?? e.op} ${r}`;
    }
  }
}
