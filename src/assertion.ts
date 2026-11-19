import type { Expr } from './ast.js';
import { State, checkedInt } from './values.js';

/**
 * Value of an assertion-language expression on a state, or `undefined` when it is not defined
 * (unbound variable, division by zero, negative exponent, overflow, unknown function).
 * Connectives are strict: an undefined operand makes the whole formula undefined.
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
      const l = bool(e.left);
      const r = bool(e.right);
      if (l === undefined || r === undefined) return undefined;
      return e.op === 'and' ? l && r : e.op === 'or' ? l || r : !l || r;
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
