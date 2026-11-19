import type { Term } from './term.js';

/**
 * Prints a term in the notation of the practicum, e.g.
 * `AS^R(1) · WH(S^2(gr, Y⇒, 0), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1)))`.
 * Superscripts are written with `^`; the local superposition S^{x1,...,xn} is written `S^[x1,...,xn]`.
 */
export function printTerm(t: Term): string {
  return print(t);
}

/** Like `printTerm`, but stops after about `maxLength` characters and abbreviates the rest with `…`. */
export function printTermLimited(t: Term, maxLength: number): string {
  const budget = { left: maxLength };
  try {
    return print(t, budget);
  } catch (e) {
    if (e !== TOO_LONG) throw e;
    return `${print(t, { left: Infinity }, 1)}…`;
  }
}

const TOO_LONG = Symbol('too long');

/** Prints `t`; with a budget, stops as soon as the output would exceed it; `depth` limits nesting for abbreviations. */
function print(t: Term, budget = { left: Infinity }, depth = Infinity): string {
  if (depth <= 0) return '…';
  let children = 0;
  const printTerm = (x: Term) => {
    const s = print(x, budget, depth - 1);
    children += s.length;
    return s;
  };
  const out = printNode(t, printTerm);
  budget.left -= out.length - children; // count only this node's own characters
  if (budget.left < 0) throw TOO_LONG;
  return out;
}

function printNode(t: Term, printTerm: (x: Term) => string): string {
  switch (t.t) {
    case 'AS':
      return `AS^${t.variable}(${printTerm(t.arg)})`;
    case 'SEQ': {
      // `·` is printed left-associatively; the brackets of begin ... end appear only around a `·` operand.
      const left = t.left.t === 'PAREN' ? `(${printTerm(t.left.inner)})` : printTerm(t.left);
      const right =
        t.right.t === 'PAREN' ? `(${printTerm(t.right.inner)})`
        : t.right.t === 'SEQ' ? `(${printTerm(t.right)})`
        : printTerm(t.right);
      return `${left} · ${right}`;
    }
    case 'IF':
      return `IF(${printTerm(t.cond)}, ${printTerm(t.then)}, ${printTerm(t.else)})`;
    case 'WH':
      return `WH(${printTerm(t.cond)}, ${printTerm(t.body)})`;
    case 'ID':
      return 'id';
    case 'PAREN':
      return printTerm(t.inner);
    case 'S':
      return `S^${t.args.length}(${t.fn}, ${t.args.map(printTerm).join(', ')})`;
    case 'DNM':
      return `${t.variable}⇒`;
    case 'CONST':
      return String(t.value);
    case 'CALL':
      return t.args.length === 0
        ? printTerm(t.callee)
        : `S^[${t.params.join(',')}](${[t.callee, ...t.args].map(printTerm).join(', ')})`;
    case 'FN':
      return t.name;
    case 'BOTTOM':
      return '⊥';
  }
}
