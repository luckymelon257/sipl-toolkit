import type { Term } from './term.js';

/**
 * Prints a term in the notation of the practicum, e.g.
 * `AS^R(1) · WH(S^2(gr, Y⇒, 0), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1)))`.
 * Superscripts are written with `^`; the local superposition S^{x1,...,xn} is written `S^[x1,...,xn]`.
 */
export function printTerm(t: Term): string {
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
