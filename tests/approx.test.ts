import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parseProgram } from '../src/parser.js';
import { applyApproximation, approximationTerms, describeApproximations, printApproximation, treeSize } from '../src/fixpoint/approx.js';
import { envOf, evalValue } from '../src/semantics/evaluate.js';
import { buildFunctional } from '../src/semantics/term.js';
import { printTerm } from '../src/semantics/print.js';
import { readExample } from './helpers.js';

const div = parseProgram(readExample('rec-div.sipl'));

test('approximations of practical work 7 (x ÷ y)', () => {
  const [f0, f1, f2] = approximationTerms(div, 'f', 2).map(printTerm);
  assert.equal(f0, '⊥');
  assert.equal(f1, 'IF(S^2(less, X⇒, Y⇒), 0, ⊥)');
  assert.equal(
    f2,
    'IF(S^2(less, X⇒, Y⇒), 0, S^2(add, S^[X,Y](IF(S^2(less, X⇒, Y⇒), 0, ⊥), S^2(sub, X⇒, Y⇒), Y⇒), 1))',
  );
});

test('testing the approximations on [X ↦ 7, Y ↦ 4] as in the practicum', () => {
  const st = { X: 7, Y: 4 };
  assert.equal(applyApproximation(div, 'f', 0, st).ok, false);
  const f1 = applyApproximation(div, 'f', 1, st);
  assert.equal(f1.ok, false);
  assert.equal(f1.ok === false && f1.undef.reason, 'bottom');
  const f2 = applyApproximation(div, 'f', 2, st);
  assert.deepEqual([f2.ok, f2.ok && f2.value], [true, 1]);
  assert.ok(f2.steps.some((s) => s.formula === 'AF_CALL' && s.detail.includes('[X ↦ 3, Y ↦ 4]')));
  assert.ok(f1.steps.some((s) => s.formula === 'AF_BOT'));
});

test('applying an approximation term agrees with evaluation at level k', () => {
  const env = envOf(div);
  const phi = buildFunctional(div, 'f');
  for (let k = 0; k <= 4; k++) {
    for (let x = 0; x <= 12; x++) {
      for (let y = 1; y <= 4; y++) {
        const byTerm = applyApproximation(div, 'f', k, { X: x, Y: y });
        const byLevel = k === 0 ? { ok: false } : evalValue(phi, { X: x, Y: y }, env, { level: k - 1 });
        assert.equal(byTerm.ok, byLevel.ok, `k=${k} x=${x} y=${y}`);
        if (byTerm.ok && byLevel.ok) assert.equal(byTerm.value, (byLevel as { value: number }).value);
      }
    }
  }
});

test('factorial: f_k is defined exactly for N ≤ k (Example 5.1)', () => {
  const p = parseProgram(readExample('rec-factorial.sipl'));
  const states = [1, 2, 3, 4, 5].map((n) => ({ N: n }));
  const table = describeApproximations(p, 'f', 4, states);
  assert.deepEqual(table.rows.map((r) => r.firstDefined), [1, 2, 3, 4, null]);
  assert.deepEqual(table.rows[2].values, [null, null, null, 6, 6]);
  assert.deepEqual(table.definedCount, [0, 1, 2, 3, 4]);
});

test('defined values never change with k (monotonicity)', () => {
  const states = [];
  for (let x = 0; x <= 15; x++) for (let y = 1; y <= 5; y++) states.push({ X: x, Y: y });
  const table = describeApproximations(div, 'f', 6, states);
  for (const row of table.rows) {
    const first = row.values.findIndex((v) => v !== null);
    if (first < 0) continue;
    for (const v of row.values.slice(first)) assert.equal(v, row.values[first]);
    assert.equal(row.values[first], Math.floor(row.state.X / row.state.Y));
  }
});

test('helper functions are approximated together with the main function', () => {
  const p = parseProgram(readExample('rec-power.sipl'));
  const table = describeApproximations(p, 'p', 4, [{ X: 3, Y: 0 }, { X: 3, Y: 2 }, { X: 3, Y: 4 }]);
  assert.deepEqual(table.rows.map((r) => r.firstDefined), [2, 3, 4]);
  assert.equal(table.rows[2].values[4], 81);
});

test('huge approximation terms are not printed in full', () => {
  const p = parseProgram(readExample('rec-fib.sipl'));
  const terms = approximationTerms(p, 'fib', 25);
  assert.ok(treeSize(terms[25]) > 1_000_000);
  const text = printApproximation(terms, 25, 'fib', 2_000);
  assert.match(text, /^φ\(fib24\)/);
  assert.ok(text.length < 200);
  assert.equal(printApproximation(terms, 1, 'fib'), 'IF(S^2(less, N⇒, 2), N⇒, ⊥)');
});

test('unknown function is rejected', () => {
  assert.throws(() => approximationTerms(div, 'g', 2), /no function g/);
});
