import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parseAssertion, parseProgram } from '../src/parser.js';
import { evalAssertion } from '../src/assertion.js';
import { checkMonotone, gridStates, testApproximations } from '../src/fixpoint/report.js';
import { renderHtml, renderTable } from '../src/fixpoint/render.js';
import { readExample } from './helpers.js';

const div = parseProgram(readExample('rec-div.sipl'));
const a = (s: string) => parseAssertion(s, undefined, 'int');

test('assertion evaluation: arithmetic, logic and partiality', () => {
  const ev = (s: string, st = {}) => evalAssertion(parseAssertion(s), st);
  const n = (s: string, st = {}) => evalAssertion(a(s), st);
  assert.equal(n('7 div 2'), 3);
  assert.equal(n('-7 div 2'), -4);
  assert.equal(n('-7 mod 2'), 1);
  assert.equal(n('2 ^ 10'), 1024);
  assert.equal(n('gcd(12, 18) + abs(-3)'), 9);
  assert.equal(n('if X > 0 then X else 0 - X', { X: -4 }), 4);
  assert.equal(n('1 div 0'), undefined);
  assert.equal(n('2 ^ -1'), undefined);
  assert.equal(n('2 ^ 60'), undefined);
  assert.equal(n('Z + 1'), undefined);
  assert.equal(ev('X > 1 → X ≥ 1', { X: 0 }), true);
  assert.equal(ev('X ≠ 1 ∧ ¬X = 2 ∨ false', { X: 3 }), true);
  assert.equal(ev('true → 1 div 0 = 1'), undefined);
});

test('grid of test states', () => {
  assert.deepEqual(gridStates('X=0..2,Y=1..2'), [
    { X: 0, Y: 1 }, { X: 0, Y: 2 }, { X: 1, Y: 1 }, { X: 1, Y: 2 }, { X: 2, Y: 1 }, { X: 2, Y: 2 },
  ]);
  assert.deepEqual(gridStates('N=-1..1, M=5'), [{ N: -1, M: 5 }, { N: 0, M: 5 }, { N: 1, M: 5 }]);
  assert.throws(() => gridStates('X=3..1'), /empty range/);
  assert.throws(() => gridStates('X=0..1000,Y=0..1000'), /too many/);
  assert.throws(() => gridStates('X'), /bad grid/);
});

test('division: fk becomes defined at k = x div y + 1', () => {
  const r = testApproximations(div, 'f', { k: 5, states: gridStates('X=0..14,Y=1..4'), expect: a('X div Y') });
  for (const row of r.table.rows) {
    const q = Math.floor(row.state.X / row.state.Y);
    assert.equal(row.firstDefined, q + 1 <= 5 ? q + 1 : null, JSON.stringify(row.state));
  }
  assert.equal(r.checks.monotone, true);
  assert.deepEqual(r.checks.mismatches, []);
  assert.equal(r.checks.allDefined, false);
});

test('the chain stabilises on a finite set of states', () => {
  const r = testApproximations(div, 'f', { k: 6, states: gridStates('X=0..5,Y=2..3') });
  assert.equal(r.checks.allDefined, true);
  assert.equal(r.checks.stabilizedAt, 3);
});

test('expected undefined is not a mismatch', () => {
  const r = testApproximations(div, 'f', { k: 4, states: gridStates('X=1..3,Y=1'), expect: a('X div (Y - 1)') });
  assert.deepEqual(r.checks.mismatches, []);
  assert.ok(r.rows.every((row) => row.expected === null));
});

test('a wrong expected function is reported', () => {
  const r = testApproximations(div, 'f', { k: 4, states: gridStates('X=0..3,Y=2'), expect: a('X div Y + 1') });
  assert.equal(r.checks.mismatches.length, 4);
  assert.deepEqual(r.checks.mismatches[0], { state: { X: 0, Y: 2 }, k: 1, actual: 0, expected: 1 });
});

test('where filters the test states', () => {
  const r = testApproximations(div, 'f', { k: 2, states: gridStates('X=0..3,Y=0..2'), where: parseAssertion('Y > 0') });
  assert.equal(r.table.rows.length, 8);
});

test('monotonicity check fails on a forged table', () => {
  assert.equal(checkMonotone([{ state: {}, values: [null, 1, 2], firstDefined: 1 }]), false);
  assert.equal(checkMonotone([{ state: {}, values: [null, 1, null], firstDefined: 1 }]), false);
  assert.equal(checkMonotone([{ state: {}, values: [null, null, 4], firstDefined: 2 }]), true);
});

test('text table', () => {
  const r = testApproximations(div, 'f', { k: 2, states: gridStates('X=3..4,Y=4'), expect: a('X div Y') });
  const text = renderTable(r);
  assert.match(text, /f1 = IF\(S\^2\(less, X⇒, Y⇒\), 0, ⊥\)/);
  assert.match(text, /│ 3 │ 4 │ ⊥ +│ 0 +│ 0 +│ 1 +│ 0 /);
  assert.match(text, /│ 4 │ 4 │ ⊥ +│ ⊥ +│ 1 +│ 2 +│ 1 /);
  assert.match(text, /monotone: yes/);
});

test('html report has one table row and one heatmap cell per state', () => {
  const states = gridStates('X=0..9,Y=1..3');
  const html = renderHtml(testApproximations(div, 'f', { k: 4, states, expect: a('X div Y') }));
  assert.match(html, /^<!doctype html>/);
  assert.equal(html.match(/<tr class="state"/g)?.length, states.length);
  assert.equal(html.match(/<rect class="cell"/g)?.length, states.length);
  assert.match(html, /<svg[^>]*class="bars"/);
  assert.ok(!html.includes('undefined'));
});

test('html heatmap needs one or two varying variables', () => {
  const states = gridStates('X=0..2,Y=1..2').map((s) => ({ ...s, Z: s.X }));
  const html = renderHtml(testApproximations(div, 'f', { k: 2, states }));
  assert.equal(html.match(/<rect class="cell"/g), null);
  assert.match(html, /heatmap needs/);
});
