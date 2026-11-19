import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parseAssertion, parseProgram } from '../src/parser.js';
import { printExpr } from '../src/assertion.js';
import { substitute, generateVCs } from '../src/verify/wp.js';
import { checkVC, verifyProgram } from '../src/verify/verify.js';
import { listExamples, readExample } from './helpers.js';

const load = (name: string) => parseProgram(readExample(`verify/${name}`));

test('printExpr prints with minimal parentheses', () => {
  const p = (s: string) => printExpr(parseAssertion(s));
  assert.equal(p('(A + B) * C = A - (B - C)'), '(A + B) * C = A - (B - C)');
  assert.equal(p('A = 1 ∧ (B = 1 ∨ C = 1) → ¬(D = 1)'), 'A = 1 ∧ (B = 1 ∨ C = 1) → ¬D = 1');
  assert.equal(p('X ^ (Y ^ 2) = (X ^ Y) ^ 2'), 'X ^ Y ^ 2 = (X ^ Y) ^ 2');
  assert.equal(p('X - -1 >= 0'), 'X - -1 ≥ 0');
});

test('substitution Q[x ↦ a] replaces every free occurrence', () => {
  const q = parseAssertion('R * X ^ Y = x ^ y ∧ Y ≥ 0');
  const a = parseAssertion('Y - 1', undefined, 'int');
  assert.equal(printExpr(substitute(q, 'Y', a)), 'R * X ^ (Y - 1) = x ^ y ∧ Y - 1 ≥ 0');
});

test('verification conditions of the power program', () => {
  const vcs = generateVCs(load('power.sipl'));
  assert.deepEqual(vcs.map((v) => v.kind), ['entry', 'preserve', 'exit', 'variant-bound', 'variant-decrease']);
  const preserve = vcs[1];
  assert.equal(printExpr(preserve.hypothesis), 'R * X ^ Y = x ^ y ∧ Y ≥ 0 ∧ X = x ∧ Y > 0');
  assert.equal(printExpr(preserve.goal), 'R * X * X ^ (Y - 1) = x ^ y ∧ Y - 1 ≥ 0 ∧ X = x');
  assert.ok(preserve.derivation.some((l) => l === 'wp(Y := Y - 1, R * X ^ Y = x ^ y ∧ Y ≥ 0 ∧ X = x) = R * X ^ (Y - 1) = x ^ y ∧ Y - 1 ≥ 0 ∧ X = x'));
  assert.equal(printExpr(vcs[0].goal), '1 * X ^ Y = x ^ y ∧ Y ≥ 0 ∧ X = x');
  assert.equal(printExpr(vcs[4].goal), 'Y - 1 < t0');
});

test('the power program is verified in bounds with total correctness', () => {
  const r = verifyProgram(load('power.sipl'));
  assert.deepEqual(r.diagnostics, []);
  assert.equal(r.verdict, 'checked-in-bounds');
  assert.equal(r.total, true);
  assert.ok(r.vcs.every((v) => v.result.status === 'checked'));
  assert.ok(r.runs.count > 0);
  assert.deepEqual(r.runs.violations, []);
});

test('GCD: total correctness with the variant M + N (theorems 1.3-1.4)', () => {
  const r = verifyProgram(load('gcd.sipl'));
  assert.equal(r.verdict, 'checked-in-bounds');
  assert.equal(r.total, true);
  assert.equal(r.vcs.length, 5);
});

test('every annotated example except the deliberately wrong ones verifies', () => {
  for (const f of listExamples('verify')) {
    if (/wrong|not-inductive/.test(f)) continue;
    const r = verifyProgram(parseProgram(readExample(f)));
    assert.equal(r.verdict, 'checked-in-bounds', `${f}: ${JSON.stringify(r.vcs.filter((v) => v.result.status !== 'checked').map((v) => v.title))}`);
  }
});

test('a wrong invariant is refuted with a counterexample and a failing run', () => {
  const r = verifyProgram(load('wrong-invariant.sipl'));
  assert.equal(r.verdict, 'refuted');
  const entry = r.vcs.find((v) => v.kind === 'entry')!;
  assert.equal(entry.result.status, 'refuted');
  const ce = entry.result.status === 'refuted' ? entry.result.counterexample : {};
  assert.equal(ce.X, ce.x);
  assert.equal(ce.Y, ce.y);
  const v = r.runs.violations[0];
  assert.equal(v.kind, 'invariant');
  assert.equal(v.iteration, 0);
});

test('non-inductive invariant: the step fails, but no real run violates it', () => {
  const r = verifyProgram(load('not-inductive.sipl'));
  assert.equal(r.verdict, 'unproven');
  const step = r.vcs.find((v) => v.kind === 'preserve')!;
  assert.equal(step.result.status, 'refuted');
  if (step.result.status === 'refuted') {
    assert.equal(step.result.counterexample.X, 3);
    assert.deepEqual(step.result.afterBody, { X: 5 });
  }
  assert.deepEqual(r.runs.violations, []);
  assert.match(r.summary, /not inductive|strengthen/);
});

test('a postcondition that does not hold is caught by the exit condition and by runs', () => {
  const src = readExample('verify/power.sipl').replace('//@ post: R = x ^ y', '//@ post: R = x ^ y + 1');
  const r = verifyProgram(parseProgram(src));
  assert.equal(r.verdict, 'refuted');
  assert.equal(r.vcs.find((v) => v.kind === 'exit')!.result.status, 'refuted');
  assert.equal(r.runs.violations[0].kind, 'post');
});

test('a loop without an invariant is a diagnostic', () => {
  const r = verifyProgram(parseProgram('begin while X > 0 do X := X - 1 end'));
  assert.deepEqual(r.diagnostics.map((d) => d.code), ['V001']);
  assert.equal(r.verdict, 'unproven');
});

test('function calls are not supported by the verifier', () => {
  const r = verifyProgram(parseProgram(readExample('rec-div.sipl')));
  assert.deepEqual(r.diagnostics.map((d) => d.code), ['V002']);
});

test('without a variant only partial correctness is claimed', () => {
  const src = readExample('verify/power.sipl').replace(/^ *\/\/@ variant.*$/m, '');
  const r = verifyProgram(parseProgram(src));
  assert.equal(r.verdict, 'checked-in-bounds');
  assert.equal(r.total, false);
});

test('a bad variant is refuted', () => {
  const src = readExample('verify/power.sipl').replace('//@ variant: Y', '//@ variant: 10 - Y');
  const r = verifyProgram(parseProgram(src));
  assert.equal(r.vcs.find((v) => v.kind === 'variant-decrease')!.result.status, 'refuted');
});

test('checkVC samples when the box is too large and says so', () => {
  const vc = generateVCs(load('power.sipl'))[1];
  const r = checkVC(vc, { range: [-50, 50], maxCases: 1000 });
  assert.equal(r.status, 'checked');
  assert.equal(r.status === 'checked' && r.mode, 'sampled');
  assert.equal(r.status === 'checked' && r.cases, 1000);
});
