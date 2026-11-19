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
  // The old value t0 of the variant is bound to the variant itself, so it is not a free variable of the check.
  assert.equal(printExpr(vcs[4].hypothesis), 'R * X ^ Y = x ^ y ∧ Y ≥ 0 ∧ X = x ∧ Y > 0');
  assert.equal(printExpr(vcs[4].goal), 'Y - 1 < Y');
  assert.ok(vcs[4].derivation.some((l) => l.includes('t0 ↦ Y')));
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
  // Every pair of positive initial values in [-3, 8] is run: 8 × 8 executions.
  assert.deepEqual([r.runs.count, r.runs.mode], [64, 'exhaustive']);
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

test('vacuous conditions are pointed out', () => {
  const narrow = verifyProgram(load('not-inductive.sipl'));
  assert.match(narrow.summary, /condition\(s\) 3 never had a true hypothesis/);
  const wide = verifyProgram(load('not-inductive.sipl'), { range: [0, 12] });
  assert.doesNotMatch(wide.summary, /never had a true hypothesis/);
});

const FLAG_6 = [
  '//@ pre: B = B ∧ C = C ∧ D = D ∧ E = E ∧ F = F',
  'begin',
  '  X := 0;',
  '  //@ invariant: X ≠ 5 ∨ B ≠ 1 ∨ C ≠ 2 ∨ D ≠ 3 ∨ E ≠ 4 ∨ F ≠ 0',
  '  while X < 10 do X := X + 2',
  'end',
  '//@ post: X ≥ 10',
].join('\n');

test('a sampled check never claims to cover all states', () => {
  const r = verifyProgram(parseProgram(FLAG_6));
  // The exit condition needs X ≥ 10, which the default box never reaches, so the check is not complete either.
  assert.equal(r.verdict, 'inconclusive');
  assert.match(r.summary, /random sample/);
  assert.doesNotMatch(r.summary, /all variables in/);
  assert.equal(verifyProgram(parseProgram(FLAG_6), { maxCases: 3_000_000 }).verdict, 'unproven');
});

test('every condition of the power program is checked exhaustively', () => {
  const r = verifyProgram(load('power.sipl'));
  assert.ok(r.vcs.every((v) => v.result.status === 'checked' && v.result.mode === 'exhaustive'));
});

test('runs cut at the run limit are reported as truncated', () => {
  const r = verifyProgram(load('gcd.sipl'), { maxRuns: 3 });
  assert.deepEqual([r.runs.count, r.runs.mode], [3, 'truncated']);
  assert.equal(r.verdict, 'checked-in-sample');
});

const NESTED = [
  '//@ pre: A = a ∧ B = b ∧ a ≥ 0 ∧ b ≥ 0',
  'begin R := 0;',
  '  //@ invariant: R = (a - A) * b ∧ A ≥ 0 ∧ B = b ∧ b ≥ 0',
  '  //@ variant: A',
  '  while A > 0 do begin',
  '    C := B;',
  '    //@ invariant: R + C = (a - A + 1) * b ∧ C ≥ 0 ∧ A > 0 ∧ B = b ∧ b ≥ 0',
  '    //@ variant: C',
  '    while C > 0 do begin R := R + 1; C := C - 1 end;',
  '    A := A - 1 end',
  'end',
  '//@ post: R = a * b',
].join('\n');

test('nested loops: the outer variant passes the inner loop by the frame rule', () => {
  const r = verifyProgram(parseProgram(NESTED), { range: [0, 4] });
  assert.equal(r.verdict, 'checked-in-bounds', JSON.stringify(r.vcs.filter((v) => v.result.status !== 'checked').map((v) => [v.title, printExpr(v.goal)])));
  assert.equal(r.total, true);
  const dec = r.vcs.find((v) => v.kind === 'variant-decrease' && v.loop!.span.start.line === 5)!;
  assert.equal(printExpr(dec.goal), 'A - 1 < A');
  assert.ok(dec.derivation.some((l) => /frame/.test(l)));
});

test('an inner loop that changes the outer variant is reported, not failed', () => {
  const src = [
    '//@ pre: A ≥ 0',
    'begin',
    '  //@ invariant: A ≥ 0',
    '  //@ variant: A',
    '  while A > 0 do begin',
    '    //@ invariant: A ≥ 0',
    '    while A > 5 do A := A - 1;',
    '    A := A - 1',
    '  end',
    'end',
  ].join('\n');
  const r = verifyProgram(parseProgram(src));
  assert.deepEqual(r.diagnostics.map((d) => [d.code, d.severity]), [['V003', 'warning']]);
  assert.ok(!r.vcs.some((v) => v.kind === 'variant-decrease' && v.loop!.span.start.line === 5));
  assert.equal(r.total, false);
  assert.notEqual(r.verdict, 'refuted');
});

test('runs that exceed the iteration budget are inconclusive, not violations', () => {
  const r = verifyProgram(load('sum.sipl'), { range: [12000, 12002] });
  assert.notEqual(r.verdict, 'refuted');
  assert.equal(r.runs.inconclusive, 3);
  assert.match(r.summary, /did not finish/);
  const more = verifyProgram(load('sum.sipl'), { range: [12000, 12002], maxIterations: 20_000 });
  assert.equal(more.runs.inconclusive, 0);
});

test('runs check the variant at every loop head', () => {
  const src = readExample('verify/power.sipl').replace('//@ variant: Y', '//@ variant: 10 - Y');
  const r = verifyProgram(parseProgram(src));
  assert.equal(r.verdict, 'refuted');
  assert.equal(r.runs.violations[0].kind, 'variant');
});

test('unknown functions in annotations are rejected', () => {
  assert.throws(() => parseProgram('begin skip end\n//@ post: foo(X) = 1'), /E006|unknown function foo/);
  assert.throws(() => parseAssertion('gcd(X) = 1'), /gcd/);
});

test('a check that tests nothing is inconclusive, never a pass', () => {
  const src = [
    '//@ pre: X > 100',
    'begin',
    '  //@ invariant: X > 1000',
    '  while X > 0 do X := X - 1',
    'end',
    '//@ post: X = 77',
  ].join('\n');
  const r = verifyProgram(parseProgram(src));
  assert.equal(r.verdict, 'inconclusive');
  assert.equal(r.runs.count, 0);
  assert.match(r.summary, /never run/);
  assert.equal(verifyProgram(parseProgram(src), { range: [95, 110] }).verdict, 'refuted');
});

test('overflow makes a run inconclusive, not a refutation', () => {
  const r = verifyProgram(load('power.sipl'), { range: [0, 20] });
  assert.notEqual(r.verdict, 'refuted', r.summary);
  assert.ok(r.runs.inconclusive > 0);
  assert.match(r.summary, /integer range/);
});

test('ghost variables that occur only in the postcondition range over the box in runs', () => {
  const r = verifyProgram(parseProgram('//@ pre: X = X\nbegin X := 1 end\n//@ post: X = 1 ∧ Z = Z'));
  assert.equal(r.verdict, 'checked-in-bounds', r.summary);
  assert.equal(r.runs.count, 144);
});
