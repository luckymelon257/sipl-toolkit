import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parseProgram } from '../src/parser.js';
import { envOf, evalState, evalValue, runProgram } from '../src/semantics/evaluate.js';
import { buildFunctional, buildTerm } from '../src/semantics/term.js';
import { formatState, parseAssignments } from '../src/values.js';
import { listExamples, readExample, runSpecs } from './helpers.js';

const prog = (name: string) => parseProgram(readExample(name));

test('power term on [X ↦ 5, Y ↦ 2] gives R ↦ 25 (practicum, practical work 2)', () => {
  const r = runProgram(prog('power.sipl'), { X: 5, Y: 2 });
  assert.equal(r.status, 'defined');
  assert.deepEqual(r.state, { X: 5, Y: 0, R: 25 });
});

test('GCD term on [M ↦ 8, N ↦ 16] (Example 1.4)', () => {
  const r = runProgram(prog('gcd.sipl'), { M: 8, N: 16 });
  assert.deepEqual(r.state, { M: 8, N: 8 });
});

test('every example produces its documented results', () => {
  for (const f of listExamples()) {
    const specs = runSpecs(readExample(f));
    assert.ok(specs.length > 0, `${f} documents no run`);
    for (const { input, expect } of specs) {
      const r = runProgram(prog(f), input);
      assert.equal(r.status, 'defined', `${f} ${JSON.stringify(input)}: ${r.undef?.message}`);
      for (const [k, v] of Object.entries(expect)) assert.equal(r.state?.[k], v, `${f} ${JSON.stringify(input)} ${k}`);
    }
  }
});

test('recursive division 7 ÷ 4 = 1 (practical work 7)', () => {
  assert.equal(runProgram(prog('rec-div.sipl'), { A: 7, B: 4 }).state?.Q, 1);
});

test('reading an unassigned variable is undefined, with the variable named', () => {
  const r = runProgram(parseProgram('begin X := Y + 1 end'), {});
  assert.equal(r.status, 'undefined');
  assert.equal(r.undef?.reason, 'unbound-variable');
  assert.match(r.undef!.message, /Y/);
});

test('a non-terminating loop hits the iteration limit', () => {
  const r = runProgram(parseProgram('begin while 1 = 1 do X := X + 1 end'), { X: 0 }, { maxIterations: 50 });
  assert.equal(r.status, 'undefined');
  assert.equal(r.undef?.reason, 'iteration-limit');
});

test('runaway recursion is reported, not thrown', () => {
  const p = parseProgram('program func f(X) = f(X + 1) begin Y := f(0) end');
  const r = runProgram(p, {});
  assert.equal(r.undef?.reason, 'call-depth');
  const deep = runProgram(p, {}, { maxCallDepth: 1_000_000 });
  assert.equal(deep.status, 'undefined');
  assert.equal(deep.undef?.reason, 'call-depth');
});

test('integer overflow makes the value undefined', () => {
  const r = runProgram(parseProgram('begin X := 9007199254740991 + 1 end'), {});
  assert.equal(r.undef?.reason, 'overflow');
});

test('evaluation at a finite level is an approximation', () => {
  const p = prog('rec-div.sipl');
  const env = envOf(p);
  const phi = buildFunctional(p, 'f');
  // With `level: k`, calls in the evaluated term refer to the approximation f_k, so φ at level k is f_(k+1).
  assert.deepEqual(evalValue(phi, { X: 7, Y: 4 }, env, { level: 0 }), { ok: false, undef: { reason: 'bottom', message: 'f is undefined at approximation level 0 (f0 = ⊥)' } });
  assert.deepEqual(evalValue(phi, { X: 7, Y: 4 }, env, { level: 1 }), { ok: true, value: 1 });
  assert.equal(evalValue(phi, { X: 9, Y: 4 }, env, { level: 1 }).ok, false);
  assert.deepEqual(evalValue(phi, { X: 3, Y: 4 }, env, { level: 0 }), { ok: true, value: 0 });
});

test('recorded steps follow the formulas AF_* of the course', () => {
  const r = runProgram(prog('power.sipl'), { X: 5, Y: 2 }, { record: true });
  const formulas = new Set(r.steps.map((s) => s.formula));
  for (const f of ['AF_SEQ', 'AF_AS', 'AF_WH', 'AF_S']) assert.ok(formulas.has(f as never), f);
  const wh = r.steps.filter((s) => s.formula === 'AF_WH').map((s) => s.detail);
  assert.deepEqual(wh, [
    'st0 = [X ↦ 5, Y ↦ 2, R ↦ 1], S^2(gr, Y⇒, 0)(st0) = true',
    'st1 = [X ↦ 5, Y ↦ 1, R ↦ 5], S^2(gr, Y⇒, 0)(st1) = true',
    'st2 = [X ↦ 5, Y ↦ 0, R ↦ 25], S^2(gr, Y⇒, 0)(st2) = false, result st2',
  ]);
  assert.ok(r.steps.some((s) => s.formula === 'AF_AS' && s.detail === '[X ↦ 5, Y ↦ 2] ∇ [R ↦ 1] = [X ↦ 5, Y ↦ 2, R ↦ 1]'));
  assert.ok(r.steps.some((s) => s.formula === 'AF_S' && s.detail === 'gr(2, 0) = true'));
});

test('recorded steps of a call show the local superposition', () => {
  const r = runProgram(prog('rec-div.sipl'), { A: 7, B: 4 }, { record: true });
  const call = r.steps.find((s) => s.formula === 'AF_CALL')!;
  assert.equal(call.detail, 'f([A ↦ 7, B ↦ 4] ∇ [X ↦ 7, Y ↦ 4])');
});

test('step recording is capped and reports truncation', () => {
  const r = runProgram(prog('power.sipl'), { X: 2, Y: 50 }, { record: true, maxSteps: 10 });
  assert.equal(r.steps.length, 10);
  assert.equal(r.truncated, true);
});

test('evalState works on any statement term', () => {
  const t = buildTerm(parseProgram('begin skip end'));
  assert.deepEqual(evalState(t, { A: 1 }, {}), { ok: true, state: { A: 1 } });
});

test('formatState and parseAssignments', () => {
  assert.equal(formatState({ X: 5, Y: -2 }), '[X ↦ 5, Y ↦ -2]');
  assert.equal(formatState({}), '[]');
  assert.deepEqual(parseAssignments(['X=5', 'Y=-2,Z=0']), { X: 5, Y: -2, Z: 0 });
  assert.throws(() => parseAssignments(['X=five']), /X=five/);
  assert.throws(() => parseAssignments(['1X=2']), /1X=2/);
});
