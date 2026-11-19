import { test } from 'node:test';
import assert from 'node:assert/strict';
import { check } from '../src/check.js';
import { readExample } from './helpers.js';

const codes = (src: string) => check(src).diagnostics.map((d) => d.code);

test('power program: inputs X and Y, base dialect, no errors', () => {
  const r = check(readExample('power.sipl'));
  assert.equal(r.ok, true);
  assert.equal(r.dialect, 'SIPL');
  assert.deepEqual(r.inputs, ['Y', 'X']);
  assert.deepEqual(r.diagnostics.map((d) => [d.code, d.severity]), [['W001', 'warning'], ['W001', 'warning']]);
  assert.ok(r.program);
});

test('syntax errors become diagnostics instead of exceptions', () => {
  const r = check('begin X := 1; end');
  assert.equal(r.ok, false);
  assert.equal(r.program, undefined);
  assert.deepEqual(codes('begin X := 1; end'), ['E100']);
});

test('a variable assigned in only one branch is still an input', () => {
  const r = check('begin if A > 0 then X := 1 else skip; Y := X end');
  assert.deepEqual(r.inputs, ['A', 'X']);
});

test('a variable assigned in both branches is defined afterwards', () => {
  assert.deepEqual(check('begin if A > 0 then X := 1 else X := 2; Y := X end').inputs, ['A']);
});

test('assignments inside a loop body do not count after the loop', () => {
  assert.deepEqual(check('begin while A > 0 do begin X := 1; A := A - 1 end; Y := X end').inputs, ['A', 'X']);
});

test('SIPL-R dialect and function checks', () => {
  const r = check(readExample('rec-div.sipl'));
  assert.equal(r.ok, true);
  assert.equal(r.dialect, 'SIPL-R');
  assert.deepEqual(r.inputs, ['A', 'B']);
});

test('unknown function', () => {
  const r = check('begin X := g(1) end');
  assert.deepEqual(codes('begin X := g(1) end'), ['E300']);
  assert.equal(r.ok, false);
  assert.deepEqual(r.diagnostics[0].span.start, { line: 1, column: 12, offset: 11 });
});

test('arity mismatch', () => {
  assert.deepEqual(codes('program func f(X) = X begin Y := f(1, 2) end'), ['E301']);
  assert.deepEqual(codes('program func f(X, Y) = X begin Y := f end'), ['E301']);
});

test('duplicate function and duplicate parameter', () => {
  assert.deepEqual(codes('program func f = 1; func f = 2 begin X := f end'), ['E302']);
  assert.deepEqual(codes('program func f(X, X) = X begin Y := f(1, 2) end'), ['E303']);
});

test('assignment to a function name', () => {
  assert.deepEqual(codes('program func f = 1 begin f := 2 end'), ['E304']);
});

test('function body reading a non-parameter variable is a warning', () => {
  const r = check('program func f(X) = X + K begin K := 1; Y := f(2) end');
  assert.equal(r.ok, true);
  assert.deepEqual(r.diagnostics.map((d) => d.code), ['W002']);
  assert.match(r.diagnostics[0].message, /K/);
});

test('ghost variables in annotations are not program inputs', () => {
  const r = check(readExample('verify/power.sipl'));
  assert.equal(r.ok, true);
  assert.deepEqual(r.inputs, ['Y', 'X']);
});
