import { test } from 'node:test';
import assert from 'node:assert/strict';
import { tokenize } from '../src/lexer.js';
import { SiplError } from '../src/span.js';

const kinds = (src: string, mode: 'program' | 'assertion' = 'program') =>
  tokenize(src, mode).tokens.map((t) => t.kind);

function lexError(src: string): SiplError {
  try {
    tokenize(src);
  } catch (e) {
    assert.ok(e instanceof SiplError);
    return e;
  }
  assert.fail('expected a lexical error');
}

test('tokenizes the power program', () => {
  const src = 'begin R := 1; while Y > 0 do begin R := R * X; Y := Y - 1 end end';
  assert.deepEqual(kinds(src), [
    'begin', 'ident', ':=', 'number', ';', 'while', 'ident', '>', 'number', 'do',
    'begin', 'ident', ':=', 'ident', '*', 'ident', ';', 'ident', ':=', 'ident', '-', 'number',
    'end', 'end', 'eof',
  ]);
});

test('maps Unicode operators from the textbook', () => {
  assert.deepEqual(kinds('¬ M = N ∨ X > Y – 1 − 2 ∗ 3 × 4'), [
    'not', 'ident', '=', 'ident', 'or', 'ident', '>', 'ident', '-', 'number', '-', 'number',
    '*', 'number', '*', 'number', 'eof',
  ]);
  assert.deepEqual(kinds('not A or B'), ['not', 'ident', 'or', 'ident', 'eof']);
});

test('recognises SIPL-R keywords and punctuation', () => {
  assert.deepEqual(kinds('program func f(X, Y) = if X < Y then 0 else 1 begin skip end'), [
    'program', 'func', 'ident', '(', 'ident', ',', 'ident', ')', '=', 'if', 'ident', '<', 'ident',
    'then', 'number', 'else', 'number', 'begin', 'skip', 'end', 'eof',
  ]);
});

test('CRLF line endings give correct line and column', () => {
  const { tokens } = tokenize('begin\r\n  X := 10\r\nend');
  const x = tokens[1];
  assert.equal(x.text, 'X');
  assert.deepEqual(x.span.start, { line: 2, column: 3, offset: 9 });
  const ten = tokens[3];
  assert.deepEqual(ten.span.start, { line: 2, column: 8, offset: 14 });
  assert.deepEqual(ten.span.end, { line: 2, column: 10, offset: 16 });
  assert.deepEqual(tokens[4].span.start, { line: 3, column: 1, offset: 18 });
});

test('rejects div and mod in programs with a dedicated message', () => {
  const e = lexError('begin X := Y div 2 end');
  assert.equal(e.diagnostic.code, 'E002');
  assert.match(e.diagnostic.message, /div/);
  assert.match(e.diagnostic.message, /not part of SIPL/);
  assert.deepEqual(e.diagnostic.span.start, { line: 1, column: 14, offset: 13 });
  assert.equal(lexError('begin X := Y mod 2 end').diagnostic.code, 'E002');
  assert.equal(lexError('begin X := 1 end //@ pre: x ∧ y\nX ∧ Y').diagnostic.code, 'E002');
});

test('assertion mode accepts the extended operators', () => {
  assert.deepEqual(kinds('A ∧ B → C ≤ D ≥ E ≠ F ^ 2 div 3 mod 4 <= >= != and implies', 'assertion'), [
    'ident', 'and', 'ident', 'implies', 'ident', '<=', 'ident', '>=', 'ident', '!=', 'ident', '^',
    'number', 'div', 'number', 'mod', 'number', '<=', '>=', '!=', 'and', 'implies', 'eof',
  ]);
});

test('collects //@ annotations and skips ordinary comments', () => {
  const src = [
    '//@ pre: X = x ∧ X > 0',
    'begin // plain comment',
    '  //@ invariant: R = 1',
    '  skip',
    'end',
  ].join('\n');
  const { tokens, annotations } = tokenize(src);
  assert.deepEqual(tokens.map((t) => t.kind), ['begin', 'skip', 'end', 'eof']);
  assert.deepEqual(annotations.map((a) => [a.key, a.text]), [
    ['pre', 'X = x ∧ X > 0'],
    ['invariant', 'R = 1'],
  ]);
  assert.deepEqual(annotations[1].span.start, { line: 3, column: 18, offset: 63 });
});

test('unknown annotation key is an error', () => {
  const e = lexError('//@ foo: 1\nbegin skip end');
  assert.equal(e.diagnostic.code, 'E003');
});

test('reports unexpected character with its position', () => {
  const e = lexError('begin X := 1 # end');
  assert.equal(e.diagnostic.code, 'E001');
  assert.deepEqual(e.diagnostic.span.start, { line: 1, column: 14, offset: 13 });
});

test('a lone colon is reported, not silently accepted', () => {
  assert.equal(lexError('begin X : 1 end').diagnostic.code, 'E001');
});
