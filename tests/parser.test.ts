import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parseAssertion, parseProgram } from '../src/parser.js';
import { SiplError } from '../src/span.js';
import type { Program, Stm } from '../src/ast.js';
import { listExamples, readExample, sx } from './helpers.js';

const body = (src: string) => sx(parseProgram(src).body);
const expr = (e: string) => {
  const s = parseProgram(`begin X := ${e} end`).body;
  assert.equal(s.kind, 'assign');
  return sx(s.value);
};
const cond = (c: string) => {
  const s = parseProgram(`begin while ${c} do skip end`).body;
  assert.equal(s.kind, 'while');
  return sx(s.cond);
};

function parseError(src: string): SiplError {
  try {
    parseProgram(src);
  } catch (e) {
    assert.ok(e instanceof SiplError, String(e));
    return e;
  }
  assert.fail('expected a syntax error');
}

test('AST of the practicum power program', () => {
  const src = readExample('power.sipl');
  assert.equal(
    body(src),
    '(; (:= R 1) (WHILE (> Y 0) (BLOCK (; (:= R (* R X)) (:= Y (- Y 1))))))',
  );
  const p = parseProgram(src);
  assert.equal(p.extended, false);
  assert.deepEqual(p.functions, []);
});

test('multiplication binds tighter than addition', () => {
  assert.equal(expr('X + Y * Z'), '(+ X (* Y Z))');
  assert.equal(expr('(X + Y) * Z'), '(* (+ X Y) Z)');
});

test('binary operators are left associative', () => {
  assert.equal(expr('A - B - C'), '(- (- A B) C)');
  assert.equal(expr('A * B * C'), '(* (* A B) C)');
});

test('negative literals', () => {
  assert.equal(expr('-1'), '-1');
  assert.equal(expr('X - -3'), '(- X -3)');
  assert.equal(expr('X -1'), '(- X 1)');
});

test('sequence is left associative and binds loosest', () => {
  assert.equal(body('begin A := 1; B := 2; C := 3 end'), '(; (; (:= A 1) (:= B 2)) (:= C 3))');
  assert.equal(body('begin while X > 0 do X := X - 1; Y := 0 end'), '(; (WHILE (> X 0) (:= X (- X 1))) (:= Y 0))');
  assert.equal(
    body('begin if X > 0 then Y := 1 else Y := 2; Z := 3 end'),
    '(; (IF (> X 0) (:= Y 1) (:= Y 2)) (:= Z 3))',
  );
});

test('negation is weaker than comparison and stronger than disjunction', () => {
  assert.equal(cond('¬ M = N'), '(not (= M N))');
  assert.equal(cond('¬ A > B ∨ C = D'), '(or (not (> A B)) (= C D))');
  assert.equal(cond('A = 1 ∨ B = 2 ∨ C = 3'), '(or (or (= A 1) (= B 2)) (= C 3))');
});

test('parenthesised conditions and parenthesised expressions both parse', () => {
  assert.equal(cond('(X + 1) > 2'), '(> (+ X 1) 2)');
  assert.equal(cond('(X > 1)'), '(> X 1)');
  assert.equal(cond('((X > 1) ∨ (Y = 2))'), '(or (> X 1) (= Y 2))');
  assert.equal(cond('¬(X > 1)'), '(not (> X 1))');
});

test('the GCD program of Example 1.1', () => {
  assert.equal(
    body(readExample('gcd.sipl')),
    '(WHILE (not (= M N)) (IF (> M N) (:= M (- M N)) (:= N (- N M))))',
  );
});

test('node spans point at source text and ids are preorder', () => {
  const src = 'begin\n  R := R * X\nend';
  const p = parseProgram(src);
  const s = p.body;
  assert.equal(s.kind, 'assign');
  assert.equal(src.slice(s.span.start.offset, s.span.end.offset), 'R := R * X');
  assert.equal(src.slice(s.value.span.start.offset, s.value.span.end.offset), 'R * X');
  assert.deepEqual(s.span.start, { line: 2, column: 3, offset: 8 });
  assert.equal(p.id, 0);
  assert.equal(s.id, 1);
  assert.equal(s.value.id, 2);
});

test('semicolon before end', () => {
  const e = parseError('begin\n  X := 1;\nend');
  assert.equal(e.diagnostic.code, 'E100');
  assert.deepEqual(e.diagnostic.span.start, { line: 3, column: 1, offset: 16 });
  assert.match(e.diagnostic.message, /';'/);
  assert.match(e.diagnostic.message, /no empty statement/);
});

test('syntax errors name what was expected', () => {
  const e = parseError('begin X = 1 end');
  assert.equal(e.diagnostic.code, 'E100');
  assert.match(e.diagnostic.message, /expected ':='/);
  assert.match(e.diagnostic.message, /found '='/);
  assert.match(parseError('begin X := 1').diagnostic.message, /end of input/);
});

test('program with function declarations (SIPL-R)', () => {
  const p = parseProgram(readExample('rec-div.sipl'));
  assert.equal(p.extended, true);
  assert.equal(p.functions.length, 1);
  const f = p.functions[0];
  assert.equal(f.name, 'f');
  assert.deepEqual(f.params, ['X', 'Y']);
  assert.equal(sx(f.body), '(if (< X Y) 0 (+ (f (- X Y) Y) 1))');
  assert.equal(sx(p.body), '(:= Q (f A B))');
});

test('declarations are separated by semicolons and the list may be empty', () => {
  const p = parseProgram('program func one = 1; func inc(N) = N + one begin X := inc(one) end');
  assert.deepEqual(p.functions.map((f) => [f.name, f.params]), [['one', []], ['inc', ['N']]]);
  assert.equal(sx(p.body), '(:= X (inc (one)))');
  assert.equal(sx(p.functions[1].body), '(+ N (one))');
  assert.equal(parseProgram('program begin skip end').functions.length, 0);
});

test('a semicolon after the last declaration is explained', () => {
  const e = parseError('program func f = 1; begin X := f end');
  assert.equal(e.diagnostic.code, 'E100');
  assert.match(e.diagnostic.message, /before 'begin'/);
});

test('if-expression else branch extends to the right', () => {
  assert.equal(expr('if X < Y then 0 else F + 1'), '(if (< X Y) 0 (+ F 1))');
  assert.equal(expr('1 + if B > 0 then 2 else 3 * 4'), '(+ 1 (if (> B 0) 2 (* 3 4)))');
});

test('extension constructs mark the program as SIPL-R', () => {
  assert.equal(parseProgram('begin while X < 3 do X := X + 1 end').extended, true);
  assert.equal(parseProgram('begin X := if Y > 0 then 1 else 2 end').extended, true);
  assert.equal(parseProgram('begin X := Y end').extended, false);
});

test('annotations attach to the next while and to the program', () => {
  const src = [
    '//@ pre: X = x ∧ Y = y ∧ Y ≥ 0',
    'begin',
    '  //@ invariant: R * X ^ Y = x ^ y',
    '  //@ variant: Y',
    '  R := 1;',
    '  while Y > 0 do begin R := R * X; Y := Y - 1 end',
    'end',
    '//@ post: R = x ^ y',
  ].join('\n');
  const p: Program = parseProgram(src);
  assert.equal(sx(p.pre!), '(and (and (= X x) (= Y y)) (>= Y 0))');
  assert.equal(sx(p.post!), '(= R (^ x y))');
  const w = (p.body as Extract<Stm, { kind: 'seq' }>).second;
  assert.equal(w.kind, 'while');
  assert.equal(sx(w.invariant!), '(= (* R (^ X Y)) (^ x y))');
  assert.equal(sx(w.variant!), 'Y');
  assert.equal(src.slice(w.invariant!.span.start.offset, w.invariant!.span.end.offset), 'R * X ^ Y = x ^ y');
});

test('an invariant with no following while is an error', () => {
  const e = parseError('begin X := 1 end\n//@ invariant: X = 1');
  assert.equal(e.diagnostic.code, 'E005');
});

test('two invariants for one loop are an error', () => {
  const e = parseError('begin //@ invariant: X = 1\n//@ invariant: X = 2\nwhile X > 0 do X := X - 1 end');
  assert.equal(e.diagnostic.code, 'E004');
});

test('assertion language', () => {
  assert.equal(sx(parseAssertion('A = 1 → B = 1 ∨ C = 1 ∧ ¬D = 1')),
    '(implies (= A 1) (or (= B 1) (and (= C 1) (not (= D 1)))))');
  assert.equal(sx(parseAssertion('M + N', undefined, 'int')), '(+ M N)');
  assert.equal(sx(parseAssertion('X ^ Y ^ 2 = 2 * gcd(M, N) div 3 mod 4')),
    '(= (^ X (^ Y 2)) (mod (div (* 2 (gcd M N)) 3) 4))');
  assert.equal(sx(parseAssertion('true ∧ X ≤ 1 ∧ X ≥ 0 ∧ X ≠ 2')),
    '(and (and (and true (<= X 1)) (>= X 0)) (!= X 2))');
  assert.equal(sx(parseAssertion('A = 1 → B = 1 → C = 1')), '(implies (= A 1) (implies (= B 1) (= C 1)))');
});

test('an annotation with a syntax error reports a position inside the annotation', () => {
  const e = parseError('//@ pre: X >\nbegin skip end');
  assert.equal(e.diagnostic.code, 'E100');
  assert.equal(e.diagnostic.span.start.line, 1);
  assert.equal(e.diagnostic.span.start.column, 13);
});

test('every valid example parses', () => {
  const files = listExamples();
  assert.ok(files.length >= 10, `only ${files.length} valid examples`);
  for (const f of files) assert.doesNotThrow(() => parseProgram(readExample(f)), f);
});

test('every invalid example fails with its expected code and position', () => {
  const files = listExamples('invalid');
  assert.ok(files.length >= 10, `only ${files.length} invalid examples`);
  for (const f of files) {
    const src = readExample(f);
    const m = /^\/\/ expect: (\w+) (\d+):(\d+)/m.exec(src);
    assert.ok(m, `${f} has no '// expect:' line`);
    const e = parseError(src);
    assert.equal(e.diagnostic.code, m[1], f);
    assert.deepEqual([e.diagnostic.span.start.line, e.diagnostic.span.start.column], [Number(m[2]), Number(m[3])], f);
  }
});
