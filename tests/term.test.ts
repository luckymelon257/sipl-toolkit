import { test } from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { basename, join } from 'node:path';
import { parseProgram } from '../src/parser.js';
import { buildFunctional, buildTerm, deriveTerm, type Term } from '../src/semantics/term.js';
import { printTerm } from '../src/semantics/print.js';
import { ROOT, listExamples, readExample } from './helpers.js';

const term = (src: string) => printTerm(buildTerm(parseProgram(src)));

test('power program gives the practicum term', () => {
  assert.equal(
    term(readExample('power.sipl')),
    'AS^R(1) · WH(S^2(gr, Y⇒, 0), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1)))',
  );
});

test('GCD program gives the term of Example 1.3', () => {
  assert.equal(
    term(readExample('gcd.sipl')),
    'WH(S^1(neg, S^2(eq, M⇒, N⇒)), IF(S^2(gr, M⇒, N⇒), AS^M(S^2(sub, M⇒, N⇒)), AS^N(S^2(sub, N⇒, M⇒))))',
  );
});

test('functional of the practical work 7 division', () => {
  const p = parseProgram(readExample('rec-div.sipl'));
  assert.equal(
    printTerm(buildFunctional(p, 'f')),
    'IF(S^2(less, X⇒, Y⇒), 0, S^2(add, S^[X,Y](f, S^2(sub, X⇒, Y⇒), Y⇒), 1))',
  );
  assert.equal(term(readExample('rec-div.sipl')), 'AS^Q(S^[X,Y](f, A⇒, B⇒))');
});

test('skip, blocks and sequences', () => {
  assert.equal(term('begin skip end'), 'id');
  assert.equal(term('begin begin A := 1; B := 2 end; C := 3 end'), '(AS^A(1) · AS^B(2)) · AS^C(3)');
  assert.equal(term('begin A := 1; B := 2; C := 3 end'), 'AS^A(1) · AS^B(2) · AS^C(3)');
  assert.equal(term('begin A := 1; begin B := 2; C := 3 end end'), 'AS^A(1) · (AS^B(2) · AS^C(3))');
  assert.equal(term('begin A := -1 end'), 'AS^A(-1)');
});

test('zero-argument function call is the function itself', () => {
  const p = parseProgram(readExample('rec-power.sipl'));
  assert.equal(printTerm(buildFunctional(p, 'one')), '1');
  assert.equal(
    printTerm(buildFunctional(p, 'p')),
    'IF(S^2(eq, Y⇒, 0), one, IF(S^2(gr, Y⇒, 1), S^2(mult, S^[X](sq, X⇒), S^[X,Y](p, X⇒, S^2(sub, Y⇒, 2))), X⇒))',
  );
});

test('unknown function name in buildFunctional is an error', () => {
  assert.throws(() => buildFunctional(parseProgram(readExample('rec-div.sipl')), 'g'), /no function g/);
});

test('every term node references the AST node it was built from', () => {
  const p = parseProgram(readExample('power.sipl'));
  const ids = new Set<number>();
  const visit = (t: Term) => {
    assert.ok(t.ref, `${t.t} has no ref`);
    ids.add(t.ref.nodeId);
    for (const c of Object.values(t)) {
      if (c && typeof c === 'object' && 't' in c) visit(c as Term);
      if (Array.isArray(c)) c.forEach(visit);
    }
  };
  visit(buildTerm(p));
  assert.ok(ids.size > 10);
});

test('derivation of the power program follows the course rules', () => {
  const src = readExample('power.sipl');
  const steps = deriveTerm(parseProgram(src), src);
  assert.deepEqual(steps.slice(0, 4).map((s) => s.rule), ['NS_Prog', 'NS_Stm_Seq', 'NS_Stm_As', 'NS_A_Num']);
  assert.equal(steps[1].lhs, 'sem_S(R := 1; while Y > 0 do begin R := R * X; Y := Y - 1 end)');
  assert.equal(steps[1].rhs, 'sem_S(R := 1) · sem_S(while Y > 0 do begin R := R * X; Y := Y - 1 end)');
  assert.deepEqual(
    steps.find((s) => s.rule === 'NS_B_gr'),
    { rule: 'NS_B_gr', nodeId: steps.find((s) => s.rule === 'NS_B_gr')!.nodeId, lhs: 'sem_B(Y > 0)', rhs: 'S^2(gr, sem_A(Y), sem_A(0))' },
  );
  assert.ok(steps.some((s) => s.rule === 'NS_Stm_BE' && s.rhs === '(sem_S(R := R * X; Y := Y - 1))'));
  assert.ok(steps.some((s) => s.rule === 'NS_A_Var' && s.lhs === 'sem_A(X)' && s.rhs === 'X⇒'));
});

test('derivation of a recursive program covers its functions', () => {
  const src = readExample('rec-div.sipl');
  const steps = deriveTerm(parseProgram(src), src);
  const fn = steps.find((s) => s.rule === 'NS_Func')!;
  assert.equal(fn.lhs, 'φ(f)');
  assert.equal(fn.rhs, 'sem_A(if X < Y then 0 else f(X - Y, Y) + 1)');
  assert.ok(steps.some((s) => s.rule === 'NS_A_Call' && s.rhs === 'S^[X,Y](f, sem_A(X - Y), sem_A(Y))'));
  assert.ok(steps.some((s) => s.rule === 'NS_A_If'));
  assert.ok(steps.some((s) => s.rule === 'NS_B_less'));
});

test('every example matches its golden term', () => {
  const dir = join(ROOT, 'tests', 'golden');
  mkdirSync(dir, { recursive: true });
  for (const f of listExamples()) {
    const p = parseProgram(readExample(f));
    const text = [
      printTerm(buildTerm(p)),
      ...p.functions.map((fn) => `φ(${fn.name}) = ${printTerm(buildFunctional(p, fn.name))}`),
    ].join('\n') + '\n';
    const golden = join(dir, basename(f, '.sipl') + '.term.txt');
    if (process.env.UPDATE_GOLDEN) writeFileSync(golden, text);
    assert.ok(existsSync(golden), `missing ${golden}; run with UPDATE_GOLDEN=1`);
    assert.equal(text, readFileSync(golden, 'utf8'), f);
  }
});
