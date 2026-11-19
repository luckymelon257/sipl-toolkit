import { test } from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdtempSync, readFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { ROOT } from './helpers.js';

const CLI = join(ROOT, '.test-build', 'src', 'cli.js');
const ex = (name: string) => join(ROOT, 'examples', name);

function sipl(args: string[], input?: string) {
  const r = spawnSync(process.execPath, [CLI, ...args], { input, encoding: 'utf8' });
  return { code: r.status, out: r.stdout, err: r.stderr };
}
const json = (args: string[]) => {
  const r = sipl([...args, '--json']);
  return { code: r.code, doc: JSON.parse(r.out) };
};

test('--help and --version', () => {
  const h = sipl(['--help']);
  assert.equal(h.code, 0);
  for (const cmd of ['check', 'run', 'term', 'approx', 'verify']) assert.match(h.out, new RegExp(`sipl ${cmd}`));
  const v = sipl(['--version']);
  assert.equal(v.out.trim(), JSON.parse(readFileSync(join(ROOT, 'package.json'), 'utf8')).version);
});

test('check: ok program lists its inputs', () => {
  const r = sipl(['check', ex('power.sipl')]);
  assert.equal(r.code, 0);
  assert.match(r.out, /SIPL program is correct/);
  assert.match(r.out, /inputs: Y, X/);
});

test('check: syntax error exits 1 with file:line:col and a caret', () => {
  const r = sipl(['check', ex('invalid/semicolon-before-end.sipl')]);
  assert.equal(r.code, 1);
  assert.match(r.err, /semicolon-before-end\.sipl:4:1: error E100: unexpected 'end' after ';'/);
  assert.match(r.err, /\n +4 \| end\n +\| \^\^\^/);
});

test('run: power with -s X=5 -s Y=2', () => {
  const r = sipl(['run', ex('power.sipl'), '-s', 'X=5', '-s', 'Y=2']);
  assert.equal(r.code, 0);
  assert.match(r.out, /\[X ↦ 5, Y ↦ 0, R ↦ 25\]/);
});

test('run --trace shows the applied formulas', () => {
  const r = sipl(['run', ex('power.sipl'), '-s', 'X=5,Y=2', '--trace']);
  assert.match(r.out, /AF_WH .*st2 = \[X ↦ 5, Y ↦ 0, R ↦ 25\]/);
});

test('run: missing input is undefined and exits 2', () => {
  const r = sipl(['run', ex('power.sipl'), '-s', 'X=5']);
  assert.equal(r.code, 2);
  assert.match(r.out + r.err, /undefined/);
  assert.match(r.err, /Y/);
});

test('run: non-terminating loop exits 2 with the iteration limit', () => {
  const r = sipl(['run', '-', '--max-iterations', '100'], 'begin while 1 = 1 do skip end');
  assert.equal(r.code, 2);
  assert.match(r.err, /100 iterations/);
});

test('term and --explain', () => {
  const r = sipl(['term', ex('rec-div.sipl'), '--explain']);
  assert.equal(r.code, 0);
  assert.match(r.out, /φ\(f\) = IF\(S\^2\(less, X⇒, Y⇒\), 0, S\^2\(add, S\^\[X,Y\]\(f, S\^2\(sub, X⇒, Y⇒\), Y⇒\), 1\)\)/);
  assert.match(r.out, /NS_Stm_As/);
});

test('approx: terms, values on a state and explanation', () => {
  const r = sipl(['approx', ex('rec-div.sipl'), '-k', '2', '-s', 'X=7,Y=4', '--explain']);
  assert.equal(r.code, 0);
  assert.match(r.out, /f1 = IF\(S\^2\(less, X⇒, Y⇒\), 0, ⊥\)/);
  assert.match(r.out, /f0\(\[X ↦ 7, Y ↦ 4\]\) = ⊥/);
  assert.match(r.out, /f2\(\[X ↦ 7, Y ↦ 4\]\) = 1/);
  assert.match(r.out, /AF_CALL/);
});

test('approx: grid with expected function and html report', () => {
  const dir = mkdtempSync(join(tmpdir(), 'sipl-'));
  const html = join(dir, 'report.html');
  const r = sipl(['approx', ex('rec-div.sipl'), '-k', '4', '--grid', 'X=0..9,Y=1..3', '--expect', 'X div Y', '--html', html]);
  assert.equal(r.code, 0, r.err);
  assert.match(r.out, /monotone: yes/);
  assert.match(readFileSync(html, 'utf8'), /<rect class="cell"/);
});

test('approx: a wrong expected function exits 2', () => {
  const r = sipl(['approx', ex('rec-div.sipl'), '--grid', 'X=0..3,Y=2', '--expect', 'X div Y + 1']);
  assert.equal(r.code, 2);
  assert.match(r.out, /MISMATCH/);
});

test('approx: function must be named when there are several', () => {
  const r = sipl(['approx', ex('rec-power.sipl')]);
  assert.equal(r.code, 64);
  assert.match(r.err, /--function/);
});

test('verify: verified, refuted and unproven programs', () => {
  const ok = sipl(['verify', ex('verify/power.sipl')]);
  assert.equal(ok.code, 0, ok.out + ok.err);
  assert.match(ok.out, /checked: .*exhaustive/);
  assert.match(ok.out, /total correctness/);
  const bad = sipl(['verify', ex('verify/wrong-invariant.sipl')]);
  assert.equal(bad.code, 2);
  assert.match(bad.out, /counterexample: \[/);
  assert.match(bad.out, /REFUTED/);
  const weak = sipl(['verify', ex('verify/not-inductive.sipl')]);
  assert.equal(weak.code, 2);
  assert.match(weak.out, /after one iteration: \[X ↦ 5\]/);
});

test('verify: custom range', () => {
  const r = json(['verify', ex('verify/isqrt.sipl'), '--range', '0..20']);
  assert.equal(r.code, 0);
  assert.deepEqual(r.doc.report.range, [0, 20]);
});

test('JSON documents carry schemaVersion, command and ok', () => {
  const docs = [
    json(['check', ex('gcd.sipl')]),
    json(['run', ex('gcd.sipl'), '-s', 'M=8,N=16']),
    json(['term', ex('gcd.sipl')]),
    json(['approx', ex('rec-div.sipl'), '--grid', 'X=0..3,Y=1..2']),
    json(['verify', ex('verify/gcd.sipl')]),
    json(['check', ex('invalid/div-operator.sipl')]),
  ];
  for (const { doc } of docs) {
    assert.equal(doc.schemaVersion, 1);
    assert.equal(typeof doc.command, 'string');
    assert.equal(typeof doc.ok, 'boolean');
    assert.ok(Array.isArray(doc.diagnostics));
  }
  assert.deepEqual(docs[1].doc.result.state, { M: 8, N: 8 });
  assert.equal(docs[2].doc.term, 'WH(S^1(neg, S^2(eq, M⇒, N⇒)), IF(S^2(gr, M⇒, N⇒), AS^M(S^2(sub, M⇒, N⇒)), AS^N(S^2(sub, N⇒, M⇒))))');
  assert.equal(docs[5].code, 1);
  assert.equal(docs[5].doc.diagnostics[0].code, 'E002');
});

test('usage errors exit 64, unreadable files exit 66', () => {
  assert.equal(sipl([]).code, 64);
  assert.equal(sipl(['frobnicate', ex('power.sipl')]).code, 64);
  assert.equal(sipl(['run', ex('power.sipl'), '--no-such-flag']).code, 64);
  assert.equal(sipl(['run', ex('power.sipl'), '-s', 'X=five']).code, 64);
  assert.equal(sipl(['approx', ex('rec-div.sipl'), '--grid', 'X=9..1']).code, 64);
  assert.equal(sipl(['check']).code, 64);
  const missing = sipl(['check', ex('no-such-file.sipl')]);
  assert.equal(missing.code, 66);
  assert.match(missing.err, /cannot read/);
});

test('stdin input with -', () => {
  const r = sipl(['run', '-', '-s', 'A=3,B=9'], readFileSync(ex('max.sipl'), 'utf8'));
  assert.equal(r.code, 0);
  assert.match(r.out, /M ↦ 9/);
});
