#!/usr/bin/env node
import { existsSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import type { Program } from './ast.js';
import { freeVars } from './ast.js';
import { printExpr } from './assertion.js';
import { check } from './check.js';
import { MAX_APPROXIMATION, approximationTerms, applyApproximation, printApproximation } from './fixpoint/approx.js';
import { renderHtml, renderTable } from './fixpoint/render.js';
import { gridStates, testApproximations } from './fixpoint/report.js';
import { parseAssertion } from './parser.js';
import { EvalStep, runProgram } from './semantics/evaluate.js';
import { printTerm } from './semantics/print.js';
import { buildFunctional, buildTerm, deriveTerm } from './semantics/term.js';
import { Diagnostic, SiplError, isStackOverflow } from './span.js';
import { formatState, parseAssignments } from './values.js';
import { verifyProgram } from './verify/verify.js';

const EXIT = { ok: 0, invalid: 1, failed: 2, usage: 64, noInput: 66, internal: 70, cannotWrite: 73 } as const;

const HELP = `SIPL toolkit: parser, semantic terms, least-fixpoint approximations and a correctness assistant.

Usage:
  sipl check <file>                         syntax and static checks; lists the input variables
  sipl run <file> [-s X=5 ...] [--trace]    apply the program's semantic term to a state
  sipl term <file> [--explain]              semantic term (and φ of every function), with the rules applied
  sipl approx <file> [-f NAME] [-k N]       approximations f0 = ⊥, f(i+1) = φ(fi) of a recursive function
         [-s X=7,Y=4] [--explain]           ... applied to one state, with the formulas used
         [--grid X=0..9,Y=1..5]             ... tabulated over a grid of test states
         [--expect EXPR] [--where COND]     ... compared with an expected function, on states satisfying COND
         [--html report.html]               ... and written as an HTML report
  sipl verify <file> [--range -3..8]        check //@ pre/post/invariant/variant annotations

Options:
  -s, --set NAME=VALUE[,...]   initial state (repeatable)
  --max-iterations N           loop iteration budget (run: 100000, verify runs: 10000)
  --max-cases N                states examined per verification condition (default 250000)
  --json                       machine-readable output (schemaVersion 1)
  -h, --help                   this help
  -v, --version                print the version

<file> may be '-' to read standard input.
Exit codes: 0 success; 1 syntax or static error; 2 undefined result, refuted or failed check;
64 usage error; 66 input file cannot be read; 70 internal error; 73 output file cannot be written.`;

class UsageError extends Error {}
class InputError extends Error {}
class OutputError extends Error {}
/** The test setup leaves nothing to check: reported as a failed check (exit 2). */
class EmptyCheckError extends Error {}

interface Out {
  json: boolean;
  file: string;
}

function version(): string {
  for (let dir = dirname(fileURLToPath(import.meta.url)); ; dir = dirname(dir)) {
    const pkg = join(dir, 'package.json');
    if (existsSync(pkg)) return JSON.parse(readFileSync(pkg, 'utf8')).version;
    if (dirname(dir) === dir) return 'unknown';
  }
}

function readSource(file: string): string {
  try {
    return readFileSync(file === '-' ? 0 : file, 'utf8');
  } catch (e) {
    throw new InputError(`cannot read ${file}: ${(e as Error).message}`);
  }
}

function excerpt(source: string, d: Diagnostic): string {
  const lines = source.split(/\r\n|\r|\n/);
  const text = lines[d.span.start.line - 1];
  if (text === undefined) return '';
  const width = String(d.span.start.line).length + 4;
  const length = d.span.end.line === d.span.start.line ? Math.max(1, d.span.end.column - d.span.start.column) : 1;
  return `\n${String(d.span.start.line).padStart(width)} | ${text}\n${' '.repeat(width)} | ${' '.repeat(d.span.start.column - 1)}${'^'.repeat(length)}`;
}

function printDiagnostics(source: string, ds: Diagnostic[], file: string): void {
  for (const d of ds) {
    console.error(`${file}:${d.span.start.line}:${d.span.start.column}: ${d.severity} ${d.code}: ${d.message}${excerpt(source, d)}`);
  }
}

function emit(out: Out, doc: Record<string, unknown>): void {
  if (out.json) console.log(JSON.stringify({ schemaVersion: 1, ...doc }, null, 2));
}

/** Parses and checks; on errors prints them and returns undefined. */
function load(out: Out, command: string): { program: Program; source: string } | undefined {
  const source = readSource(out.file);
  const r = check(source);
  if (r.ok) return { program: r.program!, source };
  if (out.json) emit(out, { command, ok: false, diagnostics: r.diagnostics });
  else printDiagnostics(source, r.diagnostics.filter((d) => d.severity === 'error'), out.file);
  return undefined;
}

function printSteps(steps: EvalStep[], truncated: boolean): void {
  for (const s of steps) console.log(`${'  '.repeat(s.depth)}${s.formula} ${s.term}: ${s.detail}`);
  if (truncated) console.log('... (trace truncated)');
}

function intOption(value: string | undefined, name: string): number | undefined {
  if (value === undefined) return undefined;
  if (!/^\d+$/.test(value)) throw new UsageError(`${name} expects a non-negative integer, got '${value}'`);
  return Number(value);
}

function assertion(text: string | undefined, kind: 'bool' | 'int', name: string) {
  if (text === undefined) return undefined;
  try {
    return parseAssertion(text, undefined, kind);
  } catch (e) {
    if (e instanceof SiplError) throw new UsageError(`${name}: ${e.message}`);
    throw e;
  }
}

function state(sets: string[] | undefined) {
  try {
    return parseAssignments(sets ?? []);
  } catch (e) {
    throw new UsageError((e as Error).message);
  }
}

// ---- commands ----

type Values = ReturnType<typeof parse>['values'];

function cmdCheck(out: Out): number {
  const source = readSource(out.file);
  const r = check(source);
  if (out.json) {
    emit(out, { command: 'check', ok: r.ok, diagnostics: r.diagnostics, dialect: r.dialect, inputs: r.inputs });
    return r.ok ? EXIT.ok : EXIT.invalid;
  }
  printDiagnostics(source, r.diagnostics.filter((d) => d.code !== 'W001'), out.file);
  if (!r.ok) return EXIT.invalid;
  console.log(`${out.file}: ${r.dialect} program is correct`);
  console.log(`inputs: ${r.inputs.length ? r.inputs.join(', ') : '(none)'}`);
  return EXIT.ok;
}

function cmdRun(out: Out, v: Values): number {
  const st = state(v.set);
  const maxIterations = intOption(v['max-iterations'], '--max-iterations');
  const loaded = load(out, 'run');
  if (!loaded) return EXIT.invalid;
  const r = runProgram(loaded.program, st, { maxIterations, record: v.trace });
  if (out.json) {
    emit(out, {
      command: 'run', ok: r.status === 'defined', diagnostics: [],
      result: { status: r.status, input: st, state: r.state, undefined: r.undef, steps: v.trace ? r.steps : undefined },
    });
  } else {
    if (v.trace) printSteps(r.steps, r.truncated);
    if (r.status === 'defined') console.log(`result: ${formatState(r.state!)}`);
    else {
      console.log('result: undefined (↑)');
      console.error(`${out.file}: ${r.undef!.reason}: ${r.undef!.message}`);
    }
  }
  return r.status === 'defined' ? EXIT.ok : EXIT.failed;
}

function cmdTerm(out: Out, v: Values): number {
  const loaded = load(out, 'term');
  if (!loaded) return EXIT.invalid;
  const { program, source } = loaded;
  const term = printTerm(buildTerm(program));
  const functions = Object.fromEntries(program.functions.map((f) => [f.name, printTerm(buildFunctional(program, f.name))]));
  const derivation = v.explain ? deriveTerm(program, source) : undefined;
  if (out.json) {
    emit(out, { command: 'term', ok: true, diagnostics: [], term, functions, derivation });
    return EXIT.ok;
  }
  if (derivation) for (const s of derivation) console.log(`[${s.rule}] ${s.lhs} = ${s.rhs}`);
  for (const [name, phi] of Object.entries(functions)) console.log(`φ(${name}) = ${phi}`);
  console.log(`sem_P = ${term}`);
  return EXIT.ok;
}

function cmdApprox(out: Out, v: Values): number {
  const k = intOption(v.k, '-k') ?? 3;
  const st = v.set ? state(v.set) : undefined;
  const grid = v.grid === undefined ? undefined : (() => {
    try {
      return gridStates(v.grid);
    } catch (e) {
      throw new UsageError((e as Error).message);
    }
  })();
  const expect = assertion(v.expect, 'int', '--expect');
  const where = assertion(v.where, 'bool', '--where');
  if (v.html && !grid) throw new UsageError('--html needs --grid');
  const loaded = load(out, 'approx');
  if (!loaded) return EXIT.invalid;
  const { program } = loaded;
  const names = program.functions.map((f) => f.name);
  if (names.length === 0) throw new UsageError('the program declares no functions (approximations need a SIPL-R program)');
  const name = v.function ?? (names.length === 1 ? names[0] : undefined);
  if (!name) throw new UsageError(`the program declares several functions (${names.join(', ')}); choose one with --function`);
  if (!names.includes(name)) throw new UsageError(`no function ${name}; declared: ${names.join(', ')}`);

  if (k > MAX_APPROXIMATION) throw new UsageError(`-k must be at most ${MAX_APPROXIMATION}`);

  // Every variable the function reads must get a value, or the whole table would be ⊥ for a trivial reason.
  const fn = program.functions.find((f) => f.name === name)!;
  const needed = [...new Set([...fn.params, ...freeVars(fn.body)])];
  const given = new Set(grid ? Object.keys(grid[0]) : st ? Object.keys(st) : needed);
  const missing = needed.filter((x) => !given.has(x));
  if (missing.length) {
    throw new UsageError(`${name} reads ${missing.join(', ')}; give ${missing.length > 1 ? 'them' : 'it'} values in ${grid ? '--grid' : '-s'}`);
  }
  for (const [flag, e] of [['--expect', expect], ['--where', where]] as const) {
    const unknown = e ? freeVars(e).filter((x) => !given.has(x)) : [];
    if (unknown.length) throw new UsageError(`${flag} uses ${unknown.join(', ')}, which ${grid ? '--grid' : '-s'} does not define`);
  }

  const chain = approximationTerms(program, name, k);
  const terms = chain.map((_, i) => printApproximation(chain, i, name));
  const values = st
    ? chain.map((_, i) => applyApproximation(program, name, i, st, { record: Boolean(v.explain) && i === k }))
    : undefined;
  const report = grid ? testApproximations(program, name, { k, states: grid, expect, where, expectText: v.expect }) : undefined;
  if (report && report.rows.length === 0) throw new EmptyCheckError('no test states left after --where');
  if (report && expect && !report.rows.some((r) => r.firstDefined !== null && r.expected !== null)) {
    throw new EmptyCheckError('nothing to compare: no test state has both a defined approximation and a defined --expect value');
  }
  if (report && v.html) {
    try {
      writeFileSync(v.html, renderHtml(report));
    } catch (e) {
      throw new OutputError(`cannot write ${v.html}: ${(e as Error).message}`);
    }
  }
  const ok = !report || (report.checks.monotone && report.checks.mismatches.length === 0);

  if (out.json) {
    emit(out, {
      command: 'approx', ok, diagnostics: [], function: name, k, terms,
      values: values?.map((r, i) => ({ k: i, value: r.ok ? r.value : null, undefined: r.ok ? undefined : r.undef })),
      report: report && { rows: report.rows, checks: report.checks, definedCount: report.table.definedCount },
    });
    return ok ? EXIT.ok : EXIT.failed;
  }
  if (report) process.stdout.write(renderTable(report));
  else terms.forEach((t, i) => console.log(`${name}${i} = ${t}`));
  if (values && st) {
    console.log('');
    values.forEach((r, i) => console.log(`${name}${i}(${formatState(st)}) = ${r.ok ? r.value : `⊥ (${r.undef.message})`}`));
    if (v.explain) {
      console.log(`\nApplying ${name}${k} to ${formatState(st)}:`);
      printSteps(values[k].steps, values[k].truncated);
    }
  }
  if (v.html) console.log(`\nHTML report written to ${v.html}`);
  return ok ? EXIT.ok : EXIT.failed;
}

function cmdVerify(out: Out, v: Values): number {
  let range: [number, number] | undefined;
  if (v.range !== undefined) {
    const m = /^(-?\d+)\.\.(-?\d+)$/.exec(v.range);
    if (!m || Number(m[2]) < Number(m[1])) throw new UsageError(`--range expects LO..HI, got '${v.range}'`);
    range = [Number(m[1]), Number(m[2])];
  }
  const maxCases = intOption(v['max-cases'], '--max-cases');
  if (maxCases === 0) throw new UsageError('--max-cases must be at least 1');
  const maxIterations = intOption(v['max-iterations'], '--max-iterations');
  const loaded = load(out, 'verify');
  if (!loaded) return EXIT.invalid;
  const r = verifyProgram(loaded.program, { range, maxCases, maxIterations });
  const ok = r.verdict.startsWith('checked');
  const errors = r.diagnostics.filter((d) => d.severity === 'error');
  const vcs = r.vcs.map((vc) => ({
    id: vc.id, kind: vc.kind, title: vc.title, loopId: vc.loop?.id,
    hypothesis: printExpr(vc.hypothesis), goal: printExpr(vc.goal), derivation: vc.derivation, result: vc.result,
  }));
  if (out.json) {
    emit(out, {
      command: 'verify', ok, diagnostics: r.diagnostics,
      report: { verdict: r.verdict, total: r.total, range: r.range, summary: r.summary, vcs, runs: r.runs },
    });
    return ok ? EXIT.ok : errors.length ? EXIT.invalid : EXIT.failed;
  }
  printDiagnostics(loaded.source, r.diagnostics, out.file);
  if (errors.length) return EXIT.invalid;
  for (const vc of vcs) {
    console.log(`VC ${vc.id} [${vc.kind}] ${vc.title}`);
    console.log(`  ${vc.hypothesis}  →  ${vc.goal}`);
    for (const line of vc.derivation) console.log(`    ${line}`);
    const res = vc.result;
    if (res.status === 'checked') {
      console.log(`  checked: ${res.cases} states (${res.mode}), hypothesis true in ${res.relevant}${res.relevant === 0 ? ' (vacuous!)' : ''}`);
    } else {
      console.log(`  FAILS: counterexample: ${formatState(res.counterexample)}, the goal is ${res.goalValue}` +
        (res.afterBody ? `; after one iteration: ${formatState(res.afterBody)}` : ''));
    }
    console.log('');
  }
  console.log(`Runs: ${r.runs.count} execution(s) from states satisfying the precondition (${r.runs.mode})` +
    (r.runs.inconclusive ? `, ${r.runs.inconclusive} did not finish within the iteration budget` : ''));
  for (const viol of r.runs.violations) console.log(`  ${viol.kind} violated from ${formatState(viol.input)}: ${viol.message}`);
  console.log(`\n${r.summary}`);
  return ok ? EXIT.ok : EXIT.failed;
}

function parse(argv: string[]) {
  return parseArgs({
    args: argv,
    allowPositionals: true,
    strict: true,
    options: {
      set: { type: 'string', short: 's', multiple: true },
      json: { type: 'boolean' },
      trace: { type: 'boolean' },
      explain: { type: 'boolean' },
      function: { type: 'string', short: 'f' },
      k: { type: 'string', short: 'k' },
      grid: { type: 'string' },
      expect: { type: 'string' },
      where: { type: 'string' },
      html: { type: 'string' },
      range: { type: 'string' },
      'max-iterations': { type: 'string' },
      'max-cases': { type: 'string' },
      help: { type: 'boolean', short: 'h' },
      version: { type: 'boolean', short: 'v' },
    },
  });
}

const VALUE_OPTIONS = new Set(['--set', '-s', '-f', '--function', '-k', '--grid', '--expect', '--where', '--html', '--range', '--max-iterations', '--max-cases']);

/** `--range -3..8`: parseArgs would read `-3..8` as an option, so glue such values to their option. */
function glueNegativeValues(argv: string[]): string[] {
  const out: string[] = [];
  for (let i = 0; i < argv.length; i++) {
    if (VALUE_OPTIONS.has(argv[i]) && /^-\d/.test(argv[i + 1] ?? '')) out.push(`${argv[i].startsWith('--') ? argv[i] + '=' : argv[i]}${argv[++i]}`);
    else out.push(argv[i]);
  }
  return out;
}

export function main(argv: string[]): number {
  let parsed: ReturnType<typeof parse>;
  try {
    parsed = parse(glueNegativeValues(argv));
  } catch (e) {
    console.error(`sipl: ${(e as Error).message}\nRun 'sipl --help' for usage.`);
    return EXIT.usage;
  }
  const { values, positionals } = parsed;
  if (values.help) {
    console.log(HELP);
    return EXIT.ok;
  }
  if (values.version) {
    console.log(version());
    return EXIT.ok;
  }
  const [command, file, ...extra] = positionals;
  const commands: Record<string, (out: Out, v: Values) => number> = {
    check: cmdCheck, run: cmdRun, term: cmdTerm, approx: cmdApprox, verify: cmdVerify,
  };
  try {
    if (!command) throw new UsageError('missing command');
    if (!commands[command]) throw new UsageError(`unknown command '${command}'`);
    if (!file) throw new UsageError(`'sipl ${command}' needs a file (or '-' for standard input)`);
    if (extra.length) throw new UsageError(`unexpected argument '${extra[0]}'`);
    return commands[command]({ json: Boolean(values.json), file }, values);
  } catch (e) {
    if (e instanceof UsageError) {
      console.error(`sipl: ${e.message}\nRun 'sipl --help' for usage.`);
      return EXIT.usage;
    }
    if (e instanceof InputError) {
      console.error(`sipl: ${e.message}`);
      return EXIT.noInput;
    }
    if (e instanceof OutputError) {
      console.error(`sipl: ${e.message}`);
      return EXIT.cannotWrite;
    }
    if (e instanceof EmptyCheckError) {
      console.error(`sipl: ${e.message}`);
      return EXIT.failed;
    }
    if (isStackOverflow(e)) {
      console.error('sipl: the input is too large or nested too deeply for this implementation (call stack exhausted)');
      return EXIT.failed;
    }
    console.error(`sipl: internal error: ${(e as Error).message}`);
    return EXIT.internal;
  }
}

process.exitCode = main(process.argv.slice(2));
