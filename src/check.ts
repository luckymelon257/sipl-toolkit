import type { Expr, Program, Stm } from './ast.js';
import { freeVars, walk } from './ast.js';
import { parseProgram } from './parser.js';
import { Diagnostic, SiplError, SourceSpan, isStackOverflow } from './span.js';

export interface CheckResult {
  ok: boolean;
  diagnostics: Diagnostic[];
  program?: Program;
  /** Variables that may be read before they are assigned: they must be given in the initial state. */
  inputs: string[];
  dialect: 'SIPL' | 'SIPL-R';
}

/** Parses and statically checks a program. Never throws on bad input. */
export function check(source: string): CheckResult {
  try {
    return checkProgram(source);
  } catch (e) {
    if (!isStackOverflow(e)) throw e;
    const start = { line: 1, column: 1, offset: 0 };
    return {
      ok: false, inputs: [], dialect: 'SIPL',
      diagnostics: [diag('error', 'E102', 'the program is too long or nested too deeply for this implementation (call stack exhausted)', { start, end: start })],
    };
  }
}

function checkProgram(source: string): CheckResult {
  let program: Program;
  try {
    program = parseProgram(source);
  } catch (e) {
    if (!(e instanceof SiplError)) throw e;
    return { ok: false, diagnostics: [e.diagnostic], inputs: [], dialect: 'SIPL' };
  }
  const diagnostics = [...checkFunctions(program)];
  const inputs: string[] = [];
  const read = (e: Expr, defined: Set<string>) => {
    for (const n of walk(e)) {
      if (n.kind === 'var' && !defined.has(n.name) && !inputs.includes(n.name)) {
        inputs.push(n.name);
        diagnostics.push(diag('warning', 'W001',
          `variable ${n.name} may be read before it is assigned; give it a value in the initial state`, n.span));
      }
    }
  };
  definitelyAssigned(program.body, new Set(), read);
  diagnostics.sort((a, b) => a.span.start.offset - b.span.start.offset);
  return {
    ok: !diagnostics.some((d) => d.severity === 'error'),
    diagnostics,
    program,
    inputs,
    dialect: program.extended ? 'SIPL-R' : 'SIPL',
  };
}

/** Variables of the program body that may be read before they are assigned (in order of first read). */
export function programInputs(program: Program): string[] {
  const inputs: string[] = [];
  definitelyAssigned(program.body, new Set(), (e, defined) => {
    for (const v of freeVars(e)) if (!defined.has(v) && !inputs.includes(v)) inputs.push(v);
  });
  return inputs;
}

function diag(severity: Diagnostic['severity'], code: string, message: string, span: SourceSpan): Diagnostic {
  return { severity, code, message, span };
}

/** Returns the variables definitely assigned after `s`, reporting reads through `read`. */
function definitelyAssigned(s: Stm, defined: Set<string>, read: (e: Expr, d: Set<string>) => void): Set<string> {
  switch (s.kind) {
    case 'assign':
      read(s.value, defined);
      return new Set([...defined, s.target]);
    case 'seq':
      return definitelyAssigned(s.second, definitelyAssigned(s.first, defined, read), read);
    case 'if': {
      read(s.cond, defined);
      const a = definitelyAssigned(s.then, defined, read);
      const b = definitelyAssigned(s.else, defined, read);
      return new Set([...a].filter((x) => b.has(x)));
    }
    case 'while':
      read(s.cond, defined);
      definitelyAssigned(s.body, defined, read);
      return defined;
    case 'block':
      return definitelyAssigned(s.body, defined, read);
    case 'skip':
      return defined;
  }
}

function checkFunctions(program: Program): Diagnostic[] {
  const out: Diagnostic[] = [];
  const arity = new Map<string, number>();
  for (const f of program.functions) {
    if (arity.has(f.name)) out.push(diag('error', 'E302', `function ${f.name} is declared twice`, f.nameSpan));
    else arity.set(f.name, f.params.length);
    f.params.forEach((p, i) => {
      if (program.functions.some((g) => g.name === p)) {
        out.push(diag('error', 'E305', `parameter ${p} of ${f.name} has the name of a function; rename one of them`, f.paramSpans[i]));
      }
      if (f.params.indexOf(p) !== i) {
        out.push(diag('error', 'E303', `parameter ${p} of ${f.name} is declared twice`, f.paramSpans[i]));
      }
    });
    for (const v of freeVars(f.body)) {
      if (!f.params.includes(v)) {
        out.push(diag('warning', 'W002',
          `function ${f.name} reads ${v}, which is not a parameter; its value comes from the caller's state`, f.nameSpan));
      }
    }
  }
  for (const n of walk(program)) {
    if (n.kind === 'call') {
      const expected = arity.get(n.name);
      if (expected === undefined) {
        out.push(diag('error', 'E300', `unknown function ${n.name}`, n.span));
      } else if (expected !== n.args.length) {
        out.push(diag('error', 'E301',
          `function ${n.name} expects ${expected} argument(s), got ${n.args.length}`, n.span));
      }
    }
    if (n.kind === 'assign' && arity.has(n.target)) {
      out.push(diag('error', 'E304', `cannot assign to ${n.target}: it is a function`, n.targetSpan));
    }
  }
  return out;
}
