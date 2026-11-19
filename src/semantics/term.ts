import type { Expr, FuncDecl, Node, Program, Stm } from '../ast.js';

/** Names of the replacement rules (Nikitchenko 2020, table 1.6; SIPL-R additions marked). */
export type SemRule =
  | 'NS_Prog'
  | 'NS_Stm_As' | 'NS_Stm_Seq' | 'NS_Stm_If' | 'NS_Stm_Wh' | 'NS_Stm_BE' | 'NS_Stm_skip'
  | 'NS_A_Num' | 'NS_A_Var' | 'NS_A_Add' | 'NS_A_Sub' | 'NS_A_Mult'
  | 'NS_A_If' | 'NS_A_Call' // SIPL-R
  | 'NS_B_eq' | 'NS_B_gr' | 'NS_B_less' | 'NS_B_or' | 'NS_B_neg'
  | 'NS_Func'; // SIPL-R: φ(f) = sem_A(body of f)

/** Operations of the data algebra: add, sub, mult (Int), eq, gr, less (Int² → Bool), or, neg (Bool). */
export type BaseFn = 'add' | 'sub' | 'mult' | 'eq' | 'gr' | 'less' | 'or' | 'neg';

export interface TermRef {
  nodeId: number;
  rule: SemRule;
}

interface TermBase {
  /** The AST node and the rule that produced this term (absent for synthesised terms such as ⊥). */
  ref?: TermRef;
}

/** Terms of the program algebra A_SIPL (and its SIPL-R extension). */
export type Term =
  | (TermBase & { t: 'AS'; variable: string; arg: Term }) // AS^x(fa)
  | (TermBase & { t: 'SEQ'; left: Term; right: Term }) // fs1 · fs2
  | (TermBase & { t: 'IF'; cond: Term; then: Term; else: Term }) // IF(fb, f1, f2)
  | (TermBase & { t: 'WH'; cond: Term; body: Term }) // WH(fb, fs)
  | (TermBase & { t: 'ID' }) // id
  | (TermBase & { t: 'PAREN'; inner: Term }) // (sem_S(S)) of rule NS_Stm_BE
  | (TermBase & { t: 'S'; fn: BaseFn; args: Term[] }) // S^n(f, g1, ..., gn)
  | (TermBase & { t: 'DNM'; variable: string }) // x⇒
  | (TermBase & { t: 'CONST'; value: number }) // n
  | (TermBase & { t: 'CALL'; callee: Term; params: string[]; args: Term[] }) // S^[x1..xn](f, g1..gn)
  | (TermBase & { t: 'FN'; name: string }) // function symbol f
  | (TermBase & { t: 'BOTTOM' }); // ⊥, the nowhere-defined function

const ARITH: Record<string, [BaseFn, SemRule]> = {
  '+': ['add', 'NS_A_Add'],
  '-': ['sub', 'NS_A_Sub'],
  '*': ['mult', 'NS_A_Mult'],
};
const COMPARE: Record<string, [BaseFn, SemRule]> = {
  '=': ['eq', 'NS_B_eq'],
  '>': ['gr', 'NS_B_gr'],
  '<': ['less', 'NS_B_less'],
};

type Params = Map<string, string[]>;

function paramsOf(program: Program): Params {
  return new Map(program.functions.map((f) => [f.name, f.params]));
}

/** sem_P: the semantic term of a program (rule NS_Prog). Calls refer to function symbols. */
export function buildTerm(program: Program): Term {
  return semS(program.body, paramsOf(program));
}

/** φ(f): the term of the body of function `name`, in which recursive calls refer to the symbol f. */
export function buildFunctional(program: Program, name: string): Term {
  const f = program.functions.find((fn) => fn.name === name);
  if (!f) throw new Error(`no function ${name} in the program`);
  return semA(f.body, paramsOf(program));
}

export function semS(s: Stm, params: Params): Term {
  const ref = (rule: SemRule): TermRef => ({ nodeId: s.id, rule });
  switch (s.kind) {
    case 'assign':
      return { t: 'AS', variable: s.target, arg: semA(s.value, params), ref: ref('NS_Stm_As') };
    case 'seq':
      return { t: 'SEQ', left: semS(s.first, params), right: semS(s.second, params), ref: ref('NS_Stm_Seq') };
    case 'if':
      return {
        t: 'IF', cond: semB(s.cond, params), then: semS(s.then, params), else: semS(s.else, params),
        ref: ref('NS_Stm_If'),
      };
    case 'while':
      return { t: 'WH', cond: semB(s.cond, params), body: semS(s.body, params), ref: ref('NS_Stm_Wh') };
    case 'block':
      return { t: 'PAREN', inner: semS(s.body, params), ref: ref('NS_Stm_BE') };
    case 'skip':
      return { t: 'ID', ref: ref('NS_Stm_skip') };
  }
}

export function semA(a: Expr, params: Params): Term {
  switch (a.kind) {
    case 'num':
      return { t: 'CONST', value: a.value, ref: { nodeId: a.id, rule: 'NS_A_Num' } };
    case 'var':
      return { t: 'DNM', variable: a.name, ref: { nodeId: a.id, rule: 'NS_A_Var' } };
    case 'binary': {
      const op = ARITH[a.op];
      if (!op) throw new Error(`operation ${a.op} is not part of SIPL`);
      return { t: 'S', fn: op[0], args: [semA(a.left, params), semA(a.right, params)], ref: { nodeId: a.id, rule: op[1] } };
    }
    case 'cond':
      return {
        t: 'IF', cond: semB(a.cond, params), then: semA(a.then, params), else: semA(a.else, params),
        ref: { nodeId: a.id, rule: 'NS_A_If' },
      };
    case 'call': {
      const ref: TermRef = { nodeId: a.id, rule: 'NS_A_Call' };
      return {
        t: 'CALL', callee: { t: 'FN', name: a.name, ref }, params: params.get(a.name) ?? [],
        args: a.args.map((x) => semA(x, params)), ref,
      };
    }
    default:
      throw new Error(`expected an arithmetic expression, found ${a.kind}`);
  }
}

export function semB(b: Expr, params: Params): Term {
  const ref = (rule: SemRule): TermRef => ({ nodeId: b.id, rule });
  switch (b.kind) {
    case 'compare': {
      const op = COMPARE[b.op];
      if (!op) throw new Error(`comparison ${b.op} is not part of SIPL`);
      return { t: 'S', fn: op[0], args: [semA(b.left, params), semA(b.right, params)], ref: ref(op[1]) };
    }
    case 'logic':
      if (b.op !== 'or') throw new Error(`connective ${b.op} is not part of SIPL`);
      return { t: 'S', fn: 'or', args: [semB(b.left, params), semB(b.right, params)], ref: ref('NS_B_or') };
    case 'not':
      return { t: 'S', fn: 'neg', args: [semB(b.operand, params)], ref: ref('NS_B_neg') };
    default:
      throw new Error(`expected a condition, found ${b.kind}`);
  }
}

// ---- derivation (the sequence of rule applications, as written in the practicum) ----

export interface DerivationStep {
  rule: SemRule;
  nodeId: number;
  /** e.g. `sem_S(R := 1; Y := 2)` */
  lhs: string;
  /** e.g. `sem_S(R := 1) · sem_S(Y := 2)` */
  rhs: string;
}

/** All rule applications that build the term of `program` (functions first, then the body), in preorder. */
export function deriveTerm(program: Program, source: string): DerivationStep[] {
  const text = (n: Node) => source.slice(n.span.start.offset, n.span.end.offset).replace(/\s+/g, ' ').trim();
  const steps: DerivationStep[] = [];
  const params = paramsOf(program);
  const sA = (e: Expr) => `sem_A(${text(e)})`;
  const sB = (e: Expr) => `sem_B(${text(e)})`;
  const sS = (s: Stm) => `sem_S(${text(s)})`;

  const fn = (f: FuncDecl) => {
    steps.push({ rule: 'NS_Func', nodeId: f.id, lhs: `φ(${f.name})`, rhs: sA(f.body) });
    expr(f.body, 'A');
  };
  const stm = (s: Stm): void => {
    const step = (rule: SemRule, rhs: string): void => {
      steps.push({ rule, nodeId: s.id, lhs: sS(s), rhs });
    };
    switch (s.kind) {
      case 'assign':
        step('NS_Stm_As', `AS^${s.target}(${sA(s.value)})`);
        return expr(s.value, 'A');
      case 'seq':
        step('NS_Stm_Seq', `${sS(s.first)} · ${sS(s.second)}`);
        stm(s.first);
        return stm(s.second);
      case 'if':
        step('NS_Stm_If', `IF(${sB(s.cond)}, ${sS(s.then)}, ${sS(s.else)})`);
        expr(s.cond, 'B');
        stm(s.then);
        return stm(s.else);
      case 'while':
        step('NS_Stm_Wh', `WH(${sB(s.cond)}, ${sS(s.body)})`);
        expr(s.cond, 'B');
        return stm(s.body);
      case 'block':
        step('NS_Stm_BE', `(${sS(s.body)})`);
        return stm(s.body);
      case 'skip':
        return step('NS_Stm_skip', 'id');
    }
  };
  const expr = (e: Expr, sort: 'A' | 'B'): void => {
    const lhs = sort === 'A' ? sA(e) : sB(e);
    const step = (rule: SemRule, rhs: string): void => {
      steps.push({ rule, nodeId: e.id, lhs, rhs });
    };
    switch (e.kind) {
      case 'num':
        return step('NS_A_Num', String(e.value));
      case 'var':
        return step('NS_A_Var', `${e.name}⇒`);
      case 'binary':
        step(ARITH[e.op][1], `S^2(${ARITH[e.op][0]}, ${sA(e.left)}, ${sA(e.right)})`);
        expr(e.left, 'A');
        return expr(e.right, 'A');
      case 'compare':
        step(COMPARE[e.op][1], `S^2(${COMPARE[e.op][0]}, ${sA(e.left)}, ${sA(e.right)})`);
        expr(e.left, 'A');
        return expr(e.right, 'A');
      case 'logic':
        step('NS_B_or', `S^2(or, ${sB(e.left)}, ${sB(e.right)})`);
        expr(e.left, 'B');
        return expr(e.right, 'B');
      case 'not':
        step('NS_B_neg', `S^1(neg, ${sB(e.operand)})`);
        return expr(e.operand, 'B');
      case 'cond':
        step('NS_A_If', `IF(${sB(e.cond)}, ${sA(e.then)}, ${sA(e.else)})`);
        expr(e.cond, 'B');
        expr(e.then, 'A');
        return expr(e.else, 'A');
      case 'call': {
        const ps = params.get(e.name) ?? [];
        step('NS_A_Call', e.args.length === 0 ? e.name : `S^[${ps.join(',')}](${e.name}, ${e.args.map(sA).join(', ')})`);
        return e.args.forEach((x) => expr(x, 'A'));
      }
      case 'bool':
        throw new Error('boolean literals are not part of SIPL');
    }
  };

  steps.push({ rule: 'NS_Prog', nodeId: program.id, lhs: `sem_P(${text(program)})`, rhs: sS(program.body) });
  program.functions.forEach(fn);
  stm(program.body);
  return steps;
}
