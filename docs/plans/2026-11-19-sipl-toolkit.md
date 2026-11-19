# SIPL Correctness & Fixpoint Toolkit Implementation Plan

**Goal:** Node.js/TypeScript toolkit for SIPL and its recursive extension SIPL-R: parser with typed AST, semantic terms, recursive functions with least-fixpoint approximations, approximation testing with visualization, and a correctness assistant for loop programs.

**Architecture:** One library package (`sipl-toolkit`). Hand-written lexer and recursive-descent parser build a typed AST with source spans. The semantic layer turns the AST into course-notation terms; a single term evaluator is the runtime (programs run by applying their semantic term to a state). Approximations f0 = ⊥, f1 = φ(f0), … reuse the same evaluator with a bounded unfolding level. The verifier generates verification conditions by weakest precondition over the AST and checks them by bounded search and by running the program. The CLI is a thin client of the library.

**Tech Stack:** Node.js ≥ 20, TypeScript (strict, ES2022, NodeNext), `node:test` + `c8`, `node:util.parseArgs`, ESLint (`typescript-eslint`). No runtime dependencies.

**Spec:** `TP_course_project_2026.pdf`; practicum «Теорія програмування. Практикум» (2024): ПР 1–3, ПР 7; Нікітченко М.С. «Теорія програмування» (2020): §1.1–1.4, §5.7.3.

## Selected tasks (claimed 12.5, graded max 10)

| ID | Points | Delivered by |
|----|--------|--------------|
| CORE-02 | 1.5 | Tasks 1–2 |
| SEM-01 | 2.0 | Task 3 |
| REC-01 | 2.0 | Tasks 2, 4 |
| REC-02 | 2.5 | Task 5 |
| REC-03 | 1.5 | Task 6 |
| SEM-04 | 2.5 | Task 7 |
| REL-01 | 0.5 | Task 9 |

## Global Constraints

- Base SIPL = course BNF (Нікітченко, табл. 1.2). Priority high→low: `*`; `+ -`; `= >`; `¬`; `∨`; `:=`; `while`; `if`; `;`. All binary operators left-associative.
- SIPL-R = base + Нікітченко табл. 5.1/5.2: `P ::= program dec1; …; decn begin S end`, `dec ::= func fn = a | func fn(x1, …, xn) = a`, `a ::= … | if b then a1 else a2 | fn | fn(a1, …, an)`, plus comparison `<` (`less`, used by ПР 7 examples). `if … then … else` in an expression extends as far right as possible.
- Call semantics = local superposition: `S^[x1,…,xn](f, g1, …, gn)(st) = f(st ∇ [x1 ↦ g1(st), …, xn ↦ gn(st)])`.
- Assertion language (verifier only) = conditions plus `∧ and`, `→ =>`, `< ≤ <= ≥ >= ≠ !=`, `^`, `div`, `mod`, `gcd(a, b)`, `abs(a)`; names that occur only in annotations are ghost (logical) variables, constant during execution.
- Integers are JS numbers; any result outside `Number.isSafeInteger` makes the value undefined with reason `overflow`.
- Positions: line/column 1-based, offset 0-based, span end exclusive; `\r\n` is one line break.
- Term notation: `AS^R(1) · WH(S^2(gr, Y⇒, 0), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1)))`; `⊥` for the nowhere-defined function; states `[X ↦ 5, Y ↦ 2]`.
- Conventional Commits.

## Review Focus

1. Practicum variants with `div`/`mod` in a program → `E002` saying these are not SIPL operators (Task 1 test `rejects div and mod in programs`).
2. `;` directly before `end` → `E100` at `end` explaining SIPL has no empty statement (Task 2 test `semicolon before end`).
3. Recursion that never reaches a base case (`func f(X) = f(X + 1)`) → `undefined` with reason `call-depth`, never a JS stack overflow (Task 4 test `runaway recursion is reported, not thrown`).
4. Invariant that holds on reachable states but is not inductive → VC refuted with a counterexample marked "not reachable from pre in bounds" so the user is not told the program is wrong (Task 7 test `non-inductive invariant`).
5. Approximation grid with an input where the expected function is itself undefined (e.g. `X div Y` with `Y = 0`) → cell marked `n/a`, not a failure (Task 6 test `expected undefined is not a mismatch`).

---

### Task 1: Scaffold, spans, lexer

**Files:** `package.json`, `tsconfig.json`, `tsconfig.build.json`, `eslint.config.js`, `.gitignore`, `src/span.ts`, `src/lexer.ts`, `tests/lexer.test.ts`

**Produces:**
- `Position { line; column; offset }`, `SourceSpan { start; end }`, `Diagnostic { severity: 'error'|'warning'|'info'; code; message; span }`, `class SiplError extends Error { diagnostic }`
- `TokenKind`: keywords `begin end if then else while do skip program func`, `ident`, `number`, `:= ; , + - * ( ) = > < or not and implies <= >= != ^ div mod`, `eof`
- `Token { kind; text; span }`; `Annotation { key: 'pre'|'post'|'invariant'|'variant'; text: string; span }` (from `//@ key: text` comments)
- `tokenize(source: string, mode: 'program'|'assertion' = 'program'): { tokens: Token[]; annotations: Annotation[] }`

Unicode aliases: `∨`→or, `¬`→not, `∧`→and, `→`→implies, `≤ ≥ ≠`, `– −`→`-`, `∗ ×`→`*`. In `program` mode `and implies <= >= != ^ div mod` raise `E002` naming the operator; unknown char `E001`.

- [ ] Tests: `tokenizes the power program`, `maps Unicode operators`, `CRLF positions`, `rejects div and mod in programs`, `assertion mode accepts ∧ ≤ ^ div`, `collects //@ annotations`, `unexpected character position`.
- [ ] Watch fail → implement → pass → commit `chore: scaffold project and add SIPL lexer`.

### Task 2: Grammar, parser, AST, static check (CORE-02, REC-01 syntax)

**Files:** `grammar/sipl.ebnf`, `grammar/sipl-r.ebnf`, `grammar/assertions.ebnf`, `src/ast.ts`, `src/parser.ts`, `src/check.ts`, `examples/*.sipl`, `examples/invalid/*.sipl`, `tests/parser.test.ts`, `tests/check.test.ts`

**Produces (every node has `id: number` (preorder) and `span`):**
- `Program { kind: 'program'; functions: FuncDecl[]; body: Stm; extended: boolean; annotations: Annotation[] }`
- `FuncDecl { kind: 'func'; name; params: string[]; body: Aexp }`
- `Stm = Assign{target, value} | Seq{first, second} | If{cond, then, else} | While{cond, body, invariant?: Expr, variant?: Expr} | Block{body} | Skip`
- `Expr` (shared by programs and assertions) `= Num{value} | Var{name} | Binary{op: '+'|'-'|'*'|'^'|'div'|'mod'; left; right} | Cond{cond, then, else} | Call{name, args} | Compare{op: '='|'>'|'<'|'>='|'<='|'!='; left; right} | Logic{op: 'or'|'and'|'implies'; left; right} | Not{operand} | BoolLit{value}`
- `parseProgram(source: string): Program` (throws `SiplError`); `parseAssertion(text: string, offsetSpan?: SourceSpan): Expr`
- `check(source: string): CheckResult { ok; diagnostics; program?; inputs: string[]; dialect: 'SIPL'|'SIPL-R' }` never throws.

Rules: `//@ invariant`/`//@ variant` attach to the next `while`; `pre`/`post` stay program-level. Check diagnostics: `E300` unknown function, `E301` arity mismatch, `E302` duplicate function, `E303` duplicate parameter, `E304` assignment to a function name, `W001` variable may be read before assignment. Conditions in `(`: try `aexp cmp aexp`, backtrack to `( b )`.

- [ ] Tests: `power program AST`, `X + Y * Z precedence`, `left associativity`, `while b do S1; S2 is a sequence`, `¬ M = N`, `parenthesised condition backtracking`, `semicolon before end`, `program with func declarations`, `if-expression else extends right`, `annotations attach to while`, examples dir: every valid parses, every invalid fails with its `// expect: CODE line:col`; check: `E300`–`E304`, `W001`, `dialect detection`.
- [ ] ≥ 10 valid examples (power, GCD, factorial loop, sum 2..2n, Fibonacci, parity, isqrt, rec div, rec factorial, rec gcd, rec fib, rec power) and ≥ 10 invalid.
- [ ] Commit `feat: add SIPL and SIPL-R grammars, parser with typed AST and static check`.

### Task 3: Semantic terms (SEM-01)

**Files:** `src/semantics/term.ts`, `src/semantics/print.ts`, `tests/term.test.ts`, `tests/golden/*.term.txt`

**Produces:**
- `SemRule` = `NS_Prog | NS_Stm_As | NS_Stm_Seq | NS_Stm_If | NS_Stm_Wh | NS_Stm_BE | NS_Stm_skip | NS_A_Num | NS_A_Var | NS_A_Add | NS_A_Sub | NS_A_Mult | NS_A_Par | NS_A_If | NS_A_Call | NS_B_eq | NS_B_gr | NS_B_less | NS_B_or | NS_B_neg | NS_B_Par`
- `Term = AS{variable, arg} | SEQ{left, right} | IF{cond, then, else} | WH{cond, body} | ID | PAREN{inner} | S{fn: 'add'|'sub'|'mult'|'eq'|'gr'|'less'|'or'|'neg', args} | DNM{variable} | CONST{value} | CALL{fn: string, params: string[], args: Term[]} | FN{name} | BOTTOM`; every node has `ref?: { nodeId; rule }`.
- `buildTerm(program): Term`; `buildFunctional(program, fnName): Term` (φ body with recursive calls as `FN`); `deriveTerm(program, source): DerivationStep[] { rule; nodeId; lhs; rhs }`; `printTerm(term): string`.

- [ ] Golden: power = `AS^R(1) · WH(S^2(gr, Y⇒, 0), AS^R(S^2(mult, R⇒, X⇒)) · AS^Y(S^2(sub, Y⇒, 1)))`; GCD = `WH(S^1(neg, S^2(eq, M⇒, N⇒)), IF(S^2(gr, M⇒, N⇒), AS^M(S^2(sub, M⇒, N⇒)), AS^N(S^2(sub, N⇒, M⇒))))`; φ of ПР 7 div = `IF(S^2(less, X⇒, Y⇒), 0, S^2(add, S^[X,Y](f, S^2(sub, X⇒, Y⇒), Y⇒), 1))`; every example matches its golden file; derivation begins `NS_Prog`.
- [ ] Commit `feat: build semantic terms and functionals with derivation steps`.

### Task 4: Term evaluator and runtime (REC-01 runtime)

**Files:** `src/values.ts`, `src/semantics/evaluate.ts`, `tests/evaluate.test.ts`

**Produces:**
- `State = Record<string, number>`; `formatState(s): string`; `parseAssignments(list: string[]): State`
- `Env = Record<string, { params: string[]; body: Term }>`; `envOf(program): Env`
- `EvalOptions { level?: number (unfolding budget; Infinity = least fixpoint); maxIterations?: number (100000); maxCallDepth?: number (1000); record?: boolean; maxSteps?: number (5000) }`
- `EvalStep { formula: 'AF_S'|'AF_AS'|'AF_SEQ'|'AF_IF'|'AF_WH'|'AF_DNM'|'AF_ID'|'AF_CONST'|'AF_CALL'|'AF_BOT'; depth; term; detail }`
- `Undefined { reason: 'unbound-variable'|'overflow'|'iteration-limit'|'call-depth'|'bottom'; message }`
- `evalState(term, st, env, opts): { ok: true; state } | { ok: false; undef }` plus `evalValue(term, st, env, opts)`; `runProgram(program, st, opts): RunResult { status: 'defined'|'undefined'; state?; undef?; steps: EvalStep[]; truncated }`

Calls at `level` k evaluate the callee body at level k−1; level 0 call → `bottom`. Undefinedness propagates (Нікітченко, зауваження 1.6).

- [ ] Tests: `power on [X ↦ 5, Y ↦ 2]`, `GCD on [M ↦ 8, N ↦ 16]`, `rec div 7 ÷ 4 = 1`, `rec factorial 5 = 120`, `unbound variable`, `WH iteration-limit`, `runaway recursion is reported, not thrown`, `level 2 of div is undefined on [X ↦ 9, Y ↦ 4]`, `steps record AF_WH with states`, every valid example runs with its documented input.
- [ ] Commit `feat: evaluate semantic terms with recursion and partiality`.

### Task 5: Approximation chain (REC-02)

**Files:** `src/fixpoint/approx.ts`, `tests/approx.test.ts`

**Produces:**
- `approximationTerms(program, fnName, k): Term[]` — `f0 = BOTTOM`, `f(i+1) = simplify(φ[f ↦ fi])`; `simplify` applies strictness: `S(…⊥…) = ⊥`, `S^[…](⊥, …) = ⊥`, `IF(b, ⊥, ⊥) = ⊥`.
- `applyApproximation(program, fnName, k, st): { value?: number; undef?: Undefined; steps }` (evaluation at level k)
- `describeApproximations(program, fnName, k, states: State[]): ApproxTable { fn; k; rows: { state; values: (number|null)[]; firstDefined: number|null }[] }`

- [ ] Tests: ПР 7 `f1 = IF(S^2(less, X⇒, Y⇒), 0, ⊥)`; `f2` matches the practicum inlined form; `f2([X ↦ 7, Y ↦ 4]) = 1`, `f1` undefined there; factorial `f_k` defined exactly for `N ≤ k` (Нікітченко приклад 5.1); `monotone: defined values never change with k`.
- [ ] Commit `feat: build and apply least-fixpoint approximations`.

### Task 6: Approximation testing and visualization (REC-03)

**Files:** `src/fixpoint/report.ts`, `src/fixpoint/render.ts`, `tests/report.test.ts`

**Produces:**
- `gridStates(spec: string): State[]` (`'X=0..9,Y=1..5'`)
- `testApproximations(program, fnName, { k, states, expect?: Expr, where?: Expr }): ApproxReport { table; checks: { monotone: boolean; mismatches: …[]; stabilizedAt: number|null } }`
- `renderTable(report): string` (text, columns `f0 … fk`, `⊥` cells, `first` column), `renderHtml(report): string` (self-contained HTML: table, heatmap SVG for 1- or 2-parameter grids coloured by first defined k, chart of defined-count per k).

- [ ] Tests: `div report first-defined = x div y + 1`, `expected undefined is not a mismatch`, `mismatch detected for wrong function`, `html contains one cell per state`, `monotonicity check fails on a forged table`.
- [ ] Commit `feat: test approximation chains and render fixpoint reports`.

### Task 7: Correctness assistant (SEM-04)

**Files:** `src/verify/wp.ts`, `src/verify/check.ts`, `tests/verify.test.ts`, `examples/verify/*.sipl`

**Produces:**
- `VC { id; kind: 'init'|'preserve'|'exit'|'variant-bound'|'variant-decrease'|'straight'; loopId?: number; hypothesis: Expr; goal: Expr; derivation: string[] }`
- `generateVCs(program): VC[]` — wp rules: assign = substitution, seq, if = `(b → wp1) ∧ (¬b → wp2)`, skip, block, while uses its invariant; variant VCs only when `//@ variant` present. Derivation lines name the rule and show the formula after it.
- `checkVC(vc, { range: [lo, hi] }): { status: 'refuted'; counterexample: State; reachable?: boolean } | { status: 'checked'; cases: number }`
- `verifyProgram(program, opts): VerifyReport { vcs: (VC & result)[]; runs: { input; outcome; violation? }[]; verdict: 'refuted'|'checked-in-bounds' }` — `runs` executes the program on every pre-satisfying state in range and checks invariants at each loop head (course: state after k iterations) and post at the end.

Bounded results are reported as "checked for all states with values in [lo, hi]", never as proofs.

- [ ] Tests: `power program verifies with invariant R * X^Y = x^y`, `GCD total correctness with variant M + N`, `wrong invariant refuted with counterexample`, `non-inductive invariant`, `missing invariant on a loop is a diagnostic`, `derivation shows wp substitution`.
- [ ] Commit `feat: add loop correctness assistant with verification conditions and counterexamples`.

### Task 8: CLI

**Files:** `src/cli.ts`, `src/index.ts`, `tests/cli.test.ts`

Commands: `check <file>`, `run <file> -s X=5 …`, `term <file> [--explain] [--function f]`, `approx <file> --function f -k 3 --grid X=0..9,Y=1..5 [--expect EXPR] [--where EXPR] [--html out.html]`, `verify <file> [--range -3..8]`; all accept `--json`; `-` = stdin. Exit codes: `0` ok, `1` syntax/static error, `2` undefined result / refuted VC / mismatch, `64` usage, `66` unreadable file.

- [ ] Integration tests for each command and each exit code.
- [ ] Commit `feat: add sipl command-line interface`.

### Task 9: Docs and CI (REL-01)

**Files:** `README.md`, `CHANGELOG.md`, `LICENSE`, `docs/language.md`, `docs/semantics.md`, `docs/fixpoint.md`, `docs/verification.md`, `docs/architecture.md`, `.github/workflows/ci.yml`

README: selected IDs and points, install, quick start for every command, limits (bounded checking is not proof, integer range, unfolding limits). CI: Node 20/22, `npm ci`, lint, typecheck, test with coverage, build, `npm pack` artifact; badge.

- [ ] Clean `npm ci && npm run lint && npm run typecheck && npm test && npm run build` passes; every README command run against `examples/`.
- [ ] Commit `docs: add documentation and CI workflow`; tag `v0.1.0`.
