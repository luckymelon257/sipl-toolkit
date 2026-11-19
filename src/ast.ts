import type { Annotation } from './lexer.js';
import type { SourceSpan } from './span.js';

/** Every AST node carries a preorder id (unique within its program) and its source span. */
interface NodeBase {
  id: number;
  span: SourceSpan;
}

export type ArithOp = '+' | '-' | '*' | '^' | 'div' | 'mod';
export type CompareOp = '=' | '>' | '<' | '>=' | '<=' | '!=';
export type LogicOp = 'or' | 'and' | 'implies';

export interface Num extends NodeBase { kind: 'num'; value: number }
export interface Var extends NodeBase { kind: 'var'; name: string }
export interface Binary extends NodeBase { kind: 'binary'; op: ArithOp; left: Expr; right: Expr }
/** SIPL-R conditional expression `if b then a1 else a2`. */
export interface Cond extends NodeBase { kind: 'cond'; cond: Expr; then: Expr; else: Expr }
/** SIPL-R function call `fn` or `fn(a1, ..., an)`; also `gcd`/`abs` in assertions. */
export interface Call extends NodeBase { kind: 'call'; name: string; args: Expr[] }
export interface Compare extends NodeBase { kind: 'compare'; op: CompareOp; left: Expr; right: Expr }
export interface Logic extends NodeBase { kind: 'logic'; op: LogicOp; left: Expr; right: Expr }
export interface Not extends NodeBase { kind: 'not'; operand: Expr }
/** `true` / `false`, assertions only. */
export interface BoolLit extends NodeBase { kind: 'bool'; value: boolean }

/** Arithmetic expressions (Aexp) and conditions (Bexp) share one type; the parser keeps them apart. */
export type Expr = Num | Var | Binary | Cond | Call | Compare | Logic | Not | BoolLit;

export interface Assign extends NodeBase { kind: 'assign'; target: string; targetSpan: SourceSpan; value: Expr }
export interface Seq extends NodeBase { kind: 'seq'; first: Stm; second: Stm }
export interface If extends NodeBase { kind: 'if'; cond: Expr; then: Stm; else: Stm }
export interface While extends NodeBase {
  kind: 'while';
  cond: Expr;
  body: Stm;
  /** From a preceding `//@ invariant:` annotation. */
  invariant?: Expr;
  /** From a preceding `//@ variant:` annotation. */
  variant?: Expr;
}
export interface Block extends NodeBase { kind: 'block'; body: Stm }
export interface Skip extends NodeBase { kind: 'skip' }

export type Stm = Assign | Seq | If | While | Block | Skip;

export interface FuncDecl extends NodeBase {
  kind: 'func';
  name: string;
  nameSpan: SourceSpan;
  params: string[];
  paramSpans: SourceSpan[];
  body: Expr;
}

export interface Program extends NodeBase {
  kind: 'program';
  functions: FuncDecl[];
  body: Stm;
  /** True when SIPL-R constructs are used (`program`/`func`, calls, `<`, if-expressions). */
  extended: boolean;
  annotations: Annotation[];
  pre?: Expr;
  post?: Expr;
}

export type Node = Program | FuncDecl | Stm | Expr;

/** Direct children in source order. */
export function children(node: Node): Node[] {
  switch (node.kind) {
    case 'program':
      return [...node.functions, node.body];
    case 'func':
      return [node.body];
    case 'assign':
      return [node.value];
    case 'seq':
      return [node.first, node.second];
    case 'if':
    case 'cond':
      return [node.cond, node.then, node.else];
    case 'while':
      return [node.cond, node.body];
    case 'block':
      return [node.body];
    case 'binary':
    case 'compare':
    case 'logic':
      return [node.left, node.right];
    case 'not':
      return [node.operand];
    case 'call':
      return node.args;
    case 'num':
    case 'var':
    case 'bool':
    case 'skip':
      return [];
  }
}

/** Preorder walk. */
export function* walk(node: Node): Generator<Node> {
  yield node;
  for (const c of children(node)) yield* walk(c);
}

/** Variables read by an expression, in order of first occurrence. */
export function freeVars(e: Expr, out: string[] = []): string[] {
  for (const n of walk(e)) if (n.kind === 'var' && !out.includes(n.name)) out.push(n.name);
  return out;
}
