import { readdirSync, readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath } from 'node:url';
import type { Expr, Stm } from '../src/ast.js';

/** Repository root (tests are compiled to .test-build/tests). */
export const ROOT = join(dirname(fileURLToPath(import.meta.url)), '..', '..');

export function readExample(rel: string): string {
  return readFileSync(join(ROOT, 'examples', rel), 'utf8');
}

export function listExamples(dir = ''): string[] {
  return readdirSync(join(ROOT, 'examples', dir))
    .filter((f) => f.endsWith('.sipl'))
    .sort()
    .map((f) => join(dir, f));
}

/** Compact s-expression of an AST node, ignoring ids and spans. */
export function sx(node: Stm | Expr): string {
  switch (node.kind) {
    case 'num':
      return String(node.value);
    case 'var':
      return node.name;
    case 'bool':
      return String(node.value);
    case 'binary':
    case 'compare':
    case 'logic':
      return `(${node.op} ${sx(node.left)} ${sx(node.right)})`;
    case 'not':
      return `(not ${sx(node.operand)})`;
    case 'cond':
      return `(if ${sx(node.cond)} ${sx(node.then)} ${sx(node.else)})`;
    case 'call':
      return `(${node.name}${node.args.map((a) => ' ' + sx(a)).join('')})`;
    case 'assign':
      return `(:= ${node.target} ${sx(node.value)})`;
    case 'seq':
      return `(; ${sx(node.first)} ${sx(node.second)})`;
    case 'if':
      return `(IF ${sx(node.cond)} ${sx(node.then)} ${sx(node.else)})`;
    case 'while':
      return `(WHILE ${sx(node.cond)} ${sx(node.body)})`;
    case 'block':
      return `(BLOCK ${sx(node.body)})`;
    case 'skip':
      return 'skip';
  }
}

/** Reads `// run: A=1 B=2 -> R=3` lines from an example. */
export function runSpecs(source: string): { input: Record<string, number>; expect: Record<string, number> }[] {
  const toState = (s: string) =>
    Object.fromEntries(
      s.trim().split(/\s+/).filter(Boolean).map((kv) => {
        const [k, v] = kv.split('=');
        return [k, Number(v)];
      }),
    );
  return [...source.matchAll(/^\/\/ run:(.*)->(.*)$/gm)].map((m) => ({ input: toState(m[1]), expect: toState(m[2]) }));
}
