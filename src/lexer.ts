import { Position, SiplError, SourceSpan } from './span.js';

export type TokenKind =
  | 'begin' | 'end' | 'if' | 'then' | 'else' | 'while' | 'do' | 'skip' | 'program' | 'func'
  | 'ident' | 'number'
  | ':=' | ';' | ',' | '+' | '-' | '*' | '(' | ')' | '=' | '>' | '<'
  | 'or' | 'not' | 'and' | 'implies' | '<=' | '>=' | '!=' | '^' | 'div' | 'mod'
  | 'eof';

export interface Token {
  kind: TokenKind;
  /** Text exactly as written in the source (e.g. `∨` for kind `or`). */
  text: string;
  span: SourceSpan;
}

export type AnnotationKey = 'pre' | 'post' | 'invariant' | 'variant';

/** A `//@ key: text` comment; `span` covers `text`. */
export interface Annotation {
  key: AnnotationKey;
  text: string;
  span: SourceSpan;
}

export type LexMode = 'program' | 'assertion';

const WORDS: Record<string, TokenKind> = {
  begin: 'begin', end: 'end', if: 'if', then: 'then', else: 'else', while: 'while', do: 'do',
  skip: 'skip', program: 'program', func: 'func', or: 'or', not: 'not', and: 'and',
  implies: 'implies', div: 'div', mod: 'mod',
};

// Longest match first.
const SYMBOLS: [string, TokenKind][] = [
  [':=', ':='], ['<=', '<='], ['>=', '>='], ['!=', '!='], ['=>', 'implies'],
  [';', ';'], [',', ','], ['+', '+'], ['-', '-'], ['*', '*'], ['(', '('], [')', ')'],
  ['=', '='], ['>', '>'], ['<', '<'], ['^', '^'],
  ['∨', 'or'], ['¬', 'not'], ['∧', 'and'], ['→', 'implies'], ['≤', '<='], ['≥', '>='], ['≠', '!='],
  ['–', '-'], ['−', '-'], ['∗', '*'], ['×', '*'],
];

/** Kinds that exist only in the assertion language of annotations. */
const ASSERTION_ONLY = new Set<TokenKind>(['and', 'implies', '<=', '>=', '!=', '^', 'div', 'mod']);

const ANNOTATION_KEYS = new Set<string>(['pre', 'post', 'invariant', 'variant']);

export function tokenize(source: string, mode: LexMode = 'program'): { tokens: Token[]; annotations: Annotation[] } {
  const tokens: Token[] = [];
  const annotations: Annotation[] = [];
  let offset = 0;
  let line = 1;
  let column = 1;

  const here = (): Position => ({ line, column, offset });
  const advance = (count: number): void => {
    for (let i = 0; i < count; i++) {
      const ch = source[offset];
      if (ch === '\r' && source[offset + 1] === '\n') {
        offset += 2;
        line++;
        column = 1;
      } else if (ch === '\n' || ch === '\r') {
        offset++;
        line++;
        column = 1;
      } else {
        offset++;
        column++;
      }
    }
  };
  const push = (kind: TokenKind, length: number): void => {
    const start = here();
    const text = source.slice(offset, offset + length);
    advance(length);
    const span = { start, end: here() };
    if (mode === 'program' && ASSERTION_ONLY.has(kind)) {
      throw new SiplError(
        'E002',
        `'${text}' is not part of SIPL programs; ` +
          (kind === 'div' || kind === 'mod'
            ? 'express it with +, -, * in a loop or a recursive function'
            : 'it may be used only in //@ annotations'),
        span,
      );
    }
    tokens.push({ kind, text, span });
  };

  while (offset < source.length) {
    const ch = source[offset];
    if (/\s/.test(ch)) {
      advance(1);
      continue;
    }
    if (source.startsWith('//', offset)) {
      const eol = source.slice(offset).search(/[\r\n]/);
      const lineEnd = eol < 0 ? source.length : offset + eol;
      if (source[offset + 2] === '@') readAnnotation(lineEnd);
      advance(lineEnd - offset);
      continue;
    }
    const word = /^[A-Za-z][A-Za-z0-9_]*/.exec(source.slice(offset, offset + 256));
    if (word) {
      push(WORDS[word[0]] ?? 'ident', word[0].length);
      continue;
    }
    const num = /^[0-9]+/.exec(source.slice(offset, offset + 64));
    if (num) {
      push('number', num[0].length);
      continue;
    }
    const sym = SYMBOLS.find(([s]) => source.startsWith(s, offset) && (s !== '=>' || mode === 'assertion'));
    if (sym) {
      push(sym[1], sym[0].length);
      continue;
    }
    const start = here();
    advance(1);
    throw new SiplError('E001', `unexpected character '${ch}'`, { start, end: here() });
  }
  tokens.push({ kind: 'eof', text: '', span: { start: here(), end: here() } });
  return { tokens, annotations };

  function readAnnotation(lineEnd: number): void {
    const body = source.slice(offset + 3, lineEnd);
    const m = /^(\s*)([A-Za-z]+)\s*:(\s*)(.*?)\s*$/.exec(body);
    const lineStart = { line, column, offset };
    const at = (delta: number): Position => ({ line, column: lineStart.column + delta, offset: lineStart.offset + delta });
    if (!m || !ANNOTATION_KEYS.has(m[2])) {
      throw new SiplError(
        'E003',
        `malformed annotation; expected '//@ pre|post|invariant|variant: <assertion>'`,
        { start: at(0), end: at(lineEnd - offset) },
      );
    }
    const textStart = 3 + body.indexOf(':') + 1 + m[3].length;
    annotations.push({
      key: m[2] as AnnotationKey,
      text: m[4],
      span: { start: at(textStart), end: at(textStart + m[4].length) },
    });
  }
}
