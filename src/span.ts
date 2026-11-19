/** A point in source text. `line` and `column` are 1-based, `offset` is 0-based (UTF-16 units). */
export interface Position {
  line: number;
  column: number;
  offset: number;
}

/** Half-open source range: `end` points just past the last character. */
export interface SourceSpan {
  start: Position;
  end: Position;
}

export type Severity = 'error' | 'warning' | 'info';

export interface Diagnostic {
  severity: Severity;
  code: string;
  message: string;
  span: SourceSpan;
}

/** Error carrying a diagnostic bound to a source span. */
export class SiplError extends Error {
  readonly diagnostic: Diagnostic;

  constructor(code: string, message: string, span: SourceSpan) {
    super(`${span.start.line}:${span.start.column}: ${message}`);
    this.name = 'SiplError';
    this.diagnostic = { severity: 'error', code, message, span };
  }
}

export function spanBetween(from: SourceSpan, to: SourceSpan): SourceSpan {
  return { start: from.start, end: to.end };
}

export function formatDiagnostic(d: Diagnostic, file = '<input>'): string {
  return `${file}:${d.span.start.line}:${d.span.start.column}: ${d.severity} ${d.code}: ${d.message}`;
}
