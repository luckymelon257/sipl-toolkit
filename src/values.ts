/** A state of variables, State = Var → Int (Nikitchenko 2020, §1.3.1). Key order is the order of creation. */
export type State = Record<string, number>;

/** `[X ↦ 5, Y ↦ 2]` as in the practicum. */
export function formatState(st: State): string {
  return `[${Object.entries(st).map(([k, v]) => `${k} ↦ ${v}`).join(', ')}]`;
}

/** Parses `['X=5', 'Y=-2,Z=0']` into a state. Throws `Error` naming the bad item. */
export function parseAssignments(items: string[]): State {
  const st: State = {};
  for (const item of items.flatMap((s) => s.split(',')).map((s) => s.trim()).filter(Boolean)) {
    const m = /^([A-Za-z][A-Za-z0-9_]*)\s*=\s*(-?[0-9]+)$/.exec(item);
    const value = m ? Number(m[2]) : NaN;
    if (!m || !Number.isSafeInteger(value)) throw new Error(`bad assignment '${item}', expected NAME=INTEGER`);
    st[m[1]] = value;
  }
  return st;
}

/** Result of an integer operation, or `undefined` when it leaves the safe integer range. */
export function checkedInt(value: number): number | undefined {
  return Number.isSafeInteger(value) ? value : undefined;
}
