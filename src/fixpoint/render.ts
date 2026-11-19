import { State } from '../values.js';
import type { ApproxReport, ReportRow } from './report.js';

const BOT = '⊥';

function variablesOf(rows: ReportRow[]): string[] {
  const names: string[] = [];
  for (const r of rows) for (const k of Object.keys(r.state)) if (!names.includes(k)) names.push(k);
  return names;
}

function summary(report: ApproxReport): string[] {
  const { table, checks, rows } = report;
  const lines = [
    `defined on: ${table.definedCount.map((c, i) => `${table.fn}${i}: ${c}/${rows.length}`).join('  ')}`,
    `monotone: ${checks.monotone ? 'yes' : 'NO'} (once defined, a value never changes in later approximations)`,
    checks.allDefined
      ? `f${table.k} is defined on all test states; the defined part stopped growing at ${table.fn}${checks.stabilizedAt}`
      : `f${table.k} is still not defined on ${rows.length - table.definedCount[table.k]} test state(s); raise k to see more`,
  ];
  if (report.expect !== undefined) {
    const comparable = rows.filter((r) => r.firstDefined !== null && r.expected !== null).length;
    lines.push(checks.mismatches.length === 0
      ? `expected ${report.expect}: matches on all ${comparable} comparable state(s)`
      : `expected ${report.expect}: ${checks.mismatches.length} MISMATCH(ES), e.g. ${describeMismatch(report)}`);
  }
  return lines;
}

function describeMismatch(report: ApproxReport): string {
  const m = report.checks.mismatches[0];
  return `${stateText(m.state)}: ${report.table.fn}${m.k} = ${m.actual}, expected ${m.expected}`;
}

function stateText(st: State): string {
  return Object.entries(st).map(([k, v]) => `${k}=${v}`).join(', ');
}

/** Plain-text report: the approximation terms, a table of values and the checks. */
export function renderTable(report: ApproxReport): string {
  const { table, rows } = report;
  const vars = variablesOf(rows);
  const header = [...vars, ...table.terms.map((_, i) => `${table.fn}${i}`), 'first', ...(report.expect !== undefined ? ['expected'] : [])];
  const body = rows.map((r) => [
    ...vars.map((v) => String(r.state[v] ?? '')),
    ...r.values.map((v) => (v === null ? BOT : String(v))),
    r.firstDefined === null ? '-' : String(r.firstDefined),
    ...(report.expect !== undefined ? [r.expected === null ? 'n/a' : String(r.expected)] : []),
  ]);
  const widths = header.map((h, i) => Math.max(h.length, ...body.map((row) => row[i].length)));
  const line = (l: string, m: string, r: string) => l + widths.map((w) => '─'.repeat(w + 2)).join(m) + r;
  const row = (cells: string[]) => cells.map((c, i) => `│ ${c.padEnd(widths[i])} `).join('') + '│';
  return [
    `Approximations of ${table.fn}, k = 0..${table.k}`,
    ...table.terms.map((t, i) => `  ${table.fn}${i} = ${t}`),
    '',
    line('┌', '┬', '┐'),
    row(header),
    line('├', '┼', '┤'),
    ...body.map(row),
    line('└', '┴', '┘'),
    ...summary(report),
  ].join('\n') + '\n';
}

function esc(s: string): string {
  return s.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

/** Fill colour for "first defined at index i of k": early indices dark, late ones light. */
function shade(i: number, k: number): string {
  const t = k <= 1 ? 0 : (i - 1) / (k - 1);
  return `hsl(212 70% ${Math.round(30 + t * 50)}%)`;
}

function heatmap(report: ApproxReport): string {
  const { rows, table } = report;
  const varying = variablesOf(rows).filter((v) => new Set(rows.map((r) => r.state[v])).size > 1);
  if (varying.length === 0 || varying.length > 2) {
    return `<p class="note">The heatmap needs one or two varying variables; these test states vary in ${varying.length}.</p>`;
  }
  const [xv, yv] = varying;
  const xs = [...new Set(rows.map((r) => r.state[xv]))].sort((a, b) => a - b);
  const ys = yv ? [...new Set(rows.map((r) => r.state[yv]))].sort((a, b) => a - b) : [0];
  const cell = 30;
  const left = 48;
  const top = 12;
  const width = left + xs.length * cell + 12;
  const height = top + ys.length * cell + 40;
  const cells = rows.map((r) => {
    const x = left + xs.indexOf(r.state[xv]) * cell;
    const y = top + (ys.length - 1 - ys.indexOf(yv ? r.state[yv] : 0)) * cell;
    const first = r.firstDefined;
    const fill = first === null ? 'var(--bottom)' : shade(first, table.k);
    const label = first === null ? BOT : String(first);
    const tip = first === null
      ? `${stateText(r.state)}: not defined in ${table.fn}0..${table.fn}${table.k}`
      : `${stateText(r.state)}: defined from ${table.fn}${first}, value ${r.values[first]}`;
    return `<g><title>${esc(tip)}</title><rect class="cell" x="${x}" y="${y}" width="${cell - 2}" height="${cell - 2}" rx="3" fill="${fill}"/>` +
      `<text x="${x + (cell - 2) / 2}" y="${y + cell / 2 + 3}" class="${first === null ? 'bot' : first > table.k / 2 ? 'dark' : 'light'}">${label}</text></g>`;
  });
  const xLabels = xs.map((v, i) => `<text class="axis" x="${left + i * cell + (cell - 2) / 2}" y="${top + ys.length * cell + 14}">${v}</text>`);
  const yLabels = yv ? ys.map((v, i) => `<text class="axis" x="${left - 8}" y="${top + (ys.length - 1 - i) * cell + cell / 2 + 3}" text-anchor="end">${v}</text>`) : [];
  return `<svg class="heatmap" role="img" aria-label="First approximation index at which ${esc(table.fn)} is defined" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">
${cells.join('\n')}
${xLabels.join('')}${yLabels.join('')}
<text class="axis-title" x="${left + (xs.length * cell) / 2}" y="${height - 6}">${esc(xv)}</text>
${yv ? `<text class="axis-title" x="12" y="${top + (ys.length * cell) / 2}" transform="rotate(-90 12 ${top + (ys.length * cell) / 2})">${esc(yv)}</text>` : ''}
</svg>
<p class="note">Each cell is a test state; the number is the index i of the first approximation ${esc(table.fn)}i defined on it (darker = earlier), ${BOT} = not defined up to ${esc(table.fn)}${table.k}.</p>`;
}

function bars(report: ApproxReport): string {
  const { table, rows } = report;
  const bar = 34;
  const h = 140;
  const width = 40 + table.definedCount.length * bar;
  const max = Math.max(rows.length, 1);
  const items = table.definedCount.map((c, i) => {
    const bh = Math.round((c / max) * h);
    const x = 30 + i * bar;
    return `<g><title>${esc(`${table.fn}${i}: defined on ${c} of ${rows.length} test states`)}</title>` +
      `<rect x="${x}" y="${10 + h - bh}" width="${bar - 8}" height="${bh}" rx="2" class="bar"/>` +
      `<text class="axis" x="${x + (bar - 8) / 2}" y="${h + 26}">${esc(table.fn)}${i}</text>` +
      `<text class="axis" x="${x + (bar - 8) / 2}" y="${10 + h - bh - 4}">${c}</text></g>`;
  });
  return `<svg class="bars" role="img" aria-label="Number of test states on which each approximation is defined" width="${width}" height="${h + 34}" viewBox="0 0 ${width} ${h + 34}">
<line x1="26" y1="${10 + h}" x2="${width}" y2="${10 + h}" class="baseline"/>
${items.join('\n')}
</svg>`;
}

/** Self-contained HTML report with the terms, a heatmap of the domain of definedness, convergence bars and the table. */
export function renderHtml(report: ApproxReport): string {
  const { table, rows } = report;
  const vars = variablesOf(rows);
  const head = [...vars, ...table.terms.map((_, i) => `${table.fn}${i}`), 'first', ...(report.expect !== undefined ? ['expected'] : [])];
  const mismatched = new Set(report.checks.mismatches.map((m) => JSON.stringify(m.state)));
  const tableRows = rows.map((r) => {
    const cells = [
      ...vars.map((v) => `<td class="var">${r.state[v] ?? ''}</td>`),
      ...r.values.map((v) => (v === null ? `<td class="bot">${BOT}</td>` : `<td class="def">${v}</td>`)),
      `<td>${r.firstDefined ?? '–'}</td>`,
      ...(report.expect !== undefined ? [`<td>${r.expected ?? 'n/a'}</td>`] : []),
    ];
    const bad = mismatched.has(JSON.stringify(r.state)) ? ' bad' : '';
    return `<tr class="state${bad}">${cells.join('')}</tr>`;
  });
  return `<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Approximations of ${esc(table.fn)}</title>
<style>
:root { --bg: #ffffff; --fg: #1d2330; --muted: #5d6677; --line: #d9dee7; --bottom: #e4e7ec; --bar: #3a78c9; --bad: #fde2e1; --def: #eef4fc; }
@media (prefers-color-scheme: dark) { :root { --bg: #14171d; --fg: #e6e9ef; --muted: #9aa3b2; --line: #2c323d; --bottom: #2a2f38; --bar: #6aa3ea; --bad: #4a2427; --def: #1b2533; } }
body { margin: 0; padding: 24px 16px; background: var(--bg); color: var(--fg); font: 15px/1.5 system-ui, -apple-system, "Segoe UI", sans-serif; }
main { max-width: 1100px; margin: 0 auto; }
h1 { font-size: 22px; margin: 0 0 4px; } h2 { font-size: 17px; margin: 28px 0 8px; }
.sub, .note { color: var(--muted); font-size: 13px; }
code, td, .terms { font-family: ui-monospace, "SF Mono", Menlo, Consolas, monospace; font-size: 13px; }
ol.terms { padding-left: 0; list-style: none; } ol.terms li { margin: 4px 0; overflow-wrap: anywhere; }
ul.checks { padding-left: 18px; }
.scroll { overflow-x: auto; }
table { border-collapse: collapse; } th, td { border: 1px solid var(--line); padding: 3px 8px; text-align: right; }
th { font-weight: 600; } td.bot { color: var(--muted); } td.def { background: var(--def); } tr.bad td { background: var(--bad); }
svg text { fill: var(--fg); font: 11px ui-monospace, Menlo, monospace; text-anchor: middle; }
svg text.light { fill: #ffffff; } svg text.dark { fill: #1d2330; } svg text.bot { fill: var(--muted); }
svg text.axis { fill: var(--muted); } svg text.axis-title { font-weight: 600; }
svg .bar { fill: var(--bar); } svg .baseline { stroke: var(--line); }
</style>
</head>
<body>
<main>
<h1>Least fixed point of ${esc(table.fn)}: approximations ${esc(table.fn)}0 … ${esc(table.fn)}${table.k}</h1>
<p class="sub">${esc(table.fn)}0 = ⊥, ${esc(table.fn)}(i+1) = φ(${esc(table.fn)}i). ${rows.length} test state(s). Generated from the program's semantic terms.</p>
<h2>Approximation terms</h2>
<ol class="terms" start="0">${table.terms.map((t, i) => `<li><b>${esc(table.fn)}${i}</b> = ${esc(t)}</li>`).join('')}</ol>
<h2>Checks</h2>
<ul class="checks">${summary(report).map((l) => `<li>${esc(l)}</li>`).join('')}</ul>
<h2>Where each test state becomes defined</h2>
<div class="scroll">${heatmap(report)}</div>
<h2>Defined states per approximation</h2>
<div class="scroll">${bars(report)}</div>
<h2>Values</h2>
<div class="scroll"><table>
<thead><tr>${head.map((h) => `<th>${esc(h)}</th>`).join('')}</tr></thead>
<tbody>
${tableRows.join('\n')}
</tbody>
</table></div>
</main>
</body>
</html>
`;
}
