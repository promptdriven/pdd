// Generated from prompts/cli/runtime-output.prompt.md (sha256: 31950901b783bbac888f3427cd803ad039e81f78abfd01bf33ca9ba9cebeecd5).
export const OPEN_STATES = new Set(['queued', 'running']);
const RESULT_WORDS = { not_run: 'not run' };

// The first match from the top wins: 3 > 5 > 4 > 1 > 0.
export function exitCodeFor(rows, { interrupted = false, lintUnknown = false } = {}) {
  const states = new Set(rows.map(row => row.state));
  // Any state that is not a known end (also queued, running or a half-written row) may still run: 3.
  if (interrupted || lintUnknown || [...states].some(state => !['passed', 'failed', 'refused', 'not_run'].includes(state))) return 3;
  if (states.has('not_run')) return 5;
  if (states.has('refused')) return 4;
  if (states.has('failed')) return 1;
  return 0;
}

const SERVER_PATH = /(?<![\w.:/-])\/(?:home|Users|srv|var|tmp|private|opt|mnt|workspace|usr|etc)\/[^\s"'<>)\]]*/g;
// Server text in the terminal: no control characters, no token and, in free text, no server paths.
export function cleanText(value, secrets = [], { paths = true } = {}) {
  let text = String(value ?? '').replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '').replace(/[\x00-\x1f\x7f-\x9f]/g, ' ');
  for (const secret of secrets) if (secret) text = text.split(secret).join('[secret]');
  return (paths ? text.replace(SERVER_PATH, '<server path>') : text).trim();
}
const cleanField = (value, secrets) => cleanText(value, secrets, { paths: false });
const shown = (value, secrets) => { const text = cleanField(JSON.stringify(value) ?? 'nothing', secrets); return text.length > 80 ? `${text.slice(0, 77)}...` : text; };

// A secret browser link from the runtime: same scheme and host as the origin, the expected path, no user or password.
export function validLink(value, origin, kind) {
  if (typeof value !== 'string') return null;
  try {
    const url = new URL(value), base = new URL(origin);
    const path = kind === 'try' ? /^\/s\/[A-Za-z0-9_-]+\/$/ : /^\/r\/[A-Za-z0-9_.-]+$/;
    return url.protocol === base.protocol && url.host === base.host && !url.username && !url.password
      && !url.search && !url.hash && path.test(url.pathname) ? url.href : null;
  } catch { return null; }
}

const scrub = (value, secrets) => typeof value === 'string' ? secrets.reduce((text, secret) => secret ? text.split(secret).join('[secret]') : text, value)
  : Array.isArray(value) ? value.map(item => scrub(item, secrets))
  : value && typeof value === 'object' ? Object.fromEntries(Object.entries(value).map(([key, item]) => [key, scrub(item, secrets)])) : value;

// The parts of a server answer that pdd shows.
export function projectAnswer(answer, { origin, secrets = [] } = {}) {
  const result = answer?.result ?? null, report = result?.report ?? null;
  const steps = Array.isArray(report?.samples) && Array.isArray(report.samples[0]?.steps) ? report.samples[0].steps : [];
  const all = steps.flatMap(step => Array.isArray(step?.checks) ? step.checks : []).map(check => ({
    criterion_id: cleanField(check?.criterion_id, secrets), target: cleanField(check?.target, secrets), path: cleanField(check?.path, secrets),
    expected: scrub(check?.expected, secrets), actual: scrub(check?.actual, secrets), passed: check?.passed === true }));
  const refusals = (Array.isArray(result?.refusals) ? result.refusals : []).map(item => ({
    code: cleanText(item?.code, secrets) || 'unknown', section: cleanText(item?.section, secrets) || null,
    message: cleanText(item?.message, secrets) || null, engine_message: cleanText(item?.engine_message, secrets) || null, hint: null }));
  const usage = answer?.usage ?? {};
  const model = [usage.requested_model, report?.evaluation?.requested_model].find(value => typeof value === 'string' && value && value !== 'unknown');
  const results = Array.isArray(report?.criterion_results) ? report.criterion_results : [];
  const cause = Array.isArray(report?.samples) ? report.samples.map(sample => sample?.refusal?.failure_cause).find(isObjectLike) : null;
  const provider = answer?.state === 'unknown' && (refusals.some(item => item.code === 'graph-provider-failure') || cause?.kind === 'transport_unknown')
    ? { code: refusals.find(item => item.code === 'graph-provider-failure')?.code ?? 'graph-provider-failure',
      detail: [cause?.kind, cause?.detail].filter(Boolean).map(text => cleanText(text, secrets)).join(', ') || null } : null;
  return {
    state: answer?.state, checks: all.length ? { passed: all.filter(check => check.passed).length, total: all.length } : null,
    criteria: results.length ? { passed: results.filter(item => item?.status === 'passed').length, total: results.length } : null,
    all_checks: all, failed_checks: all.filter(check => !check.passed).map(({ passed, ...check }) => check), refusals,
    calls: typeof usage.calls === 'number' ? usage.calls : 'unknown', requested_model: model ? cleanText(model, secrets) : null,
    server_seconds: typeof usage.seconds === 'number' ? usage.seconds : null,
    report_url: validLink(answer?.report_url, origin, 'report'), why: result?.why ? cleanText(result.why, secrets) : null,
    engine_sha: typeof answer?.engine_sha === 'string' ? answer.engine_sha : null, provider,
    // The server's list of draft prompts (prompt-runtime #365) wins over pdd's local guess; null when the server has none.
    draft: Array.isArray(answer?.draft_prompts) ? answer.draft_prompts.length > 0 : null };
}

const isObjectLike = value => value !== null && typeof value === 'object' && !Array.isArray(value);
export const PROVIDER_TEXT = 'the AI provider failed during the run. It is not a failed check. Do not send it again yet.';
const round = seconds => typeof seconds === 'number' ? Math.round(seconds * 10) / 10 : null;
const sentRow = row => row.phase === 'server';

export function jsonRow(row) {
  return { story: row.story, title: row.title, test: row.test, state: row.state, checks: row.checks ?? null, criteria: row.criteria ?? null,
    failed_checks: row.failed_checks ?? [], refusals: (row.refusals ?? []).map(item => ({ code: item.code, section: item.section ?? null,
      message: item.message ?? null, engine_message: item.engine_message ?? null, hint: item.hint ?? null })), calls: sentRow(row) ? row.calls ?? 'unknown' : 0,
    seconds: round(row.seconds), requested_model: row.requested_model ?? null, report_url: row.report_url ?? null,
    request_id: row.request_ids?.at(-1) ?? null, draft: !!row.draft,
    reason: row.provider ? { code: row.provider.code, message: PROVIDER_TEXT } : row.note ?? (row.why ? { code: null, message: row.why } : null) };
}

export function renderJson({ batch = null, repo, rows, warnings = [], exitCode, summaryLine: line = summaryLine(rows) }) {
  const perStory = new Map(storyLines(rows).map(([story, text]) => [story, text]));
  return { batch, repo, exit_code: exitCode, summary_line: line, draft: rows.some(row => row.draft),
    rows: rows.map(row => ({ ...jsonRow(row), summary_line: perStory.get(row.story) ?? null })), warnings };
}

const count = (number, word) => `${number} ${word}${number === 1 ? '' : 's'}`;
// One line an agent can paste into a PR: ✓ only when every story passed.
// One paste line per Story (0.1.6: many Stories in one run), in table order; a Story with two test files gets one line.
export function storyLines(rows) {
  const groups = new Map();
  for (const row of rows) groups.set(row.story, [...(groups.get(row.story) ?? []), row]);
  return [...groups].map(([story, own]) => [story, summaryLine(own, story)]);
}

export function summaryLine(rows, story = null) {
  const own = row => row.criteria ?? { passed: row.state === 'passed' ? row.criteria_total ?? 0 : 0, total: row.criteria_total ?? 0 };
  const criteria = rows.reduce((sum, row) => ({ passed: sum.passed + own(row).passed, total: sum.total + own(row).total }), { passed: 0, total: 0 });
  const checks = rows.reduce((sum, row) => ({ passed: sum.passed + (row.checks?.passed ?? 0), total: sum.total + (row.checks?.total ?? 0) }), { passed: 0, total: 0 });
  const sent = rows.filter(sentRow), known = sent.filter(row => typeof row.calls === 'number' && !OPEN_STATES.has(row.state));
  const calls = known.reduce((sum, row) => sum + row.calls, 0), unknownCalls = sent.length - known.length;
  const others = ['refused', 'not_run', 'unknown', 'queued', 'running'].map(state => [state, rows.filter(row => row.state === state).length])
    .filter(([, number]) => number).map(([state, number]) => `${number} ${RESULT_WORDS[state] ?? state}`);
  // A cross only for a real failure; a check that still runs or has no verdict says so (cli 12b).
  const bad = rows.some(row => ['failed', 'refused', 'not_run'].includes(row.state));
  const mark = rows.length && rows.every(row => row.state === 'passed') ? '✓' : bad ? '✗'
    : rows.some(row => OPEN_STATES.has(row.state)) ? 'running ·' : 'unknown ·';
  return [`Runtime check${story ? ` (${story})` : ''}${rows.some(row => row.draft) ? ' (DRAFT)' : ''}: ${mark} ${criteria.passed} of ${count(criteria.total, 'criterion').replace(/criterions$/, 'criteria')}`,
    `${checks.passed}/${checks.total} checks`, ...others, `${count(calls, 'AI call')}${unknownCalls ? ` + ${unknownCalls} unknown` : ''}`].join(' · ');
}

function table(rows) {
  const lines = [['Story', 'Test', 'Result', 'Checks', 'Time'], ...rows.map(row => [row.title ?? row.story, row.test,
    `${RESULT_WORDS[row.state] ?? row.state}${row.draft ? ' (DRAFT)' : ''}`, row.checks ? `${row.checks.passed}/${row.checks.total}` : '-',
    typeof row.seconds === 'number' ? `${round(row.seconds).toFixed(1)} s` : '-'])];
  const widths = lines[0].map((_, column) => Math.max(...lines.map(line => line[column].length)));
  return lines.map(line => line.map((cell, column) => column === line.length - 1 ? cell : cell.padEnd(widths[column])).join('  ').trimEnd());
}

const checkLine = (check, secrets) => `${check.criterion_id}  ${check.target} ${check.path}  expected ${shown(check.expected, secrets)}, got ${shown(check.actual, secrets)}`;
function refusalLines(item) {
  const lines = [`  ${[item.code, item.section, item.message].filter(Boolean).join('  ')}`];
  if (item.engine_message && item.engine_message !== item.code && item.engine_message !== item.message) lines.push(`  engine: ${item.engine_message}`);
  if (item.hint) lines.push(`  ${item.hint}`);
  return lines;
}

// The terminal result of a batch (stdout).
export function renderText({ batch, rows, warnings = [], details = false, timeoutMin = 10, interrupted = false, reading = false, exitCode, secrets = [], recovery }) {
  const out = [];
  if (exitCode === 3) out.push(recovery ?? `pdd check --read ${batch}`);
  out.push(...table(rows), ...storyLines(rows).map(([, text]) => text), summaryLine(rows));
  for (const row of rows.filter(row => row.state === 'failed')) {
    out.push(`FAILED  ${row.title} (${row.test})`, ...(row.failed_checks ?? []).map(check => `  ${checkLine(check, secrets)}`),
      ...(row.warnings ?? []).map(text => `  ${text}`),
      `  Report: ${row.report_url ?? 'none'}   Next: show the person this check. Do not change the expected value yourself.`);
  }
  const local = rows.filter(row => row.state === 'refused' && !sentRow(row));
  if (local.length) {
    out.push('REFUSED before sending (not sent, 0 AI calls)');
    for (const row of local) for (const item of row.refusals) {
      out.push(`  ${row.test}${item.step ? `  step ${item.step}` : ''}  ${item.code}`, `  ${item.message}`, ...(item.hint ? [`  ${item.hint}`] : []));
    }
  }
  for (const row of rows.filter(row => row.state === 'refused' && sentRow(row))) {
    out.push(`REFUSED  ${row.title} (${row.test})`, ...row.refusals.flatMap(refusalLines), ...(row.report_url ? [`  Report: ${row.report_url}`] : []));
  }
  for (const row of rows.filter(row => row.state === 'not_run')) {
    out.push(`NOT RUN  ${row.title} (${row.test}): ${row.note?.message ?? 'pdd did not send it.'}${row.note?.code ? ` (${row.note.code})` : ''}`);
  }
  for (const row of rows.filter(row => OPEN_STATES.has(row.state))) {
    out.push(`STILL RUNNING${reading ? '' : interrupted ? ' when pdd stopped reading' : ` after ${timeoutMin} min`}: ${row.title}. Do not send it again.`);
  }
  for (const row of rows.filter(row => row.state === 'unknown' && !row.provider)) {
    out.push(`UNKNOWN  ${row.title}: the run may have executed. Its result is unknown.`, ...(row.why ? [`  ${row.why}`] : []));
  }
  for (const row of rows.filter(row => row.state === 'unknown' && row.provider)) {
    out.push(`UNKNOWN  ${row.title}: ${PROVIDER_TEXT}`, `  ${row.provider.code}${row.provider.detail ? ` (${row.provider.detail})` : ''}${row.report_url ? `  Report: ${row.report_url}` : ''}`,
      '  To try again, run `pdd check` again (a new request).');
  }
  if (details) for (const row of rows.filter(row => row.all_checks?.length)) {
    out.push(`Checks for ${row.title} (${row.test}):`,
      ...[...row.all_checks].sort((a, b) => a.passed - b.passed).map(check => `  ${check.passed ? 'passed' : 'failed'}  ${checkLine(check, secrets)}`));
  }
  const models = [...new Set(rows.map(row => row.requested_model).filter(Boolean))];
  out.push(`${rows.filter(row => row.state === 'passed').length} of ${rows.length} stories passed.${models.length ? ` Model asked for: ${models.join(', ')}.` : ''}`);
  const linked = rows.filter(row => row.report_url);
  if (linked.length) {
    const width = Math.max(...linked.map(row => row.story.length));
    out.push('Reports (anyone with a link can open it):', ...linked.map(row => `  ${row.story.padEnd(width)}  ${row.report_url}${row.draft ? '  (DRAFT)' : ''}`));
  }
  const rest = [...warnings, ...rows.filter(row => row.state !== 'failed').flatMap(row => (row.warnings ?? []).map(text => `${text} (${row.test})`))];
  out.push(...rest);
  return `${out.join('\n')}\n`;
}
