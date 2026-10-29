// Generated from prompts/cli/runtime-output.prompt.md (sha256: 415c8f638ff185f85e1e88caad824762a5602ea81b6a2a0a4d1816765777ebb6).
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

// Progress for slow steps: plain lines on stderr, the same for a person and an agent; stdout keeps the result.
export const sinceText = ms => ms < 60_000 ? `${Math.floor(ms / 1000)} s` : `${Math.floor(ms / 60_000)} min`;
export function progressTicker(stream, now, everyMs = 15_000) {
  const start = now();
  let shown = start;
  return text => { if (now() - shown < everyMs) return; shown = now(); stream.write(`${text} · ${sinceText(shown - start)}\n`); };
}
// The real reason of a tool or server error: its first line, without control characters, secrets or tokens.
const TOKENS = /\b(?:gh[pousr]_[A-Za-z0-9_]+|github_pat_[A-Za-z0-9_]+|sk-[A-Za-z0-9_-]{12,})\b|Bearer\s+\S+/g;
export const causeText = (value, secrets = []) => (String(value ?? '').split(/\r?\n/).map(text => cleanField(text, secrets)).find(Boolean) ?? '')
  .replace(TOKENS, '[secret]').slice(0, 300);
const shown = (value, secrets) => cleanField(JSON.stringify(value) ?? 'nothing', secrets);

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

// A server step deadline is execution evidence, separate from a polling deadline or a queue wait.
export function stepTimeLimit(answer, { steps = [], secrets = [] } = {}) {
  const report = answer?.result?.report, candidates = [];
  const add = (refusal, index, step) => { if (refusal && typeof refusal === 'object') candidates.push({ refusal, index, step }); };
  const refusals = Array.isArray(answer?.result?.refusals) ? answer.result.refusals : [];
  for (const refusal of refusals) add(refusal);
  add(report?.refusal);
  for (const sample of Array.isArray(report?.samples) ? report.samples : []) {
    add(sample?.refusal);
    for (const [index, step] of (Array.isArray(sample?.steps) ? sample.steps : []).entries()) add(step?.refusal, index, step?.step_id);
  }
  for (const { refusal, index, step } of candidates) {
    const cause = refusal.failure_cause ?? {}, details = refusal.details ?? {};
    const text = [cause.detail, refusal.engine_message, refusal.message].filter(value => typeof value === 'string').join(' ');
    const typed = cause.kind === 'step_timeout';
    if (!typed && !(refusal.code === 'graph-provider-failure' && (cause.kind === 'timeout' || /\b(?:timeout|timed[ -]out|time[ -]limit|deadline[ -]exceeded)\b/i.test(text)))) continue;
    const explicit = [refusal.timeout_seconds, refusal.limit_seconds, details.timeout_seconds, details.limit_seconds, cause.timeout_seconds]
      .find(value => typeof value === 'number' && Number.isFinite(value) && value > 0 && value <= 86400);
    const duration = /(?:after|timeout[=:]?|limit(?: of)?)\s*(\d+(?:\.\d+)?)\s*(seconds?|secs?|s|minutes?|mins?|m)\b/i.exec(text);
    const parsed = duration ? Number(duration[1]) * (/^m/i.test(duration[2]) ? 60 : 1) : null;
    const seconds = explicit ?? (parsed > 0 && parsed <= 86400 ? parsed : typed ? 600 : 180);
    const companions = refusals.filter(item => item?.code === refusal.code);
    const section = refusal.section ?? refusal.at ?? (companions.length === 1 ? companions[0].section ?? companions[0].at : '');
    const at = index ?? refusal.step_index ?? Number(/(?:^|\.)steps\[(\d+)\]/.exec(section)?.[1] ?? -1);
    const name = [refusal.step_id, details.step_id, refusal.step_name, step, Number.isInteger(at) && steps[at]?.step_id]
      .find(value => typeof value === 'string' && value.trim());
    const label = cleanText(name || 'unnamed step', secrets).slice(0, 200), minutes = Number((seconds / 60).toFixed(3));
    return { code: cleanText(refusal.code || 'step_timeout', secrets), step: label, minutes,
      message: `Step ${label} took more than ${minutes} minutes and was stopped.`,
      fix: 'Make the step smaller, for example split 30 moves into 3 steps of 10.' };
  }
  return null;
}

// The parts of a server answer that pdd shows.
export function projectAnswer(answer, { origin, secrets = [], steps: authoredSteps = [] } = {}) {
  const result = answer?.result ?? null, report = result?.report ?? null, time_limit = stepTimeLimit(answer, { steps: authoredSteps, secrets });
  const steps = Array.isArray(report?.samples) && Array.isArray(report.samples[0]?.steps) ? report.samples[0].steps : [];
  const all = steps.flatMap(step => Array.isArray(step?.checks) ? step.checks : []).map(check => ({
    criterion_id: cleanField(check?.criterion_id, secrets), target: cleanField(check?.target, secrets), path: cleanField(check?.path, secrets),
    expected: scrub(check?.expected, secrets), actual: scrub(check?.actual, secrets), passed: check?.passed === true }));
  // prompt-runtime #379 adds reason, fix, file, at, where and cause to each refusal; the live server may not send them yet.
  const refusals = (Array.isArray(result?.refusals) ? result.refusals : []).map(item => ({
    code: cleanText(item?.code, secrets) || 'unknown', section: cleanText(item?.section, secrets) || null,
    message: cleanText(item?.message, secrets) || null, engine_message: cleanText(item?.engine_message, secrets) || null, hint: null,
    reason: cleanText(item?.reason, secrets) || null, fix: cleanText(item?.fix, secrets) || null,
    where: cleanText(item?.where, secrets) || [item?.file, item?.at].map(part => cleanText(part, secrets)).filter(Boolean).join(' ') || null,
    cause: cleanText(item?.cause, secrets) || null }));
  const usage = answer?.usage ?? {};
  const model = [usage.requested_model, report?.evaluation?.requested_model].find(value => typeof value === 'string' && value && value !== 'unknown');
  const results = Array.isArray(report?.criterion_results) ? report.criterion_results : [];
  const cause = Array.isArray(report?.samples) ? report.samples.map(sample => sample?.refusal?.failure_cause).find(isObjectLike) : null;
  const provider = answer?.state === 'unknown' && (refusals.some(item => item.code === 'graph-provider-failure') || cause?.kind === 'transport_unknown')
    ? { code: refusals.find(item => item.code === 'graph-provider-failure')?.code ?? 'graph-provider-failure',
      detail: [cause?.kind, cause?.detail].filter(Boolean).map(text => cleanText(text, secrets)).join(', ') || null } : null;
  return {
    state: time_limit ? 'unknown' : answer?.state, time_limit, checks: all.length ? { passed: all.filter(check => check.passed).length, total: all.length } : null,
    criteria: results.length ? { passed: results.filter(item => item?.status === 'passed').length, total: results.length } : null,
    all_checks: all, failed_checks: all.filter(check => !check.passed).map(({ passed, ...check }) => check), refusals,
    calls: typeof usage.calls === 'number' ? usage.calls : 'unknown', requested_model: model ? cleanText(model, secrets) : null,
    server_seconds: typeof usage.seconds === 'number' ? usage.seconds : null,
    report_url: validLink(answer?.report_url, origin, 'report'), why: result?.why ? cleanText(result.why, secrets) : null,
    engine_sha: typeof answer?.engine_sha === 'string' ? answer.engine_sha : null, provider: time_limit ? null : provider,
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
      message: item.message ?? null, engine_message: item.engine_message ?? null, hint: item.hint ?? null, reason: item.reason ?? null, fix: item.fix ?? null,
      where: item.where ?? null, cause: item.cause ?? null })), calls: sentRow(row) ? row.calls ?? 'unknown' : 0,
    seconds: round(row.seconds), requested_model: row.requested_model ?? null, report_url: row.report_url ?? null,
    request_id: row.request_ids?.at(-1) ?? null, draft: !!row.draft, busy: !!row.busy, can_retry: !!row.can_retry, time_limit: row.time_limit ?? null,
    reason: row.time_limit ? { code: row.time_limit.code, message: `${row.time_limit.message} ${row.time_limit.fix}` } : row.provider ? { code: row.provider.code, message: PROVIDER_TEXT } : row.note ?? (row.why ? { code: null, message: row.why } : null) };
}

export function renderJson({ batch = null, repo, sourceSha256 = null, coverage, rows, warnings = [], exitCode, summaryLine: line = summaryLine(rows) }) {
  const perStory = new Map(storyLines(rows).map(([story, text]) => [story, text]));
  return { batch, repo, ...(coverage ? { coverage } : {}), source_sha256: sourceSha256, exit_code: exitCode, summary_line: line, draft: rows.some(row => row.draft),
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
  const bad = rows.some(row => ['failed', 'refused', 'not_run'].includes(row.state) && !row.busy);
  const mark = rows.length && rows.every(row => row.state === 'passed') ? '✓' : bad ? '✗'
    : rows.some(row => OPEN_STATES.has(row.state)) ? 'running ·' : rows.some(row => row.state === 'unknown') ? 'unknown ·' : rows.some(row => row.busy) ? 'busy ·' : 'unknown ·';
  return [`Runtime check${story ? ` (${story})` : ''}${rows.some(row => row.draft) ? ' (DRAFT)' : ''}: ${mark} ${criteria.passed} of ${count(criteria.total, 'criterion').replace(/criterions$/, 'criteria')}`,
    `${checks.passed}/${checks.total} checks`, ...others, `${count(calls, 'AI call')}${unknownCalls ? ` + ${unknownCalls} unknown` : ''}`].join(' · ');
}

function table(rows) {
  const lines = [['Story', 'Test', 'Result', 'Checks', 'Time'], ...rows.map(row => [row.title ?? row.story, row.test,
    `${row.busy ? 'busy (not run)' : RESULT_WORDS[row.state] ?? row.state}${row.draft ? ' (DRAFT)' : ''}`, row.checks ? `${row.checks.passed}/${row.checks.total}` : '-',
    typeof row.seconds === 'number' ? `${round(row.seconds).toFixed(1)} s` : '-'])];
  const widths = lines[0].map((_, column) => Math.max(...lines.map(line => line[column].length)));
  return lines.map(line => line.map((cell, column) => column === line.length - 1 ? cell : cell.padEnd(widths[column])).join('  ').trimEnd());
}

// ---- Expected and got (round-2 tester: a CLI's stdout lost its line breaks and was cut near the difference) ----
const VALUE_LINES = 20;
// One line of a value: no control characters and no token, but its spaces stay.
const plainLine = (text, secrets) => secrets.reduce((value, secret) => secret ? value.split(secret).join('[secret]') : value,
  text.replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '').replace(/[\x00-\x08\x0b-\x1f\x7f-\x9f]/g, ' '));
const oneLine = value => typeof value !== 'string' || !/\n(?!$)/.test(value);
const valueLines = value => typeof value === 'string' ? value.replace(/\n$/, '').split('\n') : (JSON.stringify(value, null, 2) ?? 'nothing').split('\n');

// The check line: one line when both values fit, else the check and a block for each value, never cut inside a line.
function checkLines(check, secrets) {
  const head = `${check.criterion_id}  ${check.target} ${check.path}`;
  const fits = [check.expected, check.actual].every(value => oneLine(value) && shown(value, secrets).length <= 80);
  if (fits) return [`${head}  expected ${shown(check.expected, secrets)}, got ${shown(check.actual, secrets)}`];
  const expected = valueLines(check.expected), actual = valueLines(check.actual);
  // Start 2 lines before the first line where two strings differ, when it is past the first 20.
  const differ = typeof check.expected === 'string' && typeof check.actual === 'string' ? expected.findIndex((text, index) => text !== actual[index]) : -1;
  const from = differ >= VALUE_LINES ? differ - 2 : 0;
  const block = (word, value, lines) => [`  ${word}:`, ...(from ? [`    … ${from} lines before`] : []),
    ...lines.slice(from, from + VALUE_LINES).map(text => `    ${plainLine(text, secrets)}`),
    ...(lines.length > from + VALUE_LINES ? [`    … ${lines.length - from - VALUE_LINES} more lines in the report`] : []),
    ...(typeof value === 'string' && value.endsWith('\n') ? ['    (ends with a line break)'] : [])];
  return [head, ...block('expected', check.expected, expected), ...block('got', check.actual, actual)];
}
// With a plain reason (#379): the reason, where and the fix; an AI service failure is not a problem in the test.
function refusalLines(item) {
  const lines = item.reason ? [`  ${item.code}: ${item.reason}`, ...(item.where ? [`  Where: ${item.where}`] : []),
    ...(item.cause === 'ai-service' ? ['  Your test is fine. Run it again.'] : item.fix ? [`  Fix: ${item.fix}`] : [])]
    : [`  ${[item.code, item.section, item.message].filter(Boolean).join('  ')}`];
  if (!item.reason && item.engine_message && item.engine_message !== item.code && item.engine_message !== item.message) lines.push(`  engine: ${item.engine_message}`);
  if (item.hint) lines.push(`  ${item.hint}`);
  return lines;
}

function localRefusals(rows) {
  const local = rows.filter(row => row.state === 'refused' && !sentRow(row)), out = [];
  if (local.length) {
    out.push('REFUSED before sending (not sent, 0 AI calls)');
    for (const row of local) for (const item of row.refusals) {
      out.push(`  ${row.test}${item.step ? `  step ${item.step}` : ''}  ${item.code}`, `  ${item.message}`, ...(item.hint ? [`  ${item.hint}`] : []));
    }
  }
  return out;
}

// The terminal result of a batch (stdout).
export function renderText({ batch, rows, coverage, warnings = [], details = false, timeoutMin = null, interrupted = false, reading = false, exitCode, secrets = [], recovery }) {
  const out = [];
  if (exitCode === 3) out.push(recovery ?? `pdd check --read ${batch}`);
  // One Story: its own line is the result; the overall line comes only with two or more Stories.
  const perStory = storyLines(rows).map(([, text]) => text);
  out.push(...table(rows), ...(perStory.length === 1 ? perStory : [...perStory, summaryLine(rows)]));
  for (const row of rows.filter(row => row.state === 'failed')) {
    out.push(`FAILED  ${row.title} (${row.test})`, ...(row.failed_checks ?? []).flatMap(check => checkLines(check, secrets).map(text => `  ${text}`)),
      ...(row.warnings ?? []).map(text => `  ${text}`),
      `  Report: ${row.report_url ?? 'none'}   Next: show the person this check. Do not change the expected value yourself.`);
  }
  out.push(...localRefusals(rows));
  for (const row of rows.filter(row => row.state === 'refused' && sentRow(row))) {
    out.push(`REFUSED  ${row.title} (${row.test})`, ...row.refusals.flatMap(refusalLines), ...(row.report_url ? [`  Report: ${row.report_url}`] : []));
  }
  for (const row of rows.filter(row => row.state === 'not_run')) {
    out.push(`NOT RUN  ${row.title} (${row.test}): ${row.note?.message ?? 'pdd did not send it.'}${row.note?.code ? ` (${row.note.code})` : ''}`);
  }
  for (const row of rows.filter(row => OPEN_STATES.has(row.state))) {
    const limit = Number.isInteger(timeoutMin) ? `${timeoutMin} min` : `${Math.round(timeoutMin * 60)} s`;
    out.push(`STILL RUNNING${reading || (!interrupted && !timeoutMin) ? '' : interrupted ? ' when pdd stopped reading' : ` after ${limit}`}: ${row.title}. Do not send it again.`);
  }
  for (const row of rows.filter(row => row.state === 'unknown' && !row.provider && !row.time_limit)) {
    out.push(`UNKNOWN  ${row.title}: the run may have executed. Its result is unknown.`, ...(row.why ? [`  ${row.why}`] : []));
  }
  for (const row of rows.filter(row => row.time_limit)) {
    out.push(`STOPPED  ${row.title}: ${row.time_limit.message}`, `  ${row.time_limit.fix}`,
      ...(row.report_url ? [`  Report: ${row.report_url}`] : []));
  }
  for (const row of rows.filter(row => row.state === 'unknown' && row.provider)) {
    out.push(`UNKNOWN  ${row.title}: ${PROVIDER_TEXT}`, `  ${row.provider.code}${row.provider.detail ? ` (${row.provider.detail})` : ''}${row.report_url ? `  Report: ${row.report_url}` : ''}`,
      '  To try again, run `pdd check` again (a new request).');
  }
  if (details) for (const row of rows.filter(row => row.all_checks?.length)) {
    out.push(`Checks for ${row.title} (${row.test}):`,
      ...[...row.all_checks].sort((a, b) => a.passed - b.passed).flatMap(check => checkLines(check, secrets)
        .map((text, index) => index ? `  ${text}` : `  ${check.passed ? 'passed' : 'failed'}  ${text}`)));
  }
  if (coverage) out.push(coverageText(coverage));
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

// Owner-provided Try accounting is separate from a program's stdout/body and from account-wide allowances.
export function tryUsage(answer, { cap } = {}) {
  const number = value => Number.isSafeInteger(value) && value >= 0 ? value : 'unknown';
  const total = number(answer?.calls?.cap ?? answer?.result?.session?.max_calls ?? cap);
  const remaining = number(answer?.calls?.remaining ?? answer?.result?.session?.remaining_calls ?? answer?.result?.report?.remaining_calls);
  return { calls: number(answer?.usage?.calls), remaining, cap: total,
    used: typeof total === 'number' && typeof remaining === 'number' && remaining <= total ? total - remaining : 'unknown' };
}
export function tryUsageLine(usage, { command = false } = {}) {
  return `Try AI usage: ${command ? `${usage.calls} this command · ` : ''}${usage.used} used · ${usage.remaining} remaining (session cap ${usage.cap}).`;
}
export function tryUsageHeaders(usage) {
  return { 'x-pdd-ai-calls': String(usage.calls), 'x-pdd-try-used': String(usage.used),
    'x-pdd-try-remaining': String(usage.remaining), 'x-pdd-try-cap': String(usage.cap) };
}

export function coverageText(coverage) {
  if (!coverage?.available) return 'Module binding coverage unavailable: no pdd-bindings.json.';
  return [`${coverage.bound} of ${coverage.total} modules bound`, ...coverage.modules.filter(m => m.state === 'unbound').map(m => `  ${m.path}: ${m.reason} Port attempted: ${m.port_attempt}`)].join('\n');
}
