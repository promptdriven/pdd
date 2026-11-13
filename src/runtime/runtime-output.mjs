import { bindingRefusals } from './runtime-binding-plan.mjs';
// Generated from prompts/cli/runtime-output.prompt.md (sha256: 0d8c32400b35939d17c43a8be209d99602ccadbae81543bdffbdb8e64e57667d).
import { hasProgress, outcomeFor, outcomeText, progressText, resultOutcome, PROVIDER_TEXT } from './runtime-outcome.mjs';
export const OPEN_STATES = new Set(['queued', 'running', 'sent']);

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

// One server refusal as pdd shows it, cleaned; each field is null when missing.
export const refusalView = (item, secrets = []) => ({
  code: cleanText(item?.code, secrets) || 'unknown', path: cleanText(item?.file ?? item?.path, secrets) || null,
  field: cleanText(item?.field ?? item?.at ?? item?.section, secrets) || null, section: cleanText(item?.section, secrets) || null,
  message: cleanText(item?.message, secrets) || null, engine_message: cleanText(item?.engine_message, secrets) || null, hint: null,
  reason: cleanText(item?.reason, secrets) || null, fix: cleanText(item?.fix, secrets) || null,
  where: cleanText(item?.where, secrets) || [item?.file, item?.at].map(part => cleanText(part, secrets)).filter(Boolean).join(' ') || null,
  cause: cleanText(item?.cause, secrets) || null });

// Attribute only direct authored references backed by this sample's raw error.
function predecessorErrors(refusal, report, steps, secrets) {
  if (typeof refusal?.section !== 'string') return [];
  const anchor = /^samples\[(\d+)\]\.steps\[(\d+)\]$/.exec(refusal?.section);
  if (!anchor || !Array.isArray(steps) || !Array.isArray(report?.samples)) return [];
  const sampleIndex = Number(anchor[1]), index = Number(anchor[2]);
  if (!Number.isSafeInteger(sampleIndex) || !Number.isSafeInteger(index)) return [];
  const reported = report.samples[sampleIndex]?.steps, dependent = steps[index];
  if (!Array.isArray(reported) || !isObjectLike(dependent) || !Object.hasOwn(dependent, 'input')) return [];
  // A relative location can corroborate this anchor, but cannot select a sample.
  for (const location of [refusal.at, refusal.field, refusal.where]) {
    if (location == null) continue;
    if (typeof location !== 'string') return [];
    let conflict = false;
    const remainder = location.replace(/(?:samples\[(\d+)\]\.)?steps\[(\d+)\]/g, (text, sample, step) => {
      if (Number(step) !== index || sample !== undefined && Number(sample) !== sampleIndex) conflict = true;
      return '';
    });
    if (conflict || /\b(?:samples|steps)\[/.test(remainder)) return [];
  }
  const safe = (value, pointers = false) => {
    let text = String(value ?? '').replace(/\x1b\[[0-9;?]*[ -/]*[@-~]/g, '').replace(/[\x00-\x1f\x7f-\x9f]/g, '');
    for (const secret of secrets) if (secret) text = text.split(secret).join('[secret]');
    text = text.replace(TOKENS, '[secret]');
    // Pointer spaces name members. Host paths in identities/codes need no word delimiter.
    return pointers ? text : text.replace(/\/(?:home|Users|srv|var|tmp|private|opt|mnt|workspace|usr|etc)\/[^\s"'<>)\]]*/g, '<server path>').trim();
  };
  const identity = value => typeof value === 'string' && value.trim() && safe(value)
    && !/^(?:\[(?:secret|redacted)\]|<(?:secret|redacted|server path)>|redacted|\*+)$/i.test(safe(value));
  const id = dependent.step_id;
  if (!identity(id) || steps.filter(step => step?.step_id === id).length !== 1) return [];
  if (reported[index] !== undefined && reported[index]?.step_id !== id) return [];
  if (reported.some((step, at) => step?.step_id === id && at !== index)) return [];
  const facts = [];
  const pending = [{ value: dependent.input, path: '' }];
  while (pending.length) {
    const { value, path } = pending.pop();
    if (!value || typeof value !== 'object') continue;
    const ref = value.$step_result;
    if (isObjectLike(value) && Object.keys(value).length === 1 && isObjectLike(ref)
      && Object.keys(ref).length === 2 && Object.hasOwn(ref, 'step_id') && Object.hasOwn(ref, 'path')
      && typeof ref.path === 'string' && identity(ref.step_id)) {
      const authored = steps.map((step, at) => ({ step, at })).filter(({ step }) => step?.step_id === ref.step_id);
      const matches = reported.filter(step => step?.step_id === ref.step_id);
      if (authored.length !== 1 || authored[0].at >= index || matches.length !== 1) continue;
      const predecessor = matches[0];
      if (predecessor.result != null || !identity(predecessor.error?.code)) continue;
      facts.push({ step_id: safe(id), input_path: safe(path, true), predecessor_step_id: safe(ref.step_id),
        result_path: safe(ref.path, true), error_code: safe(predecessor.error.code) });
      continue;
    }
    const children = Object.entries(value);
    // Reverse stack insertion keeps authored object/array traversal order.
    for (let at = children.length - 1; at >= 0; at--) {
      const [key, item] = children[at];
      pending.push({ value: item, path: `${path}/${key.replaceAll('~', '~0').replaceAll('/', '~1')}` });
    }
  }
  return facts;
}

// The parts of a server answer that pdd shows.
export function projectAnswer(answer, { origin, secrets = [], steps: authoredSteps = [], criterionTexts = {}, test, sourceFiles, capacityUncertain = false } = {}) {
  const result = answer?.result ?? null, report = result?.report ?? null, time_limit = stepTimeLimit(answer, { steps: authoredSteps, secrets });
  const outcome = outcomeFor(answer, { test, steps: authoredSteps, timeLimit: !!time_limit, sourceFiles, capacityUncertain });
  const safeCompatibility = (value, key = '') => typeof value === 'string'
    ? /^(?:path|prompt_path|target_path)$/.test(key) && /^(?:\/|[A-Za-z]:[\\/])/.test(value) ? '<server path>' : cleanText(value, secrets).replace(TOKENS, '[secret]')
    : Array.isArray(value) ? value.map(item => safeCompatibility(item, key))
    : isObjectLike(value) ? Object.fromEntries(Object.entries(value).map(([key, item]) => [key, safeCompatibility(item, key)])) : value;
  const advice = reason => {
    if (reason === 'binding-missing') return { owner: 'application/binding author', next_step: 'Run pdd test --explain-bindings STORY. Fix the fixture resource/operation name, add the named binding, or declare the Story Runtime boundary. If the exact fixture is selected, ask the compatibility owner to diagnose the refusal before retrying.' };
    if (['source-mismatch', 'source-admission-refused'].includes(reason)) return { owner: 'source/prompt author', next_step: 'Repair the reported source/admission problem.' };
    if (['retained-attachment-unsupported', 'retained-mutation-unsupported', 'runtime-mode-unsupported'].includes(reason))
      return { owner: 'interpreter owner', next_step: 'Review the unsupported capability or mode.' };
    if (reason === 'engine-build-unknown') return { owner: 'interpreter deployment owner', next_step: 'Identify the executing build.' };
    if (reason === 'supported') return { owner: 'application author', next_step: 'Behavioral execution remains required. Installed-engine, host/profile and physical-observation proof remains unproved.' };
    return { owner: 'unresolved', next_step: reason === 'capability-association-mismatch'
      ? 'Review captured source and interpreter deployment identity.' : 'Review the source and interpreter evidence.' };
  };
  const compatibility = outcome.compatibility ? safeCompatibility(outcome.compatibility) : null;
  if (compatibility?.reported) for (const row of [...(compatibility.reported.operations ?? []), ...(compatibility.reported.edges ?? [])])
    row.client_advice = advice(row.reason_code);
  const client_advice = compatibility ? advice(compatibility.issue ?? (compatibility.state === 'supported' ? 'supported'
    : [...(compatibility.reported?.operations ?? []), ...(compatibility.reported?.edges ?? [])].find(row => row.verdict === compatibility.state)?.reason_code)) : null;
  const steps = Array.isArray(report?.samples) && Array.isArray(report.samples[0]?.steps) ? report.samples[0].steps : [];
  const nonNegativeInt = value => Number.isSafeInteger(value) && value >= 0 ? value : undefined;
  const rerunStep = item => ({
    step_id: cleanField(item.step_id, secrets) || null,
    ...(nonNegativeInt(item.runs) !== undefined ? { runs: nonNegativeInt(item.runs) } : {}),
    ...(nonNegativeInt(item.failed) !== undefined ? { failed: nonNegativeInt(item.failed) } : {}),
    ...(item.stable === true ? { stable: true } : {}),
    ...(Array.isArray(item.changed_paths) ? { changed_paths: item.changed_paths.map(path => cleanField(path, secrets)) } : {}) });
  const rerun = isObjectLike(report?.rerun) ? {
    ...(nonNegativeInt(report.rerun.calls) !== undefined ? { calls: nonNegativeInt(report.rerun.calls) } : {}),
    ...(typeof report.rerun.skipped === 'string' ? { skipped: cleanField(report.rerun.skipped, secrets) } : {}),
    ...(Array.isArray(report.rerun.steps) ? { steps: report.rerun.steps.filter(isObjectLike).map(rerunStep) } : {}) } : null;
  const all = steps.flatMap((step, index) => Array.isArray(step?.checks) ? step.checks.map(check => ({ step, check, index })) : []).map(({ step, check, index }) => {
    const criterion_id = cleanField(check?.criterion_id, secrets), diagnosis = isObjectLike(check?.diagnosis) ? {
      kind: cleanText(check.diagnosis.kind, secrets) || null, who: cleanText(check.diagnosis.who, secrets) || null,
      why: cleanText(check.diagnosis.why, secrets) || null, next_step: cleanText(check.diagnosis.next_step, secrets) || null,
      evidence: Array.isArray(check.diagnosis.evidence) ? check.diagnosis.evidence.map(item => cleanText(item, secrets)).filter(Boolean) : undefined,
      likely: check.diagnosis.likely === true ? true : undefined,
      ...(isObjectLike(check.diagnosis.rerun) ? { rerun: rerunStep(check.diagnosis.rerun) } : {}) } : null;
    const ref_target = typeof check?.ref_target === 'string' && check.ref_target ? cleanField(check.ref_target, secrets) : undefined;
    const ref_path = typeof check?.ref_path === 'string' ? cleanField(check.ref_path, secrets) : undefined;
    const ref_json_path = typeof check?.ref_json_path === 'string' ? cleanField(check.ref_json_path, secrets) : undefined;
    return { criterion_id, step_id: cleanField(step?.step_id, secrets) || cleanField(authoredSteps[index]?.step_id, secrets) || null,
      criterion_text: typeof criterionTexts[criterion_id] === 'string' && criterionTexts[criterion_id].length <= 160 ? cleanField(criterionTexts[criterion_id], secrets) : null,
      target: cleanField(check?.target, secrets), path: cleanField(check?.path, secrets),
      ...(ref_target !== undefined ? { op: cleanField(check?.op, secrets), ref_target, ...(ref_path !== undefined ? { ref_path } : {}), ...(ref_json_path !== undefined ? { ref_json_path } : {}) } : {}),
      expected: scrub(check?.expected, secrets),
      actual: scrub(check?.actual, secrets), passed: check?.passed === true,
      normal_result: Object.prototype.hasOwnProperty.call(step ?? {}, 'result') && !step?.error, ...(diagnosis ? { diagnosis } : {}) };
  });
  // prompt-runtime #379 adds reason, fix, file, at, where and cause to each refusal; the live server may not send them yet.
  const refusals = (Array.isArray(result?.refusals) ? result.refusals : []).map(item => {
    const view = refusalView(item, secrets);
    const facts = answer?.command === 'check' && ['passed', 'failed', 'refused'].includes(answer?.state)
      ? predecessorErrors(item, report, authoredSteps, secrets) : [];
    return { ...view, ...(facts.length ? { dependency_errors: facts } : {}) };
  });
  const usage = answer?.usage ?? {};
  const accountingSurfaces = [answer, usage, result, report].filter(isObjectLike);
  const accountingValues = key => accountingSurfaces.filter(surface => Object.hasOwn(surface, key)).map(surface => nonNegativeInt(surface[key]));
  const accountingKeys = ['calls', 'known_calls', 'unknown_calls', 'provider_calls'];
  const invalidCounter = accountingKeys.some(key => accountingValues(key).some(value => value === undefined));
  const conflictingCounters = accountingKeys.some(key => new Set(accountingValues(key).filter(value => value !== undefined)).size > 1);
  const flags = [[answer, 'accounting_complete'], [usage, 'accounting_complete'], [result, 'accounting_complete'], [report, 'accounting_complete']]
    .filter(([source, key]) => source && Object.hasOwn(source, key)).map(([source, key]) => source[key]);
  const invalidFlag = flags.some(value => typeof value !== 'boolean'), conflictingFlags = new Set(flags.filter(value => typeof value === 'boolean')).size > 1;
  const usageCalls = nonNegativeInt(usage.calls);
  const knownValues = accountingValues('known_calls').filter(value => value !== undefined);
  const callValues = accountingValues('calls').filter(value => value !== undefined);
  const providerValues = accountingValues('provider_calls').filter(value => value !== undefined);
  const providerCalls = providerValues.length ? Math.max(...providerValues) : undefined;
  const unknownValues = accountingValues('unknown_calls').filter(value => value !== undefined);
  const reportedUnknown = Math.max(...unknownValues, 0);
  const deductedTotals = [...callValues, ...providerValues].map(value => Math.max(0, value - reportedUnknown));
  const knownCalls = knownValues.length ? Math.max(...knownValues, 0) : Math.max(...deductedTotals, 0);
  const incomplete = capacityUncertain || invalidCounter || conflictingCounters || invalidFlag || conflictingFlags || flags.includes(false)
    || reportedUnknown > 0 || usageCalls === undefined || knownCalls > usageCalls
    || (providerCalls !== undefined && providerCalls > usageCalls);
  const unknownCalls = incomplete ? Math.max(1, reportedUnknown) : 0;
  const model = [usage.requested_model, report?.evaluation?.requested_model].find(value => typeof value === 'string' && value && value !== 'unknown');
  const results = Array.isArray(report?.criterion_results) ? report.criterion_results : [];
  const cause = Array.isArray(report?.samples) ? report.samples.map(sample => sample?.refusal?.failure_cause).find(isObjectLike) : null;
  const provider = answer?.state === 'unknown' && (refusals.some(item => item.code === 'graph-provider-failure') || cause?.kind === 'transport_unknown')
    ? { code: refusals.find(item => item.code === 'graph-provider-failure')?.code ?? 'graph-provider-failure',
      detail: [cause?.kind, cause?.detail].filter(Boolean).map(text => cleanText(text, secrets)).join(', ') || null } : null;
  const rawRefusals = Array.isArray(result?.refusals) && result.refusals.length ? result.refusals : [report?.refusal];
  const busyRefusal = outcome.state === 'not_run' && outcome.retryable === true && answer?.command === 'check'
    ? rawRefusals.find(item => item?.retryable === true || item?.details?.retryable === true) : null;
  const tokens = tokenUsageOf(answer, { incomplete });
  return {
    ...(compatibility ? { compatibility, client_advice } : {}),
    busy_display: busyRefusal ? { max_wait_seconds: busyRefusal.max_wait_seconds } : null,
    state: outcome.state, ...(outcome.progress ? { progress: { ...outcome.progress, ...(typeof outcome.progress.step === 'string' ? { step: cleanText(outcome.progress.step, secrets) } : {}) } } : {}),
    ...(outcome.ahead !== undefined ? { ahead: outcome.ahead } : {}),
    note: outcome.state === 'not_run' ? { code: cleanText(outcome.code, secrets) || null, message: cleanText(outcome.message, secrets) || null } : null,
    time_limit, checks: all.length ? { passed: all.filter(check => check.passed).length, total: all.length } : null,
    criteria: results.length ? { passed: results.filter(item => item?.status === 'passed').length, total: results.length } : null,
    all_checks: all, failed_checks: all.filter(check => !check.passed).map(({ passed, ...check }) => check), refusals,
    calls: !incomplete ? usageCalls : 'unknown',
    ...tokens,
    ...(incomplete ? { known_calls: knownCalls } : {}), unknown_calls: unknownCalls, accounting_complete: !incomplete, requested_model: model ? cleanText(model, secrets) : null,
    server_seconds: typeof usage.seconds === 'number' ? usage.seconds : null,
    report_url: validLink(answer?.report_url, origin, 'report'), why: result?.why ? cleanText(result.why, secrets) : null,
    who: result?.who ? cleanText(result.who, secrets) : null, next_step: result?.next_step ? cleanText(result.next_step, secrets) : null,
    rerun,
    engine_sha: typeof answer?.engine_sha === 'string' ? answer.engine_sha : null, provider: time_limit ? null : provider,
    // The server's list of draft prompts (prompt-runtime #365) wins over pdd's local guess; null when the server has none.
    draft: Array.isArray(answer?.draft_prompts) ? answer.draft_prompts.length > 0 : null };
}

const isObjectLike = value => value !== null && typeof value === 'object' && !Array.isArray(value);
export { PROVIDER_TEXT } from './runtime-outcome.mjs';
const round = seconds => typeof seconds === 'number' ? Math.round(seconds * 10) / 10 : null;
const sentRow = row => row.phase === 'server' || !!row.request_id || row.state === 'sent';
const tokenInt = value => Number.isSafeInteger(value) && value >= 0 ? value : undefined;
const absentToken = value => value === undefined || value === null || value === 'unknown';
const malformedToken = value => !absentToken(value) && tokenInt(value) === undefined;
const shareOf = (input, cached) => typeof input === 'number' && typeof cached === 'number' && input > 0 && cached <= input ? cached / input : null;
const unknownTokens = () => ({ input_tokens: 'unknown', cached_input_tokens: 'unknown', output_tokens: 'unknown', cached_input_share: null });
const formatPromptCacheTokens = usage => {
  if (typeof usage?.input_tokens !== 'number' || typeof usage?.cached_input_tokens !== 'number' || usage.cached_input_tokens > usage.input_tokens) return null;
  const share = shareOf(usage.input_tokens, usage.cached_input_tokens);
  const pct = share !== null ? `, ${(share * 100).toFixed(1)}%` : '';
  const out = typeof usage.output_tokens === 'number' ? ` · ${usage.output_tokens} output` : '';
  return `${usage.input_tokens} input (${usage.cached_input_tokens} cached${pct})${out}`;
};

export function tokenUsageOf(answer, { incomplete = false } = {}) {
  const usage = isObjectLike(answer?.usage) ? answer.usage : {};
  const result = isObjectLike(answer?.result) ? answer.result : {};
  const report = isObjectLike(result.report) ? result.report : null;
  const topReport = isObjectLike(answer?.report) ? answer.report : null;
  const surfaces = [answer, usage, result, report, topReport].filter(isObjectLike);
  if (incomplete || surfaces.some(s => Object.hasOwn(s, 'accounting_complete') && s.accounting_complete !== true)) return unknownTokens();
  if (surfaces.some(s => ['not_started', 'pre-dispatch'].includes(s.dispatch) || s.dispatch_state === 'pre-dispatch')) return unknownTokens();
  if (['input_tokens', 'cached_input_tokens', 'output_tokens'].some(key => malformedToken(usage[key]))) return unknownTokens();
  const uIn = tokenInt(usage.input_tokens), uCached = tokenInt(usage.cached_input_tokens), uOut = tokenInt(usage.output_tokens);
  if (uIn !== undefined && uCached !== undefined && uCached > uIn) return unknownTokens();
  const modelUsage = report?.model_usage ?? topReport?.model_usage;
  let muIn, muCached, muOut;
  if (modelUsage !== undefined && modelUsage !== null) {
    if (!isObjectLike(modelUsage)) return unknownTokens();
    const totals = isObjectLike(modelUsage.totals) ? modelUsage.totals : null;
    const complete = totals && Object.hasOwn(totals, 'complete') ? totals.complete : Object.hasOwn(modelUsage, 'complete') ? modelUsage.complete : undefined;
    const cov = isObjectLike(modelUsage.coverage) ? modelUsage.coverage : null;
    if (complete === false || (complete !== undefined && typeof complete !== 'boolean')
      || cov?.accounting_incomplete === true
      || (Number.isSafeInteger(cov?.unobserved_current_calls) && cov.unobserved_current_calls > 0)) return unknownTokens();
    if (totals) {
      if (['input_tokens', 'cached_input_tokens', 'output_tokens'].some(key => malformedToken(totals[key]))) return unknownTokens();
      const shareRaw = totals.cached_input_share;
      if (shareRaw !== undefined && shareRaw !== null && !(typeof shareRaw === 'number' && Number.isFinite(shareRaw) && shareRaw >= 0 && shareRaw <= 1)) return unknownTokens();
    }
    const tIn = totals ? tokenInt(totals.input_tokens) : tokenInt(modelUsage.input_tokens);
    const tCached = totals ? tokenInt(totals.cached_input_tokens) : tokenInt(modelUsage.cached_input_tokens);
    const tOut = totals ? tokenInt(totals.output_tokens) : tokenInt(modelUsage.output_tokens);
    if (tIn !== undefined && tCached !== undefined && tCached > tIn) return unknownTokens();
    if (Array.isArray(modelUsage.calls)) {
      if (modelUsage.calls.some(call => !isObjectLike(call))) return unknownTokens();
      const current = modelUsage.calls.filter(call => (call.origin ?? 'current') === 'current');
      const dispatched = current.filter(call => call.dispatch_state !== 'pre-dispatch');
      if (current.length > 0 && dispatched.length === 0) return unknownTokens();
      if (dispatched.some(call => call.dispatch_state === 'transport-uncertain' || call.usage_status === 'unknown'
        || tokenInt(call.input_tokens) === undefined || tokenInt(call.cached_input_tokens) === undefined
        || call.cached_input_tokens > call.input_tokens || malformedToken(call.output_tokens))) return unknownTokens();
      if (modelUsage.calls.length > 0) {
        const cIn = dispatched.reduce((sum, call) => sum + call.input_tokens, 0);
        const cCached = dispatched.reduce((sum, call) => sum + call.cached_input_tokens, 0);
        const allCurrent = modelUsage.calls.every(call => (call.origin ?? 'current') === 'current');
        if (allCurrent && ((tIn !== undefined && tIn !== cIn) || (tCached !== undefined && tCached !== cCached))) return unknownTokens();
        muIn = cIn;
        muCached = cCached;
        if (dispatched.length > 0 && dispatched.every(call => tokenInt(call.output_tokens) !== undefined)) {
          muOut = dispatched.reduce((sum, call) => sum + call.output_tokens, 0);
        }
      } else if (complete === true) {
        muIn = tIn ?? 0;
        muCached = tCached ?? 0;
        muOut = tOut;
      }
    } else if (complete === true) {
      if (tIn === undefined || tCached === undefined) return unknownTokens();
      muIn = tIn;
      muCached = tCached;
      muOut = tOut;
    } else return unknownTokens();
  }
  const input_tokens = muIn ?? uIn ?? 'unknown';
  const cached_input_tokens = muCached ?? uCached ?? 'unknown';
  const output_tokens = muOut ?? uOut ?? 'unknown';
  if (typeof input_tokens === 'number' && typeof cached_input_tokens === 'number' && cached_input_tokens > input_tokens) return unknownTokens();
  return { input_tokens, cached_input_tokens, output_tokens, cached_input_share: shareOf(input_tokens, cached_input_tokens) };
}

function criterionCoverage(row) {
  if (!Array.isArray(row.steps)) return null;
  const counts = new Map(Object.keys(row.criterion_texts ?? {}).map(id => [id, []]));
  for (const step of row.steps) {
    if (!isObjectLike(step) || !Array.isArray(step.checks)) return null;
    for (const check of step.checks) {
      if (!isObjectLike(check) || typeof check.criterion_id !== 'string' || !check.criterion_id.trim()
        || typeof check.target !== 'string' || typeof check.path !== 'string') return null;
      if (!counts.has(check.criterion_id)) counts.set(check.criterion_id, []);
      counts.get(check.criterion_id).push(check);
    }
  }
  return [...counts].map(([criterion_id, checks]) => ({ criterion_id, check_count: checks.length,
    exit_code_only: checks.length > 0 && checks.every(check => check.target === 'result' && ['/exit_code', '/exitCode'].includes(check.path)) }));
}

export function jsonRow(row) {
  const publicChecks = checks => (checks ?? []).map(({ normal_result, ...check }) => check);
  const rowTokens = row.cached
    ? { input_tokens: 0, cached_input_tokens: 0, output_tokens: 0, cached_input_share: null }
    : (() => {
        const input_tokens = tokenInt(row.input_tokens) ?? 'unknown';
        const cached_input_tokens = tokenInt(row.cached_input_tokens) ?? 'unknown';
        const output_tokens = tokenInt(row.output_tokens) ?? 'unknown';
        if (typeof input_tokens === 'number' && typeof cached_input_tokens === 'number' && cached_input_tokens > input_tokens) return unknownTokens();
        return { input_tokens, cached_input_tokens, output_tokens, cached_input_share: shareOf(input_tokens, cached_input_tokens) };
      })();
  return { story: row.story, title: row.title, test: row.test, ...(row.native_only?.length ? {native_only:row.native_only} : {}), ...resultOutcome(row), ...(row.unsent ? {unsent:true} : {}), ...(row.not_checked?.length ? {not_checked:row.not_checked} : {}), ...(row.binding_plan ? {binding_plan:row.binding_plan,binding_diagnostics:bindingRefusals(row.binding_plan,row.compatibility)} : {}), ...(row.compatibility ? { compatibility: row.compatibility, client_advice: row.client_advice } : {}), criterion_coverage: criterionCoverage(row), ...(row.progress ? { progress: row.progress } : {}), ...(row.ahead !== undefined && row.ahead !== null ? { ahead: row.ahead } : {}), checks: row.checks ?? null, criteria: row.criteria ?? null,
    failed_checks: publicChecks(row.failed_checks), refusals: (row.refusals ?? []).map(item => ({ code: item.code, ...(item.path ? { path: item.path } : {}), field: item.field ?? null, section: item.section ?? null,
      message: item.message ?? null, engine_message: item.engine_message ?? null, hint: item.hint ?? null, reason: item.reason ?? null, fix: item.fix ?? null,
      where: item.where ?? null, cause: item.cause ?? null,
      ...(item.dependency_errors?.length ? { dependency_errors: item.dependency_errors } : {}) })), calls: sentRow(row) ? row.calls ?? 'unknown' : 0,
    ...rowTokens,
    seconds: round(row.seconds), requested_model: row.requested_model ?? null, report_url: row.report_url ?? null,
    ...(row.accounting_complete !== undefined ? { known_calls: row.known_calls ?? null, unknown_calls: row.unknown_calls ?? 0, accounting_complete: row.accounting_complete } : {}),
    request_id: row.request_ids?.at(-1) ?? null, draft: !!row.draft, busy: !!row.busy, can_retry: !!row.can_retry, time_limit: row.time_limit ?? null,
    why: row.why ?? null, who: row.who ?? null, next_step: row.next_step ?? null,
    rerun: row.rerun ?? null, ...(typeof row.cache_reason === 'string' ? { cache_reason: row.cache_reason } : {}), ...(row.cached ? { cached: true, passed_at: row.passed_at } : {}),
    ...resultOutcome(row) };
}

function batchTokenUsage(publicRows) {
  const sumKey = key => publicRows.every(row => typeof row[key] === 'number')
    ? publicRows.reduce((sum, row) => sum + row[key], 0) : 'unknown';
  const input_tokens = sumKey('input_tokens');
  const cached_input_tokens = typeof input_tokens === 'number' ? sumKey('cached_input_tokens') : 'unknown';
  const output_tokens = sumKey('output_tokens');
  const complete = typeof input_tokens === 'number' && typeof cached_input_tokens === 'number';
  return { input_tokens, cached_input_tokens, output_tokens, cached_input_share: shareOf(input_tokens, cached_input_tokens), complete };
}

export function renderJson({ batch = null, repo, sourceSha256 = null, coverage, rows, warnings = [], exitCode, summaryLine: line }, ports = {}) {
  rows = [...rows.filter(row=>row.unsent),...rows.filter(row=>!row.unsent)];
  line = line ?? summaryLine(rows, null, ports);
  const perStory = new Map(storyLines(rows, ports).map(([story, text]) => [story, text]));
  const publicRows = rows.map(row => ({ ...jsonRow(row), summary_line: perStory.get(row.story) ?? null }));
  return { batch, repo, ...(coverage ? { coverage } : {}), source_sha256: sourceSha256, exit_code: exitCode, summary_line: line, draft: rows.some(row => row.draft),
    token_usage: batchTokenUsage(publicRows), rows: publicRows, warnings };
}

const count = (number, word) => `${number} ${word}${number === 1 ? '' : 's'}`;
// One line an agent can paste into a PR: ✓ only when every story passed.
// One paste line per Story (0.1.6: many Stories in one run), in table order; a Story with two test files gets one line.
export function storyLines(rows, ports = {}) {
  const groups = new Map();
  for (const row of rows) groups.set(row.story, [...(groups.get(row.story) ?? []), row]);
  return [...groups].map(([story, own]) => [story, summaryLine(own, story, ports)]);
}

const DEFAULT_PROMPT_TESTS_LABEL = 'Prompt tests';
export function summaryLine(rows, story = null, ports = {}) {
  const labelText = ports?.promptTestsLabel ?? DEFAULT_PROMPT_TESTS_LABEL;
  // A passed row proves only the criteria its report lists; without the list its criteria are not reported, never counted.
  const unreported = row => row.state === 'passed' && !row.criteria;
  const own = row => row.criteria ?? { passed: 0, total: row.criteria_total ?? 0 };
  const criteria = rows.filter(row => !unreported(row)).reduce((sum, row) => ({ passed: sum.passed + own(row).passed, total: sum.total + own(row).total }), { passed: 0, total: 0 });
  const notReported = rows.some(unreported), someCounted = rows.some(row => !unreported(row));
  const criteriaText = [...(someCounted || !notReported ? [`${criteria.passed} of ${count(criteria.total, 'criterion').replace(/criterions$/, 'criteria')}`] : ['passed']),
    ...(notReported ? ['criteria details not reported'] : [])].join(' · ');
  const checks = rows.reduce((sum, row) => ({ passed: sum.passed + (row.checks?.passed ?? 0), total: sum.total + (row.checks?.total ?? 0) }), { passed: 0, total: 0 });
  // A running row with server progress reports its calls in the one progress fragment; the calls part counts the other rows.
  const progress = progressText(rows), counted = rows.filter(row => !hasProgress(row));
  const sent = counted.filter(sentRow), known = sent.filter(row => typeof row.calls === 'number' && !OPEN_STATES.has(row.state));
  const partial = sent.filter(row => !OPEN_STATES.has(row.state) && typeof row.calls !== 'number');
  const calls = known.reduce((sum, row) => sum + row.calls, 0) + partial.reduce((sum, row) => sum + (row.known_calls ?? 0), 0);
  const unknownCalls = sent.reduce((sum, row) => sum + (known.includes(row) ? 0 : row.unknown_calls || 1), 0);
  const rerunCalls = rows.reduce((sum, row) => sum + (Number.isInteger(row.rerun?.calls) && row.rerun.calls > 0 ? row.rerun.calls : 0), 0);
  const labels = rows.filter(row => row.state !== 'passed').map(row => outcomeText({ ...row, progress: undefined, ahead: undefined }));
  const others = [...new Set(labels)].map(label => `${labels.filter(value => value === label).length} ${label}`);
  // A cross only for a real failure; a check that still runs or has no verdict says so (cli 12b).
  const mark = rows.some(row => row.state === 'failed') ? '✗'
    : rows.length && rows.every(row => row.state === 'passed') ? '✓'
    : rows.some(row => OPEN_STATES.has(row.state)) ? 'running ·'
    : rows.some(row => row.busy && ['not_run', 'not run'].includes(row.state)) && rows.every(row => row.state === 'passed' || (row.busy && ['not_run', 'not run'].includes(row.state))) ? 'busy ·' : 'no verdict ·';
  const rerunShare = rerunCalls ? `${rerunCalls} for reruns` : '';
  const usage = known.length ? `${count(calls, 'AI call')}${rerunShare ? ` (${rerunShare})` : ''}` : rerunShare || count(calls, 'AI call');
  const skipped = rows.some(row => row.cached) ? [count(new Set(rows.filter(row => row.cached).map(row => row.story_path ?? row.story)).size, 'Story').replace('Storys', 'Stories') + ' skipped'] : [];
  const broken = rows.filter(row=>row.unsent).length, unchecked = rows.reduce((n,row)=>n+(row.not_checked?.length??0),0);
  return [`${labelText}${story ? ` (${story})` : ''}${rows.some(row => row.draft) ? ' (DRAFT)' : ''}: ${mark} ${criteriaText}`,
    `${checks.passed}/${checks.total} checks`, ...(broken ? [`${broken} tests could not run`] : []), ...(unchecked ? [`${unchecked} criteria not checked; the Story is not a full pass`] : []), ...(progress ? [progress] : []), ...others, ...skipped, ...(progress && !sent.length ? [] : [`${usage}${unknownCalls ? ` + ${unknownCalls} unknown` : ''}`])].join(' · ');
}

const shellWord = word => /^[A-Za-z0-9_./:@%+=,-]+$/.test(word) ? word : `'${word.replaceAll("'", "'\\''")}'`;

function table(rows, now) {
  const previousPass = row => {
    const date = new Date(row.passed_at), today = new Date(now), two = number => String(number).padStart(2, '0');
    return 'unchanged, passed ' + (date.toDateString() === today.toDateString() ? `${two(date.getHours())}:${two(date.getMinutes())}` : `${date.getFullYear()}-${two(date.getMonth() + 1)}-${two(date.getDate())}`)
      + `; force with pdd test --cache-clear ${shellWord(row.story)}`;
  };
  const lines = [['Story', 'Test', 'Result', 'Checks', 'Time'], ...rows.map(row => [row.title ?? row.story, row.test,
    `${row.cached ? previousPass(row) : outcomeText(row)}${row.draft ? ' (DRAFT)' : ''}${row.cache_reason ? `; ${cleanText(row.cache_reason)}` : ''}`, row.checks ? `${row.checks.passed}/${row.checks.total}` : '-',
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
  const head = `${check.criterion_id}${check.step_id ? `  step ${check.step_id}` : ''}  ${check.target} ${check.path}`;
  const noError = check.target === 'error' && check.actual && typeof check.actual === 'object' && !Array.isArray(check.actual)
    && check.actual.missing === true && Object.keys(check.actual).length === 1
    && (check.normal_result === true || ['no-error', 'needs-tool'].includes(check.diagnosis?.kind));
  const actualValue = noError ? 'no error (a normal result)' : check.actual, actualDisplay = noError ? actualValue : shown(actualValue, secrets);
  const criterion = check.criterion_text ? [`  Criterion: ${plainLine(check.criterion_text, secrets)}`] : [];
  const refLabel = check.ref_target && check.ref_path !== undefined
    ? `${check.op ? `${check.op} ` : ''}${check.ref_target} ${check.ref_path || '/'}${check.ref_json_path ? ` (${check.ref_json_path})` : ''}` : null;
  const fits = [check.expected, check.actual].every(value => oneLine(value) && shown(value, secrets).length <= 80);
  if (fits) return [`${head}  expected ${refLabel ? `${refLabel} (${shown(check.expected, secrets)})` : shown(check.expected, secrets)}, got ${actualDisplay}`, ...criterion];
  const expected = valueLines(check.expected), actual = valueLines(actualValue);
  // Start 2 lines before the first line where two strings differ, when it is past the first 20.
  const differ = typeof check.expected === 'string' && typeof check.actual === 'string' ? expected.findIndex((text, index) => text !== actual[index]) : -1;
  const from = differ >= VALUE_LINES ? differ - 2 : 0;
  const block = (word, value, lines) => [`  ${word}:`, ...(from ? [`    … ${from} lines before`] : []),
    ...lines.slice(from, from + VALUE_LINES).map(text => `    ${plainLine(text, secrets)}`),
    ...(lines.length > from + VALUE_LINES ? [`    … ${lines.length - from - VALUE_LINES} more lines in the report`] : []),
    ...(typeof value === 'string' && value.endsWith('\n') ? ['    (ends with a line break)'] : [])];
  return [head, ...criterion, ...block(refLabel ? `expected (${refLabel})` : 'expected', check.expected, expected), ...block('got', check.actual, actual)];
}
// With a plain reason (#379): the reason, where and the fix; an AI service failure is not a problem in the test.
function refusalLines(item, serverNext = false) {
  const lines = item.reason ? [`  ${item.code}: ${item.reason}`, ...(item.where ? [`  Where: ${item.where}`] : []),
    ...(serverNext ? [] : item.cause === 'ai-service' ? ['  Your test is fine. Run it again.'] : item.fix ? [`  Fix: ${item.fix}`] : [])]
    : [`  ${[item.code, item.section, item.message].filter(Boolean).join('  ')}`];
  if (!item.reason && item.engine_message && item.engine_message !== item.code && item.engine_message !== item.message) lines.push(`  engine: ${item.engine_message}`);
  if (item.hint && !serverNext) lines.push(`  ${item.hint}`);
  for (const fact of item.dependency_errors ?? []) lines.push(`  Dependency: step ${JSON.stringify(fact.step_id)} input ${JSON.stringify(fact.input_path)} references step ${JSON.stringify(fact.predecessor_step_id)} result ${JSON.stringify(fact.result_path)}; that step reported error code ${JSON.stringify(fact.error_code)}.`);
  return lines;
}

const serverAdvice = (row, secrets = []) => [
  ...(row.why ? [`  Why: ${cleanText(row.why, secrets)}`] : []),
  ...(row.next_step ? [`  Next: ${cleanText(row.next_step, secrets)}`] : [])];

// Text-only metadata comes from the raw refusal; technical JSON keeps its original fields.
function busyMessage(row, secrets) {
  const seconds = row.busy_display?.max_wait_seconds;
  const duration = Number.isSafeInteger(seconds) && seconds > 0
    ? seconds % 60 === 0 ? count(seconds / 60, 'minute') : count(seconds, 'second') : null;
  const story = typeof row.story === 'string' ? cleanText(row.story, secrets) : '';
  const retry = story && story !== '-' ? `: pdd test ${shellWord(story)}` : '.';
  return `Not run: PDD stayed busy${duration ? ` for ${duration}` : ''}, so your check did not start. Nothing was charged. Try again in a few minutes${retry}`;
}

const validRerun = item => Number.isInteger(item?.runs) && item.runs >= 2
  && Number.isInteger(item?.failed) && item.failed >= 0 && item.failed <= item.runs;
const rerunVerdict = item => item.failed === 0
  ? `passed ${item.runs} of ${item.runs} reruns.`
  : item.stable === true && item.runs >= 2 && item.failed === item.runs
    ? `failed ${item.failed} of ${item.runs} (stable). A recheck of the same files will not help.`
    : `failed ${item.failed} of ${item.runs} (unstable). Make the rule in the prompt firmer.`;
function rerunEntries(row, failed) {
  const entries = [], seen = new Set();
  for (const check of failed) {
    const key = check.step_id ?? '';
    if (seen.has(key)) continue;
    seen.add(key);
    const sameStep = failed.filter(item => (item.step_id ?? '') === key);
    const diagnosis = sameStep.map(item => item.diagnosis?.rerun).find(validRerun);
    const reportStep = row.rerun?.steps?.find(item => item.step_id && item.step_id === check.step_id);
    const item = diagnosis ?? (validRerun(reportStep) ? reportStep : null);
    if (item) entries.push({ key, line: `  Rerun: ${rerunVerdict(item)}` });
  }
  if (!entries.length && row.rerun?.skipped) entries.push({ key: null, line: `  Rerun: skipped (${row.rerun.skipped}).` });
  return entries;
}

function localRefusals(rows, secrets) {
  const local = rows.filter(row => row.state === 'refused' && !sentRow(row)), out = [];
  if (local.length) {
    out.push('REFUSED before sending (not sent, 0 AI calls)');
    for (const row of local) {
      for (const item of row.refusals) {
        out.push(`  ${row.test}${item.step ? `  step ${item.step}` : ''}  ${item.code}`, `  ${item.message}`, ...(item.hint && !row.next_step ? [`  ${item.hint}`] : []));
      }
      out.push(...serverAdvice(row, secrets));
    }
  }
  return out;
}

// The terminal result of a batch (stdout).
export function renderText({ batch, rows, coverage, warnings = [], details = false, timeoutMin = null, interrupted = false, reading = false, exitCode, secrets = [], recovery, now = Date.now(), noFailed = false }, ports = {}) {
  const out = [];
  rows = [...rows.filter(row=>row.unsent),...rows.filter(row=>!row.unsent)];
  out.push(...localRefusals(rows.filter(row=>row.unsent),secrets));
  if (exitCode === 3) out.push(recovery ?? `pdd test --read ${batch}`);
  // One Story: its own line is the result; the overall line comes only with two or more Stories.
  const perStory = storyLines(rows, ports).map(([, text]) => text);
  if (noFailed) return 'No failed Stories. 0 AI calls.\n';
  out.push(...table(rows, now), ...(perStory.length === 1 ? perStory : [...perStory, summaryLine(rows, null, ports)]));
  if ([3, 4, 5].includes(exitCode)) {
    const failed = new Set(rows.filter(row => row.state === 'failed').map(row => row.story));
    const inconclusive = new Set(rows.filter(row => !['passed', 'failed'].includes(row.state)).map(row => row.story));
    const other = [...inconclusive].filter(story => !failed.has(story)).length;
    const overlap = [...inconclusive].filter(story => failed.has(story)).length;
    if (failed.size && inconclusive.size) {
      const first = failed.size === 1 ? '1 Story failed its checks.' : `${failed.size} Stories failed their checks.`;
      const second = other ? other === 1 ? 'Another Story has no verdict' : `${other} other Stories have no verdict`
        : failed.size === 1 ? 'That Story also has checks with no verdict'
        : `${overlap} of those Stories also ${overlap === 1 ? 'has' : 'have'} checks with no verdict`;
      out.push(`${first} ${second}, so the exit code is ${exitCode}.`);
    }
  }
  for (const row of rows.filter(row => row.state === 'failed')) {
    const failed = row.failed_checks ?? [], reruns = rerunEntries(row, failed), rerunByStep = new Map(reruns.filter(item => item.key !== null).map(item => [item.key, item.line])), lines = [`FAILED  ${row.title} (${row.test})`];
    for (const check of failed) {
      lines.push(...checkLines(check, secrets).map(text => `  ${text}`));
      if (check.diagnosis?.why) lines.push(`  Why: ${check.diagnosis.why}`);
      if (check.diagnosis?.next_step) lines.push(`  Next: ${check.diagnosis.next_step}`);
      const key = check.step_id ?? '', line = rerunByStep.get(key);
      if (line) { lines.push(line); rerunByStep.delete(key); }
    }
    if (reruns.some(item => item.key === null)) lines.push(reruns.find(item => item.key === null).line);
    lines.push(...(row.warnings ?? []).map(text => `  ${text}`));
    const diagnosed = failed.some(check => check.diagnosis?.why || check.diagnosis?.next_step);
    if (!diagnosed && row.next_step && row.why) lines.push(`  Why: ${row.why}`);
    if (!diagnosed && row.next_step) lines.push(`  Next: ${row.next_step}`);
    if (!diagnosed && !row.next_step) lines.push('  Next: show this check to the person. A person decides expected values. The agent may propose a change, and never makes it.');
    lines.push(`  Report: ${row.report_url ?? 'none'}`); out.push(...lines);
  }
  out.push(...localRefusals(rows.filter(row=>!row.unsent), secrets));
  for (const row of rows.filter(row => row.state === 'refused' && row.native_only?.length)) out.push(`  Native-only: ${cleanText(row.note?.message, secrets)}`);
  for (const row of rows.filter(row => row.state === 'refused' && sentRow(row))) {
    out.push(`REFUSED  ${row.title} (${row.test})`, ...row.refusals.flatMap(item => refusalLines(item, !!row.next_step)), ...serverAdvice(row, secrets), ...(row.report_url ? [`  Report: ${row.report_url}`] : []));
  }
  for (const row of rows.filter(row => ['not_run', 'not run'].includes(row.state))) {
    if ((row.busy_display || row.busy && row.request_ids?.length) && !row.note?.message?.startsWith('Stopped.')) {
      const { reason } = resultOutcome(row);
      if (['timeout-flag', 'deadline', 'interrupted'].includes(reason?.code)) out.push(cleanText(reason.message, secrets));
      out.push(busyMessage(row, secrets));
      continue;
    }
    const note = row.note ?? row.reason;
    const message = note?.message ?? (row.request_ids?.length ? 'No checks ran for this attempt.' : 'pdd did not send it.');
    const explanation = row.next_step ? message.replace(/(?:^|\s)(?:Retry this batch later|Run it again|Run the same command again later|Run a fresh pdd (?:test|check) command to start checks|Try again later)\.?/g, '').trim() : message;
    out.push(`NOT RUN  ${row.title} (${row.test})${explanation ? `: ${explanation}` : ''}${note?.code ? ` (${note.code})` : ''}`, ...serverAdvice(row, secrets));
  }
  for (const row of rows.filter(row => OPEN_STATES.has(row.state))) {
    const limit = Number.isInteger(timeoutMin) ? `${timeoutMin} min` : `${Math.round(timeoutMin * 60)} s`;
    out.push(`STILL RUNNING${reading || (!interrupted && !timeoutMin) ? '' : interrupted ? ' when pdd stopped reading' : ` after ${limit}`}: ${row.title}. Do not send it again.${row.note?.code === 'timeout-flag' || row.reason?.code === 'timeout-flag' ? ` ${row.note?.message ?? row.reason.message}` : ''}`);
  }
  for (const row of rows.filter(row => ['unknown', 'partial'].includes(row.state) && !row.provider && !row.time_limit)) {
    out.push(`UNKNOWN  ${row.title}: the run may have executed. Its result is unknown.`, ...((row.lost || row.final) && row.why ? [`  ${row.why}`, ...(row.next_step ? [`  Next: ${cleanText(row.next_step, secrets)}`] : [])] : serverAdvice(row, secrets)));
  }
  for (const row of rows.filter(row => row.time_limit)) {
    out.push(`STOPPED  ${row.title}: ${row.time_limit.message}`, ...(row.next_step ? [] : [`  ${row.time_limit.fix}`]), ...serverAdvice(row, secrets),
      ...(row.report_url ? [`  Report: ${row.report_url}`] : []));
  }
  for (const row of rows.filter(row => row.state === 'unknown' && row.provider)) {
    out.push(`UNKNOWN  ${row.title}: ${PROVIDER_TEXT}`, `  ${row.provider.code}${row.provider.detail ? ` (${row.provider.detail})` : ''}${row.report_url ? `  Report: ${row.report_url}` : ''}`,
      ...(row.next_step ? [] : ['  To try again, run `pdd test` again (a new request).']), ...serverAdvice(row, secrets));
  }
  if (details) for (const row of rows.filter(row => row.all_checks?.length || !row.cached && formatPromptCacheTokens(row))) {
    const tokenText = !row.cached ? formatPromptCacheTokens(row) : null;
    out.push(`Checks for ${row.title} (${row.test}):`,
      ...(tokenText ? [`  Tokens: ${tokenText}`] : []),
      ...[...(row.all_checks ?? [])].sort((a, b) => a.passed - b.passed).flatMap(check => checkLines(check, secrets)
        .map((text, index) => index ? `  ${text}` : `  ${check.passed ? 'passed' : 'failed'}  ${text}`)));
  }
  for (const row of rows) for (const item of criterionCoverage(row) ?? []) {
    const text = row.criterion_texts?.[item.criterion_id];
    out.push(`criterion ${item.criterion_id}:${text ? ` ${cleanText(text, secrets)}` : ''}${item.exit_code_only ? ' — checked by exit code only' : ''}`);
  }
  for (const row of rows) for (const item of row.not_checked ?? []) out.push(
    `${row.test} ${item.criterion_id}: not checked: ${cleanText(item.reason,secrets)} (${cleanText(item.text,secrets)})`);
  for (const row of rows.filter(row=>row.binding_plan)) for (const detail of bindingRefusals(row.binding_plan,row.compatibility)) out.push(cleanText(JSON.stringify(detail),secrets));
  for (const row of rows.filter(row => row.compatibility)) out.push(`Compatibility (${cleanText(row.test, secrets)}): ${JSON.stringify(row.compatibility, null, 2)}`,
    `  Client advice: ${JSON.stringify(row.client_advice)}`);
  if (coverage) out.push(coverageText(coverage, {busy: rows.some(row => row.busy_display || row.busy) && rows.every(row => row.state === 'passed' || row.busy_display || row.busy)}));
  const models = [...new Set(rows.map(row => row.requested_model).filter(Boolean))];
  out.push(`${rows.filter(row => row.state === 'passed').length} of ${rows.length} stories passed.${models.length ? ` Model asked for: ${models.join(', ')}.` : ''}`);
  const activeRows = rows.filter(row => !row.cached);
  const cacheRows = activeRows.filter(row => formatPromptCacheTokens(row) !== null);
  if (cacheRows.length) {
    const input_tokens = cacheRows.reduce((sum, row) => sum + row.input_tokens, 0);
    const cached_input_tokens = cacheRows.reduce((sum, row) => sum + row.cached_input_tokens, 0);
    const output_tokens = cacheRows.every(row => typeof row.output_tokens === 'number')
      ? cacheRows.reduce((sum, row) => sum + row.output_tokens, 0) : 'unknown';
    const unknownCount = activeRows.length - cacheRows.length;
    out.push(`Token usage: ${formatPromptCacheTokens({ input_tokens, cached_input_tokens, output_tokens })}${unknownCount ? ` + ${unknownCount} unknown` : ''}.`);
  }
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
    used: typeof total === 'number' && typeof remaining === 'number' && remaining <= total ? total - remaining : 'unknown',
    ...tokenUsageOf(answer) };
}
export function tryUsageLine(usage, { command = false } = {}) {
  const tokens = formatPromptCacheTokens(usage);
  return `Try AI usage: ${command ? `${usage.calls} this command · ` : ''}${usage.used} used · ${usage.remaining} remaining (session cap ${usage.cap})${tokens ? ` · ${tokens}` : ''}.`;
}
export function tryUsageHeaders(usage) {
  return { 'x-pdd-ai-calls': String(usage.calls), 'x-pdd-try-used': String(usage.used),
    'x-pdd-try-remaining': String(usage.remaining), 'x-pdd-try-cap': String(usage.cap),
    ...(tokenInt(usage?.input_tokens) !== undefined ? { 'x-pdd-input-tokens': String(usage.input_tokens) } : {}),
    ...(tokenInt(usage?.cached_input_tokens) !== undefined ? { 'x-pdd-cached-input-tokens': String(usage.cached_input_tokens) } : {}) };
}

export function coverageText(coverage, {busy = false} = {}) {
  const runtime = coverage?.runtime;
  const promptLine = runtime ? `${busy || runtime.native_only ? 'Runtime' : 'Interpreter'} coverage: ${runtime.checkable} of ${runtime.total} prompts checkable, ${runtime.native_only} native-only\n` : '';
  if (!coverage?.available) return promptLine + 'Module binding coverage unavailable: no pdd-bindings.json.';
  return promptLine + [`${coverage.bound} of ${coverage.total} modules bound`, ...coverage.modules.filter(m => m.state === 'unbound').map(m => `  ${m.path}: ${m.reason} Port attempted: ${m.port_attempt}`)].join('\n');
}
