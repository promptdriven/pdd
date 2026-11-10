// Source: prompts/cli/autopilot-runtime.prompt.md.
const binding = row => Boolean(row && (['binding-missing', 'missing-binding'].includes(row.reason?.code)
  || (Array.isArray(row.refusals) ? row.refusals : []).some(r => ['binding-missing', 'missing-binding'].includes(r?.code))
  || row.compatibility?.state === 'missing-binding'));
const terminalVerdict = check => check?.states?.length > 0 && check.states.every(row => ['passed', 'failed'].includes(row.state));
export const runtimeEvidence = run => JSON.stringify([run.parkReason ?? null, run.runtimeWait ?? null, run.gate ?? null, run.done?.check ?? null]);
export function classifyRuntimeFailure(check, health = null) {
  const rows = Array.isArray(check?.states) ? check.states : Array.isArray(check?.rows) ? check.rows : null;
  if (!rows?.length || rows.some(row => !row || typeof row !== 'object' || binding(row) || row.state === 'failed'
    || ['ready', 'waiting', 'sending', 'queued', 'running', 'sent'].includes(row.state))) return null;
  const open = rows.filter(row => !['passed', 'failed'].includes(row.state));
  if (!open.length) return null;
  const runtimeCodes = new Set(['graph-provider-failure', 'graph-uncertain-child-dispatch', 'runner-stopped',
    'service-restarted', 'step_timeout', 'server-refusal', 'runtime-internal-error', 'provider-unavailable']);
  const expectationCodes = new Set(['check-plan-prerequisite', 'broken-test', 'invalid-input', 'interface-missing',
    'undefined-call-bound', 'recursive-call-bound', 'auth-required', 'blocked', 'expectation-failed', 'file-rule',
    'provider-call-cap', 'call-cap-reached']);
  const rowCodes = row => [row.reason?.code, row.note?.code, row.provider?.code, row.code,
    ...(Array.isArray(row.refusals) ? row.refusals.map(refusal => refusal?.code) : [])].filter(value => typeof value === 'string');
  if (open.some(row => rowCodes(row).some(code => expectationCodes.has(code)))) return null;
  if (open.some(row => row.state === 'refused' && !rowCodes(row).some(code => runtimeCodes.has(code)))) return null;
  const codes = open.flatMap(rowCodes);
  const text = open.flatMap(row => [row.state, row.reason?.code, row.reason?.message, row.reason?.reason,
    row.note?.code, row.note?.message, row.provider?.code, row.provider?.message, row.error?.code, row.error?.message,
    ...(Array.isArray(row.refusals) ? row.refusals.flatMap(refusal => [refusal?.code, refusal?.message]) : [])])
    .filter(value => typeof value === 'string').join(' ');
  if (/\(HTTP 40[13]\)|\bgh auth (?:login|status)\b/i.test(text)) return null;
  const cause = codes.includes('step_timeout') || /\b(?:step )?timed?[- ]?out\b|time limit|deadline exceeded/i.test(text) ? 'timeout'
    : codes.includes('runner-stopped') || codes.includes('service-restarted') || /runner[ -]stopped|service[ -]restarted|ECONNREFUSED|ECONNRESET|fetch failed/i.test(text) ? 'runner-stopped'
    : codes.some(code => /provider|uncertain-child-dispatch/.test(code)) || /provider[ -]error|upstream model|ai-service/i.test(text) ? 'provider-error'
    : codes.some(code => ['server-refusal', 'runtime-internal-error'].includes(code)) || /server refusal|HTTP 5\d\d|internal server error|runtime_internal_error/i.test(text) ? 'server-refusal'
    : open.every(row => ['partial', 'unknown', 'not run', 'no-verdict'].includes(row.state)) ? 'no-verdict' : null;
  if (!cause) return null;
  const offered = health?.cause?.code ?? health?.cause ?? health?.code;
  return typeof offered === 'string' && /^[a-z][a-z0-9-]{0,79}$/.test(offered) ? offered : cause;
}
export async function reconcileRuntimeIncidents(state, ports, config, runs, {localOnly = false} = {}) {
  const ledger = state.runtimeIncidents ??= {causes: {}, seen: {}};
  const checks = new Map(), blockers = new Map(), pending = new Map(), now = ports.now();
  for (const run of runs) {
    try {checks.set(run.number, await ports.readCheck(run));} catch { /* Isolate an unreadable run. */ }
  }
  const eligible = run => ['stuck', 'waiting', 'paused'].includes(run.state)
    && !(run.question && !run.question.answeredAt)
    && (!run.blockedOn || ['runtime', 'interpreter'].includes(run.blockedOn.kind))
    && !['waking', 'releasing'].includes(run.parking?.phase);
  let health = null;
  if (!localOnly && runs.some(run => eligible(run) && classifyRuntimeFailure(checks.get(run.number)))) {
    try {health = await ports.health();} catch { /* Optional health, including 401/absence, is not required. */ }
  }
  for (const run of runs) {
    const check = checks.get(run.number);
    if (!eligible(run)) continue;
    try {if (await ports.busy(run)) continue;} catch {continue;}
    const prior = run.parking?.blocker;
    if (prior?.kind === 'runtime' && prior.evidence === runtimeEvidence(run) && !classifyRuntimeFailure(check)) {
      blockers.set(run.number, prior);
      continue;
    }
    if (localOnly) {
      if (prior?.kind === 'runtime' && prior.evidence === runtimeEvidence(run)) blockers.set(run.number, prior);
      continue;
    }
    if (!check?.batch) continue;
    const cause = prior?.kind === 'runtime' && prior.batch === check.batch ? prior.cause : classifyRuntimeFailure(check, health);
    if (!cause) continue;
    const key = `${run.runId}:${check.batch}:${cause}`;
    const record = ledger.causes[cause] ??= {cause, checkKind: 'pdd test', firstAt: now, failures: {}, runs: {}, issue: null};
    // A still-failing batch after recovery is a new incident observation. This
    // also makes a failed issue reopen cancel recovery before another wake.
    const priorAttempt = Object.values(record.runs).find(row => row.runId === run.runId && row.batch === check.batch)
      ?? record.runs[run.runId];
    const attemptKey = record.recoveredAt && priorAttempt?.batch === check.batch
      ? `${key}:retry:${record.recoveredAt}` : key;
    if (!ledger.seen[attemptKey]) {
      ledger.seen[attemptKey] = now;
      record.failures[attemptKey] = now;
      record.lastFailureAt = now;
      record.runs[`${run.runId}:${check.batch}`] = {runId: run.runId, number: run.number, batch: check.batch};
      record.recoveredAt = null;
      record.dirty = true;
    }
    pending.set(run.number, {run, check, cause, record});
  }
  if (!localOnly) for (const record of Object.values(ledger.causes)) {
    if (!record.dirty || typeof ports.reportRuntimeCause !== 'function') continue;
    try {
      if (!await ports.save()) continue;
      const marker = `<!-- pdd:runtime-cause:${record.cause} -->`;
      const reported = await ports.reportRuntimeCause({cause: record.cause, marker, title: `Runtime: ${record.cause}`,
        runs: Object.values(record.runs).map(({number, batch}) => ({number, batch})), runtimeOwner: config.runtimeOwner});
      if (!Number.isSafeInteger(reported?.number) || reported.number < 1 || typeof reported.url !== 'string') continue;
      record.issue = {number: reported.number, url: reported.url,
        repository: typeof reported.repository === 'string' && /^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(reported.repository)
          ? reported.repository : 'promptdriven/pdd'};
      record.dirty = false;
    } catch { /* Keep the cause pending; the shared reporter owns retry and dedupe. */ }
  }
  for (const [number, {check, cause, record}] of pending) {
    const issue = record.issue;
    blockers.set(number, {kind: 'runtime', until: issue ? String(issue.number) : null, cause,
      batch: check.batch, checkKind: 'pdd test', evidence: runtimeEvidence(runs.find(run => run.number === number)),
      ...(issue?.repository ? {repository: issue.repository} : {})});
  }
  for (const record of Object.values(ledger.causes)) {
    // check.at is the batch start time. It can predate a failure that was only
    // observed now, so only a batch started after that observation can recover it.
    const later = [...checks.values()].find(check => terminalVerdict(check) && check.at > record.lastFailureAt);
    if (later) record.recoveredAt = Math.max(record.recoveredAt ?? 0, now);
    if (!localOnly && record.issue && !record.dirty) try {
      if (await ports.issueClosed(record.issue)) record.recoveredAt ??= now;
    } catch { /* Unknown issue state keeps the failure pending. */ }
  }
  if (Object.keys(ledger.causes).length) await ports.save();
  return blockers;
}
