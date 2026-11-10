// Source: prompts/cli/autopilot-runtime.prompt.md.
const binding = row => ['binding-missing', 'missing-binding'].includes(row.reason?.code)
  || (Array.isArray(row.refusals) ? row.refusals : []).some(r => ['binding-missing', 'missing-binding'].includes(r.code))
  || row.compatibility?.state === 'missing-binding';
const terminalVerdict = check => check?.states?.length > 0 && check.states.every(row => ['passed', 'failed'].includes(row.state));
export const runtimeEvidence = run => JSON.stringify([run.parkReason ?? null, run.runtimeWait ?? null, run.gate ?? null, run.done?.check ?? null]);
export function classifyRuntimeFailure(check, health = null) {
  const rows = check?.states;
  if (!rows?.length || rows.some(row => binding(row) || ['ready', 'waiting', 'sending', 'queued', 'running', 'sent'].includes(row.state))) return null;
  const open = rows.filter(row => !['passed','failed'].includes(row.state));
  if (!open.length) return null;
  const codes = open.flatMap(row => [row.reason?.code, row.note?.code, row.provider?.code, ...(Array.isArray(row.refusals) ? row.refusals : []).map(r => r.code)]).filter(Boolean);
  if (codes.some(code => ['check-plan-prerequisite','broken-test','invalid-input','interface-missing','undefined-call-bound','recursive-call-bound','auth-required','blocked'].includes(code))) return null;
  const words = JSON.stringify(open);
  if (/\(HTTP 40[13]\)|\bgh auth login\b/.test(words)) return null;
  const cause = /timeout|timed.out|time.limit|deadline/i.test(words) ? 'timeout'
    : codes.includes('runner-stopped') ? 'runner-stopped'
    : codes.some(code => /provider|uncertain-child-dispatch/.test(code)) ? 'provider-error'
    : open.every(row => ['partial', 'unknown', 'not run'].includes(row.state)) ? 'no-verdict' : null;
  if (!cause) return null;
  const offered = health?.cause?.code ?? health?.cause ?? health?.code;
  return typeof offered === 'string' && /^[a-z][a-z0-9-]{0,79}$/.test(offered) ? offered : cause;
}

export async function reconcileRuntimeIncidents(state, ports, config, runs, {localOnly = false} = {}) {
  const ledger = state.runtimeIncidents ??= {causes: {}, seen: {}};
  const checks = new Map(), blockers = new Map(), now = ports.now();
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
    if (!ledger.seen[key]) {
      ledger.seen[key] = now;
      record.failures[key] = Number.isFinite(check.at) ? check.at : now;
      record.lastFailureAt = Math.max(record.lastFailureAt ?? 0, check.at ?? now);
      record.runs[run.runId] = {number: run.number, batch: check.batch};
      record.recoveredAt = null;
      record.dirty = true;
    }
    if (!localOnly) {
      try {
        const marker = `<!-- pdd:runtime-cause:${cause} -->`;
        if (!record.issue) {
          const found = await ports.findIssue(marker);
          if (found) record.issue = {number: found.number, url: found.url};
          else if (!record.creating) {
            record.creating = true;
            if (!await ports.save()) continue;
            const issue = await ports.createIssue({title: `Runtime: ${cause}`, body: marker, owner: config.runtimeOwner});
            record.issue = {number: issue.number, url: issue.url};
          }
        }
        if (record.issue && record.dirty) {
          const body = `${marker}\n\nRuntime check failure: ${cause}. The required check remains pending.\n\n`
            + Object.values(record.runs).map(row => `- Run #${row.number}, batch ${row.batch}`).join('\n');
          await ports.updateIssue({...record.issue, body, reopen: true});
          record.dirty = false;
        }
      } catch (error) {
        if (error.notCreated) delete record.creating;
        // Otherwise search the marker next tick; an unknown create is not replayed.
      }
    }
    if (record.issue) blockers.set(run.number, {kind: 'runtime', until: String(record.issue.number), cause,
      batch: check.batch, checkKind: 'pdd test', evidence: runtimeEvidence(run)});
  }
  for (const record of Object.values(ledger.causes)) {
    const later = [...checks.values()].find(check => terminalVerdict(check) && check.at > record.lastFailureAt);
    if (later) record.recoveredAt = Math.max(record.recoveredAt ?? 0, later.at);
    if (!localOnly && record.issue) try {
      if (await ports.issueClosed(record.issue.number)) record.recoveredAt ??= now;
    } catch { /* Unknown issue state keeps the failure pending. */ }
  }
  const enabled = Object.values(ledger.causes).some(record => !record.recoveredAt
    && Object.values(record.failures).filter(at => now - at < 1_800_000).length >= 3);
  if (Object.keys(ledger.causes).length) {
    await ports.configure(enabled);
    await ports.save();
  }
  return blockers;
}
