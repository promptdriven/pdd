// Generated from prompts/cli/metrics-model.prompt.md (sha256: b530fd8b75cfa4110173e250edc83c332df76518641f7f4f097ecf771f50bf18).
const stable = value => {
  if (Array.isArray(value)) return `[${value.map(stable).join(',')}]`;
  if (value && typeof value === 'object') return `{${Object.keys(value).sort().map(k => `${JSON.stringify(k)}:${stable(value[k])}`).join(',')}}`;
  return JSON.stringify(value);
};
const time = value => Date.parse(value);
const order = (a, b) => time(a.at) - time(b.at) || time(a.observedAt) - time(b.observedAt) || a.source.localeCompare(b.source) || a.id.localeCompare(b.id);
const latest = events => [...events].sort(order).at(-1);
const reasonList = events => [...new Set(events.flatMap(e => [...(Array.isArray(e.data.reasons) ? e.data.reasons : []), ...(e.data.reason ? [e.data.reason] : [])]))].sort();
const state = (yes, unknown = false) => yes ? 'yes' : unknown ? 'unknown' : 'no';
const count = (issues, predicate, scope, observedAt) => {
  const selected = issues.filter(predicate);
  const unknown = issues.filter(i => predicate(i) === null).length;
  const numerator = selected.length, denominator = issues.length;
  return { numerator, denominator, unknown, percentage: denominator ? numerator * 100 / denominator : null, scope, observedAt, issues: selected.map(i => i.issue) };
};

/** Calculate measurements solely from supplied observations. */
export function calculateMetrics({ events, repo, scope, timezone, observedAt, sources }) {
  const canonicalRepo = repo.toLowerCase();
  const cutoff = time(observedAt);
  if (!Number.isFinite(cutoff)) throw new TypeError('Invalid observation time');
  const formatter = new Intl.DateTimeFormat('en-CA', { timeZone: timezone, year: 'numeric', month: '2-digit', day: '2-digit' });
  const dateOf = at => { const parts = Object.fromEntries(formatter.formatToParts(new Date(at)).map(p => [p.type, p.value])); return `${parts.year}-${parts.month}-${parts.day}`; };
  const identities = new Map();
  for (const event of events) {
    if (typeof event.repo !== 'string' || event.repo.toLowerCase() !== canonicalRepo || time(event.at) > cutoff || time(event.observedAt) > cutoff || !Number.isFinite(time(event.at)) || !Number.isFinite(time(event.observedAt))) continue;
    const key = JSON.stringify([event.source, event.id]);
    const variants = identities.get(key) || new Map();
    const normalized = { ...event, repo: canonicalRepo, data: { ...(event.data || {}) } };
    const { observedAt: ignored, ...facts } = normalized;
    const fingerprint = stable(event.type === 'ci' && event.source.startsWith('github:') ? {...facts,at:null} : facts);
    const prior = variants.get(fingerprint);
    if (!prior || time(normalized.observedAt) < time(prior.observedAt)) variants.set(fingerprint, normalized);
    identities.set(key, variants);
  }
  const conflicts = [], clean = [];
  for (const variants of identities.values()) {
    let entries = [...variants.values()].sort((a, b) => stable(a).localeCompare(stable(b)));
    if (entries.length > 1 && entries.every(e => e.type === 'check')) {
      const claim = e => stable({...e, observedAt:null, data:{...e.data, acceptance:null}});
      if (new Set(entries.map(claim)).size === 1) {
        const known = entries.filter(e => e.data.acceptance != null && e.data.acceptance !== 'unknown');
        if (new Set(known.map(e => e.data.acceptance)).size <= 1) entries = [(known.length ? known : entries).sort((a,b) => time(a.observedAt) - time(b.observedAt))[0]];
      }
    }
    if (entries.length > 1) conflicts.push({ source: entries[0].source, id: entries[0].id, events: entries });
    else clean.push(entries[0]);
  }
  clean.sort(order);
  conflicts.sort((a, b) => a.source.localeCompare(b.source) || a.id.localeCompare(b.id));
  const selections = clean.filter(e => e.type === 'selection' && e.data.snapshotId === scope.snapshotId);
  const selectionByIssue = new Map();
  for (const e of selections) {
    const list = selectionByIssue.get(e.issue) || []; list.push(e); selectionByIssue.set(e.issue, list);
  }
  const issueIds = scope.kind === 'daily-start'
    ? [...new Set(clean.filter(e => e.type === 'start' && dateOf(e.at) === scope.date).map(e => e.issue))]
    : scope.kind === 'activity'
    ? [...new Set(clean.filter(e => dateOf(e.at) === scope.date).map(e => e.issue))]
    : [...new Set([...selectionByIssue.keys(), ...conflicts.flatMap(c => c.events.filter(e => e.type === 'selection' && e.data.snapshotId === scope.snapshotId).map(e => e.issue))])];
  issueIds.sort((a, b) => a - b);
  const relevantConflicts = issue => conflicts.filter(c => c.events.some(e => e.issue === issue));
  const issues = issueIds.map(issue => {
    const rows = clean.filter(e => e.issue === issue);
    const issueConflicts = relevantConflicts(issue);
    const hasConflict = type => issueConflicts.some(c => c.events.some(e => e.type === type));
    const selectionRows = selectionByIssue.get(issue) || [];
    const selection = latest(selectionRows);
    const startRows = rows.filter(e => e.type === 'start');
    const attempts = [...new Set(rows.map(e => e.attempt).filter(Boolean))].sort();
    const explicitCandidates = rows.filter(e => e.data.pr != null && (e.type === 'candidate' || (e.type === 'milestone' && ['code-pr','implementation-ready'].includes(e.data.stage)))).sort(order);
    const terminal = new Set(rows.filter(e => e.attempt && ((e.type === 'step' && e.data.step === 'cancel' && e.data.status === 'done') || (e.type === 'outcome' && ['cancelled','superseded'].includes(e.data.status)))).map(e => e.attempt));
    const scopedCandidates = explicitCandidates.filter(e => e.attempt);
    const activeCandidates = scopedCandidates.filter(e => !terminal.has(e.attempt));
    const activeAttempts = new Set(activeCandidates.map(e => e.attempt));
    const explicit = activeCandidates.at(-1) || explicitCandidates.filter(e => !e.attempt).at(-1);
    const selectedAttempt = activeAttempts.size === 1 ? [...activeAttempts][0] : null;
    const competing = activeAttempts.size > 1 || (explicit && (selectedAttempt ? activeCandidates : explicitCandidates.filter(e => !e.attempt)).some(e => time(e.at) === time(explicit.at) && e.data.pr !== explicit.data.pr));
    const candidates = explicit ? rows.filter(e => e.data.pr === explicit.data.pr && e.data.head && (e.type === 'candidate' || (e.type === 'milestone' && ['code-pr','implementation-ready','candidate-head','head'].includes(e.data.stage))) && (!e.attempt || e.attempt === selectedAttempt)).sort(order) : [];
    const candidate = competing ? null : candidates.at(-1);
    let changedAt = 0;
    for (let n = 1; n < candidates.length; n++) if (candidates[n].data.head !== candidates[n-1].data.head) changedAt = time(candidates[n].at);
    const ready = Boolean(candidate && rows.some(e => e.type === 'milestone' && e.data.stage === 'implementation-ready' && e.data.pr === candidate.data.pr && e.data.head === candidate.data.head && (selectedAttempt ? e.attempt === selectedAttempt : !scopedCandidates.length && !e.attempt) && time(e.at) >= changedAt));
    const checks = rows.filter(e => e.type === 'check');
    const currentChecks = checks.filter(e => candidate && e.data.pr === candidate.data.pr && e.data.head === candidate.data.head && time(e.at) >= changedAt);
    const accepted = e => Boolean(e.data.reviewer && e.data.evidence) && ['accepted', 'equivalent', 'pass', 'PASS'].includes(e.data.acceptance);
    const check = latest(currentChecks);
    const opposing = check && currentChecks.filter(e => e.data.verdict !== check.data.verdict);
    const lastOpposing = opposing?.length ? Math.max(...opposing.map(e => time(e.at))) : -Infinity;
    const agreeing = currentChecks.filter(e => e.data.verdict === check?.data.verdict && time(e.at) > lastOpposing && accepted(e) && e.data.checkerFamily && e.data.checkerMode);
    const session = e => { const prefix = `${e.data.checkerFamily}:session-`; return e.data.reviewer.startsWith(prefix) ? e.data.reviewer.slice(prefix.length) : ''; };
    const pair = agreeing.some((a, i) => agreeing.slice(i + 1).some(b => session(a) && session(b) && session(a) !== session(b) && ['same-family','different-family'].includes(a.data.checkerMode) && ['same-family','different-family'].includes(b.data.checkerMode) && (a.data.checkerFamily.toLowerCase() !== b.data.checkerFamily.toLowerCase() || (a.data.checkerMode === 'same-family' && b.data.checkerMode === 'same-family'))));
    const unresolvedSplit = opposing?.length && !pair;
    const validated = hasConflict('check') || hasConflict('milestone') || unresolvedSplit || !check || !candidate || (scopedCandidates.length > 0 && !selectedAttempt) || !accepted(check) ? 'unknown' : check.data.verdict === 'PASS' ? 'yes' : check.data.verdict === 'FAIL' ? 'no' : 'unknown';
    const deliveries = rows.filter(e => e.type === 'delivery' && e.data.explicit === true && e.data.evidence && e.data.pr != null);
    const delivery = latest(deliveries);
    const required = latest(rows.filter(e => e.type === 'outcome' || e.type === 'start') .filter(e => e.data.requiredOutcome))?.data.requiredOutcome || 'unknown';
    const activeWaits = new Map();
    for (const e of rows.filter(e => e.type === 'milestone' && ['wait', 'resume'].includes(e.data.stage))) {
      const stage = e.data.waitStage || e.data.area || 'unknown';
      const key = JSON.stringify([e.attempt || '', stage]);
      if (e.data.stage === 'wait') {
        const prior = activeWaits.get(key);
        if (prior) prior.reasons = [...new Set([...prior.reasons, ...reasonList([e])])].sort();
        else {
          const scopeAtWait = latest(rows.filter(r => ['outcome', 'start'].includes(r.type) && r.data.requiredOutcome && time(r.at) <= time(e.at) && (!r.attempt || r.attempt === e.attempt)))?.data.requiredOutcome || 'unknown';
          activeWaits.set(key, { issue, stage, reasons: reasonList([e]), since: e.at, source: e.source, requiredOutcome: scopeAtWait, promptOnlyStop: scopeAtWait === 'prompt-only' });
        }
      } else activeWaits.delete(key);
    }
    const waits = [...activeWaits.values()].map(w => ({...w, reason: w.reasons.join(', ') || 'unknown', elapsedMs: cutoff - time(w.since)}));
    const reports = rows.filter(e => e.type === 'report');
    const linked = new Map(deliveries.map(d => [d, []]));
    for (const report of reports) {
      if (report.data.classification !== 'failed-fix' || report.data.humanReported !== true || !report.data.evidence) continue;
      const match = (report.attempt || report.data.pr != null) && latest(deliveries.filter(d => time(d.at) <= time(report.at) && (!report.attempt || d.attempt === report.attempt) && (report.data.pr == null || d.data.pr === report.data.pr)));
      if (match) linked.get(match).push(report);
    }
    const failed = reports.filter(report => report.data.classification === 'failed-fix' && report.data.humanReported === true && report.data.evidence && deliveries.some(d => time(d.at) <= time(report.at)));
    const unassociatedFailedFixReports = failed.filter(report => ![...linked.values()].some(list => list.includes(report)));
    const unclassifiedReports = reports.filter(report => report.data.classification === 'failed-fix' && !failed.includes(report));
    const deliveryFollowUps = deliveries.map(d => {
      const deliveryReports = linked.get(d);
      const followUp = Object.fromEntries([7, 30].map(days => {
        const end = time(d.at) + days * 86400000;
        const within = deliveryReports.filter(e => time(e.at) <= end);
        return [String(days), { mature: cutoff >= end, failedFixReports: within, status: within.length ? 'reported' : unassociatedFailedFixReports.some(e => time(e.at) >= time(d.at) && time(e.at) <= end) ? 'unknown' : cutoff >= end ? 'no-report-observed' : 'immature' }];
      }));
      return { delivery: d, failedFixReports: deliveryReports, followUp };
    });
    const followUp = delivery ? deliveryFollowUps.find(item => item.delivery === delivery).followUp : null;
    const coverage = rows.filter(e => e.type === 'coverage');
    const assistance = rows.filter(e => e.type === 'assistance');
    const assisted = assistance.some(e => e.data.classification === 'recovery') ? 'yes' : startRows.length > 0 && startRows.every(start => coverage.some(e => e.source === start.source && e.data.complete === true && e.data.since && e.data.until && time(e.data.since) <= time(start.at) && time(e.data.until) >= cutoff)) && !hasConflict('assistance') && !hasConflict('coverage') ? 'no' : 'unknown';
    const selectionConflict = hasConflict('selection') || new Set(selectionRows.map(e => stable([e.data.inScope, e.data.state]))).size > 1;
    return {
      repo: canonicalRepo, issue,
      selection: { inScope: selectionConflict ? null : selection?.data.inScope ?? null, state: selectionConflict ? 'unknown' : selection?.data.state || 'unknown', reasons: reasonList(selectionRows) },
      prCreated: hasConflict('pr') ? 'unknown' : state(rows.some(e => e.type === 'pr' || (e.data.pr != null && ['milestone','check','delivery'].includes(e.type))), !rows.some(e => e.type === 'pr' || (e.data.pr != null && ['milestone','check','delivery'].includes(e.type)))),
      implementationReady: hasConflict('milestone') ? 'unknown' : state(Boolean(ready), !ready),
      failedFix: state(failed.length > 0, !failed.length),
      started: hasConflict('start') ? 'unknown' : state(startRows.length > 0, !startRows.length),
      validated,
      delivered: hasConflict('delivery') ? 'unknown' : state(deliveries.length > 0, !deliveries.length),
      requiredOutcome: required, promptOnlyStop: required === 'prompt-only',
      origins: [...new Set(startRows.map(e => e.data.origin || 'unknown'))].sort(), attempts, starts: startRows,
      candidate: candidate || null, checks, ci: rows.filter(e => e.type === 'ci'),
      steps: rows.filter(e => e.type === 'step'), deliveries, reports, failedFixReports: failed, unassociatedFailedFixReports, unclassifiedReports, followUp, deliveryFollowUps,
      waits, assistance: { status: assisted, events: assistance }, coverage,
      conflicts: issueConflicts.map(c => ({ source: c.source, id: c.id }))
    };
  });
  const stageNames = ['started', 'validated', 'delivered'];
  const stages = Object.fromEntries(stageNames.map(name => [name, count(issues, i => i[name] === 'yes' ? true : i[name] === 'unknown' ? null : false, scope, observedAt)]));
  const stageValue = (i, name) => {
    if (name === 'inScope') return i.selection.inScope === null ? 'unknown' : i.selection.inScope ? 'yes' : 'no';
    if (name === 'eligible') return i.selection.inScope === false || ['excluded', 'waiting'].includes(i.selection.state) ? 'no' : i.selection.inScope === true && i.selection.state === 'ready' ? 'yes' : 'unknown';
    if (name === 'autopilot') return i.origins.includes('autopilot') ? 'yes' : 'unknown';
    return i[name];
  };
  const transitions = {};
  for (const [name, from, to] of [['eligibility','inScope','eligible'], ['autopilotStarts','eligible','autopilot'], ['prCreation','autopilot','prCreated'], ['implementationReady','autopilot','implementationReady'], ['validation','implementationReady','validated'], ['delivery','validated','delivered'], ['failedFix','delivered','failedFix']]) {
    const denominatorIssues = issues.filter(i => stageValue(i, from) === 'yes');
    const measure = count(denominatorIssues, i => stageValue(i, to) === 'yes' ? true : stageValue(i, to) === 'no' ? false : null, scope, observedAt);
    transitions[name] = {...measure, denominatorIssues: denominatorIssues.map(i => i.issue), denominatorUnknown: issues.filter(i => stageValue(i, from) === 'unknown').length};
  }
  const queue = Object.fromEntries(['ready', 'excluded', 'waiting', 'unknown'].map(s => [s, { count: issues.filter(i => i.selection.state === s).length, issues: issues.filter(i => i.selection.state === s).map(i => ({ issue: i.issue, reasons: i.selection.reasons })) }]));
  const activityRows = clean.filter(e => dateOf(e.at) === scope.date);
  const activity = scope.kind !== 'activity' ? null : Object.fromEntries(Object.entries({ starts: e => e.type === 'start', candidateCompletions: e => e.type === 'milestone' && e.data.stage === 'implementation-ready' && e.data.pr != null && e.data.head, validationResults: e => e.type === 'check', deliveries: e => e.type === 'delivery' && e.data.explicit === true && e.data.evidence && e.data.pr != null }).map(([name, matches]) => { const matched = activityRows.filter(matches); return [name, { count: matched.length, issues: [...new Set(matched.map(e => e.issue))].sort((a,b) => a-b), events: matched }]; }));
  const coverage = clean.filter(e => e.type === 'coverage');
  const sourceId = s => typeof s === 'string' ? s : s.source;
  return { definitionVersion: 'pdd.metrics.v1', repo: canonicalRepo, scope: { ...scope }, timezone, observedAt, sources: [...sources].sort((a,b) => String(sourceId(a)).localeCompare(String(sourceId(b)))), coverage: { events: coverage, missingSources: sources.map(sourceId).filter(s => !clean.some(e => e.source === s)).sort(), complete: false }, conflicts, issues, queue, activity, stages, transitions, waits: issues.flatMap(i => i.waits) };
}
