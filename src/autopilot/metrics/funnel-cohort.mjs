// Layer-2 Pillar 2A honest stage-by-stage funnel %, DST-safe PT standup windows, and mature 7-day cohort tracker.

export const FUNNEL_SCHEMA = 'pdd.autopilot.funnel.v2';
export const FUNNEL_STAGES = Object.freeze(['considered', 'eligible', 'claimed', 'pr', 'merged']);
export const DISPOSITION_KINDS = Object.freeze(['autoMerged', 'humanMerged', 'wouldMerge', 'realHold', 'missingCapacity', 'inProgress', 'dropped']);
export const COHORT_STATUSES = Object.freeze(['mature-clean', 'mature-regressed', 'immature-clean', 'immature-regressed']);
export const DEFAULT_STANDUP_TIMEZONE = 'America/Los_Angeles';
export const DEFAULT_STANDUP_HOUR = 9;
export const DEFAULT_COHORT_MATURITY_DAYS = 7;

const DAY_MS = 86_400_000, HOUR_MS = 3_600_000;
const WEEKDAY_INDEX = Object.freeze({ Mon: 0, Tue: 1, Wed: 2, Thu: 3, Fri: 4, Sat: 5, Sun: 6 });
const STAGE_RANK = Object.freeze({ considered: 0, eligible: 1, claimed: 2, pr: 3, merged: 4 });
const REAL_HOLD_SIGNALS = new Set([
  'real-hold', 'real_hold', 'needs-person', 'needs-decision', 'human_decision', 'human-decision',
  'protected-path', 'protected_path', 'codeowners-hold', 'unclear_or_unsound', 'unclear-or-unsound',
  'cross_repo', 'cross-repo', 'unverifiable_boundary', 'unverifiable-boundary', 'held', 'assigned',
  'blocked-by', 'not_planned', 'blocker-closed-not-planned', 'blocker-unavailable-404',
]);
const CAPACITY_SIGNALS = new Set([
  'missing-capacity', 'missing_capacity', 'missing-capability', 'missing_capability',
  'capacity-full', 'slot-cap', 'no-worker-slot', 'quota-exhausted', 'rate-limited', 'rate-limit',
]);
const PASS_GATES = new Set(['pass', 'passed', 'green', 'proved', 'bounded']);
const FAIL_GATES = new Set(['fail', 'failed', 'red', 'broken', 'hung']);
const RUNNING_GATES = new Set(['running', 'pending', 'in_progress', 'queued']);

const isObj = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const asText = v => (typeof v === 'string' ? v : '');
const posInt = v => Number.isSafeInteger(v) && v > 0;
const lower = v => asText(v).trim().toLowerCase();
const parseMs = (v, fb = null) => (typeof v === 'number' && Number.isFinite(v) ? v : (typeof v === 'string' && v.trim() && Number.isFinite(Date.parse(v)) ? Date.parse(v) : fb));

export const roundPct = (num, den) => (den === null || den === undefined || den <= 0 ? null : Math.round((num / den) * 1000) / 10);
export const fmtPct = pct => (pct === null ? 'n/a' : `${pct.toFixed(1)}%`);

export function validateTimezone(timezone) {
  const tz = typeof timezone === 'string' && timezone.trim() ? timezone.trim() : 'UTC';
  try { new Intl.DateTimeFormat('en-US', { timeZone: tz }).format(0); return tz; }
  catch { throw Object.assign(new Error(`Invalid IANA timezone "${timezone}".`), { code: 'invalid-timezone' }); }
}

/** Extract wall-clock parts in any IANA timezone using `Intl.DateTimeFormat` (zero hardcoded offsets). */
export function localDateParts(ms, timezone) {
  const dtf = new Intl.DateTimeFormat('en-US', {
    timeZone: timezone, weekday: 'short', year: 'numeric', month: '2-digit', day: '2-digit',
    hour: '2-digit', minute: '2-digit', second: '2-digit', hourCycle: 'h23',
  });
  const m = {};
  for (const p of dtf.formatToParts(new Date(ms))) if (p.type !== 'literal') m[p.type] = p.value;
  return {
    weekday: WEEKDAY_INDEX[m.weekday] ?? 0, year: Number(m.year), month: Number(m.month), day: Number(m.day),
    hour: Number(m.hour === '24' ? 0 : m.hour), minute: Number(m.minute), second: Number(m.second),
  };
}

/** Resolve exact UTC ms for a local wall-clock anchor (`year, month, day, hour`) in `timezone` (DST-safe). */
export function localAnchorUtcMs(year, month, day, hour = 0, timezone = 'UTC') {
  const tz = validateTimezone(timezone), targetUtc = Date.UTC(year, month - 1, day, hour, 0, 0, 0);
  let guess = targetUtc;
  for (let i = 0; i < 6; i++) {
    const p = localDateParts(guess, tz);
    const diff = Date.UTC(p.year, p.month - 1, p.day, p.hour, p.minute, p.second, 0) - targetUtc;
    if (diff === 0) break;
    guess -= diff;
  }
  return guess;
}

function parseDateArg(date) {
  if (isObj(date) && posInt(date.year) && posInt(date.month) && posInt(date.day)) {
    return { text: date.text ?? `${String(date.year).padStart(4, '0')}-${String(date.month).padStart(2, '0')}-${String(date.day).padStart(2, '0')}`, year: date.year, month: date.month, day: date.day };
  }
  if (typeof date !== 'string' || !/^\d{4}-\d{2}-\d{2}$/.test(date.trim())) {
    throw Object.assign(new Error(`Invalid date "${date ?? ''}". Expected YYYY-MM-DD.`), { code: 'invalid-date' });
  }
  const text = date.trim(), [year, month, day] = text.split('-').map(Number), probe = new Date(Date.UTC(year, month - 1, day));
  if (probe.getUTCFullYear() !== year || probe.getUTCMonth() !== month - 1 || probe.getUTCDate() !== day) {
    throw Object.assign(new Error(`Invalid calendar date "${text}". Expected YYYY-MM-DD.`), { code: 'invalid-date' });
  }
  return { text, year, month, day };
}

/** Compute DST-safe 09:00-09:00 standup window boundaries (23h spring-forward, 25h fall-back, 24h standard). */
export function resolveStandupWindow({ now = Date.now(), date = null, timezone = DEFAULT_STANDUP_TIMEZONE, anchorHour = DEFAULT_STANDUP_HOUR } = {}) {
  const tz = validateTimezone(timezone);
  const finish = (label, startMs, endMs, endExclusiveMs) => ({
    key: 'standup', label, timezone: tz, anchorHour, startMs, endMs, endExclusiveMs,
    startAt: new Date(startMs).toISOString(), endAt: new Date(endMs).toISOString(),
    durationHours: Math.round(((endExclusiveMs - startMs) / HOUR_MS) * 1000) / 1000,
  });
  if (date !== null && date !== undefined && date !== '') {
    const d = parseDateArg(date), prev = new Date(Date.UTC(d.year, d.month - 1, d.day - 1));
    const startMs = localAnchorUtcMs(prev.getUTCFullYear(), prev.getUTCMonth() + 1, prev.getUTCDate(), anchorHour, tz);
    const endExclusiveMs = localAnchorUtcMs(d.year, d.month, d.day, anchorHour, tz);
    return finish(`Standup ${d.text} (9am-9am)`, startMs, endExclusiveMs - 1, endExclusiveMs);
  }
  const nowMs = parseMs(now, null);
  if (nowMs === null) throw Object.assign(new Error(`Invalid timestamp "${now ?? ''}".`), { code: 'invalid-now' });
  const local = localDateParts(nowMs, tz), prev = new Date(Date.UTC(local.year, local.month - 1, local.day - 1));
  const todayAnchor = localAnchorUtcMs(local.year, local.month, local.day, anchorHour, tz);
  const startMs = localAnchorUtcMs(prev.getUTCFullYear(), prev.getUTCMonth() + 1, prev.getUTCDate(), anchorHour, tz);
  const endMs = nowMs >= todayAnchor ? todayAnchor - 1 : nowMs;
  const label = tz === DEFAULT_STANDUP_TIMEZONE ? 'Standup (9am-9am PT)' : 'Standup (9am-9am)';
  return finish(label, startMs, endMs, endMs + 1);
}

/** Shared summary builder for `metrics-model.mjs` overview/stages funnel line. */
export function buildFunnelSummary({ pool, poolDisplay, taken, pr, merged, regressions, regressionsComplete = true }) {
  const takenPct = pool !== null ? roundPct(taken, pool) : null, prPct = roundPct(pr, taken);
  const mergedOfPrPct = roundPct(merged, pr), mergedOfTakenPct = roundPct(merged, taken), rawRegPct = roundPct(regressions, merged);
  const incompleteZero = !regressionsComplete && merged > 0 && regressions === 0;
  const incompletePartial = !regressionsComplete && merged > 0 && regressions > 0;
  const regressionsPct = incompleteZero ? null : rawRegPct;
  const regPart = incompleteZero ? '? Regressions (scan incomplete)'
    : incompletePartial ? `${regressions}+ Regressions (${rawRegPct.toFixed(1)}%+)` : `${regressions} Regressions (${fmtPct(regressionsPct)})`;
  const line = `${poolDisplay} Pool -> ${taken} Taken (${fmtPct(takenPct)}) -> ${pr} PRs (${fmtPct(prPct)}) -> ${merged} Merged (${fmtPct(mergedOfPrPct)} of PRs, ${fmtPct(mergedOfTakenPct)} of Taken) | ${regPart}`;
  return { pool, poolDisplay, taken, takenPct, pr, prPct, merged, mergedOfPrPct, mergedOfTakenPct, regressions, regressionsPct, line };
}

const normalizeGateBucket = raw => {
  const v = lower(raw);
  return !v ? 'not-run' : PASS_GATES.has(v) ? 'pass' : FAIL_GATES.has(v) ? 'fail' : RUNNING_GATES.has(v) ? 'running' : 'not-run';
};

function canonicalRecord(raw, idx) {
  const repo = asText(raw.repo).trim() || 'default/repo', issue = posInt(raw.issue) ? raw.issue : null;
  const attempt = asText(raw.attemptId ?? raw.attempt).trim();
  const id = asText(raw.id).trim() || (issue ? `${repo.toLowerCase()}#${issue}${attempt ? `@${attempt}` : ''}` : `item-${idx + 1}`);
  const status = lower(raw.status ?? raw.outcome), hint = lower(raw.disposition ?? raw.holdReason ?? raw.reasonCode ?? raw.skipReason);
  const stageIdx = STAGE_RANK[lower(raw.stage)] ?? -1;

  const humanMerged = raw.humanMerged === true || lower(raw.mergeSource ?? raw.mergedBy) === 'human' || status === 'human-merged';
  const merged = raw.merged === true || raw.autoMerged === true || humanMerged || status === 'merged' || status === 'auto-merged' || stageIdx >= 4;
  const autoMerged = merged && !humanMerged;
  const wouldMerge = !merged && (raw.wouldMerge === true || status === 'would-merge');
  const realHold = !merged && !wouldMerge && (raw.realHold === true || REAL_HOLD_SIGNALS.has(status) || REAL_HOLD_SIGNALS.has(hint));
  const missingCapacity = !merged && !wouldMerge && !realHold && (raw.missingCapacity === true || CAPACITY_SIGNALS.has(status) || CAPACITY_SIGNALS.has(hint));
  const pr = merged || wouldMerge || raw.prCreated === true || posInt(raw.pr) || stageIdx >= 3;
  const claimed = pr || raw.claimed === true || stageIdx >= 2 || ['running', 'ended', 'failed', 'stopped', 'released', 'abandoned'].includes(status);
  const eligible = claimed || missingCapacity || raw.eligible === true || (!realHold && raw.eligible !== false);
  const regressed = merged && (raw.regressed === true || raw.reopened === true || raw.reverted === true || (Array.isArray(raw.regressionIssues) && raw.regressionIssues.length > 0));
  const disposition = autoMerged ? 'autoMerged' : humanMerged ? 'humanMerged' : wouldMerge ? 'wouldMerge'
    : realHold ? 'realHold' : missingCapacity ? 'missingCapacity' : status === 'running' ? 'inProgress' : 'dropped';
  const reachedStage = merged ? 'merged' : pr ? 'pr' : claimed ? 'claimed' : eligible ? 'eligible' : 'considered';
  const atMs = parseMs(raw.mergedAt ?? raw.at ?? raw.updatedAt ?? raw.startedAt, 0);
  const rank = merged ? 6 : wouldMerge ? 5 : pr ? 4 : claimed ? 3 : eligible ? 2 : 1;
  return {
    id, repo, issue, prNumber: posInt(raw.pr) ? raw.pr : null, atMs, rank,
    stages: { considered: true, eligible, claimed, pr, merged }, reachedStage, disposition,
    autoMerged, humanMerged, wouldMerge, realHold, missingCapacity, regressed, gates: isObj(raw.gates) ? raw.gates : {},
  };
}

/**
 * Compute canonical `considered -> eligible -> claimed -> pr -> merged` stage funnel with honest `%`
 * separating autoMerged, humanMerged, wouldMerge, realHold, missingCapacity, regressed, and never mixing `not-run` into pass counts.
 */
export function computeStageFunnel(records = [], { gates = ['runtime', 'vectors', 'formal', 'suite', 'review', 'ci'] } = {}) {
  const byId = new Map();
  for (let i = 0; i < (Array.isArray(records) ? records.length : 0); i++) {
    if (!isObj(records[i])) continue;
    const rec = canonicalRecord(records[i], i), prev = byId.get(rec.id);
    if (!prev || rec.rank > prev.rank || (rec.rank === prev.rank && rec.atMs >= prev.atMs)) byId.set(rec.id, rec);
  }
  const items = [...byId.values()].sort((a, b) => a.id.localeCompare(b.id));
  const counts = {
    considered: items.length, eligible: 0, claimed: 0, pr: 0, merged: 0,
    autoMerged: 0, humanMerged: 0, wouldMerge: 0, realHold: 0, missingCapacity: 0, regressed: 0, inProgress: 0, dropped: 0,
  };
  const gateStats = Object.fromEntries(gates.map(g => [g, { passed: 0, failed: 0, running: 0, notRun: 0, applicable: 0, passPct: null }]));

  for (const item of items) {
    if (item.stages.eligible) counts.eligible += 1;
    if (item.stages.claimed) counts.claimed += 1;
    if (item.stages.pr) counts.pr += 1;
    if (item.stages.merged) counts.merged += 1;
    for (const k of ['autoMerged', 'humanMerged', 'wouldMerge', 'realHold', 'missingCapacity', 'regressed']) if (item[k]) counts[k] += 1;
    if (item.disposition === 'inProgress') counts.inProgress += 1;
    if (item.disposition === 'dropped') counts.dropped += 1;
    for (const g of gates) {
      const b = normalizeGateBucket(item.gates[g]), cell = gateStats[g];
      if (b === 'pass') { cell.passed += 1; cell.applicable += 1; }
      else if (b === 'fail') { cell.failed += 1; cell.applicable += 1; }
      else if (b === 'running') cell.running += 1;
      else cell.notRun += 1;
    }
  }
  for (const g of gates) gateStats[g].passPct = roundPct(gateStats[g].passed, gateStats[g].applicable);

  const rates = {
    eligiblePct: roundPct(counts.eligible, counts.considered),
    takenPct: roundPct(counts.claimed, counts.eligible),
    takenOfConsideredPct: roundPct(counts.claimed, counts.considered),
    prPct: roundPct(counts.pr, counts.claimed),
    mergedPct: roundPct(counts.merged, counts.pr),
    mergedOfClaimedPct: roundPct(counts.merged, counts.claimed),
    autoMergedPct: roundPct(counts.autoMerged, counts.pr),
    regressionPct: roundPct(counts.regressed, counts.merged),
  };
  return { schema: FUNNEL_SCHEMA, stages: FUNNEL_STAGES, items, counts, rates, gateStats };
}

/** Extract `REOPENED_EVENT` timestamps from GitHub GraphQL issue timeline nodes. */
export function extractGraphQlReopenedEvents(graphqlData, { repo = null } = {}) {
  const out = [];
  const collect = (repoName, nodes) => {
    for (const issue of Array.isArray(nodes) ? nodes : []) {
      if (!isObj(issue) || !posInt(issue.number)) continue;
      for (const ev of Array.isArray(issue.timelineItems?.nodes) ? issue.timelineItems.nodes : []) {
        if (!isObj(ev) || (ev.__typename && ev.__typename !== 'ReopenedEvent')) continue;
        const ts = parseMs(ev.createdAt ?? ev.created_at, null);
        if (ts !== null) out.push({ repo: repoName ?? repo, issue: issue.number, reopenedAt: new Date(ts).toISOString(), actor: asText(ev.actor?.login) || null });
      }
    }
  };
  if (Array.isArray(graphqlData)) { collect(repo, graphqlData); return out; }
  const root = isObj(graphqlData?.data) ? graphqlData.data : graphqlData;
  if (!isObj(root)) return out;
  for (const val of Object.values(root)) {
    if (!isObj(val)) continue;
    const repoName = asText(val.nameWithOwner).trim() || repo;
    collect(repoName, val.issues?.nodes);
    collect(repoName, val.closedIssues?.nodes);
  }
  return out;
}

/**
 * Mature 7-day post-merge cohort tracker separating mature (`>= 7d`) vs immature (`< 7d`) merges.
 * Counts GraphQL `REOPENED_EVENT` timestamps, reverts, and linked follow-up defect issues strictly at/after merge.
 */
export function evaluateMatureCohort(merges = [], {
  now = Date.now(), maturityDays = DEFAULT_COHORT_MATURITY_DAYS, reopenedEvents = [], reverts = [], followUpIssues = [],
} = {}) {
  const nowMs = parseMs(now, null);
  if (nowMs === null) throw Object.assign(new Error(`Invalid timestamp "${now ?? ''}".`), { code: 'invalid-now' });
  const days = typeof maturityDays === 'number' && Number.isFinite(maturityDays) && maturityDays > 0 ? maturityDays : DEFAULT_COHORT_MATURITY_DAYS;
  const maturityMs = days * DAY_MS;

  const indexList = (list, keyFn) => {
    const map = new Map();
    for (const row of Array.isArray(list) ? list : []) {
      if (!isObj(row)) continue;
      for (const k of keyFn(row)) if (k) map.set(k, [...(map.get(k) ?? []), row]);
    }
    return map;
  };
  const rk = (r, type, num) => (posInt(num) ? `${lower(r)}#${type}:${num}` : null);
  const reopensByKey = indexList(reopenedEvents, r => [rk(r.repo, 'issue', r.issue), rk(r.repo, 'pr', r.pr)]);
  const revertsByKey = indexList(reverts, r => [rk(r.repo, 'pr', r.pr), rk(r.repo, 'issue', r.issue)]);
  const followUpsByKey = indexList(followUpIssues, r => [rk(r.repo, 'pr', r.pr ?? r.targetPr), rk(r.repo, 'issue', r.targetIssue ?? r.linkedIssue)]);
  const makeBucket = () => ({ total: 0, clean: 0, regressed: 0, reopened: 0, reverted: 0, followUpDefects: 0, items: [] });
  const mature = makeBucket(), immature = makeBucket();

  for (const m of Array.isArray(merges) ? merges : []) {
    if (!isObj(m)) continue;
    const mergedAtMs = parseMs(m.mergedAt, null);
    if (mergedAtMs === null || mergedAtMs > nowMs) continue;
    const repo = asText(m.repo).trim() || 'default/repo', issue = posInt(m.issue) ? m.issue : null, pr = posInt(m.pr) ? m.pr : null;
    const ageMs = nowMs - mergedAtMs, isMature = ageMs >= maturityMs;
    const keys = [rk(repo, 'issue', issue), rk(repo, 'pr', pr), rk('', 'issue', issue), rk('', 'pr', pr)].filter(Boolean);

    const reopenTs = [
      ...(m.reopenedAt ? [parseMs(m.reopenedAt, null)] : []),
      ...(Array.isArray(m.reopenedEvents) ? m.reopenedEvents.map(e => parseMs(isObj(e) ? (e.createdAt ?? e.reopenedAt ?? e.at) : e, null)) : []),
      ...keys.flatMap(k => (reopensByKey.get(k) ?? []).map(e => parseMs(e.reopenedAt ?? e.createdAt ?? e.at, null))),
    ].filter(ts => ts !== null && ts >= mergedAtMs).sort((a, b) => a - b);
    const reopened = reopenTs.length > 0 || (m.reopened === true && !m.reopenedAt);
    const reopenedAt = reopenTs.length > 0 ? new Date(reopenTs[0]).toISOString() : null;

    const revertMatches = keys.flatMap(k => revertsByKey.get(k) ?? []);
    const revertTs = [...(m.revertedAt ? [parseMs(m.revertedAt, null)] : []), ...revertMatches.map(e => parseMs(e.revertedAt ?? e.createdAt ?? e.at, null))]
      .filter(ts => ts !== null && ts >= mergedAtMs).sort((a, b) => a - b);
    const reverted = revertTs.length > 0 || m.reverted === true || revertMatches.some(e => parseMs(e.revertedAt ?? e.createdAt ?? e.at, null) === null);
    const revertedAt = revertTs.length > 0 ? new Date(revertTs[0]).toISOString() : null;

    const followSet = new Set(Array.isArray(m.followUpIssues ?? m.regressionIssues) ? (m.followUpIssues ?? m.regressionIssues).filter(posInt) : []);
    const followTs = [];
    for (const k of keys) for (const f of followUpsByKey.get(k) ?? []) {
      const createdMs = parseMs(f.createdAt ?? f.at, null);
      if (createdMs !== null && createdMs < mergedAtMs) continue;
      if (posInt(f.issue ?? f.number)) followSet.add(f.issue ?? f.number);
      if (createdMs !== null) followTs.push(createdMs);
    }
    const linkedFollowUps = [...followSet].sort((a, b) => a - b);
    const regressed = reopened || reverted || linkedFollowUps.length > 0;
    const allTs = [...reopenTs, ...revertTs, ...followTs].sort((a, b) => a - b);
    const item = {
      id: asText(m.id).trim() || `${repo.toLowerCase()}#${pr ? `pr:${pr}` : `issue:${issue}`}`, repo, issue, pr,
      mergedAt: new Date(mergedAtMs).toISOString(), ageDays: Math.round((ageMs / DAY_MS) * 100) / 100, mature: isMature,
      cohortStatus: isMature ? (regressed ? 'mature-regressed' : 'mature-clean') : (regressed ? 'immature-regressed' : 'immature-clean'),
      regressed, reopened, reopenedAt, reverted, revertedAt, followUpIssues: linkedFollowUps,
      earliestRegressionAt: allTs.length > 0 ? new Date(allTs[0]).toISOString() : null,
    };
    const b = isMature ? mature : immature;
    b.total += 1;
    if (regressed) b.regressed += 1; else b.clean += 1;
    if (reopened) b.reopened += 1;
    if (reverted) b.reverted += 1;
    if (linkedFollowUps.length > 0) b.followUpDefects += 1;
    b.items.push(item);
  }

  const allTotal = mature.total + immature.total, allRegressed = mature.regressed + immature.regressed;
  return {
    maturityDays: days, asOf: new Date(nowMs).toISOString(),
    mature: { ...mature, regressionPct: roundPct(mature.regressed, mature.total) },
    immature: { ...immature, earlyRegressionPct: roundPct(immature.regressed, immature.total) },
    all: { total: allTotal, matureCount: mature.total, immatureCount: immature.total, regressed: allRegressed, regressionPct: roundPct(allRegressed, allTotal) },
  };
}
