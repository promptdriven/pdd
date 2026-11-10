// Source: prompts/cli/autopilot-parking.prompt.md.
import {environmentRecovery} from './autopilot-environment.mjs';
import {workflowEnded as ended} from './workflow-runs.mjs';
const stopped = run => ['stuck', 'waiting', 'paused'].includes(run.state);
const reasonFor = run => [run.parkReason, run.question && !run.question.answeredAt ? run.question.text : ''].filter(Boolean).join(' ');
// Route reports are facts from the worker, not decisions made by a model in a tick.
export function routeQuestionFor(run) {
  if (ended(run)) return null;
  if (run.routeWait) return run.routeWait;
  const q = run.question;
  if (!q || q.answeredAt || !/^which supported\b/i.test(q.text ?? '')
    || !/\b(?:native|PDD|verification|replay)\b/i.test(q.text)) return null;
  const absent = /no established [^.]*Runtime operation|no (?:supported |native |PDD |drafting )*(?:command|tool|route)|(?:installed PDD|installed CLI).*(?:no |cannot|missing)|(?:route|command|tool).*(?:does not exist|is missing|is unavailable)/i.test(q.text);
  const kind = /supported native recovery/i.test(q.text) && /PR\s*1/i.test(q.text) ? 'prompt-reentry'
    : /native.*PDD/i.test(q.text) && /draft.*interface|interface.*draft/i.test(q.text) && absent ? 'interface-drafting'
    : /native[- ]only verification/i.test(q.text) && /approved[- ]case replay/i.test(q.text) && /route/i.test(q.text) && absent ? 'native-replay'
    : /native.*PDD/i.test(q.text) && /route|command|tool/i.test(q.text) && absent ? 'supported-route' : null;
  if (!kind) return null;
  const area = run.areas?.[run.area];
  return {kind, step: area?.steps?.find(step => !run.done?.[step]) ?? area?.name ?? '',
    question: q.text, at: q.at, until: kind === 'prompt-reentry' ? '#2897' : `capability:route-${kind}`};
}
export function collectRouteQuestions(ledger = {records: [], groups: []}, runs) {
  const result = structuredClone(ledger);
  for (const run of runs) {
    for (const route of [...(run.routeReports ?? []), routeQuestionFor(run)].filter(Boolean)) {
      const id = JSON.stringify([run.runId, route.kind, route.step, route.question, route.at]);
      if (result.records.some(row => row.id === id)) continue;
      result.records.push({id, ...route, runId: run.runId, run: run.number, issue: run.issue?.url});
      let group = result.groups.find(row => row.kind === route.kind);
      if (!group) {group = {kind: route.kind, count: 0, recordIds: []}; result.groups.push(group);}
      group.recordIds.push(id); group.count = group.recordIds.length;
    }
  }
  return result;
}
export function interpreterWaitFor(run) {
  if (ended(run)) return null;
  if (run.runtimeWait) return run.runtimeWait;
  const cached = run.parking?.blocker?.kind === 'interpreter' ? run.parking.interpreterWait : null;
  const reason = String(run.parkReason ?? '');
  if (!stopped(run) || !(run.stuckCause === 'interpreter' || /pdd:no[- ]verdict|runner-stopped|unknown saved[- ]read/i.test(reason)
    || /interpreter/i.test(reason) && /no[- ]verdict|unknown|runner-stopped|saved[- ](?:batch|read)|outage/i.test(reason)))
    return cached && !reason && !run.stuckCause && JSON.stringify(run.gate ?? null) === JSON.stringify(run.parking.interpreterGate ?? null) ? cached : null;
  const inferred = {at: run.updatedAt ?? run.startedAt ?? 0, reason,
    batch: /\b\d{8}-\d{6}-[a-z0-9]+\b/i.exec(reason)?.[0] ?? null,
    cause: /unknown|runner-stopped/i.test(reason) ? 'unknown' : 'service'};
  return cached && ['reason', 'batch', 'cause'].every(key => cached[key] === inferred[key]) ? cached : inferred;
}
export function blockerFor(run) {
  if (ended(run)) return null;
  if (run.blockedOn) return run.blockedOn;
  if (run.runtimeWait) return {kind: 'interpreter', until: null};
  if (!stopped(run) && !run.parking && !run.gate && !(run.question && !run.question.answeredAt)) return null;
  const question = run.question && !run.question.answeredAt;
  const reason = question ? String(run.question.text ?? '') : reasonFor(run);
  const dependency = /(?:waiting|blocked) (?:for|on|by) (?:issue )?#([1-9][0-9]*) (?:to )?merge/i.exec(reason);
  if (dependency) return {kind: 'dependency', until: dependency[1]};
  const chat = [...(run.chats ?? [])].reverse().find(chat => chat.area === run.areas?.[run.area]?.name);
  const resumedQuestion = !stopped(run) && !run.parking && question && Number.isFinite(chat?.resumedAt) && chat.resumedAt >= run.question.at;
  if (/(?:missing|wait(?:ing)?|needs?|no supported).*#2897/i.test(reason)
    || /(?:no supported|missing|installed PDD has no).*PR\s*1.*(?:current[- ]main|integration|re-entry)/i.test(reason)
    || /supported native recovery.*PR\s*1/i.test(reason)) return resumedQuestion ? null : {kind: 'pdd', until: '#2897'};
  const fix = /missing PDD (?:feature|bug|fix).*?#([1-9][0-9]*)/i.exec(reason);
  if (fix) return resumedQuestion ? null : {kind: 'pdd', until: `#${fix[1]}`};
  const route = routeQuestionFor(run);
  if (route) return {kind: 'pdd-route', until: route.until};
  if (question) return {kind: 'person', until: null};
  if (/binding-missing|missing-binding|unresolved binding contract/i.test(reason)) return {kind:'binding',until:null};
  if (interpreterWaitFor(run)) return {kind: 'interpreter', until: null};
  if (/github.*(?:rate|limit)|(?:account|usage)[- ]limit/i.test(reason)) return {
    kind: /github/i.test(reason) ? 'github' : 'account',
    until: /\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?(?:Z|[+-]\d{2}:\d{2})/.exec(reason)?.[0] ?? null};
  if (/review lease/i.test(reason)) return {kind: 'review', until: run.pr?.at(-1)?.url ?? null};
  if (/waiting for CI|CI (?:pending|result)/i.test(reason)) return {kind: 'ci', until: run.pr?.at(-1)?.url ?? null};
  if (run.question && !run.question.answeredAt || run.gate) return {kind: 'person', until: null};
  if (environmentRecovery(run)) return {kind: 'environment', until: null};
  if (run.state === 'waiting' && run.pr?.length) return {kind: 'ci', until: run.pr.at(-1).url};
  return null;
}
export function idleSince(run) {
  return Math.max(...[[run.progressAt, run.updatedAt, run.startedAt, 0].find(Number.isFinite),
    run.gate?.at, run.question && !run.question.answeredAt ? run.question.at : null,
    run.chatIdleLimit?.at, run.chatResumeLimit?.at].filter(Number.isFinite));
}
export function idleParkingBlocker(run, now, graceMs = 60_000) {
  if (ended(run) || now < idleSince(run) + graceMs) return null;
  return blockerFor(run) ?? (stopped(run) ? {kind: 'unknown', until: null} : null);
}
const label = blocker => blocker?.kind === 'pdd-route' ? 'missing PDD route' : blocker?.kind === 'dependency' ? `needs #${blocker.until}`
  : blocker?.kind === 'pdd' ? `needs ${blocker.until}` : blocker?.kind ?? 'unknown';
const needsGrace = run => run.chatIdleLimit || run.chatResumeLimit || run.state === 'paused' && !run.parkReason && !run.stuckCause;
function closingHold(run, now, blocker = blockerFor({...run, parking: undefined})) {
  if (run.parking?.phase !== 'closing' || blocker) return null;
  if (!stopped(run) && [run.progressAt, run.updatedAt].some(at => Number.isFinite(at) && at > run.parking.at))
    return 'new progress since park';
  if (needsGrace(run) && Number.isFinite(now) && now < idleSince(run) + 60_000)
    return `recovery grace until ${new Date(idleSince(run) + 60_000).toISOString()}`;
  return null;
}
const custody = run => Boolean(run.checkHeld || run.parking?.checkHeld || ['closing', 'waking', 'releasing'].includes(run.parking?.phase));
export function parkingSummary(runs, limit, now) {
  const live = runs.filter(run => !ended(run) || custody(run)), parked = live.filter(run => !ended(run) && run.parking?.phase === 'parked' && !run.parking.checkHeld && !run.checkHeld);
  const reservations = run => run.parking && run.parking.phase !== 'parked' || run.parking?.checkHeld;
  const working = live.filter(run => custody(run) || !parked.includes(run) && !ended(run) && (!stopped(run) || reservations(run) || run.checkHeld)).length;
  const blockers = {};
  for (const run of parked) {const name = label(run.parking.blocker); blockers[name] = (blockers[name] ?? 0) + 1;}
  const closing = live.filter(run => run.parking?.phase === 'closing').map(run => {
    const hold = closingHold(run, now);
    return {number: run.number, reasons: hold ? {[hold]: 1, ...(now - run.parking.at >= 60_000 ? {'closing-retry': 1} : {})}
      : Object.keys(run.parking.closeReasons ?? {}).length ? run.parking.closeReasons : {'cleanup-pending': 1}};
  });
  return {working, parked: parked.length, blockers, wakePending: [], limit, closing};
}
export function parkingWords(summary, interpreter) {
  const s = summary ?? {working: 0, parked: 0, blockers: {}, limit: 0};
  return `working ${s.working} of ${s.limit} · parked ${s.parked}${s.parked ? ` (${Object.entries(s.blockers).map(([name, count]) => `${name} ${count}`).join(', ')})` : ''}`
    + (s.closing?.length ? ` · closing ${s.closing.map(row => `#${row.number} (${Object.entries(row.reasons).map(([reason,count]) => `${reason} ${count}`).join(', ')})`).join('; ')}` : '')
    + (interpreter?.testMode ? ` · interpreter: test mode (${interpreter.streak} no-verdict in a row)` : '');
}
export async function reconcileParking(state, ports, {wakeRules = [], wake = false, policy = {}, release = true} = {}) {
  const limit = state.runs ?? state.checkCapacity?.runs ?? 1;
  const owned = run => (!ended(run) || custody(run)) && run.repo?.toLowerCase() === state.repo.toLowerCase()
    && run.automaticOrigin?.coordinatorId === state.coordinatorId && run.automaticOrigin?.machine === state.machine
    && run.sourceRoot === state.cwd;
  const list = async () => (await ports.list()).filter(owned);
  let runs = await list();
  for (const run of runs) {
    if (['waking', 'releasing'].includes(run.parking?.phase)) continue;
    if (ended(run)) {
      if (run.parking?.phase !== 'parked' || run.parking.checkHeld !== true || !run.parking.blocker) continue;
      if (await ports.checkProgress(run)) continue;
      await ports.park(run, run.parking.blocker);
      continue;
    }
    const chat = [...(run.chats ?? [])].reverse().find(chat => chat.area === run.areas?.[run.area]?.name);
    if (!run.parking && ['area-end', 'run-end', 'budget', 'cancel'].includes(chat?.closed?.reason)) continue;
    // Classify current facts before consulting the park's cached inference.
    // A finished check can change its saved result at an unchanged gate.
    const saved = blockerFor({...run, parking: undefined});
    // Native check/limit evidence can refine a generic gate; explicit named waits win.
    const observed = !saved || saved.kind === 'person' ? await ports.observeBlocker?.(run) : null;
    // Unclassified stops also release native resources after a short grace.
    // Their original recovery counters and alert custody survive the park.
    const graceHold = needsGrace(run);
    if (closingHold(run, ports.now(), observed ?? saved)) continue;
    const blocker = observed ?? saved ?? run.parking?.blocker
      ?? (stopped(run) && !graceHold ? {kind: 'unknown', until: null} : idleParkingBlocker(run, ports.now()));
    if (!blocker && !run.parking) continue;
    const progress = await ports.checkProgress(run);
    if (progress && !run.parking) continue;
    await ports.park(run, blocker ?? run.parking.blocker);
    if (blocker?.kind === 'unknown' && !run.chatIdleLimit && !run.chatResumeLimit && run.state !== 'paused') {
      const key = JSON.stringify([run.runId, run.parkReason ?? null, run.question ?? null]);
      state.parkingAlerts ??= {};
      if (!state.parkingAlerts[key] && await ports.alertUnknown?.(run) === true) state.parkingAlerts[key] = true;
    }
  }
  runs = await list();
  const oldest = runs.filter(run => run.parking).sort((a, b) => a.parking.at - b.parking.at || a.number - b.number);
  const ready = [];
  if (wake) for (const run of oldest) {
    if (!['parked', 'waking'].includes(run.parking.phase) || run.parking.checkHeld || await ports.checkProgress(run)) continue;
    const rule = wakeRules.find(rule => rule.number === run.number && ['runtime-ready', 'environment-ready'].includes(rule.kind));
    if (run.parking.phase === 'waking' || await ports.blockerCleared(run, rule)) ready.push({run, rule});
  }
  const summarize = async rows => parkingSummary(await Promise.all(rows.map(async run =>
    stopped(run) && !run.parking && await ports.checkProgress(run) ? {...run, checkHeld: true} : run)), limit, ports.now());
  let summary = await summarize(runs);
  let occupancy = summary.working;
  for (const {run, rule} of ready) {
    if (run.parking.phase !== 'waking' && occupancy >= limit) {summary.wakePending.push(run.number); continue;}
    const result = await ports.wake(run, rule);
    if (result?.recovery === 'resumed') {
      const index = wakeRules.indexOf(rule); if (index >= 0) wakeRules.splice(index, 1);
    } else summary.wakePending.push(run.number);
    occupancy = (await summarize(await list())).working;
  }
  // Wake-up wins at the timeout boundary. Failed cleanup/resume retains its slot.
  if (wake && release) {
    const hours = Number.isFinite(policy.hours) && policy.hours > 0 ? policy.hours : 48;
    const maxParked = Number.isSafeInteger(policy.maxParked) && policy.maxParked > 0 ? policy.maxParked : 2 * limit;
    const parked = (await list()).filter(run => ['parked', 'releasing'].includes(run.parking?.phase) && !run.parking.checkHeld).sort((a, b) => a.parking.at - b.parking.at || a.number - b.number);
    let excess = Math.max(0, parked.length - maxParked);
    for (const run of parked) if (run.parking.phase === 'releasing' || ports.now() - run.parking.at >= hours * 3600000 || excess > 0) {
      if (await ports.checkProgress(run)) continue;
      const released = await ports.release(run);
      if (released) excess = Math.max(0, excess - 1);
    }
  }
  const final = await summarize(await list());
  final.wakePending = summary.wakePending.filter(number => !ended((runs.find(run => run.number === number) ?? {})));
  return final;
}
