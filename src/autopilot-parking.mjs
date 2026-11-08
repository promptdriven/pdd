// Source: prompts/cli/autopilot-parking.prompt.md.
import {environmentRecovery} from './autopilot-environment.mjs';

const ended = run => ['completed', 'cancelled'].includes(run.state);
export function blockerFor(run) {
  if (ended(run)) return null;
  if (run.blockedOn) return run.blockedOn;
  if (run.runtimeWait) return {kind: 'interpreter', until: null};
  if (run.question && !run.question.answeredAt || run.gate) return {kind: 'person', until: null};
  if (environmentRecovery(run)) return {kind: 'environment', until: null};
  if (run.state === 'waiting' && run.pr?.length) return {kind: 'ci', until: run.pr.at(-1).url};
  return null;
}
const label = blocker => blocker?.kind === 'dependency' ? `needs #${blocker.until}`
  : blocker?.kind === 'pdd' ? `needs ${blocker.until}` : blocker?.kind ?? 'unknown';
export function parkingSummary(runs, limit) {
  const live = runs.filter(run => !ended(run)), parked = live.filter(run => run.parking?.phase === 'parked');
  const blockers = {};
  for (const run of parked) {const name = label(run.parking.blocker); blockers[name] = (blockers[name] ?? 0) + 1;}
  return {working: live.length - parked.length, parked: parked.length, blockers, wakePending: [], limit};
}
export function parkingWords(summary, interpreter) {
  const s = summary ?? {working: 0, parked: 0, blockers: {}, limit: 0};
  return `working ${s.working} of ${s.limit} · parked ${s.parked}${s.parked ? ` (${Object.entries(s.blockers).map(([name, count]) => `${name} ${count}`).join(', ')})` : ''}`
    + (interpreter?.testMode ? ` · interpreter: test mode (${interpreter.streak} no-verdict in a row)` : '');
}
export async function reconcileParking(state, ports, {wakeRules = [], wake = false, policy = {}, release = true} = {}) {
  const limit = state.runs ?? state.checkCapacity?.runs ?? 1;
  const owned = run => !ended(run) && run.repo?.toLowerCase() === state.repo.toLowerCase()
    && run.automaticOrigin?.coordinatorId === state.coordinatorId && run.automaticOrigin?.machine === state.machine
    && run.sourceRoot === state.cwd;
  const list = async () => (await ports.list()).filter(owned);
  let runs = await list();
  for (const run of runs) {
    if (run.parking?.phase === 'waking') continue;
    const blocker = blockerFor(run) ?? await ports.observeBlocker?.(run);
    if (!blocker && !run.parking) continue;
    const progress = await ports.checkProgress(run);
    if (progress) continue;
    await ports.park(run, blocker ?? run.parking.blocker);
  }
  runs = await list();
  const oldest = runs.filter(run => run.parking).sort((a, b) => a.parking.at - b.parking.at || a.number - b.number);
  const ready = [];
  if (wake) for (const run of oldest) {
    if (!['parked', 'waking'].includes(run.parking.phase)) continue;
    const rule = wakeRules.find(rule => rule.number === run.number && ['runtime-ready', 'environment-ready'].includes(rule.kind));
    if (run.parking.phase === 'waking' || await ports.blockerCleared(run, rule)) ready.push({run, rule});
  }
  let summary = parkingSummary(runs, limit);
  for (const {run, rule} of ready) {
    if (run.parking.phase !== 'waking' && summary.working >= limit) {summary.wakePending.push(run.number); continue;}
    const result = await ports.wake(run, rule);
    if (result?.recovery === 'resumed') {
      const index = wakeRules.indexOf(rule); if (index >= 0) wakeRules.splice(index, 1);
    } else summary.wakePending.push(run.number);
    summary.working = parkingSummary(await list(), limit).working;
  }
  // Wake-up wins at the timeout boundary. Failed cleanup/resume retains its slot.
  if (wake && release) {
    const hours = Number.isFinite(policy.hours) && policy.hours > 0 ? policy.hours : 48;
    const maxParked = Number.isSafeInteger(policy.maxParked) && policy.maxParked > 0 ? policy.maxParked : 2 * limit;
    const parked = (await list()).filter(run => run.parking?.phase === 'parked').sort((a, b) => a.parking.at - b.parking.at || a.number - b.number);
    let excess = Math.max(0, parked.length - maxParked);
    for (const run of parked) if (ports.now() - run.parking.at >= hours * 3600000 || excess > 0) {
      const released = await ports.release(run);
      if (released) excess = Math.max(0, excess - 1);
    }
  }
  const final = parkingSummary(await list(), limit);
  final.wakePending = summary.wakePending.filter(number => !ended((runs.find(run => run.number === number) ?? {})));
  return final;
}
