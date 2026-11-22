// Retired #3053/JSON-comment dependency intake; minimal zero-legacy compat stub retained only for frozen src/workflow-runner.mjs and src/pdd-cli.mjs until Train 2 Tail / Train 4 L1 cleanup.
import { parkingSummary } from './autopilot-parking.mjs';
import { projectIssueGraph, issueKey } from './issue-dependencies.mjs';
import { createDependencyReadPorts, readDependencySnapshot } from './issue-dependencies-github.mjs';

const snapshotRead = (ports, args) => (ports.snapshots?.read ? ports.snapshots.read(args) : readDependencySnapshot(args, ports));
const root = (key, repository) => key.toLowerCase().startsWith(`https://github.com/${repository.toLowerCase()}/issues/`);
const json = value => (typeof value === 'string' ? JSON.parse(value) : value);

export async function checkDependencyStart({ cwd = '', repository, issue, coordinator }, ports = {}) {
  try {
    ports = createDependencyReadPorts({ cwd }, ports);
    const subjectNumber = Number(issueKey(issue)?.split('/').pop());
    if (Number.isSafeInteger(subjectNumber)) ports.dependencyReads?.live(repository, subjectNumber);
    const [settings, read, ownerReply] = await Promise.all([
      ports.settings.read({ cwd, repository }),
      snapshotRead(ports, { cwd, repository }),
      ports.owners.read({ repository, issues: [issue] }),
    ]);
    const owners = json(ownerReply.json);
    const snapshot = read.snapshot;
    if (settings.mode === 'off') return { allowed: false, reason: 'off' };
    if (settings.healthPaused === true) return { allowed: false, reason: 'health' };
    const key = issueKey(issue);
    const selected = key && root(key, repository) ? key : null;
    const claim = selected && (owners.claims || []).find(x => issueKey(x.issue) === selected && x.active);
    if (!coordinator || coordinator.repository?.toLowerCase() !== repository.toLowerCase() || !coordinator.coordinatorId
      || owners.localOwner !== coordinator.coordinatorId || !coordinator.machine
      || !coordinator.claim?.commentId || !coordinator.claim?.labelEventId
      || !claim || claim.owner !== coordinator.coordinatorId || claim.coordinatorId !== coordinator.coordinatorId
      || claim.machine !== coordinator.machine || claim.commentId !== coordinator.claim.commentId
      || claim.labelEventId !== coordinator.claim.labelEventId) {
      return { allowed: false, reason: 'owner' };
    }
    if (settings.activation !== coordinator.activation || settings.runs !== coordinator.runs) return { allowed: false, reason: 'stale' };
    if (owners.runsKnown !== true || !Array.isArray(owners.runs)) return { allowed: false, reason: 'runs' };
    const slots = new Map();
    for (const run of owners.runs) {
      const slotKey = run.runId || run.issue;
      const working = run.working ?? (run.occupied === true || parkingSummary([run], 1).working > 0);
      const prior = slots.get(slotKey);
      slots.set(slotKey, { run, working: working || prior?.working === true });
    }
    const occupied = [...slots.values()].filter(slot => slot.working).map(slot => slot.run);
    const runCap = settings.runs ?? settings.capacityRuns;
    if (runCap !== undefined) {
      if (!Number.isSafeInteger(runCap) || runCap < 1) return { allowed: false, reason: 'runs' };
      if (occupied.length + (occupied.some(x => selected && issueKey(x.issue) === selected) ? 0 : 1) > runCap) {
        return { allowed: false, reason: 'runs' };
      }
      const parkedCap = settings.maxParked ?? 2 * runCap;
      if (!Number.isSafeInteger(parkedCap) || parkedCap < 1 || slots.size - occupied.length >= parkedCap) {
        return { allowed: false, reason: 'parked' };
      }
    }
    if (owners.runs.some(run => selected && issueKey(run.issue) === selected)) return { allowed: false, reason: 'dependency' };
    const copy = structuredClone(snapshot);
    const subject = copy.issues.find(x => selected && issueKey(x.key) === selected);
    if (subject && subject.executionClaim?.coordinatorId === claim.coordinatorId
      && subject.executionClaim?.commentId === claim.commentId
      && subject.executionClaim?.labelEventId === claim.labelEventId) {
      subject.execution = 'idle';
      subject.holds = subject.holds.filter(x => !/^(running|claim|claimed)$/i.test(x));
    }
    const node = projectIssueGraph({ snapshot: copy }).nodes.find(x => selected && issueKey(x.key) === selected);
    if (!node || node.reasons.includes('Incomplete relevant observations')) return { allowed: false, reason: 'unknown' };
    if (node.eligible && ports.checkPaneCapacity) {
      try { await ports.checkPaneCapacity(); }
      catch (error) { return { allowed: false, reason: error.code === 'herdr_pane_budget' ? 'panes' : 'unknown' }; }
    }
    return node.eligible ? { allowed: true, reason: 'ok' } : { allowed: false, reason: 'dependency' };
  } catch {
    return { allowed: false, reason: 'unknown' };
  }
}

export async function runDependencyIntake() {
  return {
    exitCode: 2,
    message: 'pdd dependencies prepare|complete has been retired; use pdd autopilot intake and pdd graph.\n',
  };
}
