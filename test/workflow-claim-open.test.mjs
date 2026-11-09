import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync} from 'node:fs';
import {openRun, resumeStoppedRun, parkBlockedRun, wakeParkedRun, runStatus, stepDone} from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const origin = {repository: 'example/project', coordinatorId: 'owner-a', machine: 'machine-a',
  claim: {commentId: '11', labelEventId: '12'}};
const winner = run => ({issue: run.issue.url, active: true, owner: origin.coordinatorId,
  coordinatorId: origin.coordinatorId, machine: origin.machine, ...origin.claim});
const effects = calls => calls.filter(args => args[0] === 'pane' && args[1] === 'run'
  || args[0] === 'agent' && args[1] === 'prompt' || args.includes('focus') || args.includes('attach'));

async function ready(t, route) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref: '17', cwd: f.source}, f.ports)).exitCode, 0);
  const run = f.record();
  assert.ok(run.chats.at(-1).session?.id);
  run.automaticOrigin = structuredClone(origin);
  if (route === 'historical') run.area = 1;
  writeRun(run);
  f.observation = {localOwner: origin.coordinatorId, claims: [winner(run)]};
  f.ports.owners = {read: async () => {
    if (f.observation instanceof Error) throw f.observation;
    return {json: JSON.stringify(f.observation)};
  }};
  const args = {ref: '17', cwd: f.source, packageRoot, coordinatorId: origin.coordinatorId, machine: origin.machine};
  if (route === 'wake' || route === 'parked-open') {
    const paused = f.record(); paused.state = 'paused';
    paused.blockedOn = {kind: 'dependency', until: '18'}; writeRun(paused);
    const parked = await parkBlockedRun({...args, blocker: {kind: 'dependency', until: '18'}}, f.ports);
    assert.equal(parked.recovery, 'parked', parked.message);
  } else if (route === 'resume') {
    f.herdr.paneOf(run.chats.at(-1)).agent = null;
    f.tick(120000);
  } else if (route === 'missing-tab') {
    const chat = run.chats.at(-1);
    f.herdr.tabs = f.herdr.tabs.filter(tab => tab.tab_id !== chat.tabId);
    f.herdr.panes = f.herdr.panes.filter(pane => pane.pane_id !== chat.paneId);
  }
  f.action = () => route === 'resume' ? resumeStoppedRun(args, f.ports)
    : route === 'wake' ? wakeParkedRun({...args, at: f.record().parking.at}, f.ports)
      : openRun({...args, cwd: route === 'parked-open' ? f.source : f.record().root, ...(route === 'new' ? {newSession: true} : {}),
        ...(['area', 'historical'].includes(route) ? {area: f.record().areas[0].name} : {})}, f.ports);
  f.herdr.calls.length = 0;
  return f;
}

for (const route of ['open', 'area', 'historical', 'new', 'missing-tab', 'resume', 'wake', 'parked-open']) {
  test(`claim transfer refuses ${route}, retains work and releases identified local chats`, async t => {
    const f = await ready(t, route), before = f.record();
    f.observation.claims = [{...winner(before), owner: 'owner-b', coordinatorId: 'owner-b',
      machine: 'machine-b', commentId: '21', labelEventId: '22'}];
    const result = await f.action();
    assert.notEqual(result.exitCode, 0, `claim-transfer-${route}`);
    assert.equal(effects(f.herdr.calls).length, 0);
    assert.match(result.message, /claim|ownership/i);
    const after = f.record();
    assert.equal(after.state, 'cancelled');
    assert.equal(after.cancelled.state, 'handed-over');
    for (const key of ['runId', 'root', 'branch', 'area', 'done', 'decisions', 'gate', 'question', 'pr', 'automaticOrigin', 'parking'])
      assert.deepEqual(after[key], before[key], key);
    assert.ok(existsSync(before.root));
    if (route === 'missing-tab') {
      // A missing tab without a prior close checkpoint has uncertain custody.
      // The existing cleanup owner must retain that fact, never claim release.
      assert.ok(after.cleanupKept.length > 0);
      assert.match(result.message, /kept/i);
    } else {
      assert.equal(f.herdr.panes.filter(p => p.workspace_id === before.layout.workspaceId).length, 0);
      assert.equal(after.layout.phase, 'closed');
    }
    assert.equal(f.pushes.length, 0); assert.equal(f.prs.length, 0);
    f.herdr.calls.length = 0;
    const repeated = await openRun({ref: '17', cwd: f.source, packageRoot, newSession: true}, f.ports);
    assert.notEqual(repeated.exitCode, 0);
    assert.match(repeated.message, /hand|claim|ownership/i);
    assert.doesNotMatch(repeated.message, /(?:codex resume|claude --resume)/);
    assert.equal(effects(f.herdr.calls).length, 0);
    const progress = await stepDone({step: 'plan', summary: 'Old worker continues', cwd: before.root}, f.agentPorts());
    assert.notEqual(progress.exitCode, 0);
    assert.match(progress.message, /claim|ownership/i);
  });
}

for (const route of ['open', 'resume', 'wake']) {
  for (const observation of ['unavailable', 'absent', 'expired', 'ambiguous', 'malformed', 'missing-local-owner', 'inconsistent-winner', 'same-machine']) {
    test(`${route} refuses ${observation} ownership without a handover or chat effects`, async t => {
      const f = await ready(t, route), before = f.record(), claim = winner(before);
      f.observation = observation === 'unavailable' ? Error('Synthetic ownership outage')
        : {localOwner: origin.coordinatorId, claims: observation === 'absent' ? []
          : observation === 'expired' ? [{...claim, active: false}]
            : observation === 'ambiguous' ? [claim, {...claim, machine: 'machine-b'}]
              : observation === 'missing-local-owner' ? [{...claim, machine: 'machine-b'}]
                : observation === 'inconsistent-winner' ? [{...claim, machine: 'machine-b', owner: 'other'}]
                  : observation === 'malformed' ? [{...claim, machine: ''}]
                : [{...claim, owner: 'new-coordinator', coordinatorId: 'new-coordinator'}]};
      if (observation === 'missing-local-owner') delete f.observation.localOwner;
      const result = await f.action();
      assert.notEqual(result.exitCode, 0, `claim-${observation}-${route}`);
      assert.equal(effects(f.herdr.calls).length, 0);
      assert.deepEqual(f.record(), before);
      assert.equal(f.herdr.calls.filter(args => args[0] === 'tab' && args[1] === 'close').length, 0);
    });
  }
  test(`${route} permits the matching admitted claim`, async t => {
    const f = await ready(t, route), before = f.record();
    const result = await f.action();
    assert.equal(result.exitCode, 0, result.message);
    if (route !== 'open') assert.equal(result.recovery, 'resumed', result.message);
    assert.equal(f.record().chats.at(-1).session.id, before.chats.at(-1).session.id);
    assert.equal(f.record().runId, before.runId);
    assert.deepEqual(f.record().cancelled, before.cancelled);
  });
}

test('manual open keeps its saved chat without an ownership read', async t => {
  const f = await ready(t, 'open'), run = f.record(); delete run.automaticOrigin; writeRun(run);
  f.ports.owners.read = async () => assert.fail('Manual chat must not read claims');
  assert.equal((await f.action()).exitCode, 0);
});

for (const route of ['open', 'wake']) test(`handover survives a failed close and ${route} retries only local cleanup`, async t => {
  const f = await ready(t, 'open');
  if (route === 'wake') {
    // Retained waking custody may contain a live resumed chat after a crash.
    const run = f.record();
    run.parking = {at: f.clock, phase: 'waking', blocker: {kind: 'dependency', until: '18'}};
    writeRun(run);
    f.action = () => wakeParkedRun({ref: '17', cwd: f.source, at: run.parking.at,
      coordinatorId: origin.coordinatorId, machine: origin.machine, packageRoot}, f.ports);
  }
  const before = f.record();
  f.observation.claims = [{...winner(before), machine: 'machine-b', owner: 'owner-b', coordinatorId: 'owner-b'}];
  const herdr = f.ports.herdr; let refuseClose = true;
  f.ports.herdr = args => {
    if (refuseClose && args[0] === 'tab' && args[1] === 'close') throw Error('Synthetic close outage');
    return herdr(args);
  };
  const first = await f.action();
  assert.notEqual(first.exitCode, 0);
  assert.equal(f.record().cancelled.state, 'handed-over');
  assert.ok(f.record().cleanupKept.length > 0);
  assert.match(first.message, /kept/i);
  refuseClose = false;
  f.ports.owners.read = async () => assert.fail('Saved handover needs no new ownership read');
  const second = await f.action();
  assert.notEqual(second.exitCode, 0);
  assert.equal(f.record().layout.phase, 'closed');
  assert.deepEqual(f.record().cleanupKept, []);
  assert.equal(effects(f.herdr.calls).length, 0);
});

test('handover keeps a caller pane and refuses to attach or dispatch', async t => {
  const f = await ready(t, 'open'), before = f.record();
  f.observation.claims = [{...winner(before), machine: 'machine-b', owner: 'owner-b', coordinatorId: 'owner-b'}];
  f.ports.env.HERDR_PANE_ID = before.chats.at(-1).paneId;
  const result = await f.action();
  assert.notEqual(result.exitCode, 0);
  assert.equal(f.record().cancelled.state, 'handed-over');
  assert.ok(f.herdr.paneOf(before.chats.at(-1)));
  assert.ok(f.record().cleanupKept.some(item => item.reason === 'caller-pane'));
  assert.equal(effects(f.herdr.calls).length, 0);
});
