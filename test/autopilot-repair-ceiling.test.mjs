import test from 'node:test';
import assert from 'node:assert/strict';
import { startRun, stepDone, approveRun } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

// Issue #3041: an Autopilot run gets at most 5 repair rounds in one area. A manual run
// keeps its skill's own 2-repair rule, and pdd does not refuse its reruns.
async function buildArea(t, { automatic }) {
  const f = await fixture(t, { name: 'small-change', agent: 'codex' });
  f.ports.env = { HOME: f.ports.env.HOME };
  assert.equal((await startRun({ name: 'small-change', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  const run = f.record(); f.tick();
  await stepDone({ step: 'scope', summary: 'plan', cwd: run.root }, f.agentPorts());
  f.tick(); assert.equal((await approveRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  if (automatic) {
    const saved = f.record();
    saved.automaticOrigin = { repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: { commentId: '11', labelEventId: '12' } };
    writeRun(saved);
  }
  const done = async (step, summary) => { f.tick(); return stepDone({ step, summary, cwd: run.root }, f.agentPorts()); };
  return { f, done };
}

test('repair ceiling: the 5th failed round refuses a 6th in an Autopilot run; a manual run is not refused', async t => {
  const auto = await buildArea(t, { automatic: true });
  assert.equal((await auto.done('change', 'first change')).exitCode, 0);
  for (let round = 1; round <= 5; round++) {
    assert.equal((await auto.done('verify', `✗ round ${round - 1} fails`)).exitCode, 0);
    const again = await auto.done('change', `repair ${round}`);
    assert.equal(again.exitCode, 0, again.message);
    assert.match(again.message, /warning: change ran again after verify/);
    assert.match(again.message, new RegExp(`Repair round ${round} of 5 in the build area`));
  }
  assert.equal((await auto.done('verify', '✗ round 5 fails')).exitCode, 0);
  const refused = await auto.done('change', 'repair 6');
  assert.equal(refused.exitCode, 1);
  assert.match(refused.message, /refused another repair round: the build area of this Autopilot run has had 5 repair rounds/);
  assert.match(refused.message, /pdd:stuck.*one comment with the cause.*one stuck alert.*keep the claim and progress/);
  const kept = auto.f.record();
  assert.deepEqual(kept.repairRounds, { build: 5 });
  assert.equal(kept.done.change.summary, 'repair 5', 'the refused round is not recorded');
  assert.equal(kept.done.verify.summary, '✗ round 5 fails', 'the failed check stays as the cause');
  assert.equal(auto.f.pushes.length, 0);

  const manual = await buildArea(t, { automatic: false });
  assert.equal((await manual.done('change', 'first change')).exitCode, 0);
  for (let round = 1; round <= 6; round++) {
    assert.equal((await manual.done('verify', `✗ round ${round - 1} fails`)).exitCode, 0);
    const again = await manual.done('change', `repair ${round}`);
    assert.equal(again.exitCode, 0, again.message);
    assert.match(again.message, /warning: change ran again after verify/);
    assert.doesNotMatch(again.message, /Repair round/);
  }
  assert.equal(manual.f.record().repairRounds, undefined, 'a manual run saves no count');
});
