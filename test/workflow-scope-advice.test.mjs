import test from 'node:test';
import assert from 'node:assert/strict';
import { stepDone } from '../src/workflow-runner.mjs';
import { cancellationFixture } from './helpers/cancellation-fixture.mjs';

for (const summary of ['Recommend `feature` because the scope is larger', 'Recommended workflow: feature', 'Recommended workflow: **pdd-feature**', 'Do not use bug; switch to `feature` instead.']) {
  test(`scope advice retains a positive recommendation: ${summary}`, async t => {
    const f = await cancellationFixture(t);
    const gate = await stepDone({ step: 'scope', summary, cwd: f.old.root }, f.ports);
    assert.equal(gate.exitCode, 0, gate.message);
    const refusal = await f.start({ name: 'bug' });
    assert.equal(refusal.exitCode, 1, refusal.message);
    assert.deepEqual(f.read().scopeRecommendation, { workflow: 'feature', reason: summary }, `Gate:\n${gate.message}\nRefusal:\n${refusal.message}`);
    assert.equal(f.read().done.scope.summary, summary);
    const command = `pdd workflow run feature 17 --replace ${f.old.runId}`;
    assert.ok(gate.message.includes(summary));
    assert.ok(gate.message.includes(command));
    assert.ok(refusal.message.includes(summary));
    assert.ok(refusal.message.includes(command));
  });
}

test('scope advice does not invent a switch from a negated recommendation', async t => {
  const f = await cancellationFixture(t);
  const summary = 'Do not use feature; keep small-change';
  const gate = await stepDone({ step: 'scope', summary, cwd: f.old.root }, f.ports);
  assert.equal(gate.exitCode, 0, gate.message);
  const refusal = await f.start({ name: 'bug' });
  assert.equal(refusal.exitCode, 1, refusal.message);
  assert.equal(f.read().scopeRecommendation, undefined, `Gate:\n${gate.message}\nRefusal:\n${refusal.message}`);
  const command = `pdd workflow run feature 17 --replace ${f.old.runId}`;
  assert.ok(!gate.message.includes(command));
  assert.ok(!refusal.message.includes(command));
});

for (const summary of ['Do not use feature; keep small-change', "Don't recommend `feature`; keep small-change", 'No switch is needed.', 'Recommended workflow: small-change']) {
  test(`re-recording scope clears previous switch advice: ${summary}`, async t => {
    const f = await cancellationFixture(t);
    const previous = await stepDone({ step: 'scope', summary: 'Recommend feature', cwd: f.old.root }, f.ports);
    assert.equal(previous.exitCode, 0, previous.message);
    assert.equal(f.read().scopeRecommendation.workflow, 'feature');
    const gate = await stepDone({ step: 'scope', summary, cwd: f.old.root }, f.ports);
    assert.equal(gate.exitCode, 0, gate.message);
    const refusal = await f.start({ name: 'bug' });
    assert.equal(refusal.exitCode, 1, refusal.message);
    assert.equal(f.read().scopeRecommendation, undefined);
    assert.equal(f.read().done.scope.summary, summary);
    for (const message of [gate.message, refusal.message]) {
      assert.ok(!message.includes('Scope recommends feature:'), message);
      assert.ok(!message.includes(`pdd workflow run feature 17 --replace ${f.old.runId}`), message);
    }
  });
}
