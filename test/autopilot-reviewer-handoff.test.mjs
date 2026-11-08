import test from 'node:test';
import assert from 'node:assert/strict';
import { autopilotGithubWorld } from './helpers/autopilot-github-world.mjs';

test('dependency request delivery stops if chat readiness outlives the reviewer generation', async t => {
  const source = process.env.REVIEW_NEXT_MULTI_SOURCE;
  const w = await autopilotGithubWorld({ src: source, issues: 1, machine: 'reviewer-a' });
  t.after(() => w.cleanup());
  const other = await autopilotGithubWorld({ src: source, issues: 1, machine: 'reviewer-b', sharedGithub: w.github });
  t.after(() => other.cleanup());
  const originalHerdr = w.ports.herdr;
  let waited = false, successor;
  w.ports.herdr = async args => {
    const stored = w.github.contents.get('pdd/autopilot-reviewer');
    if (!waited && stored && args[0] === 'agent' && args[1] === 'get') {
      waited = true;
      const lease = JSON.parse(Buffer.from(stored.content, 'base64').toString('utf8'));
      w.time = Date.parse(lease.expiresAt) + 1000;
      other.time = w.time;
      assert.equal((await other.invoke('start')).exitCode, 0);
      assert.equal(other.requests.length, 1, 'the successor has started current analysis');
      successor = JSON.parse(other.requests[0].contextJson).reviewer;
      assert.notEqual(successor.generation, lease.generation);
    }
    return originalHerdr(args);
  };
  const result = await w.invoke('start');
  assert.equal(result.exitCode, 0);
  assert.equal(waited, true, 'the native wake waits for chat readiness after lease acquisition');
  assert.equal(w.requests.length, 0, 'no analysis request starts under an expired generation');
});

test('manual identity is absent before the first launcher and managed after migration', async t => {
  const w = await autopilotGithubWorld({ issues: 0 });
  t.after(() => w.cleanup());
  const { reviewerIdentity } = await import('../src/autopilot-reviewer.mjs');
  assert.equal(await reviewerIdentity({ cwd: w.cwd, repository: w.repository }, w.commandPorts()), null);
  assert.equal((await w.invoke('start')).exitCode, 0);
  const identity = await reviewerIdentity({ cwd: w.cwd, repository: w.repository }, w.commandPorts());
  assert.equal(identity.coordinatorId, w.state().coordinatorId);
  assert.equal(identity.enabled, true);
  await w.invoke('stop');
  assert.equal((await reviewerIdentity({ cwd: w.cwd, repository: w.repository }, w.commandPorts())).enabled, false);
});

test('a direct tick keeps managed authority when only the state filename supplies its root', async t => {
  const w = await autopilotGithubWorld({ issues: 1 });
  t.after(() => w.cleanup());
  assert.equal((await w.invoke('start')).exitCode, 0);
  const request = structuredClone(w.requests[0]);
  const context = JSON.parse(request.contextJson); delete context.reviewer;
  request.contextJson = JSON.stringify(context);
  request.id = 'missing-authority';
  w.agent = 'idle';
  const { tickAutopilot } = await import('../src/autopilot-launcher.mjs');
  const before = w.requests.length;
  await tickAutopilot(w.stateFile(), { ...w.ports, stateRoot: undefined,
    reconcileDependencyIntake: async (_input, { pending }) => {
      await pending.save({ json: JSON.stringify({ requested: 'missing-authority' }) });
      await pending.deliver({ requestJson: JSON.stringify(request) });
      return { eligible: [], queued: [], skipped: [], pending: true };
    },
  });
  assert.equal(w.requests.length, before);
  assert.equal(w.state().dependencyPending.requested, 'missing-authority');
  assert.equal(w.state().dependencyPending.delivered, undefined);
});
