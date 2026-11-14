import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { join } from 'node:path';
import { runCheck } from '../../src/runtime-seam.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';

for (const [twice, codeName] of [[false, 'graph-provider-failure'], [true, 'no-server-verdict']]) test(`simulated terminal no verdict is retried once (${codeName})`, async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check') {
      const count = f.posts.filter(post => post.command === 'check').length;
      if (twice || count === 1) return { status: 200, json: f.check(entry.request.requestId, 'unknown', [], [{code:codeName}]) };
      return { status: 200, json: f.check(entry.request.requestId) };
    }
    return f.normal(entry);
  });
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
  const code = await runCheck({ words:['place-order'], options:{'--json':true}, cwd:setup.repo }, ports);
  const checks = fake.posts.filter(post => post.command === 'check');
  assert.equal(checks.length, 2, ports.stderr.text + ports.stdout.text);
  assert.notEqual(checks[0].request.requestId, checks[1].request.requestId);
  assert.equal(checks[0].request.source_sha256, checks[1].request.source_sha256);
  assert.equal(code, twice ? 3 : 0, ports.stderr.text + ports.stdout.text);
  assert.equal(JSON.parse(ports.stdout.text).rows[0].calls, 2);
});

test('a failed assertion blocks automatic retry', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'check'
    ? { status: 200, json: f.check(entry.request.requestId, 'unknown', [{ criterion_id:'AC1', target:'result', path:'/totalCents', passed:false }], [{code:'graph-provider-failure'}]) }
    : f.normal(entry));
  const { ports } = portsFor({ HOME:setup.home, PDD_RUNTIME_URL:fake.origin, PDD_STATE_DIR:setup.state });
  await runCheck({ words:['place-order'], cwd:setup.repo }, ports);
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 1);
});

test('an uncertain POST is read at the original ID instead of replayed', async t => {
  const setup = harbor(t);
  const fake = await fakeRuntime(t, (entry, f) => entry.method === 'POST' && entry.command === 'check' ? { destroy:true } : f.normal(entry));
  const { ports } = portsFor({ HOME:setup.home, PDD_RUNTIME_URL:fake.origin, PDD_STATE_DIR:setup.state });
  await runCheck({ words:['place-order'], cwd:setup.repo }, ports);
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 1);
});

test('sibling worktrees serialize checks with a shared batch queue and job cap one', async t => {
  const setup = harbor(t), sibling = join(setup.sandbox, 'sibling');
  const git = spawnSync('git', ['worktree', 'add', '--detach', sibling], { cwd:setup.repo, encoding:'utf8' });
  assert.equal(git.status, 0, git.stderr);
  let release, notifyFirst;
  const held = new Promise(done => { release = done; });
  const first = new Promise(done => { notifyFirst = done; });
  const fake = await fakeRuntime(t, async (entry, f) => {
    if (entry.method === 'POST' && entry.command === 'check' && f.posts.filter(post => post.command === 'check').length === 1) {
      notifyFirst(); await held;
    }
    return f.normal(entry);
  });
  const env = { HOME:setup.home, PDD_RUNTIME_URL:fake.origin, PDD_STATE_DIR:setup.state, PDD_MAX_JOBS:'1' };
  const a = portsFor(env), b = portsFor(env);
  const one = runCheck({ words:['place-order'], cwd:setup.repo }, a.ports);
  await first;
  const two = runCheck({ words:['place-order'], cwd:sibling }, b.ports);
  await new Promise(done => setTimeout(done, 200));
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 1);
  release();
  assert.deepEqual(await Promise.all([one, two]), [0, 0]);
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 2);
});

test('live or unavailable compatibility cannot authorize replay', async t => {
  for (const mode of ['live', 'unavailable']) {
    const setup = harbor(t);
    const fake = await fakeRuntime(t, (entry, f) => {
      if (entry.method === 'POST' && entry.command === 'lint') {
        const answer = f.lint(entry.request.requestId);
        for (const item of answer.result.capabilities) for (const operation of item.report.operations) operation.resource_mode = mode === 'live' ? 'live' : 'unknown';
        for (const item of answer.result.report.lint.tests) for (const operation of item.capabilities.operations) operation.resource_mode = mode === 'live' ? 'live' : 'unknown';
        return {status:200, json:answer};
      }
      if (entry.method === 'POST' && entry.command === 'check') return {status:200, json:f.check(entry.request.requestId, 'unknown', [], [{code:'graph-provider-failure'}])};
      return f.normal(entry);
    });
    const { ports } = portsFor({ HOME:setup.home, PDD_RUNTIME_URL:fake.origin, PDD_STATE_DIR:setup.state });
    await runCheck({ words:['place-order'], cwd:setup.repo }, ports);
    assert.ok(fake.posts.filter(post => post.command === 'check').length <= 1, mode);
  }
});
