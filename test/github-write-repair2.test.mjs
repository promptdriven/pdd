import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { createGithubRepoFake } from './helpers/github-repo-fake.mjs';

const source = process.env.PDD_WRITE_REPAIR_SOURCE
  ? pathToFileURL(resolve(process.env.PDD_WRITE_REPAIR_SOURCE) + '/') : new URL('../src/', import.meta.url);
const { githubWriteBudget } = await import(new URL('github-writes.mjs', source));
const { countGithubCalls } = await import(new URL('github-calls.mjs', source));
const { githubWriteRunner } = await import(new URL('github-write-proxy.mjs', source));
const { createDependencyReadPorts, refreshClaimHeartbeat } = await import(new URL('issue-dependencies-github.mjs', source));
const NOW = Date.parse('2026-11-07T00:00:00Z'), HOUR = 3_600_000;
const iso = time => new Date(time).toISOString();
function world(t) {
  const root = fs.mkdtempSync(join(tmpdir(), 'pdd-write-repair2-'));
  t.after(() => fs.rmSync(root, { recursive: true, force: true }));
  return root;
}

for (const graphql of [false, true]) for (const headers of [true, false]) {
  test(`successful ${graphql ? 'GraphQL' : 'REST'} content with ${headers ? 'HTTP headers' : 'JSON only'} leaves writes admitted`, async t => {
    const root = world(t), fake = createGithubRepoFake({ issues: 1, now: () => NOW });
    fake.issues.get(1).body = 'Fix HTTP 429 secondary rate limit handling.\nRetry-After: 900';
    fake.comment(1, 'HTTP 403 abuse limit report');
    const options = { root, env: {}, identity: 'acme', now: () => NOW };
    const args = graphql ? ['api', '--include', 'graphql', '--input', '-']
      : ['api', '--include', 'repos/acme/widgets/issues/1'];
    const input = graphql ? { input: JSON.stringify({ query: 'query { repository { issue { body } } }', variables: { n0: 1 } }) } : {};
    const outcome = await fake.gh(args, input);
    assert.equal(outcome.code, 0);
    assert.match(outcome.stdout, /^HTTP\/\S+ 200 /);
    if (!headers) outcome.stdout = outcome.stdout.split('\r\n\r\n')[1];
    // Exercise both the lazy resolver and an already-resolved budget. The
    // public budget must be safe even when called without the counter.
    let resolutions = 0;
    const budget = githubWriteBudget(options);
    const counter = countGithubCalls(async () => outcome, {
      writes: async () => { resolutions++; return budget; }, now: () => NOW, env: {},
    });
    assert.equal(await counter('gh', args, input), outcome);
    assert.equal(resolutions, 0);
    budget.observe(outcome);
    assert.equal(budget.usage().state, 'normal');
    const run = githubWriteRunner(async (_file, words, opts) => words === args ? outcome : fake.gh(words, opts), options);
    assert.equal(await run('gh', args, input), outcome);
    assert.equal(budget.usage().hour, 0);
    await run('gh', ['api', '--method', 'PATCH', 'repos/acme/widgets/issues/1', '--input', '-'], { input: '{}' });
    assert.equal(fake.calls.filter(call => call.method === 'PATCH').length, 1);
    assert.equal(budget.usage().hour, 1);
  });
}

for (const status of [403, 429]) for (const headers of [true, false]) {
  test(`real ${status} ${headers ? 'response' : 'gh diagnostic'} retains a shared cooldown`, async t => {
    const options = { root: world(t), env: {}, identity: 'acme', now: () => NOW };
    const outcome = headers
      ? { code: 1, stdout: `HTTP/2.0 ${status}\r\nRetry-After: 90\r\n\r\n{}`, stderr: '' }
      : Object.assign(Error('request failed'), { code: 1, stdout: '', stderr: `gh: secondary rate limit (HTTP ${status})` });
    const reader = githubWriteRunner(async () => { if (!headers) throw outcome; return outcome; }, options);
    const args = ['api', 'graphql', '-f', 'query=query { viewer { login } }'];
    if (headers) assert.equal(await reader('gh', args), outcome);
    else await assert.rejects(reader('gh', args), error => error === outcome);
    const budget = githubWriteBudget(options);
    assert.equal(budget.usage().hour, 0);
    assert.throws(() => budget.reserve(1), { code: 'github_write_budget', retryAt: NOW + (headers ? 90_000 : 60_000) });
  });
}

test('successful diagnostics and payload Retry-After lines cannot supply throttle headers', t => {
  const budget = githubWriteBudget({ root: world(t), identity: 'acme', now: () => NOW });
  budget.observe({ code: 0, stdout: '{}', stderr: 'HTTP 429 secondary rate limit' });
  assert.doesNotThrow(() => budget.reserve(1));
  budget.observe({ code: 1, stdout: 'HTTP/2.0 403\r\n\r\nRetry-After: 900' });
  assert.doesNotThrow(() => budget.reserve(1));
});

test('the budget alone ignores successful issue content before any counter filtering', async t => {
  const options = { root: world(t), identity: 'acme', now: () => NOW };
  const budget = githubWriteBudget(options), fake = createGithubRepoFake({ issues: 1, now: () => NOW });
  fake.issues.get(1).body = 'HTTP 429 secondary rate limit\nRetry-After: 900';
  const outcome = await fake.gh(['api', '--include', 'repos/acme/widgets/issues/1']);
  budget.observe(outcome);
  assert.doesNotThrow(() => budget.reserve(1));
  assert.equal(budget.usage().hour, 1);
});

const recordOf = body => JSON.parse(/```json\n([\s\S]*?)\n```/.exec(body)[1]);
async function observedClaim(t, { legacy, age }) {
  const root = world(t); let time = NOW - age;
  const fake = createGithubRepoFake({ issues: 1, now: () => time });
  const comment = fake.claim(1, { coordinatorId: 'owner-a', machine: 'one' });
  if (legacy) {
    const record = recordOf(comment.body); delete record.lastSeen;
    comment.body = 'Legacy claim.\n\n```json\n' + JSON.stringify(record) + '\n```';
  }
  time = NOW;
  const execFile = async (file, args, options) => file === 'gh' ? fake.gh(args, options) : { code: 1, stdout: '', stderr: 'No checkout' };
  const ports = createDependencyReadPorts({ cwd: root }, { execFile, autopilotStateRoot: root,
    authority: { read: async () => ({ authority: 'trusted' }) }, clock: { now: async () => ({ iso: iso(time) }) } });
  const owners = JSON.parse((await ports.owners.read({ repository: 'acme/widgets', issues: ['https://github.com/acme/widgets/issues/1'] })).json);
  const claim = owners.claims[0];
  assert.ok(claim);
  const refresh = (extra = {}) => refreshClaimHeartbeat({ repository: 'acme/widgets', claim, coordinatorId: 'owner-a', machine: 'one', at: iso(NOW), ...extra }, { execFile });
  return { fake, comment, claim, refresh };
}

for (const age of [HOUR, 23 * HOUR]) test(`a live legacy observation at ${age / HOUR} hours receives its first heartbeat`, async t => {
  const { fake, comment, claim, refresh } = await observedClaim(t, { legacy: true, age });
  assert.equal(claim.active, true);
  assert.equal(claim.lastSeen, iso(fake.issues.get(1).updated));
  const before = recordOf(comment.body), mark = fake.mark();
  assert.deepEqual(await refresh(), { state: 'refreshed', lastSeen: iso(NOW) });
  assert.deepEqual(recordOf(comment.body), { ...before, lastSeen: iso(NOW) });
  assert.equal(fake.since(mark).calls.filter(call => call.method === 'PATCH').length, 1);
});

test('legacy expiry and identity checks still prevent a heartbeat', async t => {
  const expired = await observedClaim(t, { legacy: true, age: 25 * HOUR });
  assert.equal(expired.claim.active, false);
  const mark = expired.fake.mark();
  assert.deepEqual(await expired.refresh(), { state: 'skipped' });
  assert.deepEqual(await expired.refresh({ claim: { ...expired.claim, active: true } }), { state: 'skipped' });
  assert.equal(expired.fake.since(mark).calls.length, 0);
  const live = await observedClaim(t, { legacy: true, age: 23 * HOUR });
  // A normalized observation alone cannot authorize a changed comment identity.
  live.comment.body = live.comment.body.replace('owner-a', 'owner-b');
  const next = live.fake.mark();
  assert.deepEqual(await live.refresh(), { state: 'skipped' });
  assert.equal(live.fake.since(next).calls.filter(call => call.method === 'PATCH').length, 0);
});

test('modern observations skip early and expired heartbeats without I/O', async t => {
  for (const age of [HOUR, 4 * HOUR + 1]) {
    const { fake, claim, refresh } = await observedClaim(t, { legacy: false, age });
    const mark = fake.mark();
    if (age > 4 * HOUR) assert.equal(claim.active, false);
    // Even a caller retaining an old active observation cannot revive it.
    assert.deepEqual(await refresh({ claim: { ...claim, active: true } }), { state: 'skipped' });
    assert.equal(fake.since(mark).calls.length, 0);
  }
});
