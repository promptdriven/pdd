import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync } from 'node:fs';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { createGithubRepoFake } from './helpers/github-repo-fake.mjs';

const src = process.env.PDD_WRITE_TEST_SOURCE || new URL('../src/', import.meta.url).pathname;
const { refreshClaimHeartbeat } = await import(pathToFileURL(join(src, 'issue-dependencies-github.mjs')));
const { countGithubCalls: counter } = await import(pathToFileURL(join(src, 'github-calls.mjs')));
const api = (method, path) => ['api', '--include', '--method', method, path];

test('shared write admission stops dispatch before a second write even when its purpose is claims', async () => {
  let sent = 0, used = 0;
  const refused = Object.assign(Error('budget'), { code: 'github_write_budget', retryAt: 10 });
  const run = counter(async () => { sent++; return { code: 0, stdout: '{}' }; }, {
    writes: async () => ({ reserve: () => { if (used++) throw refused; }, observe: () => {} }),
  });
  await run('gh', api('PATCH', 'repos/acme/widgets/issues/comments/1'), { purpose: 'claims' });
  await assert.rejects(run('gh', api('PATCH', 'repos/acme/widgets/issues/comments/2'), { purpose: 'claims' }), { code: 'github_write_budget' });
  assert.equal(sent, 1);
});

test('GraphQL queries do not spend content budget, mutations do', async () => {
  let used = 0;
  const run = counter(async () => ({ code: 0, stdout: '{}' }), { writes: async () => ({ reserve: n => { used += n; }, observe: () => {} }) });
  await run('gh', [...api('POST', 'graphql'), '--input', '-'], { input: JSON.stringify({ query: 'query { viewer { login } }' }) });
  assert.equal(used, 0);
  await run('gh', [...api('POST', 'graphql'), '--input', '-'], { input: JSON.stringify({ query: 'mutation { addComment(input: {}) { clientMutationId } }' }) });
  assert.equal(used, 1);
});

test('one replayed day: a live claim needs twelve heartbeat writes, with no read for a fresh heartbeat', async t => {
  let time = Date.parse('2026-11-07T00:00:00Z');
  const fake = createGithubRepoFake({ repository: 'acme/widgets', issues: 1, now: () => time });
  const comment = fake.claim(1, { coordinatorId: 'a', machine: 'one', actor: 'acme' });
  const claim = { active: true, issue: 'https://github.com/acme/widgets/issues/1', coordinatorId: 'a', machine: 'one', commentId: comment.id,
    labelEventId: fake.issues.get(1).timeline[0].id, lastSeen: new Date(time).toISOString() };
  for (let tick = 1; tick <= 48; tick++) {
    time += 30 * 60_000;
    const result = await refreshClaimHeartbeat({ repository: 'acme/widgets', claim, coordinatorId: 'a', machine: 'one', at: new Date(time).toISOString() }, { execFile: (_file, args, options) => fake.gh(args, options) });
    if (result.state === 'refreshed') claim.lastSeen = result.lastSeen;
  }
  const writes = fake.calls.filter(c => c.method === 'PATCH');
  t.diagnostic(JSON.stringify({ dayHeartbeatWrites: writes.length, dayHeartbeatReads: fake.calls.length - writes.length }));
  assert.equal(writes.length, 12, 'heartbeat cadence must leave two hours before claim expiry');
  assert.equal(fake.calls.length, 24, 'fresh heartbeat must make no read');
});

// The baseline adapter is the original separate label commands and append-only
// progress path. Both routes use the same fake world and old/new native heartbeat.
test('the same day workload uses 288 content requests and keeps eight progress comments', async () => {
  const {replayWriteDay}=await import('./helpers/github-write-day.mjs');
  const result=await replayWriteDay({src,baseline:!existsSync(join(src,'github-write-proxy.mjs'))});
  assert.equal(result.writes,288);
  assert.equal(result.postComments,8);
});
