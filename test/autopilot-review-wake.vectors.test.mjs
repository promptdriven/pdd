import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { runAutopilotLauncher, tickAutopilot } from '../src/autopilot-launcher.mjs';

// Native replays of the approved review-wake cases. No Runtime interface or
// Runtime scenario exists for this launcher; these are native evidence only.
const issue = (number, extra = {}) => ({
  number, state: 'open', title: `Issue ${number}`, body: 'Owner asks for work',
  user: { login: 'owner' }, created_at: '2026-11-04T00:01:00Z', updated_at: '2026-11-04T00:01:00Z',
  comments: 0, labels: [], html_url: `https://github.com/owner/repo/issues/${number}`, ...extra,
});
const review = (extra = {}) => ({
  id: 1001, user: { login: 'helper' }, author_association: 'NONE', state: 'CHANGES_REQUESTED',
  body: 'Please revise the timeout.', submitted_at: '2026-11-04T00:10:00Z', commit_id: 'synthetic-head', ...extra,
});
const packet = f => JSON.parse(f.prompts.at(-1).trim().split('\n').at(-1));
const reviewsIn = f => packet(f).issues.find(row => row.number === 70).pullRequests[0].reviews;
const reply = (value, status = 200, headers = {}) => ({
  code: status >= 400 ? 1 : 0, stderr: '',
  stdout: `HTTP/2.0 ${status}\r\n${Object.entries(headers).map(([key, value]) => `${key}: ${value}\r\n`).join('')}\r\n${status === 304 ? '' : JSON.stringify(value)}`,
});

async function fixture(t, initialReviews = [[]]) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-review-wake-'));
  const cwd = join(dir, 'repo'), home = join(dir, 'home'), stateRoot = join(dir, 'state');
  mkdirSync(cwd); mkdirSync(home);
  const f = {
    time: Date.parse('2026-11-04T00:00:00Z'), issueVersion: 1, pageVersions: initialReviews.map(() => 1),
    rows: [issue(70), issue(90, { body: 'Fixes #70', pull_request: {} })],
    detail: { state: 'open', draft: false, merged: false, head: { sha: 'synthetic-head' } },
    reviewPages: structuredClone(initialReviews), comments: [], permissions: {}, requests: [], warnings: [],
    prompts: [], attempts: 0, failures: 0, agentStatus: 'idle', modelCalls: 0,
  };
  f.setTrust = names => writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'observe', trust: names } }));
  f.setTrust(['helper']);
  f.addReview = (row = review(), page = 0) => { f.reviewPages[page].push(row); f.pageVersions[page]++; };
  f.ports = {
    stateRoot, platform: 'linux', env: { HOME: home }, now: () => f.time,
    readRunProgress: async () => [], warn: text => f.warnings.push(text),
    reconcileDependencyIntake: async () => ({ eligible: f.rows.map(row => row.html_url), queued: [], skipped: [] }),
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }),
    pathDiagnostic: () => [], timer: async () => true,
    run: async (command, args) => {
      if (['codex', 'claude', 'agy', 'gemini'].includes(command)) f.modelCalls++;
      if (command === 'git') return { code: 0, stdout: `${cwd}\n`, stderr: '' };
      if (command === 'herdr' && args[0] === '--version') return { code: 0, stdout: '1.0', stderr: '' };
      if (command === 'loginctl') return { code: 0, stdout: 'yes\n', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo","url":"https://github.com/owner/repo"}', stderr: '' };
      assert.ok(command === 'gh' && args[0] === 'api' && args.includes('GET'), `Unexpected process: ${command} ${args.join(' ')}`);
      const endpoint = args[args.indexOf('GET') + 1], request = { endpoint, args: [...args] };
      f.requests.push(request);
      if (endpoint.startsWith('repos/owner/repo/issues?')) {
        const etag = `"issues-${f.issueVersion}"`;
        request.status = args.includes(`If-None-Match: ${etag}`) ? 304 : 200;
        return reply(f.rows, request.status, { ETag: etag });
      }
      if (endpoint === 'repos/owner/repo/pulls/90') return reply(f.detail);
      if (endpoint.startsWith('repos/owner/repo/issues/90/comments')) return reply(f.comments);
      if (endpoint.startsWith('repos/owner/repo/pulls/90/reviews')) {
        if (f.reviewFailure) return f.reviewFailure;
        const page = Number(endpoint.match(/[?&]page=(\d+)/)?.[1] ?? 1) - 1;
        const etag = `"reviews-${page}-${f.pageVersions[page]}"`;
        request.status = args.includes(`If-None-Match: ${etag}`) ? 304 : 200;
        return reply(f.reviewPages[page], request.status, {
          ETag: etag, ...(page + 1 < f.reviewPages.length ? {
            Link: `<https://api.github.com/repos/owner/repo/pulls/90/reviews?per_page=100&page=${page + 2}>; rel="next"`,
          } : {}),
        });
      }
      const login = endpoint.match(/\/collaborators\/([^/]+)\/permission$/)?.[1];
      if (login) return typeof f.permissions[login] === 'object' ? f.permissions[login] : reply({ permission: f.permissions[login] ?? 'read' });
      assert.fail(`Unexpected GitHub read: ${endpoint}`);
    },
    herdr: async args => {
      const live={pane_id:'fake-pane',workspace_id:'fake-workspace',cwd,foreground_cwd:cwd,tab_id:'t',terminal_id:'term',agent:'codex',agent_status:f.agentStatus,agent_session:'session'};
      if (args[0] === 'workspace') return { result: { type:'workspace_info', root_pane: { pane_id: 'fake-pane' }, workspace: { workspace_id: 'fake-workspace' } } };
      if (args[0] === 'pane' && args[1] === 'get') return {result:{type:'pane_info',pane:live}};
      if (args[0] === 'pane' && args[1] === 'run') { f.agentStarted = true; return {}; }
      if (args[0] === 'pane' && args[1] === 'read') return '';
      if (args[0] === 'agent' && args[1] === 'get') { if (!f.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' }); return { result: { type:'agent_info', agent:live } }; }
      assert.ok(args[0] === 'agent' && args[1] === 'prompt', `Unexpected Herdr action: ${args.join(' ')}`);
      f.attempts++;
      if (f.failures) { f.failures--; throw Error('Synthetic delivery failure'); }
      const instruction = args.at(-1), match = /Artifact path: (.+)/.exec(instruction);
      f.prompts.push(match ? readFileSync(JSON.parse(match[1]), 'utf8') : instruction); return {};
    },
  };
  t.after(() => { rmSync(dir, { recursive: true, force: true }); assert.equal(f.modelCalls, 0, 'Review discovery must make no model call (AC4).'); });
  const started = await runAutopilotLauncher({ command: 'start', cwd, env: { HOME: home }, packageRoot: resolve('.') }, f.ports);
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(f.prompts.length, 1, 'The fake Herdr port captures the start-up recipe.');
  assert.deepEqual(f.warnings, []);
  f.prompts.length = 0; f.requests.length = 0; f.attempts = 0;
  f.stateFile = join(stateRoot, readdirSync(stateRoot).find(name => name.endsWith('.json')));
  f.state = () => JSON.parse(readFileSync(f.stateFile, 'utf8'));
  f.tick = () => tickAutopilot(f.stateFile, f.ports);
  return f;
}

for (const metadata of ['unchanged issues 304', 'changed PR timestamp 200']) {
  test(`AC1/2/4: trusted request-changes review wakes once with ${metadata}`, async t => {
    const f = await fixture(t), originalIssue = structuredClone(f.rows[0]), originalDetail = structuredClone(f.detail);
    f.addReview();
    if (metadata.endsWith('200')) { f.rows[1].updated_at = '2026-11-04T00:10:00Z'; f.issueVersion++; }
    await f.tick();
    assert.equal(f.prompts.length, 1, 'A new trusted review must wake the idle agent once (issue 2952).');
    assert.deepEqual(reviewsIn(f), [{ id: 1001, author: 'helper', submittedAt: '2026-11-04T00:10:00Z', state: 'CHANGES_REQUESTED', body: 'Please revise the timeout.', commit: 'synthetic-head' }]);
    assert.deepEqual(f.rows[0], originalIssue); assert.deepEqual(f.detail, originalDetail);
    assert.equal(f.rows[1].comments, 0); assert.deepEqual(f.comments, []);
    for (let tick = 0; tick < 4; tick++) await f.tick();
    assert.equal(f.prompts.length, 1, 'An unchanged review must not wake it again.');
    assert.equal(f.requests[0].status, metadata.endsWith('304') ? 304 : 200);
    assert.deepEqual(f.warnings, []);
  });
}

for (const state of ['APPROVED', 'COMMENTED']) test(`AC1/2/4: a new trusted ${state} submission wakes once`, async t => {
  const f = await fixture(t); f.addReview(review({ state }));
  await f.tick(); assert.equal(f.prompts.length, 1); assert.equal(reviewsIn(f)[0].state, state);
  await f.tick(); assert.equal(f.prompts.length, 1);
});

test('AC2/4: association alone grants no trust; later packets exclude outsider reviews', async t => {
  const f = await fixture(t);
  f.addReview(review({ id: 1000, user: { login: 'outsider' }, author_association: 'MEMBER', body: 'OUTSIDER REVIEW' }));
  await f.tick(); assert.equal(f.prompts.length, 0);
  f.addReview(); await f.tick(); assert.equal(f.prompts.length, 1);
  assert.deepEqual(reviewsIn(f).map(row => row.id), [1001]); assert.doesNotMatch(f.prompts[0], /OUTSIDER REVIEW/);
  await f.tick(); assert.equal(f.prompts.length, 1);
});

for (const status of ['working', 'blocked', 'unknown']) test(`AC1/3/4: ${status} delivery keeps both reviews pending`, async t => {
  const f = await fixture(t); f.agentStatus = status; f.addReview();
  await f.tick(); await f.tick(); assert.equal(f.prompts.length, 0); assert.equal(f.attempts, 0);
  f.addReview(review({ id: 1002, body: 'Also cover the timeout limit.' }));
  await f.tick(); assert.equal(f.attempts, 0);
  f.agentStatus = 'idle'; await f.tick(); assert.equal(f.prompts.length, 1);
  assert.deepEqual(reviewsIn(f).map(row => row.id), [1001, 1002]);
  await f.tick(); assert.equal(f.prompts.length, 1);
});

test('AC3/4: a failed idle delivery consumes no review', async t => {
  const f = await fixture(t); f.addReview(); f.failures = 1;
  await assert.rejects(f.tick(), /Synthetic delivery failure/); assert.equal(f.prompts.length, 0);
  await f.tick(); assert.equal(f.prompts.length, 1); assert.equal(f.attempts, 2);
  assert.equal(reviewsIn(f)[0].id, 1001);
  await f.tick(); assert.equal(f.prompts.length, 1); assert.equal(f.attempts, 2);
});

test('AC2/3/4: unavailable authority defers a submission until write access is confirmed', async t => {
  const f = await fixture(t);
  f.permissions.writer = reply({ message: 'Resource not accessible' }, 403, { 'x-ratelimit-remaining': 499 });
  f.addReview(review({ user: { login: 'writer' } })); await f.tick();
  assert.equal(f.prompts.length, 0); assert.equal(f.warnings.length, 1); assert.equal(f.state().retryAt, undefined);
  f.permissions.writer = 'write'; await f.tick(); assert.equal(f.prompts.length, 1);
  assert.equal(reviewsIn(f)[0].author, 'writer');
  await f.tick(); assert.equal(f.prompts.length, 1);
});

for (const authority of ['explicit', 'write']) test(`AC2/3/4: revoked pending ${authority} trust never forwards review text`, async t => {
  const f = await fixture(t);
  if (authority === 'write') { f.setTrust([]); f.permissions.helper = 'write'; }
  f.agentStatus = 'working'; f.addReview(review({ body: 'REVOKED REVIEW' })); await f.tick();
  assert.equal(f.prompts.length, 0);
  f.setTrust([]); f.permissions.helper = 'read'; f.agentStatus = 'idle';
  await f.tick(); assert.equal(f.prompts.length, 0, 'Revocation alone must not become work.');
  f.addReview(review({ id: 1002, user: { login: 'outsider' }, body: 'OUTSIDER REVIEW' }));
  await f.tick(); assert.equal(f.prompts.length, 0);
  f.rows[0].body = 'New owner instruction'; f.issueVersion++; await f.tick();
  assert.equal(f.prompts.length, 1); assert.match(f.prompts[0], /New owner instruction/);
  assert.deepEqual(reviewsIn(f), []); assert.doesNotMatch(f.prompts[0], /REVOKED REVIEW|OUTSIDER REVIEW/);
});

test('AC1/2/4: existing submitted reviews establish a quiet baseline', async t => {
  const f = await fixture(t, [[review()]]);
  for (let tick = 0; tick < 4; tick++) await f.tick();
  assert.equal(f.prompts.length, 0);
  assert.ok(f.requests.filter(row => row.endpoint.includes('/reviews')).every(row => row.status === 304));
  assert.equal(f.requests.filter(row => row.endpoint.endsWith('/permission')).length, 0, 'Unchanged ticks need no permission lookup.');
});

test('AC1/2/4: conditional review pages find a new submission beyond an unchanged first page', async t => {
  const f = await fixture(t, [[review({ id: 998 })], [review({ id: 999 })]]);
  f.addReview(review(), 1); await f.tick(); assert.equal(f.prompts.length, 1);
  assert.deepEqual(reviewsIn(f).map(row => row.id), [998, 999, 1001]);
  const reads = f.requests.filter(row => row.endpoint.includes('/reviews'));
  assert.deepEqual(reads.map(row => row.status), [304, 200]);
  assert.ok(reads.every(row => row.args.includes('per_page=100') || row.endpoint.includes('per_page=100')));
  assert.ok(reads.every(row => row.args.some(value => value.startsWith('If-None-Match: '))));
  f.requests.length = 0; await f.tick(); assert.equal(f.prompts.length, 1);
  assert.deepEqual(f.requests.filter(row => row.endpoint.includes('/reviews')).map(row => row.status), [304, 304]);
  assert.equal(f.requests.filter(row => row.endpoint === 'repos/owner/repo/pulls/90').length, 0, 'Review reads do not refetch unchanged PR details.');
});

test('AC3/4: an ordinary review lookup failure defers its issue while unrelated work proceeds', async t => {
  const f = await fixture(t);
  f.rows.push(issue(71)); f.issueVersion++; await f.tick(); f.prompts.length = 0;
  f.addReview(); f.reviewFailure = reply({ message: 'Resource not accessible' }, 403, { 'x-ratelimit-remaining': 499 });
  f.rows[2].body = 'Independent owner instruction'; f.issueVersion++; await f.tick();
  assert.equal(f.prompts.length, 1); assert.deepEqual(packet(f).issues.map(row => row.number), [71]);
  assert.equal(f.state().retryAt, undefined); assert.equal(f.warnings.length, 1);
  delete f.reviewFailure; await f.tick(); assert.equal(f.prompts.length, 2);
  assert.deepEqual(packet(f).issues.map(row => row.number), [70]); assert.equal(reviewsIn(f)[0].id, 1001);
});

for (const status of [429, 403]) test(`AC3/4: review HTTP ${status} rate limit stops further GitHub reads until reset`, async t => {
  const f = await fixture(t), resetAt = f.time + 60 * 60 * 1000;
  f.addReview(); f.reviewFailure = reply({ message: 'Forbidden' }, status, { 'x-ratelimit-remaining': 0, 'x-ratelimit-reset': resetAt / 1000 });
  f.rows.push(issue(71)); f.issueVersion++; await f.tick();
  assert.equal(f.prompts.length, 0); assert.equal(f.state().retryAt, resetAt);
  assert.equal(f.requests.at(-1).endpoint, 'repos/owner/repo/pulls/90/reviews?per_page=100');
  const reads = f.requests.length; await f.tick(); assert.equal(f.requests.length, reads);
  delete f.reviewFailure; f.time = resetAt; await f.tick(); assert.equal(f.prompts.length, 1);
  assert.deepEqual(packet(f).issues.map(row => row.number), [70, 71]);
  assert.equal(reviewsIn(f)[0].id, 1001);
});
