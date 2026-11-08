import './helpers/test-home.mjs';
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
    readRunProgress: async () => [], warn: text => f.warnings.push(text), allocationCheck: async () => ({ state: 'ready', message: '' }),
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

// Exhaustive finite domains, with expectations derived from the two Stories.
for (const trusted of [false, true]) for (const status of ['idle', 'working', 'blocked', 'unknown']) for (const fail of [false, true]) {
  test(`bounded review trust=${trusted} status=${status} fail=${fail}`, async t => {
    const f = await fixture(t); f.setTrust(trusted ? ['helper'] : []);
    f.agentStatus = status; f.addReview(); f.failures = fail ? 1 : 0;
    if (trusted && status === 'idle' && fail) await assert.rejects(f.tick(), /Synthetic delivery failure/);
    else await f.tick();
    const initial = trusted && status === 'idle' && !fail ? 1 : 0;
    assert.equal(f.prompts.length, initial, 'bounded review: trusted idle delivery');
    f.agentStatus = 'idle'; f.failures = 0;
    await f.tick();
    assert.equal(f.prompts.length, trusted ? 1 : 0, 'bounded review: pending work delivers exactly once');
    if (trusted) assert.deepEqual(reviewsIn(f).map(r => r.id), [1001]);
    await f.tick(); assert.equal(f.prompts.length, trusted ? 1 : 0, 'bounded review: repeat is quiet');
  });
}

for (const rule of ['run', 'claim']) for (const age of [3599999, 3600000, 3600001]) for (const status of ['idle', 'working', 'blocked', 'unknown']) {
  test(`bounded ${rule} age=${age} status=${status}`, async t => {
    const f = await fixture(t); const changedAt = f.time;
    if (rule === 'run') f.ports.readRunProgress = async () => [{ number: 101, changedAt }];
    else {
      f.rows[0].labels = [{ name: 'pdd:working' }];
      f.rows[0].updated_at = new Date(changedAt).toISOString(); f.issueVersion++;
      await f.tick(); f.prompts.length = 0;
    }
    f.agentStatus = status; f.time = changedAt + age; await f.tick();
    const due = age >= 3600000;
    assert.equal(f.prompts.length, due && status === 'idle' ? 1 : 0, 'bounded timer threshold and idle gate');
    f.agentStatus = 'idle'; await f.tick();
    assert.equal(f.prompts.length, due ? 1 : 0, 'bounded timer pending delivery');
    if (due) {
      const events = packet(f).timeRules;
      assert.equal(events.length, 1); assert.equal(events[0].number, rule === 'run' ? 101 : 70);
      assert.equal(events[0].reason.split('\n').length, 1);
      assert.match(events[0].reason, rule === 'run' ? /pdd:stuck/ : /takeover/);
      if (rule === 'claim') assert.equal(packet(f).issues[0].claimed, true);
    }
    await f.tick(); assert.equal(f.prompts.length, due ? 1 : 0, 'bounded timer repeat is quiet');
  });
}
