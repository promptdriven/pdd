import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdtempSync, mkdirSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { createHash } from 'node:crypto';
import { countGithubCalls, githubBudget, githubLedger, githubPurpose, githubReply, githubStatusLine, githubUsage, githubEtagCache, nativeGithubCounter } from '../src/github-calls.mjs';
import { createDependencyReadPorts, readDependencySnapshot, saveDependencyReview } from '../src/issue-dependencies-github.mjs';

// Issue #3046: Autopilot counts its GitHub calls, keeps a budget and reads less.
const repo = 'owner/repo', minute = 60 * 1000, hour = 60 * minute;
const NOW = Date.parse('2026-11-06T12:00:00.000Z');
const at = ms => new Date(ms).toISOString();
const key = n => `https://github.com/${repo}/issues/${n}`;
const reset = () => Math.floor(NOW / 1000) + 3600;
// A REST reply as `gh api --include` prints it, with GitHub's rate-limit headers.
const reply = (status, body, { etag, remaining = 4000, resource = 'core', link } = {}) => [
  `HTTP/2.0 ${status} ${status === 304 ? 'Not Modified' : 'OK'}`, ...(etag ? [`Etag: ${etag}`] : []), ...(link ? [`Link: ${link}`] : []),
  'X-Ratelimit-Limit: 5000', `X-Ratelimit-Remaining: ${remaining}`, `X-Ratelimit-Reset: ${reset()}`, `X-Ratelimit-Resource: ${resource}`, `X-Ratelimit-Used: ${5000 - remaining}`,
  '', status === 304 ? '' : JSON.stringify(body)].join('\r\n');
const endpointOf = args => args.find((word, index) => index > 0 && !String(word).startsWith('-') && !['GET', 'POST', 'PATCH'].includes(word) && !/^[A-Z][A-Za-z-]+: /.test(word) && args[index - 1] !== '--input');
const claimBody = fields => `Autopilot claim on machine-a.\n\n\`\`\`json\n${JSON.stringify({ repository: repo, labelEventId: '701', lastSeen: '', ...fields })}\n\`\`\``;

// The no-AI tick with a fake gh that answers like GitHub. The dependency intake is a fake that reads
// through the GitHub runner that the tick gives it, like the native intake.
async function tickWorld(t, { github } = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-github-calls-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, 'repo'), home = join(dir, 'home');
  mkdirSync(cwd); mkdirSync(home);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], ...(github ? { github } : {}) } }));
  const w = { time: NOW, remaining: 4000, issues: [], since: [], gh: [], patches: [], intakes: 0, prompts: [], claim: null, warnings: [] };
  w.ports = {
    allocationCheck: async () => ({ state: 'ready', message: '' }),
    stateRoot: join(home, 'state'), now: () => w.time, readRunProgress: async () => [], warn: text => w.warnings.push(text),
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }), pathDiagnostic: () => [], timer: async () => true,
    run: async (command, args, options = {}) => {
      if (command === 'git') return { code: 0, stdout: `${cwd}\n`, stderr: '' };
      if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
      if (command !== 'gh') throw Error(`unexpected process ${command}`);
      w.gh.push(args);
      if (args[0] === 'repo') return { code: 0, stdout: JSON.stringify({ nameWithOwner: repo, url: `https://github.com/${repo}` }), stderr: '' };
      if (args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      const endpoint = endpointOf(args), sent = args.find(word => /^If-None-Match: /.test(word))?.slice(15), method = args[args.indexOf('--method') + 1];
      const answer = (status, body, extra) => ({ code: status === 304 ? 1 : 0, stdout: reply(status, body, { remaining: status === 304 ? w.remaining : --w.remaining, ...extra }), stderr: status === 304 ? 'gh: HTTP 304\n' : '' });
      const listed = (rows, tag) => sent === tag ? answer(304) : answer(200, rows, { etag: tag });
      // The open list has two pages: the first issue, then the rest.
      if (endpoint.startsWith(`repos/${repo}/issues?state=open`)) {
        const second = endpoint.endsWith('&page=2'), rows = second ? w.issues.slice(1) : w.issues.slice(0, 1);
        const tag = `"open-${second ? 2 : 1}-${JSON.stringify(rows).length}"`;
        return sent === tag ? answer(304) : answer(200, rows, { etag: tag, ...(second ? {} : { link: `<https://api.github.com/repos/${repo}/issues?state=open&sort=updated&direction=desc&per_page=100&page=2>; rel="next"` }) });
      }
      if (endpoint.startsWith(`repos/${repo}/issues?state=all`)) { w.sinceReads = [...(w.sinceReads ?? []), endpoint]; return listed(w.since, `"since-${endpoint}-${JSON.stringify(w.since).length}"`); }
      if (endpoint === `repos/${repo}/issues/comments/901`) {
        if (method === 'PATCH') { const { body } = JSON.parse(options.input); w.patches.push(body); w.claim = { ...w.claim, body, updated_at: at(w.time) }; }
        return answer(200, w.claim);
      }
      if (endpoint.includes('/reviews?')) return answer(200, []);
      if (endpoint === 'graphql') return answer(200, { data: {} }, { resource: 'graphql' });
      if (endpoint.includes('/timeline')) return answer(200, []);
      return answer(200, []);
    },
    reconcileDependencyIntake: async (input, ports) => {
      w.intakes++;
      // A bulk GraphQL read and a claim check, as the native intake makes them.
      await ports.execFile('gh', ['api', '--include', '--method', 'POST', 'graphql', '-H', 'Accept: application/vnd.github+json', '--input', '-'], { input: '{}' });
      await ports.execFile('gh', ['api', '--include', '--method', 'GET', `repos/${repo}/issues/7/timeline?per_page=100`, '-H', 'Accept: application/vnd.github+json'], { purpose: 'claims' });
      const state = w.state();
      return { eligible: [], queued: [], skipped: [], claims: w.claim ? [{ issue: key(7), active: true, owner: state.coordinatorId, coordinatorId: state.coordinatorId, machine: state.machine, commentId: '901', labelEventId: '701', lastSeen: w.claim.updated_at }] : [] };
    },
    herdr: async args => {
      if (args[0] === 'status') return { running: true };
      const live = { pane_id: 'p1', workspace_id: 'w1', cwd, foreground_cwd: cwd, tab_id: 't1', terminal_id: 'term1', agent: 'codex', agent_status: 'idle', agent_session: 'session' };
      if (args[0] === 'workspace') return { result: { type: 'workspace_info', workspace: { workspace_id: 'w1' }, root_pane: { pane_id: 'p1' } } };
      if (args[0] === 'pane' && args[1] === 'get') return { result: { type: 'pane_info', pane: live } };
      if (args[0] === 'agent' && args[1] === 'get') { if (!w.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' }); return { result: { type: 'agent_info', agent: live } }; }
      if (args[0] === 'pane' && args[1] === 'run') { w.agentStarted = true; return {}; }
      if (args[0] === 'pane' && args[1] === 'read') return '';
      if (args[0] === 'agent' && args[1] === 'prompt') w.prompts.push(args.at(-1));
      return {};
    },
  };
  const launcher = await import('../src/autopilot-launcher.mjs');
  w.stateFile = () => join(w.ports.stateRoot, readdirSync(w.ports.stateRoot).find(name => name.endsWith('.json')));
  w.state = () => { try { return JSON.parse(readFileSync(w.stateFile(), 'utf8')); } catch { return {}; } };
  w.invoke = command => launcher.runAutopilotLauncher({ command, cwd, env: { HOME: home, PATH: process.env.PATH }, packageRoot: resolve('.'), issues: [] }, w.ports);
  w.tick = () => launcher.tickAutopilot(w.stateFile(), w.ports);
  w.ledger = () => githubLedger({ root: w.ports.stateRoot, repository: repo });
  w.ownClaim = () => { const { coordinatorId, machine } = w.state(); w.claim = { id: 901, user: { login: 'owner' }, created_at: at(w.time), updated_at: at(w.time), body: claimBody({ coordinatorId, machine }) }; };
  w.issue = (n, extra = {}) => ({ number: n, state: 'open', title: `Issue ${n}`, body: 'trusted body', user: { login: 'owner' }, created_at: at(NOW - 48 * hour), updated_at: at(w.time), comments: 0, labels: [], html_url: key(n), ...extra });
  // Earlier calls in the last hour on this machine, as another tick wrote them.
  w.seed = (count, fields = {}) => { const ledger = githubLedger({ root: w.ports.stateRoot, repository: 'other/repo' }); for (let i = 0; i < count; i++) ledger.record({ at: w.time, api: 'rest', purpose: 'dependencies', status: 200, ...fields }); };
  return w;
}

test('measure: the tick records each GitHub call with its purpose and the remaining limit, and status shows them in one line', async t => {
  const w = await tickWorld(t);
  w.issues = [w.issue(7, { labels: [{ name: 'pdd:working' }] })];
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.ownClaim(); w.time += 30 * minute; await w.tick();
  const entries = w.ledger().read(), count = purpose => entries.filter(entry => entry.purpose === purpose).length;
  assert.equal(count('setup'), 1, 'gh auth status at start; the first gh repo view comes before the repository is known');
  assert.equal(count('dependencies'), 2, 'the bulk GraphQL read of each intake');
  assert.equal(count('claims'), 2, 'one claim check in each intake; the fresh heartbeat needs no read');
  assert.ok(count('issues') >= 2, 'the issue list of each tick');
  assert.equal(w.patches.length, 0, 'the claim is fresh');
  const graphql = entries.find(entry => entry.api === 'graphql' && entry.purpose === 'dependencies');
  assert.equal(graphql.resource, 'graphql');
  const newest = entries.filter(entry => entry.resource === 'core').at(-1);
  assert.deepEqual([newest.remaining, newest.limit, newest.resetAt], [w.remaining, 5000, reset() * 1000]);
  const status = (await w.invoke('status')).message.split('\n');
  const line = status.find(text => text.startsWith('GitHub calls in the last hour:'));
  assert.ok(line, status.join('\n'));
  const total = entries.filter(entry => entry.at > w.time - hour).length;
  assert.match(line, new RegExp(`^GitHub calls in the last hour: ${total} \\(dependencies 2, claims 2, issues \\d+, setup 1\\);`));
  assert.match(line, new RegExp(`REST limit ${w.remaining} of 5000 left until 13:00Z`));
  assert.match(line, /budget normal: Autopilot on this machine used \d+ of 1500 \(30%\)/);
});

test('measure: a call that the tick makes after the hour has passed does not count, and an old limit is not shown', async t => {
  const w = await tickWorld(t);
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.time += 2 * hour;
  const line = (await w.invoke('status')).message.split('\n').find(text => text.startsWith('GitHub calls'));
  assert.equal(line, undefined, 'no call in the last hour: no GitHub line');
  w.seed(1);
  const after = (await w.invoke('status')).message.split('\n').find(text => text.startsWith('GitHub calls'));
  assert.match(after, /REST limit not seen in the last hour/, 'the limit seen 2 hours ago is past its reset');
});

test('budget: over its share the tick defers the dependency re-sync for an hour and keeps the heartbeat', async t => {
  const w = await tickWorld(t, { github: { share: 1, floor: 100 } });
  w.issues = [w.issue(7, { labels: [{ name: 'pdd:working' }] })];
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.ownClaim(); w.time += 30 * minute; await w.tick();
  assert.equal(w.intakes, 2); assert.equal(w.patches.length, 0);
  w.seed(60); // 1% of 5000 is 50 calls; Autopilot on this machine used more.
  w.time += 10 * minute; await w.tick();
  assert.equal(w.intakes, 2, 'the dependency re-sync of unchanged issues waits');
  assert.equal(w.patches.length, 0, 'the live claim is fresh');
  assert.match(w.warnings.at(-1), /GitHub budget low: Autopilot on this machine used \d+ of 50 calls \(1%\)/);
  const status = (await w.invoke('status')).message;
  assert.match(status, /budget low: Autopilot on this machine used \d+ of 50 \(1%\)/);
  w.time += 20 * minute; w.seed(60); await w.tick();
  assert.equal(w.intakes, 2, '30 minutes after the last re-sync it still waits');
  assert.equal(w.patches.length, 0);
  w.time += 30 * minute; await w.tick();
  assert.equal(w.intakes, 3, 'one hour after the last re-sync it runs once, also with the budget still low');
  w.time += 10 * minute; await w.tick();
  assert.equal(w.intakes, 3);
  assert.equal(w.patches.length, 0, 'no heartbeat before two hours');
  w.time += 20 * minute; await w.tick();
  assert.equal(w.patches.length, 1, 'a due heartbeat keeps priority even with the read share low');
});

test('budget: below the floor the tick makes no GitHub call until the reset, then works again', async t => {
  const w = await tickWorld(t);
  w.issues = [w.issue(7, { labels: [{ name: 'pdd:working' }] })];
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.ownClaim();
  w.time += minute;
  w.seed(1, { resource: 'core', remaining: 120, limit: 5000, resetAt: NOW + 20 * minute });
  const calls = w.gh.length;
  const result = await w.tick();
  assert.match(result.message, /GitHub limit low: 120 REST calls left, below the floor of 1000; Autopilot waits until 2026-11-06T12:20:00.000Z/);
  assert.equal(w.gh.length, calls, 'no GitHub call at all, also no heartbeat');
  w.time += 10 * minute; await w.tick();
  assert.equal(w.gh.length, calls, 'still waiting before the reset');
  w.time += 10 * minute; await w.tick();
  assert.ok(w.gh.length > calls, 'after the reset the tick reads GitHub again');
  assert.equal(w.patches.length, 0, 'the fresh heartbeat needs no write');
});

test('since: between full reads of a list of two pages the tick reads only changed issues, a close leaves the list, and an unchanged list is a 304', async t => {
  const w = await tickWorld(t);
  w.issues = [w.issue(7), w.issue(8, { updated_at: at(NOW - hour) })];
  assert.equal((await w.invoke('start')).exitCode, 0);
  assert.deepEqual(w.state().cachedIssues.map(row => row.number), [7, 8]);
  w.time += 30 * minute;
  w.since = [{ ...w.issue(8), state: 'closed' }, w.issue(9)];
  await w.tick();
  assert.equal((w.sinceReads ?? []).length, 1, 'the tick reads the changed issues with since');
  assert.match(w.sinceReads[0], new RegExp(`^repos/${repo}/issues\\?state=all&sort=updated&direction=desc&since=${encodeURIComponent(at(NOW))}&per_page=100$`));
  assert.deepEqual(w.state().cachedIssues.map(row => row.number).sort(), [7, 9], 'the closed issue left; the new one came in');
  const before = w.ledger().read().length;
  w.time += 30 * minute; await w.tick();
  w.time += 30 * minute; await w.tick();
  const lists = w.ledger().read().slice(before).filter(entry => entry.purpose === 'issues');
  assert.equal(lists.at(-1).status, 304, 'the same since URL with its ETag: nothing changed');
  assert.equal(lists.at(-1).conditional, true);
  assert.ok(!w.gh.slice(-6).some(args => endpointOf(args)?.includes('state=open')), 'no full list read before 6 hours');
  w.time += 6 * hour; await w.tick();
  assert.ok(endpointOf(w.gh.filter(args => endpointOf(args)?.includes('/issues?')).at(-1)).includes('state=open'), 'after 6 hours the whole open list is read again');
  const line = (await w.invoke('status')).message.split('\n').find(text => text.startsWith('GitHub calls'));
  assert.match(line, /\d+ of \d+ conditional reads were 304 \(\d+%\)/);
});

// The native dependency reader with a fake gh: one open issue and its pages.
function readerWorld() {
  const w = { calls: [], changed: false, entries: [] };
  const issue = { id: 1007, number: 7, html_url: key(7), title: 'Issue 7', body: 'Fix it.', state: 'open', user: { login: 'owner' }, labels: [], assignees: [], created_at: at(NOW - hour), updated_at: at(NOW - hour) };
  const bodies = { [`repos/${repo}/issues?state=open&per_page=100`]: [issue], [`repos/${repo}/issues/7`]: issue,
    [`repos/${repo}/issues/7/comments?per_page=100`]: [], [`repos/${repo}/issues/7/dependencies/blocked_by?per_page=100`]: [],
    [`repos/${repo}/issues/7/dependencies/blocking?per_page=100`]: [], [`repos/${repo}/issues/7/timeline?per_page=100`]: [] };
  const fake = async (file, args) => {
    assert.equal(file, 'gh');
    const endpoint = endpointOf(args), sent = args.find(word => /^If-None-Match: /.test(word))?.slice(15);
    w.calls.push({ endpoint, sent });
    if (endpoint === 'graphql') return { code: 0, stdout: reply(200, { errors: [{ message: 'not in this fixture' }] }, { resource: 'graphql' }) };
    const body = bodies[endpoint];
    assert.ok(body, `unexpected endpoint ${endpoint}`);
    const tag = `"${createHash('sha256').update(JSON.stringify(body)).digest('hex').slice(0, 12)}"`;
    // Like gh: a 304 exits with 1 and prints the headers.
    if (sent === tag) return { code: 1, stdout: reply(304), stderr: 'gh: HTTP 304\n' };
    return { code: 0, stdout: reply(200, body, { etag: tag }) };
  };
  const ledger = { record: entry => w.entries.push(entry) };
  w.ports = cache => ({ execFile: countGithubCalls(fake, { ledger, purpose: 'dependencies', now: () => NOW }), githubCache: cache,
    authority: { read: async () => ({ authority: 'trusted' }) },
    context: { read: async () => ({ json: JSON.stringify({ inputs: [], conditions: [], execution: [] }) }) },
    owners: { read: async () => ({ json: JSON.stringify({ localOwner: '', claims: [], runs: [], runsKnown: true }) }) },
    clock: { now: async () => ({ iso: at(NOW) }) } });
  return w;
}

test('ETag: a second dependency read sends the saved ETags, reuses the bodies of 304 replies and makes no counted REST call', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-github-etags-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const w = readerWorld(), cache = () => githubEtagCache({ root: dir, repository: repo });
  const first = cache(), one = await readDependencySnapshot({ repository: repo }, w.ports(first)); first.save();
  assert.equal(one.snapshot.complete, true, one.snapshot.warnings.join('; '));
  const rest = () => w.calls.filter(call => call.endpoint !== 'graphql');
  assert.equal(rest().filter(call => call.sent).length, 0, 'the first read has no saved ETag');
  const before = w.calls.length, counted = w.entries.length;
  const second = cache(), two = await readDependencySnapshot({ repository: repo }, w.ports(second)); second.save();
  const again = w.calls.slice(before).filter(call => call.endpoint !== 'graphql');
  assert.ok(again.length >= 6);
  assert.ok(again.every(call => call.sent), 'every REST read of the second tick is conditional');
  assert.deepEqual(two.snapshot.issues, one.snapshot.issues, 'the 304 bodies give the same observation');
  assert.equal(two.snapshot.complete, true, two.snapshot.warnings.join('; '));
  const usage = githubUsage(w.entries.slice(counted), NOW);
  assert.equal(usage.counted, 0, 'no REST call of the second read counts against the limit');
  assert.equal(usage.notModified, again.length);
  assert.ok(Object.keys(JSON.parse(readFileSync(second.file, 'utf8'))).length >= 6, 'the cache keeps the working set');
});

test('one call: purposes, the reply headers of a real 304, the budget states and the status line', () => {
  const api = (method, endpoint, ...rest) => ['api', '--include', '--method', method, endpoint, '-H', 'Accept: application/vnd.github+json', ...rest];
  assert.equal(githubPurpose(api('GET', `repos/${repo}/issues/7/timeline?per_page=100`)), 'dependencies');
  assert.equal(githubPurpose(api('GET', `repos/${repo}/issues/7/dependencies/blocked_by?per_page=100`)), 'dependencies');
  assert.equal(githubPurpose(api('PATCH', `repos/${repo}/issues/comments/901`)), 'writes');
  assert.equal(githubPurpose(api('GET', `repos/${repo}/issues/comments/901`)), 'claims');
  assert.equal(githubPurpose(api('GET', `repos/${repo}/pulls/9/reviews?per_page=100`)), 'pulls');
  assert.equal(githubPurpose(['pr', 'view', 'https://github.com/owner/repo/pull/9', '--json', 'state']), 'pulls');
  assert.equal(githubPurpose(['pr', 'create', '--repo', repo]), 'writes');
  assert.equal(githubPurpose(api('GET', `repos/${repo}/issues?state=open&per_page=100`)), 'issues');
  assert.equal(githubPurpose(['api', `repos/${repo}/issues/7/comments`, '-f', 'body=hi']), 'writes', 'a field makes gh send a POST');
  assert.equal(githubPurpose(['auth', 'status']), 'setup');
  // The headers of a real `gh api -i` 304 reply (2026-11-06), shortened.
  const real = 'HTTP/2.0 304 Not Modified\r\nCache-Control: private, max-age=60, s-maxage=60\r\nEtag: "29f5400c"\r\nX-Ratelimit-Limit: 5000\r\nX-Ratelimit-Remaining: 4993\r\nX-Ratelimit-Reset: 1794036132\r\nX-Ratelimit-Resource: core\r\nX-Ratelimit-Used: 7\r\n\r\n';
  assert.deepEqual(githubReply(real), { status: 304, etag: '"29f5400c"', link: undefined, rate: { resource: 'core', remaining: 4993, limit: 5000, resetAt: 1794036132000 }, body: '' });
  const entries = [{ at: NOW - 10 * minute, api: 'rest', purpose: 'issues', status: 304, conditional: true, resource: 'core', remaining: 4993, limit: 5000, resetAt: NOW + 20 * minute },
    { at: NOW - 5 * minute, api: 'rest', purpose: 'claims', status: 200 }, { at: NOW - 2 * hour, api: 'rest', purpose: 'claims', status: 200 },
    { at: NOW - minute, api: 'graphql', purpose: 'dependencies', status: 200, resource: 'graphql', remaining: 4800, limit: 5000, resetAt: NOW + 30 * minute }];
  const usage = githubUsage(entries, NOW);
  assert.deepEqual({ calls: usage.calls, counted: usage.counted, conditional: usage.conditional, notModified: usage.notModified }, { calls: 3, counted: 1, conditional: 1, notModified: 1 });
  assert.deepEqual(githubBudget({ usage, share: 30, floor: 500 }), { state: 'normal', allowed: 1500, used: 1, share: 30, floor: 500 });
  assert.equal(githubBudget({ usage: { ...usage, counted: 1500 }, share: 30, floor: 500 }).state, 'low');
  assert.deepEqual(githubBudget({ usage, share: 30, floor: 4900 }), { state: 'reserve', allowed: 1500, used: 1, share: 30, floor: 4900, resource: 'graphql', remaining: 4800, resetAt: NOW + 30 * minute },
    'the GraphQL limit is below the floor');
  assert.equal(githubBudget({ usage, share: 30, floor: 4995 }).state, 'reserve');
  assert.equal(githubBudget({ usage, share: 30, floor: 4995 }).resource, 'core', 'the REST limit comes first');
  assert.equal(githubStatusLine({ usage, budget: githubBudget({ usage }) }),
    'GitHub calls in the last hour: 3 (dependencies 1, claims 1, issues 1); 1 of 1 conditional reads were 304 (100%); REST limit 4993 of 5000 left until 12:20Z; budget normal: Autopilot on this machine used 1 of 1500 (30%).');
});

test('native counter: a pdd command records each gh call in the ledger of its repository, keeps the result and the error, and runs other programs unchanged', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-github-native-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const seen = [];
  const exec = async (file, args, options) => {
    seen.push([file, options]);
    if (args.includes('fail')) throw Object.assign(Error('gh failed'), { code: 1, stdout: '', stderr: 'gh: Not Found (HTTP 404)\n' });
    return { stdout: file === 'gh' ? reply(200, { ok: true }) : 'x', stderr: '' };
  };
  const counted = nativeGithubCounter(exec, { stateRoot: dir, purpose: 'dependencies', now: () => NOW });
  await counted('gh', ['api', 'repos/owner/repo/issues/6']);
  assert.equal(existsSync(join(dir, 'github')), false, 'without an Autopilot ledger for the repository nothing is written');
  mkdirSync(join(dir, 'github')); writeFileSync(githubLedger({ root: dir, repository: 'owner/repo' }).file, '');
  seen.length = 0;
  assert.equal((await counted('git', ['status'], { cwd: dir, purpose: 'claims' })).stdout, 'x');
  assert.deepEqual(seen[0], ['git', { cwd: dir }], 'the purpose option never reaches the program');
  assert.match((await counted('gh', ['api', '--include', 'repos/Owner/Repo/issues/7'], { cwd: dir })).stdout, /^HTTP\/2.0 200/);
  await counted('gh', ['api', '--include', '--method', 'POST', 'graphql', '--input', '-'], { input: JSON.stringify({query:'query { viewer { login } }'}), repository: 'Owner/Repo' });
  await assert.rejects(counted('gh', ['api', 'repos/owner/repo/issues/8', 'fail']), /gh failed/);
  await counted('gh', ['api', 'user']);
  assert.deepEqual(seen.slice(1).map(([, {env, ...options}]) => options), [{ cwd: dir }, { input: JSON.stringify({query:'query { viewer { login } }'}) }, {}, {}]);
  assert.ok(seen.slice(1, 4).every(([, options]) => options.env?.PDD_GITHUB_COUNTED === '1'));
  const entries = githubLedger({ root: dir, repository: 'owner/repo' }).read();
  assert.deepEqual(entries.map(entry => [entry.api, entry.purpose, entry.status, entry.repo]),
    [['rest', 'dependencies', 200, 'owner/repo'], ['graphql', 'dependencies', 200, 'owner/repo'], ['rest', 'dependencies', 404, 'owner/repo']]);
  assert.deepEqual(readdirSync(join(dir, 'github')), [`${createHash('sha256').update('owner/repo').digest('hex').slice(0, 20)}.jsonl`],
    'gh api user names no repository and is not recorded');
});

// The native reader with a fake GitHub that pages lists by 100. As on GitHub (checked live), the ETag is a hash of the
// body only, so a page keeps its ETag when a next page appears, and a 304 reply has no Link header.
function pagedWorld() {
  const w = { calls: [], posts: 0, comments: [], timeline: [] };
  w.issue = { id: 1007, number: 7, html_url: key(7), title: 'Issue 7', body: 'Fix it.', state: 'open', user: { login: 'owner' }, labels: [], assignees: [], created_at: at(NOW - 3 * hour), updated_at: at(NOW - 3 * hour) };
  w.comment = (n, body = `comment ${n}`) => ({ id: 5000 + n, body, user: { login: 'owner' }, created_at: at(NOW - 2 * hour + n * 1000), updated_at: at(NOW - 2 * hour + n * 1000), html_url: `${key(7)}#issuecomment-${5000 + n}` });
  const lists = () => ({ 'issues/7/comments': w.comments, 'issues/7/timeline': w.timeline, 'issues/7/dependencies/blocked_by': [], 'issues/7/dependencies/blocking': [] });
  const fake = async (file, args, options = {}) => {
    if (file !== 'gh') throw Error(`no ${file} in this fixture`);
    const endpoint = endpointOf(args), method = args[args.indexOf('--method') + 1], sent = args.find(word => /^If-None-Match: /.test(word))?.slice(15);
    w.calls.push({ endpoint, method, sent });
    if (endpoint === 'graphql') return { code: 0, stdout: reply(200, { errors: [{ message: 'not in this fixture' }] }, { resource: 'graphql' }) };
    if (method === 'POST' && endpoint === `repos/${repo}/issues/7/comments`) {
      w.posts++; const row = w.comment(w.comments.length + 1, JSON.parse(options.input).body); w.comments.push(row);
      return { code: 0, stdout: reply(201, row) };
    }
    const [path, query = ''] = endpoint.split('?'), route = path.replace(`repos/${repo}/`, ''), page = Number(new URLSearchParams(query).get('page') ?? 1);
    let body, link;
    if (route === 'issues') body = [w.issue];
    else if (route === 'issues/7') body = w.issue;
    else if (/^issues\/comments\/[0-9]+$/.test(route)) body = w.comments.find(row => route === `issues/comments/${row.id}`);
    else if (lists()[route]) {
      const all = lists()[route]; body = all.slice((page - 1) * 100, page * 100);
      if (all.length > page * 100) link = `<https://api.github.com/${path}?per_page=100&page=${page + 1}>; rel="next"`;
    }
    assert.ok(body !== undefined, `unexpected endpoint ${endpoint}`);
    const tag = `"${createHash('sha256').update(JSON.stringify(body)).digest('hex').slice(0, 12)}"`;
    if (sent === tag) return { code: 1, stdout: reply(304), stderr: 'gh: HTTP 304\n' };
    return { code: 0, stdout: reply(200, body, { etag: tag, link }) };
  };
  w.ports = (cache, extra = {}) => ({ execFile: countGithubCalls(fake, { ledger: null }), ...(cache ? { githubCache: cache } : {}),
    authority: { read: async () => ({ authority: 'trusted' }) },
    context: { read: async () => ({ json: JSON.stringify({ inputs: [], conditions: [], execution: [] }) }) },
    owners: { read: async () => ({ json: JSON.stringify({ localOwner: '', claims: [], runs: [], runsKnown: true }) }) },
    clock: { now: async () => ({ iso: at(NOW) }) }, ...extra });
  return w;
}
const etagDir = t => { const dir = mkdtempSync(join(tmpdir(), 'pdd-github-full-page-')); t.after(() => rmSync(dir, { recursive: true, force: true })); return dir; };
// One read with the saved ETag cache of the last read, as one tick's intake does it.
const cachedRead = async (dir, read) => { const cache = githubEtagCache({ root: dir, repository: repo }); try { return await read(cache); } finally { cache.save(); } };

test('ETag: a full last page is read again, so comment 101 after exactly 100 comments is seen and the read stays complete', async t => {
  const dir = etagDir(t), w = pagedWorld();
  w.comments = Array.from({ length: 100 }, (_, i) => w.comment(i + 1));
  const snapshot = cache => readDependencySnapshot({ repository: repo }, w.ports(cache)).then(result => result.snapshot);
  const one = await cachedRead(dir, snapshot);
  assert.equal(one.complete, true, one.warnings.join('; '));
  w.comments.push(w.comment(101, 'A new trusted comment after a full page.'));
  const before = w.calls.length;
  const two = await cachedRead(dir, snapshot), second = w.calls.slice(before);
  const fresh = await snapshot(null);
  assert.ok(JSON.stringify(fresh).includes(`${key(7)}#issuecomment-5101`), 'the uncached read sees comment 101');
  assert.deepEqual(two, fresh, 'the cached read sees comment 101 too and gives the same observation');
  assert.equal(two.complete, true, two.warnings.join('; '));
  const page = second.find(call => call.endpoint === `repos/${repo}/issues/7/comments?per_page=100`);
  assert.equal(page.sent, undefined, 'the full first page with no next page is read without its ETag');
  assert.ok(second.some(call => call.endpoint === `repos/${repo}/issues/7/comments?per_page=100&page=2`), 'and the new second page is read');
  assert.ok(second.filter(call => call.endpoint.includes('/dependencies/') || call.endpoint.includes('/timeline')).every(call => call.sent), 'a page that is not full stays conditional');
});

test('ETag: a claim check through the cache sees a new claim era after a full last page of history and comments', async t => {
  const dir = etagDir(t), w = pagedWorld();
  const event = (id, extra = {}) => ({ id, event: 'subscribed', actor: { login: 'owner' }, created_at: at(NOW - 2 * hour + id), ...extra });
  const claim = (n, coordinatorId, labelEventId) => w.comment(n, `Autopilot claim on machine-a.\n\n\`\`\`json\n${JSON.stringify({ repository: repo, coordinatorId, machine: 'machine-a', labelEventId, lastSeen: '' })}\n\`\`\``);
  w.issue.labels = [{ name: 'pdd:working' }];
  w.timeline = [...Array.from({ length: 99 }, (_, i) => event(i + 1)), event(701, { event: 'labeled', label: { name: 'pdd:working' } })];
  w.comments = [...Array.from({ length: 99 }, (_, i) => w.comment(i + 1)), claim(100, 'coordinator-a', '701')];
  const owners = cache => createDependencyReadPorts({}, w.ports(cache, { owners: undefined })).owners.read({ repository: repo, issues: [key(7)] }).then(raw => JSON.parse(raw.json).claims);
  const [first] = await cachedRead(dir, owners);
  assert.deepEqual([first.coordinatorId, first.labelEventId, first.active], ['coordinator-a', '701', true]);
  // The label is removed and added again by another coordinator, which posts its own claim: item 101 and 102.
  w.timeline.push(event(702, { event: 'unlabeled', label: { name: 'pdd:working' } }), event(703, { event: 'labeled', label: { name: 'pdd:working' } }));
  w.comments.push(claim(101, 'coordinator-b', '703'));
  w.issue = { ...w.issue, updated_at: at(NOW - hour) };
  const [second] = await cachedRead(dir, owners);
  const [fresh] = await owners(null);
  assert.deepEqual([fresh.coordinatorId, fresh.labelEventId], ['coordinator-b', '703']);
  assert.deepEqual(second, fresh, 'the cached claim check sees the new claim, not the old one');
});

test('ETag: a repeated record append through the cache finds its own comment after a full last page and posts no copy', async t => {
  const dir = etagDir(t), w = pagedWorld();
  w.comments = Array.from({ length: 100 }, (_, i) => w.comment(i + 1));
  const row = { key: key(7), revision: createHash('sha256').update(JSON.stringify({ title: 'Issue 7', body: 'Fix it.' })).digest('hex') };
  const review = { analysis: 'Checked for the full-page case.', base: [], continuation: '', issue: key(7), inputs: [row], candidates: [row], outcome: 'complete', dependencies: [], questions: [], effects: 'none' };
  const save = cache => saveDependencyReview({ repository: repo, issue: key(7), review }, w.ports(cache));
  const one = await cachedRead(dir, save);
  assert.deepEqual([one.state, one.id, w.posts], ['saved', '5101', 1]);
  const two = await cachedRead(dir, save);
  assert.deepEqual([two.state, two.id], ['saved', '5101'], 'the retry finds comment 101');
  assert.equal(w.posts, 1, 'no second copy of the record');
});

test('budget: below the floor the tick skips fresh heartbeats and sends only a due heartbeat', async t => {
  const w = await tickWorld(t);
  w.issues = [w.issue(7, { labels: [{ name: 'pdd:working' }] })];
  assert.equal((await w.invoke('start')).exitCode, 0);
  w.ownClaim(); w.time += 30 * minute; await w.tick();
  assert.equal(w.patches.length, 0, 'the intake saw a fresh own claim');
  // Other use on this login leaves 120 calls until the reset at 13:00.
  w.remaining = 120; w.seed(1, { resource: 'core', remaining: 120, limit: 5000, resetAt: reset() * 1000 });
  for (const step of [15, 10]) {
    w.time += step * minute;
    const calls = w.gh.length, intakes = w.intakes, result = await w.tick();
    assert.match(result.message, /GitHub limit low: \d+ REST calls left, below the floor of 1000; Autopilot waits until 2026-11-06T13:00:00.000Z/);
    assert.equal(w.intakes, intakes, 'no dependency re-sync');
    assert.deepEqual(w.gh.slice(calls).map(args => [args[args.indexOf('--method') + 1], endpointOf(args)]),
      [], 'the heartbeat is fresh, so there are no requests');
  }
  assert.equal(w.patches.length, 0, 'no heartbeat for a fresh claim in reserve');
  // With fewer REST calls left than the heartbeats need, the tick sends none.
  w.seed(1, { resource: 'core', remaining: 1, limit: 5000, resetAt: reset() * 1000 });
  w.time += 3 * minute;
  const calls = w.gh.length; await w.tick();
  assert.equal(w.gh.length, calls, 'no GitHub call with 1 REST call left');
  w.time += 10 * minute; await w.tick();
  assert.equal(w.intakes, 3, 'after the reset the tick works as usual');
  w.time = NOW + 2 * hour;
  w.seed(1, {resource:'core',remaining:120,limit:5000,resetAt:w.time + hour});
  await w.tick();
  assert.equal(w.patches.length, 1, 'the due heartbeat runs in reserve');
});

test('status line: in reserve the budget part names the calls left and the floor', () => {
  const usage = githubUsage([{ at: NOW - minute, api: 'rest', purpose: 'claims', status: 200, resource: 'core', remaining: 120, limit: 5000, resetAt: NOW + 20 * minute }], NOW);
  assert.equal(githubStatusLine({ usage, budget: githubBudget({ usage }) }),
    'GitHub calls in the last hour: 1 (claims 1); no conditional reads; REST limit 120 of 5000 left until 12:20Z; budget reserve (120 REST calls left, below the floor of 1000): Autopilot on this machine used 1 of 1500 (30%).');
});
