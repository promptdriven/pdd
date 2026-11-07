// #3039: a Runtime outage parks only the runs that need Runtime, frees their slots, alerts once and recovers by itself.
// Every Runtime, health, HTTP, Discord and clock port is injected; no test calls the real Runtime or a chat service.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { parkAutomaticRun, runStatus, changeRun, stepDone, startRun, approveRun, yieldAutomaticCapacity } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { checkCause } from '../src/workflow-results.mjs';
import { checkRuntimeHealth } from '../src/runtime-client.mjs';
import { runAutopilotAlerts } from '../src/autopilot-alerts.mjs';
import { createDependencyReadPorts, readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { fixture as runFixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const BATCH = '20261027-170500-abcd';
const origin = { repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: { commentId: '11', labelEventId: '12' } };

// An automatic run at its check step, with a current claim read through a fake gh.
async function automaticRun(t) {
  const f = await runFixture(t, { name: 'bug', agent: 'codex' });
  f.ports.env = { HOME: f.ports.env.HOME };
  assert.equal((await startRun({ name: 'bug', issue: '17', agent: 'codex', cwd: f.source, packageRoot }, f.ports)).exitCode, 0);
  for (const step of ['reproduce', 'prompt-story']) { f.tick(); assert.equal((await stepDone({ step, summary: step, cwd: f.record().root }, f.agentPorts())).exitCode, 0); }
  const run = f.record(); run.automaticOrigin = structuredClone(origin); writeRun(run);
  const root = realpathSync(f.source), stateRoot = join(f.state, 'autopilot'); mkdirSync(stateRoot, { recursive: true });
  writeFileSync(join(stateRoot, `${createHash('sha256').update(root).digest('hex').slice(0, 20)}.json`), JSON.stringify({ repo: run.repo, cwd: root, coordinatorId: origin.coordinatorId }));
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const fixturePath = join(f.base, 'reader.json'), logPath = join(f.base, 'gh.log');
  writeFileSync(fixturePath, JSON.stringify({ labels: ['pdd:working'], events: [{ id: 12, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' } }], comments: [{ id: 11, user: { login: 'example' }, body: JSON.stringify({ repository: origin.repository, coordinatorId: origin.coordinatorId, machine: origin.machine, labelEventId: '12' }) }] }));
  const { execFile: callback } = await import('node:child_process'); const { promisify } = await import('node:util'); const exec = promisify(callback);
  const original = f.ports.execFile;
  const execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === '--include' ? exec(process.execPath, [join(packageRoot, 'test/helpers/continuation-fake-gh.mjs'), ...args], { ...opts, env: { ...process.env, READER_FIXTURE_FILE: fixturePath, READER_GH_LOG: logPath } }) : original(file, args, opts);
  const ports = extra => ({ ...f.agentPorts(), execFile, autopilotStateRoot: stateRoot, ...extra });
  // The story gate is approved: the run works on its check step.
  const approved = await approveRun({ ref: '17', cwd: f.record().root, said: 'I approve' }, ports());
  assert.equal(approved.exitCode, 0, approved.message); assert.equal(f.record().state, 'running');
  return { f, ports, root: f.record().root };
}
// pdd's own saved check for this worktree, as pdd test writes it.
function savedCheck(f, rows) {
  const folder = join(f.ports.env.HOME, '.pdd', 'runtime', 'batches', BATCH); mkdirSync(folder, { recursive: true });
  const run = f.record();
  writeFileSync(join(folder, 'batch.json'), JSON.stringify({ version: 1, batch: BATCH, root: run.root, intent: 'check', created_at: new Date(f.clock).toISOString(), rows: rows.map(row => ({ test: 'tests/a.json', story: 'a', request_ids: [], ...row })) }));
  writeFileSync(join(folder, 'summary.json'), JSON.stringify({ batch: BATCH, summary_line: 'Prompt tests: no verdict ·', rows: rows.map(row => ({ test: 'tests/a.json', story: 'a', ...row })) }));
}

test('an AI-service no-verdict parks only this run for Runtime: no question, visible status, slot free, wake by delivery', async t => {
  const { f, ports, root } = await automaticRun(t);
  savedCheck(f, [{ state: 'refused', refusals: [{ code: 'graph-provider-failure' }] }]);
  const before = f.record();
  const parked = await parkAutomaticRun({ reason: 'graph-provider-failure: the AI service failed', runtime: true, cwd: root }, ports());
  assert.equal(parked.exitCode, 0, parked.message);
  assert.match(parked.message, /waits for Runtime/); assert.match(parked.message, /Ask no person/); assert.match(parked.message, new RegExp(`pdd test --read ${BATCH}`));
  const run = f.record();
  assert.equal(run.state, 'paused'); assert.deepEqual(run.runtimeWait, { at: f.clock, reason: 'graph-provider-failure: the AI service failed', batch: BATCH, cause: 'service' });
  assert.equal(run.question ?? null, null, 'no question to a person');
  for (const key of ['area', 'done', 'gate', 'branch', 'root', 'automaticOrigin', 'chats']) assert.deepEqual(run[key], before[key], `${key} is kept`);
  const status = await runStatus({ ref: '17', cwd: f.source }, ports());
  assert.match(status.message, /State: waiting for Runtime: graph-provider-failure/); assert.doesNotMatch(status.message, /waiting for you/);
  const listed = JSON.parse((await runStatus({ cwd: f.source, json: true }, ports())).message).runs[0];
  assert.equal(listed.group, 'working', 'a Runtime wait is not a person question'); assert.match(listed.words, /^waiting for Runtime/);
  // The worker ends its turn: the coordinator may yield the slot under the existing rule.
  const chat = run.chats.find(item => item.area === run.areas[run.area].name);
  f.herdr.paneOf(chat).agent.agent_status = 'done';
  const requests = [];
  const yielded = await yieldAutomaticCapacity({ ref: '17', cwd: f.source }, ports({ requestAutopilotCompletion: async args => { requests.push(args); return { state: 'reconciled' }; } }));
  assert.equal(yielded.exitCode, 0, yielded.message); assert.equal(requests.length, 1);
  for (const key of ['state', 'runtimeWait', 'area', 'done', 'gate', 'automaticOrigin', 'root', 'branch']) assert.deepEqual(f.record()[key], run[key], `yield keeps ${key}`);
  // The coordinator wakes it through the existing delivery route.
  f.herdr.paneOf(chat).agent.agent_status = 'idle';
  const woken = await changeRun({ ref: '17', cwd: f.source, text: `Runtime is back. First run pdd test --read ${BATCH} once.`, packageRoot }, ports());
  assert.equal(woken.exitCode, 0, woken.message);
  assert.equal(f.record().state, 'running'); assert.equal(f.record().runtimeWait, undefined);
});

for (const [name, rows, words] of [
  ['a failed expectation', [{ state: 'failed' }], /this issue's own work/],
  ['a file-rule refusal', [{ state: 'refused', refusals: [{ code: 'invalid-input' }] }], /this issue's own work/],
  ['an AI-service refusal next to a failed Story', [{ state: 'refused', refusals: [{ code: 'graph-provider-failure' }] }, { state: 'failed' }], /this issue's own work/],
  ['a sign-in problem', [{ state: 'not_run', note: { code: 'blocked', message: 'Run gh auth login' } }], /access/],
  ['a passed check', [{ state: 'passed' }], /passed/],
]) test(`${name} is not a Runtime outage: park --runtime refuses and changes nothing`, async t => {
  const { f, ports, root } = await automaticRun(t);
  savedCheck(f, rows);
  const before = f.record();
  const result = await parkAutomaticRun({ reason: 'no verdict', runtime: true, cwd: root }, ports());
  assert.equal(result.exitCode, 1); assert.match(result.message, words); assert.match(result.message, /Nothing was parked/);
  assert.deepEqual(f.record(), before);
});

test('an unknown outcome waits with its cause; a plain park still records the stuck path', async t => {
  const { f, ports, root } = await automaticRun(t);
  savedCheck(f, [{ state: 'unknown', why: 'The answer to the request was lost.' }]);
  assert.equal((await parkAutomaticRun({ reason: 'HTTP 503 after 3 retries', runtime: true, cwd: root }, ports())).exitCode, 0);
  assert.equal(f.record().runtimeWait.cause, 'unknown');
  // The graph reads the same wait from local custody.
  const owners = JSON.parse((await createDependencyReadPorts({ cwd: f.source }, { ...ports(), herdr: f.ports.herdr }).owners.read({ repository: 'example/project', issues: [] })).json);
  assert.equal(owners.runs.find(run => run.issue.endsWith('/issues/17'))?.waiting, 'runtime');
  const stuck = await parkAutomaticRun({ reason: 'stuck after one retry', cwd: root }, ports());
  assert.equal(stuck.exitCode, 0, stuck.message);
  assert.equal(f.record().state, 'stuck'); assert.equal(f.record().runtimeWait, undefined);
});

test('pdd graph shows the Runtime wait as a hold of its own issue only', async () => {
  const key = number => `https://github.com/example/project/issues/${number}`;
  const issue = number => ({ id: number, number, html_url: key(number), title: `Issue ${number}`, body: 'body', state: 'open', user: { login: 'owner' }, labels: [], assignees: [], created_at: '2026-11-05T19:00:00.000Z', updated_at: '2026-11-05T19:00:00.000Z', comments: 0 });
  const issues = [issue(17), issue(18)], reply = value => ({ json: JSON.stringify(value) });
  const ports = {
    github: { issue: async ({ issue: number }) => reply(issues.find(item => item.number === number) ?? { error: 'not_found' }), page: async ({ kind }) => reply({ items: kind === 'issues' ? issues : [], next: '' }) },
    authority: { read: async () => ({ authority: 'trusted' }) },
    context: { read: async () => reply({ inputs: [], conditions: [], execution: [], nativeExecution: true }) },
    owners: { read: async () => reply({ localOwner: 'coordinator-a', claims: [], runsKnown: true, runs: [{ issue: key(17), runId: 'run-17', state: 'paused', occupied: false, waiting: 'runtime' }, { issue: key(18), runId: 'run-18', state: 'running' }] }) },
    clock: { now: async () => ({ iso: '2026-11-05T20:00:00.000Z' }) },
  };
  const { snapshot } = await readDependencySnapshot({ cwd: '', repository: 'example/project' }, ports);
  const nodes = projectIssueGraph({ snapshot }).nodes;
  assert.ok(nodes.find(node => node.key === key(17)).reasons.includes('Waiting for Runtime'));
  assert.ok(!nodes.find(node => node.key === key(18)).reasons.includes('Waiting for Runtime'));
});

test('checkCause tells this issue from the service from its saved rows', () => {
  const cases = [
    [[], 'none'], [[{ state: 'passed' }], 'passed'],
    [[{ state: 'failed' }], 'issue'], [[{ state: 'refused', refusals: [{ code: 'story-criterion-mismatch' }] }], 'issue'],
    [[{ state: 'refused', refusals: [] }], 'issue'],
    [[{ state: 'refused', refusals: [{ code: 'graph-provider-failure' }] }], 'service'],
    [[{ state: 'refused', refusals: [{ code: 'graph-uncertain-child-dispatch' }] }, { state: 'passed' }], 'service'],
    [[{ state: 'not_run', busy: true, note: { code: 'check-busy' } }], 'service'],
    [[{ state: 'not_run', reason: { code: 'auth-required' } }], 'access'],
    [[{ state: 'unknown', reason: { code: 'graph-provider-failure' } }], 'service'],
    [[{ state: 'unknown', why: 'The interpreter answered HTTP 502.' }], 'unknown'],
    [[{ state: 'running' }], 'unknown'],
  ];
  for (const [rows, cause] of cases) assert.equal(checkCause(rows), cause, JSON.stringify(rows));
});

test('the health check is one free GET of /v1/capacity: no source, no check, no AI call', async () => {
  const calls = [];
  const probe = async (reply, gh = { status: 0, stdout: 'gho_token\n' }) => checkRuntimeHealth({ env: { HOME: '/nowhere', PDD_RUNTIME_URL: 'https://runtime.example.test' } }, {
    gh: args => { calls.push(['gh', ...args]); return gh; }, now: () => Date.parse('2026-11-06T12:00:00Z'),
    fetch: async (url, init) => { calls.push([init.method, String(url), init.body ?? null, init.headers.Authorization]); if (reply instanceof Error) throw reply; return new Response(reply.body ?? '', { status: reply.status }); } });
  assert.deepEqual(await probe({ status: 200, body: '{"maintenance":null,"slots":{"check":{"running":0,"limit":4}}}' }), { state: 'healthy', detail: 'HTTP 200' });
  assert.deepEqual(calls, [['gh', 'auth', 'token'], ['GET', 'https://runtime.example.test/v1/capacity', null, 'Bearer gho_token']]);
  assert.equal((await probe({ status: 503, body: 'The runtime opens soon.' })).state, 'unavailable');
  assert.equal((await probe({ status: 502 })).state, 'unavailable');
  assert.equal((await probe({ status: 429 })).state, 'unavailable');
  assert.equal((await probe(Object.assign(Error('fetch failed'), { cause: { code: 'ECONNREFUSED' } }))).state, 'unavailable');
  assert.deepEqual(await probe({ status: 200, body: '{"maintenance":{"until":"2026-11-06T13:00:00Z"}}' }), { state: 'unavailable', detail: 'maintenance' });
  assert.equal((await probe({ status: 401 })).state, 'unknown');
  calls.length = 0;
  assert.equal((await probe({ status: 200 }, { status: 1, stdout: '' })).state, 'unknown');
  assert.deepEqual(calls, [['gh', 'auth', 'token']], 'no sign-in sends nothing');
});

// ---- Launcher ticks, with fake Herdr, GitHub, health and alert ports (adapted from autopilot-launcher.test.mjs).
async function launcher(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-runtime-outage-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, 'repo'), home = join(dir, 'home');
  mkdirSync(cwd); mkdirSync(home);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const f = { dir, cwd, home, time: Date.parse('2026-11-06T12:00:00Z'), prompts: [], issues: [], waits: [], health: { state: 'healthy', detail: 'HTTP 200' }, healthCalls: 0, alerts: [], sent: [] };
  f.ports = {
    stateRoot: join(home, 'state'), now: () => f.time, readRunProgress: async () => [], warn: () => {},
    readRuntimeWaits: async () => structuredClone(f.waits),
    runtimeHealth: async () => { f.healthCalls++; return f.health; },
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }), pathDiagnostic: () => [],
    run: async (command, args) => {
      if (command === 'git') return { code: 0, stdout: cwd + '\n', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo","url":"https://github.com/owner/repo"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api') return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' };
      if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
      throw Error(`unexpected process ${command} ${args}`);
    },
    timer: async () => true,
    queryIssues: async () => ({ status: 200, etag: '"one"', issues: structuredClone(f.issues) }),
    comments: async () => [],
    reconcileDependencyIntake: async () => ({ eligible: f.issues.map(issue => issue.html_url), queued: [], skipped: [] }),
    herdr: async args => {
      if (args[0] === 'status') return { running: true };
      const live = { pane_id: 'p1', workspace_id: 'w1', cwd, foreground_cwd: cwd, tab_id: 't1', terminal_id: 'term1', agent: 'codex', agent_status: 'idle', agent_session: 'session' };
      if (args[0] === 'workspace') return { result: { type: 'workspace_info', workspace: { workspace_id: 'w1' }, root_pane: { pane_id: 'p1' } } };
      if (args[0] === 'pane' && args[1] === 'get') return { result: { type: 'pane_info', pane: live } };
      if (args[0] === 'agent' && args[1] === 'get') { if (!f.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' }); return { result: { type: 'agent_info', agent: live } }; }
      if (args[0] === 'pane' && args[1] === 'run') { f.agentStarted = true; return {}; }
      if (args[0] === 'pane' && args[1] === 'read') return '';
      if (args[0] === 'agent' && args[1] === 'prompt') { const match = /Artifact path: (.+)/.exec(args.at(-1)); f.prompts.push(match ? readFileSync(JSON.parse(match[1]), 'utf8') : args.at(-1)); }
      return {};
    },
    // The real alerts module with a saved Discord webhook and a fake HTTP port.
    alertPorts: { http: async ({ body }) => { f.sent.push(body.content); return { status: 200, text: JSON.stringify({ id: String(f.sent.length), content: body.content }) }; } },
  };
  const env = { HOME: home, PATH: process.env.PATH, XDG_CONFIG_HOME: join(home, '.config') };
  mkdirSync(join(home, '.config', 'pdd'), { recursive: true });
  writeFileSync(join(home, '.config', 'pdd', 'autopilot-alerts.json'), JSON.stringify({ v: 1, service: 'discord', url: 'https://discord.com/api/webhooks/1/abc' }));
  const module = await import('../src/autopilot-launcher.mjs');
  f.start = () => module.runAutopilotLauncher({ command: 'start', cwd, env, packageRoot: resolve('.'), issues: [] }, f.ports);
  f.stateFile = () => join(f.ports.stateRoot, readdirSync(f.ports.stateRoot).find(x => x.endsWith('.json')));
  f.tick = () => module.tickAutopilot(f.stateFile(), f.ports);
  f.packet = () => JSON.parse(f.prompts.at(-1).trim().split('\n').at(-1));
  f.rules = () => f.prompts.length ? f.packet().timeRules ?? [] : [];
  return f;
}
const minute = 60 * 1000;
const issue = number => ({ number, state: 'open', title: `Issue ${number}`, body: 'trusted body', user: { login: 'owner' }, author_association: 'OWNER', created_at: '2026-11-06T11:00:00Z', updated_at: '2026-11-06T11:00:00Z', comments: 0, labels: [], html_url: `https://github.com/owner/repo/issues/${number}` });
const wait = (number, at, extra = {}) => ({ number, at, batch: BATCH, cause: 'service', mark: '1:2', ...extra });

test('no run waits for Runtime: the tick makes no health check', async t => {
  const f = await launcher(t);
  assert.equal((await f.start()).exitCode, 0);
  for (let i = 0; i < 3; i++) { f.time += 30 * minute; await f.tick(); }
  assert.equal(f.healthCalls, 0); assert.equal(f.sent.length, 0);
});

test('one issue alone with healthy Runtime: one retry of that run only, no alert; the same step again is stuck', async t => {
  const f = await launcher(t);
  await f.start(); f.prompts.length = 0;
  const at = f.time; f.waits = [wait(12, at)]; f.time += minute;
  await f.tick();
  assert.equal(f.healthCalls, 1);
  assert.deepEqual(f.rules().map(rule => [rule.kind, rule.number]), [['runtime-ready', 12]], 'only the waiting run is named');
  assert.match(f.rules()[0].reason, /one retry/); assert.equal(f.packet().runtime, undefined, 'no outage');
  assert.equal(f.sent.length, 0, 'an issue-specific failure alerts nobody');
  // The wake is delivered once; an unchanged tick sends nothing more.
  const count = f.prompts.length; f.time += 30 * minute; await f.tick(); assert.equal(f.prompts.length, count);
  // The worker resends; the same step waits for Runtime again while Runtime is healthy.
  f.waits = []; f.time += minute; await f.tick();
  f.waits = [wait(12, f.time)]; f.time += minute; await f.tick();
  assert.deepEqual(f.rules().map(rule => [rule.kind, rule.number]), [['runtime-stuck', 12]]);
  assert.match(f.rules()[0].reason, /pdd:stuck rule/);
  assert.equal(f.sent.length, 0);
});

test('a Runtime outage: one runtime alert per repository and machine, other work keeps moving, one recovery, wakes oldest first', async t => {
  const f = await launcher(t);
  await f.start(); f.prompts.length = 0;
  const first = f.time;
  f.waits = [wait(15, first + 5 * minute), wait(12, first, { cause: 'unknown' })];
  f.health = { state: 'unavailable', detail: 'HTTP 503' }; f.time += 6 * minute;
  f.issues = [issue(30)];
  await f.tick();
  assert.equal(f.sent.length, 1, 'one alert for both waiting issues');
  assert.match(f.sent[0], /PDD Autopilot alert: runtime/); assert.match(f.sent[0], /issues\/12/); assert.match(f.sent[0], /health check failed \(HTTP 503\)/);
  const packet = f.packet();
  assert.equal(packet.runtime.state, 'unavailable'); assert.match(packet.runtime.note, /Keep other work moving/);
  assert.deepEqual(packet.issues.map(item => item.number), [30], 'a new issue may still start');
  assert.deepEqual(packet.timeRules ?? [], [], 'no wake while Runtime is down');
  const record = JSON.parse(readFileSync(join(f.ports.stateRoot, 'alerts', readdirSync(join(f.ports.stateRoot, 'alerts'))[0]), 'utf8'));
  assert.deepEqual(Object.values(record.incidents).map(item => [item.kind, item.issues]), [['runtime', [12, 15]]]);
  for (let i = 0; i < 2; i++) { f.time += 30 * minute; await f.tick(); }
  assert.equal(f.sent.length, 1, 'the open outage sends nothing more');
  f.health = { state: 'healthy', detail: 'HTTP 200' }; f.time += 30 * minute;
  await f.tick();
  assert.equal(f.sent.length, 2); assert.match(f.sent[1], /PDD Autopilot recovered: runtime/);
  const rules = f.rules();
  assert.deepEqual(rules.map(rule => [rule.kind, rule.number]), [['runtime-ready', 12], ['runtime-ready', 15]], 'oldest first');
  for (const rule of rules) {
    assert.ok(rule.reason.indexOf(`pdd test --read ${BATCH}`) >= 0, 'read the saved result first');
    assert.ok(rule.reason.indexOf('pdd test --read') < Math.max(rule.reason.indexOf('--retry'), rule.reason.indexOf('again')), 'the read comes before any resend');
  }
  assert.match(rules[0].reason, /unknown outcome: never send it again blind/); assert.doesNotMatch(rules[0].reason, /--retry/, 'an unknown outcome is never resent');
  assert.match(rules[1].reason, new RegExp(`pdd test --retry ${BATCH}`)); assert.match(rules[1].reason, /Never resend a failed/);
  f.waits = []; f.time += 30 * minute; await f.tick();
  assert.equal(f.sent.length, 2, 'one recovery only');
});

test('AI-service errors in two issues close together: one outage, one test wake of the oldest, the rest after it passes', async t => {
  const f = await launcher(t);
  await f.start(); f.prompts.length = 0;
  const first = f.time;
  f.waits = [wait(12, first), wait(15, first + 2 * minute)]; f.time += 3 * minute;
  await f.tick();
  assert.equal(f.sent.length, 1); assert.match(f.sent[0], /AI-service errors in 2 different issues within 15 minutes/);
  assert.deepEqual(f.rules(), [], 'the health check cannot see AI-service errors, so the first test waits');
  f.time += 30 * minute; await f.tick();
  assert.deepEqual(f.rules().map(rule => [rule.kind, rule.number]), [['runtime-ready', 12]]); assert.match(f.rules()[0].reason, /as a test/);
  // The test run fails again: the outage stays and no other run is woken.
  const prompts = f.prompts.length;
  f.waits = [wait(15, first + 2 * minute), wait(12, f.time + minute)]; f.time += 2 * minute; await f.tick();
  assert.equal(f.prompts.length, prompts); assert.equal(f.sent.length, 1);
  f.time += 30 * minute; await f.tick();
  assert.deepEqual(f.rules().map(rule => [rule.kind, rule.number]), [['runtime-ready', 15]], 'the next test wake is the oldest waiting run');
  // It ran: it no longer waits after the settle time. Runtime is back for all.
  f.waits = [wait(12, f.waits[1].at)]; f.time += 11 * minute; await f.tick();
  assert.equal(f.sent.length, 2); assert.match(f.sent[1], /recovered: runtime/);
  assert.deepEqual(f.rules().map(rule => [rule.kind, rule.number]), [['runtime-ready', 12]]);
});

test('the runtime alert kind is one incident per repository and machine', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-runtime-alert-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const env = { HOME: dir, XDG_CONFIG_HOME: join(dir, 'config') }, sent = [];
  mkdirSync(join(dir, 'config', 'pdd'), { recursive: true });
  writeFileSync(join(dir, 'config', 'pdd', 'autopilot-alerts.json'), JSON.stringify({ v: 1, service: 'slack', url: 'https://hooks.slack.com/services/T/B/x' }));
  const ports = { stateRoot: join(dir, 'state'), hostname: () => 'host-a', repository: async () => ({ nameWithOwner: 'owner/repo' }), http: async ({ body }) => { sent.push(body.text); return { status: 200, text: 'ok' }; } };
  const call = (issue, kind, fields) => runAutopilotAlerts({ action: 'alert', cwd: dir, env, issue, kind, text: JSON.stringify(fields) }, ports);
  const fields = { cause: 'Runtime down', tried: 'retries', need: 'nothing now' };
  assert.equal((await call('12', 'runtime', fields)).exitCode, 0);
  assert.match((await call('15', 'runtime', fields)).message, /Added #15 to the open runtime alert/);
  assert.equal(sent.length, 1);
  assert.match((await call('15', 'recovered', { cause: 'Runtime is back', kind: 'runtime' })).message, /Recovery sent/);
  assert.equal(sent.length, 2); assert.match(sent[1], /recovered: runtime/); assert.match(sent[1], /issues\/12, https:\/\/github.com\/owner\/repo\/issues\/15/);
});
