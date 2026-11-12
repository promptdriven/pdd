import './helpers/test-home.mjs';
import { isolatedCheckCapacity } from './helpers/check-machine.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
// #3039: an interpreter outage parks only the runs that need the interpreter, frees their slots, alerts once and recovers by itself.
// Every the interpreter, health, HTTP, Discord and clock port is injected; no test calls the real the interpreter or a chat service.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { cpSync, mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { createServer } from 'node:http';
import { parkAutomaticRun, runStatus, changeRun, stepDone, startRun, approveRun, yieldAutomaticCapacity, runtimeWakeTag } from '../src/workflow-runner.mjs';
import { writeRun } from '../src/workflow-runs.mjs';
import { checkCause, savedCheckCause } from '../src/workflow-results.mjs';
import { checkRuntimeHealth, runCheck } from '../src/runtime-seam.mjs';
import { fakeRuntime, harbor, portsFor } from './runtime-fake.mjs';
import { runAutopilotAlerts } from '../src/autopilot-alerts.mjs';
import { createDependencyReadPorts, readDependencySnapshot } from '../src/issue-dependencies-github.mjs';
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { runIssueGraph } from '../src/issue-dependency-graph.mjs';
import { renderIssueGraph } from '../src/issue-dependency-graph-view.mjs';
import { fixture as runFixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const BATCH = '20261027-170500-abcd';
// pdd's own words for an interpreter 401 and for a server step deadline (runtime-client AUTH_TEXT, runtime-output stepTimeLimit).
const AUTH_TEXT = 'The PDD interpreter did not accept your GitHub login (HTTP 401). Run gh auth login, then run the command again.';
const TIME_LIMIT = { code: 'graph-provider-failure', step: 'move', minutes: 10, message: 'Step move took more than 10 minutes and was stopped.', fix: 'Make the step smaller, for example split 30 moves into 3 steps of 10.' };
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

test('an AI-service no-verdict parks only this run for the interpreter: no question, visible status, slot free, wake by delivery', async t => {
  const { f, ports, root } = await automaticRun(t);
  savedCheck(f, [{ state: 'refused', refusals: [{ code: 'graph-provider-failure' }] }]);
  const before = f.record();
  const parked = await parkAutomaticRun({ reason: 'graph-provider-failure: the AI service failed', runtime: true, cwd: root }, ports());
  assert.equal(parked.exitCode, 0, parked.message);
  assert.match(parked.message, /waits for the interpreter/); assert.match(parked.message, /Ask no person/); assert.match(parked.message, new RegExp(`pdd test --read ${BATCH}`));
  const run = f.record();
  assert.equal(run.state, 'paused'); assert.deepEqual(run.runtimeWait, { at: f.clock, reason: 'graph-provider-failure: the AI service failed', batch: BATCH, cause: 'service' });
  assert.equal(run.question ?? null, null, 'no question to a person');
  for (const key of ['area', 'done', 'gate', 'branch', 'root', 'automaticOrigin', 'chats']) assert.deepEqual(run[key], before[key], `${key} is kept`);
  const status = await runStatus({ ref: '17', cwd: f.source }, ports());
  assert.match(status.message, /State: waiting for the interpreter: graph-provider-failure/); assert.doesNotMatch(status.message, /waiting for you/);
  const listed = JSON.parse((await runStatus({ cwd: f.source, json: true }, ports())).message).runs[0];
  assert.equal(listed.group, 'working', 'an interpreter wait is not a person question'); assert.match(listed.words, /^waiting for the interpreter/);
  // The worker ends its turn: the coordinator may yield the slot under the existing rule.
  const chat = run.chats.find(item => item.area === run.areas[run.area].name);
  f.herdr.paneOf(chat).agent.agent_status = 'done';
  const requests = [];
  const yielded = await yieldAutomaticCapacity({ ref: '17', cwd: f.source }, ports({ requestAutopilotCompletion: async args => { requests.push(args); return { state: 'reconciled' }; } }));
  assert.equal(yielded.exitCode, 0, yielded.message); assert.equal(requests.length, 1);
  for (const key of ['state', 'runtimeWait', 'area', 'done', 'gate', 'automaticOrigin', 'root', 'branch']) assert.deepEqual(f.record()[key], run[key], `yield keeps ${key}`);
  // The coordinator wakes it through the existing delivery route.
  f.herdr.paneOf(chat).agent.agent_status = 'idle';
  const text = `${runtimeWakeTag(run.runtimeWait.at)} The interpreter is back. First run pdd test --read ${BATCH} once.`;
  const woken = await changeRun({ ref: '17', cwd: f.source, text, packageRoot }, ports());
  assert.equal(woken.exitCode, 0, woken.message);
  assert.equal(f.record().state, 'running'); assert.equal(f.record().runtimeWait, undefined);
  // A second copy of the same wake (a completion tick offered it again) reaches the chat at most once per park.
  const prompts = f.herdr.paneOf(chat).agent.prompts.length;
  const again = await changeRun({ ref: '17', cwd: f.source, text, packageRoot }, ports());
  assert.equal(again.exitCode, 0, again.message); assert.match(again.message, /Nothing was sent/);
  assert.equal(f.herdr.paneOf(chat).agent.prompts.length, prompts, 'the chat gets the wake once');
  assert.equal(f.record().changes.filter(change => change.text.startsWith('Interpreter wake for the park')).length, 1);
});

for (const [name, rows, words] of [
  ['a failed expectation', [{ state: 'failed' }], /this issue's own work/],
  ['a file-rule refusal', [{ state: 'refused', refusals: [{ code: 'invalid-input' }] }], /this issue's own work/],
  ['an AI-service refusal next to a failed Story', [{ state: 'refused', refusals: [{ code: 'graph-provider-failure' }] }, { state: 'failed' }], /this issue's own work/],
  ['a sign-in problem', [{ state: 'not_run', note: { code: 'blocked', message: 'Run gh auth login' } }], /access/],
  ['an interpreter 401 with another error code', [{ state: 'not_run', note: { code: 'invalid-token', message: AUTH_TEXT } }], /a person must fix the sign-in.*gh auth status/],
  ['a step time limit', [{ state: 'refused', refusals: [{ code: 'graph-provider-failure', message: 'The AI provider failed.' }], time_limit: TIME_LIMIT, reason: { code: TIME_LIMIT.code, message: `${TIME_LIMIT.message} ${TIME_LIMIT.fix}` } }], /this issue's own work.*make the step smaller/],
  ['a passed check', [{ state: 'passed' }], /passed/],
]) test(`${name} is not an interpreter outage: park --interpreter refuses and changes nothing`, async t => {
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

test('a result read that fails is an unknown outcome, never "no check ran"', async t => {
  const { f, ports, root } = await automaticRun(t);
  const parked = await parkAutomaticRun({ reason: 'not run after 3 tries', runtime: true, cwd: root }, ports({ readRunResults: () => { throw Object.assign(Error('EACCES'), { code: 'EACCES' }); } }));
  assert.equal(parked.exitCode, 0, parked.message);
  assert.equal(f.record().runtimeWait.cause, 'unknown');
});

test('savedCheckCause: a check still open, a stale summary after an interrupted retry, or unreadable rows is unknown', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-runtime-cause-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const env = { HOME: dir, PDD_STATE_DIR: dir };
  const save = (name, { summary, batch }) => {
    const folder = join(dir, 'batches', name); mkdirSync(folder, { recursive: true });
    if (summary) writeFileSync(join(folder, 'summary.json'), JSON.stringify({ batch: name, rows: summary }));
    if (batch) writeFileSync(join(folder, 'batch.json'), JSON.stringify({ version: 1, batch: name, intent: 'check', rows: batch }));
  };
  const busy = { test: 'tests/a.json', story: 'a', state: 'not_run', busy: true, note: { code: 'check-busy' } };
  save('20261106-120000-aaaa', { summary: [busy], batch: [busy] });
  assert.equal(savedCheckCause('20261106-120000-aaaa', { env }), 'service');
  // pdd test --retry stopped in the middle: the old summary says not run, the saved rows were sent again.
  save('20261106-120000-bbbb', { summary: [busy], batch: [{ ...busy, state: 'unknown', busy: false, request_ids: ['new-request'] }] });
  assert.equal(savedCheckCause('20261106-120000-bbbb', { env }), 'unknown');
  save('20261106-120000-cccc', { summary: [busy], batch: [{ ...busy, state: 'sending' }] });
  assert.equal(savedCheckCause('20261106-120000-cccc', { env }), 'unknown');
  save('20261106-120000-dddd', {});
  assert.equal(savedCheckCause('20261106-120000-dddd', { env }), 'unknown', 'a named check that cannot be read');
  assert.equal(savedCheckCause('not-a-batch', { env }), 'none');
});

test('pdd graph shows the interpreter wait as a hold of its own issue only', async () => {
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
  const graph = projectIssueGraph({ snapshot });
  const { html } = renderIssueGraph({ graph, repository: 'example/project', selected: key(17) });
  assert.match(html, /<li>Waiting for the interpreter<\/li>/);
  assert.doesNotMatch(html, /Waiting for Runtime/);
  const command = await runIssueGraph({ cwd: '', repository: 'example/project' }, {
    cache: { read: async () => ({ json: '' }), write: async () => ({ ok: true }) },
    snapshots: { read: async () => ({ snapshot }) },
  });
  assert.equal(command.exitCode, 0);
  assert.match(command.message, /\n  Waiting for the interpreter\n/);
  assert.doesNotMatch(command.message, /Waiting for Runtime/);
  assert.ok(graph.nodes.find(node => node.key === key(17)).reasons.includes('Waiting for the interpreter'));
  assert.ok(!graph.nodes.find(node => node.key === key(18)).reasons.includes('Waiting for the interpreter'));
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
    // A step time limit is this issue's own work (split the step), in the summary shape and in the saved batch shape.
    [[{ state: 'refused', refusals: [{ code: 'graph-provider-failure' }], time_limit: TIME_LIMIT }], 'issue'],
    [[{ state: 'unknown', reason: { code: TIME_LIMIT.code, message: `${TIME_LIMIT.message} ${TIME_LIMIT.fix}` } }], 'issue'],
    [[{ state: 'refused', refusals: [{ code: 'graph-provider-failure', engine_message: 'step deadline exceeded after 600 seconds' }] }], 'issue'],
    // An interpreter 401 is a sign-in problem whatever its error code.
    [[{ state: 'not_run', note: { code: 'invalid-token', message: AUTH_TEXT } }], 'access'],
    [[{ state: 'unknown', why: AUTH_TEXT }], 'access'],
    // pdd's temporary PDD Cloud answer (503 cloud-unavailable) is a service state, not a sign-in problem.
    [[{ state: 'not_run', note: { code: 'blocked', message: 'PDD Cloud could not confirm your access. Try again in a minute.' } }], 'service'],
    [[{ state: 'not_run', note: { code: 'blocked', message: 'Your GitHub login octo is not on the PDD interpreter invite list yet.' } }], 'access'],
    [[{ state: 'running' }], 'unknown'],
  ];
  for (const [rows, cause] of cases) assert.equal(checkCause(rows), cause, JSON.stringify(rows));
});

test('the health check is one free GET of /v1/capacity: no source, no check, no AI call', async () => {
  const calls = [];
  const probe = async (reply, gh = { status: 0, stdout: 'gho_token\n' }) => checkRuntimeHealth({ env: { HOME: '/nowhere', PDD_RUNTIME_URL: 'https://runtime.example.test' } }, {
    gh: args => { calls.push(['gh', ...args]); return gh; }, now: () => Date.parse('2026-11-06T12:00:00Z'),
    fetch: async (url, init) => { calls.push([init.method, String(url), init.body ?? null, init.headers.Authorization]); if (reply instanceof Error) throw reply; return new Response(reply.body ?? '', { status: reply.status }); } });
  // An older interpreter without the capacity read answers 404 with JSON; a 404 page that is not JSON is a wrong address.
  assert.deepEqual(await probe({ status: 404, body: '{"error":{"code":"not-found"}}' }), { state: 'healthy', detail: 'HTTP 404' });
  for (const body of ['<html>Not Found</html>', '']) {
    const health = await probe({ status: 404, body });
    assert.equal(health.state, 'access', JSON.stringify(body)); assert.match(health.fix, /PDD_RUNTIME_URL/);
  }
  calls.length = 0;
  assert.deepEqual(await probe({ status: 200, body: '{"maintenance":null,"slots":{"check":{"running":0,"limit":4}}}' }), { state: 'healthy', detail: 'HTTP 200' });
  assert.deepEqual(calls, [['gh', 'auth', 'token'], ['GET', 'https://runtime.example.test/v1/capacity', null, 'Bearer gho_token']]);
  assert.equal((await probe({ status: 503, body: 'The runtime opens soon.' })).state, 'unavailable');
  assert.equal((await probe({ status: 502 })).state, 'unavailable');
  assert.equal((await probe({ status: 429 })).state, 'unavailable');
  assert.equal((await probe(Object.assign(Error('fetch failed'), { cause: { code: 'ECONNREFUSED' } }))).state, 'unavailable');
  // #3241: a maintenance answer names its end and reason, so the core can wait for it.
  assert.deepEqual(await probe({ status: 200, body: '{"maintenance":{"until":"2026-11-06T13:00:00Z"}}' }), { state: 'unavailable', detail: 'maintenance', until: '2026-11-06T13:00:00.000Z', reason: null });
  assert.deepEqual(await probe({ status: 200, body: '{"maintenance":{"until":"2026-11-06T13:00:00Z","reason":"deploy gho_token"}}' }), { state: 'unavailable', detail: 'maintenance', until: '2026-11-06T13:00:00.000Z', reason: 'deploy [secret]' });
  // An answer that is neither healthy nor down is a sign-in or setup problem: it names its fix.
  for (const [reply, fix] of [[{ status: 401 }, /gh auth status/], [{ status: 403 }, /gh auth status/], [{ status: 302 }, /PDD_RUNTIME_URL/],
    [{ status: 200, body: '<html>proxy login</html>' }, /PDD_RUNTIME_URL/], [{ status: 418 }, /PDD_RUNTIME_URL/]]) {
    const health = await probe(reply);
    assert.equal(health.state, 'access', JSON.stringify(reply)); assert.match(health.fix, fix); assert.doesNotMatch(JSON.stringify(health), /gho_token/);
  }
  calls.length = 0;
  const signedOut = await probe({ status: 200 }, { status: 1, stdout: '' });
  assert.equal(signedOut.state, 'access'); assert.match(signedOut.fix, /gh auth status/);
  assert.deepEqual(calls, [['gh', 'auth', 'token']], 'no sign-in sends nothing');
  const badAddress = await checkRuntimeHealth({ env: { HOME: '/nowhere', PDD_RUNTIME_URL: 'ftp://runtime.example.test/path' } }, { gh: () => { throw Error('not called'); }, fetch: async () => { throw Error('not called'); } });
  assert.equal(badAddress.state, 'access'); assert.match(badAddress.fix, /PDD_RUNTIME_URL/);
});

// ---- Launcher ticks, with fake Herdr, GitHub, health and alert ports (adapted from autopilot-launcher.test.mjs).
async function launcher(t) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-runtime-outage-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, 'repo'), home = join(dir, 'home');
  mkdirSync(cwd); mkdirSync(home);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const f = { dir, cwd, home, time: Date.parse('2026-11-06T12:00:00Z'), prompts: [], issues: [], waits: [], health: { state: 'healthy', detail: 'HTTP 200' }, healthCalls: 0, probe: 'pending', alerts: [], sent: [] };
  f.ports = {
    ...healthyMachine,
    allocationCheck: async () => ({ state: 'ready', message: '' }),
    checkCapacityPorts: isolatedCheckCapacity(dir), stateRoot: join(home, 'state'), now: () => f.time, readRunProgress: async () => [], warn: () => {},
    readRuntimeWaits: async () => structuredClone(f.waits),
    runtimeHealth: async () => { f.healthCalls++; return f.health; },
    readRuntimeProbe: async () => f.probe,
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }), pathDiagnostic: () => [],
    run: async (command, args) => {
      if (command === 'git') return { code: 0, stdout: cwd + '\n', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo","defaultBranchRef":{"name":"main"},"url":"https://github.com/owner/repo"}', stderr: '' };
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
      // #3123 admission reads complete native pane inventory before allocation.
      if (args[0] === 'pane' && args[1] === 'list') return {result: {type: 'pane_list', panes: [live]}};
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
const T0 = Date.parse('2026-11-06T12:00:00Z');

const kinds = f => f.rules().map(rule => [rule.kind, rule.number]);
// Ticks every 30 minutes; a delivered wake ends the wait, and an issue failure of its own waits again 5 minutes later.
async function hours(f, count, { persistent = new Set(), after = () => {} } = {}) {
  const log = []; let seen = f.prompts.length;
  for (let i = 0; i < count * 2; i++) {
    await f.tick();
    const rules = f.prompts.length > seen ? kinds(f) : []; seen = f.prompts.length;
    log.push(...rules);
    for (const [kind, number] of rules) if (kind === 'runtime-ready') {
      const old = f.waits.find(w => w.number === number);
      f.waits = f.waits.filter(w => w.number !== number);
      if (persistent.has(number)) f.waits.push(wait(number, f.time + 5 * minute, { mark: old.mark }));
    } else if (kind === 'runtime-stuck') f.waits = f.waits.filter(w => w.number !== number);
    after(rules);
    f.time += 30 * minute;
  }
  return log;
}

test('the interpreter alert kind is one incident per repository and machine', async t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-runtime-alert-')); t.after(() => rmSync(dir, { recursive: true, force: true }));
  const env = { HOME: dir, XDG_CONFIG_HOME: join(dir, 'config') }, sent = [];
  mkdirSync(join(dir, 'config', 'pdd'), { recursive: true });
  writeFileSync(join(dir, 'config', 'pdd', 'autopilot-alerts.json'), JSON.stringify({ v: 1, service: 'slack', url: 'https://hooks.slack.com/services/T/B/x' }));
  const ports = { stateRoot: join(dir, 'state'), hostname: () => 'host-a', repository: async () => ({ nameWithOwner: 'owner/repo' }), http: async ({ body }) => { sent.push(body.text); return { status: 200, text: 'ok' }; } };
  const call = (issue, kind, fields) => runAutopilotAlerts({ action: 'alert', cwd: dir, env, issue, kind, text: JSON.stringify(fields) }, ports);
  const fields = { cause: 'The interpreter down', tried: 'retries', need: 'nothing now' };
  assert.equal((await call('12', 'interpreter', fields)).exitCode, 0);
  assert.match((await call('15', 'interpreter', fields)).message, /Added #15 to the open interpreter alert/);
  assert.equal(sent.length, 1);
  assert.match((await call('15', 'recovered', { cause: 'The interpreter is back', kind: 'interpreter' })).message, /Recovery sent/);
  assert.equal(sent.length, 2); assert.match(sent[1], /recovered: interpreter/); assert.match(sent[1], /issues\/12, https:\/\/github.com\/owner\/repo\/issues\/15/);
});

test('release: native mixed broken-test batch cannot park as an interpreter outage', async t => {
  const { f, ports, root } = await automaticRun(t);
  const template = join(packageRoot, 'test', 'fixtures', 'harbor');
  for (const dir of ['user_stories', 'tests', 'prompts']) cpSync(join(template, dir), join(root, dir), { recursive: true });
  const bad = JSON.parse(readFileSync(join(root, 'tests/place-order.json'), 'utf8'));
  bad.story_path = 'user_stories/bad-order.md'; bad.steps[0].input.items[0].quantity = 0;
  cpSync(join(root, 'user_stories/place-order.md'), join(root, bad.story_path));
  writeFileSync(join(root, 'tests/bad-order.json'), JSON.stringify(bad));
  const fake = await fakeRuntime(t, (entry, runtime) => runtime.normal(entry));
  const made = portsFor({ HOME: f.ports.env.HOME, PDD_RUNTIME_URL: fake.origin }); made.clock.now = f.clock;
  assert.equal(await runCheck({ cwd: root, words: [], options: { '--json': true } }, made.ports), 4);
  const result = JSON.parse(made.ports.stdout.text), broken = result.rows.find(row => row.test === 'tests/bad-order.json');
  assert.equal(broken.state, 'not run'); assert.equal(broken.refusals[0].code, 'invalid-input');
  assert.equal(result.rows.some(row => row.state === 'passed'), true);
  const cause = savedCheckCause(result.batch, { env: { HOME: f.ports.env.HOME } });
  const out = await parkAutomaticRun({ reason: 'last check did not pass', runtime: true, cwd: root }, ports());
  assert.equal(out.exitCode, 1); assert.equal(cause, 'issue'); assert.equal(f.record().state, 'running');
});
for (const state of ['not run', 'partial']) test(`release: named ${state} retains access and uncertain dispatch routes`, () => {
  assert.equal(checkCause([{ state, reason: { code: 'auth-required' } }]), 'access');
  assert.equal(checkCause([{ state, reason: { code: 'broken-test' } }]), 'issue');
  assert.equal(checkCause([{ state: 'partial', reason: { code: 'dispatch-uncertain' } }]), 'unknown');
  assert.equal(checkCause([{ state: 'partial', reason: { code: 'graph-provider-failure' } }]), 'service');
});

test('release: saved legacy and public state spellings retain the same access cause', async t => {
  const { f } = await automaticRun(t);
  savedCheck(f, [{ state: 'not run', reason: { code: 'auth-required' } }]);
  const path = join(f.ports.env.HOME, '.pdd', 'runtime', 'batches', BATCH, 'batch.json');
  const batch = JSON.parse(readFileSync(path, 'utf8')); batch.rows[0].state = 'not_run';
  writeFileSync(path, JSON.stringify(batch));
  assert.equal(savedCheckCause(BATCH, { env: f.ports.env }), 'access');
});

