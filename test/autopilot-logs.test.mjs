import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync, spawn, spawnSync } from 'node:child_process';
import { once } from 'node:events';
import { appendFileSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, renameSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runPdd } from '../src/pdd-cli.mjs';

const bin = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
const write = (path, value) => writeFileSync(path, JSON.stringify(value));
const snapshot = root => Object.fromEntries(readdirSync(root, { recursive: true, withFileTypes: true })
  .filter(entry => entry.isFile()).map(entry => {
    const file = join(entry.parentPath, entry.name);
    return [file, readFileSync(file, 'utf8')];
  }));

function fixture(t) {
  const root = mkdtempSync(join(import.meta.dirname, '.worker-view-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const cwd = join(root, 'repo'), home = join(root, 'home'), queue = join(root, 'queue');
  mkdirSync(cwd); mkdirSync(queue);
  execFileSync('git', ['init', '-q', cwd]);
  const id = createHash('sha256').update(cwd).digest('hex').slice(0, 20);
  const state = join(home, '.local', 'state', 'pdd', 'autopilot');
  const core = join(state, `${id}-core`), logs = join(core, 'logs'), jobs = join(core, 'jobs');
  mkdirSync(logs, { recursive: true }); mkdirSync(jobs);
  write(join(state, `${id}.json`), { cwd, mode: 'observe', enabled: true, engine: 'core', environment: { PDD_SUITE_QUEUE: queue } });
  const env = { ...process.env, HOME: home, PDD_SUITE_QUEUE: join(root, 'not-the-worker-queue') };
  const jobFile = issue => join(jobs, `${issue}.json`);
  const save = job => {
    write(join(jobs, 'job.tmp'), job);
    renameSync(join(jobs, 'job.tmp'), jobFile(job.issue));
  };
  const cli = (...args) => spawnSync(process.execPath, [bin, 'autopilot', ...args], { cwd, env, encoding: 'utf8', timeout: 5000 });
  const start = async (args, options = {}) => {
    const child = spawn(process.execPath, args, { cwd, env, stdio: 'ignore', ...options });
    const exit = once(child, 'exit');
    t.after(async () => { child.kill('SIGKILL'); await exit; });
    await once(child, 'spawn');
    return { child, exit };
  };
  const worker = async (issue, role, text) => {
    const base = join(logs, `${issue}-${role}-fixture`);
    const token = `${base}.spec.json`, log = `${base}.log`, result = `${base}.result.json`, exit = `${base}.exit.json`;
    const proc = await start(['-e', 'setInterval(() => {}, 10000)', token], { detached: true });
    writeFileSync(log, text);
    write(result, { note: 'result body not streamed' });
    return { proc, agent: { pid: proc.child.pid, token, log, result, exit, started: Date.now() - 1000 } };
  };
  return { root, cwd, queue, env, save, jobFile, cli, start, worker };
}

function captureOutput(child) {
  let output = '', errors = '';
  child.stdout.setEncoding('utf8').on('data', chunk => { output += chunk; });
  child.stderr.setEncoding('utf8').on('data', chunk => { errors += chunk; });
  return { output: () => output, errors: () => errors };
}

async function untilOutput(child, captured, expected) {
  const deadline = Date.now() + 8000;
  while (!expected.test(captured.output()) && child.exitCode === null && child.signalCode === null && Date.now() < deadline) {
    await new Promise(done => setTimeout(done, 25));
  }
  assert.match(captured.output(), expected, captured.errors());
}

test('Autopilot help discovers worker logs and follow requires an issue', t => {
  const scope = fixture(t);
  const help = scope.cli('--help');
  assert.equal(help.status, 0, help.stderr);
  assert.match(help.stdout, /pdd autopilot logs \[--issue N \[--follow\]\]/);
  assert.equal(scope.cli('logs', '--follow').status, 2);
  assert.equal(scope.cli('logs', '--issue', '0').status, 2);
  const empty = scope.cli('logs');
  assert.equal(empty.status, 0, empty.stderr);
  assert.match(empty.stdout, /No current Autopilot workers/);
  const absent = scope.cli('logs', '--issue', '42', '--follow');
  assert.equal(absent.status, 1, absent.stderr);
  assert.match(absent.stderr, /No current Autopilot worker.*#42.*pdd autopilot logs/);
});

test('Autopilot logs lists workers, selects a grouped issue and does not mutate observe-mode state', async t => {
  const scope = fixture(t);
  const { agent } = await scope.worker(42, 'repair', '\u001b[35mrepair progress\u001b[0m\n');
  scope.save({ issue: 43, phase: 'running', role: 'build' });
  scope.save({ issue: 42, issues: [42, 122], phase: 'running', role: 'repair', agent, lastError: 'waiting for account quota' });
  const before = snapshot(scope.root);
  const list = scope.cli('logs');
  assert.equal(list.status, 0, list.stderr);
  assert.match(list.stdout, /#42 .*repair.*last activity .*Z[\s\S]*#43 .*build/);
  assert.doesNotMatch(list.stdout, /repair progress/);
  let stdout = '', stderr = '';
  const sideEffects = [];
  const exitCode = await runPdd(['autopilot', 'logs', '--issue', '122'], {
    cwd: scope.cwd, env: scope.env, stdout: { write: text => { stdout += text; } }, stderr: { isTTY: true, write: text => { stderr += text; } },
    syncOwnedUserSkills: () => sideEffects.push('sync skills'),
    releaseNotice: () => sideEffects.push('check releases'),
    autopilotGithub: { checkAutopilotSettings: () => sideEffects.push('contact GitHub') },
  });
  assert.equal(exitCode, 0, stderr);
  assert.match(stdout, /#42 .*#122/);
  assert.match(stdout, /repair: wrapper running; last activity \S+Z/);
  assert.match(stdout, /waiting for account quota/);
  assert.ok(stdout.includes(agent.log));
  assert.ok(stdout.includes(agent.result));
  assert.match(stdout, /\[repair\] repair progress/);
  assert.doesNotMatch(stdout, /\x1b|#43|result body not streamed/);
  assert.deepEqual(sideEffects, []);
  assert.deepEqual(snapshot(scope.root), before);
});

test('Autopilot logs distinguishes waiting, admitted, live and stale suite evidence', async t => {
  const scope = fixture(t);
  const { agent, proc } = await scope.worker(42, 'suite', 'suite output\n');
  const group = await scope.start(['-e', 'setInterval(() => {}, 10000)'], { detached: true });
  const receiptPath = join(scope.queue, 'ticket-2.json');
  const receipt = { ticket: 2, cwd: scope.cwd, pid: proc.child.pid, queuedAt: Date.now(), startedAt: null, finishedAt: null, state: 'waiting', receiptPath };
  write(join(scope.queue, 'ticket-1.json'), { ...receipt, ticket: 1, cwd: scope.root, receiptPath: null });
  write(receiptPath, receipt);
  scope.save({ issue: 42, phase: 'pr', pr: 101, suite: { cwd: scope.cwd, agent }, lane: { state: 'waiting', holder: 99 } });
  const show = () => {
    const result = scope.cli('logs', '--issue', '42');
    assert.equal(result.status, 0, result.stderr);
    return result.stdout;
  };
  const waiting = show();
  assert.match(waiting, /waiting for a check slot \(position 2\)/);
  assert.match(waiting, /merge lane.*PR #99/);
  assert.doesNotMatch(waiting, /tests running/);
  write(receiptPath, { ...receipt, state: 'running', startedAt: Date.now() });
  assert.match(show(), /tests have not started/);
  write(receiptPath, { ...receipt, state: 'running', startedAt: Date.now(), childPid: group.child.pid });
  const running = show();
  assert.match(running, /suite: wrapper running; tests running/);
  assert.ok(running.includes(receiptPath));
  write(receiptPath, { ...receipt, state: 'running', queuedAt: agent.started - 1, startedAt: Date.now(), childPid: group.child.pid });
  const old = show();
  assert.match(old, /no live test process confirmed/);
  assert.doesNotMatch(old, /tests running/);
  assert.ok(!old.includes(receiptPath));
  write(receiptPath, { ...receipt, state: 'running', startedAt: Date.now(), childPid: group.child.pid });
  proc.child.kill('SIGTERM'); await proc.exit;
  write(agent.exit, { code: 1, at: Date.now() });
  const stale = show();
  assert.match(stale, /suite: wrapper exited \(status 1\); no live test process confirmed/);
  assert.doesNotMatch(stale, /tests running/);
});

test('Autopilot follow streams append and repair transitions, then drains the last output', async t => {
  const scope = fixture(t);
  const build = await scope.worker(42, 'build', 'started build\n');
  scope.save({ issue: 42, phase: 'running', role: 'build', agent: build.agent });
  const { child, exit } = await scope.start([bin, 'autopilot', 'logs', '--issue', '42', '--follow'], { stdio: ['ignore', 'pipe', 'pipe'] });
  const captured = captureOutput(child);
  await untilOutput(child, captured, /\[build\] started build/);
  const message = JSON.stringify({ type: 'item.completed', item: { type: 'agent_message', text: 'finished build' } });
  appendFileSync(build.agent.log, message.slice(0, 45));
  appendFileSync(build.agent.log, `${message.slice(45)}\n`);
  const repair = await scope.worker(42, 'repair', 'started repair\n');
  scope.save({ issue: 42, phase: 'running', role: 'repair', agent: repair.agent });
  await untilOutput(child, captured, /\[repair\] started repair/);
  assert.match(captured.output(), /\[build\] finished build/);
  appendFileSync(repair.agent.log, 'final repair output');
  rmSync(scope.jobFile(42));
  await untilOutput(child, captured, /no longer current/);
  assert.deepEqual(await exit, [0, null]);
  assert.match(captured.output(), /\[repair\] final repair output/);
  assert.equal(captured.output().match(/started build/g)?.length, 1);
  assert.equal(captured.output().match(/started repair/g)?.length, 1);
});

test('Ctrl-C exits the Autopilot viewer without stopping its worker', async t => {
  const scope = fixture(t);
  const { agent, proc } = await scope.worker(42, 'build', 'worker remains alive\n');
  scope.save({ issue: 42, phase: 'running', role: 'build', agent });
  const { child, exit } = await scope.start([bin, 'autopilot', 'logs', '--issue', '42', '--follow'], { stdio: ['ignore', 'pipe', 'pipe'] });
  const captured = captureOutput(child);
  await untilOutput(child, captured, /worker remains alive/);
  child.kill('SIGINT');
  assert.deepEqual(await exit, [null, 'SIGINT']);
  assert.equal(proc.child.exitCode, null);
  assert.match(scope.cli('logs', '--issue', '42').stdout, /build: wrapper running/);
});

test('Autopilot logs bounds log reads and does not follow a replaced log symlink', async t => {
  const scope = fixture(t);
  const { agent } = await scope.worker(42, 'build', `old line\n${'x'.repeat(80_000)}\nrecent line\n`);
  scope.save({ issue: 42, phase: 'running', role: 'build', agent });
  const bounded = scope.cli('logs', '--issue', '42');
  assert.equal(bounded.status, 0, bounded.stderr);
  assert.match(bounded.stdout, /earlier log bytes omitted/);
  assert.match(bounded.stdout, /\[build\] recent line/);
  assert.doesNotMatch(bounded.stdout, /old line/);
  rmSync(agent.log);
  symlinkSync(agent.result, agent.log);
  const linked = scope.cli('logs', '--issue', '42');
  assert.equal(linked.status, 0, linked.stderr);
  assert.doesNotMatch(linked.stdout, /result body not streamed/);
});
