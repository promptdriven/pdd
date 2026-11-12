import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, writeFileSync, existsSync, rmSync, mkdirSync, chmodSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { agentCommand, jobEnvironment, startAgentJob, readAgentJob, stopAgentJob, agentJobCpu, agentJobHangs, jobStopper, hungRound } from '../src/agent-job.mjs';

const folder = t => { const dir = mkdtempSync(join(tmpdir(), 'pdd-agent-job-')); t.after(() => rmSync(dir, { recursive: true, force: true })); return dir; };
const fakePs = (dir, body) => {
  const bin = join(dir, 'bin'), file = join(bin, 'ps');
  mkdirSync(bin, { recursive: true }); writeFileSync(file, `#!/bin/sh\n${body}\n`); chmodSync(file, 0o755);
  return bin;
};
const until = async (check, ms = 10000) => {
  const end = Date.now() + ms;
  while (Date.now() < end) { const value = check(); if (value) return value; await new Promise(r => setTimeout(r, 25)); }
  assert.fail('condition not reached');
};
// A scripted agent: it reads the prompt on stdin and follows one instruction in it.
const SCRIPT = `
let text=''; process.stdin.on('data',c=>text+=c); process.stdin.on('end',()=>{
  const m=JSON.parse(text.split('\\n').find(l=>l.startsWith('{')));
  process.stdout.write('agent saw '+m.say+'\\n'); process.stderr.write('agent note\\n');
  if(m.result) require('fs').writeFileSync(m.result, JSON.stringify({outcome:'pr',pr:7,head:'a'.repeat(40)}));
  if(m.sleep) setTimeout(()=>process.exit(0), m.sleep); else process.exit(m.code ?? 0);
});`;

test('agent commands follow the headless auditor launch for codex and claude', () => {
  assert.deepEqual(agentCommand({ kind: 'codex', command: '/bin/codex' }), { command: '/bin/codex',
    args: ['exec', '--json', '--dangerously-bypass-approvals-and-sandbox', '-c', 'features.multi_agent=false', '-'] });
  assert.deepEqual(agentCommand({ kind: 'claude' }, { model: 'opus' }), { command: 'claude',
    args: ['-p', '--output-format', 'stream-json', '--verbose', '--permission-mode', 'bypassPermissions', '--model', 'opus'] });
  assert.throws(() => agentCommand({ kind: 'gemini' }), /codex or claude/);
});

test('job environment drops caller agent, Herdr and coordinator session markers', () => {
  const env = jobEnvironment({ HOME: '/h', PATH: '/bin', CODEX_HOME: '/c', CLAUDECODE: '1', CLAUDE_CODE_ENTRYPOINT: 'x', CODEX_THREAD_ID: 't',
    CODEX_SANDBOX: 'seatbelt', HERDR_PANE: 'p', PDD_AGENT_SESSION: 's', PDD_AUTOPILOT_CONTEXT: '{}', GH_TOKEN: 'keep' });
  assert.deepEqual(env, { HOME: '/h', PATH: '/bin', CODEX_HOME: '/c', GH_TOKEN: 'keep' });
});

test('a detached job writes its log, exit code and result file, and survives as files only', async t => {
  const dir = folder(t), result = join(dir, 'r.json');
  const job = startAgentJob({ id: '17-build-1', dir, cwd: dir, command: process.execPath, args: ['-e', SCRIPT],
    input: `Task\n${JSON.stringify({ say: 'hello', result })}\n`, env: { PATH: process.env.PATH } });
  assert.ok(Number.isSafeInteger(job.pid) && job.pid > 0);
  assert.equal(job.result, join(dir, '17-build-1.result.json'));
  const done = await until(() => { const s = readAgentJob({ ...job, result }); return s.state === 'exited' && s; });
  assert.deepEqual(done.exit.code, 0);
  assert.deepEqual(done.result, { outcome: 'pr', pr: 7, head: 'a'.repeat(40) });
  const log = readFileSync(job.log, 'utf8');
  assert.match(log, /agent saw hello/); assert.match(log, /agent note/);
});

test('a failed job reports its exit code and a missing result', async t => {
  const dir = folder(t);
  const job = startAgentJob({ id: '18-build-1', dir, cwd: dir, command: process.execPath, args: ['-e', SCRIPT],
    input: `${JSON.stringify({ say: 'x', code: 3 })}\n`, env: { PATH: process.env.PATH } });
  const done = await until(() => { const s = readAgentJob(job); return s.state === 'exited' && s; });
  assert.equal(done.exit.code, 3); assert.equal(done.result, null);
});

test('an invalid result file is reported as invalid, not as success', async t => {
  const dir = folder(t), job = { pid: 1, token: 'x', exit: join(dir, 'e.json'), result: join(dir, 'r.json') };
  writeFileSync(job.exit, JSON.stringify({ code: 0, signal: null, at: 1 }));
  writeFileSync(job.result, '{not json');
  assert.equal(readAgentJob(job, { alive: () => false }).result, 'invalid');
  writeFileSync(job.result, '[1]');
  assert.equal(readAgentJob(job, { alive: () => false }).result, 'invalid');
});

test('a dead job without an exit file is dead; a reused pid without the job token is not alive', async t => {
  const dir = folder(t);
  const job = { pid: process.pid, token: join(dir, 'never-started.spec.json'), exit: join(dir, 'e.json'), result: join(dir, 'r.json') };
  assert.equal(readAgentJob(job).state, 'dead');
  assert.equal(readAgentJob(job, { alive: () => true }).state, 'running');
});

test('the native liveness read keeps a long job token after ps wide output', t => {
  const dir = folder(t), token = `job-${'x'.repeat(200)}`, bin = fakePs(dir, 'case "$LC_ALL:$*" in C:*-ww*) printf "%s\\n" "$PS_TOKEN" ;; *) printf "%s\\n" "node truncated" ;; esac');
  const module = new URL('../src/agent-job.mjs', import.meta.url).href;
  const child = spawnSync(process.execPath, ['--input-type=module', '-e', `import { readAgentJob } from ${JSON.stringify(module)}; process.stdout.write(readAgentJob({ pid: process.pid, token: process.env.PS_TOKEN, exit: '/missing-exit', result: '/missing-result' }).state);`],
    { encoding: 'utf8', env: { ...process.env, PATH: `${bin}:${process.env.PATH}`, PS_TOKEN: token } });
  assert.equal(child.status, 0, child.stderr);
  assert.equal(child.stdout, 'running');
});

test('stop ends the whole job process group and the wrapper records the signal', async t => {
  const dir = folder(t);
  const job = startAgentJob({ id: '19-build-1', dir, cwd: dir, command: process.execPath, args: ['-e', SCRIPT],
    input: `${JSON.stringify({ say: 'long', sleep: 60000 })}\n`, env: { PATH: process.env.PATH } });
  await until(() => readAgentJob(job).state === 'running' && existsSync(job.log) && /agent saw long/.test(readFileSync(job.log, 'utf8')));
  assert.equal(stopAgentJob(job), true);
  const done = await until(() => { const s = readAgentJob(job); return s.state !== 'running' && s; });
  assert.equal(done.state, 'exited'); assert.ok(done.exit.signal || done.exit.code !== 0);
  assert.equal(stopAgentJob(job), false);
});

// CHAOS-B2: a hung `npm ci` under `sh` took the first SIGTERM as "stop gracefully" and lived on as an orphan.
// The grandchild ignores every SIGTERM, so only the group SIGKILL after the grace time ends it.
test('stop ends the whole process group after the grace time: a grandchild that ignores every SIGTERM does not survive', async t => {
  const dir = folder(t), mark = join(dir, 'grandchild.pid');
  const grandchild = `require('fs').writeFileSync(${JSON.stringify(mark)}, String(process.pid)); process.on('SIGTERM', () => {}); setInterval(() => {}, 1000);`;
  const job = startAgentJob({ id: '20-suite-1', dir, cwd: dir, command: '/bin/sh', args: ['-c', `${JSON.stringify(process.execPath)} -e ${JSON.stringify(grandchild)} & wait`],
    input: '', env: { PATH: process.env.PATH } });
  const pid = Number(await until(() => existsSync(mark) && readFileSync(mark, 'utf8')));
  t.after(() => { try { process.kill(pid, 'SIGKILL'); } catch {} });
  const stoppedAt = Date.now();
  assert.equal(stopAgentJob(job), true);
  const groupAlive = () => { try { process.kill(-job.pid, 0); return true; } catch (error) { return error.code !== 'ESRCH'; } };
  await until(() => !groupAlive(), 20000);   // the grace is 2 s; a loaded machine needs longer to reap (only the test timeout)
  assert.throws(() => process.kill(pid, 0), { code: 'ESRCH' }, 'the grandchild is gone');
  const done = readAgentJob(job);
  assert.equal(done.state, 'exited'); assert.equal(done.exit.signal, 'SIGTERM', JSON.stringify(done.exit));
  // A real-process smoke check with a wide bound (the order and the grace time are checked with ports below): the exit
  // record, written just before the group SIGKILL, comes after the grace time and within 15 s on a loaded machine.
  const after = done.exit.at - stoppedAt;
  assert.ok(after >= 1500 && after < 15000, `the SIGKILL came ${after} ms after the stop`);
});

// Claude round 5 SF, lead: the stop order with ports, not wall time: SIGTERM to the group, one timer of the grace time,
// then the exit record and SIGKILL to the group, then the exit; a failed record write never skips the SIGKILL.
test('jobStopper: a stop is SIGTERM, then after the grace time the exit record, SIGKILL and the exit, in that order', () => {
  const run = (options = {}) => {
    const log = [], timers = [];
    const stopper = jobStopper({ killGroup: signal => log.push(signal), setTimer: (fn, ms) => { log.push(`timer ${ms}`); timers.push(fn); },
      writeExit: record => { if (options.writeFails) throw Error('EISDIR'); log.push(`exit record ${record.signal} ${record.code}`); }, exit: () => log.push('exit'), now: () => 7, grace: 2000 });
    return { log, timers, stopper };
  };
  let { log, timers, stopper } = run();
  stopper.stop('SIGTERM');
  assert.deepEqual(log, ['SIGTERM', 'timer 2000'], 'nothing else before the grace time');
  stopper.stop('SIGINT'); stopper.exited(null, 'SIGTERM');
  assert.deepEqual(log, ['SIGTERM', 'timer 2000'], 'a second stop and the child exit change nothing');
  timers[0]();
  assert.deepEqual(log, ['SIGTERM', 'timer 2000', 'exit record SIGTERM null', 'SIGKILL', 'exit']);
  timers[0](); assert.equal(log.length, 5, 'it finishes once');
  // A failed exit record write never skips the group SIGKILL.
  ({ log, timers, stopper } = run({ writeFails: true }));
  stopper.stop('SIGHUP'); timers[0]();
  assert.deepEqual(log, ['SIGTERM', 'timer 2000', 'SIGKILL', 'exit']);
  // A child that ends by a stop signal before the wrapper's own handler runs is that stop (no orphan is left).
  ({ log, timers, stopper } = run());
  stopper.exited(null, 'SIGTERM');
  assert.deepEqual(log, ['SIGTERM', 'timer 2000']); timers[0]();
  assert.deepEqual(log.slice(2), ['exit record SIGTERM null', 'SIGKILL', 'exit']);
  // A child that exits by itself: the record, no group signal.
  ({ log, stopper } = run());
  stopper.exited(0, null);
  assert.deepEqual(log, ['exit record null 0', 'exit']);
});

// Codex delta 7: a failed exit-record write (here a folder at its path) never skips the group SIGKILL.
test('a stop whose exit record cannot be written still ends the whole group', async t => {
  const dir = folder(t), mark = join(dir, 'grandchild.pid');
  const grandchild = `require('fs').writeFileSync(${JSON.stringify(mark)}, String(process.pid)); process.on('SIGTERM', () => {}); setInterval(() => {}, 1000);`;
  const job = startAgentJob({ id: '22-suite-1', dir, cwd: dir, command: '/bin/sh', args: ['-c', `${JSON.stringify(process.execPath)} -e ${JSON.stringify(grandchild)} & wait`],
    input: '', env: { PATH: process.env.PATH } });
  const pid = Number(await until(() => existsSync(mark) && readFileSync(mark, 'utf8')));
  t.after(() => { try { process.kill(pid, 'SIGKILL'); } catch {} });
  mkdirSync(job.exit);                                                 // the rename of the exit record fails
  assert.equal(stopAgentJob(job), true);
  const groupAlive = () => { try { process.kill(-job.pid, 0); return true; } catch (error) { return error.code !== 'ESRCH'; } };
  await until(() => !groupAlive(), 20000);   // the grace is 2 s; a loaded machine needs longer to reap
  assert.throws(() => process.kill(pid, 0), { code: 'ESRCH' }, 'the grandchild is gone');
});

test('agentJobCpu sums the tree under the wrapper by parent pid, without the wrapper and the agent CLI', () => {
  const table = [
    '  100     1      0:01.00',     // the wrapper (job pid)
    '  101   100     12:30.50',     // the agent CLI: not counted
    '  102   101      0:20.25',     // a test run under the CLI
    '  103   102   1:02:03',        // its child in its own process group
    '  104   101   2-00:00:01',     // days
    '  200     1      9:00.00',     // another process
  ].join('\n');
  const calls = [];
  const cpu = agentJobCpu({ pid: 100 }, { spawnSync: (command, args) => { calls.push([command, ...args]); return { status: 0, stdout: table }; } });
  assert.deepEqual(cpu, { 102: 20.25, 103: 3723, 104: 172801 });
  assert.deepEqual(calls, [['ps', '-A', '-o', 'pid=,ppid=,time=']]);
  assert.equal(agentJobCpu({ pid: 100 }, { spawnSync: () => ({ status: 1, stdout: '' }) }), null);
  assert.equal(agentJobCpu({}, { spawnSync: () => { throw Error('not called'); } }), null);
});

// STOPS-0129 (#3238 A1): the wrapper stops a command that the agent waits on when the log is silent and the command
// makes almost no CPU; the agent sees the command fail and goes on. A helper that was there at the first output stays.
const HUNG_AGENT = `
const { spawn } = require('child_process'), fs = require('fs');
const helper = spawn(process.execPath, ['-e', 'setInterval(() => {}, 1e6)'], { stdio: 'ignore' });
fs.writeFileSync(process.env.HELPER_PID, String(helper.pid));
process.stdout.write('agent started\\n');
setTimeout(() => {
  process.stdout.write(JSON.stringify({ type: 'item.started', item: { type: 'command_execution', command: 'npm install' } }) + '\\n');
  const command = spawn(process.execPath, ['-e', 'setInterval(() => {}, 1e6) /* pdd-hung-npm-install */'], { stdio: ['ignore', 'pipe', 'pipe'] });
  fs.writeFileSync(process.env.COMMAND_PID, String(command.pid));
  command.on('exit', (code, signal) => {
    process.stdout.write('agent saw the command fail: ' + signal + '\\n');
    if (process.env.RESULT) fs.writeFileSync(process.env.RESULT, JSON.stringify({ outcome: 'pr', pr: 7, head: 'a'.repeat(40) }));
    process.exit(0);
  });
}, 600);`;
const alive = pid => { try { process.kill(pid, 0); return true; } catch { return false; } };

test('the hung-command watch stops only the silent command; the agent goes on and a helper stays (STOPS-0129)', async t => {
  const dir = folder(t), helperPid = join(dir, 'helper.pid'), commandPid = join(dir, 'command.pid'), result = join(dir, 'r.json');
  const job = startAgentJob({ id: '30-build-1', dir, cwd: dir, command: process.execPath, args: ['-e', HUNG_AGENT], input: '',
    env: { PATH: process.env.PATH, HELPER_PID: helperPid, COMMAND_PID: commandPid, RESULT: result }, hung: { after: 1500, every: 150, cpu: 0.5 } });
  assert.equal(job.hangs, join(dir, '30-build-1.hangs.json'));
  assert.deepEqual(JSON.parse(readFileSync(job.token, 'utf8')).hung, { after: 1500, every: 150, cpu: 0.5 });
  const helper = Number(await until(() => existsSync(helperPid) && readFileSync(helperPid, 'utf8')));
  t.after(() => { try { process.kill(helper, 'SIGKILL'); } catch {} });
  const command = Number(await until(() => existsSync(commandPid) && readFileSync(commandPid, 'utf8')));
  t.after(() => { try { process.kill(command, 'SIGKILL'); } catch {} });
  await new Promise(r => setTimeout(r, 900));
  assert.ok(alive(command), 'not stopped before the silent time');
  const done = await until(() => { const s = readAgentJob({ ...job, result }); return s.state === 'exited' && s; }, 15000);
  assert.equal(done.exit.code, 0, 'the agent went on and ended by itself');
  assert.deepEqual(done.result, { outcome: 'pr', pr: 7, head: 'a'.repeat(40) });
  const log = readFileSync(job.log, 'utf8');
  assert.match(log, /agent-job: stopped a hung command after [\d.]+ min with no output and almost no CPU: .*pdd-hung-npm-install/);
  assert.match(log, /last output: \{"type":"item\.started"/);
  assert.match(log, /agent saw the command fail: SIGTERM/);
  const hangs = agentJobHangs(job);
  assert.equal(hangs.length, 1, 'one record, the helper is not one');
  assert.equal(hangs[0].pid, command); assert.match(hangs[0].command, /pdd-hung-npm-install/); assert.equal(hangs[0].head, null, 'not a Git folder');
  assert.ok(alive(helper), 'the idle helper of the agent is never stopped');
  assert.ok(hangs[0].minutes >= 0 && Number.isFinite(hangs[0].at));
});

// Lead, Nov 11: a pdd test that waits for Runtime capacity or a maintenance window is silent with almost no CPU, like a
// hang. The watch never stops it, also when the agent's shell runs it as "$PDD_CLI" test.
const WAITING_AGENT = `
const { spawn } = require('child_process'), fs = require('fs');
process.stdout.write('agent started\\n');
setTimeout(() => {
  process.stdout.write(JSON.stringify({ type: 'item.started', item: { type: 'command_execution', command: '"$PDD_CLI" test format-bytes' } }) + '\\n');
  const command = spawn('/bin/sh', ['-c', 'exec "$0" "$1" test format-bytes', process.execPath, process.env.PDD_FAKE], { stdio: ['ignore', 'pipe', 'pipe'] });
  fs.writeFileSync(process.env.COMMAND_PID, String(command.pid));
  command.on('exit', (code, signal) => { process.stdout.write('pdd test ended: ' + signal + '\\n'); process.exit(0); });
}, 600);`;
test('the hung-command watch never stops a pdd test that waits for Runtime (lead, Nov 11)', async t => {
  const dir = folder(t), commandPid = join(dir, 'command.pid'), fake = join(dir, 'bin', 'pdd.mjs');
  mkdirSync(join(dir, 'bin'), { recursive: true }); writeFileSync(fake, 'setInterval(() => {}, 1e6); // waits for Runtime capacity\n');
  const widePs = fakePs(dir, 'case "$LC_ALL:$*" in C:*-ww*) exec /bin/ps "$@" ;; *) /bin/ps "$@" | awk \'{ printf "%s %s %s %s node\\n", $1, $2, $3, $4 }\' ;; esac');
  const job = startAgentJob({ id: '32-build-1', dir, cwd: dir, command: process.execPath, args: ['-e', WAITING_AGENT], input: '',
    env: { PATH: `${widePs}:${process.env.PATH}`, COMMAND_PID: commandPid, PDD_FAKE: fake }, hung: { after: 1200, every: 150, cpu: 0.5 } });
  const command = Number(await until(() => existsSync(commandPid) && readFileSync(commandPid, 'utf8')));
  t.after(() => { try { process.kill(command, 'SIGKILL'); } catch {} try { stopAgentJob(job); } catch {} });
  await new Promise(r => setTimeout(r, 4000));                      // more than 3 times the silent time
  assert.ok(alive(command), 'the waiting pdd test still runs');
  assert.doesNotMatch(readFileSync(job.log, 'utf8'), /stopped a hung command/); assert.deepEqual(agentJobHangs(job), []);
  process.kill(command, 'SIGTERM');
  await until(() => readAgentJob(job).state === 'exited', 15000);
});

test('the hung-command watch rounds (pure): a busy command, a helper and a waiting pdd test stay; a silent command is stopped once (STOPS-0129)', () => {
  const settings = { after: 1200, cpu: 0.3 }, agent = 10, at = 1_000_000, log = { size: 10, mtimeMs: at };
  const row = (pid, ppid, cpu, command, start = at + 100) => ({ pid, ppid, cpu, start, command });
  const memo = {};
  // Round 1 with log content: the helper of the agent is known.
  assert.deepEqual(hungRound(memo, { rows: [row(10, 1, 1, 'codex'), row(11, 10, 0, 'mcp-server', at - 50_000)], log, now: at + 200, agentPid: agent, settings }), []);
  const table = (busyCpu, silentCpu) => [row(10, 1, 1, 'codex'), row(11, 10, 0, 'mcp-server', at - 50_000),
    row(20, 10, busyCpu, 'node build.js'), row(30, 10, silentCpu, 'npm install'), row(40, 10, 0, '/bin/bash -lc "$PDD_CLI" test format-bytes'), row(41, 40, 0, 'node /p/bin/pdd.mjs test format-bytes')];
  // The busy command grows by 0.5 s of CPU each round; the silent one by nothing; time goes on in fixed steps.
  let stopped = [];
  for (let i = 1; i <= 6; i++) stopped.push(...hungRound(memo, { rows: table(0.5 * i, 0.01), log, now: at + 200 + i * 500, agentPid: agent, settings }).map(s => s.row.command));
  assert.deepEqual(stopped, ['npm install'], 'only the silent command, once');
  // A log change starts the silent time again.
  const fresh = {};
  hungRound(fresh, { rows: table(0, 0), log, now: at + 200, agentPid: agent, settings });
  assert.deepEqual(hungRound(fresh, { rows: table(0, 0), log: { size: 20, mtimeMs: at + 1500 }, now: at + 2000, agentPid: agent, settings }), []);
});

test('the hung-command watch: a job without hung and a broken setting have no watch (STOPS-0129)', async t => {
  const dir = folder(t);
  // No hung setting: no watch, no record, and the spec has no hung field.
  const plain = startAgentJob({ id: '32-suite-1', dir, cwd: dir, command: process.execPath, args: ['-e', 'process.exit(0)'], input: '', env: { PATH: process.env.PATH } });
  assert.equal(JSON.parse(readFileSync(plain.token, 'utf8')).hung, undefined);
  assert.equal(JSON.parse(readFileSync(startAgentJob({ id: '33-x', dir, cwd: dir, command: process.execPath, args: ['-e', ''], input: '', env: {}, hung: { after: 'x' } }).token, 'utf8')).hung, undefined, 'a broken setting is no watch');
  await until(() => readAgentJob(plain).state === 'exited');
  // agentJobHangs reads only a list of objects.
  writeFileSync(join(dir, 'h.json'), JSON.stringify([{ at: 1 }, 2, null]));
  assert.deepEqual(agentJobHangs({ hangs: join(dir, 'h.json') }), [{ at: 1 }]);
  writeFileSync(join(dir, 'h.json'), '{bad');
  assert.deepEqual(agentJobHangs({ hangs: join(dir, 'h.json') }), []);
  assert.deepEqual(agentJobHangs({}), []);
});
