import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, writeFileSync, existsSync, rmSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { agentCommand, jobEnvironment, startAgentJob, readAgentJob, stopAgentJob, agentJobCpu, agentJobHangs } from '../src/agent-job.mjs';

const folder = t => { const dir = mkdtempSync(join(tmpdir(), 'pdd-agent-job-')); t.after(() => rmSync(dir, { recursive: true, force: true })); return dir; };
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
  // Claude round 5 SF: the wrapper writes the exit record just before the group SIGKILL, after the 2 s grace time.
  const after = done.exit.at - stoppedAt;
  assert.ok(after >= 1500 && after < 6000, `the SIGKILL came ${after} ms after the stop`);
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

test('the hung-command watch leaves a busy command, a job without hung and a plain command alone (STOPS-0129)', async t => {
  const dir = folder(t), mark = join(dir, 'busy.done');
  // A command with CPU growth runs past the silent time and ends by itself.
  const busy = `const { spawnSync } = require('child_process');
process.stdout.write('agent started\\n');
setTimeout(() => { process.stdout.write('{"type":"item.started"}\\n');
  const r = spawnSync(process.execPath, ['-e', 'const end = Date.now() + 2500; while (Date.now() < end) {}'], { stdio: 'ignore' });
  require('fs').writeFileSync(${JSON.stringify(mark)}, String(r.status)); process.exit(0); }, 400);`;
  const job = startAgentJob({ id: '31-build-1', dir, cwd: dir, command: process.execPath, args: ['-e', busy], input: '', env: { PATH: process.env.PATH }, hung: { after: 1200, every: 150, cpu: 0.3 } });
  const done = await until(() => { const s = readAgentJob(job); return s.state === 'exited' && s; }, 15000);
  assert.equal(done.exit.code, 0); assert.equal(readFileSync(mark, 'utf8'), '0', 'the busy command ended by itself');
  assert.doesNotMatch(readFileSync(job.log, 'utf8'), /stopped a hung command/); assert.deepEqual(agentJobHangs(job), []);
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
