import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, writeFileSync, existsSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { agentCommand, jobEnvironment, startAgentJob, readAgentJob, stopAgentJob, agentJobCpu } from '../src/agent-job.mjs';

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

test('agent commands follow the headless auditor launch for codex, claude and agy', () => {
  assert.deepEqual(agentCommand({ kind: 'codex', command: '/bin/codex' }), { command: '/bin/codex',
    args: ['exec', '--json', '--dangerously-bypass-approvals-and-sandbox', '-c', 'features.multi_agent=false', '-'] });
  assert.deepEqual(agentCommand({ kind: 'claude' }, { model: 'opus' }), { command: 'claude',
    args: ['-p', '--output-format', 'stream-json', '--verbose', '--permission-mode', 'bypassPermissions', '--model', 'opus'] });
  assert.deepEqual(agentCommand({ kind: 'agy' }), { command: 'agy',
    args: ['--input-format', 'text', '--output-format', 'stream-json', '--dangerously-skip-permissions'] });
  assert.deepEqual(agentCommand({ kind: 'agy', command: '/opt/bin/agy' }, { model: 'gemini-3.8-flash-medium' }), { command: '/opt/bin/agy',
    args: ['--input-format', 'text', '--output-format', 'stream-json', '--dangerously-skip-permissions', '--model', 'gemini-3.8-flash-medium'] });
  assert.throws(() => agentCommand({ kind: 'gemini' }), /codex, claude or agy/);
});

test('job environment drops caller agent, Herdr and coordinator session markers', () => {
  const env = jobEnvironment({ HOME: '/h', PATH: '/bin', CODEX_HOME: '/c', ANTIGRAVITY_APP_DATA_DIR: '/a',
    ANTIGRAVITY_AGENT: '1', ANTIGRAVITY_CONVERSATION_ID: 'conv', ANTIGRAVITY_CSRF_TOKEN: 'csrf',
    CLAUDECODE: '1', CLAUDE_CODE_ENTRYPOINT: 'x', CODEX_THREAD_ID: 't',
    CODEX_SANDBOX: 'seatbelt', HERDR_PANE: 'p', PDD_AGENT_SESSION: 's', PDD_AUTOPILOT_CONTEXT: '{}', GH_TOKEN: 'keep' });
  assert.deepEqual(env, { HOME: '/h', PATH: '/bin', CODEX_HOME: '/c', ANTIGRAVITY_APP_DATA_DIR: '/a', GH_TOKEN: 'keep' });
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
