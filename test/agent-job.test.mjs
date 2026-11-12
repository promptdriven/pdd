import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, writeFileSync, existsSync, rmSync, mkdirSync, chmodSync, realpathSync } from 'node:fs';
import { spawn, spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { agentCommand, jobEnvironment, startAgentJob, readAgentJob, stopAgentJob, snapshotAgentJob, cleanupAgentJob, agentJobCpu, agentJobHangs, jobStopper, hungRound } from '../src/agent-job.mjs';

const folderAt = (t, prefix) => { const dir = mkdtempSync(prefix); t.after(() => rmSync(dir, { recursive: true, force: true })); return dir; };
const folder = t => folderAt(t, join(tmpdir(), 'pdd-agent-job-'));
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

test('snapshotAgentJob retains a separate-group helper while its wrapper is live', () => {
  const job = { pid: 100, token: '/state/one.spec.json' };
  const table = [
    '100 1 100 1 Mon Nov 11 10:00:00 2026 node wrapper /state/one.spec.json',
    '101 100 101 1 Mon Nov 11 10:00:01 2026 node mcp /worktree',
    '102 101 101 1 Mon Nov 11 10:00:02 2026 node helper /worktree',
    '200 1 200 1 Mon Nov 11 10:00:03 2026 node other'
  ].join('\n');
  assert.deepEqual(snapshotAgentJob(job, { spawnSync: () => ({ status: 0, stdout: table }) }).map(row => row.pid), [100, 101, 102]);
});

test('cleanup snapshots a live legacy wrapper before stopping its separate-group helper', async t => {
  const dir = folder(t), token = join(dir, 'live-legacy.spec.json'), exit = join(dir, 'live-legacy.exit.json');
  writeFileSync(token, JSON.stringify({ command: 'node', args: [], cwd: dir, log: join(dir, 'live.log'), exit }));
  const caller = { pid: process.pid, ppid: 1, pgid: process.pid, rss: 1, start: '@caller', args: 'node test caller' };
  const wrapper = { pid: 70011, ppid: 1, pgid: 70011, rss: 1, start: '@live-wrapper', args: `node --wrapper ${token}` };
  const agent = { pid: 70012, ppid: wrapper.pid, pgid: wrapper.pid, rss: 1, start: '@live-agent', args: 'node agent' };
  const helper = { pid: 70013, ppid: agent.pid, pgid: 70013, rss: 1, start: '@separate-helper', args: 'node mcp helper' };
  let rows = [caller, wrapper, agent, helper];
  const table = () => rows.map(row => `${row.pid} ${row.ppid} ${row.pgid} ${row.rss} ${row.start} ${row.args}`).join('\n');
  const signals = [], job = { pid: wrapper.pid, token, exit, log: join(dir, 'live.log') };
  const proof = await cleanupAgentJob(job, { alive: () => true, spawnSync: () => ({ status: 0, stdout: table() }), list: () => rows,
    kill: (pid, signal) => {
      signals.push([pid, signal]);
      if (pid === -wrapper.pid) rows = [caller, helper];
      else if (pid === helper.pid && signal === 'SIGTERM') rows = [caller];
    }, sleep: async () => {}, grace: 1, poll: 1 });
  assert.equal(proof.confirmed, true);
  assert.ok(JSON.parse(readFileSync(`${token}.processes.json`, 'utf8')).some(row => row.pid === helper.pid));
  assert.deepEqual(signals, [[-wrapper.pid, 'SIGTERM'], [helper.pid, 'SIGTERM']]);
  await t.test('an incomplete fresh snapshot leaves the live wrapper untouched', async t => {
    const missingDir = folder(t), missingToken = join(missingDir, 'missing-wrapper.spec.json'), missingExit = join(missingDir, 'missing-wrapper.exit.json');
    writeFileSync(missingToken, JSON.stringify({ command: 'node', args: [], cwd: missingDir, log: join(missingDir, 'missing.log'), exit: missingExit }));
    const stale = { pid: 70021, ppid: 1, pgid: 70021, rss: 1, start: '@stale-wrapper', args: `node --wrapper ${missingToken}` };
    writeFileSync(`${missingToken}.processes.json`, JSON.stringify([stale]));
    const onlyCaller = { pid: process.pid, ppid: 1, pgid: process.pid, rss: 1, start: '@caller', args: 'node test caller' };
    const text = `${onlyCaller.pid} ${onlyCaller.ppid} ${onlyCaller.pgid} ${onlyCaller.rss} ${onlyCaller.start} ${onlyCaller.args}`;
    const missingSignals = [], result = await cleanupAgentJob({ pid: stale.pid, token: missingToken }, {
      alive: () => true, spawnSync: () => ({ status: 0, stdout: text }), list: () => [onlyCaller],
      kill: (...args) => missingSignals.push(args) });
    assert.equal(result.confirmed, false);
    assert.deepEqual(missingSignals, []);
    assert.equal(existsSync(`${missingToken}.processes.error`), false);
    assert.equal(JSON.parse(readFileSync(`${missingToken}.processes.cleanup-snapshot.json`, 'utf8')).resolutions.length, 0);
  });
});

test('a vanished wrapper keeps a valid saved manifest; missing or invalid manifests stay uncertain', t => {
  const dir = folder(t), token = join(dir, 'exit.spec.json'), row = { pid: 501, ppid: 1, pgid: 501, rss: 1, start: 'Mon Nov 11 10:00:00 2026', args: 'node wrapper exit.spec.json' };
  writeFileSync(`${token}.processes.json`, JSON.stringify([row]));
  const job = { pid: 501, token };
  assert.deepEqual(snapshotAgentJob(job, { list: () => [] }), [row]);
  assert.equal(job.processesUncertain, undefined);
  assert.equal(existsSync(`${token}.processes.error`), false);

  const missing = join(dir, 'missing.spec.json');
  assert.equal(snapshotAgentJob({ pid: 502, token: missing }, { list: () => [] }), null);
  assert.ok(existsSync(`${missing}.processes.error`));

  const invalid = join(dir, 'invalid.spec.json');
  writeFileSync(`${invalid}.processes.json`, '{broken');
  assert.equal(snapshotAgentJob({ pid: 503, token: invalid }, { list: () => [] }), null);
  assert.ok(existsSync(`${invalid}.processes.error`));
});

test('an active 0.1.28 wrapper can be snapshotted after upgrade, but an exited one needs a core-validated legacy scan', async t => {
  const dir = folder(t), token = join(dir, 'legacy.spec.json'), caller = { pid: process.pid, ppid: 1, pgid: process.pid, rss: 1, start: '@caller', args: 'node test' };
  writeFileSync(token, JSON.stringify({ command: 'node', args: [], cwd: dir, input: join(dir, 'legacy.input'), log: join(dir, 'legacy.log'), exit: join(dir, 'legacy.exit.json') }));
  let live = true;
  const wrapper = { pid: 7001, ppid: 1, pgid: 7001, rss: 1, start: '@legacy-wrapper', args: `node wrapper ${token}` };
  const child = { pid: 7002, ppid: 7001, pgid: 7002, rss: 1, start: '@legacy-child', args: 'node legacy agent' };
  const rows = () => live ? [caller, wrapper, child] : [caller], job = { pid: wrapper.pid, token, log: join(dir, 'legacy.log'), exit: join(dir, 'legacy.exit.json'), result: join(dir, 'legacy.result.json') };
  const saved = snapshotAgentJob(job, { list: rows });
  assert.deepEqual(saved.map(row => row.pid), [7001, 7002]);
  assert.equal(JSON.parse(readFileSync(token, 'utf8')).custodyRoot, undefined, 'the old spec is not upgraded by guessing a root');
  const signals = [], proof = await cleanupAgentJob(job, { alive: () => false, list: rows, kill: (pid, signal) => { signals.push([pid, signal]); if (signal === 'SIGTERM') live = false; }, sleep: async () => {}, grace: 1, poll: 1 });
  assert.equal(proof.confirmed, true, 'the post-upgrade snapshot supplies stable identities for the live old wrapper');
  assert.deepEqual(signals.map(([pid]) => pid).sort(), [7001, 7002]);

  const missing = join(dir, 'legacy-exited.spec.json');
  writeFileSync(missing, JSON.stringify({ command: 'node', args: [], cwd: dir }));
  const noSnapshot = await cleanupAgentJob({ pid: 7003, token: missing }, { alive: () => false, list: () => [caller], kill: () => assert.fail('a missing legacy manifest supplies no signal identity') });
  assert.equal(noSnapshot.confirmed, false, 'an exited old wrapper with no manifest stays unconfirmed');
});

test('cleanup accepts a valid saved manifest after its wrapper exited, but rejects a corrupt or malformed manifest', async t => {
  const dir = folder(t), token = join(dir, 'job.spec.json'), row = { pid: 501, ppid: 1, pgid: 501, rss: 1, start: 'Mon Nov 11 10:00:00 2026', args: 'node wrapper job.spec.json' };
  writeFileSync(`${token}.processes.json`, JSON.stringify([row]));
  const gone = await cleanupAgentJob({ pid: 501, token }, { alive: () => false, list: () => [], kill: () => assert.fail('no signal') });
  assert.equal(gone.confirmed, true);
  writeFileSync(`${token}.processes.json`, '{broken');
  const corrupt = await cleanupAgentJob({ pid: 501, token, processes: [row] }, { alive: () => false, list: () => [] });
  assert.equal(corrupt.confirmed, false); assert.ok(existsSync(`${token}.processes.error`));
  for (const manifest of ['[]', '[{}]', JSON.stringify([{ ...row, start: '   ' }]), JSON.stringify([{ ...row, args: '   ' }]), JSON.stringify([{ ...row, start: 'not a process start' }])]) {
    writeFileSync(`${token}.processes.json`, manifest);
    assert.equal((await cleanupAgentJob({ pid: 501, token, processes: [row] }, { alive: () => false, list: () => [] })).confirmed, false);
  }
  rmSync(`${token}.processes.json`);
  assert.equal((await cleanupAgentJob({ pid: 501, token, processes: [{}] }, { alive: () => false, list: () => [] })).confirmed, false);
});

test('a snapshot failure stays uncertain after a later valid process inventory', async t => {
  const dir = folder(t), token = join(dir, 'job.spec.json'), job = { pid: 501, token };
  const row = { pid: 501, ppid: 1, pgid: 501, rss: 1, start: 'Mon Nov 11 10:00:00 2026', args: `node wrapper ${token}` };
  assert.equal(snapshotAgentJob(job, { list: () => null }), null);
  assert.deepEqual(snapshotAgentJob(job, { list: () => [row] }).map(part => part.pid), [501]);
  assert.equal(job.processesUncertain, true);
  assert.equal((await cleanupAgentJob(job, { alive: () => false, list: () => [] })).confirmed, false);
});

test('a failed cleanup snapshot can retry only with the same live wrapper identity', async t => {
  const dir = folder(t), token = join(dir, 'retry-cleanup.spec.json'), signals = [];
  const job = { pid: 70031, token }, wrapper = custodyRow(job.pid, '@cleanup-wrapper', `node --wrapper ${token}`);
  const agent = custodyRow(70032, '@cleanup-agent', 'node agent', process.getuid()); agent.ppid = wrapper.pid;
  const savedManifest = [wrapper, agent];
  writeFileSync(`${token}.processes.json`, JSON.stringify(savedManifest));
  let rows = null;
  const ports = { alive: () => true, list: () => rows, kill: (pid, signal) => {
    signals.push([pid, signal]);
    if (pid === -job.pid && signal === 'SIGTERM') rows = [agent];
    else if (pid === agent.pid && signal === 'SIGTERM') rows = [];
  }, sleep: async () => {}, grace: 1, poll: 1 };

  const first = await cleanupAgentJob(job, ports);
  assert.equal(first.confirmed, false);
  assert.equal(existsSync(`${token}.processes.error`), false, 'a cleanup-only snapshot failure does not become a permanent sample error');
  assert.deepEqual(signals, []);
  assert.deepEqual(JSON.parse(readFileSync(`${token}.processes.json`, 'utf8')), savedManifest,
    'the saved process identities survive an incomplete cleanup capture');
  const failed = JSON.parse(readFileSync(`${token}.processes.cleanup-snapshot.json`, 'utf8'));
  assert.equal(failed.attempts.length, 1);
  assert.equal(failed.resolutions.length, 0);
  assert.equal(failed.attempts[0].wrapper.pid, wrapper.pid);
  assert.equal(failed.attempts[0].wrapper.start, wrapper.start);

  rows = [wrapper, agent];
  const proof = await cleanupAgentJob(job, ports);
  assert.equal(proof.confirmed, true);
  assert.deepEqual(signals, [[-job.pid, 'SIGTERM'], [agent.pid, 'SIGTERM']]);
  assert.deepEqual(JSON.parse(readFileSync(`${token}.processes.json`, 'utf8')), savedManifest,
    'the valid retry confirms the same saved process identities before cleanup');
  const recovered = JSON.parse(readFileSync(`${token}.processes.cleanup-snapshot.json`, 'utf8'));
  assert.equal(recovered.attempts.length, 1, 'the failed attempt stays in the record');
  assert.equal(recovered.resolutions.length, 1);
  assert.equal(recovered.resolutions[0].attempt, 1);
});

test('cleanup keeps an incomplete snapshot pending after the wrapper exits or its PID is reused', async t => {
  await t.test('the wrapper exits before a complete retry', async t => {
    const dir = folder(t), token = join(dir, 'retry-exit.spec.json'), signals = [];
    const job = { pid: 70041, token }, ports = { alive: () => true, list: () => null, kill: (...args) => signals.push(args) };
    assert.equal((await cleanupAgentJob(job, ports)).confirmed, false);
    const proof = await cleanupAgentJob(job, { ...ports, alive: () => false });
    assert.equal(proof.confirmed, false);
    assert.deepEqual(signals, []);
    assert.equal(JSON.parse(readFileSync(`${token}.processes.cleanup-snapshot.json`, 'utf8')).resolutions.length, 0);
  });

  await t.test('the same PID now names a different wrapper identity', async t => {
    const dir = folder(t), token = join(dir, 'retry-reuse.spec.json'), signals = [];
    const job = { pid: 70051, token }, original = custodyRow(job.pid, '@original-wrapper', `node --wrapper ${token}`);
    const invalidChild = custodyRow(70052, '@bad-child', '   '); invalidChild.ppid = original.pid;
    const replacement = custodyRow(job.pid, '@replacement-wrapper', `node --wrapper ${token}`);
    const child = custodyRow(70053, '@replacement-agent', 'node agent'); child.ppid = replacement.pid;
    let rows = [original, invalidChild];
    const ports = { alive: () => true, list: () => rows, kill: (...args) => signals.push(args) };
    assert.equal((await cleanupAgentJob(job, ports)).confirmed, false);
    assert.equal(existsSync(`${token}.processes.error`), false);
    rows = [replacement, child];
    assert.equal((await cleanupAgentJob(job, ports)).confirmed, false);
    assert.deepEqual(signals, []);
    const retry = JSON.parse(readFileSync(`${token}.processes.cleanup-snapshot.json`, 'utf8'));
    assert.equal(retry.resolutions.length, 0);
    assert.equal(retry.attempts[0].wrapper.start, original.start);
  });
});

test('a captured descendant without an identity makes the snapshot uncertain', async t => {
  const dir = folder(t), token = join(dir, 'job.spec.json'), job = { pid: 501, token };
  const root = { pid: 501, ppid: 1, pgid: 501, rss: 1, start: 'Mon Nov 11 10:00:00 2026', args: `node wrapper ${token}` };
  const missingCommand = { pid: 502, ppid: 501, pgid: 501, rss: 1, start: 'Mon Nov 11 10:00:01 2026', args: '   ' };
  assert.equal(snapshotAgentJob(job, { list: () => [root, missingCommand] }), null);
  assert.equal((await cleanupAgentJob(job, { alive: () => false, list: () => [] })).confirmed, false);
});

const DETACHED_HELPER = `
const { spawn } = require('child_process'), fs = require('fs');
const helper = spawn(process.execPath, ['-e', 'setInterval(() => {}, 1000)'], { detached: true, stdio: 'ignore' });
helper.unref(); fs.writeFileSync(process.env.HELPER_PID, String(helper.pid));
const published = () => { try { return JSON.parse(fs.readFileSync(process.env.MANIFEST, 'utf8')).some(row => row.pid === helper.pid); } catch { return false; } };
const wait = setInterval(() => { if (published()) { clearInterval(wait); process.exit(0); } }, 10);
setTimeout(() => { clearInterval(wait); process.exit(42); }, 5000);`;
test('the wrapper saves a detached helper before its direct agent exits with a manifest handshake', async t => {
  const dir = folder(t), mark = join(dir, 'helper.pid');
  const job = startAgentJob({ id: 'detached-helper', dir, cwd: dir, command: process.execPath, args: ['-e', DETACHED_HELPER], input: '', env: { PATH: process.env.PATH, HELPER_PID: mark, MANIFEST: join(dir, 'detached-helper.spec.json.processes.json') } });
  const helper = Number(await until(() => existsSync(mark) && readFileSync(mark, 'utf8')));
  t.after(() => { try { process.kill(helper, 'SIGKILL'); } catch {} });
  await until(() => existsSync(job.exit));
  const saved = JSON.parse(readFileSync(`${job.token}.processes.json`, 'utf8'));
  assert.ok(saved.some(row => row.pid === helper), 'the helper survives its direct parent and stays in the manifest');
});

const LATE_DETACHED_HELPER = `
const { spawn } = require('child_process'), fs = require('fs');
setTimeout(() => {
  const helper = spawn(process.execPath, ['-e', 'setInterval(() => {}, 1000)'], { detached: true, stdio: 'ignore' });
  helper.unref(); fs.writeFileSync(process.env.HELPER_PID, String(helper.pid)); process.exit(0);
}, 80);`;
test('a late unsampled detached helper retains a /tmp worktree without a cwd-based signal', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const dir = folderAt(t, '/tmp/pdd-agent-job-late-'), mark = join(dir, 'late-helper.pid');
  const job = startAgentJob({ id: 'late-detached-helper', dir, cwd: dir, custodyRoot: dir, command: process.execPath, args: ['-e', LATE_DETACHED_HELPER], input: '', env: { PATH: process.env.PATH, HELPER_PID: mark } });
  assert.equal(JSON.parse(readFileSync(job.token, 'utf8')).custodyRoot, dir);
  const helper = Number(await until(() => existsSync(mark) && readFileSync(mark, 'utf8')));
  t.after(() => { try { process.kill(helper, 'SIGKILL'); } catch {} });
  await until(() => existsSync(job.exit));
  assert.ok(existsSync(`${job.token}.processes.custody.json`), 'late custody evidence must retain the job');
  assert.equal(existsSync(`${job.token}.processes.error`), false, 'a complete custody finding is distinct from an incomplete manifest');
  await until(() => !alive(job.pid));
  const signals = [], proof = await cleanupAgentJob(job, { kill: (...args) => signals.push(args) });
  assert.equal(proof.confirmed, false);
  assert.deepEqual(signals, [], 'cwd evidence never authorizes a signal');
  assert.ok(alive(helper), 'the unknown helper stays untouched until evidence shows it ended');
  const first = JSON.parse(readFileSync(`${job.token}.processes.custody.json`, 'utf8'));
  assert.equal(first.resolution, null);
  assert.ok(first.observations.some(row => row.identities.some(identity => identity.pid === helper)));
  try { process.kill(helper, 'SIGKILL'); } catch {}
  await until(() => ended(helper));
  const recovered = await cleanupAgentJob(job);
  assert.equal(recovered.confirmed, true, 'a fresh complete inventory can resolve an exited suspect');
  const history = JSON.parse(readFileSync(`${job.token}.processes.custody.json`, 'utf8'));
  assert.ok(history.observations.length >= first.observations.length, 'resolution keeps the original finding');
  assert.equal(history.resolution.recordedIdentitiesGone, true);
});

test('an unrecorded helper with a deleted worktree cwd stays held without a signal', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const dir = folderAt(t, '/tmp/pdd-agent-job-deleted-');
  const job = startAgentJob({ id: 'deleted-cwd', dir, cwd: dir, custodyRoot: dir,
    command: process.execPath, args: ['-e', 'process.exit(0)'], input: '', env: { PATH: process.env.PATH } });
  await until(() => existsSync(job.exit) && !alive(job.pid));

  const nested = join(dir, 'deleted-cwd'); mkdirSync(nested);
  const helper = spawn(process.execPath, ['-e', 'setInterval(() => {}, 1000)'], { cwd: nested, detached: true, stdio: 'ignore' });
  helper.unref();
  t.after(() => { try { process.kill(helper.pid, 'SIGKILL'); } catch {} });
  await until(() => alive(helper.pid));
  assert.equal(JSON.parse(readFileSync(`${job.token}.processes.json`, 'utf8')).some(row => row.pid === helper.pid), false,
    'the helper starts after the wrapper has finished and is absent from its manifest');
  rmSync(nested, { recursive: true, force: true });
  assert.equal(existsSync(nested), false);

  const held = await cleanupAgentJob(job);
  assert.equal(held.confirmed, false);
  assert.ok(alive(helper.pid), 'cwd evidence retains the job but does not signal this unrecorded helper');
  const retained = JSON.parse(readFileSync(`${job.token}.processes.custody.json`, 'utf8'));
  assert.ok(retained.observations.at(-1).identities.some(row => row.pid === helper.pid));

  try { process.kill(helper.pid, 'SIGKILL'); } catch {}
  await until(() => ended(helper.pid));
  assert.equal((await cleanupAgentJob(job)).confirmed, true, 'a complete scan resolves the exited suspect and keeps its history');
});

test('a clean exited job keeps cleanup confirmation with a complete readable inventory', async t => {
  const dir = folder(t), root = join(dir, 'owned-worktree'), token = join(dir, 'clean-exit.spec.json');
  mkdirSync(root);
  const exit = join(dir, 'clean-exit.exit.json'), boundary = Date.now() - 1000;
  const wrapper = custodyRow(900080, '@wrapper', 'node clean exit wrapper');
  const job = { pid: wrapper.pid, token, exit, custodyBoundary: boundary };
  writeFileSync(token, JSON.stringify({ command: 'node', args: [], cwd: root, log: join(dir, 'job.log'),
    exit, custodyRoot: root, custodyBoundary: boundary }));
  writeFileSync(exit, JSON.stringify({ code: 0, signal: null, at: Date.now() }));
  writeFileSync(token + '.processes.json', JSON.stringify([wrapper]));
  assert.equal(readAgentJob(job, { alive: () => false }).state, 'exited');

  // The complete injected table has only the caller, whose cwd is readable outside the root.
  const rows = [cleanCallerRow()], signals = [];
  const result = await cleanupAgentJob(job, { alive: () => false, list: () => rows,
    cwd: () => process.cwd(), kill: (...args) => signals.push(args) });
  if (result.confirmed !== true) {
    let custody = null;
    try { custody = JSON.parse(readFileSync(token + '.processes.custody.json', 'utf8')); } catch {}
    const latest = Array.isArray(custody?.observations) ? custody.observations.at(-1) : null;
    assert.fail(JSON.stringify({
      cleanup: { confirmed: result.confirmed === true, stopped: result.stopped, killed: result.killed, remaining: result.remaining },
      savedBoundary: boundary,
      latestCustody: latest ? { reason: latest.reason, identities: Array.isArray(latest.identities)
        ? latest.identities.map(row => ({ pid: row.pid, start: row.start })) : [] } : null,
    }));
  }
  assert.equal(result.confirmed, true);
  assert.deepEqual(signals, [], 'a completed job has no process to signal');
});

test('a cwd-read failure keeps only a same-identity live process in custody', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const lstart = at => {
    const date = new Date(at), days = ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'], months = ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'];
    const two = value => String(value).padStart(2, '0');
    return `${days[date.getDay()]} ${months[date.getMonth()]} ${String(date.getDate()).padStart(2, ' ')} ${two(date.getHours())}:${two(date.getMinutes())}:${two(date.getSeconds())} ${date.getFullYear()}`;
  };
  const run = async (name, nextState, expected, olderSession = false) => t.test(name, async t => {
    const dir = folder(t), token = join(dir, 'cwd-recheck.spec.json'), boundary = Date.now();
    const wrapper = custodyRow(70061, '@wrapper', `node --wrapper ${token}`);
    const suspect = custodyRow(70062, lstart(boundary), 'node candidate');
    const session = olderSession ? { id: 70070, start: lstart(boundary - 60_000) } : null;
    const caller = custodyRow(process.pid, '@caller', 'node test caller');
    writeFileSync(token, JSON.stringify({ command: 'node', args: [], cwd: dir, log: join(dir, 'job.log'),
      exit: join(dir, 'job.exit.json'), custodyRoot: dir, custodyBoundary: boundary }));
    writeFileSync(`${token}.processes.json`, JSON.stringify([wrapper]));
    let rows = [caller, suspect]; const signals = [];
    const ports = { alive: () => false, list: () => rows,
      cwd: pid => {
        if (pid === suspect.pid) {
          if (nextState === 'Z') rows = [caller, { ...suspect, state: 'Z' }];
          const error = Error('synthetic cwd read failure'); error.code = 'EACCES'; throw error;
        }
        return '/outside/core-worktree';
      }, spawnSync: (_command, args) => {
        if (!session) return { status: 1, stdout: '' };
        const selected = Number(args[args.indexOf('-p') + 1]);
        if (selected === suspect.pid) return { status: 0, stdout: `${suspect.pid} ${session.id} ${suspect.uid} S ${suspect.start}\n` };
        if (selected === session.id) return { status: 0, stdout: `${session.id} ${session.id} 0 Ss ${session.start}\n` };
        return { status: 1, stdout: '' };
      }, kill: (...args) => signals.push(args) };
    const result = await cleanupAgentJob({ pid: wrapper.pid, token }, ports);
    assert.equal(result.confirmed, expected);
    assert.deepEqual(signals, []);
    if (expected) {
      assert.equal(existsSync(`${token}.processes.custody.json`), false);
      assert.equal(existsSync(`${token}.processes.error`), false);
    } else {
      const record = JSON.parse(readFileSync(`${token}.processes.custody.json`, 'utf8'));
      assert.ok(record.observations.at(-1).identities.some(row => row.pid === suspect.pid && row.start === suspect.start));
    }
  });
  await run('a process rechecked as a zombie no longer holds cleanup', 'Z', true);
  await run('the same identity rechecked as live still holds cleanup', 'S', false);
  // The older-session exclusion is Linux-only; Darwin has no such proof.
  if (process.platform === 'linux') {
    await run('a live candidate in a provably older Linux session does not hold cleanup', 'S', true, true);
  } else {
    await run('an unreadable candidate stays held without Linux session proof', 'S', false, true);
  }
});

test('a persistent source cwd is not custody without an explicit disposable root', async t => {
  const dir = folder(t);
  const job = startAgentJob({ id: 'source-cwd', dir, cwd: process.cwd(), command: process.execPath, args: ['-e', 'process.exit(0)'], input: '', env: { PATH: process.env.PATH } });
  await until(() => existsSync(job.exit));
  assert.equal(JSON.parse(readFileSync(job.token, 'utf8')).custodyRoot, undefined);
  assert.equal(existsSync(`${job.token}.processes.error`), false);
  assert.equal((await cleanupAgentJob(job)).confirmed, true);
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
const ended = pid => {
  try { process.kill(pid, 0); } catch { return true; }
  const row = spawnSync('ps', ['-o', 'stat=', '-p', String(pid)], { encoding: 'utf8' });
  return row.status !== 0 || /^\s*Z/.test(row.stdout);
};

const custodyRow = (pid, start, args, uid = process.getuid()) => ({ pid, ppid: 1, pgid: pid, rss: 1, uid, state: 'S', start, args });
function custodyFixture(t, suspect, boundary = null) {
  const dir = folder(t), token = join(dir, 'owned.spec.json'), captured = custodyRow(900001, '@ended', 'ended saved agent');
  writeFileSync(token, JSON.stringify({ custodyRoot: dir, ...(boundary === null ? {} : { custodyBoundary: boundary }) }));
  writeFileSync(`${token}.processes.json`, JSON.stringify([captured]));
  writeFileSync(`${token}.processes.custody.json`, JSON.stringify({ schema: 1, root: realpathSync(dir),
    observations: [{ at: 1, reason: 'unsaved process uses worktree', identities: [suspect] }], resolution: null }));
  return { dir, token, job: { pid: 900002, token } };
}
const cleanCallerRow = () => custodyRow(process.pid, '@caller', 'node cleanup caller');

function legacyFixture(t, rootName = '17-review') {
  const dir = folder(t), root = join(dir, rootName), token = join(dir, '17-review-job.spec.json'), exit = join(dir, '17-review-job.exit.json');
  mkdirSync(root, { recursive: true });
  writeFileSync(token, JSON.stringify({ command: 'node', args: [], cwd: root, input: join(dir, 'job.input'), log: join(dir, '17-review-job.log'), exit }));
  writeFileSync(exit, JSON.stringify({ code: 0, signal: null, at: Date.now() }));
  return { dir, root, token, job: { id: '17-review-job', role: 'review', issue: 17, pid: 900006, token, exit, log: join(dir, '17-review-job.log') } };
}

test('a legacy core job can finish only after a complete checkout and old-group scan, with its limit returned', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const f = legacyFixture(t), rows = [cleanCallerRow()], signals = [];
  const proof = await cleanupAgentJob(f.job, { legacyCustodyRoot: f.root, list: () => rows, cwd: () => '/outside/core-worktree', kill: (...args) => signals.push(args) });
  assert.equal(proof.confirmed, true);
  assert.ok(proof.legacy?.trim(), 'the bounded legacy limitation is reported');
  assert.deepEqual(signals, [], 'legacy clearance never signals a process');
});

test('a legacy process-group member stays held by identity after leaving the checkout, then resolves after exit', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const f = legacyFixture(t), suspect = custodyRow(900007, '@legacy-helper', 'node legacy helper'), signals = [];
  suspect.pgid = f.job.pid;
  let rows = [cleanCallerRow(), suspect];
  const ports = { legacyCustodyRoot: f.root, list: () => rows, cwd: () => '/outside/core-worktree', kill: (...args) => signals.push(args) };
  const held = await cleanupAgentJob(f.job, ports);
  assert.equal(held.confirmed, false);
  const first = JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8'));
  assert.equal(first.legacy, true);
  assert.ok(first.observations.some(row => row.identities.some(identity => identity.pid === suspect.pid)));
  suspect.pgid = 1;
  rows = [cleanCallerRow(), suspect];
  assert.equal((await cleanupAgentJob(f.job, ports)).confirmed, false, 'a recorded live helper stays held outside the root and group');
  rows = [cleanCallerRow()];
  const recovered = await cleanupAgentJob(f.job, ports);
  assert.equal(recovered.confirmed, true);
  assert.equal(JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8')).resolution.manifestConfirmed, false);
  assert.deepEqual(signals, [], 'the legacy process is never signalled');
});

test('legacy cleanup reopens a resolved record when a new process enters the checkout', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const f = legacyFixture(t), first = custodyRow(900009, '@legacy-first', 'node first helper');
  let late = null, rows = [cleanCallerRow(), first];
  const ports = { legacyCustodyRoot: f.root, list: () => rows,
    cwd: pid => pid === first.pid || pid === late?.pid ? f.root : '/outside/core-worktree',
    kill: () => assert.fail('legacy cleanup never signals a process') };
  assert.equal((await cleanupAgentJob(f.job, ports)).confirmed, false, 'the first in-root helper is retained');
  rows = [cleanCallerRow()];
  assert.equal((await cleanupAgentJob(f.job, ports)).confirmed, true, 'a complete later scan resolves the exited helper');
  const resolved = JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8'));
  assert.ok(resolved.resolution);

  late = custodyRow(900010, 'Wed Nov 11 10:01:00 2026', 'node late helper');
  rows = [cleanCallerRow(), late];
  assert.equal((await cleanupAgentJob(f.job, ports)).confirmed, false, 'a later process must invalidate the old resolution');
  const reopened = JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8'));
  assert.equal(reopened.resolution, null);
  assert.ok(reopened.observations.at(-1).identities.some(identity => identity.pid === late.pid));
});

test('an incomplete legacy process table remains retryable and a current wrapper blocks clearance', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const f = legacyFixture(t), caller = cleanCallerRow();
  let rows = [];
  const ports = { legacyCustodyRoot: f.root, list: () => rows, cwd: () => '/outside/core-worktree', kill: () => assert.fail('legacy scan never signals') };
  assert.equal((await cleanupAgentJob(f.job, ports)).confirmed, false, 'a table without this reader is incomplete');
  rows = [caller, custodyRow(f.job.pid, '@live-wrapper', `node src/agent-job.mjs --wrapper ${f.token}`)];
  assert.equal((await cleanupAgentJob(f.job, ports)).confirmed, false, 'an exact live wrapper identity cannot be finalized');
  rows = [caller];
  assert.equal((await cleanupAgentJob(f.job, ports)).confirmed, true, 'a later complete scan can finish the old job');
});

test('custody resolution keeps a live suspect held after it moves outside the root', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const suspect = custodyRow(900003, '@old-suspect', 'node detached helper'), f = custodyFixture(t, suspect), rows = [cleanCallerRow(), suspect];
  const signals = [], proof = await cleanupAgentJob(f.job, { alive: () => false, list: () => rows,
    cwd: pid => pid === suspect.pid ? '/outside/worktree' : process.cwd(), kill: (...args) => signals.push(args) });
  assert.equal(proof.confirmed, false, 'the same pid/start identity remains held outside the scanned root');
  assert.deepEqual(signals, [], 'checking a suspect identity never signals it');
  const record = JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8'));
  assert.equal(record.resolution, null);
  assert.ok(record.observations.length > 1, 'the latest held identity is retained as history');
});

test('custody resolution treats a different start identity as pid reuse', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const suspect = custodyRow(900004, '@old-suspect', 'node detached helper'), reused = custodyRow(suspect.pid, '@reused-pid', 'node unrelated');
  const f = custodyFixture(t, suspect), rows = [cleanCallerRow(), reused];
  const proof = await cleanupAgentJob(f.job, { alive: () => false, list: () => rows,
    cwd: pid => pid === reused.pid ? '/outside/worktree' : process.cwd(), kill: () => assert.fail('no process is eligible for a signal') });
  assert.equal(proof.confirmed, true);
  const record = JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8'));
  assert.equal(record.resolution.recordedIdentitiesGone, true);
});

test('an incomplete custody process table keeps uncertainty until a complete retry', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const suspect = custodyRow(900005, '@suspect', 'node detached helper'), f = custodyFixture(t, suspect), caller = cleanCallerRow();
  let reads = 0;
  const ports = { alive: () => false, list: () => ++reads === 2 ? [] : [caller], cwd: () => process.cwd(), kill: () => assert.fail('no process is eligible for a signal') };
  const first = await cleanupAgentJob(f.job, ports);
  assert.equal(first.confirmed, false, 'a table without the current caller is incomplete');
  assert.equal(JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8')).resolution, null);
  const second = await cleanupAgentJob(f.job, ports);
  assert.equal(second.confirmed, true, 'a later complete table can resolve the exited identity');
  assert.equal(JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8')).resolution.completeProcessTable, true);
});

const CUSTODY_BOUNDARY = Date.parse('2026-11-11T10:00:00Z') + 750;
const oldStart = 'Tue Nov 10 09:00:00 2026', boundaryStart = 'Wed Nov 11 10:00:00 2026';

test('custody scans a reused wrapper PID inside the root', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const f = custodyFixture(t, custodyRow(900050, '@ended-suspect', 'node ended'), CUSTODY_BOUNDARY);
  const reusedWrapper = custodyRow(f.job.pid, boundaryStart, 'node unrelated wrapper');
  const proof = await cleanupAgentJob(f.job, { alive: () => false, list: () => [cleanCallerRow(), reusedWrapper],
    cwd: pid => pid === reusedWrapper.pid ? f.dir : process.cwd(), kill: () => assert.fail('cwd evidence never signals') });
  assert.equal(proof.confirmed, false);
  const record = JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8'));
  assert.ok(record.observations.at(-1).identities.some(row => row.pid === reusedWrapper.pid && row.start === reusedWrapper.start));
});

test('an unreadable process proven older than the pre-spawn boundary is ignored', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  const f = custodyFixture(t, custodyRow(900051, '@ended-suspect', 'node ended'), CUSTODY_BOUNDARY);
  const old = custodyRow(900052, oldStart, 'node unrelated');
  const proof = await cleanupAgentJob(f.job, { alive: () => false, list: () => [cleanCallerRow(), old],
    cwd: pid => { if (pid === old.pid) throw Error('EACCES'); return process.cwd(); }, kill: () => assert.fail('cwd evidence never signals') });
  assert.equal(proof.confirmed, true);
});

test('a readable old process in the root and unreadable unknown-time process both remain held', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  for (const [name, suspect, cwd] of [
    ['readable old in root', custodyRow(900053, oldStart, 'node unrelated'), pid => pid === 900053 ? null : process.cwd()],
    ['unreadable unknown time', custodyRow(900054, '@unknown', 'node unrelated'), pid => { if (pid === 900054) throw Error('EACCES'); return process.cwd(); }]
  ]) {
    await t.test(name, async t => {
      const f = custodyFixture(t, custodyRow(900055, '@ended-suspect', 'node ended'), CUSTODY_BOUNDARY);
      const signals = [];
      const proof = await cleanupAgentJob(f.job, { alive: () => false, list: () => [cleanCallerRow(), suspect],
        cwd: pid => cwd(pid) ?? f.dir, spawnSync: () => ({ status: 1, stdout: '' }),
        kill: (...args) => signals.push(args) });
      assert.equal(proof.confirmed, false);
      assert.deepEqual(signals, [], 'uncertain cwd ownership never authorizes a signal');
      if (name === 'unreadable unknown-time') {
        const record = JSON.parse(readFileSync(f.token + '.processes.custody.json', 'utf8'));
        assert.ok(record.observations.at(-1).identities.some(row => row.pid === suspect.pid && row.start === suspect.start),
          'the exact unresolved process identity remains in custody');
      }
    });
  }
});

test('same-second unreadable and same PID/start with changed argv remain held', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  await t.test('same second is not proven older when the boundary has milliseconds', async t => {
    const f = custodyFixture(t, custodyRow(900056, '@ended-suspect', 'node ended'), CUSTODY_BOUNDARY);
    const sameSecond = custodyRow(900057, boundaryStart, 'node unrelated');
    const proof = await cleanupAgentJob(f.job, { alive: () => false, list: () => [cleanCallerRow(), sameSecond],
      cwd: pid => { if (pid === sameSecond.pid) throw Error('EACCES'); return process.cwd(); }, kill: () => assert.fail('cwd evidence never signals') });
    assert.equal(proof.confirmed, false);
  });
  await t.test('saved identity command change', async t => {
    const saved = custodyRow(900058, boundaryStart, 'node saved helper'), f = custodyFixture(t, saved, CUSTODY_BOUNDARY);
    const changed = { ...saved, args: 'node changed helper' };
    const proof = await cleanupAgentJob(f.job, { alive: () => false, list: () => [cleanCallerRow(), changed],
      cwd: () => '/outside/worktree', kill: () => assert.fail('cwd evidence never signals') });
    assert.equal(proof.confirmed, false);
  });
});

test('legacy unreadable candidates need a core-supplied pre-spawn boundary', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  for (const [name, options, expected] of [
    ['missing boundary', {}, false],
    ['safe boundary', { legacyCustodyBoundary: CUSTODY_BOUNDARY }, true]
  ]) {
    await t.test(name, async t => {
      const f = legacyFixture(t), old = custodyRow(900059, oldStart, 'node unrelated');
      f.job.started = CUSTODY_BOUNDARY + 60_000; // A post-spawn part time must not become a cutoff.
      const proof = await cleanupAgentJob(f.job, { legacyCustodyRoot: f.root, list: () => [cleanCallerRow(), old],
        cwd: pid => { if (pid === old.pid) throw Error('EACCES'); return process.cwd(); }, kill: () => assert.fail('legacy scan never signals'), ...options });
      assert.equal(proof.confirmed, expected);
    });
  }
});

test('cleanup rereads a custody error written while captured identities stop', async t => {
  const dir = folder(t), token = join(dir, 'shutdown.spec.json'), row = custodyRow(900060, boundaryStart, 'node saved helper');
  writeFileSync(`${token}.processes.json`, JSON.stringify([row]));
  let rows = [row];
  const proof = await cleanupAgentJob({ pid: 900061, token }, { alive: () => false, list: () => rows,
    kill: (pid, signal) => { if (pid === row.pid && signal === 'SIGTERM') { writeFileSync(`${token}.processes.error`, 'custody scan failed\n'); rows = []; } },
    sleep: async () => {}, grace: 1, poll: 1 });
  assert.equal(proof.confirmed, false);
});

test('post-shutdown custody scan creates and reopens custody findings', { skip: !['darwin', 'linux'].includes(process.platform) }, async t => {
  await t.test('a new in-root process is found with no marker at cleanup entry', async t => {
    const dir = folder(t), token = join(dir, 'new-finding.spec.json'), saved = custodyRow(900062, '@ended', 'node saved helper');
    writeFileSync(token, JSON.stringify({ custodyRoot: dir, custodyBoundary: CUSTODY_BOUNDARY }));
    writeFileSync(`${token}.processes.json`, JSON.stringify([saved]));
    const foreign = custodyRow(900063, boundaryStart, 'node foreign helper');
    const proof = await cleanupAgentJob({ pid: 900064, token }, { alive: () => false, list: () => [cleanCallerRow(), foreign],
      cwd: pid => pid === foreign.pid ? dir : process.cwd(), kill: () => assert.fail('cwd evidence never signals') });
    assert.equal(proof.confirmed, false);
    assert.ok(existsSync(`${token}.processes.custody.json`));
  });
  await t.test('a resolved marker reopens when a fresh scan finds a process', async t => {
    const f = custodyFixture(t, custodyRow(900065, '@ended', 'node ended'), CUSTODY_BOUNDARY), foreign = custodyRow(900066, boundaryStart, 'node foreign helper');
    const record = JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8'));
    record.resolution = { at: 1, completeProcessTable: true, completeCwdInventory: true, recordedIdentitiesGone: true, unsavedProcessesInRoot: 0, manifestConfirmed: true };
    writeFileSync(`${f.token}.processes.custody.json`, JSON.stringify(record));
    const proof = await cleanupAgentJob(f.job, { alive: () => false, list: () => [cleanCallerRow(), foreign],
      cwd: pid => pid === foreign.pid ? f.dir : process.cwd(), kill: () => assert.fail('cwd evidence never signals') });
    assert.equal(proof.confirmed, false);
    assert.equal(JSON.parse(readFileSync(`${f.token}.processes.custody.json`, 'utf8')).resolution, null);
  });
});

test('the hung-command watch stops only the silent command; the agent goes on and a helper stays (STOPS-0129)', async t => {
  const dir = folder(t), helperPid = join(dir, 'helper.pid'), commandPid = join(dir, 'command.pid'), result = join(dir, 'r.json');
  const largePs = fakePs(dir, 'case "$LC_ALL:$*" in C:*-ww*) /usr/bin/head -c 1100000 /dev/zero | /usr/bin/tr \'\\000\' x; printf "\\n"; exec /bin/ps "$@" ;; *) exec /bin/ps "$@" ;; esac');
  const job = startAgentJob({ id: '30-build-1', dir, cwd: dir, command: process.execPath, args: ['-e', HUNG_AGENT], input: '',
    env: { PATH: `${largePs}:/usr/bin:/bin`, HELPER_PID: helperPid, COMMAND_PID: commandPid, RESULT: result }, hung: { after: 1500, every: 150, cpu: 0.5 } });
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
