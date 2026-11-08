import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { chatLaunch, chatCommand } from '../src/workflow-chat.mjs';
import { temp } from './runtime-fake.mjs';
import { openRun, runStatus } from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';
import { acquireInterpreterSlot } from '../src/interpreter-queue.mjs';
import { codexConfigs } from './helpers/codex-config-args.mjs';

for (const agent of ['codex', 'claude', 'gemini', 'agy']) for (const mode of ['start', 'resume'])
  for (const configured of [true, false]) test(`workflow queue environment: ${agent} ${mode}, ${configured ? 'custom' : 'default'} caller settings replace stale daemon values`, t => {
    const root = temp(t), program = join(root, 'agent');
    writeFileSync(program, `#!${process.execPath}\nconsole.log(JSON.stringify({queue:process.env.PDD_INTERPRETER_QUEUE,cap:process.env.PDD_INTERPRETER_CONCURRENCY,argv:process.argv.slice(2)}));\n`, { mode: 0o700 });
    const queue = join(root, `queue ' " $HOME $(touch injected) \u007f`);
    const env = { HOME: root, ...(configured ? { PDD_INTERPRETER_QUEUE: queue, PDD_INTERPRETER_CONCURRENCY: '1' } : {}) };
    const launch = chatLaunch({ run: { runDir: root }, agent, configDir: null, env });
    const id = '11111111-1111-4111-8111-111111111111';
    const command = chatCommand({ agent, cwd: root, configDir: null, ...launch, program,
      ...(mode === 'resume' ? { resumeId: id } : { sessionId: id }) });
    for (const daemon of [{}, { PDD_INTERPRETER_QUEUE: '/stale-queue', PDD_INTERPRETER_CONCURRENCY: '9' }]) {
      const child = spawnSync('/bin/sh', ['-c', command], { encoding: 'utf8', env: { HOME: root, PATH: process.env.PATH, ...daemon } });
      assert.equal(child.status, 0, child.stderr);
      const out = JSON.parse(child.stdout), expected = { queue: configured ? queue : `/tmp/pdd-interpreter-${process.getuid?.() ?? 'user'}`, cap: configured ? '1' : '2' };
      assert.deepEqual({ queue: out.queue, cap: out.cap }, expected, 'workflow agent must share the caller queue and cap');
      if (agent === 'codex') {
        const { set } = codexConfigs(out.argv);
        assert.equal(set.PDD_INTERPRETER_QUEUE, expected.queue, 'Codex shell commands need the same queue');
        assert.equal(set.PDD_INTERPRETER_CONCURRENCY, expected.cap);
      }
    }
  });

test('workflow start, resume, replacement and status share the caller machine queue', async t => {
  const f = await fixture(t), bin = join(f.base, 'bin'); mkdirSync(bin);
  writeFileSync(join(bin, 'claude'), `#!${process.execPath}\nconsole.log(JSON.stringify({queue:process.env.PDD_INTERPRETER_QUEUE,cap:process.env.PDD_INTERPRETER_CONCURRENCY}));\n`, { mode: 0o700 });
  const queue = join(f.base, "queue 'q'"), daemon = { HOME: f.ports.env.HOME, PATH: `${bin}:/usr/bin:/bin`,
    PDD_INTERPRETER_QUEUE: '/stale-queue', PDD_INTERPRETER_CONCURRENCY: '9' };
  Object.assign(f.ports.env, { PDD_INTERPRETER_QUEUE: queue, PDD_INTERPRETER_CONCURRENCY: '1' });
  const commands = () => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');
  const expectCaller = () => {
    const child = spawnSync('/bin/sh', ['-c', commands().at(-1)[3]], { env: daemon, encoding: 'utf8' });
    assert.equal(child.status, 0, child.stderr);
    assert.deepEqual(JSON.parse(child.stdout), { queue, cap: '1' });
  };
  assert.equal((await f.run()).exitCode, 0); expectCaller();
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  f.herdr.paneOf(f.record().chats[0]).agent = null;
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0); expectCaller();
  assert.equal((await openRun({ ref: '17', cwd: f.source, newSession: true }, f.ports)).exitCode, 0); expectCaller();
  assert.equal(commands().length, 3);
  await acquireInterpreterSlot({ cwd: f.record().root, origin: 'http://localhost:1', requestId: 'active', kind: 'check', env: f.ports.env });
  let queued, release, stopped = false;
  const waiting = new Promise(done => { queued = done; }), wake = new Promise(done => { release = done; });
  const next = acquireInterpreterSlot({ cwd: f.record().root, origin: 'http://localhost:1', requestId: 'waiting', kind: 'check', env: f.ports.env },
    { say: queued, interrupted: () => stopped, sleep: () => wake });
  try {
    await waiting;
    const status = await runStatus({ ref: '17', cwd: f.source }, f.ports);
    assert.equal(status.exitCode, 0);
    assert.match(status.message, /interpreter slot.*position 1/, 'status must observe the queue used by its chats');
  } finally { stopped = true; release(); await next; }
});
