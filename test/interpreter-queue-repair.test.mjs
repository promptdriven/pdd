import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { spawn, spawnSync } from 'node:child_process';
import { runCheck } from '../src/runtime-client.mjs';
import { readInterpreterProgress } from '../src/interpreter-queue.mjs';
import { fakeRuntime, harbor, portsFor, temp } from './runtime-fake.mjs';

const rows = queue => readdirSync(queue).filter(name => /^ticket-\d+\.json$/.test(name))
  .map(name => JSON.parse(readFileSync(join(queue, name))));

for (const stop of ['timeout', 'interrupt']) test(`machine queue ${stop} leaves unsent checks retryable in a new caller`, async t => {
  const setup = harbor(t), queue = temp(t), sent = new Set(); let recover = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return f.normal(entry);
    if (entry.method === 'POST') sent.add(entry.request.requestId);
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    return { status: 200, json: f.check(id, recover ? 'passed' : 'running') };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin,
    PDD_INTERPRETER_QUEUE: queue, PDD_INTERPRETER_CONCURRENCY: '1' };
  const first = portsFor(env);
  if (stop === 'interrupt') {
    const sleep = first.ports.sleep;
    first.ports.sleep = async ms => {
      await sleep(ms);
      if (sent.size === 1 && rows(queue).some(row => row.state === 'waiting' && row.kind === 'check')) first.clock.interrupt();
    };
  }
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--json': true, '--timeout': '1' } }, first.ports), 3);
  const saved = JSON.parse(first.ports.stdout.text);
  assert.equal(sent.size, 1);
  const unsent = saved.rows.find(row => row.state === 'not_run');
  assert.equal(unsent?.calls, 0);
  const batch = JSON.parse(readFileSync(join(setup.state, 'batches', saved.batch, 'batch.json')));
  assert.deepEqual(batch.rows.find(row => row.test === unsent.test).request_ids, [], 'local waits must not create permanent dispatch claims');
  const waiting = rows(queue).find(row => row.kind === 'check' && !row.dispatched);
  assert.equal(waiting.state, 'finished'); assert.equal(waiting.outcome, 'not_sent');
  assert.ok(!fake.gets.some(entry => entry.url.endsWith(waiting.requestId)), 'never poll an unsent ID');
  recover = true;
  const next = portsFor(env);
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--retry': saved.batch, '--json': true, '--timeout': '1' } }, next.ports), 0,
    'a new caller must retry the saved unsent check after terminal recovery');
  assert.equal(sent.size, 2, 'retry sends only the unstarted check');
  assert.ok(JSON.parse(next.ports.stdout.text).rows.every(row => row.state === 'passed'));
});

test('a killed queue waiter recovers its saved unsent check after process restart', async t => {
  const setup = harbor(t), queue = temp(t), sent = new Set(); let recover = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return f.normal(entry);
    if (entry.method === 'POST') sent.add(entry.request.requestId);
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    return { status: 200, json: f.check(id, recover ? 'passed' : 'running') };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin,
    PDD_INTERPRETER_QUEUE: queue, PDD_INTERPRETER_CONCURRENCY: '1' };
  const source = `
    import {runCheck} from ${JSON.stringify(new URL('../src/runtime-client.mjs', import.meta.url).href)};
    import {portsFor} from ${JSON.stringify(new URL('./runtime-fake.mjs', import.meta.url).href)};
    const {ports}=portsFor(${JSON.stringify(env)}, {now:Date.now,pollMs:5,sleep:()=>new Promise(done=>setTimeout(done,5))});
    await runCheck({cwd:${JSON.stringify(setup.repo)},words:[],options:{'--json':true}},ports);
  `;
  const child = spawn(process.execPath, ['--input-type=module', '-e', source], { stdio: 'ignore' });
  const closed = new Promise(done => child.once('close', done));
  t.after(() => { if (child.exitCode === null && child.signalCode === null) child.kill('SIGKILL'); });
  let queued = false;
  for (let n = 0; n < 500; n++) {
    if (sent.size === 1 && rows(queue).some(row => row.kind === 'check' && row.state === 'waiting')) { queued = true; break; }
    await new Promise(done => setTimeout(done, 10));
  }
  assert.ok(queued, 'child must reach machine contention before the crash');
  child.kill('SIGKILL'); await closed;
  const batchName = readdirSync(join(setup.state, 'batches')).find(name => /^\d{8}-\d{6}-[a-z0-9]{4}$/.test(name));
  assert.ok(batchName);
  recover = true;
  const next = portsFor(env);
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--retry': batchName, '--json': true, '--timeout': '1' } }, next.ports), 0,
    'a restarted process must recover only the check held locally');
  assert.equal(sent.size, 2);
  assert.ok(JSON.parse(next.ports.stdout.text).rows.every(row => row.state === 'passed'));
});

test('terminal --request read releases retained capacity and admits the next public check', async t => {
  const setup = harbor(t), queue = temp(t); let recover = false;
  const fake = await fakeRuntime(t, (entry, f) => {
    if (entry.command === 'lint') return f.normal(entry);
    if (entry.method === 'POST' && !recover) return { destroy: true };
    return recover ? f.normal(entry) : { status: 404, json: { error: { code: 'not-found' } } };
  });
  const env = { HOME: setup.home, PDD_STATE_DIR: setup.state, PDD_RUNTIME_URL: fake.origin,
    PDD_INTERPRETER_QUEUE: queue, PDD_INTERPRETER_CONCURRENCY: '1' };
  const first = portsFor(env, { pollMs: 60_000 });
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true, '--timeout': '1' } }, first.ports), 3);
  const held = rows(queue).find(row => row.kind === 'check');
  assert.equal(held.state, 'running'); assert.equal(held.dispatched, true);
  recover = true;
  const next = portsFor(env), posts = fake.posts.length;
  assert.equal(await runCheck({ cwd: setup.repo, words: [], options: { '--request': held.requestId, '--json': true } }, next.ports), 0);
  assert.equal(fake.posts.length, posts, 'request reads must not POST');
  assert.equal(next.clock.uuids, 0, 'request reads allocate no new request IDs');
  const after = readInterpreterProgress({ cwd: setup.repo, env }).requests.find(row => row.requestId === held.requestId);
  assert.equal(after.state, 'finished', 'terminal --request must release machine capacity');
  assert.equal(after.outcome, 'verdict');
  assert.equal(await runCheck({ cwd: setup.repo, words: ['place-order'], options: { '--json': true, '--timeout': '1' } }, portsFor(env).ports), 0);
  assert.equal(fake.posts.filter(entry => entry.command === 'check').length, 2);
});

// A native child bounds the old infinite loop. The parent requires a completed
// local-state error and unchanged uncertain evidence, not merely a child exit.
for (const operation of ['acquire', 'mark', 'observe']) test(`malformed admission lock fails closed during ${operation}`, t => {
  const queue = temp(t), moduleUrl = new URL('../src/interpreter-queue.mjs', import.meta.url).href;
  const source = `
    import {acquireInterpreterSlot,markInterpreterDispatch,observeInterpreterRequest} from ${JSON.stringify(moduleUrl)};
    import {writeFileSync,readFileSync} from 'node:fs';
    const env={PDD_INTERPRETER_QUEUE:${JSON.stringify(queue)}};
    const input={cwd:process.cwd(),origin:'http://localhost:1',requestId:'paid',kind:'check',env};
    const operation=${JSON.stringify(operation)};
    const slot=operation==='acquire'?null:await acquireInterpreterSlot(input);
    if(operation==='observe') await markInterpreterDispatch(slot);
    writeFileSync(${JSON.stringify(join(queue, 'interpreter-admission.lock'))},'{');
    try {
      if(operation==='acquire') await acquireInterpreterSlot(input);
      if(operation==='mark') await markInterpreterDispatch(slot);
      if(operation==='observe') await observeInterpreterRequest({...input,outcome:'verdict',terminal:true},{interrupted:()=>true});
      console.log(JSON.stringify({code:'unexpected-success'}));
    } catch(error) {console.log(JSON.stringify({code:error.code}));}
  `;
  const child = spawnSync(process.execPath, ['--input-type=module', '-e', source], { encoding: 'utf8', timeout: 2000 });
  assert.equal(child.error?.code, undefined, 'malformed lock must not hang');
  assert.equal(child.status, 0, child.stderr);
  assert.equal(JSON.parse(child.stdout).code, 'local-state-unavailable');
  assert.equal(readFileSync(join(queue, 'interpreter-admission.lock'), 'utf8'), '{', 'never steal unverifiable ownership');
  if (operation !== 'acquire') {
    assert.equal(rows(queue)[0].state, 'running');
    assert.equal(rows(queue)[0].dispatched, operation === 'observe');
  }
});

for (const operation of ['mark', 'observe']) for (const stop of ['interrupt', 'deadline'])
  test(`live admission contention stops ${operation} on ${stop} and retains evidence`, t => {
    const queue = temp(t), moduleUrl = new URL('../src/interpreter-queue.mjs', import.meta.url).href;
    const source = `
      import {acquireInterpreterSlot,markInterpreterDispatch,observeInterpreterRequest} from ${JSON.stringify(moduleUrl)};
      import {writeFileSync} from 'node:fs';
      const env={PDD_INTERPRETER_QUEUE:${JSON.stringify(queue)}};
      const input={cwd:process.cwd(),origin:'http://localhost:1',requestId:'paid',kind:'check',env};
      const slot=await acquireInterpreterSlot(input);
      if(${JSON.stringify(operation)}==='observe') await markInterpreterDispatch(slot);
      writeFileSync(${JSON.stringify(join(queue, 'interpreter-admission.lock'))},JSON.stringify({pid:process.pid,token:'11111111-1111-4111-8111-111111111111'}));
      let now=1000,interrupted=false;
      const ports={now:()=>now,interrupted:()=>interrupted,sleep:async ms=>{now+=ms;interrupted=${JSON.stringify(stop)}==='interrupt';}};
      try {
        if(${JSON.stringify(operation)}==='mark') await markInterpreterDispatch(slot,ports);
        else await observeInterpreterRequest({...input,outcome:'verdict',terminal:true},ports);
        console.log(JSON.stringify({code:'unexpected-success'}));
      } catch(error) {console.log(JSON.stringify({code:error.code,now}));}
    `;
    const child = spawnSync(process.execPath, ['--input-type=module', '-e', source], { encoding: 'utf8', timeout: 2000 });
    assert.equal(child.error?.code, undefined, 'ledger mutation must stop waiting for live lock ownership');
    assert.equal(child.status, 0, child.stderr);
    const result = JSON.parse(child.stdout);
    assert.equal(result.code, 'local-state-unavailable');
    assert.ok(result.now <= 6000);
    assert.equal(rows(queue)[0].state, 'running');
    assert.equal(rows(queue)[0].dispatched, operation === 'observe');
  });
