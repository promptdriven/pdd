import { checkMachine } from './helpers/check-machine.mjs';
import { calculateCheckCapacity } from '../src/test-suite-queue.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, existsSync, readFileSync, readdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { spawn } from 'node:child_process';
import { runPdd } from '../src/pdd-cli.mjs';
import { fixture as workflowFixture } from './helpers/workflow-runner-fixture.mjs';
import { runStatus } from '../src/workflow-runner.mjs';

const capture = () => ({text:'', write(text) { this.text += text; }});
const until = async (predicate, explanation) => {
  for (let i = 0; i < 500; i++) { if (predicate()) return; await new Promise(done => setTimeout(done, 5)); }
  assert.fail(explanation);
};
function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'pdd-suite-queue-'));
  const f = { root, queue:join(root,'queue'), clock:100_000, started:[], finished:false, promises:[], outputs:[] };
  f.env = { ...process.env, PDD_SUITE_QUEUE:f.queue, HOME:join(root,'home') };
  mkdirSync(f.queue,{recursive:true});
  writeFileSync(join(f.queue,'capacity.json'),JSON.stringify(calculateCheckCapacity({checks:3},checkMachine({taskset:null}).ports)));
  f.ports = { ...checkMachine({taskset:null}).ports, now:() => f.clock, alive:pid => f.isAlive ? f.isAlive(pid) : true, sleep:() => new Promise(done => setTimeout(done, 1)),
    execute:async (command, options) => {
      options.onChild(process.pid);
      const call = {command, options}; f.started.push(call);
      if (f.finished) return {exitCode:0};
      return new Promise(done => { call.finish = (exitCode = 0, reason) => done({exitCode, reason}); });
    } };
  f.run = (index, extra = {}) => {
    const cwd = join(root, `repository-${index}`); mkdirSync(cwd, {recursive:true});
    const stdout = capture(), stderr = capture(); f.outputs.push(stdout);
    const promise = runPdd(['workflow','suite','--command',`check-${index}`, ...(extra.timeout ? ['--timeout',String(extra.timeout)] : [])], {
      cwd, env:{...f.env, HOME:join(root,`profile-${index}`)}, stdout, stderr,
      workflowRunner:{runSuite:async (input, ports) => (await import('../src/test-suite-queue.mjs')).runTestSuite(input, {...ports, ...f.ports})},
    });
    f.promises.push(promise); return promise;
  };
  f.status = async (index, since = 0) => (await import('../src/test-suite-queue.mjs')).readSuiteProgress({cwd:join(root,`repository-${index}`), since, env:f.env}, f.ports);
  t.after(async () => { f.finished = true; f.isAlive = pid => pid === process.pid; for (const call of f.started) call.finish?.(); await Promise.all(f.promises); rmSync(root, {recursive:true, force:true}); });
  return f;
}

test('full suites from eight repositories and profiles share three slots and preserve queue order', async t => {
  const f = fixture(t);
  const work = [];
  for (let index = 1; index <= 8; index++) {
    work.push(f.run(index));
    // Registration order is the invocation order, independent of equal clocks.
    await until(() => existsSync(f.queue) && readdirSync(f.queue).filter(name => name.startsWith('ticket-')).length === index || f.promises.length && f.finished, 'suite registration must reach the shared queue');
  }
  await until(() => f.started.length === 3, 'three suites start');
  for (let index = 4; index <= 8; index++) {
    assert.equal((await f.status(index)).state, 'waiting');
    assert.equal((await f.status(index)).position, index - 3);
  }
  for (let index = 0; index < 5; index++) {
    assert.equal(f.started.length - index, 3, 'only three suite commands occupy slots');
    f.started[index].finish();
    await until(() => f.started.length === index + 4, 'the oldest waiter starts on release');
    assert.equal(f.started.at(-1).command, `check-${index + 4}`);
  }
  f.finished = true; for (const call of f.started) call.finish();
  assert.deepEqual(await Promise.all(work), Array(8).fill(0));
  assert.deepEqual(f.started.map(call => call.command), Array.from({length:8}, (_, index) => `check-${index + 1}`));
  assert.equal(f.outputs[3].text.includes('position 1'), true);
  assert.equal(f.started.every(call => call.options.timeoutMs === 30 * 60_000), true);
});

test('waiting does not spend suite execution timeout, and restart reads preserve paused time', async t => {
  const f = fixture(t);
  for (let index = 1; index <= 3; index++) f.run(index);
  await until(() => f.started.length === 3, 'initial suites start');
  f.clock = 200_000; f.run(4, {timeout:2});
  await until(() => f.outputs[3].text.includes('position'), 'fourth suite reports waiting');
  f.clock = 9_000_000;
  assert.equal((await f.status(4, 150_000)).pausedMs, 8_800_000);
  assert.equal((await f.status(4)).state, 'waiting');
  f.started[0].finish(); await until(() => f.started.length === 4, 'queued suite starts');
  assert.equal(f.started[3].options.timeoutMs, 120_000);
  f.clock += 50_000; f.started[3].finish();
  assert.equal(await f.promises[3], 0);
  const {readSuiteProgress} = await import('../src/test-suite-queue.mjs');
  const status = readSuiteProgress({cwd:join(f.root,'repository-4'), since:150_000, env:f.env}, {now:() => f.clock + 100_000});
  assert.equal(status.state, 'finished'); assert.equal(status.reason, null);
  assert.equal(status.pausedMs, 8_850_000);
});

test('suite failure retains its own reason and status, then releases a slot', async t => {
  const f = fixture(t);
  for (let index = 1; index <= 4; index++) f.run(index);
  await until(() => f.started.length === 3 && f.outputs[3].text.includes('position'), 'queue fills');
  f.clock += 10_000;
  f.started[0].finish(124, 'per-file timeout: test/slow.test.mjs');
  assert.equal(await f.promises[0], 124);
  const status = await f.status(1);
  assert.equal(status.state, 'finished'); assert.match(status.reason, /per-file timeout.*slow/);
  await until(() => f.started.length === 4, 'timeout releases capacity');
});

test('dead waiter is removed from position while an orphan with a live child retains capacity', async t => {
  const f = fixture(t);
  mkdirSync(f.queue,{recursive:true});
  const row = (ticket, state, pid, childPid) => ({ticket,state,pid,childPid,cwd:join(f.root,`seed-${ticket}`),queuedAt:1,startedAt:state === 'running' ? 2 : null,finishedAt:null,reason:null});
  for (const value of [row(1,'running',10,20), row(2,'running',11,21), row(3,'running',12,22), row(4,'waiting',13,null)])
    writeFileSync(join(f.queue,`ticket-${value.ticket}.json`), JSON.stringify(value));
  f.isAlive = pid => pid < 0 || pid === process.pid;
  f.run(5); await until(() => f.outputs[0].text.includes('position'), 'new suite enters queue');
  assert.equal((await f.status(5)).position, 1);
  assert.equal(f.started.length, 0, 'live orphan suites still occupy all slots');
  const orphan = (await import('../src/test-suite-queue.mjs')).readSuiteProgress({cwd:join(f.root,'seed-1'),env:f.env},f.ports);
  assert.equal(orphan.state, 'running'); assert.match(orphan.reason, /runner ended/);
  f.isAlive = pid => pid === process.pid || pid === -21 || pid === -22;
  await until(() => f.started.length === 1, 'dead child can release its slot');
});

test('workflow JSON status reads queue position even while the run has ordinary ownership', async t => {
  const f = await workflowFixture(t); const result = await f.run(); assert.equal(result.exitCode, 0, result.message);
  const run = f.record(), queue = join(f.base,'suite-queue'); mkdirSync(queue);
  const row = {ticket:1,pid:process.pid,childPid:null,cwd:run.root,state:'waiting',queuedAt:f.clock,startedAt:null,finishedAt:null,reason:null};
  writeFileSync(join(queue,'ticket-1.json'), JSON.stringify(row));
  const owner = join(run.runDir,'.ordinary-owner'); mkdirSync(owner, {recursive:true});
  writeFileSync(join(owner,'owner-suite-test.json'), JSON.stringify({pid:process.pid,hostname:'suite-test',token:'suite-test'}));
  const before = readFileSync(join(run.runDir,'status.json'));
  const status = await runStatus({cwd:run.root,json:true}, {...f.ports, env:{...f.ports.env,PDD_SUITE_QUEUE:queue}});
  assert.equal(status.exitCode, 0, status.message);
  const item = JSON.parse(status.message).runs[0];
  assert.equal(item.suite?.state, 'waiting'); assert.equal(item.suite?.position, 1);
  assert.match(item.words, /position 1/);
  assert.deepEqual(readFileSync(join(run.runDir,'status.json')), before, 'queue status does not mutate workflow state');
});

test('CLI rejects absent commands and invalid timeouts before execution', async () => {
  for (const args of [[], ['--command','x','--timeout','0'], ['--command','x','--timeout','121']]) {
    const stderr = capture(); let calls = 0;
    const code = await runPdd(['workflow','suite',...args], {stderr, stdout:capture(), workflowRunner:{runSuite:() => { calls++; }}});
    assert.equal(code, 2); assert.equal(calls, 0);
  }
});

test('native CLI preserves cwd, env, closed stdin, stdout, stderr and exit code', async t => {
  const f = fixture(t), cwd = join(f.root,'native repo'); mkdirSync(cwd);
  const program = join(f.root,'fake-suite.cjs'), output = join(f.root,'native.json');
  writeFileSync(program, `const fs=require('node:fs'); fs.writeFileSync(process.env.SUITE_OBSERVATION, JSON.stringify({cwd:process.cwd(),value:process.env.SUITE_VALUE,stdin:fs.readFileSync(0,'utf8')})); console.log('suite-out'); console.error('suite-err'); process.exitCode=7;`);
  const quote = value => `'${value.replaceAll("'", "'\\''")}'`;
  const child = spawn(process.execPath, [resolve('bin/pdd.mjs'),'workflow','suite','--command',`${quote(process.execPath)} ${quote(program)}`], {cwd, env:{...f.env,SUITE_VALUE:'literal $() value',SUITE_OBSERVATION:output}});
  let stdout = '', stderr = ''; child.stdout.on('data', value => stdout += value); child.stderr.on('data', value => stderr += value);
  const code = await new Promise(done => child.on('close', done));
  assert.equal(code, 7, stderr);
  assert.deepEqual(JSON.parse(readFileSync(output,'utf8')), {cwd,value:'literal $() value',stdin:''});
  assert.match(stdout, /suite-out/); assert.match(stderr, /suite-err/);
});

test('native timeout stops a suite process group before its descendant can act', async t => {
  const f = fixture(t), marker = join(f.root,'escaped-child'), started = join(f.root,'child-started');
  // Admission and CLI timeout units are tested above. This injected native port
  // shortens only the execution clock, so the real signal path runs in milliseconds.
  f.ports.execute = async (command, options) => (await import('../src/test-suite-queue.mjs')).executeSuite(command, {...options, timeoutMs:1000});
  const program = join(f.root,'slow-suite.cjs');
  writeFileSync(program, `const {spawn}=require('node:child_process'); spawn(process.execPath,['-e',${JSON.stringify(`require('node:fs').writeFileSync(${JSON.stringify(started)},'started'); setTimeout(()=>require('node:fs').writeFileSync(${JSON.stringify(marker)},'escaped'),1500)`)}],{stdio:'ignore'}); setInterval(()=>{},1000);`);
  const quote = value => `'${value.replaceAll("'", "'\\''")}'`;
  const stdout = capture(), stderr = capture();
  const code = await runPdd(['workflow','suite','--command',`${quote(process.execPath)} ${quote(program)}`], {cwd:f.root, env:f.env, stdout, stderr,
    workflowRunner:{runSuite:async (input, ports) => (await import('../src/test-suite-queue.mjs')).runTestSuite(input,{...ports,...f.ports})}});
  assert.equal(code, 124); assert.match(stderr.text, /timeout/);
  assert.equal(existsSync(started), true, 'the descendant reached its action before timeout');
  await new Promise(done => setTimeout(done, 1600));
  assert.equal(existsSync(marker), false, 'timeout stops descendants before they can act');
});

test('corrupt queue ownership cannot admit a suite command', async t => {
  const f = fixture(t); mkdirSync(f.queue,{recursive:true}); writeFileSync(join(f.queue,'ticket-1.json'), '{');
  assert.equal(await f.run(1), 1); assert.equal(f.started.length, 0);
});

test('separate CLI processes and the compatibility script share the same three native slots', async t => {
  const root = mkdtempSync(join(tmpdir(),'pdd-native-suite-')), queue = join(root,'queue'), children = [];
  t.after(async () => {
    for (const item of children) if (!item.ended) item.child.kill('SIGTERM');
    await Promise.all(children.map(item => item.done)); rmSync(root,{recursive:true,force:true});
  });
  mkdirSync(queue);
  writeFileSync(join(queue,'capacity.json'),JSON.stringify(calculateCheckCapacity({checks:3},checkMachine({taskset:null}).ports)));
  const program = join(root,'controlled-suite.cjs');
  writeFileSync(program, `const fs=require('node:fs'),path=require('node:path'); fs.writeFileSync(path.join(process.cwd(),'started'),''); const timer=setInterval(()=>{if(fs.existsSync(path.join(process.cwd(),'release'))){clearInterval(timer); process.exitCode=0;}},10);`);
  const quote = value => `'${value.replaceAll("'", "'\\''")}'`;
  const command = `${quote(process.execPath)} ${quote(program)}`;
  for (let index=1; index<=5; index++) {
    const cwd=join(root,`repo-${index}`), home=join(root,`profile-${index}`); mkdirSync(cwd); mkdirSync(home);
    const env={...process.env, HOME:home, PDD_SUITE_QUEUE:queue, PDD_VM_SUITE_LOCK:undefined, SUITE:command};
    const child=index===5 ? spawn('/bin/bash',[resolve('scripts/vm-suite-lock.sh')],{cwd,env})
      : spawn(process.execPath,[resolve('bin/pdd.mjs'),'workflow','suite','--command',command],{cwd,env});
    const item={child,cwd,output:'',ended:false}; child.stdout.on('data',value=>item.output+=value); child.stderr.on('data',value=>item.output+=value);
    item.done=new Promise(done=>child.once('close',code=>{item.ended=true;done(code);})); children.push(item);
    await until(()=>existsSync(queue) && readdirSync(queue).filter(name=>/^ticket-.*\.json$/.test(name)).length===index,'native invocation registers a suite ticket');
  }
  await until(()=>children.slice(0,3).every(item=>existsSync(join(item.cwd,'started'))),'first three native suites start');
  assert.equal(children.slice(3).some(item=>existsSync(join(item.cwd,'started'))),false);
  await until(()=>children[3].output.includes('position 1') && children[4].output.includes('position 2'),'native waiters report their positions');
  for(let index=0;index<2;index++) {
    writeFileSync(join(children[index].cwd,'release'),'');
    assert.equal(await children[index].done,0,children[index].output);
    await until(()=>existsSync(join(children[index+3].cwd,'started')),'the next native waiter starts');
    assert.equal(children.filter(item=>existsSync(join(item.cwd,'started'))&&!existsSync(join(item.cwd,'release'))).length,3);
  }
  for(const item of children) writeFileSync(join(item.cwd,'release'),'');
  assert.deepEqual(await Promise.all(children.map(item=>item.done)),[0,0,0,0,0]);
});


test('default queue identity is independent of repository homes and agent profiles', async () => {
  const {suiteQueueRoot} = await import('../src/test-suite-queue.mjs');
  assert.equal(suiteQueueRoot({HOME:'/profile/one',CODEX_HOME:'/agent/one'}),suiteQueueRoot({HOME:'/profile/two',CODEX_HOME:'/agent/two'}));
  assert.equal(suiteQueueRoot({PDD_VM_SUITE_LOCK:'/shared/lock'}),'/shared/lock.queue');
  assert.equal(suiteQueueRoot({PDD_SUITE_QUEUE:'/explicit/queue',PDD_VM_SUITE_LOCK:'/shared/lock'}),'/explicit/queue');
  assert.throws(()=>suiteQueueRoot({PDD_SUITE_QUEUE:'relative'}));
});

for (const damage of ['malformed','unreadable']) test(`workflow JSON status exposes unavailable suite ownership (${damage}) without changing progress`, async t => {
  const f=await workflowFixture(t); assert.equal((await f.run()).exitCode,0);
  const run=f.record(),queue=join(f.base,'suite-queue'); mkdirSync(queue);
  const ticket=join(queue,'ticket-other-repository.json');
  if(damage==='malformed') writeFileSync(ticket,'{'); else mkdirSync(ticket);
  const owner=join(run.runDir,'.ordinary-owner'); mkdirSync(owner,{recursive:true});
  writeFileSync(join(owner,'owner-suite-test.json'),JSON.stringify({pid:process.pid,hostname:'suite-test',token:'suite-test'}));
  const before=readFileSync(join(run.runDir,'status.json'));
  let status;
  await assert.doesNotReject(async()=>{status=await runStatus({cwd:run.root,json:true},{...f.ports,env:{...f.ports.env,PDD_SUITE_QUEUE:queue}});},'status must return explicit queue uncertainty');
  assert.equal(status.exitCode,0,status.message);
  const item=JSON.parse(status.message).runs[0];
  assert.equal(item.suite?.state,'unavailable'); assert.equal(item.suite?.pausedMs,0);
  assert.ok(item.suite.reason.length>0); assert.match(item.words,/queue.*unavailable/i);
  assert.ok(item.words.includes(item.suite.reason),'status retains the queue read cause');
  assert.deepEqual(readFileSync(join(run.runDir,'status.json')),before);
});
