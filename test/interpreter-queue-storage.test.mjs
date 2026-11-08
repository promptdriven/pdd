import test from 'node:test';
import assert from 'node:assert/strict';
import { chmodSync, readFileSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { temp } from './runtime-fake.mjs';

const queueUrl = new URL('../src/interpreter-queue.mjs', import.meta.url).href;
const lockUrl = new URL('../src/workflow-runner.mjs', import.meta.url).href;
const operations = ['acquire', 'mark', 'observe'];
const rows = root => readdirSync(root).filter(name => /^ticket-\d+\.json$/.test(name))
  .map(name => JSON.parse(readFileSync(join(root, name))));

// Child bounds make a synchronous retry loop a behavioral assertion failure.
// READY proves that setup reached the operation before a possible timeout.
function run(source) {
  const child = spawnSync(process.execPath, ['--input-type=module', '-e', source], { encoding: 'utf8', timeout: 2000 });
  assert.match(child.stdout, /READY/);
  assert.equal(child.error?.code, undefined, 'queue operation must return instead of spinning');
  assert.equal(child.status, 0, child.stderr);
  return JSON.parse(child.stdout.trim().split('\n').at(-1));
}

function setup(root, operation) {
  return `
    import {acquireInterpreterSlot,markInterpreterDispatch,observeInterpreterRequest} from ${JSON.stringify(queueUrl)};
    import {acquireRunLock} from ${JSON.stringify(lockUrl)};
    const root=${JSON.stringify(root)}, operation=${JSON.stringify(operation)};
    const env={PDD_INTERPRETER_QUEUE:root};
    const input={cwd:process.cwd(),origin:'http://localhost:1',requestId:'paid',kind:'check',env};
    const slot=operation==='acquire'?null:await acquireInterpreterSlot(input);
    if(operation==='observe') await markInterpreterDispatch(slot);
    const call=ports=>operation==='acquire'?acquireInterpreterSlot({...input,deadline:ports.deadline},ports)
      :operation==='mark'?markInterpreterDispatch(slot,ports)
      :observeInterpreterRequest({...input,outcome:'verdict',terminal:true},ports);
    console.log('READY');
  `;
}

function retained(root, operation) {
  if (operation === 'acquire') assert.deepEqual(rows(root), []);
  else {
    assert.equal(rows(root).length, 1);
    assert.equal(rows(root)[0].state, 'running');
    assert.equal(rows(root)[0].dispatched, operation === 'observe');
    assert.equal(rows(root)[0].outcome, null);
    assert.equal(rows(root)[0].endedAt, null);
  }
}

for (const operation of operations) for (const interrupted of (operation === 'acquire' ? [false] : [false, true]))
  test(`unwritable storage fails promptly during ${operation}, interrupted=${interrupted}`, t => {
    let root;
    t.after(() => chmodSync(root, 0o700));
    root = temp(t);
    const result = run(setup(root, operation) + `
      import {chmodSync,openSync,closeSync} from 'node:fs';
      chmodSync(root,0o500);
      // Confirm a real permission error, rather than relying on mode bits alone.
      let permission;
      try { closeSync(openSync(root+'/probe','wx')); } catch(error) { permission=error.code; }
      let sleeps=0,code;
      try { await call({interrupted:()=>${interrupted},sleep:async()=>{sleeps++;}}); }
      catch(error) { code=error.code; }
      console.log(JSON.stringify({permission,code,sleeps}));
    `);
    assert.equal(result.permission, 'EACCES');
    assert.equal(result.code, 'local-state-unavailable');
    assert.equal(result.sleeps, 0, 'storage failure is not live contention');
    retained(root, operation);
  });

for (const operation of operations) for (const stop of ['interrupt', 'deadline', 'bound'])
  test(`repeated absent-lock races yield and stop ${operation} on ${stop}`, t => {
    const root = temp(t);
    const result = run(setup(root, operation) + `
      let now=1000,sleeps=0,attempts=0,interrupted=false,code,value;
      const stop=${JSON.stringify(stop)}, deadline=stop==='deadline'?1250:Infinity;
      const ports={now:()=>now,deadline,interrupted:()=>interrupted,
        acquireLock:()=>{attempts++;throw Object.assign(Error('race'),{code:'run_busy'});},
        sleep:async ms=>{sleeps++;now+=ms;if(stop==='interrupt')interrupted=true;await new Promise(done=>setImmediate(done));}};
      try { value=await call(ports); } catch(error) { code=error.code; }
      console.log(JSON.stringify({code,value,now,sleeps,attempts}));
    `);
    if (operation === 'acquire' && stop !== 'bound') assert.equal(result.value, null);
    else assert.equal(result.code, 'local-state-unavailable');
    assert.ok(result.sleeps > 0);
    assert.equal(result.attempts, result.sleeps, 'check stop before trying the lock again');
    assert.ok(result.now <= (stop === 'interrupt' ? 1100 : stop === 'deadline' ? 1250 : 6000));
    retained(root, operation);
  });

for (const operation of operations) test(`a removed queue root fails ${operation} without losing its saved evidence`, t => {
  const sandbox = temp(t), root = join(sandbox, 'queue'), saved = join(sandbox, 'saved');
  // acquire creates the root; mark and observe create it during their setup.
  const result = run(setup(root, operation) + `
    import {renameSync,mkdirSync} from 'node:fs';
    mkdirSync(root,{recursive:true});
    let sleeps=0,code,moved=false;
    try { await call({acquireLock:(dir,name)=>{if(!moved){renameSync(root,${JSON.stringify(saved)});moved=true;}return acquireRunLock(dir,name);},
      sleep:async()=>{sleeps++;}}); } catch(error) { code=error.code; }
    console.log(JSON.stringify({code,sleeps}));
  `);
  assert.equal(result.code, 'local-state-unavailable');
  assert.equal(result.sleeps, 0);
  retained(saved, operation);
});

// Pair successful release recovery and early live-lock deadlines with a storage
// regression. The same test must fail on the unfixed queue for that regression.
for (const operation of ['mark', 'observe']) test(`live release and caller deadline preserve ${operation} before a storage failure`, t => {
  let root;
  t.after(() => chmodSync(root, 0o700));
  root = temp(t);
  const result = run(setup(root, operation) + `
    import {chmodSync} from 'node:fs';
    let now=1000,sleeps=0,deadlineCode;
    const release=acquireRunLock(root,'interpreter-admission.lock');
    try { await call({now:()=>now,deadline:1200,sleep:async ms=>{now+=ms;sleeps++;}}); }
    catch(error) { deadlineCode=error.code; }
    release();
    const deadlineNow=now;
    // Reproduce a holder releasing between failed acquire and ownership read.
    let first=true,raceSleeps=0;
    const live=acquireRunLock(root,'interpreter-admission.lock');
    await call({acquireLock:(dir,name)=>{
      if(first){first=false;try{return acquireRunLock(dir,name);}finally{live();}}
      return acquireRunLock(dir,name);
    },sleep:async()=>{raceSleeps++;await new Promise(done=>setImmediate(done));}});
    // Use a new request because observation above has already finished 'paid'.
    const next=await acquireInterpreterSlot({...input,requestId:'next'});
    if(operation==='observe')await markInterpreterDispatch(next);
    chmodSync(root,0o500);
    let storageCode;
    try {
      if(operation==='mark')await markInterpreterDispatch(next);
      else await observeInterpreterRequest({...input,requestId:'next',outcome:'verdict',terminal:true});
    } catch(error) { storageCode=error.code; }
    console.log(JSON.stringify({deadlineCode,deadlineNow,sleeps,raceSleeps,storageCode}));
  `);
  assert.equal(result.deadlineCode, 'local-state-unavailable');
  assert.equal(result.deadlineNow, 1200, 'caller deadline stops before the five-second bound');
  assert.equal(result.sleeps, 2);
  assert.equal(result.raceSleeps, 1);
  assert.equal(result.storageCode, 'local-state-unavailable');
  assert.equal(rows(root).at(-1).state, 'running');
  assert.equal(rows(root).at(-1).dispatched, operation === 'observe');
});
