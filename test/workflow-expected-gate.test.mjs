import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, readdirSync, statSync, writeFileSync, mkdirSync, unlinkSync} from 'node:fs';
import {hostname} from 'node:os';
import {join} from 'node:path';
import {approveRun, changeRun, cancelRun, openRun, stepDone, acquireRunLock} from '../src/workflow-runner.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const snapshot = dir => Object.fromEntries(readdirSync(dir, {recursive:true}).filter(path => statSync(join(dir,path)).isFile()).sort().map(path => [path, readFileSync(join(dir,path)).toString('base64')]));

for (const [name, action] of Object.entries({approve: approveRun, changes: changeRun, cancel: cancelRun, open: openRun})) {
  test(`${name} refuses stale gate and step before side effects`, async t => {
    const f = await fixture(t);
    assert.equal((await f.run()).exitCode, 0);
    const run = f.record(), step = run.areas[run.area].steps.find(s => !run.done[s]);
    writeFileSync(join(run.root, 'guard-sentinel'), 'unchanged');
    const filesBefore = snapshot(run.runDir);
    const before = readFileSync(join(run.runDir, 'status.json'));
    const chat = readFileSync(run.chats.at(-1).messageFile);
    f.herdr.calls.length = 0;
    for (const expected of [{expectGate:'old-gate'}, {expectStep:'old-step'}, {expectGate:'old-gate',expectStep:step}]) {
      const result = await action({ref:'17',cwd:f.source,packageRoot,text:'A change',area:'story',newSession:true,...expected}, f.ports);
      assert.equal(result.exitCode,3,result.message);
      assert.match(result.message, /gate.*none/i);
      assert.ok(result.message.includes(step),result.message);
      assert.deepEqual(readFileSync(join(run.runDir,'status.json')),before);
      assert.deepEqual(snapshot(run.runDir),filesBefore);
      assert.equal(readFileSync(join(run.root,'guard-sentinel'),'utf8'),'unchanged');
      assert.deepEqual(readFileSync(run.chats.at(-1).messageFile),chat);
      assert.equal(f.herdr.calls.length,0);
    }
  });
}

test('CLI forwards both expectations for each action', async () => {
  for (const [command, method, operands] of [['approve','approveRun',['17']],['changes','changeRun',['17','fix']],['cancel','cancelRun',['17']],['open','openRun',['17']]]) {
    let received;
    const stream = {write(){}};
    const result = await runPdd(['workflow',command,...operands,'--expect-gate','g1','--expect-step','story'], {cwd:'/tmp',stdout:stream,stderr:stream,workflowRunner:{[method]:async input => {received=input;return {exitCode:3,message:'stale'};}}});
    assert.equal(result,3); assert.equal(received.expectGate,'g1'); assert.equal(received.expectStep,'story');
  }
});

for (const [name, action] of Object.entries({changes: changeRun, cancel: cancelRun, open: openRun})) {
  test(`${name} accepts the current step`, async t => {
    const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
    const run = f.record(), step = run.areas[run.area].steps.find(s => !run.done[s]);
    const result = await action({ref:'17',cwd:f.source,packageRoot,text:'Fix the example',expectStep:step}, f.ports);
    assert.equal(result.exitCode,0,result.message);
  });
}
test('approve with a matching step retains its ordinary response', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record(), step = run.areas[run.area].steps.find(s => !run.done[s]);
  const result = await approveRun({ref:'17',cwd:f.source,packageRoot,expectStep:step},f.ports);
  assert.notEqual(result.exitCode,3,result.message);
});

for (const [name, action] of Object.entries({approve: approveRun, changes: changeRun, cancel: cancelRun, open: openRun})) {
  test(`${name} distinguishes a newer gate from the gate that was read`, async t => {
    const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
    const run = f.record(); run.gate = {id:'new-gate',area:run.areas[run.area].name,kind:'approve',at:10};
    writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
    const before = snapshot(run.runDir); f.herdr.calls.length = 0;
    const result = await action({ref:'17',cwd:f.source,packageRoot,text:'Fix it',expectGate:'old-gate'},f.ports);
    assert.equal(result.exitCode,3,result.message); assert.match(result.message,/new-gate/);
    assert.deepEqual(snapshot(run.runDir),before); assert.equal(f.herdr.calls.length,0);
  });
}

test('a current gate approves once and a late approval is refused', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const result = await stepDone({step:'scope',summary:'Scope complete',cwd:f.record().root},f.agentPorts());
  assert.equal(result.exitCode,0,result.message);
  const gate = f.record().gate.id;
  const approved = await approveRun({ref:'17',cwd:f.source,packageRoot,expectGate:gate},f.ports);
  assert.equal(approved.exitCode,0,approved.message);
  assert.equal(f.record().decisions.length,1);
  const before = snapshot(f.record().runDir); f.herdr.calls.length = 0;
  const late = await approveRun({ref:'17',cwd:f.source,packageRoot,expectGate:gate},f.ports);
  assert.equal(late.exitCode,3,late.message); assert.match(late.message,/current step: change/);
  assert.deepEqual(snapshot(f.record().runDir),before); assert.equal(f.herdr.calls.length,0);
});

test('an approval whose gate moves during confirmation is refused', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  assert.equal((await stepDone({step:'scope',summary:'Scope complete',cwd:f.record().root},f.agentPorts())).exitCode,0);
  const run = f.record(), gate = run.gate.id;
  f.ports.confirm = async () => {
    const advanced = f.record(); advanced.gate = {id:'new-gate',area:'plan',kind:'approve',at:20};
    writeFileSync(join(run.runDir,'status.json'),JSON.stringify(advanced));
    return true;
  };
  const result = await approveRun({ref:'17',cwd:f.source,packageRoot,expectGate:gate},f.ports);
  assert.equal(result.exitCode,3,result.message); assert.match(result.message,/new-gate/);
  assert.equal(f.record().decisions.length,0); assert.equal(f.record().gate.id,'new-gate');
});

test('changes refuses when its step moves while waiting for journal admission', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record(), dir = join(run.runDir,'.delivery-journal.lock'), leaf = join(dir,'owner-other.json');
  mkdirSync(dir,{recursive:true}); writeFileSync(leaf,JSON.stringify({pid:process.pid,hostname:hostname(),token:'other'}));
  let advanced = false;
  const result = await changeRun({ref:'17',cwd:f.source,text:'Revise',expectStep:'scope'}, {...f.ports,journalSleep:async () => {
    if (!advanced) { advanced = true; assert.equal((await stepDone({step:'scope',summary:'Done',cwd:run.root},f.agentPorts())).exitCode,0); unlinkSync(leaf); }
  }});
  assert.equal(result.exitCode,3,result.message); assert.match(result.message,/current step: none/i);
  assert.equal(readdirSync(run.runDir).includes('delivery-journal.json'),false);
});

test('changes refuses when its gate moves during chat inspection', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run = f.record(); run.gate={id:'g1',area:run.areas[run.area].name,kind:'approve',at:10};
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  const herdr = f.ports.herdr; let moved=false;
  const result = await changeRun({ref:'17',cwd:f.source,text:'Revise',expectGate:'g1'}, {...f.ports,herdr:async args => {
    if (!moved && args[0]==='pane' && args[1]==='read') { moved=true; const current=f.record(); current.gate.id='g2'; writeFileSync(join(run.runDir,'status.json'),JSON.stringify(current)); }
    return herdr(args);
  }});
  assert.equal(result.exitCode,3,result.message); assert.match(result.message,/g2/);
  assert.equal(f.herdr.calls.some(args=>args[0]==='agent'&&args[1]==='prompt'),false);
  assert.equal(readdirSync(run.runDir).includes('delivery-journal.json'),false);
});

test('a stale retry preserves the exact bytes of an existing pending request', async t => {
  const f=await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run=f.record(), chat=run.chats.at(-1), path=join(run.runDir,'delivery-journal.json');
  run.gate={id:'g1',area:run.areas[run.area].name,kind:'approve',at:10};
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  const bytes=JSON.stringify({requests:[{id:'pending',text:'Revise',kind:'change',area:run.areas[run.area].name,paneId:chat.paneId,state:'pending',at:10},
    {id:'abandoned',text:'Earlier',kind:'change',area:'other',paneId:'other',state:'pending',at:9,inFlight:true,owner:{pid:process.pid+1000000,hostname:hostname(),token:'dead'}}]});
  writeFileSync(path,bytes); const herdr=f.ports.herdr; let moved=false;
  const result=await changeRun({ref:'17',cwd:f.source,text:'Revise',expectGate:'g1'}, {...f.ports,processIdentity:()=>({alive:false}),herdr:async args=>{
    if (!moved && args[0]==='pane' && args[1]==='read') { moved=true; const current=f.record(); current.gate.id='g2'; writeFileSync(join(run.runDir,'status.json'),JSON.stringify(current)); }
    return herdr(args);
  }});
  assert.equal(result.exitCode,3,result.message); assert.equal(readFileSync(path,'utf8'),bytes);
});

test('changes checks the expectation at submission under ordinary ownership', async t => {
  const f=await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run=f.record(); run.gate={id:'g1',area:run.areas[run.area].name,kind:'approve',at:10};
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run)); f.herdr.calls.length=0;
  let moved=false;
  const result=await changeRun({ref:'17',cwd:f.source,text:'Revise',expectGate:'g1'}, {...f.ports,acquireRunOwnership:()=>{
    if (!moved) { moved=true; const current=f.record(); current.gate.id='g2'; writeFileSync(join(run.runDir,'status.json'),JSON.stringify(current)); }
    return ()=>{};
  }});
  assert.equal(moved,true); assert.equal(result.exitCode,3,result.message); assert.match(result.message,/g2/);
  assert.equal(f.herdr.calls.some(args=>args[0]==='agent'&&args[1]==='prompt'),false);
  assert.equal(readdirSync(run.runDir).includes('delivery-journal.json'),false);
});

test('matching cancellation commits before cleanup can race workflow progress', async t => {
  const f=await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run=f.record(); run.gate={id:'g1',area:run.areas[run.area].name,kind:'approve',at:10};
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  const herdr=f.ports.herdr; let checked=false;
  const result=await cancelRun({ref:'17',cwd:f.source,expectGate:'g1'}, {...f.ports,herdr:async args=>{
    if (!checked) {
      checked=true; assert.equal(f.record().state,'cancelled');
      const progress=await stepDone({step:'scope',summary:'Done',cwd:run.root},f.agentPorts());
      assert.notEqual(progress.exitCode,0,progress.message); assert.equal(f.record().state,'cancelled');
    }
    return herdr(args);
  }});
  assert.equal(result.exitCode,0,result.message); assert.equal(checked,true); assert.equal(f.record().state,'cancelled');
});

test('cancellation checks the gate again under ordinary ownership', async t => {
  const f=await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run=f.record(); run.gate={id:'g1',area:run.areas[run.area].name,kind:'approve',at:10};
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run)); f.herdr.calls.length=0;
  let changed=false;
  const result=await cancelRun({ref:'17',cwd:f.source,expectGate:'g1'}, {...f.ports,acquireRunOwnership:()=>{
    if (!changed) { changed=true; const current=f.record(); current.gate.id='g2'; writeFileSync(join(run.runDir,'status.json'),JSON.stringify(current)); }
    return ()=>{};
  }});
  assert.equal(result.exitCode,3,result.message); assert.match(result.message,/g2/);
  assert.equal(f.record().gate.id,'g2'); assert.equal(f.record().state,'running'); assert.equal(f.herdr.calls.length,0);
});

test('automatic cancellation reports a stale gate before a busy lock', async t => {
  const f=await fixture(t); assert.equal((await f.run()).exitCode,0);
  const run=f.record(); run.gate={id:'new',area:run.areas[run.area].name,kind:'approve',at:10};
  run.automaticOrigin={repository:run.repo,coordinatorId:'owner',machine:'machine',claim:{commentId:'11',labelEventId:'12'}};
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  const release=acquireRunLock(run.runDir); t.after(release);
  const result=await cancelRun({ref:'17',cwd:f.source,expectGate:'old'},f.ports);
  assert.equal(result.exitCode,3,result.message); assert.match(result.message,/new/);
});
