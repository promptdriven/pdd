import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, readdirSync, statSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {approveRun, changeRun, cancelRun, openRun, stepDone} from '../src/workflow-runner.mjs';
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
