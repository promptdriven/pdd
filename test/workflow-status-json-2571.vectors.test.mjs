import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { runStatus } from '../src/workflow-runner.mjs';
import { fixture } from './helpers/workflow-runner-fixture.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/workflow-status-json-2571.json', import.meta.url)));

test('2571 scenario replay: empty machine list', async t => {
  const f = await fixture(t);
  for (const step of scenario.steps) {
    const result = await runStatus({...step.input, cwd:f.source}, f.ports);
    for (const check of step.checks) {
      assert.equal(check.target, 'result');
      const actual = check.path.slice(1).split('/').reduce((v,k) => v?.[k], result);
      if (check.op === 'equals') assert.deepEqual(actual, check.value);
      else if (check.op === 'contains') assert.ok(actual.includes(check.value));
      else assert.fail(`Unsupported operation ${check.op}`);
    }
  }
});

test('2571 list projection preserves useful state and redacts private text', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
  const path = join(f.source, '.git/pdd/runs/17/status.json');
  const record = f.record();
  record.issue.title = 'See https://runtime.example/s/secret/';
  record.question = {text:'Review https://runtime.example/s/private/', at: 99};
  record.gate = {kind:'approve-pr', area:record.areas[record.area].name, at: 1};
  record.pr = [{number:23,url:'https://github.com/example/project/pull/23',state:'open',draft:true,ci:'passing', raw:'private metadata'}];
  record.chats.at(-1).secret = 'private metadata';
  writeFileSync(path, JSON.stringify(record));
  const result = await runStatus({cwd:f.source,all:true,json:true}, {...f.ports, readPrStatus:async()=>({state:'open',draft:true,ci:'passing'}), herdr:async()=>{throw Error('unavailable');}});
  const data = JSON.parse(result.message), row = data.runs[0];
  assert.equal(data.version, 1); assert.equal(row.ref,'example/project#17');
  assert.deepEqual(row.prs,[{number:23,url:'https://github.com/example/project/pull/23',state:'open',draft:true,ci:'passing'}]);
  assert.equal(row.waiting.kind,'question'); assert.equal(row.waiting.gate,null);
  assert.equal(row.chat.session,'pdd'); assert.equal(row.chat.pane,row.chat.paneId);
  assert.ok(!result.message.includes('/s/secret')); assert.ok(!result.message.includes('/s/private'));
  assert.ok(!result.message.includes('private metadata')); assert.ok(!('chats' in row)); assert.ok(!('steps' in row));
  const old = JSON.parse((await runStatus({cwd:f.source,ref:'17',json:true},f.ports)).message);
  assert.equal(old.version,undefined); assert.ok(Array.isArray(old.runs[0].chats));
});

test('2571 waiting precedence, gate identity and absence of observation', async t => {
  const f = await fixture(t); assert.equal((await f.run()).exitCode,0);
  const path = join(f.source, '.git/pdd/runs/17/status.json');
  const initial = f.record(), area = initial.areas[initial.area].name;
  const status = async change => {
    const run = structuredClone(initial); change(run); writeFileSync(path, JSON.stringify(run));
    return JSON.parse((await runStatus({cwd:f.source,all:true,json:true}, {...f.ports, herdr:async()=>{throw Error('unavailable');}})).message).runs[0];
  };
  const gate = await status(run => {run.gate={id:'gate-1',kind:'approve-pr',area,at:1};});
  assert.deepEqual(gate.waiting,{kind:'gate',gate:'gate-1',question:null,reason:null});
  const startup = await status(run => {run.gate={id:'gate-1',kind:'approve-pr',area,at:1};run.question={text:'Q?',at:2};run.chatFailure={area,phase:'open',code:'failed',message:'failure',at:3};});
  assert.deepEqual(startup.waiting,{kind:'startup_failed',gate:null,question:null,reason:null});
  const noObservation = await status(run => {run.gate=null;run.question=null;});
  assert.equal(noObservation.waiting,null);
});
