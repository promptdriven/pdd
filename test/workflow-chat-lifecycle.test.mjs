import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import * as runner from '../src/workflow-runner.mjs';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';
const open = runner.openRunCommand ?? runner.openRun;
for (const agent of ['claude','codex']) {
  test(`${agent}: starting owner is durable before initial native dispatch`, async t => {
    const f=await fixture(t,{agent});
    if(agent==='codex'){const d=`${f.base}/codexhome`;mkdirSync(d);f.ports.env.CODEX_HOME=d;}
    let observed;
    const healthy=f.herdr.herdr;
    f.ports.herdr=async args=>{
      if(args[0]==='pane'&&args[1]==='run'){
        const record=f.record(); observed=record.chats.find(c=>c.area===record.areas[record.area].name);
        throw Object.assign(Error('reply lost'),{code:'server_unavailable'});
      }
      return healthy(args);
    };
    await f.run();
    assert.ok(observed,'Starting chat identity is saved before dispatch');
    assert.equal(observed.state,'starting');
    assert.equal(observed.startedAt,f.clock);
  });
  for(const elapsed of [0,29_999,30_000]) test(`${agent}: absent startup evidence at ${elapsed} ms stays starting in status and open`,async t=>{
    const f=await fixture(t,{agent});
    if(agent==='codex'){const d=`${f.base}/codexhome`;mkdirSync(d);f.ports.env.CODEX_HOME=d;}
    const healthy=f.herdr.herdr;
    f.ports.herdr=async args=>{
      if(args[0]==='pane'&&args[1]==='run')throw Object.assign(Error('reply lost'),{code:'server_unavailable'});
      return healthy(args);
    };
    await f.run();f.tick(elapsed);
    f.ports.sleep=async ms=>f.tick(ms);
    f.ports.findNativeSessions=async()=>[];
    const before=f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length;
    const status=await runner.runStatus({ref:'17',cwd:f.source},f.ports);
    const result=await open({ref:'17',cwd:f.source,packageRoot},f.ports);
    const record=f.record(),chat=record.chats.find(c=>c.area===record.areas[record.area].name);
    assert.ok(chat,'Unconfirmed chat custody remains saved');
    assert.equal(chat.state,'starting');
    assert.match(result.message,/starting, not confirmed/);
    assert.doesNotMatch(`${status.message}\n${result.message}`,/chat stopped|chat ended|start it yourself/);
    assert.equal(f.herdr.calls.filter(a=>a[0]==='pane'&&a[1]==='run').length,before,'Unconfirmed open neither launches nor resumes');
  });
}

for(const state of ['ended','failed'])test(`positive ${state} evidence survives temporarily unavailable Herdr`,async t=>{
  const f=await fixture(t);await f.run();const run=f.record(),chat=run.chats.at(-1);assert.ok(chat);
  chat.state=state;
  if(state==='ended')chat.evidence={kind:'session-end',at:f.clock,sessionId:chat.session.id};
  else chat.code='launch_refused';
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  f.ports.herdr=async()=>{throw Object.assign(Error('temporarily unavailable'),{code:'server_unavailable'});};
  await runner.runStatus({ref:'17',cwd:f.source},f.ports);
  const after=f.record().chats.at(-1);assert.equal(after.state,state);
  if(state==='ended')assert.deepEqual(after.evidence,chat.evidence);else assert.equal(after.code,'launch_refused');
});
test('positive live session confirms the same starting chat as running',async t=>{
  const f=await fixture(t);await f.run();const run=f.record(),chat=run.chats.at(-1);assert.ok(chat);
  chat.state='starting';writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  await runner.runStatus({ref:'17',cwd:f.source},f.ports);
  const after=f.record().chats.at(-1);assert.equal(after.state,'running');assert.deepEqual(after.session,chat.session);
});
