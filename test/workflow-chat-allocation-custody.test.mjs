import test from 'node:test';
import assert from 'node:assert/strict';
import {openRun} from '../src/workflow-runner.mjs';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';

test('lost allocation never adopts a matching unknown peer beside a relabelled allocation',async t=>{
 const f=await fixture(t);assert.equal((await f.run()).exitCode,0);
 const healthy=f.ports.herdr;
 f.ports.herdr=async args=>{
  const reply=await healthy(args);
  if(args[0]==='tab'&&args[1]==='create')throw Object.assign(Error('lost allocation reply'),{code:'server_unavailable'});
  return reply;
 };
 const open=()=>openRun({ref:'17',cwd:f.source,packageRoot,newSession:true},f.ports);
 assert.equal((await open()).exitCode,1);
 const before=f.record(),pending=before.chatReplacement;
 assert.equal(pending.phase,'createRequested');
 const allocated=f.herdr.tabs.find(tab=>tab.label==='plan');assert.ok(allocated);
 const pane=f.herdr.panes.find(row=>row.tab_id===allocated.tab_id);assert.ok(pane);
 allocated.label='other';
 f.herdr.tabs.push({...allocated,tab_id:'unknown-peer-tab',label:'plan'});
 f.herdr.panes.push({...pane,tab_id:'unknown-peer-tab',pane_id:'unknown-peer-pane',terminal_id:'unknown-peer-terminal'});
 f.ports.herdr=healthy;
 const effects=()=>f.herdr.calls.filter(args=>args[0]==='tab'&&args[1]==='create'||args[0]==='pane'&&args[1]==='run');
 const count=effects().length;
 const out=await open();
 assert.equal(out.exitCode,1,'Ambiguous allocation custody must refuse rather than adopt an unknown peer');
 assert.equal(effects().length,count,'Retry must neither allocate nor dispatch');
 const after=f.record();
 assert.deepEqual(after.chatReplacement,pending,'Exact pending attempt and native identity must remain in custody');
 assert.deepEqual(after.chats,before.chats,'Saved chats must not adopt the unknown peer');
 assert.deepEqual(after.abandonedChats,before.abandonedChats);
});
