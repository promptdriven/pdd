import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync, mkdirSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {ownSession} from '../src/workflow-chat.mjs';
import {findNativeSessions} from '../src/approval-evidence.mjs';
import {openRun} from '../src/workflow-runner.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/gemini-session-recovery.json',import.meta.url),'utf8'));
test('Gemini recovery Story vectors replay against native public operations', async t => {
  const f = await fixture(t,{agent:'gemini'});
  assert.equal((await f.run()).exitCode,0);
  const chat = f.record().chats.at(-1);
  const saved = f.record();
  Object.assign(saved.chats.at(-1),scenario.initial_world.kv.workflowChat);
  writeFileSync(join(saved.runDir,'status.json'),JSON.stringify(saved));
  f.herdr.paneOf(chat).agent = null;
  f.tick(31_000); delete f.ports.findNativeSessions;
  const snapshots = new Map();
  for(const [index,session] of scenario.initial_world.kv.nativeSessions.entries()) {
    const hash = createHash('sha256').update(session.root).digest('hex');
    const dir = join(f.ports.env.HOME,'.gemini','tmp',hash,'chats'); mkdirSync(dir,{recursive:true});
    const file = join(dir,`session-${index}.${session.format}`);
    const data = JSON.stringify({sessionId:session.id,projectHash:hash,startTime:new Date(session.startedAt).toISOString(),kind:'main',messages:[]})+(session.format==='jsonl'?'\n':'');
    writeFileSync(file,data); snapshots.set(file,data);
  }
  for(const step of scenario.steps) await t.test(step.step_id,async()=>{
    let actual;
    if(step.operation==='ownSession') actual = await ownSession({...step.input,ports:f.ports});
    else if(step.operation==='findNativeSessions') actual = await findNativeSessions(step.input,f.ports);
    else if(step.operation==='openRun') actual = await openRun({...step.input,cwd:f.source,packageRoot},f.ports);
    else assert.fail(`Unmapped public operation ${step.operation}`);
    for(const check of step.checks) {
      assert.equal(check.target,'result'); assert.equal(check.op,'equals');
      const value = check.path === '' ? actual : check.path.slice(1).split('/').reduce((obj,key)=>obj?.[key],actual);
      assert.deepEqual(value,check.value,`${step.step_id} ${check.criterion_id} ${check.path}`);
    }
    for(const [file,bytes] of snapshots) assert.equal(readFileSync(file,'utf8'),bytes,'Native history remains unchanged');
  });
});
