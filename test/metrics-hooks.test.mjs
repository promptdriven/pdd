import './helpers/test-home.mjs';
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { journalRunMutation, drainRunJournal } from '../src/metrics-hooks.mjs';

const at = '2026-11-05T10:00:00.000Z';
const base = {runId:'run-1',repo:'Owner/Repo',number:3,areas:[{name:'code',steps:['build','verify']}],done:{build:{at,summary:'private transcript'}}};
const journal = (before,after,id,observations=[]) => journalRunMutation({before,after,source:'install:one',observedAt:at,transitionId:id,observations});

test('rerun retains replaced and cleared completions without private content', () => {
  const before = {...base,done:{...base.done,verify:{at,summary:'secret'}}};
  const after = {...base,done:{build:{at:'2026-11-05T11:00:00.000Z',skipped:true,summary:'another secret'}}};
  const saved = journal(before,after,'change-1');
  assert.deepEqual(saved.metrics.events.map(e=>[e.data.step,e.data.status,e.at]),[['build','done',at],['verify','done',at],['build','skipped','2026-11-05T11:00:00.000Z']]);
  assert.equal(JSON.stringify(saved.metrics).includes('secret'),false);
  assert.ok(saved.metrics.events.every(e=>e.attempt==='run-1' && e.repo==='owner/repo'));
  const replay = journal(saved,saved,'change-2');
  assert.equal(replay.metrics.events.length,3);
});

test('explicit confirmed start and candidate facts survive failed delivery and retry unchanged', async () => {
  const saved = journal(null,{...base,done:{}},'transition-1',[
    {type:'start',at,data:{origin:'autopilot',decisionId:'decision-1',cliVersion:'1.0'}},
    {type:'milestone',at,data:{stage:'implementation-ready',pr:17,head:'abc'}}
  ]);
  const original = structuredClone(saved.metrics.events);
  assert.equal((await drainRunJournal({run:saved,root:'repo',store:{appendEvents:async()=>{throw Error('offline');}}})).ok,false);
  const batches=[];
  const store={appendEvents:async ({events})=>batches.push(structuredClone(events))};
  assert.deepEqual(await drainRunJournal({run:saved,root:'repo',store}),{ok:true,count:2});
  await drainRunJournal({run:saved,root:'repo',store});
  assert.deepEqual(batches,[original,original]);
  assert.deepEqual(saved.metrics.events,original);
});
