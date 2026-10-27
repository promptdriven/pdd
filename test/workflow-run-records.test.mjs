import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { runStatusFromState, writeRunStatus, readRunStatus, normalizeRunLinks } from '../src/workflow-run-records.mjs';
const runId='01234567-89ab-4cde-8f01-23456789abcd';
const state=()=>({runId,name:'small-change',seq:7,agent:'codex',root:'/work/project',index:1,
  definitions:[{id:'scope',kind:'agent'},{id:'change',kind:'agent'},{id:'verify',kind:'agent'}],
  completed:[{id:'scope',kind:'agent',startedAt:10,endedAt:20,backend:{agent:'codex',nativeSession:{kind:'id',value:'scope-session'}}}],
  pending:{kind:'agent',stage:'change',startedAt:30,backend:{agent:'codex',nativeSession:{kind:'id',value:'change-session'}}}});
test('C3 attributes each session and timing only to its own step',()=>{
  const s=state(),before=structuredClone(s),out=runStatusFromState(s,{phase:'record',now:40});
  assert.equal(out.v,1);assert.equal(out.journalSeq,7);assert.equal(out.state,'running');
  assert.deepEqual(out.steps.map(x=>[x.state,x.startedAt,x.endedAt,x.session]),[
    ['done',10,20,{agent:'codex',id:'scope-session'}],['current',30,null,{agent:'codex',id:'change-session'}],['next',null,null,null]]);
  assert.deepEqual(s,before);
});
test('next-advance, human, optional and merge expose distinct waiting choices',()=>{
  const s=state();s.pending=null;s.proposal={approval:'next-advance'};
  const project=()=>runStatusFromState(s,{phase:'exit',outcome:{state:'waiting'}});
  assert.deepEqual(project().waitingFor.decisions,['approve']);
  s.accepted={};s.definitions[1]={id:'review',kind:'human'};assert.deepEqual(project().waitingFor.decisions,['approve']);
  s.definitions[1]={id:'extra',kind:'agent',optional:true};assert.deepEqual(project().waitingFor.decisions,['approve','skip']);
  s.definitions[1]={id:'merge',kind:'merge'};assert.deepEqual(project().waitingFor.decisions,[]);
  s.waitingPerson={decisions:['approve','changes','invalid'],what:'Revise this plan'};
  assert.deepEqual(project().waitingFor,{decisions:['approve','changes'],what:'Revise this plan'});
  delete s.waitingPerson;delete s.accepted;s.index=s.definitions.length;
  assert.deepEqual(runStatusFromState(s).resumeDecisions,[]);
});
test('C3 bounds links and changes and preserves saved approval evidence',()=>{
  const s=state();s.links=Array.from({length:25},(_,n)=>({stage:'scope',kind:'check',url:`https://example.test/${n}`,verdict:'passed'}));
  s.links.push({stage:'scope',kind:'try',url:'https://example.test',verdict:'passed'});
  s.changes=Array.from({length:7},(_,n)=>({stage:'scope',round:n,text:'x'.repeat(4010),at:n}));
  s.approvalRecord={source:'chat',sessionId:'human-session',text:'I approve',at:50};
  const out=runStatusFromState(s);assert.equal(out.links.length,20);assert.equal(out.links[0].url,'https://example.test/5');
  assert.equal(out.changes.length,5);assert.equal(out.changes[0].round,2);assert.equal(out.changes[0].text.length,4000);
  assert.deepEqual(out.approvalRecord,s.approvalRecord);out.approvalRecord.text='changed';assert.equal(s.approvalRecord.text,'I approve');
  assert.deepEqual(normalizeRunLinks([{stage:'a',kind:'check',url:'https://user:password@example.test',verdict:null}]),[]);
});
test('legacy or malformed observations never invent progress or native identity',()=>{
  const s=state();delete s.completed[0].backend;delete s.completed[0].startedAt;s.pending=null;
  assert.equal(runStatusFromState(s).state,'unknown');assert.equal(runStatusFromState(s).steps[0].session,null);
  assert.equal(runStatusFromState(s).steps[0].startedAt,null);
  assert.deepEqual(runStatusFromState(null).steps,[]);assert.equal(runStatusFromState({index:0,definitions:'bad'}).stage,null);
});
async function directory(t){const root=await fs.mkdtemp(join(tmpdir(),'pdd-status-'));t.after(()=>fs.rm(root,{recursive:true,force:true}));const dir=join(root,runId);await fs.mkdir(dir);return dir;}
test('atomic status is private, whole and readable with matching run identity',async t=>{
  const dir=await directory(t),value=runStatusFromState(state());assert.deepEqual(await writeRunStatus(dir,value),{ok:true});
  assert.equal((await fs.stat(join(dir,'status.json'))).mode&0o777,0o600);
  assert.deepEqual((await readRunStatus(dir)).value,value);assert.deepEqual(await fs.readdir(dir),['status.json']);
});
test('failed replacement and oversized data preserve prior status and journal',async t=>{
  const dir=await directory(t),value=runStatusFromState(state());await writeRunStatus(dir,value);
  await fs.writeFile(join(dir,'journal.jsonl'),'owned journal\n');const before=await fs.readFile(join(dir,'status.json'),'utf8');
  const result=await writeRunStatus(dir,{...value,journalSeq:9},{fs:{...fs,rename:async()=>{throw Object.assign(Error('disk'),{code:'EIO'});}}});
  assert.deepEqual(result,{ok:false,code:'EIO'});assert.equal(await fs.readFile(join(dir,'status.json'),'utf8'),before);
  assert.equal((await writeRunStatus(dir,{large:'x'.repeat(256*1024)})).code,'too_large');
  assert.equal(await fs.readFile(join(dir,'journal.jsonl'),'utf8'),'owned journal\n');assert.deepEqual((await fs.readdir(dir)).sort(),['journal.jsonl','status.json']);
});
test('status writer refuses aliased run directories and reader rejects a foreign run',async t=>{
  const dir=await directory(t),alias=dir+'-alias';await fs.symlink(dir,alias);
  assert.equal((await writeRunStatus(alias,runStatusFromState(state()))).ok,false);
  await fs.writeFile(join(dir,'status.json'),JSON.stringify({v:1,runId:'other',journalSeq:1}));
  assert.equal((await readRunStatus(dir)).value,null);
});
test('phone fields retain issue number, cancellation and actual Herdr identity',()=>{
  const s=state();s.issue={number:45};s.cancelled={state:'cancelled',at:60};s.herdr={session:'pdd',workspaceId:'w3',label:'project'};
  const out=runStatusFromState(s);assert.equal(out.number,45);assert.deepEqual(out.cancelled,{state:'cancelled',at:60});
  assert.deepEqual(out.herdr,s.herdr);delete s.cancelled;delete s.herdr;
  assert.equal(runStatusFromState(s).cancelled,null);assert.equal(Object.hasOwn(runStatusFromState(s),'herdr'),false);
  s.pending.backend.session='pdd';s.pending.backend.workspaceId='w4';s.pending.backend.workspaceName='owner/project';
  assert.deepEqual(runStatusFromState(s).herdr,{session:'pdd',workspaceId:'w4',label:'owner/project'});
  s.completed[0].backend={session:'pdd',workspaceId:'w1'};s.pending.backend={session:'pdd',phase:'server_intent'};
  assert.deepEqual(runStatusFromState(s).herdr,{session:'pdd',workspaceId:'w1',label:null});
});
test('phone decisions normalize current binding evidence and already normalized area decisions',()=>{
  const s=state();s.decisions=Array.from({length:7},(_,at)=>({decisionId:`d${at}`,binding:{decision:'approve',expectStage:'scope'},approvalRecord:{kind:'terminal'},at}));
  s.decisions.push({stage:'plan',decision:'changes',via:'chat',at:7,text:'Please simplify'});
  s.decisions.push({binding:{decision:'skip',expectStage:'optional'},approvalRecord:{kind:'phone',phoneId:'phone-one'},at:8});
  const out=runStatusFromState(s);assert.equal(out.decisions.length,5);assert.equal(out.decisions[0].at,4);
  assert.deepEqual(out.decisions.slice(-2),[{stage:'plan',decision:'changes',via:'chat',at:7,text:'Please simplify'},
    {stage:'optional',decision:'skip',via:'phone',at:8,phoneId:'phone-one'}]);
  assert.deepEqual(out.decisions[0],{stage:'scope',decision:'approve',via:'terminal',at:4});
});
