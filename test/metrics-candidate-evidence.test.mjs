import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {calculateMetrics} from '../src/metrics-model.mjs';
const at = n => `2026-11-0${n}T00:00:00Z`;
const event = (id,type,data,n=1,source='a') => ({schema:'pdd.metrics.event.v1',id,repo:'a/b',issue:1,type,data,at:at(n),observedAt:at(n),source});
const run = events => calculateMetrics({events,repo:'a/b',scope:{kind:'snapshot',snapshotId:'s'},timezone:'UTC',observedAt:at(9),sources:[]}).issues[0];
const select=event('s','selection',{snapshotId:'s',inScope:true,state:'ready'});
const ready=event('r','milestone',{stage:'implementation-ready',pr:2,head:'code'});
const check=(id,verdict,acceptance,n,source='a',reviewer=id)=>event(id,'check',{pr:2,head:'code',verdict,acceptance,reviewer,evidence:'link'},n,source);
test('unknown acceptance and prompt heads cannot establish a negative or displace code',()=>{
 const issue=run([select,ready,event('prompt','milestone',{stage:'candidate-head',pr:1,head:'prompt'},3),check('f','FAIL','unknown',4)]);
 assert.equal(issue.candidate.data.pr,2); assert.equal(issue.validated,'unknown');
});
test('cross-source split stays unknown until two accepted later reviewers agree',()=>{
 const rows=[select,ready,check('f','FAIL','accepted',2,'one'),check('p','PASS','accepted',3,'two')];
 assert.equal(run(rows).validated,'unknown');
 assert.equal(run([...rows,check('p2','PASS','accepted',4,'three')]).validated,'unknown');
 const structured = (id,n,source,family) => ({...check(id,'PASS','accepted',n,source,`${family}:session-${Buffer.from(id).toString('base64url')}`),data:{...check(id,'PASS','accepted',n,source).data,reviewer:`${family}:session-${Buffer.from(id).toString('base64url')}`,checkerFamily:family,checkerMode:'different-family'}});
 assert.equal(run([...rows,structured('p3',4,'three','codex'),structured('p4',5,'four','claude')]).validated,'yes');
});

test('a later retry supersedes a historical attempt and code PR head survives missing readiness',()=>{
 const old={...ready,attempt:'old'};
 const mapping={...event('mapping','milestone',{stage:'code-pr',pr:3},3),attempt:'new'};
 const head=event('head','milestone',{stage:'candidate-head',pr:3,head:'new'},4);
 const cancel={...event('cancel','step',{step:'cancel',status:'done'},2),attempt:'old'};
 const issue=run([select,old,cancel,mapping,head]);
 assert.equal(issue.candidate.data.pr,3); assert.equal(issue.candidate.data.head,'new');
 assert.equal(issue.validated,'unknown');
});

test('simultaneous active attempts cannot borrow readiness or select by time',()=>{
 const a={...ready,attempt:'a'};
 const b={...event('b','milestone',{stage:'code-pr',pr:2,head:'code'},3),attempt:'b'};
 assert.equal(run([select,a,b]).candidate,null);
 assert.equal(run([select,a,b]).validated,'unknown');
 const cancel={...event('cancel','step',{step:'cancel',status:'done'},4),attempt:'a'};
 const issue=run([select,a,b,cancel]);
 assert.equal(issue.candidate.attempt,'b'); assert.equal(issue.implementationReady,'unknown');
});

test('unscoped PR updates retain the active attempt and cannot borrow closed readiness',()=>{
 for (const terminal of [event('cancel','step',{step:'cancel',status:'done'},2),event('supersede','outcome',{status:'superseded'},2)]) {
  const old={...ready,attempt:'old'};
  const active={...event('active','milestone',{stage:'code-pr',pr:2,head:'code'},3),attempt:'new'};
  const unscoped=event('unscoped','milestone',{stage:'code-pr',pr:2,head:'code'},4);
  const rows=[select,old,{...terminal,attempt:'old'},active,unscoped];
  assert.equal(run(rows).implementationReady,'unknown');
  assert.equal(run([...rows,{...event('new-ready','milestone',{stage:'implementation-ready',pr:2,head:'code'},5),attempt:'new'}]).implementationReady,'yes');
  assert.equal(run([select,old,active,unscoped]).implementationReady,'unknown');
 }
});

test('acceptance observations retain known evidence at each cutoff',()=>{
 const accepted=check('same','PASS','accepted',2);
 const unknown={...accepted,observedAt:at(4),data:{...accepted.data,acceptance:'unknown'}};
 const calc=(events,observedAt)=>calculateMetrics({events,repo:'a/b',scope:{kind:'snapshot',snapshotId:'s'},timezone:'UTC',observedAt,sources:[]}).issues[0];
 assert.equal(calc([select,ready,accepted,unknown],at(3)).validated,'yes');
 assert.equal(calc([select,ready,accepted,unknown],at(5)).validated,'yes');
 const reverse={...unknown,observedAt:at(2)};
 const laterAccepted={...accepted,observedAt:at(4)};
 assert.equal(calc([select,ready,reverse,laterAccepted],at(3)).validated,'unknown');
 assert.equal(calc([select,ready,reverse,laterAccepted],at(5)).validated,'yes');
 const opposing=check('opposing','FAIL','accepted',5);
 assert.equal(calc([select,ready,accepted,unknown,opposing],at(6)).validated,'unknown');
 const changed=event('head','milestone',{stage:'head',pr:2,head:'other'},5);
 assert.equal(calc([select,ready,accepted,unknown,changed],at(6)).validated,'unknown');
});

test('unscoped observations cannot displace the selected attempt or borrow its predecessors readiness',()=>{
 for (const closed of ['cancelled','superseded','active']) for (const same of [true,false]) for (const stage of ['code-pr','candidate-head']) for (const newReady of [false,true]) {
  const old={...ready,attempt:'old'};
  const terminal=closed === 'active' ? [] : [{...event('terminal','outcome',{status:closed},2),attempt:'old'}];
  const active={...event('active','milestone',{stage:'code-pr',pr:same?2:3,head:'code'},3),attempt:'new'};
  const update=event('update','milestone',{stage,pr:2,head:'code'},4);
  const currentReady={...event('current-ready','milestone',{stage:'implementation-ready',pr:same?2:3,head:'code'},5),attempt:'new'};
  const pass=event('pass','check',{pr:same?2:3,head:'code',verdict:'PASS',acceptance:'accepted',reviewer:'reviewer',evidence:'link'},6);
  const issue=run([select,old,...terminal,active,update,...(newReady?[currentReady]:[]),pass]);
  const label=`${closed} ${same} ${stage} ${newReady}`;
  if (closed === 'active') { assert.equal(issue.candidate,null,label); assert.equal(issue.validated,'unknown',label); }
  else { assert.equal(issue.candidate.data.pr,same?2:3,label); assert.equal(issue.implementationReady,newReady?'yes':'unknown',label); assert.equal(issue.validated,'yes',label); }
 }
});

test('a changed selected head invalidates readiness and checks while legacy unscoped records remain supported',()=>{
 const old={...ready,attempt:'old'};
 const close={...event('close','outcome',{status:'cancelled'},2),attempt:'old'};
 const active={...event('active','milestone',{stage:'implementation-ready',pr:3,head:'before'},3),attempt:'new'};
 const changed=event('change','milestone',{stage:'candidate-head',pr:3,head:'after'},4);
 const stale=event('stale','check',{pr:3,head:'before',verdict:'PASS',acceptance:'accepted',reviewer:'r',evidence:'link'},5);
 const issue=run([select,old,close,active,changed,stale]);
 assert.equal(issue.candidate.data.head,'after'); assert.equal(issue.implementationReady,'unknown'); assert.equal(issue.validated,'unknown');
 assert.equal(run([select,ready,check('legacy','PASS','accepted',2)]).validated,'yes');
 const unscoped=event('unscoped','milestone',{stage:'code-pr',pr:2,head:'code'},4);
 const orphan=run([select,old,close,unscoped,check('orphan','PASS','accepted',5)]);
 assert.equal(orphan.candidate.data.pr,2); assert.equal(orphan.implementationReady,'unknown'); assert.equal(orphan.validated,'unknown');
});

test('fresh accepted current candidate result is independent of missing readiness and start',()=>{
 const candidate=event('candidate','milestone',{stage:'code-pr',pr:2,head:'code'});
 const issue=run([select,candidate,check('pass','PASS','accepted',2)]);
 assert.equal(issue.validated,'yes'); assert.equal(issue.implementationReady,'unknown'); assert.equal(issue.started,'unknown');
 const changed=event('changed','milestone',{stage:'candidate-head',pr:2,head:'new'},3);
 assert.equal(run([select,candidate,check('pass','PASS','accepted',2),changed]).validated,'unknown');
 assert.equal(run([select,candidate,check('pass','PASS','unknown',2)]).validated,'unknown');
 assert.equal(run([select,check('pass','PASS','accepted',2)]).validated,'unknown');
});

test('case variants of one checker family cannot resolve a split as different families',()=>{
 const structured=(id,verdict,family,n)=>({...check(id,verdict,'accepted',n,id,`${family}:session-${Buffer.from(id).toString('base64url')}`),data:{...check(id,verdict,'accepted',n).data,reviewer:`${family}:session-${Buffer.from(id).toString('base64url')}`,checkerFamily:family,checkerMode:'different-family'}});
 const rows=[select,ready,structured('fail','FAIL','claude',2),structured('pass-a','PASS','codex',3),structured('pass-b','PASS','CODEX',4)];
 assert.equal(run(rows).validated,'unknown');
 assert.equal(run([...rows,structured('pass-c','PASS','claude',5)]).validated,'yes');
});
