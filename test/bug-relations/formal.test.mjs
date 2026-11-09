import { test } from 'node:test';
import assert from 'node:assert/strict';
import { applyReproducedBugRelations } from '../../src/issue-dependencies-github.mjs';
const key = n => `https://github.com/owner/repo/issues/${n}`;
const rel = (effect,classification='duplicate') => ({issue:2,classification,quote:'quote',source:{kind:'issue',repository:'owner/repo',issue:2,revision:'v'},effect});
const input = (...relations) => ({repository:'owner/repo',issue:1,relations});
const event = (type,id='event',actor='writer') => ({__typename:type,id,actor:{login:actor},createdAt:'2026-01-01T00:00:01Z',canonical:{url:key(2)},duplicate:{url:key(1)}});
function fixture() {
  const x={writes:[],events:[],edges:[],history:[],sub:'absent',state:null,fail:false,claim:true,complete:true};
  x.ports={github:{issue:async ({issue})=>({json:JSON.stringify({id:issue,html_url:key(issue),state:'open',title:issue===3?'Class: Test':'Bug'})}),page:async()=>({json:JSON.stringify({items:x.history,next:''})}),duplicateActor:async()=> 'writer',duplicateTimeline:async()=>x.events,markDuplicate:async a=>{x.writes.push(a);if(x.fail) throw Error('lost');x.events=[event('MarkedAsDuplicateEvent')];},relationSubIssueState:async()=>x.sub,ensureSortLink:async a=>{x.writes.push(a);x.sub='present';},addBlocker:async a=>{x.writes.push(a);x.edges.push({dependent:key(a.issue),blocker:key(Number(a.blockerId))});}},evidence:{read:async()=>({json:JSON.stringify({requirements:[{key:key(2),revision:'v',text:'quote',authority:'trusted'}]})})},owners:{read:async()=>({json:JSON.stringify({localOwner:'owner',claims:x.claim?[{issue:key(1),active:true,owner:'owner',coordinatorId:'owner',machine:'machine',commentId:'1',labelEventId:'2'}]:[]})})},relationClaim:{coordinatorId:'owner',machine:'machine',commentId:'1',labelEventId:'2'},clock:{now:async()=>({iso:'2026-01-01T00:00:00Z'})},settings:{read:async()=>({mode:'auto'})},checkpoint:{read:async()=>x.state,write:async v=>{x.state=v;}},relationSnapshot:{read:async()=>({repository:'owner/repo',complete:x.complete,issues:[1,2,3].map(n=>({key:key(n),state:'open',conditions:[],holds:[]})),edges:x.edges,reviews:[],impacts:[],inputs:[]})}};
  return x;
}
const invoke=(x,...r)=>applyReproducedBugRelations(input(...r),x.ports);
const dup=()=>rel({kind:'duplicate',duplicate:1,canonical:2});
const dep=()=>rel({kind:'blocked-by',dependent:1,blocker:2},'needs');
const sub=()=>rel({kind:'sub-issue',parent:3,child:1},'same class');

test('bounded relation permission and current evidence', async () => {
  let cases=0;
  for (const classification of ['needs','same cause','same class','duplicate','related'])
    for (const effect of ['none','blocked-by'])
      for (const evidence of ['valid','missing','changed','untrusted','unavailable']) {
        const x=fixture();
        if(evidence!=='valid') x.ports.evidence.read=async()=>{
          if(evidence==='unavailable') throw Error('offline');
          return {json:JSON.stringify({requirements:evidence==='missing'?[]:[{key:key(2),revision:evidence==='changed'?'other':'v',text:'quote',authority:evidence==='untrusted'?'outsider':'trusted'}]})};
        };
        const r=rel(effect==='none'?{kind:'none'}:{kind:'blocked-by',dependent:1,blocker:2},classification);
        const actual=(await invoke(x,r)).outcomes[0].status;
        const expected=evidence!=='valid'?'held':effect==='none'?'none':classification==='needs'?'applied':'held';
        assert.equal(actual,expected,JSON.stringify({classification,effect,evidence}));
        assert.equal(x.writes.length,expected==='applied'?1:0,JSON.stringify({classification,effect,evidence}));
        cases++;
      }
  assert.equal(cases,50);
});
test('bounded dependency prohibitions', async () => {
  let cases=0;
  for(const cycle of [false,true]) for(const removed of [false,true]) for(const complete of [false,true]) {
    const x=fixture();
    if(cycle)x.edges=[{dependent:key(2),blocker:key(1)}];
    if(removed)x.history=[{event:'blocked_by_removed',blocked_by:{html_url:key(2)}}];
    x.complete=complete;
    const expected=cycle||removed||!complete?'held':'applied';
    assert.equal((await invoke(x,dep())).outcomes[0].status,expected,JSON.stringify({cycle,removed,complete}));
    assert.equal(x.writes.length,expected==='applied'?1:0);
    cases++;
  }
  assert.equal(cases,8);
});
test('bounded duplicate recovery preserves human undo and never resends unknown dispatch',async()=>{
  for(const initial of ['unmarked','unknown']) {
    const x=fixture();
    if(initial==='unmarked')x.events=[event('UnmarkedAsDuplicateEvent')];
    else x.fail=true;
    const expected=initial==='unmarked'?'held':'unknown';
    assert.equal((await invoke(x,dup())).outcomes[0].status,expected);
    assert.equal((await invoke(x,dup())).outcomes[0].status,expected);
    assert.equal(x.writes.length,initial==='unmarked'?0:1);
  }
});

 test('bounded failed reproductions never retain a guessed cause', async t=>{
  const {fixture: workflowFixture}=await import('../helpers/workflow-delivery-fixture.mjs');
  const {stepDone}=await import('../../src/workflow-runner.mjs');
  const {writeFileSync,mkdirSync}=await import('node:fs'); const {join}=await import('node:path');
  for(const search of ['complete','unavailable']) for(const guessed of [false,true]) {
    const f=await workflowFixture(t,{name:'bug',agent:'codex'}); const skill=join(f.source,'.agents/skills/pdd-bug');mkdirSync(skill,{recursive:true});
    writeFileSync(join(skill,'workflow.json'),JSON.stringify({version:2,areas:[{name:'story',steps:['reproduce','check'],optional:[],gate:'pr'}]}));
    assert.equal((await f.run()).exitCode,0);const run=f.record();
    const input={version:1,runId:run.runId,repository:run.repo,issue:run.number,reproduced:false,cause:guessed?{file:'value.mjs',function:'value',flaw:'Value is wrong.',class:'Wrong value'}:null,search,relations:[]};
    writeFileSync(join(run.runDir,'bug-findings.json'),JSON.stringify(input));let calls=0;
    const result=await stepDone({step:'reproduce',summary:'Observed.',cwd:run.root},f.agentPorts({applyReproducedBugRelations:async()=>{calls++;}}));
    assert.equal(result.exitCode,guessed?1:0,JSON.stringify({search,guessed}));assert.equal(calls,0);
    if(!guessed)assert.equal(f.record().bugFindings.input.cause,null);
  }
});
