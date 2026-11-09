import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { applyReproducedBugRelations } from '../../src/issue-dependencies-github.mjs';
const plan = JSON.parse(await readFile(new URL('./bug-relation-links-cases.json',import.meta.url)));
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
for (const c of plan.cases) assert.ok(c.id);
test('dependency',async()=>{const x=fixture();assert.equal((await invoke(x,dep())).outcomes[0].status,'applied');assert.deepEqual(x.writes.map(a=>[a.issue,a.blockerId]),[[1,'2']]);});
test('class',async()=>{const x=fixture();assert.equal((await invoke(x,sub())).outcomes[0].status,'applied');assert.equal(x.writes[0].kind,'sub');});
test('duplicate',async()=>{const x=fixture();assert.equal((await invoke(x,dup())).outcomes[0].status,'applied');assert.equal(x.writes.length,1);});
test('holds',async()=>{for(const mode of ['cycle','unknown','claim','removed']) {const x=fixture();if(mode==='cycle')x.edges=[{dependent:key(2),blocker:key(1)}];if(mode==='unknown')x.complete=false;if(mode==='claim')x.claim=false;if(mode==='removed')x.history=[{event:'blocked_by_removed',blocked_by:{html_url:key(2)}}];assert.equal((await invoke(x,dep())).outcomes[0].status,'held',mode);assert.equal(x.writes.length,0);}});
test('uncertain',async()=>{const x=fixture();x.fail=true;const batch=await invoke(x,dup(),dep());assert.deepEqual(batch.outcomes.map(o=>o.status),['unknown','held']);await invoke(x,dup());assert.equal(x.writes.length,1);});
test('classifications',async()=>{const x=fixture();const rs=['needs','same cause','same class','duplicate','related'].map(c=>rel({kind:'none'},c));assert.deepEqual((await invoke(x,...rs)).outcomes.map(o=>o.status),Array(5).fill('none'));assert.equal(x.writes.length,0);});
test('direction',async()=>{const x=fixture();const r=rel({kind:'blocked-by',dependent:2,blocker:1},'needs');assert.equal((await invoke(x,r)).outcomes[0].status,'applied');assert.equal(x.writes[0].issue,2);assert.equal(x.writes[0].blockerId,'1');});
test('unsafe-endpoint',async()=>{const x=fixture();assert.equal((await invoke(x,rel({kind:'duplicate',duplicate:1,canonical:9}))).outcomes[0].status,'held');assert.equal(x.writes.length,0);});
test('undo',async()=>{const x=fixture();x.events=[event('UnmarkedAsDuplicateEvent')];assert.equal((await invoke(x,dup())).outcomes[0].status,'held');assert.equal(x.writes.length,0);});
test('unknown-post',async()=>{const x=fixture();x.fail=true;assert.equal((await invoke(x,dup())).outcomes[0].status,'unknown');assert.equal((await invoke(x,dup())).outcomes[0].status,'unknown');assert.equal(x.writes.length,1);});
test('unknown-readback',async()=>{const x=fixture();let count=0;x.ports.github.duplicateTimeline=async()=>{if(++count>2)throw Error('incomplete');return [];};assert.equal((await invoke(x,dup())).outcomes[0].status,'unknown');await invoke(x,dup());assert.equal(x.writes.length,1);});
test('already',async()=>{const x=fixture();x.events=[event('MarkedAsDuplicateEvent')];assert.equal((await invoke(x,dup())).outcomes[0].status,'already-present');assert.equal(x.writes.length,0);});
test('native duplicate transport paginates and posts the exact comment',async()=>{
  const x=fixture(), calls=[]; let posted=false;
  delete x.ports.github; x.ports.githubFloor=null; x.ports.snapshotStore=null;
  x.ports.execFile=async (_file,args,options)=>{
    const method=args[args.indexOf('--method')+1], endpoint=args[args.indexOf('--method')+2];
    calls.push({method,endpoint,input:options.input});
    let body;
    if(endpoint==='user') body={login:'writer'};
    else if(endpoint.endsWith('/permission')) body={permission:'write'};
    else if(endpoint==='graphql') {const {variables}=JSON.parse(options.input);const nodes=posted && variables.cursor==='next'?[event('MarkedAsDuplicateEvent')]:[];body={data:{repository:{issue:{url:key(1),timelineItems:{nodes,pageInfo:{hasNextPage:!variables.cursor,endCursor:variables.cursor?null:'next'}}}}}};}
    else if(method==='POST' && endpoint.endsWith('/comments')) {posted=true;body={id:7};}
    else {const n=Number(endpoint.split('/').at(-1));body={id:n,html_url:key(n),state:'open'};}
    return {code:0,stdout:`HTTP/1.1 200 OK\r\n\r\n${JSON.stringify(body)}`};
  };
  assert.equal((await invoke(x,dup())).outcomes[0].status,'applied');
  const post=calls.find(c=>c.method==='POST' && c.endpoint.endsWith('/comments'));
  assert.equal(post.endpoint,'repos/owner/repo/issues/1/comments');assert.deepEqual(JSON.parse(post.input),{body:'Duplicate of #2'});
  assert.ok(calls.filter(c=>c.endpoint==='graphql').length>=6);
});
test('unknown duplicate recovers from matching new event without another post',async()=>{const x=fixture();x.fail=true;assert.equal((await invoke(x,dup())).outcomes[0].status,'unknown');x.events=[event('MarkedAsDuplicateEvent')];assert.equal((await invoke(x,dup())).outcomes[0].status,'applied');assert.equal(x.writes.length,1);});
test('changed evidence after initial validation prevents dispatch',async()=>{const x=fixture();let reads=0;const original=x.ports.evidence.read;x.ports.evidence.read=async()=>++reads===1?original():({json:JSON.stringify({requirements:[]})});assert.equal((await invoke(x,dup())).outcomes[0].status,'held');assert.equal(x.writes.length,0);});
test('confirmed failure stops the batch',async()=>{const x=fixture();x.ports.github.markDuplicate=async()=>{x.writes.push('post');throw Object.assign(Error('rejected'),{status:403});};assert.deepEqual((await invoke(x,dup(),dep())).outcomes.map(x=>x.status),['failed','held']);});
test('sub-issue removal and incomplete readback do not repeat writes',async()=>{const x=fixture();x.sub='removed';assert.equal((await invoke(x,sub())).outcomes[0].status,'held');assert.equal(x.writes.length,0);});
test('failed batch revalidation preserves confirmed and uncertain dispatches without resending',async()=>{
  for (const mode of ['unavailable','changed']) {
    const x=fixture(), receipts=new Map();
    x.ports.checkpoint={read:async ({index})=>receipts.get(index),write:async row=>receipts.set(row.index,row)};
    x.fail=true;
    const relations=[dep(),dup(),sub()];
    const first=await invoke(x,...relations);
    assert.deepEqual(first.outcomes.map(o=>o.status),['applied','unknown','held']);
    const saved=structuredClone([...receipts]);
    x.ports.evidence.read=async()=>{if(mode==='unavailable')throw Error('offline');return {json:JSON.stringify({requirements:[{key:key(2),revision:'changed',text:'quote',authority:'trusted'}]})};};
    const retry=await invoke(x,...relations);
    assert.deepEqual(retry.outcomes.map(o=>o.status),['applied','unknown','held'],mode);
    assert.equal(x.writes.length,2,mode);
    assert.deepEqual([...receipts],saved,mode);
  }
});
