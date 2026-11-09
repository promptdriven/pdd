import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as dependencyGithub from '../src/issue-dependencies-github.mjs';
const { readDependencySnapshot } = dependencyGithub;
const readManualHold = dependencyGithub.readManualHold ?? (async () => ({held:false, known:false}));
import { projectIssueGraph } from '../src/issue-dependencies.mjs';
import { sortPlan } from '../src/issue-sort.mjs';

const repository = 'owner/repo', key = `https://github.com/${repository}/issues/1`;
function fixture() {
  const state = { labels: ['pdd:manual'], events: [], permission: { known: true, allowed: true } };
  const raw = () => ({ id: 1, number: 1, html_url: key, title: 'One', body: '', state: 'open', user: { login: 'owner' }, labels: state.labels.map(name => ({name})), assignees: [] });
  const ports = {
    github: {
      issue: async () => ({json: JSON.stringify(raw())}),
      page: async ({kind, cursor}) => ({json: JSON.stringify({items: kind === 'issues' ? [raw()] : kind === 'timeline' ? (cursor ? state.events.slice(1) : state.events.slice(0, 1)) : [], next: kind === 'timeline' && !cursor && state.events.length > 1 ? 'next' : ''})}),
    },
    manualAuthority: { read: async () => state.permission },
    authority: { read: async () => ({authority:'trusted'}) },
    context: { read: async () => ({json: JSON.stringify({inputs:[], conditions:[], execution:[]})}) },
    owners: { read: async () => ({json: JSON.stringify({claims:[], runs:[], runsKnown:true})}) },
    clock: { now: async () => ({iso:'2026-01-01T00:00:00Z'}) },
  };
  return {state, ports};
}
const event = (event, login) => ({event, label:{name:'pdd:manual'}, actor:{login}});
test('manual hold uses the last current application and repository permission', async () => {
  const {state, ports} = fixture();
  state.events = [event('labeled','writer')];
  assert.deepEqual(await readManualHold({repository, issue:1}, ports), {held:true, known:true});
  state.events.push(event('unlabeled','writer'), event('labeled','outsider'));
  state.permission = {known:true, allowed:false};
  assert.deepEqual(await readManualHold({repository, issue:1}, ports), {held:false, known:true});
  state.permission = {known:false, allowed:false};
  assert.deepEqual(await readManualHold({repository, issue:1}, ports), {held:false, known:false});
  state.labels = [];
  assert.deepEqual(await readManualHold({repository, issue:1}, ports), {held:false, known:true});
});
test('snapshot and sort exclude effective manual holds and restore intake after removal', async () => {
  const {state, ports} = fixture(); state.events = [event('labeled','writer')];
  const read = async () => (await readDependencySnapshot({repository}, ports)).snapshot;
  const held = await read();
  assert.ok(held.issues[0].holds.includes('pdd:manual'));
  assert.equal(projectIssueGraph({snapshot:held}).nodes[0].eligible, false);
  held.sortContext = {release:'x', areas:[], groups:[]};
  assert.deepEqual(sortPlan({snapshot:held}).queued, []);
  state.labels = [];
  const released = await read(); released.sortContext = {release:'x', areas:[], groups:[]};
  assert.ok(!released.issues[0].holds.includes('pdd:manual'));
  assert.deepEqual(sortPlan({snapshot:released}).queued, [key]);
});

function batchAuthorityWorld({shape='complete',count=2}={}) {
  const state={held:false,calls:[]};
  const ports={manualAuthority:{read:async()=>({known:true,allowed:true})},execFile:async(file,args,options={})=>{
    assert.equal(file,'gh');
    const endpoint=args.find(word=>word==='graphql'||/^repos\//.test(word));state.calls.push(endpoint);
    let value;
    if(endpoint==='graphql') {
      const {variables}=JSON.parse(options.input),rows={};
      for(const [name,number] of Object.entries(variables)) if(/^n\d+$/.test(name)) {
        const row={url:`https://github.com/${repository}/issues/${number}`,number,labels:{nodes:state.held&&number===2&&shape==='complete'?[{name:'pdd:manual'}]:[],pageInfo:{hasNextPage:false}}};
        if(number===2&&shape==='wrong-issue')row.url=`https://github.com/${repository}/issues/3`;
        if(number===2&&shape==='partial-labels')row.labels.pageInfo.hasNextPage=true;
        rows[`i${name.slice(1)}`]=number===2&&shape==='missing'?null:row;
      }
      value={data:{repository:rows},...(shape==='errors'?{errors:[{message:'unavailable'}]}:{})};
    } else {
      const subject=new RegExp(`^repos/${repository}/issues/(\\d+)(/timeline\\?per_page=100)?$`).exec(endpoint??'');
      assert.ok(subject);
      value=subject[2]?[event('labeled','owner')]:{number:Number(subject[1]),labels:state.held&&Number(subject[1])===2?[{name:'pdd:manual'}]:[]};
    }
    return {code:0,stdout:JSON.stringify(value)};
  }};
  const issues=Array.from({length:count},(_,i)=>i+1);
  const gate=async()=>dependencyGithub.issueEffectsAllowed
    ? dependencyGithub.issueEffectsAllowed({repository,issues},ports)
    : (await Promise.all(issues.map(issue=>dependencyGithub.issueEffectAllowed({repository,issue},ports)))).every(Boolean);
  return {state,gate};
}

test('fresh delivery authority batches 26 clear subjects into two queries',async()=>{
  const {state,gate}=batchAuthorityWorld({count:26});
  assert.equal(await gate(),true);
  assert.deepEqual(state.calls,['graphql','graphql']);
});
for(const shape of ['complete','wrong-issue','partial-labels','missing','errors']) test(`fresh delivery authority retains late hold through ${shape} batch`,async()=>{
  const {state,gate}=batchAuthorityWorld({shape});
  assert.equal(await gate(),true);
  state.held=true;state.calls=[];
  assert.equal(await gate(),false);
  assert.ok(state.calls.includes(`repos/${repository}/issues/2`));
  assert.ok(state.calls.includes(`repos/${repository}/issues/2/timeline?per_page=100`));
});


test('batch authority preserves an injected single-issue reader',async()=>{
  const calls=[];
  const ports={readManualHold:async({issue})=>{calls.push(issue);return {known:issue===1,held:false};},execFile:async()=>assert.fail('unexpected transport')};
  const allowed=dependencyGithub.issueEffectsAllowed
    ? await dependencyGithub.issueEffectsAllowed({repository,issues:[1,2]},ports)
    : (await Promise.all([1,2].map(issue=>dependencyGithub.issueEffectAllowed({repository,issue},ports)))).every(Boolean);
  assert.equal(allowed,false);assert.deepEqual(calls,[1,2]);
});
for(const bad of ['rejection','malformed'])test(`batch authority blocks custom reader ${bad}`,async()=>{
  const reader=async()=>{if(bad==='rejection')throw Error('unavailable');return {};};
  const allowed=dependencyGithub.issueEffectsAllowed
    ? await dependencyGithub.issueEffectsAllowed({repository,issues:[1,2]},{manualSafetyReadMany:reader})
    : false;
  assert.equal(allowed,false);
});
