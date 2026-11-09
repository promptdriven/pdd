import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,appendFileSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {captureSource,interfaceBlocks,proseSha256} from '../src/runtime-preflight.mjs';
import {runCheck} from '../src/runtime-client.mjs';
import {harbor,portsFor,fakeRuntime,PLACE} from './runtime-fake.mjs';

const TEST='tests/place-order.json', STORY='user_stories/place-order.md', RUNNER='prompts/runner.prompt.md';
const read=(f,path)=>readFileSync(join(f.repo,path),'utf8');
const save=(f,path,value)=>writeFileSync(join(f.repo,path),typeof value==='string'?value:JSON.stringify(value));
const schema={type:'object',properties:{},required:[],additionalProperties:false};
function setup(t) {
  const f=harbor(t),text=read(f,PLACE),block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);
  iface.resources=[{name:'files',kind:'port',operations:[{name:'read',arguments_schema:schema,result_schema:schema}]}];
  let runner=text.replace(block[1],JSON.stringify(iface));
  iface.prose_sha256=proseSha256(runner);runner=runner.replace(interfaceBlocks(runner)[0][1],JSON.stringify(iface));
  save(f,RUNNER,runner);
  let entry=text.replace('None.','[Runner](runner.prompt.md)');
  const entryInterface=JSON.parse(block[1]);entryInterface.resources=[];entryInterface.prose_sha256=proseSha256(entry);
  save(f,PLACE,entry.replace(block[1],JSON.stringify(entryInterface)));
  return f;
}
const declare=(f,story,body)=>appendFileSync(join(f.repo,story),`\n## Runtime boundary\n\n${body}\n`);
const entry='[Entry](../prompts/place_order.prompt.md)';
const requiredEdges=capture=>capture.bindingPlans.flatMap(plan=>plan.edges.map(edge=>JSON.stringify([plan.test,edge.step_id,edge.prompt_path,edge.key,edge.state])));
function assertRequired(capture) {
  const source=capture.sources.find(row=>row.path===RUNNER);
  assert.ok(source,'3135_REQUIRED_SOURCE');
  assert.equal(interfaceBlocks(source.bytes.toString()).length,1,'3135_REQUIRED_INTERFACE');
  const edges=capture.bindingPlans.flatMap(plan=>plan.edges).filter(edge=>edge.prompt_path===RUNNER);
  assert.ok(edges.length,'3135_REQUIRED_EDGE');
  for(const edge of edges) {assert.equal(edge.key,'files.read');assert.equal(edge.state,'missing');}
}
async function assertUpload(t,f,words) {
  let uploaded=0;
  const fake=await fakeRuntime(t,(request,engine)=>{
    if(request.command==='lint') {
      const result=spawnSync('tar',['-xOf','-',RUNNER],{input:request.tar,encoding:'utf8'});
      assert.equal(result.status,0);
      assert.equal(interfaceBlocks(result.stdout).length,1,'3135_UPLOADED_REQUIRED_INTERFACE');uploaded++;
    }
    return engine.normal(request);
  });
  const {ports}=portsFor({HOME:f.home,XDG_CONFIG_HOME:join(f.home,'config'),PDD_STATE_DIR:f.state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:f.repo,words,options:{'--json':true}},ports),0);
  assert.ok(uploaded);
  const rows=JSON.parse(ports.stdout.text).rows;
  assert.ok(rows.some(row=>row.binding_plan.edges.some(edge=>edge.prompt_path===RUNNER&&edge.key==='files.read'&&edge.state==='missing')),'3135_SAVED_MISSING_EDGE');
}

for(const [name,link,definitions] of [
  ['titled','[Runner](../prompts/runner.prompt.md "required")',''],
  ['angle','[Runner](<../prompts/runner.prompt.md> "required")',''],
  ['reference','[Runner][required]','[required]: <../prompts/runner.prompt.md> "required"'],
  ['collapsed','[Runner][]','[Runner]: ../prompts/runner.prompt.md'],
  ['shortcut','[Runner]','[Runner]: ../prompts/runner.prompt.md'],
]) test(`3135 repair: ${name} declaration keeps its boundary, upload and missing edge`,async t=>{
  const f=setup(t);
  // Definitions may precede the boundary and still resolve its declarations.
  appendFileSync(join(f.repo,STORY),`\n${definitions}\n`);
  declare(f,STORY,`${entry}\n- ${link}`);
  const capture=captureSource(f.repo,{tests:[TEST]});
  assert.deepEqual(capture.bindingPlans[0].boundary,[PLACE,RUNNER].sort(),'3135_COMPLETE_BOUNDARY');
  assertRequired(capture);
  await assertUpload(t,f,['place-order']);
});

for(const declaration of ['[Runner][missing]','[Runner](../prompts/runner.prompt.md "unclosed)', '[Runner](../prompts/runner.prompt.md', '`[Runner](../prompts/runner.prompt.md)`', '[Runner](../prompts/runner.prompt.md) unsupported'])
  test(`3135 repair: partial declaration refuses (${declaration})`,t=>{
    const f=setup(t);declare(f,STORY,`${entry}\n${declaration}`);
    assert.throws(()=>captureSource(f.repo,{tests:[TEST]}),error=>error.code==='binding-boundary-invalid','3135_PARTIAL_BOUNDARY_REFUSAL');
  });

test('3135 repair: combined Story boundaries retain the union, upload and missing binding',async t=>{
  const f=setup(t);declare(f,STORY,`${entry}\n[Runner](../prompts/runner.prompt.md)`);
  declare(f,'user_stories/unknown-item.md',entry);
  const combined=captureSource(f.repo,{tests:[TEST,'tests/unknown-item.json']});assertRequired(combined);
  const alone=captureSource(f.repo,{tests:[TEST]});assertRequired(alone);
  assert.deepEqual(combined.bindingPlans.map(plan=>plan.boundary),[[PLACE,RUNNER].sort(),[PLACE]]);
  assert.deepEqual(combined.bindingPlans[0].edges,alone.bindingPlans[0].edges);
  await assertUpload(t,f,['place-order','unknown-item']);
});

test('3135 repair: a declared member loads even without an ordinary dependency link',async t=>{
  const f=setup(t),text=read(f,PLACE).replace('[Runner](runner.prompt.md)','None.');
  const block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);iface.prose_sha256=proseSha256(text);
  save(f,PLACE,text.replace(block[1],JSON.stringify(iface)));
  declare(f,STORY,`${entry}\n[Runner](../prompts/runner.prompt.md)`);
  const capture=captureSource(f.repo,{tests:[TEST]});
  assert.deepEqual(capture.bindingPlans[0].boundary,[PLACE,RUNNER].sort());assertRequired(capture);
  await assertUpload(t,f,['place-order']);
});

test('3135 repair: property - adding any Story selection never removes a required edge',t=>{
  const f=setup(t),base=JSON.parse(read(f,TEST)),storyText=read(f,STORY),paths=[];
  // Exhaust all subsets of explicit broad/narrow and unscoped Stories, with two entries.
  for(let index=0;index<4;index++) {
    const story=`user_stories/scope-${index}.md`,path=`tests/scope-${index}.json`;
    save(f,story,storyText);save(f,path,{...base,story_path:story,steps:base.steps.map(step=>({...step,entry_path:index===3?RUNNER:PLACE}))});
    if(index<3)declare(f,story,index===0?`${entry}\n[Runner](../prompts/runner.prompt.md)`:index===1?entry:'[Runner](../prompts/runner.prompt.md)');
    // The third Story uses Runner as its entry, within its own boundary.
    if(index===2) {const doc=JSON.parse(read(f,path));doc.steps[0].entry_path=RUNNER;save(f,path,doc);}
    paths.push(path);
  }
  const captures=new Map();
  for(let mask=1;mask<16;mask++)assert.doesNotThrow(()=>captures.set(mask,captureSource(f.repo,{tests:paths.filter((_,i)=>mask&(1<<i))})), '3135_VALID_UNION_SELECTION');
  let comparisons=0;
  for(const [mask,before] of captures)for(let index=0;index<4;index++)if(!(mask&(1<<index))) {
    const after=captures.get(mask|(1<<index)),required=new Set(requiredEdges(after));
    for(const edge of requiredEdges(before))assert.ok(required.has(edge),'3135_MONOTONE_EDGE');
    for(const source of before.sources.filter(row=>row.path.endsWith('.prompt.md')&&interfaceBlocks(row.bytes.toString()).length)) {
      const retained=after.sources.find(row=>row.path===source.path);
      assert.ok(retained,'3135_MONOTONE_SOURCE');assert.equal(interfaceBlocks(retained.bytes.toString()).length,1,'3135_MONOTONE_INTERFACE');
    }
    comparisons++;
  }
  assert.equal(comparisons,28);
});
