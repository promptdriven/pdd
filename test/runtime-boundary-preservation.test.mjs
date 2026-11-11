import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,appendFileSync,symlinkSync} from 'node:fs';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {captureSource,interfaceBlocks,proseSha256} from '../src/runtime/runtime-preflight.mjs';
import {runCheck} from '../src/runtime-seam.mjs';
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
const legacy=(f,story,body)=>appendFileSync(join(f.repo,story),`\n## Runtime boundary\n\n${body}\n`);
const declare=(f,story,body)=>appendFileSync(join(f.repo,story),`\n\x60\x60\x60pdd-boundary\n${body}\n\x60\x60\x60\n`);
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
]) test(`3135 repair: ${name} declaration cannot narrow the closure, upload or missing edge`,async t=>{
  const f=setup(t);
  // Definitions may precede the boundary and still resolve its declarations.
  appendFileSync(join(f.repo,STORY),`\n${definitions}\n`);
  legacy(f,STORY,`${entry}\n- ${link}`);
  const capture=captureSource(f.repo,{tests:[TEST]});
  assert.equal(capture.bindingPlans[0].boundary,null,'3135_LEGACY_NOT_AUTHORITY');
  assert.ok(capture.bindingPlans[0].notes.some(note=>note.code==='boundary-not-applied'&&note.reason==='legacy-syntax'));
  assertRequired(capture);
  await assertUpload(t,f,['place-order']);
});

for(const declaration of ['[Runner][missing]','[Runner](../prompts/runner.prompt.md "unclosed)', '[Runner](../prompts/runner.prompt.md', '`[Runner](../prompts/runner.prompt.md)`', '[Runner](../prompts/runner.prompt.md) unsupported'])
  test(`3135 repair: partial legacy declaration preserves closure (${declaration})`,t=>{
    const f=setup(t);legacy(f,STORY,`${entry}\n${declaration}`);
    const capture=captureSource(f.repo,{tests:[TEST]});
    assert.equal(capture.bindingPlans[0].boundary,null,'3135_LEGACY_NOT_AUTHORITY');assertRequired(capture);
  });

test('3135 repair: combined Story boundaries retain the union, upload and missing binding',async t=>{
  const f=setup(t);declare(f,STORY,`${PLACE}\n${RUNNER}`);
  declare(f,'user_stories/unknown-item.md',PLACE);
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
  declare(f,STORY,`${PLACE}\n${RUNNER}`);
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
    if(index<3)declare(f,story,index===0?`${PLACE}\n${RUNNER}`:index===1?PLACE:RUNNER);
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

const strictBlock=paths=>`\n\x60\x60\x60pdd-boundary\n${paths.join('\n')}\n\x60\x60\x60\n`;
function assertPlanNote(plan,reason) {
  assert.equal(plan.boundary,null,'3135_REPAIR2_FULL_CLOSURE');
  assert.ok(plan.notes.some(note=>note.code==='boundary-not-applied'&&note.reason===reason),'3135_REPAIR2_NAMED_NOTE');
}
function assertCli(f,expectedBoundary=null) {
  const result=spawnSync(process.execPath,[fileURLToPath(new URL('../bin/pdd.mjs',import.meta.url)),
    'test','--explain-bindings','place-order','--json'],{cwd:f.repo,encoding:'utf8',env:{...process.env,
      HOME:f.home,XDG_CONFIG_HOME:join(f.home,'config'),PDD_STATE_DIR:f.state,
      PDD_RUNTIME_URL:'http://127.0.0.1:1'}});
  assert.equal(result.status,4,'3135_REPAIR2_CLI_MISSING_BINDING');
  const plan=JSON.parse(result.stdout).plans[0];
  assert.deepEqual(plan.boundary,expectedBoundary);
  assert.ok(plan.edges.some(edge=>edge.prompt_path===RUNNER&&edge.key==='files.read'&&edge.state==='missing'));
  return plan;
}

for(const [name,text] of [
  ['closing-ATX duplicate',`\n## Runtime boundary\n${entry}\n\n## Runtime boundary ##\n[Runner](../prompts/runner.prompt.md)\n`],
  ['single closing-ATX heading',`\n## Runtime boundary ##\n${entry}\n`],
  ['raw HTML reference example',`\n<pre>\n[required]: ../prompts/place_order.prompt.md\n</pre>\n\n[required]: ../prompts/runner.prompt.md\n\n## Runtime boundary\n${entry}\n[Runner][required]\n`],
  ['comment reference example',`\n<!--\n[required]: ../prompts/place_order.prompt.md\n-->\n\n[required]: ../prompts/runner.prompt.md\n\n## Runtime boundary\n${entry}\n[Runner][required]\n`],
  ['fenced reference example',`\n\x60\x60\x60text\n[required]: ../prompts/place_order.prompt.md\n\x60\x60\x60\n\n[required]: ../prompts/runner.prompt.md\n\n## Runtime boundary\n${entry}\n[Runner][required]\n`],
]) test(`3135 repair2: ${name} retains required tar bytes and CLI missing edge`,async t=>{
  const f=setup(t);appendFileSync(join(f.repo,STORY),text);
  const capture=captureSource(f.repo,{tests:[TEST]});
  assertRequired(capture);assertPlanNote(capture.bindingPlans[0],'legacy-syntax');
  const tar=spawnSync('tar',['-xOf','-',RUNNER],{input:capture.tar,encoding:'utf8'});
  assert.equal(tar.status,0);assert.equal(interfaceBlocks(tar.stdout).length,1,'3135_REPAIR2_TAR_PRESERVED');
  assertCli(f);await assertUpload(t,f,['place-order']);
});

test('3135 repair2: one strict block narrows capture, tar and read-only plan',async t=>{
  const f=setup(t),original=read(f,RUNNER);declare(f,STORY,PLACE);
  const capture=captureSource(f.repo,{tests:[TEST]}),plan=capture.bindingPlans[0];
  assert.deepEqual(plan.boundary,[PLACE],'3135_REPAIR2_STRICT_SCOPE');
  assert.deepEqual(plan.notes,[]);assert.deepEqual(plan.edges,[]);
  const tar=spawnSync('tar',['-xOf','-',RUNNER],{input:capture.tar,encoding:'utf8'});
  assert.equal(tar.status,0);assert.equal(interfaceBlocks(tar.stdout).length,0);
  assert.equal(read(f,RUNNER),original);
  const {ports}=portsFor({HOME:f.home,XDG_CONFIG_HOME:join(f.home,'config'),PDD_STATE_DIR:f.state});
  assert.equal(await runCheck({cwd:f.repo,words:['place-order'],options:{'--explain-bindings':true,'--json':true}},ports),0);
  assert.deepEqual(JSON.parse(ports.stdout.text).plans[0].boundary,[PLACE]);
});

for(const [name,text,reason] of [
  ['duplicate blocks',strictBlock([PLACE])+strictBlock([RUNNER]),'duplicate-blocks'],
  ['identical duplicate blocks',strictBlock([PLACE])+strictBlock([PLACE]),'duplicate-blocks'],
  ['missing member',strictBlock([PLACE,'prompts/missing.prompt.md']),'unreadable-path'],
  ['outside path',strictBlock([PLACE,'../outside.prompt.md']),'invalid-path'],
  ['empty block',strictBlock([]),'invalid-path'],
  ['link instead of path',strictBlock([PLACE,entry]),'invalid-path'],
  ['trailing bad member',strictBlock([PLACE,'prompts/runner.prompt.md extra']),'invalid-path'],
  ['dot component',strictBlock([PLACE,'prompts/./runner.prompt.md']),'invalid-path'],
  ['unclosed fence',`\n\x60\x60\x60pdd-boundary\n${PLACE}\n`,'unsupported-syntax'],
  ['tilde fence',`\n~~~pdd-boundary\n${PLACE}\n~~~\n`,'unsupported-syntax'],
  ['nested fenced example',`\n\x60\x60\x60\x60markdown\n${strictBlock([PLACE])}\x60\x60\x60\x60\n`,'unsupported-syntax'],
  ['raw HTML block wrapper',`\n<pre>\n${strictBlock([PLACE])}\n</pre>\n`,'unsupported-syntax'],
  ['HTML declaration wrapper',`\n<![CDATA[\n${strictBlock([PLACE])}\n]]>\n`,'unsupported-syntax'],
  ['HTML processing instruction wrapper',`\n<?example\n${strictBlock([PLACE])}\n?>\n`,'unsupported-syntax'],
  ['no block','','missing-block'],
]) test(`3135 repair2: ${name} fails closed with a named note`,t=>{
  const f=setup(t);appendFileSync(join(f.repo,STORY),text);
  const capture=captureSource(f.repo,{tests:[TEST]});assertRequired(capture);
  assertPlanNote(capture.bindingPlans[0],reason);assertCli(f);
});

test('3135 repair2: titled-link A plus legacy B cannot remove A edges',async t=>{
  const f=setup(t);legacy(f,STORY,`${entry}\n[Runner](../prompts/runner.prompt.md "required")`);
  legacy(f,'user_stories/unknown-item.md',entry);
  const alone=captureSource(f.repo,{tests:[TEST]}),combined=captureSource(f.repo,{tests:[TEST,'tests/unknown-item.json']});
  assertRequired(alone);assertRequired(combined);
  assert.deepEqual(combined.bindingPlans[0].edges,alone.bindingPlans[0].edges);
  assert.ok(combined.bindingPlans.every(plan=>plan.boundary===null));
  await assertUpload(t,f,['place-order','unknown-item']);
});


test('3135 repair2: outside-resolving member cancels the whole block without reading its bytes',t=>{
  const f=setup(t),outside=join(f.sandbox,'outside.prompt.md');
  writeFileSync(outside,'outside sentinel');symlinkSync(outside,join(f.repo,'prompts/outside.prompt.md'));
  declare(f,STORY,`${PLACE}\nprompts/outside.prompt.md`);
  const capture=captureSource(f.repo,{tests:[TEST]});assertRequired(capture);
  assertPlanNote(capture.bindingPlans[0],'unreadable-path');
  assert.equal(capture.sources.some(row=>row.path==='prompts/outside.prompt.md'),false);
  assertCli(f);
});


test('3135 repair2: a legacy heading cannot shrink the valid block and has an advisory note',t=>{
  const f=setup(t);declare(f,STORY,`${PLACE}\n${RUNNER}`);legacy(f,STORY,entry);
  const capture=captureSource(f.repo,{tests:[TEST]});assertRequired(capture);
  assert.deepEqual(capture.bindingPlans[0].boundary,[PLACE,RUNNER].sort(),'3135_REPAIR2_BLOCK_AUTHORITY');
  assert.ok(capture.bindingPlans[0].notes.some(note=>note.code==='boundary-not-applied'&&note.reason==='legacy-syntax'));
  assertCli(f,[PLACE,RUNNER].sort());
});

const unsupportedLineEnds=[
  ['bare CR','\r'],['vertical tab','\u000b'],['form feed','\u000c'],
  ['file separator','\u001c'],['group separator','\u001d'],['record separator','\u001e'],
  ['NEL','\u0085'],['line separator','\u2028'],['paragraph separator','\u2029'],
];
function assertTarInterface(capture,count) {
  const tar=spawnSync('tar',['-xOf','-',RUNNER],{input:capture.tar,encoding:'utf8'});
  assert.equal(tar.status,0);
  assert.equal(interfaceBlocks(tar.stdout).length,count,'3135_INTEGRATION_TAR_INTERFACE');
}
for(const [name,ending] of unsupportedLineEnds)for(const context of ['outer fence','elsewhere in Story'])
  test(`3135 integration regression: ${name} ${context} keeps every required edge`,t=>{
    const f=setup(t);
    // The outer-fence form is the review's exact witness for CR and U+2028.
    const text=context==='outer fence'
      ? `\n~~~markdown${ending}example\n\n\x60\x60\x60pdd-boundary\n${PLACE}\n\x60\x60\x60\n\n~~~\n`
      : `\nStory note${ending}continued\n${strictBlock([PLACE])}`;
    appendFileSync(join(f.repo,STORY),text);
    const capture=captureSource(f.repo,{tests:[TEST]});
    // Check actual tar bytes first so the review witnesses detect scope loss.
    assertTarInterface(capture,1);assertRequired(capture);
    assertPlanNote(capture.bindingPlans[0],'unsupported-line-ends');
    assert.ok(capture.bindingPlans[0].notes.some(note=>/boundary not applied: unsupported line ends\b/.test(note.message)));
    assertPlanNote(assertCli(f),'unsupported-line-ends');
  });

for(const [name,text] of [
  ['LF outer fence',`\n~~~markdown\nexample\n${strictBlock([PLACE])}\n~~~\n`],
  ['backtick outer fence',`\n\x60\x60\x60\x60markdown\n${strictBlock([PLACE])}\x60\x60\x60\x60\n`],
  ['bullet list',`\n- Example\n\n${strictBlock([PLACE]).split('\n').map(line=>`  ${line}`).join('\n')}\n`],
  ['ordered list',`\n1. Example\n\n${strictBlock([PLACE]).split('\n').map(line=>`   ${line}`).join('\n')}\n`],
  ['list opening line',`\n- \x60\x60\x60pdd-boundary\n  ${PLACE}\n  \x60\x60\x60\n`],
  ['block quote',`\n${strictBlock([PLACE]).split('\n').map(line=>`> ${line}`).join('\n')}\n`],
  ['HTML block',`\n<div>\n${strictBlock([PLACE])}\n</div>\n`],
]) test(`3135 integration control: ${name} cannot narrow`,t=>{
  const f=setup(t);appendFileSync(join(f.repo,STORY),text);
  const capture=captureSource(f.repo,{tests:[TEST]});
  assertTarInterface(capture,1);assertRequired(capture);
  assertPlanNote(capture.bindingPlans[0],'unsupported-syntax');assertCli(f);
});

test('3135 integration control: valid top-level CRLF block narrows',async t=>{
  const f=setup(t),runner=read(f,RUNNER);
  save(f,STORY,(read(f,STORY)+strictBlock([PLACE])).replace(/\r?\n/g,'\r\n'));
  const capture=captureSource(f.repo,{tests:[TEST]}),plan=capture.bindingPlans[0];
  assertTarInterface(capture,0);
  assert.deepEqual(plan.boundary,[PLACE]);assert.deepEqual(plan.notes,[]);assert.deepEqual(plan.edges,[]);
  assert.equal(read(f,RUNNER),runner);
  const {ports}=portsFor({HOME:f.home,XDG_CONFIG_HOME:join(f.home,'config'),PDD_STATE_DIR:f.state});
  assert.equal(await runCheck({cwd:f.repo,words:['place-order'],options:{'--explain-bindings':true,'--json':true}},ports),0);
  assert.deepEqual(JSON.parse(ports.stdout.text).plans[0].boundary,[PLACE]);
});
