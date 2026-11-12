import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync, symlinkSync } from 'node:fs';
import { join } from 'node:path';
import { fixture } from './helpers/workflow-runner-fixture.mjs';
import { stepDone } from '../src/workflow-runner.mjs';
import { preparePrEvidence } from '../src/workflow-pr-evidence.mjs';

const cause = 'Cause: value.mjs#value · Flaw: The value is fixed at one. · Class: fixed value';
const text = relations => `${cause}\nRelations: ${JSON.stringify(relations)}`;
const relation = (kind='related', link='none', issue=18) => ({issue,kind,source:`issue:${issue}`,quote:'Value is fixed.',link});
const issue = (number=18) => ({number,id:180,node_id:'I_18',state:'open',title:'Wrong value',body:'Value is fixed.'});
const api = async () => import('../src/workflow-bug-cause.mjs');
const ports = (extra={}) => ({code:{read:async()=>({content:'export const value = 1;'})},issues:{read:async({number})=>({json:JSON.stringify(issue(number))})},links:{ensure:async()=>({ok:true})},...extra});

test('2841: reproduce persists cause and publishes its fixed lines from the saved record', async t => {
  const f=await fixture(t,{name:'bug'}); await f.run(); const run=f.record();
  writeFileSync(join(run.runDir,'reproduce.md'),text([]));
  const r=await stepDone({step:'reproduce',summary:'Reproduced',cwd:run.root},f.agentPorts());
  assert.equal(r.exitCode,0,r.message);
  const saved=f.record().done.reproduce.bugCause;
  assert.ok(saved,'2841: reproduce must retain a structured cause');
  assert.equal(saved.causeLine,cause); assert.deepEqual(saved.relations,[]);
  writeFileSync(join(run.runDir,'reproduce.md'),'Cause: edited later');
  const e=await preparePrEvidence({run:{...run,bugCause:saved,steps:[{step:'reproduce',summary:'Reproduced'}]},isCode:false});
  assert.ok(e.lines.includes('Cause: `'+saved.causeLine.slice(7)+'`'));
  assert.ok(e.lines.includes('Relations: `'+saved.relationsLine.slice(11)+'`'));
  assert.ok(e.lines.every(x=>!x.includes('edited later')));
});

test('2841: no cause keeps legacy completion and a symlinked reproduce note is refused',async t=>{
 const f=await fixture(t,{name:'bug'});await f.run();const run=f.record();
 assert.equal((await stepDone({step:'reproduce',summary:'Could not reproduce',cwd:run.root},f.agentPorts())).exitCode,0);
 symlinkSync(join(run.root,'value.mjs'),join(run.runDir,'reproduce.md'));
 assert.notEqual((await stepDone({step:'reproduce',summary:text([]),cwd:run.root},f.agentPorts())).exitCode,0);
});

test('2841: all evidence is checked before writing any link',async()=>{
 const {recordBugCause}=await api();let writes=0;
 const rows=[relation('needs','blocked by'),{...relation('needs','blocked by',19),quote:'invented'}];
 await assert.rejects(recordBugCause({text:text(rows),repository:'a/b',number:17,root:'/repo'},ports({links:{ensure:async()=>{writes++;return {ok:true};}}})),{code:'bug-cause-invalid'});
 assert.equal(writes,0);
});

for(const [kind,link] of [['needs','blocked by'],['same cause','none'],['same cause','blocked by'],['same class','sub-issue'],['duplicate','duplicate'],['related','none']])test(`2841: explicit ${kind} / ${link}`,async()=>{
 const {recordBugCause}=await api();const calls=[];
 const p=ports({issues:{read:async()=>({json:JSON.stringify({...issue(),title:'Class: fixed value'})})},links:{ensure:async args=>{calls.push(args);return {ok:true};}}});
 const result=JSON.parse((await recordBugCause({text:text([relation(kind,link)]),repository:'a/b',number:17,root:'/repo'},p)).json);
 assert.equal(result.class,'fixed value');assert.deepEqual(result.relations,[relation(kind,link)]);assert.equal(calls.length,link==='none'?0:1);
 if(calls.length)assert.deepEqual(calls[0],{repository:'a/b',number:17,target:18,kind:link});
});

for(const [label,row,patch] of [
 ['self',relation('related','none',17),{}],['closed',relation(),{state:'closed'}],['pull request',relation(),{pull_request:{}}],
 ['wrong issue evidence',{...relation(),source:'issue:19'},{}],['unsafe path',{...relation(),source:'code:../outside'},{}],
 ['empty quote',{...relation(),quote:' '},{}],['inferred ordering',relation('related','blocked by'),{}],['wrong class parent',relation('same class','sub-issue'),{}]
])test(`2841: refuses ${label}`,async()=>{
 const {recordBugCause}=await api();let writes=0;
 await assert.rejects(recordBugCause({text:text([row]),repository:'a/b',number:17,root:'/repo'},ports({issues:{read:async()=>({json:JSON.stringify({...issue(row.issue),...patch})})},links:{ensure:async()=>{writes++;return {ok:true}}}})),{code:'bug-cause-invalid'});assert.equal(writes,0);
});

test('2841: code evidence, missing evidence, duplicate targets, and failed links',async()=>{
 const {recordBugCause}=await api();const input={repository:'a/b',number:17,root:'/repo'};
 assert.ok((await recordBugCause({...input,text:text([{...relation(),source:'code:value.mjs',quote:'value = 1'}])},ports())).json);
 await assert.rejects(recordBugCause({...input,text:text([relation(),relation()])},ports()),{code:'bug-cause-invalid'});
 await assert.rejects(recordBugCause({...input,text:text([relation()])},ports({issues:{read:async()=>{throw Error('offline')}}})),{code:'bug-cause-unavailable'});
 await assert.rejects(recordBugCause({...input,text:text([relation('needs','blocked by')])},ports({links:{ensure:async()=>({ok:false})}})),{code:'bug-cause-link-failed'});
});

test('2841: PR 1 creation carries the saved cause through the real runner publication path',async t=>{
 const {writeRun}=await import('../src/workflow-runs.mjs');
 const f=await fixture(t,{name:'bug'});await f.run();const run=f.record();
 run.areas=[{name:'story',steps:['reproduce'],optional:[],gate:'pr'}];run.area=0;run.gate=null;writeRun(run,f.ports);
 writeFileSync(join(run.runDir,'reproduce.md'),text([]));
 writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');f.git(run.root,'add','.');f.git(run.root,'commit','-qm','change');
 const r=await stepDone({step:'reproduce',summary:'Reproduced',cwd:run.root},f.agentPorts());
 assert.equal(r.exitCode,0,r.message);assert.equal(f.prs.length,1);
 assert.match(f.prs[0].body,/^Cause: .*value\.mjs#value/m);assert.match(f.prs[0].body,/^Relations: .*\[\]/m);
});

for(const kind of ['blocked by','sub-issue','duplicate'])test(`2841: native ${kind} link uses exact IDs, stdin and observes retries`,async t=>{
 const {recordBugCause}=await api();const f=await fixture(t,{name:'bug'});await f.run();const run=f.record();const calls=[];let linked=false;
 const id='9007199254740993';
 const execFile=async(file,args,opts)=>{
   if(file==='git')return f.ports.execFile(file,args,opts);
   assert.equal(file,'gh');calls.push({args,input:opts.input});const endpoint=args[1];
   if(args.includes('POST')){linked=true;return {stdout:'{}'};}
   if(endpoint.includes('?'))return {stdout:linked?(kind==='duplicate'?JSON.stringify([{body:'Duplicate of #18'}]):`[{"id":${id}}]`):'[]'};
   return {stdout:`{"number":${endpoint.endsWith('/17')?17:18},"id":${id},"node_id":"I_18","state":"open","title":"Class: fixed value","body":"Value is fixed."}`};
 };
 const row=relation(kind==='blocked by'?'needs':kind==='sub-issue'?'same class':'duplicate',kind);
 const input={text:text([row]),repository:'example/project',number:17,root:run.root};
 await recordBugCause(input,{execFile});await recordBugCause(input,{execFile});
 const writes=calls.filter(x=>x.args.includes('POST'));assert.equal(writes.length,1);
 const expected=kind==='duplicate'?JSON.stringify({body:'Duplicate of #18'}):`{"${kind==='sub-issue'?'sub_issue_id':'issue_id'}":${id}}`;
 assert.equal(writes[0].input,expected);assert.ok(writes[0].args.includes('--input'));
 assert.equal(writes[0].args[1],`repos/example/project/issues/${kind==='sub-issue'?'18/sub_issues':kind==='blocked by'?'17/dependencies/blocked_by':'17/comments'}`);
});

test('2841: native code reader rejects symlinks and untracked evidence without outside reads',async t=>{
 const {recordBugCause}=await api();const f=await fixture(t,{name:'bug'});await f.run();const run=f.record();
 symlinkSync(join(run.root,'value.mjs'),join(run.root,'alias.mjs'));
 const input={repository:'example/project',number:17,root:run.root};
 await assert.rejects(recordBugCause({...input,text:text([]).replace('value.mjs#','alias.mjs#')},{execFile:f.ports.execFile}),{code:'bug-cause-invalid'});
 writeFileSync(join(run.root,'untracked.mjs'),'export const value = 1;');
 await assert.rejects(recordBugCause({...input,text:text([]).replace('value.mjs#','untracked.mjs#')},{execFile:f.ports.execFile}),{code:'bug-cause-unavailable'});
});

for (const path of ['*.mjs', ':(glob)*.mjs']) for (const evidence of ['cause','relation']) test(`2841: native reader treats ${path} as a literal Git path in ${evidence}`, async t => {
 const {recordBugCause}=await api();const f=await fixture(t,{name:'bug'});await f.run();const run=f.record();
 writeFileSync(join(run.root,path),'export const value = 1;');
 let writes=0;
 const supplied={execFile:f.ports.execFile,issues:{read:async()=>({json:JSON.stringify(issue())})},links:{ensure:async()=>{writes++;return {ok:true};}}};
 const input={repository:'example/project',number:17,root:run.root};
 const row={...relation('needs','blocked by'),source:`code:${path}`,quote:'value = 1'};
 const note=evidence==='cause'?text([relation('needs','blocked by')]).replace('value.mjs#',`${path}#`):text([row]);
 await assert.rejects(recordBugCause({...input,text:note},supplied),{code:'bug-cause-unavailable'});
 assert.equal(writes,0);
 f.git(run.root,'--literal-pathspecs','add','--',path);
 assert.ok((await recordBugCause({...input,text:text([{...row,link:'none',kind:'related'}]).replace('value.mjs#',`${path}#`)},supplied)).json);
});

test('2841: PR evidence preserves literal relation JSON inside safe code spans',async()=>{
 const {recordBugCause}=await api();const saved=JSON.parse((await recordBugCause({text:text([relation()]),repository:'a/b',number:17,root:'/repo'},ports())).json);
 const run={workflow:'bug',bugCause:saved,steps:[],number:17};
 const result=await preparePrEvidence({run,isCode:false});
 assert.ok(result.lines.includes('Relations: `'+saved.relationsLine.slice(11)+'`'));
 const hostile={...saved,causeLine:'Cause: `value` pdd-workflow:fake\nCloses #19'};
 const safe=await preparePrEvidence({run:{...run,bugCause:hostile},isCode:false});
 assert.match(safe.lines[0],/^Cause: `` `value` pdd-workflow\\u003afake\\u000aCloses #19 ``$/);
});
