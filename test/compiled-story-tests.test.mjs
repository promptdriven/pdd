import { test, after } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { findTests, preflight, proseSha256 } from '../src/runtime-preflight.mjs';
const bin = join(process.cwd(), 'bin/pdd.mjs');
const roots = [];
after(() => { for (const root of roots) rmSync(root,{recursive:true,force:true}); });
function project({ resources = [], expected = 'hello\n', implementation = {kind:'cli',command:'node app.mjs'}, story = '1. A result.', change = () => {}, interfaceChange = () => {}, app = "process.stdin.setEncoding('utf8');let s='';for await (const c of process.stdin) s+=c;process.stdout.write(process.argv[2]+s);\n" } = {}) {
 const root=mkdtempSync(join(process.cwd(),'.compiled-test-')); roots.push(root); spawnSync('git',['init','-q',root]);
 for(const d of ['prompts','tests','user_stories']) mkdirSync(join(root,d));
 writeFileSync(join(root,'app.mjs'),app);
 const iface = {status:'draft',prose_sha256:'HASH',entries:[{operation:'main',implementation,input_schema:{type:'object',properties:{argv:{type:'array',items:{type:'string'}},stdin:{type:'string'}},required:['argv'],additionalProperties:false},result_schema:{type:'object',properties:{stdout:{type:'string'},stderr:{type:'string'},exit_code:{type:'integer'}},required:['stdout','stderr','exit_code'],additionalProperties:false},errors:['bad-input']}],resources,conventions:[{path:'/entries/0/input_schema',convention:'cli'},{path:'/entries/0/result_schema',convention:'cli'}],calls:[],limits:{max_steps:4,max_model_calls:2}};
 interfaceChange(iface);
 const prompt = '# app\n\n<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify(iface)+'\n```\n</details>\n'; writeFileSync(join(root,'prompts/app.prompt.md'),prompt.replace('HASH',proseSha256(prompt)));
 writeFileSync(join(root,'user_stories/demo.md'),'# Demo\n\n## Acceptance criteria\n\n'+story+'\n');
 const doc={schema_version:'prompt-runtime.program-scenario.v1',story_path:'user_stories/demo.md',criteria:[{id:'AC1',text:'A result.'}],initial_world:{},simulation:{},context:[],steps:[{step_id:'one',entry_path:'prompts/app.prompt.md',operation:'main',input:{argv:['hello'],stdin:'\n'},checks:[{criterion_id:'AC1',target:'result',path:'/stdout',op:'equals',value:expected},{criterion_id:'AC1',target:'result',path:'/exit_code',op:'equals',value:0},{criterion_id:'AC1',target:'result',path:'/stderr',op:'equals',value:''}]}]};
 change(doc); writeFileSync(join(root,'tests/demo.json'),JSON.stringify(doc));
 spawnSync('git',['add','.'],{cwd:root}); spawnSync('git',['-c','user.name=test','-c','user.email=test@example.com','commit','-qm','fixture'],{cwd:root}); return root;
}
function run(root){return spawnSync(process.execPath,[bin,'test','--target','code','demo','--json'],{cwd:root,encoding:'utf8',env:{...process.env,GH_TOKEN:'',GITHUB_TOKEN:'',PDD_RUNTIME_URL:'http://127.0.0.1:1'}});}
function outcome(root){const out=run(root); assert.ok(out.stdout, out.stderr);return {out,data:JSON.parse(out.stdout)};}
test('replays CLI arguments and stdin and records commit',()=>{const root=project();const {out,data}=outcome(root);assert.equal(out.status,0,out.stderr);assert.equal(data.stories[0].status,'passed');assert.match(data.commit,/^[0-9a-f]{40}$/);assert.equal(data.ai_calls,0);assert.equal(JSON.parse(readFileSync(join(root,'.pdd/code-test/latest.json'))).commit,data.commit);});
test('mismatch fails and resource steps are not run',()=>{const bad=outcome(project({expected:'wrong'}));assert.notEqual(bad.out.status,0);assert.equal(bad.data.stories[0].status,'failed');const unrun=outcome(project({resources:[{name:'db',kind:'port'}]}));assert.notEqual(unrun.out.status,0);assert.equal(unrun.data.stories[0].steps[0].status,'not run');});
test('Story criteria cannot be silently omitted or changed',()=>{for (const story of ['1. A result.\n2. Another result.', '1. A different result.']) {const {out,data}=outcome(project({story}));assert.notEqual(out.status,0);assert.notEqual(data.stories[0].status,'passed');}});
test('expected errors are never silently ignored',()=>{const {out,data}=outcome(project({change:doc=>{doc.steps[0].expected_error='bad-input';}}));assert.notEqual(out.status,0);assert.equal(data.stories[0].status,'not run');});
test('passes arguments literally, stdin, nonzero exit and stderr',()=>{const marker='$(touch SHOULD_NOT_EXIST)';const root=project({app:"process.stdin.setEncoding('utf8');let s='';for await(const c of process.stdin)s+=c;process.stdout.write(JSON.stringify(process.argv.slice(2))+s);process.stderr.write('problem\\n');process.exitCode=7;",change:doc=>{const s=doc.steps[0];s.input={argv:[marker,'two words'],stdin:'input\n'};s.checks[0].value=JSON.stringify([marker,'two words'])+'input\n';s.checks[1].value=7;s.checks[2].value='problem\n';}});const {out,data}=outcome(root);assert.equal(out.status,0,out.stderr);assert.equal(data.stories[0].status,'passed');assert.equal(existsSync(join(root,'SHOULD_NOT_EXIST')),false);});
test('bounded unsupported bindings and checks never pass',()=>{const cases=[
 {implementation:null}, {implementation:{kind:'http',command:'node app.mjs'}}, {implementation:{kind:'cli',command:'node app.mjs; touch BAD'}},
 {resources:[{name:'db',kind:'port'}]}, {change:d=>{d.initial_world={x:1};}}, {change:d=>{d.simulation={x:1};}},
 {change:d=>{d.steps[0].checks[0].target='world';}}, {change:d=>{d.steps[0].checks[0].path='/other';}}, {change:d=>{d.steps[0].checks[0].op='contains';}},
 {change:d=>{d.steps[0].checks=[];}}, {change:d=>{d.steps[0].input.argv=[3];}}
 ];for(const spec of cases){const {out,data}=outcome(project(spec));assert.notEqual(out.status,0,JSON.stringify(spec));assert.notEqual(data.stories[0].status,'passed',JSON.stringify(spec));assert.ok(data.stories[0].steps.every(step=>step.status!=='passed'),JSON.stringify(spec));}});

test('lint preflight names tested entries missing implementation',()=>{
 const missing=project({implementation:null});
 const path=join(missing,'prompts/app.prompt.md');
 writeFileSync(path,readFileSync(path,'utf8').replace('\"implementation\":null,',''));
 for(const [root,expectWarning] of [[missing,true],[project(),false]]) {
  const found=findTests({root}); const result=preflight({root,found,selected:found.tests});
  const warnings=result.warnings.filter(line=>line.includes('has no implementation declaration'));
  if(expectWarning) assert.deepEqual(warnings,['Warning: prompts/app.prompt.md entry main has no implementation declaration.']);
  else assert.deepEqual(warnings,[]);
 }
});

test('default selection includes an untested Story and cannot pass',()=>{
 const root=project(); writeFileSync(join(root,'user_stories/other.md'),'# Other\n\n## Acceptance criteria\n\n1. Another result.\n');
 const out=spawnSync(process.execPath,[bin,'test','--target','code','--json'],{cwd:root,encoding:'utf8'});
 assert.notEqual(out.status,0); assert.match(out.stdout+out.stderr,/other/i);
});
test('scenario cannot name a different Story or claim partial coverage',()=>{
 for (const change of [d=>{d.story_path='user_stories/other.md';},d=>{d.criteria_scope=['AC1'];},d=>{d.check_exemptions=[{criterion_id:'AC1'}];}]) {
  const {out,data}=outcome(project({change})); assert.notEqual(out.status,0); assert.notEqual(data.stories[0].status,'passed');
 }
});
test('stale or invalid Runtime interfaces cannot pass',()=>{
 const edits=[s=>s.replace('"status":"draft"','"status":"unknown"'),s=>s.replace('"status":"draft",',''),s=>s.replace(/"prose_sha256":"[a-f0-9]+"/,'"prose_sha256":"stale"'),s=>s.replace('"input_schema":{','"input_schema":{"unsupported_keyword":true,')];
 for(const edit of edits){const root=project();const path=join(root,'prompts/app.prompt.md');writeFileSync(path,edit(readFileSync(path,'utf8')));const {out,data}=outcome(root);assert.notEqual(out.status,0);assert.notEqual(data.stories[0].status,'passed');}
});

test('report distinguishes clean and modified source',()=>{
 const clean=project(); assert.equal(outcome(clean).data.dirty,false);
 const modified=project(); writeFileSync(join(modified,'app.mjs'),readFileSync(join(modified,'app.mjs'),'utf8')+'\n'); assert.equal(outcome(modified).data.dirty,true);
});

test('native-only declarations stay not run with reason and do not execute',()=>{
 const root=project({app:"import {writeFileSync} from 'node:fs';writeFileSync('EXECUTED','yes');process.stdout.write('hello\\n');"});
 const path=join(root,'prompts/app.prompt.md'); const text=readFileSync(path,'utf8');
 writeFileSync(path,text.replace('"status":"draft"','"kind":"native-only","reason":"The hardware port requires a physical device.","status":"draft"'));
 const {out,data}=outcome(root); assert.notEqual(out.status,0); assert.equal(data.stories[0].status,'not run');
 assert.match(JSON.stringify(data),/hardware port requires a physical device/); assert.equal(existsSync(join(root,'EXECUTED')),false);
});

function selected(cwd, ...words) {
 return spawnSync(process.execPath,[bin,'test','--target','code',...words,'--json'],{cwd,encoding:'utf8'});
}
test('launch exception is not run and later steps and Stories execute and are saved',()=>{
 const root=project({change:d=>{d.steps[0].input.argv=['bad\u0000arg'];d.steps.push({...structuredClone(d.steps[0]),step_id:'later',input:{argv:['hello'],stdin:'\n'}});}});
 const doc=JSON.parse(readFileSync(join(root,'tests/demo.json'),'utf8'));
 doc.story_path='user_stories/other.md'; doc.steps=[{...doc.steps[1],step_id:'other'}];
 writeFileSync(join(root,'user_stories/other.md'),'# Other\n\n## Acceptance criteria\n\n1. A result.\n');
 writeFileSync(join(root,'tests/other.json'),JSON.stringify(doc));
 const out=selected(root,'demo','other'); assert.equal(out.status,1,out.stderr);
 const report=JSON.parse(out.stdout), demo=report.stories.find(s=>s.story==='user_stories/demo.md'), other=report.stories.find(s=>s.story==='user_stories/other.md');
 assert.equal(demo.status,'not run'); assert.equal(demo.steps[0].status,'not run'); assert.match(demo.steps[0].reason,/Command did not complete/);
 assert.equal(demo.steps[1].status,'passed'); assert.equal(other.status,'passed');
 assert.deepEqual(JSON.parse(readFileSync(join(root,'.pdd/code-test/latest.json'),'utf8')),report);
});
test('step simulation overrides cannot execute the CLI',()=>{
 const app="import {writeFileSync} from 'node:fs';writeFileSync('EXECUTED','yes');process.stdout.write('hello\\n');";
 const blocked=project({app,change:d=>{d.steps[0].simulation_overrides={anything:{action:'fixture'}};}});
 const out=selected(blocked,'demo'); assert.equal(out.status,1); assert.match(out.stdout,/not run/i); assert.match(out.stdout,/simulation/i); assert.equal(existsSync(join(blocked,'EXECUTED')),false);
 const empty=project({change:d=>{d.steps[0].simulation_overrides={};}}); assert.equal(selected(empty,'demo').status,0);
});
test('directory selections include untested Stories once',()=>{
 const root=project(); mkdirSync(join(root,'user_stories/scope')); writeFileSync(join(root,'user_stories/scope/missing.md'),'# Missing\n\n## Acceptance criteria\n\n1. Missing.\n');
 for(const selectors of [['.'],['user_stories/'],['user_stories/scope'],['.','user_stories/','demo']]) {
  const out=selected(root,...selectors); assert.equal(out.status,1, out.stderr); const report=JSON.parse(out.stdout); assert.equal(report.stories.filter(s=>s.story==='user_stories/scope/missing.md').length,1); assert.equal(report.stories.find(s=>s.story==='user_stories/scope/missing.md').status,'not run');
 }
 assert.equal(selected(root,'user_stories/scope/missing.md').status,2);
});
test('selection paths resolve from nested invocation directory and stay bounded',()=>{
 const root=project(); mkdirSync(join(root,'scope/tests'),{recursive:true}); mkdirSync(join(root,'scope-extra/tests'),{recursive:true});
 const original=JSON.parse(readFileSync(join(root,'tests/demo.json'),'utf8'));
 for(const name of ['scope','scope-extra']) {const doc={...original,story_path:`user_stories/${name}.md`};writeFileSync(join(root,`user_stories/${name}.md`),'# Story\n\n## Acceptance criteria\n\n1. A result.\n');writeFileSync(join(root,`${name}/tests/${name}.json`),JSON.stringify(doc));}
 for(const selector of ['.','tests/scope.json']) {const out=selected(join(root,'scope'),selector);assert.equal(out.status,0,out.stderr);const stories=JSON.parse(out.stdout).stories;assert.deepEqual(stories.map(s=>s.story),['user_stories/scope.md']);}
 assert.equal(selected(join(root,'scope'),'demo').status,0);
 assert.equal(selected(join(root,'scope'),'/').status,2);
 assert.equal(selected(join(root,'scope'),'../../').status,2);
});
test('missing paths from a nested directory do not select root Stories',()=>{
 const root=project(); mkdirSync(join(root,'scope'));
 for(const selector of ['tests/demo.json','./user_stories/demo.md']) {
  const out=selected(join(root,'scope'),selector);
  assert.equal(out.status,2, `selector ${selector} unexpectedly selected a Story: ${out.stdout}`);
 }
});

test('explicit selections include nested fixture Stories while unqualified selection excludes them',()=>{
 const root=project(); const fixture='test/fixtures/sample';
 mkdirSync(join(root,fixture,'user_stories'),{recursive:true}); mkdirSync(join(root,fixture,'tests'),{recursive:true});
 const doc=JSON.parse(readFileSync(join(root,'tests/demo.json'),'utf8')); doc.story_path=`${fixture}/user_stories/nested.md`;
 writeFileSync(join(root,fixture,'user_stories/nested.md'),'# Nested\n\n## Acceptance criteria\n\n1. A result.\n');
 writeFileSync(join(root,fixture,'tests/nested.json'),JSON.stringify(doc));
 for(const selector of ['nested',`${fixture}/user_stories/nested.md`,`${fixture}/tests/nested.json`,fixture]) {
  const out=selected(root,selector); assert.equal(out.status,0,`${selector}: ${out.stderr}`);
  assert.deepEqual(JSON.parse(out.stdout).stories.map(s=>s.story),[doc.story_path]);
 }
 const all=selected(root); assert.equal(all.status,0,all.stderr);
 assert.deepEqual(JSON.parse(all.stdout).stories.map(s=>s.story),['user_stories/demo.md']);
});

test('malformed world and simulation containers never execute or save a pass',()=>{
 const app="import {writeFileSync} from 'node:fs';writeFileSync('EXECUTED','yes');process.stdout.write('hello\\n');";
 for(const field of ['initial_world','simulation','simulation_overrides']) for(const value of [[],null,false,42,'bad']) {
  const root=project({app,change:d=>{if(field==='simulation_overrides') d.steps[0][field]=value; else d[field]=value;}});
  const promptPath=join(root,'prompts/app.prompt.md');
  writeFileSync(promptPath,readFileSync(promptPath,'utf8').replace('"status":"draft"','"status":"approved"'));
  const out=selected(root,'demo'); assert.equal(out.status,1,`${field}=${JSON.stringify(value)}: ${out.stderr}`);
  const report=JSON.parse(out.stdout); assert.equal(report.stories[0].status,'not run',field);
  assert.ok(report.stories[0].steps.every(step=>step.status==='not run' && typeof step.reason==='string' && step.reason.trim()),field);
  assert.equal(existsSync(join(root,'EXECUTED')),false,field);
  assert.equal(JSON.parse(readFileSync(join(root,'.pdd/code-test/latest.json'),'utf8')).stories[0].status,'not run',field);
 }
 for(const change of [d=>{delete d.simulation;},d=>{d.steps[0].simulation_overrides={};}]) assert.equal(selected(project({change}),'demo').status,0);
});

test('malformed CLI interfaces never launch or save a pass',()=>{
 const app="import {writeFileSync} from 'node:fs';writeFileSync('EXECUTED','yes');process.stdout.write('hello\\n');";
 const cases=[
  ['resources object',i=>{i.resources={name:'db',kind:'port'};}],
  ['calls object',i=>{i.calls={operation:'helper',target:'prompts/helper.prompt.md'};}],
  ...['resources','calls'].flatMap(field=>[null,false,42,'bad',{}].map(value=>[`${field} ${JSON.stringify(value)}`,i=>{i[field]=value;} ])),
  ['entries object',i=>{i.entries={operation:'main'};}], ['null entry',i=>{i.entries=[null];}],
  ['conventions object',i=>{i.conventions={};}], ['null convention',i=>{i.conventions=[null];}],
  ['missing input schema',i=>{delete i.entries[0].input_schema;}], ['missing result schema',i=>{delete i.entries[0].result_schema;}],
  ['invalid result schema',i=>{i.entries[0].result_schema={type:'invalid'};}],
 ];
 for(const [label,interfaceChange] of cases){
  const root=project({app,interfaceChange:i=>{i.status='approved';interfaceChange(i);}}); const out=selected(root,'demo');
  assert.equal(out.status,1,`${label}: ${out.stderr} ${out.stdout}`);
  const report=JSON.parse(out.stdout); assert.equal(report.stories[0].status,'not run',label);
  assert.ok(report.stories[0].steps.every(step=>step.status==='not run' && step.reason),label);
  assert.equal(existsSync(join(root,'EXECUTED')),false,label);
  assert.equal(JSON.parse(readFileSync(join(root,'.pdd/code-test/latest.json'),'utf8')).stories[0].status,'not run',label);
 }
 for(const field of ['resources','calls']) {const root=project({interfaceChange:i=>{i.status='approved';delete i[field];}});assert.equal(selected(root,'demo').status,0,field);}
});

test('plain-text failure prints scenario, step, criterion, path and expected vs actual',()=>{
 const root=project({expected:'23.00\n',app:"process.stdout.write('20.15\\n');process.exitCode=2;\n"});
 const out=spawnSync(process.execPath,[bin,'test','--target','code','demo'],{cwd:root,encoding:'utf8',env:{...process.env,GH_TOKEN:'',GITHUB_TOKEN:'',PDD_RUNTIME_URL:'http://127.0.0.1:1'}});
 assert.equal(out.status,1);
 assert.match(out.stdout,/^FAILED\s+user_stories\/demo\.md\s+[0-9a-f]{40}\s+clean/m);
 assert.match(out.stdout,/tests\/demo\.json · step one · AC1 \/stdout: expected "23\.00\\n", actual "20\.15\\n"/);
 assert.match(out.stdout,/tests\/demo\.json · step one · AC1 \/exit_code: expected 0, actual 2/);
});

test('preserves 64-bit integers above 2^53 in scenario JSON and CLI streams',()=>{
 const root=project({expected:'9007199254740994\n',app:"process.stdin.setEncoding('utf8');let s='';for await(const c of process.stdin)s+=c;const id=BigInt(s.trim());process.stdout.write(String(id+1n)+'\\n');\n"});
 const raw=readFileSync(join(root,'tests/demo.json'),'utf8')
  .replace('"checks":[','"checks":[{"criterion_id":"AC1","target":"result","path":"/exit_code","op":"equals","value":9007199254740993},')
  .replace('"stdin":"\\n"','"stdin":"9007199254740993\\n"');
 writeFileSync(join(root,'tests/demo.json'),raw);
 spawnSync('git',['add','tests/demo.json'],{cwd:root});
 spawnSync('git',['-c','user.name=test','-c','user.email=test@example.com','commit','-qm','bigint'],{cwd:root});
 const failText=spawnSync(process.execPath,[bin,'test','--target','code','demo'],{cwd:root,encoding:'utf8',env:{...process.env,GH_TOKEN:'',GITHUB_TOKEN:'',PDD_RUNTIME_URL:'http://127.0.0.1:1'}});
 assert.equal(failText.status,1);
 assert.match(failText.stdout,/expected 9007199254740993, actual 0/);
 assert.match(readFileSync(join(root,'.pdd/code-test/latest.json'),'utf8'),/"expected": 9007199254740993/);
});
