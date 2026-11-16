import { test } from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, readFileSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { proseSha256, parseScenarioJson, stringifyScenarioJson } from '../src/runtime-seam.mjs';
import { save, commit, clean, report, seamModule } from './helpers/code-call-project.mjs';

// Synthetic data only. This has the command/read shape of the reported locale
// case, with no captured environment, conversation or operational fixture.
const localeKeys = ['PATH','LANG','LC_ALL','HOME','XDG_CONFIG_HOME','XDG_CACHE_HOME','XDG_DATA_HOME',
  'XDG_STATE_HOME','XDG_RUNTIME_DIR','CLOUDSDK_CONFIG','NO_COLOR','TERM','PYTHONNOUSERSITE'];
const locale = Object.fromEntries(localeKeys.map(key => [key,key === 'LANG' ? 'C.UTF-8' : 'synthetic']));
const emptySchema = {type:'object',properties:{},required:[],additionalProperties:false};
const localeSchema = {type:'object',properties:Object.fromEntries(localeKeys.map(key => [key,{type:'string'}])),
  required:localeKeys,additionalProperties:false};
const scenarioPath = 'tests/recorded-command.json';
const promptPath = 'prompts/read.prompt.md';
const adapter = `import {read} from './application.mjs';
import {writeFileSync} from 'node:fs';
import {isDeepStrictEqual} from 'node:util';
import {parseScenarioJson,stringifyScenarioJson,exactValue} from ${JSON.stringify(seamModule)};
writeFileSync('ADAPTER_LAUNCHED','yes');
let raw='';for await(const chunk of process.stdin)raw+=chunk;
writeFileSync('request.json',raw);
const request=parseScenarioJson(raw),world=request.initial_world;
let calls=0;
const client={status(args){
  const binding=request.simulation['client.status'];
  if(binding.action!=='fixture.lookup'||binding.result_template!==null||binding.result_value_pointer!=='')throw Error('unsupported fixture');
  const tokens=binding.world_pointer.slice(1).split('/').map(t=>t.replace(/~1/g,'/').replace(/~0/g,'~'));
  let cursor=world;for(const key of tokens.slice(0,-1))cursor=cursor[key];
  const key=tokens.at(-1),next=cursor[key]+1;
  const match=binding.cases.find(item=>item.call_index===next&&isDeepStrictEqual(exactValue(item.args),exactValue(args)));
  if(!match)throw Error('missing saved reply');
  cursor[key]=next;calls++;
  writeFileSync('recorded-call.json',stringifyScenarioJson({args,call_index:next,result:match.result}));
  return match.result;
}};
const result=read(client,request.input);
const response={schema_version:request.schema_version,result,world,calls:{resources:{'read-client-status':calls},internal:{}}};
writeFileSync('response.json',stringifyScenarioJson(response));
process.stdout.write(stringifyScenarioJson(response));
`;

function project(t,{change=()=>{},interfaceChange=()=>{},appChange=text=>text}={}) {
  const root=mkdtempSync(join(tmpdir(),'pdd-recorded-command-'));t.after(()=>clean(root));
  assert.equal(spawnSync('git',['init','-q',root]).status,0);
  const iface={status:'draft',prose_sha256:'HASH',entries:[{operation:'read',input_schema:emptySchema,result_schema:localeSchema,errors:[],
    implementation:{kind:'call',command:[process.execPath,'adapter.mjs'],symbol:'read'}}],calls:[],
    resources:[{name:'client',kind:'command',access:'read',operations:[{name:'status',access:'read',arguments_schema:emptySchema,result_schema:localeSchema}]}],
    limits:{max_steps:4,max_model_calls:3},conventions:[]};
  interfaceChange(iface);
  const prompt='# Read saved locale\n\nCall client.status once with {} and return its result unchanged.\n\n'+
    '[Binding](../runtime/live-resources.json) declares the live command. Native replay uses the saved reply.\n\n'+
    '<details><summary>Runtime interface</summary>\n\n```json\n'+stringifyScenarioJson(iface,2)+'\n```\n</details>\n';
  save(root,promptPath,prompt.replace('HASH',proseSha256(prompt)));
  save(root,'user_stories/recorded-command.md','# Read saved locale\n\n## Acceptance criteria\n\n1. The saved locale is returned.\n');
  const doc={schema_version:'prompt-runtime.program-scenario.v1',story_path:'user_stories/recorded-command.md',
    criteria:[{id:'AC1',text:'The saved locale is returned.'}],initial_world:{fixture_counters:{status:0},note:'keep'},
    simulation:{'client.status':{action:'fixture.lookup',world_pointer:'/fixture_counters/status',
      cases:[{args:{},call_index:1,result:structuredClone(locale)}],result_template:null,result_value_pointer:''}},context:[],
    steps:[{step_id:'read-once',entry_path:promptPath,operation:'read',input:{},
      checks:[{criterion_id:'AC1',target:'result',path:'/LANG',op:'equals',value:'C.UTF-8'}]}]};
  change(doc);save(root,scenarioPath,stringifyScenarioJson(doc,2));
  save(root,'application.mjs',appChange('export function read(client,input){return client.status(input);}\n'));
  save(root,'adapter.mjs',adapter);
  save(root,'live-command.mjs',"import {writeFileSync} from 'node:fs';writeFileSync('LIVE_COMMAND_RAN','unexpected');\n");
  save(root,'runtime/live-resources.json',JSON.stringify({schema_version:'prompt-runtime.live-resource-bindings.v1',operations:[{
    resource:'client',operation:'status',kind:'command',access:'read',template:{executable:process.execPath,subcommand:['live-command.mjs'],argv:[]}}]}));
  commit(root);return root;
}
const load=(root,path)=>parseScenarioJson(readFileSync(join(root,path),'utf8'));
const run=root=>report(root,{words:['recorded-command']});
const step=data=>data.stories[0].steps[0];

test('recorded command/read: actual CLI and native app execute the unchanged locale assertion',t=>{
  const root=project(t),scenario=readFileSync(join(root,scenarioPath),'utf8'),prompt=readFileSync(join(root,promptPath),'utf8');
  const {out,data}=run(root);
  assert.equal(out.status,0,`RECORDED_COMMAND_REQUIRED: ${out.stderr}\n${out.stdout}`);
  assert.equal(data.ai_calls,0);assert.equal(data.dirty,false);assert.equal(step(data).status,'passed');
  assert.equal(step(data).checks.length,1);assert.deepEqual(step(data).checks[0],{
    criterion_id:'AC1',target:'result',path:'/LANG',op:'equals',status:'passed',expected:'C.UTF-8',actual:'C.UTF-8'});
  const request=load(root,'request.json');
  assert.deepEqual(Object.keys(request).sort(),['schema_version','operation','symbol','input','initial_world','simulation'].sort());
  assert.deepEqual(request.simulation,parseScenarioJson(scenario).simulation);assert.deepEqual(request.input,{});
  assert.deepEqual(load(root,'recorded-call.json'),{args:{},call_index:1,result:locale});
  const response=load(root,'response.json');assert.deepEqual(response.result,locale);
  assert.deepEqual(response.world,{fixture_counters:{status:1},note:'keep'});
  assert.deepEqual(response.calls,{resources:{'read-client-status':1},internal:{}});
  assert.deepEqual(load(root,'.pdd/code-test/latest.json'),data);
  assert.equal(readFileSync(join(root,scenarioPath),'utf8'),scenario);assert.equal(readFileSync(join(root,promptPath),'utf8'),prompt);
  assert.equal(existsSync(join(root,'LIVE_COMMAND_RAN')),false);
});

test('wrong native locale fails the original assertion after consuming the recorded command reply',t=>{
  const root=project(t,{appChange:text=>text.replace('return client.status(input);',"return {...client.status(input),LANG:'WRONG_NATIVE_LOCALE'};")});
  const before=readFileSync(join(root,scenarioPath),'utf8'),{out,data}=run(root);
  assert.equal(out.status,1);assert.equal(step(data).status,'failed');assert.equal(step(data).checks.length,1);
  assert.equal(step(data).checks[0].status,'failed');assert.equal(step(data).checks[0].expected,'C.UTF-8');
  assert.equal(step(data).checks[0].actual,'WRONG_NATIVE_LOCALE');
  assert.equal(load(root,'recorded-call.json').result.LANG,'C.UTF-8');
  assert.equal(load(root,'response.json').calls.resources['read-client-status'],1);
  assert.equal(readFileSync(join(root,scenarioPath),'utf8'),before);assert.equal(existsSync(join(root,'LIVE_COMMAND_RAN')),false);
});

test('missing, malformed, unsupported and write-command fixtures refuse before native launch',t=>{
  const variants=[
    {change:d=>{delete d.simulation['client.status'];}},
    {change:d=>{d.simulation['client.status'].action='command.run';}},
    {change:d=>{d.simulation['client.status'].cases[0].args={extra:'invalid'};}},
    {change:d=>{d.simulation['client.status'].cases[0].result.LANG=42;}},
    {change:d=>{delete d.simulation['client.status'].cases[0].result.PATH;}},
    {interfaceChange:i=>{i.resources[0].access='write';}},
    {interfaceChange:i=>{i.resources[0].operations[0].access='write';}},
    {interfaceChange:i=>{delete i.resources[0].access;}},
    {interfaceChange:i=>{delete i.resources[0].operations[0].access;}},
    {interfaceChange:i=>{i.resources[0].kind='http';}},
  ];
  for(const options of variants){
    const root=project(t,options),{out,data}=run(root);
    assert.equal(out.status,1,out.stderr);assert.equal(step(data).status,'not run');assert.equal(step(data).checks,undefined);
    assert.equal(existsSync(join(root,'ADAPTER_LAUNCHED')),false);assert.equal(existsSync(join(root,'LIVE_COMMAND_RAN')),false);
  }
});

test('nonmatching recorded command index stops native execution with no live fallback',t=>{
  const root=project(t,{change:d=>{d.simulation['client.status'].cases[0].call_index=2;}}),{out,data}=run(root);
  assert.equal(out.status,1);assert.equal(step(data).status,'not run');assert.match(step(data).reason,/exit 1/);
  assert.equal(existsSync(join(root,'ADAPTER_LAUNCHED')),true);assert.equal(existsSync(join(root,'recorded-call.json')),false);
  assert.equal(existsSync(join(root,'response.json')),false);assert.equal(existsSync(join(root,'LIVE_COMMAND_RAN')),false);
});
