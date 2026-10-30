import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {interfaceSchemaProblems,readPrompt,findTests,preflight,proseSha256} from '../src/runtime-preflight.mjs';
import {runCheck} from '../src/runtime-client.mjs';
import {harbor,PLACE,portsFor,fakeRuntime} from './runtime-fake.mjs';
const empty={type:'object',properties:{},required:[],additionalProperties:false};
const iface=limits=>({status:'draft',prose_sha256:'',entries:[{operation:'value',input_schema:empty,result_schema:empty,errors:[]}],calls:[],resources:[],limits});
const cases=JSON.parse(readFileSync(new URL('./fixtures/runtime-limit-cases.json',import.meta.url),'utf8')).cases;
for(const row of cases)test(`2676 limits: ${row.name}`,()=>{
 const value=iface(row.limits),before=structuredClone(value),problems=interfaceSchemaProblems(value);
 assert.deepEqual(value,before,'limits checks must not change authored values');
 if(row.code===null){assert.deepEqual(problems,[]);return;}
 const problem=problems.find(problem=>problem.code===row.code&&problem.pointer===row.pointer);
 assert.ok(problem,JSON.stringify(problems));assert.match(problem.hint,/Fix|Set|Add|Remove/);assert.match(problem.rule+' '+problem.hint,/1|exactly/);
});
test('2676 absent limits uses the runtime interface-shape reason',()=>{
 const value=iface();delete value.limits;const problems=interfaceSchemaProblems(value);
 assert.ok(problems.some(p=>p.code==='invalid-interface'&&p.pointer==='/limits'));
});
function prompt(repo,path,limitsJSON,{calls=[],schema=empty}={}){
 const value=iface(null);value.entries[0].input_schema=schema;value.calls=calls;
 const prose='# Synthetic limits operation\n\nReturn an empty object.\n';
 let text=prose+'<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify(value).replace('"limits":null','"limits":'+limitsJSON)+'\n```\n</details>\n';
 text=text.replace('"prose_sha256":""','"prose_sha256":'+JSON.stringify(proseSha256(text)));
 writeFileSync(join(repo,path),text);return text;
}
const tokens=[['0','invalid-limits'],['1',null],['2',null],['-1','invalid-limits'],['0.9','invalid-limits'],['1.1','invalid-limits'],['1.0','invalid-limits'],['1e0','invalid-limits'],['1E+0','invalid-limits'],['0.99999999999999999','invalid-limits'],['9007199254740992.5','invalid-limits'],['9007199254740993',null],['1'+'0'.repeat(400),null]];
for(const key of ['max_steps','max_model_calls'])for(const [token,code] of tokens)test(`2676 source token ${key}: ${token.length>25?'large integer':token}`,t=>{
 const setup=harbor(t),other=key==='max_steps'?'max_model_calls':'max_steps';
 const text=prompt(setup.repo,PLACE,`{"${key}":${token},"${other}":1}`);
 const value=readPrompt(setup.repo,new Set([PLACE]),PLACE);
 const problems=interfaceSchemaProblems(value.interface);
 assert.equal(problems.some(p=>p.code==='invalid-limits'&&p.pointer==='/limits/'+key),code!==null,JSON.stringify(problems));
 assert.equal(readFileSync(join(setup.repo,PLACE),'utf8'),text);
});
function scanned(setup){const found=findTests({root:setup.repo});return preflight({root:setup.repo,found,selected:found.tests.filter(t=>t.path==='tests/place-order.json')}).rows[0];}
function harborLimit(setup,limitsJSON,options){
 const old=readFileSync(join(setup.repo,PLACE),'utf8');
 // Preserve the fixture's public operation/schemas and current prose hash.
 const text=old.replace(/"limits": \{[^}]+\}/,'"limits": '+limitsJSON);
 writeFileSync(join(setup.repo,PLACE),text);return text;
}
test('2676 called-prompt bad limits name the called file and field; unrelated bad limits stay unselected',t=>{
 const setup=harbor(t),child='prompts/child.prompt.md';
 prompt(setup.repo,child,'{"max_steps":1,"max_model_calls":0}');
 assert.deepEqual(scanned(setup).refusals,[]);
 const file=join(setup.repo,PLACE);const old=readFileSync(file,'utf8');
 writeFileSync(file,old.replace('"calls": []','"calls": [{"operation":"child","target":"'+child+'","target_operation":"value","max_calls":1}]'));
 const row=scanned(setup),refusal=row.refusals.find(r=>r.code==='invalid-limits');
 assert.ok(refusal,JSON.stringify(row.refusals));assert.equal(refusal.section,'/limits/max_model_calls');assert.match(refusal.message,/prompts\/child.prompt.md/);assert.match(refusal.hint,/1/);
});
for(const options of [{},{'--json':true}])test(`2676 normal check refuses before auth/network: ${JSON.stringify(options)}`,async t=>{
 const setup=harbor(t);const before=harborLimit(setup,'{"max_steps":4,"max_model_calls":0}');
 const testFile=join(setup.repo,'tests/place-order.json'),testBefore=readFileSync(testFile,'utf8');
 const {ports,clock}=portsFor({HOME:setup.home,PDD_RUNTIME_URL:'http://127.0.0.1:9',PDD_STATE_DIR:setup.state},{gh:()=>assert.fail('no authentication'),fetch:()=>assert.fail('no upload')});
 const code=await runCheck({cwd:setup.repo,words:['place-order'],options},ports);
 assert.equal(code,4,ports.stdout.text+ports.stderr.text);assert.equal(clock.uuids,0);
 const text=ports.stdout.text+ports.stderr.text;assert.match(text,/invalid-limits/);assert.match(text,/max_model_calls/);assert.match(text,/1/);assert.match(text,/Fix|Set/);
 if(options['--json'])assert.equal(JSON.parse(ports.stdout.text).rows[0].refusals[0].code,'invalid-limits');
 assert.equal(readFileSync(join(setup.repo,PLACE),'utf8'),before);assert.equal(readFileSync(testFile,'utf8'),testBefore);
});
test('2676 existing schema and hash refusals still apply with valid limits',t=>{
 const setup=harbor(t);harborLimit(setup,'{"max_steps":1,"max_model_calls":1}');
 let text=readFileSync(join(setup.repo,PLACE),'utf8');writeFileSync(join(setup.repo,PLACE),text.replace('"type": "object"','"type": ["object", "null"]'));
 assert.ok(scanned(setup).refusals.some(r=>r.code==='graph-schema-type-list'));
 writeFileSync(join(setup.repo,PLACE),text.replace('Use this menu.','Use this new menu.'));
 assert.equal(scanned(setup).refusals[0].code,'interface-stale');
});

for(const literal of ['"max_steps":1,"max_steps":"1"','"max_steps":1,"max_steps":true','"max_steps":1,"max_steps":null','"max_steps":1.0,"max_steps":1'])
 test(`2676 duplicate JSON keys follow the last authored value: ${literal}`,t=>{
 const setup=harbor(t);prompt(setup.repo,PLACE,'{'+literal+',"max_model_calls":1}');
 const parsed=readPrompt(setup.repo,new Set([PLACE]),PLACE);
 const problems=interfaceSchemaProblems(parsed.interface);
 assert.equal(problems.some(p=>p.code==='invalid-limits'),!literal.endsWith('"max_steps":1'));
});

for(const json of [false,true])test(`2676 explicit lint stops invalid limits before auth/upload (json=${json})`,async t=>{
 const setup=harbor(t);const before=harborLimit(setup,'{"max_steps":4,"max_model_calls":0}');
 const {ports,clock}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:'http://127.0.0.1:9'},{gh:()=>assert.fail('no auth for invalid lint'),fetch:()=>assert.fail('no upload for invalid lint')});
 const code=await runCheck({cwd:setup.repo,words:['place-order'],options:{'--lint':true,...(json?{'--json':true}:{})}},ports);
 assert.equal(code,4);assert.equal(clock.uuids,0);
 const text=ports.stdout.text+ports.stderr.text;assert.match(text,/invalid-limits/);assert.match(text,/max_model_calls/);assert.match(text,/Fix/);assert.match(text,/1/);
 if(json){const result=JSON.parse(ports.stdout.text);assert.equal(result.lint_state,'refused');assert.equal(result.batch,null);assert.equal(result.problems[0].path,PLACE);assert.equal(result.problems[0].code,'invalid-limits');}
 assert.equal(readFileSync(join(setup.repo,PLACE),'utf8'),before);
});
test('2676 mixed lint selection reports other rows not run, never passed or uploaded',async t=>{
 const setup=harbor(t);const child='prompts/child.prompt.md';prompt(setup.repo,child,'{"max_steps":1,"max_model_calls":0}');
 const file=join(setup.repo,'tests/unknown-item.json'),doc=JSON.parse(readFileSync(file,'utf8'));doc.steps[0].entry_path=child;doc.steps[0].operation='value';writeFileSync(file,JSON.stringify(doc));
 const {ports,clock}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:'http://127.0.0.1:9'},{gh:()=>assert.fail('no auth for mixed invalid lint'),fetch:()=>assert.fail('no upload')});
 const code=await runCheck({cwd:setup.repo,options:{'--lint':true,'--json':true}},ports);
 assert.equal(code,4);assert.equal(clock.uuids,0);
 const result=JSON.parse(ports.stdout.text);assert.equal(result.rows.length,2);
 assert.equal(result.rows.find(row=>row.test==='tests/place-order.json').state,'not_run');assert.equal(result.rows.find(row=>row.test==='tests/unknown-item.json').state,'refused');
});
test('2676 valid limits keep explicit lint server-owned for unrelated schema errors',async t=>{
 const setup=harbor(t);harborLimit(setup,'{"max_steps":1,"max_model_calls":1}');
 const file=join(setup.repo,PLACE);writeFileSync(file,readFileSync(file,'utf8').replace('"type": "object"','"type": ["object", "null"]'));
 const fake=await fakeRuntime(t,(entry,f)=>{
  assert.equal(entry.command,'lint');const answer=f.lint(entry.request.requestId);
  answer.result.tests=[{path:'tests/place-order.json',verdict:'refused'}];
  answer.result.report.problems=[{code:'graph-schema-type-list',file:PLACE,pointer:'/entries/0/input_schema/type',message:'server-only fixture diagnosis',fix:'Use oneOf.'}];
  return {status:200,json:answer};
 });
 const {ports}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
 const code=await runCheck({cwd:setup.repo,words:['place-order'],options:{'--lint':true,'--json':true}},ports);
 assert.equal(code,4,ports.stdout.text+ports.stderr.text);assert.equal(fake.posts.length,1);assert.equal(fake.posts[0].request.complete,true);
 const result=JSON.parse(ports.stdout.text);assert.ok(result.problems.some(p=>p.message==='server-only fixture diagnosis'));
});
