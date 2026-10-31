import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,rmSync,existsSync,mkdirSync,readdirSync} from 'node:fs';
import {join} from 'node:path';
import {Readable} from 'node:stream';
import {runPdd} from '../src/pdd-cli.mjs';
import {proseSha256} from '../src/runtime-preflight.mjs';
import {harbor,fakeRuntime,portsFor,PLACE} from './runtime-fake.mjs';
const obj=(properties={},required=Object.keys(properties))=>({type:'object',properties,required,additionalProperties:false});
const string={type:'string'};
function prompt(root,path,iface,heading='final',deps='None.'){
 let text=`# ${heading}\n\nA deterministic program with fake effects.\n\n## Dependencies\n\n${deps}\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
 text=text.replace('"prose_sha256":""',`"prose_sha256":"${proseSha256(text)}"`);writeFileSync(join(root,path),text);
}
function iface(cli=true){return {status:'draft',prose_sha256:'',entries:[{operation:'main',input_schema:cli?obj({argv:{type:'array',items:string}}):obj({}),result_schema:cli?obj({stdout:string,stderr:string,exit_code:{type:'integer'}}):obj({ok:{type:'boolean'}}),errors:['declared']}],calls:[],resources:[],limits:{max_steps:1,max_model_calls:1},conventions:cli?['input_schema','result_schema'].map(k=>({path:`/entries/0/${k}`,convention:'cli'})):[]};}
async function harness(t,options={}){
 const spec=iface(options.cli!==false);options.edit?.(spec);
 const h=harbor(t,root=>{rmSync(join(root,'tests'),{recursive:true});rmSync(join(root,'user_stories'),{recursive:true});prompt(root,PLACE,spec);options.files?.(root,spec);});
 const fake=await fakeRuntime(t,(e,f)=>{
  if(e.command==='lint')return {status:200,json:f.lint(e.request.requestId)};
  if(e.command==='try')return {status:200,json:f.tryJob(e.request.requestId)};
  if(e.method==='DELETE')return {status:200,json:f.stopJob(e.headers['x-request-id'],e.url.split('/').at(-1))};
  if(e.json){const output=options.outputs?.[e.json.operation]??(options.cli===false?{ok:true}:{stdout:'program only\n',stderr:options.stderr??'',exit_code:options.exit??0});const report={verdict:'passed',error:null,replayed:false,provider_calls:1,remaining_calls:299,...options.report};const job={...f.job(e.json.requestId,'call','passed',{exitCode:0,output,world:options.world??{},refusals:options.refusals??[],report},options.calls??1),session_id:e.url.split('/')[3]};f.jobs.set(e.json.requestId,job);return options.reply?.(e,f,job)??{status:200,json:job};}
  if(f.jobs.has(e.url.split('/').at(-1)))return {status:200,json:f.jobs.get(e.url.split('/').at(-1))};
  return {status:404,json:{error:{code:'not-found',message:'Not found'}}};
 });
 const env={HOME:h.home,PDD_STATE_DIR:h.state,PDD_RUNTIME_URL:fake.origin,PATH:'/usr/bin:/bin'};
 const invoke=async(args=['list'],prefix=[],extra={})=>{const io=portsFor(env,{stdin:Readable.from([]),...extra});let code;try{code=await runPdd([...prefix,PLACE,...args],{cwd:h.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});}catch(error){assert.fail('public CLI must return a plain status: '+error.message);}return {code,out:io.ports.stdout.text,err:io.ports.stderr.text,...io};};
 return {...h,fake,invoke,spec,stored:name=>JSON.parse(readFileSync(join(h.repo,'.pdd/run/place_order',name),'utf8'))};
}
const pass=r=>assert.equal(r.code,0,r.err+r.out);
test('final direct receipt uses output/world, session300, bounded call and explicit false fresh',async t=>{
 const h=await harness(t,{world:{exact:'world'}}),r=await h.invoke();pass(r);assert.equal(r.out,'program only\n');assert.equal(h.fake.posts.find(p=>p.command==='try').request.max_calls,300);assert.equal(h.fake.jsonPosts[0].json.max_calls,1);assert.equal(h.fake.jsonPosts[0].json.fresh,false);assert.deepEqual(h.stored('world.json'),{exact:'world'});
});
test('nonTTY noargs prints only usable PATH without auth/session/child',async t=>{
 const h=await harness(t),r=await h.invoke([],[],{shell(){assert.fail('no child');},gh(){assert.fail('no auth');}});pass(r);assert.match(r.out,/^export PATH=.*:\$PATH.*# then: final --help\n$/);assert.equal(r.err,'');assert.equal(h.fake.posts.length,0);assert.equal(h.fake.jsonPosts.length,0);
});
test('empty optional typed input is local usage2 but piped {} is supplied input',async t=>{
 const h=await harness(t,{cli:false}),r=await h.invoke([]);assert.equal(r.code,2,r.err);assert.match(r.err,/usage:/i);assert.equal(r.clock.gh.length,0);assert.equal(h.fake.posts.length,0);const piped=await h.invoke([],[],{stdin:Readable.from(['{}'])});pass(piped);assert.equal(piped.out,'{"ok":true}\n');
});
test('typed usage identifies required flags, optional flags, enums and scalar types',async t=>{
 const h=await harness(t,{cli:false,edit(s){s.entries[0].input_schema=obj({name:string,size:{type:'string',enum:['S','M','L']},qty:{type:'integer'}},['name']);}});const r=await h.invoke([]);assert.equal(r.code,2);assert.match(r.err,/--name STRING/);assert.match(r.err,/\[--size S\|M\|L\]/);assert.match(r.err,/\[--qty INTEGER\]/);assert.equal(r.clock.gh.length,0);
});
for(const fresh of [false,true])test(`call always sends boolean fresh=${fresh}`,async t=>{const h=await harness(t);pass(await h.invoke(['list'],fresh?['--fresh']:[]));assert.equal(h.fake.jsonPosts[0].json.fresh,fresh);});
test('fresh preserves previous confirmed world and records full metadata',async t=>{
 const outside_calls=[{resource:'cloud',kind:'http',op:'deploy',summary:'cloud deploy app',level:'declared'}],chain=[{prompt:PLACE,operation:'main',call_index:null,max_calls:null}];const h=await harness(t,{world:{old:true},report:{outside_calls,call_chain:chain}});pass(await h.invoke());const r=await h.invoke(['again'],['--fresh']);pass(r);assert.deepEqual(h.stored('world.prev.json'),{old:true});const last=h.stored('last-run.json');assert.ok(last.session_id);assert.ok(last.report_url);assert.equal(last.exit_code,0);assert.deepEqual(last.outside_calls,outside_calls);assert.deepEqual(last.call_chain,chain);assert.match(r.err,/pdd: fresh start/);
});
test('outside calls render, quiet hides all own status, prefix json preserves receipt',async t=>{
 const outside_calls=[{resource:'cloud',kind:'http',op:'deploy',summary:'cloud deploy app',level:'declared'}];const h=await harness(t,{stderr:'program error\n',report:{outside_calls}});const normal=await h.invoke();pass(normal);assert.equal(normal.out,'program only\n');assert.match(normal.err,/pdd: fake calls \(nothing real was called\):/);assert.match(normal.err,/pdd:.*cloud deploy app.*declared/);const quiet=await h.invoke(['other'],['-q','--max-calls','25']);pass(quiet);assert.equal(quiet.err,'program error\n');const json=await h.invoke(['third'],['--json']);pass(json);const record=JSON.parse(json.out);assert.deepEqual(record.outside_calls,outside_calls);assert.equal(record.output.stdout,'program only\n');assert.equal(record.exit_code,0);assert.ok(record.session_id);assert.ok(record.report_url);
});
test('server replayed receipt reports cached0 despite provider usage receipt',async t=>{const h=await harness(t,{report:{replayed:true}}),r=await h.invoke();pass(r);assert.match(r.err,/cached · 0 AI calls/);});
for(const verdict of ['failed','refused'])test(`report ${verdict} preserves code, traceback total and details link`,async t=>{
 const call_chain=[{prompt:PLACE,operation:'main',call_index:1,max_calls:3}];const h=await harness(t,{report:{verdict,error:{code:verdict==='failed'?'declared':'session-call-cap',message:'Exact reason',fix:'Increase call allowance'},call_chain,call_chain_total:80}}),r=await h.invoke();assert.equal(r.code,verdict==='failed'?1:125,r.err);assert.match(r.err,/Exact reason/);assert.match(r.err,/Traceback \(prompt calls, most recent call last\):/);assert.match(r.err,/80|79/);assert.match(r.err,/details: http/);if(verdict==='refused'){assert.match(r.err,/pdd: refused/);assert.match(r.err,/Fix: Increase call allowance/);}assert.equal(r.out,'');
});
test('two CLI entries refuse before auth',async t=>{
 const h=await harness(t,{edit(s){s.entries.push({...s.entries[0],operation:'other'});s.conventions.push(...['input_schema','result_schema'].map(k=>({path:`/entries/1/${k}`,convention:'cli'})));}}),r=await h.invoke();assert.equal(r.code,2,r.err);assert.match(r.err,/one.*program|one.*command|multiple.*CLI/i);assert.equal(r.clock.gh.length,0);assert.equal(h.fake.posts.length,0);
});
test('CLI plus typed uses CLI default and explicit typed selector',async t=>{
 const h=await harness(t,{outputs:{quote:{}},edit(s){s.entries.push({operation:'quote',input_schema:obj({item:string}),result_schema:obj({}),errors:[]});}});
 pass(await h.invoke(['list']));assert.deepEqual(h.fake.jsonPosts[0].json.input.argv,['list']);
 const typed=await h.invoke(['quote','--item','tea']);pass(typed);assert.equal(typed.out,'{}\n');assert.equal(h.fake.jsonPosts[1].json.operation,'quote');assert.deepEqual(h.fake.jsonPosts[1].json.input,{item:'tea'});
});
test('CLI combined with C HTTP selects serve and CLI name escapes clash',async t=>{
 let classified=0,launched=0;const h=await harness(t);const programApp={appKind(){classified++;return 'http';},runApp(){launched++;return 0;}};
 pass(await h.invoke(['serve'],[],{programApp}));assert.equal(launched,1);
 pass(await h.invoke(['final','serve'],[],{programApp}));assert.equal(launched,1);assert.deepEqual(h.fake.jsonPosts[0].json.input.argv,['serve']);assert.equal(classified,2);
});
test('noentry explains context and names actual dependent prompts',async t=>{const h=await harness(t,{edit(s){s.entries=[];s.conventions=[];},files(root){prompt(root,'prompts/consumer.prompt.md',iface(),'consumer','- [Context](place_order.prompt.md)');}}),r=await h.invoke([],[],{programApp:{appKind(){return null;}}});assert.equal(r.code,2,r.err);assert.match(r.err,/pdd:.*has no entry/);assert.match(r.err,/context/);assert.match(r.err,/prompts\/consumer.prompt.md/);assert.equal(r.clock.gh.length,0);});
test('call cap changes invalidate local replay',async t=>{const h=await harness(t);pass(await h.invoke(['list'],['--max-calls','2']));pass(await h.invoke(['list'],['--max-calls','3']));assert.equal(h.fake.jsonPosts.length,2);});
test('clock resource never satisfies local cached answer',async t=>{const h=await harness(t,{edit(s){s.resources=[{name:'clock',kind:'port',access:'read',operations:[{name:'now',access:'read',arguments_schema:obj({}),result_schema:obj({utc:string})}]}];}});pass(await h.invoke());pass(await h.invoke());assert.equal(h.fake.jsonPosts.length,2);});
test('default cap above100 is sent100 and explicit low cap reaches interpreter',async t=>{const h=await harness(t,{edit(s){s.calls=[{operation:'child',target:'prompts/child.prompt.md',target_operation:'main',max_calls:60}];},files(root){prompt(root,'prompts/child.prompt.md',iface());}});pass(await h.invoke());assert.equal(h.fake.jsonPosts[0].json.max_calls,100);pass(await h.invoke(['other'],['--max-calls','2']));assert.equal(h.fake.jsonPosts[1].json.max_calls,2);});
for(const kind of ['http','port'])test(`own ${kind} fake is discovered, wired exactly and captured without unrelated fakes`,async t=>{
 const wire=obj({name:string}),result=obj({value:string});const h=await harness(t,{edit(s){s.resources=[{name:'cloud',kind,access:'read',operations:[{name:'lookup',access:'read',arguments_schema:wire,result_schema:result}]}];},files(root){mkdirSync(join(root,'prompts/fakes'));const s=iface(false);s.entries=[{operation:'lookup',input_schema:wire,result_schema:result,errors:[]}];prompt(root,'prompts/fakes/cloud.prompt.md',s);prompt(root,'prompts/fakes/unrelated.prompt.md',iface(false));}});pass(await h.invoke());const req=h.fake.posts.find(p=>p.command==='try');assert.deepEqual(req.request.simulation['cloud.lookup'],{action:kind+'.prompt',target:'prompts/fakes/cloud.prompt.md',operation:'lookup',max_calls:1,request_template:{},request_mapping:[{from:'',to:''}],response_template:{},response_mapping:[{from:'',to:''}]});assert.ok(req.tar.includes(Buffer.from('prompts/fakes/cloud.prompt.md')));assert.equal(req.tar.includes(Buffer.from('prompts/fakes/unrelated.prompt.md')),false);
});
test('C data option is resolved from invocation subfolder before delegation',async t=>{const h=await harness(t,{cli:false}),cwd=join(h.repo,'sub');mkdirSync(cwd);let called;const io=portsFor(h.env??{HOME:h.home},{programApp:{appKind(){return 'http';},runApp(input){called=input;return 0;}},stdin:Readable.from([])});const code=await runPdd(['--data','seed.json','../'+PLACE],{cwd,env:io.ports.env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});assert.equal(code,0,io.ports.stderr.text);assert.equal(called.flags.data,join(cwd,'seed.json'));});
test('valid unusual prompt path executes and remains readable',async t=>{const h=await harness(t);const path='prompts/my order café.prompt.md';writeFileSync(join(h.repo,path),readFileSync(join(h.repo,PLACE)));const env={HOME:h.home,PDD_STATE_DIR:h.state,PDD_RUNTIME_URL:h.fake.origin};const io=portsFor(env,{stdin:Readable.from([])});const code=await runPdd([path,'list'],{cwd:h.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});assert.equal(code,0,io.ports.stderr.text);assert.ok(existsSync(join(h.repo,'.pdd/run/my order café/world.json')));});
test('parent internal bin and data names do not collide with nested prompt worlds',async t=>{const h=await harness(t);mkdirSync(join(h.repo,'prompts/place_order'));for(const leaf of ['bin','world.json','.pdd-run']){const path=`prompts/place_order/${leaf}.prompt.md`;writeFileSync(join(h.repo,path),readFileSync(join(h.repo,PLACE)));const env={HOME:h.home,PDD_STATE_DIR:h.state,PDD_RUNTIME_URL:h.fake.origin};const io=portsFor(env,{stdin:Readable.from([])});const code=await runPdd([path,'list'],{cwd:h.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});assert.equal(code,0,io.ports.stderr.text);}pass(await h.invoke([]));pass(await h.invoke());assert.deepEqual(h.stored('world.json'),{});});
test('real run path holds program lock until first call settles',async t=>{let enter,release;const entered=new Promise(r=>enter=r),gate=new Promise(r=>release=r);const h=await harness(t,{reply:async(e,f,job)=>{enter();await gate;return {status:200,json:job};}});const first=h.invoke(['first']);try{const started=await Promise.race([entered.then(()=>true),first.then(()=>false)]);assert.equal(started,true,'first run must reach interpreter call');const second=await h.invoke(['second']);assert.equal(second.code,125,second.err);assert.match(second.err,/busy|active|finish/i);assert.equal(h.fake.jsonPosts.length,1);}finally{release();}pass(await first);});
for(const code of ['invalid-call-cap','source-digest-mismatch','source-too-large','world-too-large','session-busy','not-signed-in','forbidden','rate-limit'])test(`runtime ${code} retains structured code, field and fix`,async t=>{const h=await harness(t,{reply(){return {status:({'invalid-call-cap':422,'source-too-large':413,'not-signed-in':401,'forbidden':403,'rate-limit':429})[code]??409,json:{error:{code,message:'Specific runtime failure',field:'max_calls',fix:'Exact supplied fix'}}};}}),r=await h.invoke();assert.equal(r.code,125,r.err);assert.match(r.err,new RegExp(code));assert.match(r.err,/max_calls/);assert.match(r.err,/Fix: Exact supplied fix/);assert.equal(h.fake.jsonPosts.length,1);});
for(const code of ['session-stopped','session-unknown'])test(`confirmed ${code} replaces session once with world`,async t=>{let refused=false;const h=await harness(t,{world:{carried:true},reply(e,f,job){if(e.json.input.argv[0]==='next'&&!refused){refused=true;return {status:409,json:{error:{code,message:'The session ended'}}};}return {status:200,json:job};}});pass(await h.invoke(['first']));const r=await h.invoke(['next']);pass(r);assert.equal(h.fake.posts.filter(p=>p.command==='try').length,2);assert.deepEqual(h.fake.posts.filter(p=>p.command==='try').at(-1).request.initial_world,{carried:true});assert.equal(h.fake.jsonPosts.filter(e=>e.json.input.argv[0]==='next').length,2);});
function fakeOptions(kind='http',bad=false){const wire=obj({name:string}),result=obj({value:string});return {edit(s){s.resources=[{name:'cloud',kind,access:'read',operations:[{name:'lookup',access:'read',arguments_schema:wire,result_schema:result}]}];},files(root){mkdirSync(join(root,'prompts/fakes'));const s=iface(false);s.entries=[{operation:'lookup',input_schema:bad?obj({wrong:string}):wire,result_schema:result,errors:[]}];prompt(root,'prompts/fakes/cloud.prompt.md',s,'cloud','- [Rules](../../fake-rules.txt)');writeFileSync(join(root,'fake-rules.txt'),'FAKE OWNED RULE');}};}
test('custom fake closure is captured and changing fake replaces session',async t=>{const h=await harness(t,fakeOptions());pass(await h.invoke());assert.ok(h.fake.posts[0].tar.includes(Buffer.from('FAKE OWNED RULE')));const path=join(h.repo,'fake-rules.txt');writeFileSync(path,'CHANGED FAKE RULE');pass(await h.invoke(['next']));assert.equal(h.fake.posts.filter(p=>p.command==='try').length,2);});
test('custom fake schema mismatch refuses locally before authentication',async t=>{const h=await harness(t,fakeOptions('http',true)),r=await h.invoke();assert.equal(r.code,2,r.err);assert.match(r.err,/fake.*schema|schema.*fake/i);assert.equal(r.clock.gh.length,0);assert.equal(h.fake.posts.length,0);});
test('explicit simulation wins over automatic own fake binding',async t=>{const h=await harness(t,fakeOptions());const simulation={'cloud.lookup':{action:'http.prompt',target:'prompts/fakes/cloud.prompt.md',operation:'lookup',max_calls:7,request_template:{},request_mapping:[{from:'',to:''}],response_template:{},response_mapping:[{from:'',to:''}]}};writeFileSync(join(h.repo,'seed.json'),JSON.stringify({initial_world:{},simulation}));pass(await h.invoke(['list'],['--data','seed.json']));assert.deepEqual(h.fake.posts.find(p=>p.command==='try').request.simulation,simulation);});
test('unsupported resource kinds keep interpreter defaults without invented fake actions',async t=>{const h=await harness(t,fakeOptions('key-value'));pass(await h.invoke());const req=h.fake.posts.find(p=>p.command==='try').request;assert.equal(req.simulation?.['cloud.lookup'],undefined);});
test('fresh plus explicit data preserves old backup while selecting explicit world',async t=>{const h=await harness(t,{world:{prior:true}});pass(await h.invoke());writeFileSync(join(h.repo,'seed.json'),'{"chosen":true}');pass(await h.invoke(['next'],['--fresh','--data','seed.json']));assert.deepEqual(h.stored('world.prev.json'),{prior:true});assert.deepEqual(h.fake.posts.filter(p=>p.command==='try').at(-1).request.initial_world,{chosen:true});});
test('flattened duplicate paths cannot collide with literal delimiter basenames',async t=>{const h=await harness(t);mkdirSync(join(h.repo,'a'));mkdirSync(join(h.repo,'b'));for(const path of ['a/main.prompt.md','b/main.prompt.md','a__main.prompt.md']){writeFileSync(join(h.repo,path),readFileSync(join(h.repo,PLACE)));const env={HOME:h.home,PDD_STATE_DIR:h.state,PDD_RUNTIME_URL:h.fake.origin};const io=portsFor(env,{stdin:Readable.from([])});const code=await runPdd([path,'list'],{cwd:h.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});assert.equal(code,0,io.ports.stderr.text);}assert.equal(h.fake.posts.filter(p=>p.command==='try').length,3);assert.deepEqual(h.fake.posts.filter(p=>p.command==='try').map(p=>p.request.initial_world),[{},{},{}]);});

for(const [label,mutate] of [
 ['error string',job=>{job.result.report.error='declared';}],
 ['error array',job=>{job.result.report.error=[];}],
 ['error missing code',job=>{job.result.report.error={message:'bad'};}],
 ['error empty code',job=>{job.result.report.error={code:''};}],
 ['error nonstring message',job=>{job.result.report.error={code:'declared',message:7};}],
 ['passed with valid error',job=>{job.result.report.error={code:'declared',message:'contradiction'};}],
 ['unknown verdict',job=>{job.result.report.verdict='unknown';}],
 ['missing verdict',job=>{delete job.result.report.verdict;}],
 ['nonstring verdict',job=>{job.result.report.verdict={passed:true};}],
 ['refused wrapper with passed verdict',job=>{job.state='refused';}],
 ['null first refusal followed by refusal',job=>{job.result.refusals=[null,{code:'refused',message:'NO'}];}],
 ['nonempty valid refusals with passed verdict',job=>{job.result.refusals=[{code:'refused',message:'NO'}];}],
 ['object refusal container',job=>{job.result.refusals={bad:'shape'};}],
 ['empty string refusal container',job=>{job.result.refusals='';}],
 ['null refusal container',job=>{job.result.refusals=null;}],
 ['malformed refusal object',job=>{job.result.refusals=[{code:'refused'}];}],
])test(`malformed terminal receipt: ${label} preserves accepted request without success`,async t=>{
 const h=await harness(t,{cli:false,world:{unconfirmed:true},reply(e,f,job){mutate(job);return {status:200,json:job};}});
 const r=await h.invoke(['--input','{}']);
 assert.equal(r.code,125,r.err);assert.equal(r.out,'');
 const accepted=h.fake.jsonPosts[0].json.requestId;
 assert.equal(h.stored('session.json').pending.id,accepted);
 assert.deepEqual(h.stored('world.json'),{});
 assert.equal(existsSync(join(h.repo,'.pdd/run/place_order/last-run.json')),false);
 assert.match(r.err,new RegExp(accepted));
 const again=await h.invoke(['--input','{}']);assert.equal(again.code,125,again.err);
 assert.equal(h.fake.jsonPosts.length,1,'uncertain accepted request must never be resent');
 const json=await h.invoke([],['--json','--read',accepted]);assert.equal(json.code,125,json.err);assert.equal(json.out,'');
 assert.equal(h.stored('session.json').pending.id,accepted);assert.deepEqual(h.stored('world.json'),{});
 assert.equal(h.fake.jsonPosts.length,1,'read recovery uses GET only');
});
test('flattening isolates underscore segment boundaries through actual runs',async t=>{
 const paths=['prompts/a_/b.prompt.md','prompts/a/_b.prompt.md','b.prompt.md','_b.prompt.md'];
 const h=await harness(t,{files(root){for(const path of paths){mkdirSync(join(root,path,'..'),{recursive:true});prompt(root,path,iface());}},reply(e,f,job){job.result.world={owner:e.json.prompt};return {status:200,json:job};}});
 const env={HOME:h.home,PDD_STATE_DIR:h.state,PDD_RUNTIME_URL:h.fake.origin};
 for(const path of paths){const io=portsFor(env,{stdin:Readable.from([])});const code=await runPdd([path,'list'],{cwd:h.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});assert.equal(code,0,io.ports.stderr.text);}
 const starts=h.fake.posts.filter(p=>p.command==='try');assert.equal(starts.length,4);
 assert.deepEqual(starts.map(p=>p.request.initial_world),[{},{},{},{}]);
 const dirs=readdirSync(join(h.repo,'.pdd/run'));assert.equal(dirs.length,4);
 const records=dirs.map(dir=>({world:JSON.parse(readFileSync(join(h.repo,'.pdd/run',dir,'world.json'))),session:JSON.parse(readFileSync(join(h.repo,'.pdd/run',dir,'session.json')))}));
 assert.deepEqual(records.map(r=>r.world.owner).sort(),[...paths].sort());
 assert.equal(new Set(records.map(r=>r.session.id)).size,4);
});

test('legacy receipt without refusals remains a valid semantic pass',async t=>{
 const h=await harness(t,{cli:false,reply(e,f,job){delete job.result.refusals;return {status:200,json:job};}});
 const r=await h.invoke(['--input','{}']);pass(r);assert.equal(r.out,'{\"ok\":true}\n');
});

// Synthetic admission oracle: these bounds are contract examples, not model output.
const budgetResource=(kind='http',name='cloud')=>({name,kind,access:'read',operations:[{name:name==='clock'?'now':'lookup',access:'read',arguments_schema:obj({}),result_schema:obj({})}]});
function admission(bound){return (e,f,job)=>{if(e.json.max_calls<bound){job.result.report={verdict:'refused',provider_calls:0,error:{code:'session-call-cap',message:`Graph requires ${bound}`,fix:'Increase cap'}};job.result.output=null;}return {status:200,json:job};};}
for(const [steps,bound] of [[1,3],[20,41]])for(const kind of ['http','command','model','port'])test(`budget admission default ${kind} steps${steps} requires${bound}`,async t=>{
 const h=await harness(t,{edit(s){s.limits.max_steps=steps;s.resources=[budgetResource(kind)];},reply:admission(bound)});
 pass(await h.invoke());assert.equal(h.fake.jsonPosts[0].json.max_calls,bound);
});
for(const [kind,name,ceiling] of [['key-value','store',20],['port','clock',20],['key-value','store',57]])test(`budget external ${kind}/${name} ceiling${ceiling}`,async t=>{
 const h=await harness(t,{edit(s){s.resources=[budgetResource(kind,name)];s.limits.max_model_calls=ceiling===57?57:1;},reply:admission(ceiling)});
 pass(await h.invoke());assert.equal(h.fake.jsonPosts[0].json.max_calls,ceiling);
});
for(const [steps,bound] of [[1,3],[4,9]])test(`budget automatic own fake steps${steps} retains invocation bound`,async t=>{
 const h=await harness(t,{edit(s){s.limits.max_steps=steps;s.resources=[budgetResource()];},files(root){mkdirSync(join(root,'prompts/fakes'));const s=iface(false);s.entries[0].operation='lookup';s.entries[0].result_schema=obj({});prompt(root,'prompts/fakes/cloud.prompt.md',s);},reply:admission(bound)});
 pass(await h.invoke());assert.equal(h.fake.jsonPosts[0].json.max_calls,bound);assert.equal(h.fake.posts.find(p=>p.command==='try').request.simulation['cloud.lookup'].max_calls,steps);
});
test('budget own fake includes nested call closure but not body dependency',async t=>{
 const h=await harness(t,{edit(s){s.resources=[budgetResource()];},files(root){mkdirSync(join(root,'prompts/fakes'));const s=iface(false);s.entries[0].operation='lookup';s.entries[0].result_schema=obj({});s.calls=[{operation:'child',target:'prompts/child.prompt.md',target_operation:'main',max_calls:2}];prompt(root,'prompts/fakes/cloud.prompt.md',s,'fake','- [Body](../../body.txt)');prompt(root,'prompts/child.prompt.md',iface(false));writeFileSync(join(root,'body.txt'),'Context has no provider cost.');},reply:admission(7)});
 pass(await h.invoke());assert.equal(h.fake.jsonPosts[0].json.max_calls,7);
 writeFileSync(join(h.repo,'body.txt'),'Different context, identical graph.');pass(await h.invoke(['next']));assert.equal(h.fake.jsonPosts[1].json.max_calls,7);
});
test('budget selected operation excludes unused resources and calls',async t=>{
 const h=await harness(t,{edit(s){s.entries[0].resource_operations=[];s.entries[0].call_operations=[];s.resources=[budgetResource()];s.calls=[{operation:'unused',target:'prompts/child.prompt.md',target_operation:'main',max_calls:10}];},files(root){prompt(root,'prompts/child.prompt.md',iface(false));},reply:admission(1)});
 pass(await h.invoke());assert.equal(h.fake.jsonPosts[0].json.max_calls,1);
});
test('budget service projection caps100, forwards insufficient explicit cap to interpreter',async t=>{
 const h=await harness(t,{edit(s){s.limits.max_steps=20;s.resources=['one','two','three'].map(n=>budgetResource('http',n));},reply:admission(121)});
 const r=await h.invoke();assert.equal(r.code,125,r.err);assert.equal(h.fake.jsonPosts[0].json.max_calls,100);assert.match(r.err,/session-call-cap|Graph requires/);
 const low=await h.invoke(['next'],['--max-calls','2']);assert.equal(low.code,125,low.err);assert.equal(h.fake.jsonPosts[1].json.max_calls,2);
});
test('budget explicit prompt simulation bound wins over automatic fake',async t=>{
 const h=await harness(t,{edit(s){s.resources=[budgetResource()];},files(root){mkdirSync(join(root,'prompts/fakes'));const s=iface(false);s.entries[0].operation='lookup';s.entries[0].result_schema=obj({});prompt(root,'prompts/fakes/cloud.prompt.md',s);},reply:admission(15)});
 const binding={action:'http.prompt',target:'prompts/fakes/cloud.prompt.md',operation:'lookup',max_calls:7,request_template:{},request_mapping:[{from:'',to:''}],response_template:{},response_mapping:[{from:'',to:''}]};writeFileSync(join(h.repo,'seed.json'),JSON.stringify({initial_world:{},simulation:{'cloud.lookup':binding}}));
 pass(await h.invoke(['list'],['--data','seed.json']));assert.equal(h.fake.jsonPosts[0].json.max_calls,15);assert.deepEqual(h.fake.posts.find(p=>p.command==='try').request.simulation['cloud.lookup'],binding);
});
test('budget shared own fake takes maximum reachable owner bound',async t=>{
 const h=await harness(t,{edit(s){s.resources=[budgetResource()];s.calls=[{operation:'child',target:'prompts/child.prompt.md',target_operation:'main',max_calls:1}];},files(root){mkdirSync(join(root,'prompts/fakes'));const fake=iface(false);fake.entries[0].operation='lookup';fake.entries[0].result_schema=obj({});prompt(root,'prompts/fakes/cloud.prompt.md',fake);const child=iface(false);child.limits.max_steps=4;child.resources=[budgetResource()];prompt(root,'prompts/child.prompt.md',child);},reply:admission(19)});
 // Shared binding4: child W9, root W1+4*2+1*(9+1)=19.
 pass(await h.invoke());assert.equal(h.fake.jsonPosts[0].json.max_calls,19);assert.equal(h.fake.posts.find(p=>p.command==='try').request.simulation['cloud.lookup'].max_calls,4);
});
test('budget fake target operation scope leaves deterministic nested ceiling',async t=>{
 const h=await harness(t,{edit(s){s.resources=[budgetResource()];s.limits.max_model_calls=33;},files(root){mkdirSync(join(root,'prompts/fakes'));const fake=iface(false);fake.entries[0].operation='lookup';fake.entries[0].result_schema=obj({});fake.entries[0].resource_operations=['store.lookup'];fake.resources=[budgetResource('key-value','store'),budgetResource('http','unused')];fake.limits.max_steps=20;prompt(root,'prompts/fakes/cloud.prompt.md',fake);},reply:admission(33)});
 pass(await h.invoke());assert.equal(h.fake.jsonPosts[0].json.max_calls,33);
});
test('budget explicit nonconventional fake captures target and selected nested closure only',async t=>{
 const h=await harness(t,{edit(s){s.resources=[budgetResource()];},files(root){mkdirSync(join(root,'sandbox'));const fake=iface(false);fake.entries[0].operation='lookup';fake.entries[0].result_schema=obj({});fake.calls=[{operation:'nested',target:'sandbox/child.prompt.md',target_operation:'main',max_calls:2}];prompt(root,'sandbox/custom.prompt.md',fake,'custom','- [Rules](rules.txt)');prompt(root,'sandbox/child.prompt.md',iface(false));prompt(root,'sandbox/unrelated.prompt.md',iface(false));writeFileSync(join(root,'sandbox/rules.txt'),'CUSTOM BINDING RULES');},reply:admission(13)});
 const binding={action:'http.prompt',target:'sandbox/custom.prompt.md',operation:'lookup',max_calls:2,request_template:{},request_mapping:[{from:'',to:''}],response_template:{},response_mapping:[{from:'',to:''}]};writeFileSync(join(h.repo,'seed.json'),JSON.stringify({initial_world:{},simulation:{'cloud.lookup':binding}}));
 pass(await h.invoke(['list'],['--data','seed.json']));assert.equal(h.fake.jsonPosts[0].json.max_calls,13);const start=h.fake.posts.find(p=>p.command==='try');assert.deepEqual(start.request.simulation['cloud.lookup'],binding);for(const path of ['sandbox/custom.prompt.md','sandbox/child.prompt.md','sandbox/rules.txt'])assert.ok(start.tar.includes(Buffer.from(path)),path);assert.equal(start.tar.includes(Buffer.from('sandbox/unrelated.prompt.md')),false);assert.ok(start.tar.includes(Buffer.from('CUSTOM BINDING RULES')));
});

for(const error of [null,undefined])test(`canonical no-error passed receipt: ${error}`,async t=>{
 const h=await harness(t,{report:{error},world:{confirmed:true}});const r=await h.invoke();pass(r);assert.equal(r.out,'program only\n');assert.deepEqual(h.stored('world.json'),{confirmed:true});assert.equal(h.stored('session.json').pending,undefined);
});
for(const error of [null,{code:'session-call-cap'}])test(`canonical refused receipt accepts optional error message: ${JSON.stringify(error)}`,async t=>{
 const h=await harness(t,{report:{verdict:'refused',error},refusals:[{code:'session-call-cap',message:'Cap exhausted'}],world:{confirmed:true}});const r=await h.invoke();assert.equal(r.code,125);assert.equal(r.out,'');assert.match(r.err,/refused/);assert.match(r.err,/session-call-cap/);assert.deepEqual(h.stored('world.json'),{confirmed:true});assert.equal(h.stored('session.json').pending,undefined);assert.equal(h.stored('last-run.json').exit_code,125);
});
test('canonical declared error without message is a confirmed failure1',async t=>{
 const h=await harness(t,{report:{verdict:'failed',error:{code:'declared'}},world:{confirmed:true}});const r=await h.invoke();assert.equal(r.code,1,r.err);assert.equal(r.out,'');assert.match(r.err,/declared/);assert.deepEqual(h.stored('world.json'),{confirmed:true});assert.equal(h.stored('session.json').pending,undefined);assert.equal(h.stored('last-run.json').exit_code,1);
});
for(const notice of ['capacity','maintenance'])for(const quiet of [false,true])test(`direct transport ${notice} notices respect quiet=${quiet} and preserve program streams`,async t=>{
 // Omit error only here to isolate notice behavior against the pre-fix runner.
 const h=await harness(t,{report:{error:undefined},stderr:'program diagnostic\n'});let reads=0;
 h.fake.capacity=()=>{reads++;return {status:200,json:notice==='capacity'?{unrecognized:true}:{maintenance:reads===1?{until:new Date(Date.parse('2026-10-27T16:27:47Z')+1000).toISOString(),reason:'Synthetic maintenance'}:null}};};
 const r=await h.invoke(['list'],quiet?['-q']:[]);pass(r);assert.equal(r.out,'program only\n');assert.ok(reads>=1);assert.equal(r.err.includes('program diagnostic\n'),true);
 const own=r.err.replace('program diagnostic\n','');if(quiet)assert.equal(own,'');else {assert.match(own,notice==='capacity'?/capacity could not be read/:/maintenance/);assert.ok(own.trim().split('\n').every(line=>line.startsWith('pdd:')),own);}
});

// Re-review 2 expectations come from DESIGN 1–5 and the lead's 20:13 decisions.
for(const port of ['1','9000','65535'])test(`prefix port ${port} reaches C unchanged`,async t=>{
 const h=await harness(t,{cli:false});let called;
 const r=await h.invoke([],['--port',port],{programApp:{appKind(){return 'http';},runApp(input){called=input;return 0;}}});pass(r);assert.equal(String(called.flags.port),port);assert.equal(h.fake.posts.length,0);
});
for(const port of ['0','65536','-1','1.2','abc'])test(`invalid prefix port ${port} refuses locally`,async t=>{
 const h=await harness(t);let launched=0;const programApp={appKind(){return 'http';},runApp(input){launched++;assert.equal(String(input.flags.port),'9000');return 0;}};
 pass(await h.invoke(['serve'],['--port','9000'],{programApp}));assert.equal(launched,1);
 const r=await h.invoke(['list'],['--port',port],{programApp});assert.equal(r.code,2,r.err);assert.equal(launched,1);assert.equal(r.clock.gh.length,0);assert.equal(h.fake.posts.length,0);
});
for(const kind of ['http','screen'])test(`${kind} rejects extra words without launching`,async t=>{
 const h=await harness(t,{cli:false});let launched=0;const programApp={appKind(){return kind;},runApp(){launched++;return 0;}};pass(await h.invoke([],[],{programApp}));assert.equal(launched,1);launched=0;const r=await h.invoke(['foo','bar'],[],{programApp});assert.equal(r.code,2,r.err);assert.equal(launched,0);assert.equal(r.clock.gh.length,0);assert.equal(h.fake.posts.length,0);if(kind==='http')assert.match(r.err,/HTTP programs take no ARGS\. Call the link\./);
});
for(const supplied of [false,true])test(`declared error uses only supplied fix=${supplied}`,async t=>{
 const h=await harness(t,{report:{verdict:'failed',error:{code:'declared',message:'Own reason',...(supplied?{fix:'Own repair'}:{})}}});const r=await h.invoke();assert.equal(r.code,1);assert.match(r.err,/pdd: declared: Own reason/);assert.doesNotMatch(r.err,/Error declared|Fix the reported/);if(supplied)assert.match(r.err,/Fix: Own repair/);else assert.doesNotMatch(r.err,/Fix:/);
});
test('cap refusal prints executable increased max-calls command',async t=>{
 // Root W1 + two (leaf W1 + caller resume1) = five calls.
 const h=await harness(t,{edit(s){s.calls=[{operation:'child',target:'prompts/child.prompt.md',target_operation:'main',max_calls:2}];},files(root){prompt(root,'prompts/child.prompt.md',iface(false));},reply:admission(5)});
 const r=await h.invoke(['list'],['--max-calls','2']);assert.equal(r.code,125);assert.equal(h.fake.jsonPosts[0].json.max_calls,2);assert.match(r.err,/Graph requires 5/);assert.match(r.err,/Fix: pdd --max-calls 5 .*place_order\.prompt\.md list/);
 pass(await h.invoke(['list'],['--max-calls','5']));assert.equal(h.fake.jsonPosts[1].json.max_calls,5);
});
test('structured HTTP409 cap refusal preserves supplied fix and original selector in increased command',async t=>{
 // Same actual graph as the semantic receipt: root W1 + two (leaf W1 + resume1) = five.
 const h=await harness(t,{edit(s){s.calls=[{operation:'child',target:'prompts/child.prompt.md',target_operation:'main',max_calls:2}];},files(root){prompt(root,'prompts/child.prompt.md',iface(false));},reply(){return {status:409,json:{error:{code:'session-call-cap',message:'Graph requires 5',fix:'Increase cap'}}};}});
 const r=await h.invoke(['final','list'],['--max-calls','2']);assert.equal(r.code,125,r.err);assert.equal(r.out,'');assert.equal(h.fake.jsonPosts.length,1);assert.equal(h.fake.jsonPosts[0].json.max_calls,2);assert.match(r.err,/session-call-cap/);assert.match(r.err,/Graph requires 5/);assert.match(r.err,/Fix: Increase cap/);assert.ok(r.err.includes(`Fix: pdd --max-calls 5 ${PLACE} final list`),r.err);
});
test('one call summary uses singular and rounded seconds',async t=>{const h=await harness(t,{reply(e,f,job){job.usage.seconds=10.6;return {status:200,json:job};}});const r=await h.invoke();pass(r);assert.match(r.err,/1 AI call · 11 s/);assert.doesNotMatch(r.err,/1 AI calls|\d+\.\d+ s/);});
test('fresh notice names actual backup path',async t=>{const h=await harness(t,{world:{old:true}});pass(await h.invoke());const r=await h.invoke(['again'],['--fresh']);pass(r);assert.ok(r.err.includes('Old data kept in .pdd/run/place_order/world.prev.json'),r.err);});
test('quiet terminal shell runs and preserves shell result without informational lines',async t=>{
 const h=await harness(t);let opened=0;const stdin=Readable.from([]);stdin.isTTY=true;const r=await h.invoke([],['-q'],{stdin,shell(){opened++;return 23;}});assert.equal(r.code,23,r.err);assert.equal(opened,1);assert.equal(r.out,'');assert.equal(r.err,'');
});
test('adding basename collision retains recorded original world and isolates newcomer',async t=>{
 const h=await harness(t,{world:{saved:true}});pass(await h.invoke());mkdirSync(join(h.repo,'later'));const newcomer='later/place_order.prompt.md';writeFileSync(join(h.repo,newcomer),readFileSync(join(h.repo,PLACE)));
 const original=await h.invoke([],['--show-data']);pass(original);assert.deepEqual(JSON.parse(original.out),{saved:true});
 const env={HOME:h.home,PDD_STATE_DIR:h.state,PDD_RUNTIME_URL:h.fake.origin};const io=portsFor(env,{stdin:Readable.from([])});const code=await runPdd([newcomer,'list'],{cwd:h.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});assert.equal(code,0,io.ports.stderr.text);assert.deepEqual(h.fake.posts.filter(p=>p.command==='try').at(-1).request.initial_world,{});assert.deepEqual(h.stored('world.json'),{saved:true});assert.equal(readdirSync(join(h.repo,'.pdd/run')).length,2);
});
for(const [words,expected] of [[['serve'],'http'],[['app'],'screen']])test(`complete C catalog routes ${words[0]} with explicit kind`,async t=>{
 const h=await harness(t,{outputs:{quote:{}},edit(s){s.entries.push({operation:'route',input_schema:obj({}),result_schema:obj({}),errors:[]},{operation:'quote',input_schema:obj({item:string}),result_schema:obj({}),errors:[]});}});let request,classification;
 const programApp={appKind(input){classification=input;return {kinds:['http','screen'],httpOperations:['route']};},runApp(input){request=input;return 0;}};
 pass(await h.invoke(words,[],{programApp}));assert.equal(classification.all,true);assert.equal(request.kind,expected);assert.equal(h.fake.posts.length,0);
 const typed=await h.invoke(['quote','--item','tea'],[],{programApp});pass(typed);assert.equal(typed.out,'{}\n');assert.equal(h.fake.jsonPosts[0].json.operation,'quote');assert.deepEqual(h.fake.jsonPosts[0].json.input,{item:'tea'});
});
test('without CLI mixed kinds print word table at zero calls',async t=>{
 const h=await harness(t,{cli:false,edit(s){s.entries[0].operation='quote';s.entries.push({...s.entries[0],operation:'route'});}});let launched=0;
 const programApp={appKind(){return {kinds:['http','screen'],httpOperations:['route']};},runApp(){launched++;return 0;}};
 for(const words of [[],['unknown'],['--help']]){const r=await h.invoke(words,[],{programApp});assert.equal(r.code,2,r.err);for(const word of ['serve','app','quote'])assert.match(r.err,new RegExp(word));assert.equal(r.clock.gh.length,0);}
 assert.equal(launched,0);assert.equal(h.fake.posts.length,0);
});
test('leading dash matching operation name remains default CLI argv',async t=>{
 const h=await harness(t,{edit(s){s.entries.push({operation:'--quote',input_schema:obj({}),result_schema:obj({}),errors:[]});}});pass(await h.invoke(['--quote']));assert.equal(h.fake.jsonPosts[0].json.operation,'main');assert.deepEqual(h.fake.jsonPosts[0].json.input.argv,['--quote']);
});
test('CLI plus typed with no words still opens default shell',async t=>{
 const h=await harness(t,{edit(s){s.entries.push({operation:'quote',input_schema:obj({}),result_schema:obj({}),errors:[]});}});const r=await h.invoke([]);pass(r);assert.match(r.out,/# then: final --help/);assert.equal(h.fake.posts.length,0);
});

test('remaining session allowance refusal keeps world and recommends no fresh reset',async t=>{const h=await harness(t,{world:{keep:true},report:{remaining_calls:0}});pass(await h.invoke(['first']));const r=await h.invoke(['second']);assert.equal(r.code,125,r.err);assert.doesNotMatch(r.err,/start fresh|--fresh/i);assert.match(r.err,/session|allowance|budget/i);assert.deepEqual(h.stored('world.json'),{keep:true});assert.equal(h.fake.jsonPosts.length,1);});

for(const mixed of [false,true])test(`same-ID read restores pending typed selection: ${mixed?'CLI plus typed':'multiple typed operations'}`,async t=>{
 const h=await harness(t,{cli:false,outputs:{quote:{}},world:{confirmed:'typed recovery'},edit(s){
  const typed={operation:'quote',input_schema:obj({}),result_schema:obj({}),errors:[]};
  if(mixed){const cli=iface();s.entries=[cli.entries[0],typed];s.conventions=cli.conventions;}
  else s.entries=[typed,{...typed,operation:'inspect'}];
 },reply(e,f,job){delete job.result.report.verdict;return {status:200,json:job};}});
 const first=await h.invoke(['quote','--input','{}']);
 assert.equal(first.code,125,first.err);assert.equal(first.out,'');
 assert.equal(h.fake.jsonPosts.length,1);assert.equal(h.fake.jsonPosts[0].json.operation,'quote');
 const accepted=h.fake.jsonPosts[0].json.requestId;
 assert.equal(h.stored('session.json').pending.id,accepted);
 assert.deepEqual(h.stored('world.json'),{});
 assert.equal(existsSync(join(h.repo,'.pdd/run/place_order/last-run.json')),false);
 // The interpreter now has a canonical confirmed receipt for the same accepted call.
 const job=h.fake.jobs.get(accepted);job.result.report.verdict='passed';job.result.output={};
 const posts=h.fake.posts.length,gets=h.fake.gets.length;
 const read=await h.invoke([mixed?'final':'inspect'],['--read',accepted]);
 pass(read);assert.equal(read.out,'{}\n');
 assert.deepEqual(h.stored('world.json'),{confirmed:'typed recovery'});
 assert.equal(h.stored('session.json').pending,undefined);
 assert.deepEqual(h.stored('last-run.json').output,{});
 assert.equal(h.fake.posts.length,posts,'recovery sends no setup POST');
 assert.equal(h.fake.jsonPosts.length,1,'recovery never repeats the accepted call');
 assert.ok(h.fake.gets.slice(gets).some(e=>e.url.endsWith(accepted)),'read fetches the accepted ID');
});

test('same-ID read acknowledges pending setup without operation in a typed word table',async t=>{
 const h=await harness(t,{cli:false,edit(s){s.entries.push({...s.entries[0],operation:'inspect'});}});
 pass(await h.invoke(['main','--input','{}']));
 // Keep the actual public run's program/login/source identity; model an accepted lint.
 const path=join(h.repo,'.pdd/run/place_order/session.json');
 const saved=h.stored('session.json'),accepted=h.fake.jsonPosts[0].json.requestId;
 saved.pending={id:accepted,command:'lint'};writeFileSync(path,JSON.stringify(saved));
 h.fake.jobs.set(accepted,h.fake.lint(accepted));
 const posts=h.fake.posts.length,gets=h.fake.gets.length;
 const read=await h.invoke([],['--read',accepted]);
 pass(read);assert.equal(read.out,'');assert.match(read.err,/setup confirmed/i);
 assert.equal(h.stored('session.json').pending,undefined);
 assert.deepEqual(h.stored('world.json'),{});
 assert.equal(h.fake.posts.length,posts);assert.equal(h.fake.jsonPosts.length,1);
 assert.ok(h.fake.gets.slice(gets).some(e=>e.url.endsWith(accepted)));
});

// Re-review 3: exact semantic codes, absent reports and backup provenance.
for(const code of ['capture-denied','capacity','session-call-cap'])test(`semantic refusal advice matches exact code ${code}`,async t=>{
 const h=await harness(t,{report:{verdict:'refused',error:{code,message:'capture capacity exhausted'}}});
 const r=await h.invoke();assert.equal(r.code,125,r.err);
 if(code==='session-call-cap')assert.match(r.err,/Fix: pdd --max-calls/);
 else assert.doesNotMatch(r.err,/Fix: pdd --max-calls/);
});
test('semantic refusal without report link omits details',async t=>{
 const h=await harness(t,{report:{verdict:'refused',error:{code:'refused',message:'No report'}},reply(e,f,job){delete job.reportUrl;delete job.report_url;delete job.result.report_url;delete job.result.report.report_url;return {status:200,json:job};}});
 const r=await h.invoke();assert.equal(r.code,125,r.err);assert.doesNotMatch(r.err,/details: undefined/);
});
test('fresh with stale backup and absent world claims no new backup',async t=>{
 const h=await harness(t);pass(await h.invoke());
 const dir=join(h.repo,'.pdd/run/place_order');rmSync(join(dir,'world.json'));
 writeFileSync(join(dir,'world.prev.json'),'{"stale":true}');
 const r=await h.invoke(['next'],['--fresh']);pass(r);assert.doesNotMatch(r.err,/Old data kept/);
 assert.deepEqual(h.stored('world.prev.json'),{stale:true});
});
test('prefix -q delegates canonical quiet flag to C',async t=>{
 const h=await harness(t,{cli:false});let flags;
 pass(await h.invoke([],['-q'],{programApp:{appKind(){return 'screen';},runApp(input){flags=input.flags;return 0;}}}));
 assert.equal(flags.quiet,true);assert.equal(Object.hasOwn(flags,'q'),false);assert.equal(h.fake.posts.length,0);
});

test('semantic refusal uses singular one AI call',async t=>{
 const h=await harness(t,{report:{verdict:'refused',error:{code:'declined',message:'Declined'}}});
 const r=await h.invoke();assert.equal(r.code,125,r.err);assert.match(r.err,/refused, 1 AI call[.]/);assert.doesNotMatch(r.err,/1 AI calls/);
});
