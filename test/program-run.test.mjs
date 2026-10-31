import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync, readFileSync, rmSync, existsSync, readdirSync, mkdirSync, symlinkSync, cpSync } from 'node:fs';
import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import { Readable } from 'node:stream';
import { runPdd } from '../src/pdd-cli.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor, PLACE, temp } from './runtime-fake.mjs';

const object = (properties, required = Object.keys(properties)) => ({ type:'object', properties, required, additionalProperties:false });
const str = {type:'string'};
const typed = object({name:str, count:{type:'integer',minimum:1}, ratio:{type:'number'}, enabled:{type:'boolean'}, tags:{type:'array',items:str}}, ['name']);
function fixture(t, cli = true, multi = false, stdin = true) {
  return harbor(t, root => {
    rmSync(join(root,'tests'),{recursive:true}); rmSync(join(root,'user_stories'),{recursive:true});
    const input = cli ? object({argv:{type:'array',items:str},...(stdin ? {stdin:str} : {})},['argv']) : typed;
    const result = cli ? object({stdout:str,stderr:str,exit_code:{type:'integer'}}) : object({ok:{type:'boolean'}});
    const iface = {status:'draft',prose_sha256:'',entries:[{operation:cli?'main':'quote',input_schema:input,result_schema:result,errors:['unknown-coupon']}],calls:[],resources:[],limits:{max_steps:1,max_model_calls:1},conventions:cli?['input_schema','result_schema'].map(key=>({path:`/entries/0/${key}`,convention:'cli'})):[]};
    if(multi) iface.entries.push({...iface.entries[0],operation:'inspect'});
    const body = () => '# paperclip\n\nReturn the supplied input deterministically.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify(iface)+'\n```\n</details>\n';
    iface.prose_sha256=proseSha256(body());writeFileSync(join(root,PLACE),body());
  });
}
async function harness(t, cli=true, options={}) {
  const setup=fixture(t,cli,options.multi,options.stdin!==false);
  const fake=await fakeRuntime(t,(e,f)=>{
    if(e.method==='DELETE') return {status:202,json:{...f.job(e.headers['x-request-id'],'stop','running'),session_id:e.url.split('/').at(-1)}};
    const stop=f.deletes.find(item=>item.headers['x-request-id']===e.url.split('/').at(-1));
    if(stop) return {status:200,json:f.stopJob(e.url.split('/').at(-1),stop.url.split('/').at(-1))};
    if(e.json){
      const result=cli?{stdout:'answer\n',stderr:options.stderr??'',exit_code:options.exit??0}:{ok:true};
      const report=options.report??{result,world:{tasks:['saved']},remaining_calls:39};
      const job={...f.job(e.json.requestId,'call',options.failure?'refused':'passed',{output:result,world:report.world??{tasks:['saved']},refusals:options.failure?[report.refusal]:[],report:{verdict:options.failure?'refused':report.error?'failed':'passed',...report}},1),session_id:e.url.split('/')[3]};
      f.jobs.set(e.json.requestId,job);
      options.onCall?.(e,f);
      return options.lost?{destroy:true}:{status:200,json:job};
    }
    if(e.command==='lint') return {status:200,json:f.lint(e.request.requestId)};
    if(e.command==='try') return {status:200,json:f.tryJob(e.request.requestId)};
    if(f.jobs.has(e.url.split('/').at(-1)))return {status:200,json:f.jobs.get(e.url.split('/').at(-1))};
    if(e.url.endsWith('/model'))return {status:200,json:{calls:{cap:40,remaining:40}}};
    return {status:200,json:f.tryJob(e.url.split('/').at(-1))};
  });
  const env={HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin,PATH:'/usr/bin:/bin'};
  async function invoke(args=[],prefix=[],extra={}){
    const io=portsFor(env,{stdin:Readable.from([]),...extra});
    const code=await runPdd([...prefix,PLACE,...args],{cwd:setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
    return {code,out:io.ports.stdout.text,err:io.ports.stderr.text,...io};
  }
  return {setup,fake,invoke};
}
async function withoutApp(t, h, args=[]) {
  const isolated=temp(t);
  cpSync(new URL('../src/',import.meta.url),join(isolated,'src'),{recursive:true});
  rmSync(join(isolated,'src/program-app.mjs'),{force:true});
  // Enter through the public CLI so alpha fails by assertion, even before B's dispatcher exists.
  const {runPdd: isolatedRunPdd}=await import(pathToFileURL(join(isolated,'src/pdd-cli.mjs')).href);
  const env={HOME:h.setup.home,PDD_STATE_DIR:h.setup.state,PDD_RUNTIME_URL:h.fake.origin,PATH:'/usr/bin:/bin'};
  const io=portsFor(env,{stdin:Readable.from([])});
  const code=await isolatedRunPdd([PLACE,...args],{cwd:h.setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
  return {code,out:io.ports.stdout.text,err:io.ports.stderr.text};
}
const ok = r => assert.equal(r.code,0,r.err+r.out);
const paths = root => existsSync(root)?readdirSync(root,{recursive:true}).map(p=>join(root,p)):[];

test('direct CLI: no arguments opens prompt-backed shell with provenance first, scope, exit and PATH',async t=>{
  const h=await harness(t);let opened;
  const r=await h.invoke([],[],{stdin:Object.assign(Readable.from([]),{isTTY:true}),shell:async(shell,env)=>{opened={shell,env};return 0;},openUrl:()=>assert.fail('CLI opens no browser')});
  ok(r);assert.equal(r.out,'');assert.match(r.err,/pdd:.*paperclip.*command.*shell/);assert.match(r.err,/pdd:.*prompt behavior, not tested code/);
  assert.ok(opened.env.PATH.endsWith(':/usr/bin:/bin'));assert.equal(h.fake.jsonPosts.length,0);
});
test('direct CLI: exact argv, piped stdin, streams and program exit pass through',async t=>{
  const h=await harness(t,true,{exit:7,stderr:'bad input'}),args=['say','two words','','--help','--fresh','--','$(touch NEVER)'];
  const r=await h.invoke(args,[],{stdin:Readable.from(['piped\n'])});
  assert.equal(r.code,7,r.err);assert.equal(r.out,'answer\n');assert.match(r.err,/^bad input/);
  assert.deepEqual(h.fake.jsonPosts[0].json.input,{argv:args,stdin:'piped\n'});
});
test('direct CLI: undeclared stdin remains available to a surrounding read loop',async t=>{
  const h=await harness(t,true,{stdin:false});const input={isTTY:false,[Symbol.asyncIterator](){assert.fail('undeclared stdin must remain unread');}};
  const r=await h.invoke(['list'],[],{stdin:input});ok(r);assert.deepEqual(h.fake.jsonPosts[0].json.input,{argv:['list']});
});
test('direct: prefix options belong to pdd and suffix options belong to CLI unchanged',async t=>{
  const h=await harness(t);const r=await h.invoke(['--data','literal','--max-calls','99'],['--fresh','--max-calls','3']);ok(r);
  assert.equal(h.fake.jsonPosts[0].json.max_calls,3);assert.deepEqual(h.fake.jsonPosts[0].json.input.argv,['--data','literal','--max-calls','99']);
});
test('direct: no Story request uses entry and empty world instead of seed',async t=>{
  const h=await harness(t);ok(await h.invoke(['list']));const req=h.fake.posts.find(p=>p.command==='try').request;
  assert.equal(req.entry,PLACE);assert.deepEqual(req.initial_world,{});assert.equal('seed' in req,false);
});
for(const [name,args,input,stdin] of [
  ['schema scalar types',['--name','latte','--count','2','--ratio','1.25','--enabled','false'],{name:'latte',count:2,ratio:1.25,enabled:false}],
  ['repeated arrays',['--name','latte','--tags','one','--tags','two'],{name:'latte',tags:['one','two']}],
  ['whole JSON',['--input','{"name":"latte","count":3}'],{name:'latte',count:3}],
  ['piped JSON',[],{name:'latte',enabled:true},'{"name":"latte","enabled":true}'],
])test(`direct typed: ${name}`,async t=>{
  const h=await harness(t,false),r=await h.invoke(args,[],{stdin:Readable.from(stdin?[stdin]:[])});ok(r);
  assert.deepEqual(h.fake.jsonPosts[0].json.input,input);assert.equal(r.out,'{"ok":true}\n');
});
test('direct typed: whole input @file',async t=>{
  const h=await harness(t,false);writeFileSync(join(h.setup.repo,'input.json'),'{"name":"file"}');
  ok(await h.invoke(['--input','@input.json']));assert.deepEqual(h.fake.jsonPosts[0].json.input,{name:'file'});
});
test('direct typed: operation selected only for multiple entries',async t=>{
  const h=await harness(t,false,{multi:true});ok(await h.invoke(['inspect','--name','latte']));assert.equal(h.fake.jsonPosts[0].json.operation,'inspect');
});
for(const [name,args] of [
 ['missing required',[]],['invalid integer',['--name','x','--count','2.5']],['minimum',['--name','x','--count','0']],
 ['invalid boolean',['--name','x','--enabled','yes']],['unknown field',['--name','x','--other','a']],
 ['duplicate scalar',['--name','a','--name','b']],['mixed whole and flags',['--input','{"name":"x"}','--name','y']],
 ['malformed JSON',['--input','{']],
])test(`direct typed: ${name} reports schema usage before any send`,async t=>{
 const h=await harness(t,false),r=await h.invoke(args);assert.equal(r.code,2);assert.match(r.err,/Usage:.*place_order\.prompt\.md/i);assert.match(r.err,/name/);assert.equal(h.fake.posts.length,0);assert.equal(r.clock.gh.length,0);
});
test('direct typed: help is local schema usage',async t=>{
 const h=await harness(t,false),r=await h.invoke(['--help']);ok(r);assert.match(r.out,/Usage:.*place_order\.prompt\.md/i);assert.match(r.out,/--name/);assert.equal(h.fake.posts.length,0);assert.equal(r.clock.gh.length,0);
});
test('direct typed: missing operation lists operations without sending',async t=>{
 const h=await harness(t,false,{multi:true}),r=await h.invoke(['--name','x']);assert.equal(r.code,2);assert.match(r.err,/quote.*inspect|inspect.*quote/);assert.equal(h.fake.posts.length,0);
});
test('direct: declared error displays interpreter call_chain and code/message',async t=>{
 const report={error:{code:'unknown-coupon',message:'Unknown SPRING99'},call_chain:[{prompt:PLACE,operation:'quote',call_index:null,max_calls:null},{prompt:'prompts/pricing.prompt.md',operation:'quote',call_index:1,max_calls:1}]};
 const h=await harness(t,false,{report}),r=await h.invoke(['--name','x']);assert.equal(r.code,1,r.err);
 assert.match(r.err,/Traceback \(prompt calls, most recent call last\):/);assert.match(r.err,/prompts\/pricing.prompt.md, operation quote \(call 1 of at most 1\)/);assert.match(r.err,/Error unknown-coupon: Unknown SPRING99/);
});
test('direct: confirmed world and last record persist in Git-ignored .pdd/run',async t=>{
 const h=await harness(t);ok(await h.invoke(['add','task']));const files=paths(join(h.setup.repo,'.pdd/run'));
 const data=files.find(p=>p.endsWith('/world.json')),last=files.find(p=>p.endsWith('/last-run.json'));assert.ok(data);assert.ok(last);
 assert.deepEqual(JSON.parse(readFileSync(data)),{tasks:['saved']});const record=JSON.parse(readFileSync(last));assert.deepEqual(record.input.argv,['add','task']);assert.ok('output' in record);assert.ok('data_before' in record);assert.ok('data_after' in record);assert.ok('ai_calls' in record);
 assert.equal(existsSync(join(h.setup.repo,'.gitignore')),false);
 assert.match(readFileSync(join(h.setup.repo,'.git/info/exclude'),'utf8'),/\.pdd\//);
 assert.equal(data,join(h.setup.repo,'.pdd/run/place_order/world.json'));
});
test('direct: explicit data seeds world and --fresh starts empty next time',async t=>{
 const h=await harness(t);writeFileSync(join(h.setup.repo,'world.json'),'{"tasks":["seed"]}');
 ok(await h.invoke(['list'],['--data','world.json']));assert.deepEqual(h.fake.posts.find(p=>p.command==='try').request.initial_world,{tasks:['seed']});
 ok(await h.invoke(['list'],['--fresh']));assert.deepEqual(h.fake.posts.filter(p=>p.command==='try').at(-1).request.initial_world,{});
});
test('direct: scenario data accepts simulation without requiring its Story',async t=>{
 const h=await harness(t);const simulation={'files.read':{action:'blob.read'}};writeFileSync(join(h.setup.repo,'data.json'),JSON.stringify({initial_world:{files:{}},simulation,steps:[],story_path:'missing.md'}));
 ok(await h.invoke(['list'],['--data','data.json']));const req=h.fake.posts.find(p=>p.command==='try').request;assert.deepEqual(req.initial_world,{files:{}});assert.deepEqual(req.simulation,simulation);
});
test('direct: session reuse and source edit replacement carry world without --new',async t=>{
 const h=await harness(t);ok(await h.invoke(['add','task']));ok(await h.invoke(['list']));assert.equal(h.fake.posts.filter(p=>p.command==='try').length,1);
 const file=join(h.setup.repo,PLACE);let text=readFileSync(file,'utf8').replace('Return the supplied','Show the supplied');text=text.replace(/"prose_sha256":"[a-f0-9]+"/,`"prose_sha256":"${proseSha256(text)}"`);writeFileSync(file,text);
 ok(await h.invoke(['list']));const req=h.fake.posts.filter(p=>p.command==='try').at(-1).request;assert.equal(h.fake.posts.filter(p=>p.command==='try').length,2);assert.deepEqual(req.initial_world,{tasks:['saved']});
});
test('direct: cache accounting, quiet and show-data do not make extra calls',async t=>{
 const h=await harness(t);const first=await h.invoke(['list']);ok(first);assert.match(first.err,/DRAFT/);assert.match(first.err,/prompt behavior, not tested code/);
 ok(await h.invoke(['list']));const cached=await h.invoke(['list']);ok(cached);assert.match(cached.err,/cached · 0 AI calls/);const n=h.fake.jsonPosts.length;
 const quiet=await h.invoke(['list'],['-q']);ok(quiet);assert.equal(quiet.err,'');const data=await h.invoke([],['--show-data']);ok(data);assert.deepEqual(JSON.parse(data.out),{tasks:['saved']});assert.equal(h.fake.jsonPosts.length,n);
});
test('direct: interpreter refusal exits125 with plain fix message',async t=>{
 const h=await harness(t,true,{failure:true,report:{refusal:{code:'session-call-cap',message:'No AI calls remain. Start fresh.'}}}),r=await h.invoke(['list']);assert.equal(r.code,125,r.err);assert.match(r.err,/No AI calls remain/);assert.equal(r.out,'');
});
test('direct: lost accepted POST reads same ID without dispatching twice',async t=>{
 const h=await harness(t,true,{lost:true}),r=await h.invoke(['list']);ok(r);assert.equal(h.fake.jsonPosts.length,1);assert.ok(h.fake.gets.some(p=>p.url.endsWith(h.fake.jsonPosts[0].json.requestId)));
});
test('direct: graph-scoped upload excludes unrelated prompt, tests and Story',async t=>{
 const h=await harness(t);writeFileSync(join(h.setup.repo,'prompts/unrelated.prompt.md'),'PRIVATE UNRELATED CONTENT');ok(await h.invoke(['list']));
 const tar=h.fake.posts[0].tar;assert.ok(tar.includes(Buffer.from(PLACE)));assert.equal(tar.includes(Buffer.from('PRIVATE UNRELATED CONTENT')),false);assert.equal(tar.includes(Buffer.from('user_stories/')),false);assert.equal(tar.includes(Buffer.from('tests/')),false);
});

test('direct: high explicit call cap warns before send and reaches call unchanged',async t=>{
 const h=await harness(t);const r=await h.invoke(['list'],['--max-calls','25']);ok(r);assert.match(r.err,/may use up to 25 AI calls/);assert.equal(h.fake.jsonPosts[0].json.max_calls,25);
});
test('direct: Ctrl-C preserves accepted ID for GET-only --read and exits130',async t=>{
 let interrupt;const h=await harness(t,true,{onCall:()=>interrupt?.()});
 const r=await h.invoke(['list'],[],{onInterrupt:handler=>{interrupt=handler;return ()=>{};}});
 assert.equal(r.code,130,r.err);assert.match(r.err,/pdd --read [a-f0-9-]+ .*prompt\.md/);assert.equal(h.fake.jsonPosts.length,1);
 const id=h.fake.jsonPosts[0].json.requestId;const read=await h.invoke([],['--read',id]);ok(read);assert.equal(h.fake.jsonPosts.length,1);assert.ok(h.fake.gets.some(p=>p.url.endsWith(id)));
});
test('direct: HTTP titled typed prompt runs typed when C module is missing',async t=>{
 const h=await harness(t,false);const path=join(h.setup.repo,PLACE);let text=readFileSync(path,'utf8').replace('"input_schema":{','"input_schema":{"title":"HTTP GET /items",');text=text.replace(/"prose_sha256":"[a-f0-9]+"/,`"prose_sha256":"${proseSha256(text)}"`);writeFileSync(path,text);
 const r=await withoutApp(t,h,['--name','x']);ok(r);assert.deepEqual(h.fake.jsonPosts[0].json.input,{name:'x'});assert.equal(r.out,'{"ok":true}\n');
});

test('direct: missing C and no CLI or typed operation gives agreed plain fallback',async t=>{
 const h=await harness(t,false),path=join(h.setup.repo,PLACE);
 let text=readFileSync(path,'utf8');
 const match=text.match(/```json\n([\s\S]*?)\n```/),iface=JSON.parse(match[1]);
 iface.entries=[];
 text=text.replace(match[1],JSON.stringify(iface));
 text=text.replace(/"prose_sha256":"[a-f0-9]+"/,`"prose_sha256":"${proseSha256(text)}"`);
 writeFileSync(path,text);
 const r=await withoutApp(t,h);
 assert.equal(r.code,2);
 assert.match(r.err,/pdd:.*has no entry, so it cannot run/);assert.match(r.err,/context for other prompts/);
 assert.equal(r.out,'');assert.equal(h.fake.posts.length,0);
});

test('direct typed: numeric and boolean array flags use item types',async t=>{
 const h=await harness(t,false);const path=join(h.setup.repo,PLACE);let text=readFileSync(path,'utf8').replace('"tags":{"type":"array","items":{"type":"string"}}','"tags":{"type":"array","items":{"type":"integer"}},"switches":{"type":"array","items":{"type":"boolean"}}');text=text.replace(/"prose_sha256":"[a-f0-9]+"/,`"prose_sha256":"${proseSha256(text)}"`);writeFileSync(path,text);
 ok(await h.invoke(['--name','x','--tags','2','--tags','3','--switches','false','--switches','true']));assert.deepEqual(h.fake.jsonPosts[0].json.input,{name:'x',tags:[2,3],switches:[false,true]});
});
test('direct typed: nested whole JSON validates child constraints before sends',async t=>{
 const h=await harness(t,false);const path=join(h.setup.repo,PLACE);let text=readFileSync(path,'utf8').replace('"name":{"type":"string"}','"name":{"type":"string"},"detail":{"type":"object","properties":{"size":{"type":"integer","minimum":1}},"required":["size"],"additionalProperties":false}');text=text.replace(/"prose_sha256":"[a-f0-9]+"/,`"prose_sha256":"${proseSha256(text)}"`);writeFileSync(path,text);
 const bad=await h.invoke(['--input','{"name":"x","detail":{"size":0}}']);assert.equal(bad.code,2);assert.match(bad.err,/detail.*size|size.*1/);assert.equal(h.fake.posts.length,0);
 ok(await h.invoke(['--input','{"name":"x","detail":{"size":2}}']));assert.deepEqual(h.fake.jsonPosts[0].json.input.detail,{size:2});
});
test('direct: graph upload includes reached calls and declared dependencies only',async t=>{
 const h=await harness(t);const path=join(h.setup.repo,PLACE),child='prompts/child.prompt.md';writeFileSync(join(h.setup.repo,child),readFileSync(path));writeFileSync(join(h.setup.repo,'rules.txt'),'REQUIRED RULE TEXT');
 let text=readFileSync(path,'utf8').replace('None.','- [Rules](../rules.txt), runtime use.').replace('"calls":[]','"calls":[{"operation":"child","target":"'+child+'","target_operation":"main","max_calls":1}]');text=text.replace(/"prose_sha256":"[a-f0-9]+"/,`"prose_sha256":"${proseSha256(text)}"`);writeFileSync(path,text);
 ok(await h.invoke(['list']));const tar=h.fake.posts[0].tar;assert.ok(tar.includes(Buffer.from(child)));assert.ok(tar.includes(Buffer.from('REQUIRED RULE TEXT')));assert.equal(h.fake.jsonPosts[0].json.max_calls,3);
});
test('direct: malformed CLI result is interpreter failure125',async t=>{
 const h=await harness(t,true,{exit:999}),r=await h.invoke(['list']);assert.equal(r.code,125,r.err);assert.match(r.err,/result|exit.code|schema/i);assert.equal(r.out,'');
});
test('direct: interpreter refusal preserves call_chain traceback',async t=>{
 const report={refusal:{code:'graph-result-failure',message:'Child result invalid. Fix the prompt.'},call_chain:[{prompt:PLACE,operation:'main',call_index:null,max_calls:null},{prompt:'prompts/child.prompt.md',operation:'main',call_index:1,max_calls:2}]};
 const h=await harness(t,true,{failure:true,report}),r=await h.invoke(['list']);assert.equal(r.code,125,r.err);assert.match(r.err,/Traceback \(prompt calls, most recent call last\):/);assert.match(r.err,/child.prompt.md, operation main \(call 1 of at most 2\)/);assert.match(r.err,/Child result invalid/);
});
test('direct: same basename entry paths keep separate saved worlds',async t=>{
 const h=await harness(t);const {mkdirSync}=await import('node:fs');mkdirSync(join(h.setup.repo,'other'));writeFileSync(join(h.setup.repo,'other/place_order.prompt.md'),readFileSync(join(h.setup.repo,PLACE)));
 ok(await h.invoke(['list']));const io=portsFor({HOME:h.setup.home,PDD_STATE_DIR:h.setup.state,PDD_RUNTIME_URL:h.fake.origin},{stdin:Readable.from([])});
 const code=await runPdd(['other/place_order.prompt.md','list'],{cwd:h.setup.repo,env:io.ports.env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});assert.equal(code,0,io.ports.stderr.text);
 const dirs=paths(join(h.setup.repo,'.pdd/run')).filter(p=>p.endsWith('/world.json'));assert.equal(dirs.length,2);assert.ok(dirs.some(p=>p.includes('/prompts__place_order/')));assert.ok(dirs.some(p=>p.includes('/other__place_order/')));assert.deepEqual(h.fake.posts.filter(p=>p.command==='try').map(p=>p.request.initial_world),[{},{}]);
});

// Review cases derive from LEAD.md18:21: repeated writes, local paths and local errors.
test('direct: repeating mutating argv sends twice and saves both tasks',async t=>{
 const h=await harness(t,true,{onCall(e,f){const n=f.jsonPosts.length;const job=f.jobs.get(e.json.requestId);job.result.world={tasks:Array(n).fill('x')};}});
 ok(await h.invoke(['add','x']));ok(await h.invoke(['add','x']));
 assert.equal(h.fake.jsonPosts.length,2,'a write changes the input world for the next identical command');
 assert.deepEqual(JSON.parse(readFileSync(join(h.setup.repo,'.pdd/run/place_order/world.json'))),{tasks:['x','x']});
});
test('direct: cached CLI answer retains nonzero exit and does not resend',async t=>{
 const h=await harness(t,true,{exit:7,report:{result:{stdout:'answer\n',stderr:'',exit_code:7},world:{}}});
 assert.equal((await h.invoke(['list'])).code,7);const replay=await h.invoke(['list']);assert.equal(replay.code,7,replay.err);assert.match(replay.err,/cached · 0 AI calls/);assert.equal(h.fake.jsonPosts.length,1);
});
test('direct: shell exit code is returned',async t=>{
 const h=await harness(t);const r=await h.invoke([],[],{stdin:Object.assign(Readable.from([]),{isTTY:true}),shell:async()=>23});assert.equal(r.code,23,r.err);assert.equal(h.fake.jsonPosts.length,0);
});
for(const [name,content,problem] of [['bad.json','{',/JSON|json/],['missing.json',undefined,/missing|not found|does not exist/i],['array.json','[]',/object/i],['null.json','null',/object/i]])test(`direct: --data ${name} is a file-specific local input error`,async t=>{
 const h=await harness(t);if(content!==undefined)writeFileSync(join(h.setup.repo,name),content);
 const r=await h.invoke(['list'],['--data',name]);assert.equal(r.code,2,r.err);assert.match(r.err,new RegExp(name.replace('.','\\.')));assert.match(r.err,problem);assert.equal(h.fake.posts.length,0);assert.equal(r.clock.gh.length,0);
});
for(const cli of [true,false])test(`direct: ${cli?'data':'input'} file resolves from invocation subfolder`,async t=>{
 const h=await harness(t,cli);const cwd=join(h.setup.repo,'sub');mkdirSync(cwd);writeFileSync(join(cwd,'selected.json'),JSON.stringify(cli?{selected:'cwd'}:{name:'cwd'}));
 const io=portsFor({HOME:h.setup.home,PDD_STATE_DIR:h.setup.state,PDD_RUNTIME_URL:h.fake.origin},{stdin:Readable.from([])});
 const args=cli?['--data','selected.json','../'+PLACE,'list']:['../'+PLACE,'--input','@selected.json'];
 const code=await runPdd(args,{cwd,env:io.ports.env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});assert.equal(code,0,io.ports.stderr.text);
 if(cli)assert.deepEqual(h.fake.posts.find(p=>p.command==='try').request.initial_world,{selected:'cwd'});else assert.deepEqual(h.fake.jsonPosts[0].json.input,{name:'cwd'});
});
test('direct: descriptive CLI heading is allowed with argv but refused as shell command',async t=>{
 const h=await harness(t);const path=join(h.setup.repo,PLACE);let text=readFileSync(path,'utf8').replace('# paperclip','# Paperclip task manager');text=text.replace(/"prose_sha256":"[a-f0-9]+"/,`"prose_sha256":"${proseSha256(text)}"`);writeFileSync(path,text);
 ok(await h.invoke(['list']));const shell=await h.invoke([],[],{stdin:Object.assign(Readable.from([]),{isTTY:true}),shell:async()=>assert.fail('unsafe command must not open shell')});assert.equal(shell.code,2,shell.err);assert.match(shell.err,/name|command/i);
});
test('direct: worst case above100 is admitted to the interpreter',async t=>{
 const h=await harness(t);const path=join(h.setup.repo,PLACE),child='prompts/child.prompt.md';writeFileSync(join(h.setup.repo,child),readFileSync(path));
 let text=readFileSync(path,'utf8').replace('"calls":[]','"calls":[{"operation":"child","target":"'+child+'","target_operation":"main","max_calls":60}]');text=text.replace(/"prose_sha256":"[a-f0-9]+"/,`"prose_sha256":"${proseSha256(text)}"`);writeFileSync(path,text);
 ok(await h.invoke(['list']));assert.equal(h.fake.jsonPosts.length,1);
});
async function dataModule(){try{return await import('../src/program-data.mjs');}catch(e){assert.fail(`Public programData module is required: ${e.code}`);}}
for(const program of ['../escape','/absolute','prompts/../escape','prompts//todo','prompts/./todo'])test(`programData rejects unsafe identity ${program} directly`,async t=>{
 const {programData}=await dataModule();const h=harbor(t);assert.throws(()=>programData({root:h.repo,program,flags:{}},{}),/identity|name|path/i);assert.equal(existsSync(join(h.repo,'.pdd/run')),false);
});
test('programData refuses a symlink ancestor without modifying its target',async t=>{
 const {programData}=await dataModule();const h=harbor(t);const outside=join(h.home,'outside');mkdirSync(outside);symlinkSync(outside,join(h.repo,'.pdd'),'dir');
 assert.throws(()=>programData({root:h.repo,program:'todo',flags:{}},{}),/unsafe|symlink|directory/i);assert.deepEqual(readdirSync(outside),[]);
});
test('program data lock excludes a concurrent owner and admits one after release',async t=>{
 const {programData,acquireProgramLock}=await dataModule();const h=harbor(t);const data=programData({root:h.repo,program:'todo',flags:{}},{});const release=acquireProgramLock(data.dir);
 try{assert.throws(()=>acquireProgramLock(data.dir),/active|busy|finish/i);}finally{release();}
 const next=acquireProgramLock(data.dir);assert.equal(typeof next,'function');next();assert.equal(existsSync(join(data.dir,'active.lock')),false);
});

test('single typed table word is optional and forwards remaining fields',async t=>{const h=await harness(t,false);ok(await h.invoke(['quote','--name','x']));assert.equal(h.fake.jsonPosts[0].json.operation,'quote');assert.deepEqual(h.fake.jsonPosts[0].json.input,{name:'x'});});
