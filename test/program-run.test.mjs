import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync, readFileSync, rmSync, existsSync, readdirSync } from 'node:fs';
import { join } from 'node:path';
import { Readable } from 'node:stream';
import { runPdd } from '../src/pdd-cli.mjs';
import { proseSha256 } from '../src/runtime-preflight.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';

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
    if(e.json){
      const result=cli?{stdout:'answer\n',stderr:options.stderr??'',exit_code:options.exit??0}:{ok:true};
      const report=options.report??{result,world:{tasks:['saved']},remaining_calls:39};
      const job={...f.job(e.json.requestId,'call',options.failure?'refused':'passed',{program_result:result,world:{tasks:['saved']},report},1),session_id:e.url.split('/')[3]};
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
const ok = r => assert.equal(r.code,0,r.err+r.out);
const paths = root => existsSync(root)?readdirSync(root,{recursive:true}).map(p=>join(root,p)):[];

test('direct CLI: no arguments opens prompt-backed shell with provenance first, scope, exit and PATH',async t=>{
  const h=await harness(t);let opened;
  const r=await h.invoke([],[],{shell:async(shell,env)=>{opened={shell,env};return 0;},openUrl:()=>assert.fail('CLI opens no browser')});
  ok(r);assert.equal(r.out.split('\n')[0],'Answers come from prompts on the PDD interpreter, not installed code.');
  assert.match(r.out,/paperclip works only in this shell; exit.*Another terminal: export PATH=/);
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
 ['malformed JSON',['--input','{']],['unselected single operation',['quote','--name','x']],
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
 assert.match(r.err,/Traceback \(prompt calls, most recent last\):/);assert.match(r.err,/prompts\/pricing.prompt.md, operation quote \(call 1 of at most 1\)/);assert.match(r.err,/Error unknown-coupon: Unknown SPRING99/);
});
test('direct: confirmed world and last record persist in Git-ignored .pdd/run',async t=>{
 const h=await harness(t);ok(await h.invoke(['add','task']));const files=paths(join(h.setup.repo,'.pdd/run'));
 const data=files.find(p=>p.endsWith('/data.json')),last=files.find(p=>p.endsWith('/last.json'));assert.ok(data);assert.ok(last);
 assert.deepEqual(JSON.parse(readFileSync(data)),{tasks:['saved']});const record=JSON.parse(readFileSync(last));assert.deepEqual(record.input.argv,['add','task']);assert.ok('output' in record);assert.ok('data_before' in record);assert.ok('data_after' in record);assert.ok('ai_calls' in record);
 assert.match(readFileSync(join(h.setup.repo,'.gitignore'),'utf8'),/\.pdd\//);
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
test('direct: named HTTP delegates lazily and missing C module gives agreed plain line',async t=>{
 const h=await harness(t,false);const path=join(h.setup.repo,PLACE);let text=readFileSync(path,'utf8').replace('"input_schema":{','"input_schema":{"title":"HTTP GET /items",');text=text.replace(/"prose_sha256":"[a-f0-9]+"/,`"prose_sha256":"${proseSha256(text)}"`);writeFileSync(path,text);
 const r=await h.invoke();assert.equal(r.code,2);assert.equal(r.err,'Screen apps and HTTP entries open this way in the next release; for now run pdd simulate STORY.\n');assert.equal(h.fake.posts.length,0);
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
 const h=await harness(t,true,{failure:true,report}),r=await h.invoke(['list']);assert.equal(r.code,125,r.err);assert.match(r.err,/Traceback \(prompt calls, most recent last\):/);assert.match(r.err,/child.prompt.md, operation main \(call 1 of at most 2\)/);assert.match(r.err,/Child result invalid/);
});
test('direct: same basename entry paths keep separate saved worlds',async t=>{
 const h=await harness(t);const {mkdirSync}=await import('node:fs');mkdirSync(join(h.setup.repo,'other'));writeFileSync(join(h.setup.repo,'other/place_order.prompt.md'),readFileSync(join(h.setup.repo,PLACE)));
 ok(await h.invoke(['list']));const io=portsFor({HOME:h.setup.home,PDD_STATE_DIR:h.setup.state,PDD_RUNTIME_URL:h.fake.origin},{stdin:Readable.from([])});
 const code=await runPdd(['other/place_order.prompt.md','list'],{cwd:h.setup.repo,env:io.ports.env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});assert.equal(code,0,io.ports.stderr.text);
 const dirs=paths(join(h.setup.repo,'.pdd/run')).filter(p=>p.endsWith('/data.json'));assert.equal(dirs.length,2);assert.deepEqual(h.fake.posts.filter(p=>p.command==='try').map(p=>p.request.initial_world),[{},{}]);
});
