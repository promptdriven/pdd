import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync,readFileSync,writeFileSync,rmSync,renameSync,symlinkSync} from 'node:fs';
import {join} from 'node:path';
import {runCheck,runTry} from '../src/runtime-client.mjs';
import {parseArgv} from '../src/argument-parser.mjs';
import {harbor,fakeRuntime,portsFor,PLACE,TOKEN} from './runtime-fake.mjs';
const binding={schema_version:'prompt-runtime.live-resource-bindings.v1',operations:[{resource:'herdr',operation:'client_status',kind:'command',access:'read',template:{executable:'herdr',subcommand:['status','client'],argv:[{literal:'--json'},{literal:'--session'},{target:'project'}]}}]};
const config=name=>({schema_version:'prompt-runtime.live-resource-run-config.v1',mode:'live',max_live_calls:1,allow_live_writes:false,command:{allowed_executables:['herdr'],allowed_subcommands:[['status','client']],sandbox_projects:[name],targets:{project:name}},http:null,model:null});
function profiles(repo,folder='tests',name='test_session'){
 mkdirSync(join(repo,folder),{recursive:true});writeFileSync(join(repo,folder,'runtime-bindings.json'),JSON.stringify(binding));writeFileSync(join(repo,folder,'runtime-run-config.json'),JSON.stringify(config(name)));
}
async function invoke(setup,fake,options={'--live':true},words=['place-order'],cwd=setup.repo){
 const {ports,clock}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
 const code=await runCheck({cwd,words,options:{'--json':true,...options}},ports);
 return{code,out:ports.stdout.text,err:ports.stderr.text,clock,json:ports.stdout.text.startsWith('{')?JSON.parse(ports.stdout.text):null};
}
function names(tar){const out=[];for(let at=0;at<tar.length&&tar[at];){const head=tar.subarray(at,at+512);out.push(head.subarray(0,100).toString().replace(/\0.*$/s,''));const size=parseInt(head.subarray(124,136).toString().replace(/\0.*$/s,'').trim(),8)||0;at+=512+Math.ceil(size/512)*512}return out}
const normal=(e,f)=>f.normal(e);
test('LIVE1: parser accepts Check live options and refuses Try live mode',()=>{
 const r=parseArgv(['check','story','--live','--bindings','a.json','--run-config','b.json']);assert.equal(r.options['--live'],true);assert.equal(r.options['--bindings'],'a.json');assert.throws(()=>parseArgv(['try','story','--live']));
});
test('LIVE2: default live files are captured and exact fields go only to CHECK',async t=>{
 const setup=harbor(t,r=>profiles(r)),fake=await fakeRuntime(t,normal),r=await invoke(setup,fake);assert.equal(r.code,0,r.err);
 const [lint,check]=fake.posts;assert.equal(lint.request.resource_mode,undefined);assert.equal(lint.request.resource_bindings,undefined);assert.equal(lint.request.resource_run_config,undefined);
 assert.deepEqual([check.request.resource_mode,check.request.resource_bindings,check.request.resource_run_config],['live','tests/runtime-bindings.json','tests/runtime-run-config.json']);
 assert.ok(names(check.tar).includes('tests/runtime-bindings.json'));assert.ok(names(check.tar).includes('tests/runtime-run-config.json'));assert.ok(check.tar.includes(Buffer.from(JSON.stringify(binding))));assert.ok(check.tar.includes(Buffer.from(JSON.stringify(config('test_session')))));assert.ok(lint.tar.equals(check.tar));
 assert.equal(r.json.live,true);assert.equal(r.json.rows[0].resource_mode,'live');assert.match(r.json.summary_line,/LIVE/);
});
test('LIVE3: simulated Check sends neither live metadata nor implicit config files',async t=>{
 const setup=harbor(t,r=>profiles(r)),fake=await fakeRuntime(t,normal),r=await invoke(setup,fake,{});assert.equal(r.code,0);
 for(const p of fake.posts){for(const key of ['resource_mode','resource_bindings','resource_run_config'])assert.equal(p.request[key],undefined);assert.ok(!names(p.tar).includes('tests/runtime-bindings.json'))}
 assert.equal(r.json.live,undefined);assert.doesNotMatch(r.json.summary_line,/LIVE/);
});
test('LIVE4: explicit paths use invocation cwd, keep canonical repo names',async t=>{
 const setup=harbor(t,r=>{profiles(r,'config');mkdirSync(join(r,'work'))}),fake=await fakeRuntime(t,normal);
 const r=await invoke(setup,fake,{'--live':true,'--bindings':'../config/runtime-bindings.json','--run-config':'../config/runtime-run-config.json'},['place-order'],join(setup.repo,'work'));assert.equal(r.code,0,r.err);
 const p=fake.posts[1];assert.equal(p.request.resource_bindings,'config/runtime-bindings.json');assert.equal(p.request.resource_run_config,'config/runtime-run-config.json');assert.ok(names(p.tar).includes('config/runtime-bindings.json'));
});
test('LIVE5: selecting multiple live Stories stops before sign-in, including implicit all',async t=>{
 for(const words of [[],['place-order','unknown-item']]){
  const setup=harbor(t,r=>{profiles(r);profiles(r,'specs','second_session');renameSync(join(r,'tests/unknown-item.json'),join(r,'specs/unknown-item.json'))}),fake=await fakeRuntime(t,normal),r=await invoke(setup,fake,{'--live':true},words);assert.equal(r.code,2,r.err);assert.match(r.err,/one Story/);assert.equal(r.clock.gh.length,0);assert.equal(fake.posts.length,0);
 }
});
test('LIVE6: option conflicts reject before any sign-in or request',async t=>{
 for(const options of [{'--bindings':'a.json'},{'--run-config':'a.json'},...['--read','--lint','--fill-hash','--files','--request'].map(k=>({'--live':true,[k]:k==='--request'?'11111111-1111-4111-8111-111111111111':true}))]){
  const setup=harbor(t,r=>profiles(r)),fake=await fakeRuntime(t,normal),r=await invoke(setup,fake,options,options['--read']?[]:['place-order']);assert.equal(r.code,2,JSON.stringify(options));assert.equal(r.clock.gh.length,0);assert.equal(fake.posts.length+fake.gets.length,0);
 }
 const setup=harbor(t,r=>profiles(r)),fake=await fakeRuntime(t,normal),{ports,clock}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});assert.equal(await runTry({cwd:setup.repo,words:['place-order'],options:{'--live':true}},ports),2);assert.equal(clock.gh.length,0);assert.equal(fake.posts.length,0);
});
test('LIVE7: missing, symlink, secret and outside config files stop before network',async t=>{
 for(const kind of ['missing','symlink','secret','outside']){
  const setup=harbor(t,r=>{if(kind!=='missing')profiles(r);if(kind==='symlink'){rmSync(join(r,'tests/runtime-run-config.json'));writeFileSync(join(r,'tests/real.json'),'{}');symlinkSync('real.json',join(r,'tests/runtime-run-config.json'))}if(kind==='secret')writeFileSync(join(r,'.env.live'),'secret')}),fake=await fakeRuntime(t,normal);
  const opts={'--live':true,...(kind==='secret'?{'--bindings':'.env.live'}:kind==='outside'?{'--bindings':join(setup.sandbox,'outside.json')}:{})};if(kind==='outside')writeFileSync(join(setup.sandbox,'outside.json'),'{}');
  const r=await invoke(setup,fake,opts);assert.equal(r.code,4,kind+':'+r.err);assert.equal(r.clock.gh.length,0);assert.equal(fake.posts.length,0);
 }
});
test('LIVE8: policy422 preserves specific reason and adds allowed-command/file guidance',async t=>{
 const setup=harbor(t,r=>profiles(r)),fake=await fakeRuntime(t,(e,f)=>e.command==='check'?{status:422,json:{dispatch:'not_started',error:{code:'live-resource-policy',message:'max_live_calls must be 1'}}}:normal(e,f));
 const r=await invoke(setup,fake,{'--live':true,'--json':false});assert.equal(r.code,4,r.err);assert.match(r.out,/max_live_calls must be 1/);assert.match(r.out,/herdr status client --json --session/);assert.match(r.out,/runtime-bindings\.json/);assert.match(r.out,/LIVE/);assert.equal(fake.posts.filter(p=>p.command==='check').length,1);
});
test('LIVE9: lost CHECK reads its ID once, LIVE and DRAFT survive saved --read without config files',async t=>{
 let id;const setup=harbor(t,r=>profiles(r)),fake=await fakeRuntime(t,(e,f)=>{if(e.command==='check'){id=e.request.requestId;return{destroy:true}}if(e.method==='GET'){const a=f.check(e.url.split('/').at(-1));a.draft_prompts=[PLACE];return{status:200,json:a}}return normal(e,f)});
 const first=await invoke(setup,fake);assert.equal(first.code,0,first.err);assert.equal(first.json.rows[0].live,true);assert.match(first.json.summary_line,/DRAFT.*LIVE/);assert.equal(fake.posts.filter(p=>p.command==='check').length,1);assert.ok(fake.gets.every(g=>g.url==='/v1/runs/'+id));
 rmSync(join(setup.repo,'tests/runtime-bindings.json'));rmSync(join(setup.repo,'tests/runtime-run-config.json'));const posts=fake.posts.length;
 const later=await invoke(setup,fake,{'--read':true},[]);assert.equal(later.code,0,later.err);assert.equal(later.json.rows[0].live,true);assert.match(later.json.summary_line,/DRAFT.*LIVE/);assert.equal(fake.posts.length,posts);assert.ok(!later.out.includes(TOKEN));
});
test('LIVE10: only a confirmed pre-dispatch 429 retries, with the same live files and bytes',async t=>{
 let calls=0;const setup=harbor(t,r=>profiles(r)),fake=await fakeRuntime(t,(e,f)=>e.command==='check'&&++calls===1?{status:429,headers:{'Retry-After':'1'},json:{dispatch:'not_started',error:{code:'server-full'}}}:normal(e,f));
 const r=await invoke(setup,fake);assert.equal(r.code,0,r.err);const checks=fake.posts.filter(p=>p.command==='check');assert.equal(checks.length,2);assert.notEqual(checks[0].request.requestId,checks[1].request.requestId);
 for(const key of ['resource_mode','resource_bindings','resource_run_config','source_sha256'])assert.equal(checks[0].request[key],checks[1].request[key]);assert.ok(checks[0].tar.equals(checks[1].tar));assert.match(r.json.summary_line,/LIVE/);
 const other=await fakeRuntime(t,(e,f)=>e.command==='check'?{status:429,json:{error:{code:'server-full'}}}:normal(e,f));const stopped=await invoke(setup,other);assert.equal(stopped.code,5);assert.equal(other.posts.filter(p=>p.command==='check').length,1);
});
test('LIVE11: any live HTTP422 retains distinct reason, fix and location with sanitized details',async t=>{
 const setup=harbor(t,r=>profiles(r)),fake=await fakeRuntime(t,(e,f)=>e.command==='check'?{status:422,json:{error:{code:'invalid-config',message:'Config rejected',reason:'Use one read '+TOKEN,fix:'Set max_live_calls to 1',file:'tests/runtime-run-config.json',at:'max_live_calls',cause:'test',details:{why:'detail '+TOKEN}}}}:normal(e,f));
 const r=await invoke(setup,fake);assert.equal(r.code,4,r.err);const refusal=r.json.rows[0].refusals[0];assert.equal(refusal.message,'Config rejected');assert.equal(refusal.reason,'Use one read [secret]');assert.equal(refusal.fix,'Set max_live_calls to 1');assert.equal(refusal.where,'tests/runtime-run-config.json max_live_calls');assert.equal(refusal.cause,'test');assert.match(refusal.engine_message,/detail \[secret\]/);assert.match(refusal.hint,/herdr status client/);assert.ok(!r.out.includes(TOKEN));
});
test('LIVE12: terminal policy refusal and successful report links show LIVE alongside DRAFT',async t=>{
 const setup=harbor(t,r=>profiles(r)),fake=await fakeRuntime(t,(e,f)=>{
  if(e.method==='GET'){const a=f.check(e.url.split('/').at(-1),'refused',[],[{code:'live-resource-policy',reason:'Unsupported read',fix:'Use client status',where:'resource herdr'}]);a.draft_prompts=[PLACE];return{status:200,json:a}}return normal(e,f)
 });
 const r=await invoke(setup,fake,{'--live':true,'--json':false});assert.equal(r.code,4,r.err);assert.match(r.out,/DRAFT\) \(LIVE/);assert.match(r.out,/Unsupported read/);assert.match(r.out,/Use client status/);assert.match(r.out,/herdr status client/);assert.match(r.out,/\/r\/\w+  \(DRAFT\)  \(LIVE\)/);assert.equal(fake.posts.filter(p=>p.command==='check').length,1);
 const success=await fakeRuntime(t,normal),passed=await invoke(setup,success,{'--live':true,'--json':false});assert.equal(passed.code,0);assert.match(passed.out,/\/r\/\w+  \(LIVE\)/);
});

test('LIVE13: one-Story restriction uses full authored identity, not matching basenames',async t=>{
 const setup=harbor(t,r=>{
  mkdirSync(join(r,'user_stories/a'));mkdirSync(join(r,'user_stories/b'));
  for(const [file,folder] of [['place-order','a'],['unknown-item','b']]){
   const doc=JSON.parse(readFileSync(join(r,'tests',file+'.json')));renameSync(join(r,doc.story_path),join(r,'user_stories',folder,'status.md'));doc.story_path='user_stories/'+folder+'/status.md';writeFileSync(join(r,'tests',file+'.json'),JSON.stringify(doc));
  }
  profiles(r);
 }),fake=await fakeRuntime(t,normal),r=await invoke(setup,fake,{'--live':true},[]);assert.equal(r.code,2,r.err);assert.equal(r.clock.gh.length,0);assert.equal(fake.posts.length,0);
});
test('LIVE14: two authored tests for the same Story retain their own config defaults',async t=>{
 const setup=harbor(t,r=>{profiles(r);profiles(r,'specs','second_session');mkdirSync(join(r,'specs'),{recursive:true});writeFileSync(join(r,'specs/second.json'),readFileSync(join(r,'tests/place-order.json')))}),fake=await fakeRuntime(t,normal),r=await invoke(setup,fake,{'--live':true},['place-order']);assert.equal(r.code,0,r.err);
 const checks=fake.posts.filter(p=>p.command==='check');assert.equal(checks.length,2);assert.deepEqual(checks.map(p=>p.request.resource_run_config).sort(),['specs/runtime-run-config.json','tests/runtime-run-config.json']);
});

test('LIVE15: read-only request recovery recognizes the real server report transport_mode',async t=>{
 const setup=harbor(t),id='11111111-1111-4111-8111-111111111111',fake=await fakeRuntime(t,(e,f)=>{const answer=f.check(id);answer.result.report.transport_mode='live';answer.draft_prompts=[PLACE];return{status:200,json:answer}});
 const r=await invoke(setup,fake,{'--request':id},[]);assert.equal(r.code,0,r.err);assert.equal(r.json.rows[0].live,true);assert.match(r.json.summary_line,/DRAFT.*LIVE/);assert.equal(fake.posts.length,0);assert.equal(fake.gets.length,1);
});
