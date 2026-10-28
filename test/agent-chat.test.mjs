import test from 'node:test';
import assert from 'node:assert/strict';
import {createAgentBridge} from '../src/agent-chat.mjs';
const ID='11111111-1111-4111-8111-111111111111',KEY='x'.repeat(43);
const agents=[{id:'codex',name:'Codex',state:'ready'},{id:'claude',name:'Claude',state:'signed_out'},{id:'gemini',name:'Gemini',state:'not_installed'}];
const entry={entry_path:'prompts/main.prompt.md',operation:'main',input_schema:{type:'object',properties:{argv:{type:'array',items:{type:'string'}}},required:['argv'],additionalProperties:false}};
function setup(handler,extra={}){
 const controller=new AbortController(),calls=[],saved=[],output=[];let state={};
 const context={root:'/owned/project',origin:'https://runtime.example',identity:{token:'gho_secret_owner'},secrets:['gho_secret_owner'],signal:controller.signal,interrupted:false,
 store:{repo:()=>state,saveRepo:(_,next)=>{state=next;saved.push(next)}},
 ports:{env:{},now:Date.now,randomUUID:()=>ID,sleep:async()=>{},stdout:{write:s=>output.push(s)},stderr:{write:s=>output.push(s)},discoverAgents:async()=>agents.map(a=>({...a})),askAgent:async()=>({say:'Ready',fill:{entry:'prompts/main.prompt.md#main',input:{argv:['list']}}}),...extra},
 runtime:{send:async(path,init,ms)=>{const call={path,init,ms,body:init.body?JSON.parse(init.body):null};calls.push(call);if(path.endsWith('/model'))return{status:200,json:{entries:[entry],stories:[{title:'Bookmarks',criteria:[{id:'AC1',text:'List bookmarks'}]}]}};return handler(call,{controller,calls,context});}}};context.agentFinalSend=context.runtime.send;
 return{context,calls,saved,output,controller};
}
const connect=({body})=>({status:200,json:{connected:true,bridge_id:body.bridge_id,browser_key:KEY}});
test('CHAT1 connects owner, uses fragment key and remembers only selection',async()=>{
 const s=setup(connect),b=await createAgentBridge(s.context,{story:'bookmarks'},ID,{},'https://runtime.example/s/abc/');assert.ok(b.url.endsWith('#agent='+KEY));assert.equal(s.calls[1].body.selected,'codex');assert.equal(s.saved[0].agent_choice,'codex');assert.ok(!JSON.stringify(s.saved).includes(KEY));assert.ok(!s.output.join('').includes(KEY));await b.close();await b.close();assert.equal(s.calls.filter(c=>c.path.endsWith('/disconnect')).length,1);
});
test('CHAT2 unsupported server retains ordinary page, malformed connection fails closed',async()=>{
 const s=setup(()=>({status:404}));assert.equal(await createAgentBridge(s.context,{},ID,{},'https://runtime.example/s/abc/'),null);
 const bad=setup(({body})=>({status:200,json:{connected:true,bridge_id:body.bridge_id,browser_key:'bad'}}));await assert.rejects(()=>createAgentBridge(bad.context,{},ID,{},'https://runtime.example/s/abc/'),/connect/i);
});
test('CHAT3 one-shot delivery, valid fill, heartbeat while slow local agent runs',async()=>{
 let polls=0,resolveAsk;const hold=new Promise(r=>{resolveAsk=r});
 const s=setup(async(c,{controller})=>{
  if(c.path.endsWith('/connect'))return connect(c);
  if(c.path.includes('/poll')){polls++;if(polls===1)return{status:200,json:{connected:true,selected:'codex',message:{id:ID,text:'list',agent:'codex',context:{entry:'prompts/main.prompt.md#main',input:{argv:[]}}}}};if(polls===2){resolveAsk({say:'Use list',fill:null});await new Promise(r=>setImmediate(r));return{status:200,json:{connected:true,selected:'claude',message:null}}}controller.abort();return{lost:true};}
  return{status:200,json:{ok:true}};
 },{askAgent:async()=>hold});
 const b=await createAgentBridge(s.context,{story:'bookmarks'},ID,{},'https://runtime.example/s/abc/');await b.run();assert.ok(polls>=2);assert.equal(s.calls.filter(c=>c.path.endsWith('/reply')).length,1);assert.equal(s.saved.at(-1).agent_choice,'claude');
});
test('CHAT4 a duplicate claimed message is never run twice',async()=>{
 let polls=0,asks=0;const s=setup((c,{controller})=>{if(c.path.endsWith('/connect'))return connect(c);if(c.path.includes('/poll')){if(++polls>2){controller.abort();return{lost:true}}return{status:200,json:{connected:true,selected:'codex',message:{id:ID,text:'help',agent:'codex',context:{}}}}}return{status:200,json:{ok:true}}},{askAgent:async()=>{asks++;return{say:'Help',fill:null}}});const b=await createAgentBridge(s.context,{},ID,{},'https://runtime.example/s/abc/');await b.run();assert.equal(asks,1);
});
test('CHAT5 signed-out choice explains state without subprocess or fallback',async()=>{
 let polls=0;const s=setup((c,{controller})=>{if(c.path.endsWith('/connect'))return connect(c);if(c.path.includes('/poll')){if(++polls>1){controller.abort();return{lost:true}}return{status:200,json:{connected:true,selected:'claude',message:{id:ID,text:'help',agent:'claude',context:{}}}}}return{status:200,json:{ok:true}}},{askAgent:async()=>{throw Error('must not run')}});const b=await createAgentBridge(s.context,{},ID,{'--agent':'claude'},'https://runtime.example/s/abc/');await b.run();assert.match(s.calls.find(c=>c.path.endsWith('/reply')).body.say,/signed out/i);
});

test('CHAT6 public parser and mode conflicts fail before sign-in',async t=>{
 const {parseArgv}=await import('../src/argument-parser.mjs');assert.equal(parseArgv(['try','story','--agent','claude']).options['--agent'],'claude');assert.throws(()=>parseArgv(['try','--agent','other']));
 const {runTry}=await import('../src/runtime-client.mjs'),{harbor,portsFor}=await import('./runtime-fake.mjs');const fixture=harbor(t),{ports,clock}=portsFor({HOME:fixture.home,PDD_STATE_DIR:fixture.state});
 for(const mode of ['--no-wait','--cli','--serve','--stop','--save-last'])assert.equal(await runTry({cwd:fixture.repo,words:['place-order'],options:{'--agent':'codex',[mode]:true}},ports),2);
 assert.equal(clock.gh.length,0);
});
test('CHAT7 ordinary background Try waits on bridge, opens private owner URL and keeps shared output keyless',async t=>{
 const {runTry}=await import('../src/runtime-client.mjs'),{harbor,portsFor,fakeRuntime}=await import('./runtime-fake.mjs');
 const fixture=harbor(t),fake=await fakeRuntime(t,(e,f)=>{
  if(e.command==='lint')return{status:200,json:f.lint(e.request.requestId)};
  if(e.command==='try')return{status:200,json:f.tryJob(e.request.requestId)};
  if(e.url.endsWith('/tests'))return{status:200,json:{tests:[]}};
  if(e.url.endsWith('/approvals'))return{status:200,json:{approvals:[]}};
  return{status:404,json:{}};
 });
 let runs=0,closes=0,opened;
 const {ports}=portsFor({HOME:fixture.home,PDD_STATE_DIR:fixture.state,PDD_RUNTIME_URL:fake.origin},{openUrl:async url=>{opened=url;return true},agentBridge:async(context,test,id,options,link)=>({url:link+'#agent='+KEY,run:async tick=>{runs++;assert.equal(options['--agent'],'claude');await tick();return 0},close:async()=>{closes++}})});
 assert.equal(await runTry({cwd:fixture.repo,words:['place-order'],options:{'--agent':'claude'}},ports),0,ports.stderr.text);assert.equal(runs,1);assert.equal(closes,1);assert.ok(opened.endsWith('#agent='+KEY));assert.ok(!ports.stdout.text.includes(KEY));assert.equal(fake.posts.filter(p=>p.command==='try').length,1);
});
test('CHAT8 known credentials are scrubbed before adapter and before reply upload',async()=>{
 let polls=0,received;const s=setup((c,{controller})=>{if(c.path.endsWith('/connect'))return connect(c);if(c.path.includes('/poll')){if(++polls>1){controller.abort();return{lost:true}}return{status:200,json:{connected:true,selected:'codex',message:{id:ID,text:'help gho_secret_owner',agent:'codex',context:{input:{password:'secret'}}}}}}return{status:200,json:{ok:true}}},{askAgent:async args=>{received=args.context;return{say:'gho_secret_owner',fill:null}}});const b=await createAgentBridge(s.context,{},ID,{},'https://runtime.example/s/abc/');await b.run();assert.ok(!JSON.stringify(received).includes('gho_secret_owner'));assert.equal(received.current.input.password,'[redacted]');assert.equal(s.calls.find(c=>c.path.endsWith('/reply')).body.say,'[redacted]');
});

test('CHAT9 approval collection cannot block relay heartbeats',async()=>{
 let polls=0,ticks=0,release;const wait=new Promise(r=>{release=r});
 const s=setup((c,{controller})=>{if(c.path.endsWith('/connect'))return connect(c);if(c.path.includes('/poll')){polls++;if(polls===2)release(true);if(polls>2){controller.abort();return{lost:true}}return{status:200,json:{connected:true,selected:'codex',message:null}}}return{status:200,json:{ok:true}}});
 const b=await createAgentBridge(s.context,{},ID,{},'https://runtime.example/s/abc/');await b.run(async()=>{ticks++;await wait;return true});assert.ok(polls>=2);assert.ok(ticks>=1);
});
