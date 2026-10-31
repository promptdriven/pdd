import test from 'node:test';
import assert from 'node:assert/strict';
import { join } from 'node:path';
import { mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { Readable } from 'node:stream';
import { runPdd } from '../src/pdd-cli.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';

async function loadProgramSession() {
  try { return await import('../src/program-session.mjs'); }
  catch (error) { assert.fail(`Public openProgramSession is required: ${error.code}`); }
}

for (const kind of ['screen','http']) test(`C classification precedes typed input for ${kind}`, async t => {
  const setup=harbor(t), env={HOME:setup.home,PDD_STATE_DIR:setup.state,PATH:'/usr/bin:/bin'};
  const calls=[];
  const programApp={appKind(input,ports){calls.push(['kind',input]);return kind;},async runApp(input,ports){calls.push(['run',input]);ports.stdout.write('http://127.0.0.1:8080/\n');return 7;}};
  const io=portsFor(env,{programApp,stdin:Readable.from([])});
  const code=await runPdd(['--reset','--data','seed.json',PLACE],{cwd:setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
  assert.equal(code,7,io.ports.stderr.text);
  assert.deepEqual(calls.map(c=>c[0]),['kind','run']);
  assert.deepEqual(calls[0][1],{file:PLACE,root:setup.repo,all:true});
  assert.deepEqual(calls[1][1],{file:PLACE,root:setup.repo,env,kind,flags:{reset:true,data:join(setup.repo,'seed.json')}});
  assert.equal(io.ports.stdout.text,'http://127.0.0.1:8080/\n');
  assert.equal(io.clock.gh.length,0);
});

test('C null result continues local typed usage without dispatch',async t=>{
  const setup=harbor(t),env={HOME:setup.home,PDD_STATE_DIR:setup.state};let classified=0;
  const io=portsFor(env,{programApp:{appKind(){classified++;return null;},runApp(){assert.fail('null is not an app');}},stdin:Readable.from([])});
  const code=await runPdd([PLACE,'--help'],{cwd:setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
  assert.equal(classified,1);assert.equal(code,0,io.ports.stderr.text);assert.match(io.ports.stdout.text,/Usage:/);assert.equal(io.clock.gh.length,0);
});

test('C session preserves app map, uploads overlay and returns proxy capability on reuse',async t=>{
  const module=await loadProgramSession();
  const setup=harbor(t,root=>{rmSync(join(root,'tests'),{recursive:true});rmSync(join(root,'user_stories'),{recursive:true});});
  const fake=await fakeRuntime(t,(e,f)=>{
    if(e.method==='GET'&&e.url.endsWith('/model'))return {status:200,json:{app_map:true,entries:[]}};
    return e.command==='lint'?{status:200,json:f.lint(e.request.requestId)}:{status:200,json:f.tryJob(e.request.requestId)};
  });
  const env={HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin};const io=portsFor(env);
  const dir=join(setup.repo,'.pdd/run/app');mkdirSync(dir,{recursive:true});
  const appMap='generated/map.json';
  const mapDoc={schema_version:'prompt-runtime.app-map.v1',name:'Example',initial_screen:'menu',screens:[{id:'menu',prompt_path:PLACE}]};
  const overlay=()=>[{path:'generated/map.json',bytes:JSON.stringify(mapDoc)},{path:'generated/seed.json',bytes:'{"count":3}'}];
  const args={root:setup.repo,file:PLACE,program:'app',data:{dir,fresh:false,startingData:{initial_world:{}}},appMap,overlay};
  const first=await module.openProgramSession(args,io.ports);
  const request=fake.posts.find(p=>p.command==='try');
  assert.equal(request.request.app_map,appMap);assert.equal(request.request.tab,'screen');assert.equal('overlay' in request.request,false);
  assert.ok(request.tar.includes(Buffer.from('generated/seed.json')));assert.ok(request.tar.includes(Buffer.from('{"count":3}')));
  for(const session of [first,await module.openProgramSession(args,io.ports)]){
    assert.equal(session.id,first.id);assert.equal(session.url,first.url);assert.match(session.url,/\/s\//);
    assert.equal(session.serve.origin,fake.origin);assert.equal(typeof session.serve.request,'function');
    const reply=await session.serve.request(`/v1/try/${session.id}/model`,{method:'GET'});assert.equal(reply.status,200);
  }
  assert.equal(fake.posts.filter(p=>p.command==='try').length,1);
});

test('C async launch rejection becomes a plain pdd error',async t=>{
 const setup=harbor(t),env={HOME:setup.home,PDD_STATE_DIR:setup.state};
 const io=portsFor(env,{programApp:{appKind(){return 'http';},async runApp(){await Promise.resolve();throw new Error('App could not start');}},stdin:Readable.from([])});
 let code;try{code=await runPdd([PLACE],{cwd:setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});}catch(error){assert.fail(`C rejection must be handled: ${error.message}`);}
 assert.equal(code,125,io.ports.stderr.text);assert.match(io.ports.stderr.text,/App could not start/);assert.doesNotMatch(io.ports.stderr.text,/\n\s+at /);assert.equal(io.clock.gh.length,0);
});

for (const [descriptor,label] of [[{kinds:['screen'],screenOperations:['render','select']},'descriptor'],['screen','legacy']]) test(`Pocket screen owns render/select with ${label}`,async t=>{
 const setup=harbor(t),env={HOME:setup.home,PDD_STATE_DIR:setup.state};
 const path=join(setup.repo,PLACE);let text=(await import('node:fs')).readFileSync(path,'utf8');
 const {proseSha256}=await import('../src/runtime-preflight.mjs');
 // Use the fixture's public runtime interface, retaining its schemas.
 const match=text.match(/```json\s*([\s\S]*?)```/);const spec=JSON.parse(match[1]);
 const base=spec.entries[0];spec.entries=[{...base,operation:'render'},{...base,operation:'select'}];spec.conventions=[];
 text=text.replace(match[1],JSON.stringify(spec)+'\n');spec.prose_sha256=proseSha256(text);text=text.replace(/```json\s*[\s\S]*?```/,'```json\n'+JSON.stringify(spec)+'\n```');writeFileSync(path,text);
 let launch;const io=portsFor(env,{stdin:Readable.from([]),programApp:{appKind(){return descriptor;},runApp(input){launch=input;return 0;}}});
 const code=await runPdd([PLACE],{cwd:setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
 assert.equal(code,0,io.ports.stderr.text);assert.equal(launch.kind,'screen');assert.equal(io.clock.gh.length,0);
});

for(const args of [['extra'],['--port','9000']])test(`HTTP suffix refuses locally: ${args.join(' ')}`,async t=>{
 const setup=harbor(t),env={HOME:setup.home,PDD_STATE_DIR:setup.state};
 const io=portsFor(env,{stdin:Readable.from([]),programApp:{appKind(){return 'http';},runApp(){assert.fail('invalid suffix must not launch');}}});
 const code=await runPdd([PLACE,...args],{cwd:setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
 assert.equal(code,2,io.ports.stderr.text);assert.match(io.ports.stderr.text,/HTTP programs take no ARGS\. Call the link\./);

 assert.equal(io.clock.gh.length,0);
});

for(const appMap of [{schema_version:'prompt-runtime.app-map.v1'},'../escape.json','/tmp/map.json'])test(`invalid C appMap refuses before authentication: ${JSON.stringify(appMap)}`,async t=>{
 const module=await loadProgramSession();const setup=harbor(t);
 const fake=await fakeRuntime(t,(e,f)=>e.command==='lint'?{status:200,json:f.lint(e.request.requestId)}:{status:200,json:f.tryJob(e.request.requestId)});
 const env={HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin};const io=portsFor(env);
 const dir=join(setup.repo,'.pdd/run/app');mkdirSync(dir,{recursive:true});
 await assert.rejects(()=>module.openProgramSession({root:setup.repo,file:PLACE,program:'app',data:{dir,fresh:false,startingData:{initial_world:{}}},appMap},io.ports),/app.?map|path|relative/i);
 assert.equal(io.clock.gh.length,0);assert.equal(fake.posts.length,0);
});

for(const withMap of [true,false])test(`C disk map capture and CLI omission: ${withMap}`,async t=>{
 const module=await loadProgramSession();
 const appMap='app-map.json',doc={schema_version:'prompt-runtime.app-map.v1',name:'Disk',initial_screen:'menu',screens:[{id:'menu',prompt_path:PLACE}]};
 const setup=harbor(t,root=>{if(withMap)writeFileSync(join(root,appMap),JSON.stringify(doc));});
 const fake=await fakeRuntime(t,(e,f)=>e.command==='lint'?{status:200,json:f.lint(e.request.requestId)}:{status:200,json:f.tryJob(e.request.requestId)});
 const env={HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin},io=portsFor(env),dir=join(setup.repo,'.pdd/run/app');mkdirSync(dir,{recursive:true});
 await module.openProgramSession({root:setup.repo,file:PLACE,program:'app',data:{dir,fresh:false,startingData:{initial_world:{}}},...(withMap?{appMap}:{})},io.ports);
 const request=fake.posts.find(p=>p.command==='try');
 if(withMap){assert.equal(request.request.app_map,appMap);assert.equal(request.request.tab,'screen');assert.ok(request.tar.includes(Buffer.from(JSON.stringify(doc))));}
 else {assert.equal('app_map' in request.request,false);assert.equal('tab' in request.request,false);}
});

test('recognized prefix port and cwd data reach HTTP unchanged',async t=>{
 const setup=harbor(t),env={HOME:setup.home,PDD_STATE_DIR:setup.state};const cwd=join(setup.repo,'sub folder');mkdirSync(cwd);let launch;
 const io=portsFor(env,{stdin:Readable.from([]),programApp:{appKind(){return {kinds:['http'],httpOperations:['place_order']};},runApp(input){launch=input;return 0;}}});
 const code=await runPdd(['--port','9000','--data','seed file.json','../'+PLACE],{cwd,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
 assert.equal(code,0,io.ports.stderr.text);assert.equal(launch.kind,'http');assert.deepEqual(launch.flags,{port:'9000',data:join(cwd,'seed file.json')});assert.equal(io.clock.gh.length,0);
});

test('screen descriptor keeps genuine typed operation in word table',async t=>{
 const setup=harbor(t),env={HOME:setup.home,PDD_STATE_DIR:setup.state};
 const io=portsFor(env,{stdin:Readable.from([]),programApp:{appKind(){return {kinds:['screen'],screenOperations:['render','select']};},runApp(){assert.fail('another typed operation requires selection');}}});
 const code=await runPdd([PLACE],{cwd:setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
 assert.equal(code,2,io.ports.stderr.text);assert.match(io.ports.stderr.text,/no "start" in its Interface/);assert.match(io.ports.stderr.text,/Declare what starts/);assert.equal(io.clock.gh.length,0);
});
