import test from 'node:test';
import assert from 'node:assert/strict';
import { join } from 'node:path';
import { mkdirSync, writeFileSync, rmSync } from 'node:fs';
import { Readable } from 'node:stream';
import { runPdd } from '../src/pdd-cli.mjs';
import { harbor, fakeRuntime, portsFor, PLACE } from './runtime-fake.mjs';

for (const kind of ['screen','http']) test(`C classification precedes typed input for ${kind}`, async t => {
  const setup=harbor(t), env={HOME:setup.home,PDD_STATE_DIR:setup.state,PATH:'/usr/bin:/bin'};
  const calls=[];
  const programApp={appKind(input,ports){calls.push(['kind',input]);return kind;},async runApp(input,ports){calls.push(['run',input]);ports.stdout.write('http://127.0.0.1:8080/\n');return 7;}};
  const io=portsFor(env,{programApp,stdin:Readable.from([])});
  const code=await runPdd(['--fresh','--data','seed.json',PLACE,'--name','suffix'],{cwd:setup.repo,env,stdout:io.ports.stdout,stderr:io.ports.stderr,stdin:io.ports.stdin,runtimePorts:io.ports});
  assert.equal(code,7,io.ports.stderr.text);
  assert.deepEqual(calls.map(c=>c[0]),['kind','run']);
  assert.deepEqual(calls[0][1],{file:PLACE,root:setup.repo});
  assert.deepEqual(calls[1][1],{file:PLACE,root:setup.repo,env,flags:{fresh:true,data:'seed.json'}});
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
  let module;
  try {module=await import('../src/program-session.mjs');}catch(error){assert.fail(`Public openProgramSession is required: ${error.code}`);}
  const setup=harbor(t,root=>{rmSync(join(root,'tests'),{recursive:true});rmSync(join(root,'user_stories'),{recursive:true});});
  const fake=await fakeRuntime(t,(e,f)=>{
    if(e.method==='GET'&&e.url.endsWith('/model'))return {status:200,json:{app_map:true,entries:[]}};
    return e.command==='lint'?{status:200,json:f.lint(e.request.requestId)}:{status:200,json:f.tryJob(e.request.requestId)};
  });
  const env={HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin};const io=portsFor(env);
  const dir=join(setup.repo,'.pdd/run/app');mkdirSync(dir,{recursive:true});
  const appMap={schema_version:'prompt-runtime.app-map.v1',name:'Example',screens:[]};
  const overlay=()=>[{path:'generated/map.json',bytes:JSON.stringify(appMap)},{path:'generated/seed.json',bytes:'{"count":3}'}];
  const args={root:setup.repo,file:PLACE,program:'app',data:{dir,fresh:false,startingData:{initial_world:{}}},appMap,overlay};
  const first=await module.openProgramSession(args,io.ports);
  const request=fake.posts.find(p=>p.command==='try');
  assert.deepEqual(request.request.app_map,appMap);assert.equal('overlay' in request.request,false);
  assert.ok(request.tar.includes(Buffer.from('generated/seed.json')));assert.ok(request.tar.includes(Buffer.from('{"count":3}')));
  for(const session of [first,await module.openProgramSession(args,io.ports)]){
    assert.equal(session.id,first.id);assert.equal(session.url,first.url);assert.match(session.url,/\/s\//);
    assert.equal(session.serve.origin,fake.origin);assert.equal(typeof session.serve.request,'function');
    const reply=await session.serve.request(`/v1/try/${session.id}/model`,{method:'GET'});assert.equal(reply.status,200);
  }
  assert.equal(fake.posts.filter(p=>p.command==='try').length,1);
});
