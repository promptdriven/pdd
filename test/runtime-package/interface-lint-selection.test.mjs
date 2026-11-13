import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {harbor,storyTest,fakeRuntime,portsFor} from './runtime-fake.mjs';
import {runCheck} from '../../src/runtime-seam.mjs';
import {proseSha256} from '../../src/runtime-seam.mjs';

const nativePath='prompts/kernel.prompt.md',nativeTest='tests/kernel.json';
const reason='cross-process filesystem locks';
function mixed(repo,invalid=false) {
  storyTest(repo,'kernel');
  let text='# Kernel\n\n<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify({kind:'native-only',reason,status:'draft',prose_sha256:''})+'\n```\n</details>\n';
  text=text.replace('"prose_sha256":""',`"prose_sha256":"${proseSha256(text)}"`);
  writeFileSync(join(repo,nativePath),text);
  const path=join(repo,nativeTest),doc=JSON.parse(readFileSync(path));
  doc.steps[0].entry_path=nativePath;
  writeFileSync(path,JSON.stringify(doc));
  if (invalid) {
    storyTest(repo,'invalid-kernel');
    const path=join(repo,'tests/invalid-kernel.json'),doc=JSON.parse(readFileSync(path));
    doc.steps[0].entry_path=nativePath;doc.criteria=[];
    writeFileSync(path,JSON.stringify(doc));
  }
}
function selection(post) {
  const listing=spawnSync('tar',['-tf','-'],{input:post.tar,encoding:'utf8'});
  assert.equal(listing.status,0);
  const paths=listing.stdout.split('\n').filter(Boolean);
  assert.ok(post.request.tests.length>0);
  assert.ok(!post.request.tests.includes(nativeTest),'native scenario omitted from named lint');
  assert.ok(!paths.includes(nativeTest),'native scenario omitted from archive');
  for(const path of post.request.tests) assert.ok(paths.includes(path),`named scenario absent from archive: ${path}`);
  assert.deepEqual(post.request.tests,paths.filter(path=>/^tests\/.*\.json$/.test(path)).sort());
}
for(const lint of [false,true]) test(`named ${lint?'lint':'check'} uses exactly executable archive scenarios`,async t=>{
  const setup=harbor(t,repo=>mixed(repo,true));
  const fake=await fakeRuntime(t,(entry,f)=>f.normal(entry));
  fake.capacity=()=>({status:200,json:{maintenance:null,features:['lint-tests']}});
  const {ports}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:setup.repo,options:{'--json':true,...(lint?{'--lint':true}:{})}},ports),5);
  selection(fake.posts.find(post=>post.command==='lint'));
  const result=JSON.parse(ports.stdout.text),row=result.rows.find(row=>row.test===nativeTest);
  assert.equal(row.state,'not run');
  assert.equal(row.reason.code,'native-only');
  assert.deepEqual(row.native_only,[{path:nativePath,reason}]);
  assert.ok(result.rows.filter(row=>!row.unsent).every(row=>row.state==='passed'));
});
for(const json of [false,true]) for(const stop of [false,true]) test(`lint ${stop?'stop':'temporary refusal'} retains local evidence in ${json?'JSON':'text'}`,async t=>{
  const setup=harbor(t,repo=>mixed(repo,true));
  const fake=await fakeRuntime(t,()=>({status:stop?401:503,json:{error:{code:stop?'auth-required':'github-unavailable',message:'source-service-test-error'}}}));
  const {ports}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  assert.equal(await runCheck({cwd:setup.repo,options:{'--lint':true,...(json?{'--json':true}:{})}},ports),5);
  assert.equal(fake.posts.filter(post=>post.command==='check').length,0);
  if(!stop) assert.ok(ports.stderr.text.includes('source-service-test-error'));
  assert.ok(ports.stdout.text.includes(reason),'native reason in immediate output');
  assert.ok(ports.stdout.text.includes(nativePath),'native prompt in immediate output');
  if(json) {
    const result=JSON.parse(ports.stdout.text),row=result.rows.find(row=>row.test===nativeTest);
    assert.equal(row.state,'not run');assert.equal(row.reason.code,'native-only');
    assert.deepEqual(row.native_only,[{path:nativePath,reason}]);
    assert.deepEqual(result.coverage.runtime,{checkable:1,total:2,native_only:1});
    const broken=result.rows.find(row=>row.test==='tests/invalid-kernel.json');
    assert.equal(broken.state,'not run');assert.equal(broken.reason.code,'broken-test');
    assert.ok(broken.refusals.length>0);assert.deepEqual(broken.native_only,[{path:nativePath,reason}]);
    const saved=JSON.parse(readFileSync(join(setup.state,'batches',result.batch,'batch.json')));
    assert.deepEqual(saved.source_selection.tests,['tests/place-order.json','tests/unknown-item.json']);
  } else assert.match(ports.stdout.text,/Runtime coverage:/);
});

for(const legacy of [false,true]) test(`saved mixed check continues with exact source selection (${legacy?'legacy':'current'} record)`,async t=>{
  const setup=harbor(t,repo=>mixed(repo,true));
  let complete=false;
  const fake=await fakeRuntime(t,(entry,f)=>{
    if(entry.command==='lint') return {status:202,json:f.job(entry.request.requestId,'lint','queued')};
    const id=entry.url.split('/').at(-1);
    if(entry.method==='GET' && f.posts.some(post=>post.command==='lint' && post.request.requestId===id))
      return {status:200,json:complete?f.lint(id):f.job(id,'lint','running')};
    return f.normal(entry);
  });
  fake.capacity=()=>({status:200,json:{maintenance:null,features:['lint-tests']}});
  const env={HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin};
  const first=portsFor(env);
  assert.equal(await runCheck({cwd:setup.repo,options:{'--json':true,'--timeout':0.01}},first.ports),3);
  const result=JSON.parse(first.ports.stdout.text),path=join(setup.state,'batches',result.batch,'batch.json');
  const before=JSON.parse(readFileSync(path));
  const native=before.rows.filter(row=>row.native_only?.length);
  const tests=['tests/place-order.json','tests/unknown-item.json'];
  assert.deepEqual(before.source_selection?.tests,tests);
  if(legacy) {delete before.source_selection;writeFileSync(path,JSON.stringify(before));}
  complete=true;
  const next=portsFor(env);
  assert.equal(await runCheck({cwd:setup.repo,options:{'--read':result.batch,'--json':true,'--timeout':1}},next.ports),5);
  const saved=JSON.parse(readFileSync(path));
  assert.deepEqual(saved.source_selection.tests,tests);
  assert.deepEqual(saved.rows.filter(row=>row.native_only?.length),native);
  for(const post of fake.posts) {
    if(post.command==='lint') selection(post);
    if(post.command==='check') assert.ok(tests.includes(post.request.scenario));
  }
  assert.equal(fake.posts.filter(post=>post.command==='check').length,tests.length);
  assert.ok(JSON.parse(next.ports.stdout.text).rows.filter(row=>!row.unsent).every(row=>row.state==='passed'));
});

for(const allNative of [false,true]) test(`files preview omits native closures (${allNative?'all native':'mixed'})`,async t=>{
  const setup=harbor(t,repo=>mixed(repo));
  const words=allNative?['kernel']:['place-order','kernel'];
  const env={HOME:setup.home,PDD_STATE_DIR:setup.state};
  const preview=portsFor(env,{gh:()=>assert.fail('files preview must not authenticate')});
  assert.equal(await runCheck({cwd:setup.repo,words,options:{'--files':true,'--json':true}},preview.ports),0);
  const result=JSON.parse(preview.ports.stdout.text),files=result.files.map(file=>file.path);
  assert.ok(!files.includes(nativeTest),'native scenario omitted from preview');
  assert.ok(!files.includes(nativePath),'native prompt omitted from preview');
  const row=result.rows.find(row=>row.test===nativeTest);
  assert.equal(row.state,'not run');assert.equal(row.reason.code,'native-only');
  assert.deepEqual(row.native_only,[{path:nativePath,reason}]);
  const text=portsFor(env,{gh:()=>assert.fail('files preview must not authenticate')});
  assert.equal(await runCheck({cwd:setup.repo,words,options:{'--files':true}},text.ports),0);
  assert.ok(text.ports.stdout.text.includes(reason));
  if(allNative) assert.equal(files.length,0);
  else {
    const fake=await fakeRuntime(t,(entry,f)=>f.normal(entry));
    const actual=portsFor({...env,PDD_RUNTIME_URL:fake.origin});
    assert.equal(await runCheck({cwd:setup.repo,words,options:{'--json':true}},actual.ports),5);
    const post=fake.posts.find(post=>post.command==='lint');
    const tar=spawnSync('tar',['-tf','-'],{input:post.tar,encoding:'utf8'});
    assert.equal(tar.status,0);
    assert.deepEqual(files,tar.stdout.split('\n').filter(Boolean));
  }
});
