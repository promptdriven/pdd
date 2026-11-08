import test from 'node:test';
import assert from 'node:assert/strict';
import {chmodSync,readFileSync,writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {runCheck} from '../src/runtime-client.mjs';
import {findTests,preflight} from '../src/runtime-preflight.mjs';
import {harbor,storyTest,fakeRuntime,portsFor,sha} from './runtime-fake.mjs';

const read=(root,path)=>JSON.parse(readFileSync(join(root,path),'utf8'));
const refusalDetails=row=>row.refusals.map(({code,section,message,hint})=>({code,section,message,hint}));
for(const mode of ['test','lint'])for(const json of [false,true])for(const reviewed of [false,true]){
  test(`2838 numeric reviews isolate unreadable test: ${mode}, json=${json}, reviewed sibling=${reviewed}`,async t=>{
    const {repo,home,state}=harbor(t,repo=>{
      storyTest(repo,'z-broken');
      const path=join(repo,'tests/place-order.json'),doc=read(repo,'tests/place-order.json');
      const step=doc.steps[0],check=step.checks.find(c=>c.criterion_id==='AC1'&&c.path==='/totalCents');
      check.value=899;
      writeFileSync(path,JSON.stringify(doc));
      writeFileSync(join(repo,'pdd-numeric-reviews.json'),JSON.stringify({schema_version:'pdd.numeric-reviews.v1',reviews:[{
        test_path:reviewed?'tests/place-order.json':'tests/unrelated.json',test_sha256:sha(readFileSync(path)),
        step_id:step.step_id,criterion_id:check.criterion_id,target:check.target,path:check.path,value:check.value,
        reason:'The reviewed assertion measures a component.'
      }]}));
    });
    chmodSync(join(repo,'tests/z-broken.json'),0);
    const fake=await fakeRuntime(t,(entry,f)=>f.normal(entry));
    const {ports}=portsFor({HOME:home,PDD_STATE_DIR:state,PDD_RUNTIME_URL:fake.origin});
    let code;
    await assert.doesNotReject(async()=>{
      code=await runCheck({cwd:repo,words:['place-order','z-broken'],options:{
        ...(mode==='lint'?{'--lint':true}:{}),...(json?{'--json':true}:{})
      }},ports);
    },'Numeric-review metadata must not abort a selection with an unreadable test.');
    assert.equal(code,4);
    const output=ports.stdout.text;
    assert.match(output,/1 tests could not run/);
    assert.doesNotMatch(output,/numeric reviews are ignored/);
    if(mode==='test')assert.equal(/possible numeric mismatch/.test(output),!reviewed);
    const found=findTests({root:repo});
    let checked;
    assert.doesNotThrow(()=>{checked=preflight({root:repo,found,selected:found.tests});},
      'Numeric reviews must preserve per-test isolation at the public preflight boundary.');
    const sibling=checked.rows.find(r=>r.test==='tests/place-order.json');
    assert.equal(sibling.warnings.some(w=>/possible numeric mismatch/.test(w)),!reviewed);
    if(json){
      const result=JSON.parse(output),row=result.rows[0];
      assert.equal(result.exit_code,4);assert.equal(row.test,'tests/z-broken.json');
      assert.equal(row.state,'refused');assert.equal(row.unsent,true);
      assert.ok(row.refusals[0].message.includes('tests/z-broken.json'));assert.match(row.refusals[0].message,/EACCES/);assert.ok(row.refusals[0].hint);
      assert.equal(result.rows.find(r=>r.test==='tests/place-order.json').state,'passed');
      const saved=read(state,`batches/${result.batch}/batch.json`).rows.find(r=>r.test===row.test);
      assert.equal(saved.state,'refused');assert.equal(saved.unsent,true);assert.deepEqual(refusalDetails(saved),refusalDetails(row));
      ports.stdout.text='';const sent=fake.posts.length;
      assert.equal(await runCheck({cwd:repo,words:[result.batch],options:{'--read':true,'--json':true}},ports),4);
      const reread=JSON.parse(ports.stdout.text);
      assert.equal(reread.rows[0].test,row.test);assert.deepEqual(reread.rows[0].refusals,row.refusals);
      assert.match(reread.summary_line,/1 tests could not run/);assert.equal(fake.posts.length,sent);
    }else{
      assert.ok(output.indexOf('tests/z-broken.json')<output.indexOf('tests/place-order.json'));
      assert.match(output,/EACCES/);assert.match(output,/Restore|readable/);
    }
    assert.deepEqual(fake.posts.filter(p=>p.command==='check').map(p=>p.request.scenario),mode==='test'?['tests/place-order.json']:[]);
    assert.equal(fake.posts.filter(p=>p.command==='lint').length,1);
    for(const post of fake.posts){
      const listing=spawnSync('tar',['-tf','-'],{input:post.tar,encoding:'utf8'});
      assert.equal(listing.status,0);assert.ok(listing.stdout.includes('tests/place-order.json'));
      assert.ok(!listing.stdout.includes('tests/z-broken.json'));
    }
  });
}
