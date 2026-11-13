import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync, symlinkSync, chmodSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {runCheck} from '../../src/runtime-seam.mjs';
import {captureSource} from '../../src/runtime-seam.mjs';
import {harbor, storyTest, fakeRuntime, portsFor} from './runtime-fake.mjs';

const read = (repo,path) => JSON.parse(readFileSync(join(repo,path),'utf8'));
const put = (repo,path,doc) => writeFileSync(join(repo,path),JSON.stringify(doc));
const unpack = (post,path) => {
  const r=spawnSync('tar',['-xOf','-',path],{input:post.tar});
  assert.equal(r.status,0,r.stderr.toString()); return r.stdout.toString();
};
async function setup(t,edit,reply) {
  const env=harbor(t,repo=>{storyTest(repo,'z-broken');edit?.(repo);});
  const fake=await fakeRuntime(t,(entry,fake)=>reply?.(entry,fake) ?? fake.normal(entry));
  const {ports,clock}=portsFor({HOME:env.home,PDD_STATE_DIR:env.state,PDD_RUNTIME_URL:fake.origin});
  return {...env,fake,ports,clock};
}
async function check(args,ports) {
  let code;
  await assert.doesNotReject(async()=>{code=await runCheck(args,ports);},'A broken selected test must not stop the command.');
  return code;
}
const modes={test:{},lint:{'--lint':true},files:{'--files':true}};
const edits={
  entry(repo){const doc=read(repo,'tests/z-broken.json');doc.steps[0].entry_path='prompts/gone.prompt.md';put(repo,'tests/z-broken.json',doc);},
  dependency(repo){const doc=read(repo,'tests/z-broken.json');doc.context=[{prompt_path:doc.steps[0].entry_path,paths:['docs/gone.md']}];put(repo,'tests/z-broken.json',doc);},
  unreadable(repo){symlinkSync('absent.md',join(repo,'broken.md'));const doc=read(repo,'tests/z-broken.json');doc.context=[{prompt_path:doc.steps[0].entry_path,paths:['broken.md']}];put(repo,'tests/z-broken.json',doc);},
  entryPermission(repo){
    writeFileSync(join(repo,'prompts/unreadable.prompt.md'),readFileSync(join(repo,'prompts/place_order.prompt.md')));
    const doc=read(repo,'tests/z-broken.json');doc.steps[0].entry_path='prompts/unreadable.prompt.md';put(repo,'tests/z-broken.json',doc);
  },
  storyPermission(){},
  called(repo){
    writeFileSync(join(repo,'prompts/caller.prompt.md'),readFileSync(join(repo,'prompts/place_order.prompt.md'),'utf8')
      .replace('"calls": []','"calls": [{"target":"prompts/gone.prompt.md","operation":"place_order","max_calls":1}]'));
    const doc=read(repo,'tests/z-broken.json');doc.steps[0].entry_path='prompts/caller.prompt.md';put(repo,'tests/z-broken.json',doc);
  },
  invalid(repo){writeFileSync(join(repo,'tests/z-broken.json'),'{');}
};
for(const [mode,options] of Object.entries(modes)) for(const [kind,edit] of Object.entries(edits)) for(const json of [false,true]) {
  test(`2838 ${mode} ${kind} (json=${json}) keeps the good test and reports the broken test first`,async t=>{
    const {repo,state,fake,ports}=await setup(t,edit);
    if(kind==='entryPermission'||kind==='storyPermission'){
      const path=join(repo,kind==='entryPermission'?'prompts/unreadable.prompt.md':'user_stories/z-broken.md');
      chmodSync(path,0);
    }
    if(mode==='files'&&json){
      const preview=await check({cwd:repo,words:['place-order','z-broken'],options},ports);
      assert.notEqual(preview,0);assert.match(ports.stdout.text,/1 tests could not run/);
      ports.stdout.text='';ports.stderr.text='';
    }
    const code=await check({cwd:repo,words:['place-order','z-broken'],options:{...options,...(json?{'--json':true}:{})}},ports);
    assert.notEqual(code,0);
    const out=ports.stdout.text;
    assert.match(out,/1 tests could not run/);
    if(json){
      const result=JSON.parse(out);assert.equal(result.exit_code,code);
      assert.equal(result.rows[0].test,'tests/z-broken.json');assert.equal(result.rows[0].unsent,true);
      assert.equal(result.rows[0].state,'not run');assert.ok(result.rows[0].refusals[0].message);
      assert.ok(result.rows[0].refusals[0].hint);
      assert.equal(result.rows.find(row=>row.test==='tests/place-order.json').state,mode==='files'?'ready':'passed');
      if(mode!=='files'){
        const saved=read(state,`batches/${result.batch}/batch.json`);
        assert.equal(saved.rows.find(row=>row.test==='tests/z-broken.json').unsent,true);
        const before=fake.posts.length;ports.stdout.text='';
        const reread=await check({cwd:repo,words:[result.batch],options:{'--read':true,'--json':true}},ports);
        assert.notEqual(reread,0);assert.equal(JSON.parse(ports.stdout.text).rows[0].unsent,true);
        assert.equal(fake.posts.length,before);
      }
    }else{
      assert.ok(out.indexOf('tests/z-broken.json')<out.indexOf('tests/place-order.json'));
      assert.match(out,/Fix|Restore/);
    }
    if(mode==='files'){assert.equal(fake.posts.length,0);assert.match(out,/prompts\/place_order.prompt.md/);}
    else {
      assert.equal(fake.posts.filter(post=>post.command==='lint').length,1);
      const lint=fake.posts.find(post=>post.command==='lint');
      const listing=spawnSync('tar',['-tf','-'],{input:lint.tar,encoding:'utf8'}).stdout;
      assert.ok(listing.includes('tests/place-order.json'));assert.ok(!listing.includes('tests/z-broken.json'));
      assert.deepEqual(fake.posts.filter(post=>post.command==='check').map(post=>post.request.scenario),mode==='test'?['tests/place-order.json']:[]);
    }
  });
}

for(const variant of ['missing-check','inexact-check','omitted-item']) for(const mode of ['test','lint']) for(const json of [false,true]) {
  test(`2862 ${variant} ${mode} (json=${json}) checks remaining criteria without a full Story pass`,async t=>{
    const {repo,state,fake,ports}=await setup(t,repo=>{
      const doc=read(repo,'tests/place-order.json');
      doc.steps[0].checks=doc.steps[0].checks.filter(c=>c.criterion_id!=='AC2');
      if(variant==='inexact-check')doc.steps[0].checks.push({criterion_id:'AC2',target:'result',path:'/customerName',op:'exists'});
      if(variant==='omitted-item')doc.criteria=doc.criteria.filter(c=>c.id!=='AC2');
      put(repo,'tests/place-order.json',doc);
    },(entry,fake)=>entry.method==='GET' ? {status:200,json:fake.check(entry.url.split('/').at(-1),'passed',[
      {criterion_id:'AC1',target:'result',path:'/totalCents',op:'equals',expected:900,actual:900,passed:true},
      {criterion_id:'AC3',target:'result',path:'/items/0/quantity',op:'equals',expected:2,actual:2,passed:true}
    ])} : null);
    const before=readFileSync(join(repo,'tests/place-order.json'),'utf8');
    const code=await check({cwd:repo,cache:mode==='test',words:['place-order'],options:{...modes[mode],...(json?{'--json':true}:{})}},ports);
    assert.notEqual(code,0);assert.equal(fake.posts.filter(post=>post.command==='lint').length,1);
    assert.equal(fake.posts.filter(post=>post.command==='check').length,mode==='test'?1:0);
    const wire=JSON.parse(unpack(fake.posts[0],'tests/place-order.json'));
    assert.equal(wire.criteria.length,3);assert.equal(wire.check_exemptions.length,1);
    assert.equal(wire.check_exemptions[0].reason,'out-of-scope');assert.ok(wire.check_exemptions[0].detail);
    assert.equal(wire.check_exemptions[0].criterion_id,variant==='omitted-item'?'ac-2':'AC2');
    assert.deepEqual(wire.steps,JSON.parse(before).steps);
    assert.equal(readFileSync(join(repo,'tests/place-order.json'),'utf8'),before);
    if(json){
      const result=JSON.parse(ports.stdout.text),row=result.rows[0];
      assert.notEqual(row.state,'passed');assert.equal(row.not_checked.length,1);assert.ok(row.not_checked[0].reason);
      if(mode==='test'){assert.equal(row.criteria.total,3);assert.equal(row.criteria.passed,2);assert.equal(row.checks.passed,2);assert.equal(row.calls,1);
        assert.equal(read(repo,'.pdd/cache/test/stories.json').stories['user_stories/place-order.md'].pass,undefined);}
      assert.equal(read(state,`batches/${result.batch}/batch.json`).rows[0].not_checked.length,1);
      const sent=fake.posts.length;ports.stdout.text='';
      const reread=await check({cwd:repo,words:[result.batch],options:{'--read':true,'--json':true}},ports);
      assert.notEqual(reread,0);assert.equal(JSON.parse(ports.stdout.text).rows[0].not_checked.length,1);assert.equal(fake.posts.length,sent);
      if(mode==='test'){
        ports.stdout.text='';
        const direct=await check({cwd:repo,words:[row.request_id],options:{'--read':true,'--json':true}},ports);
        assert.notEqual(direct,0);assert.equal(JSON.parse(ports.stdout.text).rows[0].not_checked.length,1);
        assert.equal(fake.posts.length,sent);
      }
    }else {assert.match(ports.stdout.text,/not checked:/);assert.match(ports.stdout.text,/not a full pass/);}
  });
}

for(const mode of ['test','lint'])test(`2838 ${mode} all broken stays local and counts each test`,async t=>{
  const {repo,ports,fake,clock}=await setup(t,repo=>{edits.entry(repo);writeFileSync(join(repo,'tests/place-order.json'),'{');});
  const code=await check({cwd:repo,words:['place-order','z-broken'],options:{...modes[mode],'--json':true}},ports);
  assert.notEqual(code,0);assert.equal(fake.posts.length,0);assert.equal(clock.gh.length,0);
  const result=JSON.parse(ports.stdout.text);assert.equal(result.rows.length,2);assert.match(result.summary_line,/2 tests could not run/);
});

for(const mode of ['test','lint'])test(`2862 ${mode} with no exact criterion reports every gap without a paid check`,async t=>{
  const {repo,ports,fake,clock}=await setup(t,repo=>{
    const doc=read(repo,'tests/place-order.json');doc.steps[0].checks=[];put(repo,'tests/place-order.json',doc);
  });
  const code=await check({cwd:repo,words:['place-order'],options:{...modes[mode],'--json':true}},ports);
  assert.notEqual(code,0);
  const row=JSON.parse(ports.stdout.text).rows[0];assert.ok(Array.isArray(row.not_checked));assert.equal(row.not_checked.length,3);
  assert.ok(row.not_checked.every(item=>item.reason));assert.notEqual(row.state,'passed');
  assert.equal(fake.posts.length,0);assert.equal(clock.gh.length,0);
});

test('2862 partial coverage preserves other local refusals and authored invalid metadata',async t=>{
  const {repo,fake,ports}=await setup(t,repo=>{
    const doc=read(repo,'tests/place-order.json');doc.steps[0].checks=doc.steps[0].checks.filter(c=>c.criterion_id!=='AC2');put(repo,'tests/place-order.json',doc);
  });
  const original=read(repo,'tests/place-order.json');
  await check({cwd:repo,words:['place-order'],options:{'--json':true}},ports);
  assert.equal(fake.posts.filter(post=>post.command==='check').length,1);
  const edits=[
    doc=>doc.steps[0].checks.push({criterion_id:'AC2',target:'result',path:'/customerName',op:'bogus'}),
    doc=>doc.steps[0].checks.push({criterion_id:'AC2',target:'bogus',path:'/customerName',op:'exists'}),
    doc=>doc.steps[0].checks.push({criterion_id:'AC2',target:'result',path:123,op:'exists'}),
    doc=>{doc.criteria_scope=['AC1'];}, doc=>{doc.check_exemptions=[{}];},
    doc=>{doc.criteria[1].id='AC1';}, doc=>{doc.criteria[1].text='Changed Story text';},
    doc=>{doc.steps[0].input.items[0].quantity=0;},
    doc=>doc.steps[0].checks.push({criterion_id:'unknown',target:'result',path:'/customerName',op:'equals',value:'Sam'})
  ];
  for(const edit of edits){
    const doc=structuredClone(original);edit(doc);put(repo,'tests/place-order.json',doc);ports.stdout.text='';
    const sent=fake.posts.length,code=await check({cwd:repo,words:['place-order'],options:{'--json':true}},ports);
    assert.equal(code,4);assert.equal(fake.posts.length,sent);
    assert.equal(JSON.parse(ports.stdout.text).rows[0].unsent,true);
  }
  put(repo,'tests/place-order.json',original);ports.stdout.text='';
  writeFileSync(join(repo,'pdd-source.json'),'{');
  const sent=fake.posts.length;
  assert.equal(await check({cwd:repo,words:['place-order'],options:{'--json':true}},ports),4);
  assert.equal(JSON.parse(ports.stdout.text).rows[0].state,'not run');assert.equal(fake.posts.length,sent);
  put(repo,'pdd-source.json',{include:[]});
  writeFileSync(join(repo,'tests/z-broken.json'),'{');
  const promptPath=join(repo,'prompts/place_order.prompt.md');
  writeFileSync(promptPath,readFileSync(promptPath,'utf8').replace('"max_model_calls": 2','"max_model_calls": 0'));
  ports.stdout.text='';
  assert.equal(await check({cwd:repo,words:['place-order','z-broken'],options:{'--lint':true,'--json':true}},ports),4);
  const limited=JSON.parse(ports.stdout.text);assert.equal(limited.rows[0].test,'tests/z-broken.json');
  assert.equal(limited.rows[0].unsent,true);assert.match(limited.summary_line,/1 tests could not run/);
  assert.equal(fake.posts.length,sent);

});

test('2838 a broken sibling cannot hide a good test or create a complete Story cache pass',async t=>{
  const {repo,fake,ports}=await setup(t,repo=>{
    const doc=read(repo,'tests/place-order.json');doc.steps[0].entry_path='prompts/gone.prompt.md';put(repo,'tests/place-order.broken.json',doc);
  });
  const code=await check({cwd:repo,cache:true,words:['place-order'],options:{'--json':true}},ports);
  assert.notEqual(code,0);
  assert.match(ports.stdout.text,/1 tests could not run/);const result=JSON.parse(ports.stdout.text);assert.equal(result.rows[0].test,'tests/place-order.broken.json');
  assert.equal(result.rows.find(row=>row.test==='tests/place-order.json').state,'passed');
  assert.deepEqual(fake.posts.filter(post=>post.command==='check').map(post=>post.request.scenario),['tests/place-order.json']);
  assert.equal(read(repo,'.pdd/cache/test/stories.json').stories['user_stories/place-order.md'].pass,undefined);
});

for(const mode of ['test','lint'])for(const json of [false,true])test(`2838 ${mode} sign-in failure (json=${json}) retains broken tests and the other selected row`,async t=>{
  const {repo,fake,ports}=await setup(t,edits.entry);
  ports.gh=()=>({status:1,stdout:''});
  const code=await check({cwd:repo,words:['place-order','z-broken'],options:{...modes[mode],...(json?{'--json':true}:{})}},ports);
  assert.notEqual(code,0);assert.match(ports.stdout.text,/1 tests could not run/);assert.equal(fake.posts.length,0);
  if(json){
    const result=JSON.parse(ports.stdout.text);assert.equal(result.exit_code,code);
    assert.equal(result.rows[0].test,'tests/z-broken.json');assert.equal(result.rows[0].unsent,true);
    assert.equal(result.rows.find(row=>row.test==='tests/place-order.json').state,'not run');
  }else assert.ok(ports.stdout.text.indexOf('tests/z-broken.json')<ports.stdout.text.indexOf('tests/place-order.json'));
});

for(const incompleteAtCapture of [true,false])test(`2862 captured coverage wins over an earlier preflight (incomplete=${incompleteAtCapture})`,async t=>{
  let complete;
  const {repo,ports}=await setup(t,repo=>{
    complete=read(repo,'tests/place-order.json');
    if(!incompleteAtCapture){const doc=structuredClone(complete);doc.steps[0].checks=doc.steps[0].checks.filter(c=>c.criterion_id!=='AC2');put(repo,'tests/place-order.json',doc);}
  });
  let changed=false;
  ports.captureSource=(root,selection)=>{
    if(!changed){changed=true;const doc=structuredClone(complete);
      if(incompleteAtCapture)doc.steps[0].checks=doc.steps[0].checks.filter(c=>c.criterion_id!=='AC2');
      put(repo,'tests/place-order.json',doc);
    }
    return captureSource(root,selection);
  };
  const code=await check({cwd:repo,cache:true,words:['place-order'],options:{'--json':true}},ports);
  const row=JSON.parse(ports.stdout.text).rows[0];
  if(incompleteAtCapture){
    assert.notEqual(code,0);assert.notEqual(row.state,'passed');assert.equal(row.not_checked.length,1);
    assert.equal(read(repo,'.pdd/cache/test/stories.json').stories['user_stories/place-order.md'].pass,undefined);
  }else{assert.equal(code,0);assert.equal(row.state,'passed');assert.equal(row.not_checked,undefined);}
});

for(const mode of ['test','lint'])for(const malformed of ['json','shape','step','check','criterion'])test(`2838 ${mode} refuses captured ${malformed} after a source edit and continues other tests`,async t=>{
  const {repo,fake,ports}=await setup(t,undefined,(entry)=>{
    if(entry.command==='lint'){
      const listing=spawnSync('tar',['-tf','-'],{input:entry.tar,encoding:'utf8'}).stdout;
      if(listing.includes('tests/z-broken.json'))return {status:422,json:{error:{code:'invalid-document',message:'The captured test is malformed.'}}};
    }
    return null;
  });
  let changed=false;
  ports.captureSource=(root,selection)=>{
    if(!changed){changed=true;
      if(['json','shape'].includes(malformed))writeFileSync(join(repo,'tests/z-broken.json'),malformed==='json'?'{':'{}');
      else {const doc=read(repo,'tests/z-broken.json');
        if(malformed==='step')doc.steps=[null];
        if(malformed==='check')doc.steps[0].checks=[null];
        if(malformed==='criterion')doc.criteria=[null];
        put(repo,'tests/z-broken.json',doc);
      }
    }
    return captureSource(root,selection);
  };
  const code=await check({cwd:repo,words:['place-order','z-broken'],options:{...modes[mode],'--json':true}},ports);
  assert.notEqual(code,0);assert.match(ports.stdout.text,/1 tests could not run/);const rows=JSON.parse(ports.stdout.text).rows;
  assert.equal(rows[0].test,'tests/z-broken.json');assert.equal(rows[0].unsent,true);
  assert.equal(rows[0].refusals[0].code,({step:'invalid-step',check:'invalid-check',criterion:'invalid-criterion'})[malformed]??'invalid-document');
  assert.equal(rows.find(row=>row.test==='tests/place-order.json').state,'passed');
  for(const post of fake.posts){
    const listing=spawnSync('tar',['-tf','-'],{input:post.tar,encoding:'utf8'}).stdout;
    assert.ok(!listing.includes('tests/z-broken.json'));
  }
});

for(const mode of ['test','lint','files'])test(`2838 ${mode} never uploads a broken selected test through a required include`,async t=>{
  const {repo,fake,ports}=await setup(t,repo=>{
    writeFileSync(join(repo,'tests/z-broken.json'),'{');put(repo,'pdd-source.json',{include:['tests/z-broken.json']});
  });
  const code=await check({cwd:repo,words:['place-order','z-broken'],options:{...modes[mode],...(mode==='files'?{}:{'--json':true})}},ports);
  assert.notEqual(code,0);assert.equal(fake.posts.length,0);assert.match(ports.stdout.text,/2 tests could not run/);
});

test('2838 a captured refusal invalidates an older cached pass',async t=>{
  const {repo,fake,ports}=await setup(t);
  assert.equal(await check({cwd:repo,cache:true,words:['place-order'],options:{'--json':true}},ports),0);
  assert.ok(read(repo,'.pdd/cache/test/stories.json').stories['user_stories/place-order.md'].pass);
  const original=readFileSync(join(repo,'tests/place-order.json'),'utf8');
  let changed=false;
  ports.captureSource=(root,selection)=>{
    if(!changed){changed=true;writeFileSync(join(repo,'tests/place-order.json'),'{');}
    return captureSource(root,selection);
  };
  ports.stdout.text='';const sent=fake.posts.length;
  assert.notEqual(await check({cwd:repo,cache:true,words:['place-order'],options:{'--json':true}},ports),0);
  assert.match(ports.stdout.text,/1 tests could not run/);assert.equal(JSON.parse(ports.stdout.text).rows[0].unsent,true);assert.equal(fake.posts.length,sent);
  assert.equal(read(repo,'.pdd/cache/test/stories.json').stories['user_stories/place-order.md'].pass,undefined);
  writeFileSync(join(repo,'tests/place-order.json'),original);
});
