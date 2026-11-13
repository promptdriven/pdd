import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { runCheck } from '../src/runtime-client.mjs';
import { runApprove } from '../src/prompt-approve.mjs';
import { interfaceBlocks, proseSha256, interfaceSchemaProblems } from '../src/runtime-preflight.mjs';
import { harbor, PLACE, sink, fakeRuntime, portsFor, storyTest } from './runtime-fake.mjs';

function declaration(repo, value) {
  const file = join(repo,PLACE), old = readFileSync(file,'utf8'), block = interfaceBlocks(old)[0];
  let text = old.replace(block[0],`<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify({status:'draft',prose_sha256:'',...value})}\n\`\`\`\n</details>`);
  text = text.replace('"prose_sha256":""',`"prose_sha256":"${proseSha256(text)}"`);
  writeFileSync(file,text);
}
function ports(setup) {
  return {stdout:sink(),stderr:sink(),env:{HOME:setup.home,PDD_RUNTIME_STATE_DIR:setup.state},gh(){assert.fail('native-only/local lint must not sign in');}};
}

test('native-only declares an unfakeable effect, records its approval and skips execution', async t => {
  const reason = 'Kernel ownership after atomic rename cannot be observed by blob ports.';
  const setup = harbor(t,repo => declaration(repo,{kind:'native-only',reason}));
  const p = ports(setup);
  assert.equal(await runApprove({cwd:setup.repo,words:[PLACE],said:'Reviewed the kernel effect.'},{...p,interactive:false}),0,p.stderr.text);
  const iface = JSON.parse(interfaceBlocks(readFileSync(join(setup.repo,PLACE),'utf8'))[0][1]);
  assert.equal(iface.status,'approved'); assert.equal(iface.reason,reason);
  const journal = JSON.parse(readFileSync(join(setup.repo,'.git/pdd/approvals.json'),'utf8'));
  assert.equal(journal.approvals[0].prompts[0].reason,reason);
  const out = ports(setup);
  assert.equal(await runCheck({cwd:setup.repo,options:{'--json':true}},out),5);
  const result = JSON.parse(out.stdout.text);
  assert.equal(result.rows[0].state,'not run');
  assert.match(result.rows[0].reason.message,/Kernel ownership/);
  assert.equal(result.rows[0].calls,0);
  assert.equal(result.coverage.runtime.native_only,1);
  assert.equal(result.coverage.runtime.checkable,0);
});

test('native-only missing a reason refuses before approval even when marked current', async t => {
  for (const reason of [undefined,'','   ']) {
    const setup = harbor(t,repo => declaration(repo,{status:'approved',kind:'native-only',...(reason === undefined ? {} : {reason})}));
    const p=ports(setup);
    assert.equal(await runApprove({cwd:setup.repo,words:[PLACE],said:'yes'},{...p,interactive:false}),4);
    assert.match(p.stdout.text,/native-reason-missing/);
  }
});

test('kind parsing refuses unknown kinds and preserves full, partial and legacy schemas', () => {
  const minimal={limits:{max_steps:1,max_model_calls:1},entries:[]};
  for(const kind of ['other',null,false,0,'']) assert.equal(interfaceSchemaProblems({...minimal,kind})[0]?.code,'interface-kind-invalid');
  assert.equal(interfaceSchemaProblems({kind:'native-only',reason:'Real kernel process identity.'}).length,0);
  for (const kind of [undefined,'full','partial']) assert.equal(interfaceSchemaProblems({...minimal,...(kind ? {kind} : {})}).length,0);
});

test('local lint finds missing interfaces without a Story and gives a usable draft command', async t => {
  const setup=harbor(t,repo => {
    mkdirSync(join(repo,'plain'),{recursive:true});
    writeFileSync(join(repo,'plain/no block.prompt.md'),'# Native behavior\n\nReturn the selected name.\n');
  });
  const p=ports(setup);
  assert.equal(await runCheck({cwd:setup.repo,options:{'--lint':true,'--local':true,'--json':true}},p),4);
  const result=JSON.parse(p.stdout.text), problem=result.problems.find(item => item.path==='plain/no block.prompt.md');
  assert.equal(problem.code,'interface-missing');
  assert.match(problem.message,/pdd interface draft 'plain\/no block.prompt\.md'/);
});

test('server lint refuses a missing block locally when unauthenticated', async t => {
  const setup=harbor(t,repo => {const file=join(repo,PLACE);writeFileSync(file,readFileSync(file,'utf8').replace(interfaceBlocks(readFileSync(file,'utf8'))[0][0],''));});
  const p={...ports(setup),gh:()=>({status:1,stdout:''}),fetch:()=>assert.fail('unauthenticated lint must not contact Runtime')};
  assert.equal(await runCheck({cwd:setup.repo,options:{'--lint':true,'--json':true}},p),4);
  assert.equal(JSON.parse(p.stdout.text).problems[0].code,'interface-missing');
});

test('native-only reached through a call does not execute the caller or inflate coverage', async t => {
  const setup=harbor(t,repo => {
    const file=join(repo,PLACE),text=readFileSync(file,'utf8'),block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);
    iface.calls=[{target:'prompts/kernel.prompt.md',target_operation:'rename',max_calls:1}];
    writeFileSync(file,text.replace(block[1],JSON.stringify(iface)));
    let native='# Kernel\n\n<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify({kind:'native-only',status:'draft',prose_sha256:'',reason:'Kernel file ownership after rename.'})+'\n```\n</details>\n';
    native=native.replace('"prose_sha256":""',`"prose_sha256":"${proseSha256(native)}"`);
    writeFileSync(join(repo,'prompts/kernel.prompt.md'),native);
  });
  const p=ports(setup);
  await runCheck({cwd:setup.repo,options:{'--json':true}},p);
  const result=JSON.parse(p.stdout.text);
  assert.equal(result.rows[0].state,'not run');
  assert.equal(result.coverage?.runtime?.total,2);
  assert.equal(result.coverage.runtime.native_only,1);
  assert.equal(result.coverage.runtime.checkable,1);
  assert.match(result.rows[0].reason.message,/ownership/);
});


test('mixed selections keep native-only out of uploads while checking other Stories', async t => {
  const setup=harbor(t,repo=>{
    storyTest(repo,'kernel');
    let text='# Kernel\n\n<details><summary>Runtime interface</summary>\n\n```json\n'+JSON.stringify({kind:'native-only',status:'draft',prose_sha256:'',reason:'Kernel PID liveness cannot be observed by process replies.'})+'\n```\n</details>\n';
    text=text.replace('"prose_sha256":""',`"prose_sha256":"${proseSha256(text)}"`);
    writeFileSync(join(repo,'prompts/kernel.prompt.md'),text);
    const file=join(repo,'tests/kernel.json'),doc=JSON.parse(readFileSync(file,'utf8'));
    doc.steps[0].entry_path='prompts/kernel.prompt.md';writeFileSync(file,JSON.stringify(doc));
  });
  for(const lint of [false,true]) {
    const fake=await fakeRuntime(t,(entry,server)=>server.normal(entry));
    const {ports:p}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state+(lint ? '-lint' : ''),PDD_RUNTIME_URL:fake.origin});
    const code=await runCheck({cwd:setup.repo,options:{'--json':true,...(lint ? {'--lint':true} : {})}},p);
    assert.equal(code,5,p.stdout.text+p.stderr.text);
    const result=JSON.parse(p.stdout.text),native=result.rows.find(row=>row.test==='tests/kernel.json');
    assert.equal(native.state,'not run');assert.match(native.reason.message,/PID liveness/);
    assert.equal(result.rows.find(row=>row.test==='tests/place-order.json').state,'passed');
    for(const post of fake.posts) {
      const listing=(await import('node:child_process')).spawnSync('tar',['-tf','-'],{input:post.tar,encoding:'utf8'});
      assert.equal(listing.status,0);assert.doesNotMatch(listing.stdout,/kernel/);
    }
    if(!lint) assert.ok(fake.posts.some(post=>post.command==='check'));
  }
});

test('native-only text output includes its reason and a separate Runtime coverage line', async t => {
  const setup=harbor(t,repo=>declaration(repo,{kind:'native-only',reason:'Real kernel process identity.'}));
  const p=ports(setup);
  assert.equal(await runCheck({cwd:setup.repo},p),5);
  assert.match(p.stdout.text,/NOT RUN[^\n]*Real kernel process identity/);
  assert.match(p.stdout.text,/Runtime coverage: 0 of 1 prompts checkable, 1 native-only/);
  assert.doesNotMatch(p.stdout.text,/✓/);
});


test('local lint keeps unresolved draft gaps visible when the prose hash is stale', async t => {
  const setup=harbor(t,repo=>{
    declaration(repo,{kind:'partial',entries:[],draft_gaps:['Declare the operation schemas.'],limits:{max_steps:1,max_model_calls:1}});
    const file=join(repo,PLACE);writeFileSync(file,readFileSync(file,'utf8')+'\nChanged prose.\n');
  });
  const p=ports(setup);
  assert.equal(await runCheck({cwd:setup.repo,options:{'--lint':true,'--local':true,'--json':true}},p),4);
  assert.ok(JSON.parse(p.stdout.text).problems.some(problem=>problem.code==='interface-draft-incomplete'));
});
