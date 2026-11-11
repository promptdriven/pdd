import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdirSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { runPdd } from '../src/pdd-cli.mjs';
import { runApprove } from '../src/prompt-approve.mjs';
import { interfaceBlocks } from '../src/runtime/runtime-preflight.mjs';
import { harbor, PLACE, sink, fakeRuntime, portsFor } from './runtime-fake.mjs';

function setupDraft(t,{nativePass=true,changeProse=false,scripts,broken=false,bulk=false}={}) {
  const setup=harbor(t,repo=>{
    const file=join(repo,PLACE),text=readFileSync(file,'utf8'),block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);
    delete iface.status;delete iface.prose_sha256;
    // Authored coverage evidence lets these safety tests reach their intended checks.
    // Keep the domain prose and every existing safety assertion.
    iface.entries[0].result_schema.description=text.replace(block[0],'').replace(/^#{1,6}[^\n]*$/gm,'').replace(/None\.\s*$/,'').trim();
    writeFileSync(file,text.replace(block[0],'')+'\n## Public schema\n\n```json\n'+JSON.stringify(iface)+'\n```\n');
    const scenario=JSON.parse(readFileSync(join(repo,'tests/place-order.json'),'utf8'));
    scenario.criteria=scenario.criteria.slice(0,1);scenario.steps[0].checks=scenario.steps[0].checks.slice(0,1);
    writeFileSync(join(repo,'tests/place-order.json'),JSON.stringify(scenario));
    if(broken) writeFileSync(join(repo,'tests/place-order.broken.json'),'{ invalid JSON');
    if(bulk) {
      writeFileSync(join(repo,'prompts/second.prompt.md'),readFileSync(file,'utf8'));
      const second=structuredClone(scenario);second.story_path='user_stories/second.md';second.steps[0].entry_path='prompts/second.prompt.md';
      writeFileSync(join(repo,'tests/second.json'),JSON.stringify(second));
      writeFileSync(join(repo,'user_stories/second.md'),'# Second order\n\n## Acceptance criteria\n\n1. '+scenario.criteria[0].text+'\n');
    }
    writeFileSync(join(repo,'user_stories/place-order.md'),'# Place an order\n\n## Acceptance criteria\n\n1. '+scenario.criteria[0].text+'\n');
    if(scripts) writeFileSync(join(repo,'package.json'),JSON.stringify({type:'module',scripts}));
    mkdirSync(join(repo,'src'),{recursive:true});
    writeFileSync(join(repo,'src/price.mjs'),'export const price = () => 900;\n');
    writeFileSync(join(repo,'tests/price.test.mjs'),`import assert from 'node:assert/strict';\nimport {price} from '../src/price.mjs';\nassert.equal(price(),${nativePass ? 900 : 901});\n`);
  });
  if(changeProse) writeFileSync(join(setup.repo,PLACE),readFileSync(join(setup.repo,PLACE),'utf8')+'New pricing behavior.\n');
  return setup;
}
async function draft(setup,words=[PLACE]) {
  const stdout=sink(),stderr=sink();
  const code=await runPdd(['interface','draft',...words,'--json'],{cwd:setup.repo,stdout,stderr,env:{HOME:setup.home}});
  assert.equal(code,0,stderr.text+stdout.text);
}
async function auto(setup,ports={},tests='node --test tests/price.test.mjs',path=PLACE) {
  const output={stdout:sink(),stderr:sink(),interactive:false,env:{HOME:setup.home,PATH:process.env.PATH,PDD_STATE_DIR:setup.state},...ports};
  const code=await runApprove({cwd:setup.repo,words:[path],automatic:true,tests},output);
  return {code,out:output.stdout.text,err:output.stderr.text};
}
const status=setup=>JSON.parse(interfaceBlocks(readFileSync(join(setup.repo,PLACE),'utf8'))[0][1]).status;

test('automatic approval runs existing native tests and a full current prompt check and records both', async t => {
  const setup=setupDraft(t);await draft(setup);
  const fake=await fakeRuntime(t,(entry,server)=>server.normal(entry));
  const {ports}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  const result=await auto(setup,ports);
  assert.equal(result.code,0,result.err+result.out);
  assert.equal(status(setup),'approved');
  const journal=JSON.parse(readFileSync(join(setup.repo,'.git/pdd/approvals.json'),'utf8'));
  const evidence=journal.approvals[0];
  assert.equal(evidence.route,'automatic-check-pass');assert.equal(evidence.words,null);
  assert.equal(evidence.checks.native.exit_code,0);
  assert.equal(evidence.checks.native.command,'node --test tests/price.test.mjs');
  assert.equal(evidence.checks.prompt.rows[0].state,'passed');
  assert.equal(evidence.checks.prompt.rows[0].checks.total,1);
  assert.ok(evidence.checks.source['src/price.mjs']);
  assert.ok(fake.posts.some(entry=>entry.command==='check'));
});

test('automatic approval refuses failing native tests before any Runtime call', async t => {
  const setup=setupDraft(t,{nativePass:false});await draft(setup);
  const result=await auto(setup,{gh(){assert.fail('native failure must stop before sign-in');}});
  assert.equal(result.code,4);assert.match(result.err,/native tests/);
  assert.equal(status(setup),'draft');
  assert.equal(existsSync(join(setup.repo,'.git/pdd/approvals.json')),false);
});

test('automatic approval refuses new behavior, changed code, edited interfaces and strict mode', async t => {
  for(const mode of ['new-prose','code','interface','strict']) {
    const setup=setupDraft(t,{changeProse:mode==='new-prose'});await draft(setup);
    if(mode==='code') writeFileSync(join(setup.repo,'src/price.mjs'),'export const price=()=>901;\n');
    if(mode==='interface') {
      const file=join(setup.repo,PLACE),text=readFileSync(file,'utf8');
      writeFileSync(file,text.replace('"operation": "place_order"','"operation": "changed_operation"'));
    }
    if(mode==='strict') writeFileSync(join(setup.repo,'pdd.json'),'{"strict_approvals":true}');
    const result=await auto(setup,{gh(){assert.fail('ineligible drafts must not sign in');}});
    assert.equal(result.code,4,mode+': '+result.err);assert.equal(status(setup),'draft');
    assert.match(result.err,mode==='strict' ? /Strict/ : mode==='new-prose' ? /committed prompt|new behavior/ : mode==='code' ? /committed source/ : /draft changed/);
  }
});

test('automatic approval refuses an incomplete prompt pass and leaves the draft unchanged', async t => {
  const setup=setupDraft(t);await draft(setup);
  // Add a second current check before drafting would represent the committed existing test.
  // The fake returns zero observed checks, even though it labels the request passed.
  const fake=await fakeRuntime(t,(entry,server)=>{
    if(entry.command==='lint') return server.normal(entry);
    const id=entry.request?.requestId ?? entry.url.split('/').at(-1);
    return {status:200,json:server.check(id,'passed',[])};
  });
  const {ports}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  const result=await auto(setup,ports);
  assert.equal(result.code,4,result.err);assert.equal(status(setup),'draft');
  assert.match(result.err,/every current test/);
});

test('automatic approval rejects source changes made during a passing prompt check', async t => {
  const setup=setupDraft(t);await draft(setup);
  const fake=await fakeRuntime(t,(entry,server)=>{
    if(entry.command==='check') writeFileSync(join(setup.repo,'src/price.mjs'),'export const price=()=>901;\n');
    return server.normal(entry);
  });
  const {ports}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
  const result=await auto(setup,ports);
  assert.equal(result.code,4);assert.equal(status(setup),'draft');
  assert.match(result.err,/Source changed/);
});


test('automatic approval refuses source modules, build scripts and empty test commands', async t => {
  for(const command of ['node --test src/price.mjs','npm run build','npm test']) {
    const setup=setupDraft(t,{scripts:{build:'node src/price.mjs',test:'node src/price.mjs'}});await draft(setup);
    const result=await auto(setup,{gh(){assert.fail('non-tests must stop before sign-in');}},command);
    assert.equal(result.code,4,command+': '+result.err);
    assert.equal(status(setup),'draft');
    assert.match(result.err,command==='npm test' ? /TAP test run/ : /committed tests/);
  }
});


test('automatic approval refuses an unreadable test variant of an affected Story', async t => {
  const setup=setupDraft(t,{broken:true});await draft(setup);
  const result=await auto(setup,{gh(){assert.fail('incomplete Story inventory must not sign in');}});
  assert.equal(result.code,4,result.err);assert.equal(status(setup),'draft');
  assert.match(result.err,/complete existing prompt tests/);
});

test('automatic approval can process separately committed unchanged blocks from a bulk draft', async t => {
  const setup=setupDraft(t,{bulk:true});await draft(setup,['--all']);
  for(const args of [['add',PLACE,'prompts/second.prompt.md'],['-c','user.email=t@example.com','-c','user.name=t','commit','-qm','Draft interface metadata']]) {
    const result=spawnSync('git',args,{cwd:setup.repo,encoding:'utf8'});assert.equal(result.status,0,result.stderr);
  }
  const fake=await fakeRuntime(t,(entry,server)=>entry.command==='lint'
    ? {status:200,json:server.lint(entry.request.requestId,[PLACE,'prompts/second.prompt.md'].map(path=>({path,state:'approved',admission_state:'approved',interface:{calls:[]}})))}
    : server.normal(entry));
  for(const path of [PLACE,'prompts/second.prompt.md']) {
    const {ports}=portsFor({HOME:setup.home,PDD_STATE_DIR:setup.state,PDD_RUNTIME_URL:fake.origin});
    const result=await auto(setup,ports,'node --test tests/price.test.mjs',path);
    assert.equal(result.code,0,path+': '+result.err+result.out);
    assert.equal(JSON.parse(interfaceBlocks(readFileSync(join(setup.repo,path),'utf8'))[0][1]).status,'approved');
  }
  const journal=JSON.parse(readFileSync(join(setup.repo,'.git/pdd/approvals.json'),'utf8'));
  assert.equal(journal.approvals.length,2);
});
