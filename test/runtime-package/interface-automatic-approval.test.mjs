import '../helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { interfaceBlocks } from '../../src/runtime/runtime-preflight.mjs';
import { runAutomaticApproval, runInterfaceDraft } from '../../src/runtime-seam.mjs';
import { harbor, PLACE, sink, fakeRuntime, portsFor } from './runtime-fake.mjs';

function setupDraft(t,{nativePass=true,bulk=false}={}) {
  return harbor(t,repo=>{
    const file=join(repo,PLACE),text=readFileSync(file,'utf8'),block=interfaceBlocks(text)[0],iface=JSON.parse(block[1]);
    delete iface.status;delete iface.prose_sha256;
    iface.entries[0].result_schema.description=text.replace(block[0],'').replace(/^#{1,6}[^\n]*$/gm,'').replace(/None\.\s*$/,'').trim();
    writeFileSync(file,text.replace(block[0],'')+'\n## Public schema\n\n```json\n'+JSON.stringify(iface)+'\n```\n');
    const scenario=JSON.parse(readFileSync(join(repo,'tests/place-order.json'),'utf8'));
    scenario.criteria=scenario.criteria.slice(0,1);scenario.steps[0].checks=scenario.steps[0].checks.slice(0,1);
    writeFileSync(join(repo,'tests/place-order.json'),JSON.stringify(scenario));
    if(bulk) {
      writeFileSync(join(repo,'prompts/second.prompt.md'),readFileSync(file,'utf8'));
      const second=structuredClone(scenario);second.story_path='user_stories/second.md';second.steps[0].entry_path='prompts/second.prompt.md';
      writeFileSync(join(repo,'tests/second.json'),JSON.stringify(second));
      writeFileSync(join(repo,'user_stories/second.md'),'# Second order\n\n## Acceptance criteria\n\n1. '+scenario.criteria[0].text+'\n');
    }
    writeFileSync(join(repo,'user_stories/place-order.md'),'# Place an order\n\n## Acceptance criteria\n\n1. '+scenario.criteria[0].text+'\n');
    mkdirSync(join(repo,'src'),{recursive:true});
    writeFileSync(join(repo,'src/price.mjs'),'export const price = () => 900;\n');
    writeFileSync(join(repo,'tests/price.test.mjs'),`import assert from 'node:assert/strict';\nimport {price} from '../src/price.mjs';\nassert.equal(price(),${nativePass ? 900 : 901});\n`);
  });
}
async function draft(setup,{all=false,words=all?[]:[PLACE]}={}) {
  const stdout=sink(),stderr=sink();
  const code=await runInterfaceDraft({cwd:setup.repo,words,all,json:true},{stdout,stderr,env:{HOME:setup.home}});
  assert.equal(code,0,stderr.text+stdout.text);
}
async function auto(setup,ports={},tests='node --test tests/price.test.mjs',path=PLACE) {
  const output={stdout:sink(),stderr:sink(),interactive:false,env:{HOME:setup.home,PATH:process.env.PATH,PDD_STATE_DIR:setup.state},...ports};
  const code=await runAutomaticApproval({root:setup.repo,path,tests},output);
  return {code,out:output.stdout.text,err:output.stderr.text};
}
const status=setup=>JSON.parse(interfaceBlocks(readFileSync(join(setup.repo,PLACE),'utf8'))[0][1]).status;

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

test('automatic approval can process separately committed unchanged blocks from a bulk draft', async t => {
  const setup=setupDraft(t,{bulk:true});await draft(setup,{all:true});
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
