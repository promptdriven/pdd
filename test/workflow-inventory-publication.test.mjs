import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { stepDone } from '../src/workflow-runner.mjs';
import { readRun, writeRun } from '../src/workflow-runs.mjs';

const exec = promisify(callbackExec);
const initial=`test('keep', () => {\nassert.equal(value, 1);\n});\ntest('gone', () => {});\n`;
const changed=`test('keep', () => {\nassert.equal(value, 2);\n});\ntest.todo('later');\n`;
// Git is never stubbed. Only network addressing for real push/ls-remote is
// routed to a disposable local bare repository; identity reads see GitHub.
function fixture(t,{workflow='small-change',opted=false,promptPr=false}={}) {
  const directory=mkdtempSync(join(tmpdir(),'pdd-inventory-pr-'));t.after(()=>rmSync(directory,{recursive:true,force:true}));
  const root=join(directory,'checkout'),remote=join(directory,'remote.git');mkdirSync(root);
  const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8'}).trim();
  git('init','--bare','-q',remote);git('init','-q','-b','main');git('config','user.email','test@example.invalid');git('config','user.name','Inventory Test');
  git('remote','add','origin','https://github.com/example/project.git');mkdirSync(join(root,'test'));writeFileSync(join(root,'test/a.mjs'),initial);git('add','.');git('commit','-qm','base');
  const baseSha=git('rev-parse','HEAD');git('push','-q',remote,'main');git('update-ref','refs/remotes/origin/main',baseSha);
  git('checkout','-qb','prompt');writeFileSync(join(root,'prompt.txt'),'published prompt\n');git('add','.');git('commit','-qm','prompt');const promptSha=git('rev-parse','HEAD');git('push','-q',remote,'prompt');git('update-ref','refs/remotes/origin/prompt',promptSha);
  git('checkout','-qb','topic');
  const commonDir=git('rev-parse','--path-format=absolute','--git-common-dir'),runDir=join(commonDir,'pdd/runs/17'),stateDir=join(directory,'state');
  const area={name:promptPr?'prompt-pr':'code',steps:['formal'],optional:[],gate:'pr',...(promptPr?{then:'ask-code'}:{}),...(opted?{replay_evidence:'pdd.replay-evidence.v1'}:{})};
  const areas=workflow==='small-change'?[area]:[{name:'prompt-pr',steps:['check'],optional:[],gate:'pr',then:'ask-code'},area];
  const run={runId:'inventory-run',workflow,repo:'example/project',number:17,issue:{number:17,title:'Inventory review',url:'https://github.com/example/project/issues/17'},root,sourceRoot:root,branch:'topic',baseBranch:'main',baseSha,commonDir,runDir,state:'running',areas,area:areas.length-1,done:{},chats:[],pr:workflow==='small-change'?[]:[{stage:'prompt-pr',number:22,url:'https://github.com/example/project/pull/22',branch:'prompt',base:'main'}],...(workflow==='small-change'?{}:{prBase:'prompt'})};
  const f={root,remote,git,run,baseSha,promptSha,prs:[],events:[],edits:[],failCreate:false,failEdit:false};
  const ports={stateDir,env:{HOME:directory},now:()=>Date.now(),execFile:async(file,args,opts)=>{
    if(file==='git') {
      f.events.push({kind:'git',args:[...args]});
      const route=['push','ls-remote','fetch'].includes(args[0]);
      return exec('git',route?['-c',`url.${remote}.insteadOf=https://github.com/example/project.git`,...args]:args,{...opts,encoding:args[0]==='cat-file'?'buffer':'utf8'});
    }
    assert.equal(file,'gh');f.events.push({kind:'gh',args:[...args]});
    const flag=name=>args[args.indexOf(name)+1];
    if(args[0]==='repo')return {stdout:JSON.stringify({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'})};
    if(args[1]==='list')return {stdout:JSON.stringify(f.prs)};
    if(args[1]==='create') {
      if(f.failCreate)return {stdout:'',stderr:'GraphQL: temporarily denied (createPullRequest)',code:1};
      const body=readFileSync(flag('--body-file'),'utf8'),headRefOid=git('rev-parse','HEAD');
      const pr={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid,body,isCrossRepository:false,headRepositoryOwner:{login:'example'},headRepository:{name:'project'},mergeCommit:null};
      f.prs.push(pr);return {stdout:pr.url};
    }
    if(args[1]==='edit') {
      f.editAttempts=(f.editAttempts??0)+1;
      if(f.failEdit || f.editAttempts===f.failEditAt)return {stdout:'',stderr:'GraphQL: body update denied',code:1};
      const body=readFileSync(flag('--body-file'),'utf8');f.edits.push(body);f.prs[0].body=body;return {stdout:''};
    }
    assert.fail(`Unexpected gh ${args.join(' ')}`);
  }};
  writeRun(run,ports);f.ports=ports;f.record=()=>readRun(runDir);
  f.done=(summary='formal done')=>stepDone({cwd:root,step:'formal',summary},ports);
  f.remoteHead=()=>git('--git-dir',remote,'rev-parse','refs/heads/topic');
  return f;
}
function artifact(f){const path=join(f.run.runDir,'test-inventory.json');assert.ok(existsSync(path),'publication saved its inventory artifact');return JSON.parse(readFileSync(path,'utf8'));}
function proveCurrent(f,report) {
  const head=f.git('rev-parse','HEAD');assert.equal(report.baseSha,f.baseSha);assert.equal(report.headSha,head);assert.equal(f.remoteHead(),head);
  const prefix=`Test inventory commits: ${f.baseSha} → ${head}.`;
  if(f.run.areas.at(-1).replay_evidence)assert.ok(f.prs[0].body.includes(prefix));
  else assert.equal(f.prs[0].body.split('\n')[0],prefix);
  assert.equal((f.prs[0].body.match(/<!-- pdd-workflow:/g)??[]).length,1);
}

test('small-change publication commits first, pushes to a real bare remote and places current inventory before runtime evidence',async t=>{
  const f=fixture(t);writeFileSync(join(f.root,'test/a.mjs'),changed);
  const result=await f.done('Runtime check: ✓ 1/1 criteria');assert.equal(result.exitCode,0,result.message);
  assert.match(f.prs[0].body,/Tests vs base: "test\/a.mjs" 2 → 2 tests. Removed: 1 \("gone"\)/);
  const inventoryAt=f.prs[0].body.indexOf('Test inventory commits:'),runtimeAt=f.prs[0].body.indexOf('Runtime check:');
  assert.ok(inventoryAt>=0&&inventoryAt<runtimeAt);
  proveCurrent(f,artifact(f));assert.equal(artifact(f).saved,true);assert.ok(artifact(f).details.includes('assert.equal(value, 1)'));
});

test('feature and bug stacked code PRs compare the saved run base, then refresh on every existing PR update without replay opt-in',async t=>{
  for(const workflow of ['feature','bug']) {
    const f=fixture(t,{workflow});writeFileSync(join(f.root,'test/a.mjs'),changed);assert.equal((await f.done()).exitCode,0);
    assert.equal(f.prs[0].baseRefName,'prompt');proveCurrent(f,artifact(f));assert.notEqual(artifact(f).baseSha,f.promptSha);
    const oldHead=artifact(f).headSha;writeFileSync(join(f.root,'test/a.mjs'),`test('keep', () => assert.ok(value));\n`);
    const result=await f.done();assert.equal(result.exitCode,0,result.message);assert.equal(f.edits.length,1);
    assert.notEqual(artifact(f).headSha,oldHead);proveCurrent(f,artifact(f));assert.match(f.prs[0].body,/2 → 1 tests/);
    const pushes=f.events.filter(e=>e.kind==='git'&&e.args[0]==='push');assert.equal(pushes.at(-1).args[2],`${artifact(f).headSha}:refs/heads/topic`);
  }
});

test('failed create retry recollects from its newly committed SHA and preserves report-only unavailable comparisons',async t=>{
  const f=fixture(t);f.failCreate=true;writeFileSync(join(f.root,'test/a.mjs'),changed);
  const first=await f.done();assert.equal(first.exitCode,1);assert.equal(f.prs.length,0);
  const oldHead=f.git('rev-parse','HEAD');f.failCreate=false;writeFileSync(join(f.root,'test/a.mjs'),`test.todo('next');\n`);
  const result=await f.done();assert.equal(result.exitCode,0,result.message);assert.notEqual(f.git('rev-parse','HEAD'),oldHead);proveCurrent(f,artifact(f));
  const run=f.record();run.baseSha='f'.repeat(40);writeRun(run,f.ports);writeFileSync(join(f.root,'test/a.mjs'),`test('again', () => {});\n`);
  assert.equal((await f.done()).exitCode,0);assert.equal(artifact(f).available,false);assert.match(f.prs[0].body,/Tests vs base: unavailable/);assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));
});

test('inventory update failure warns of the previous visible commit pair, while real push and local current report succeed',async t=>{
  const f=fixture(t);writeFileSync(join(f.root,'test/a.mjs'),changed);assert.equal((await f.done()).exitCode,0);
  const previous=f.prs[0].body,oldHead=f.git('rev-parse','HEAD');f.failEdit=true;writeFileSync(join(f.root,'test/a.mjs'),`test('third', () => {});\n`);
  const result=await f.done();assert.equal(result.exitCode,0,result.message);assert.equal(f.prs[0].body,previous);assert.ok(previous.includes(oldHead));
  assert.match(result.message,/still shows the previous inventory/);assert.ok(result.message.includes(`${f.baseSha} → ${f.git('rev-parse','HEAD')}`));
  assert.match(result.message,/was saved locally/);assert.match(result.message,/body update denied/);assert.match(result.message,/run done formal again/);
  assert.equal(artifact(f).headSha,f.remoteHead());
  f.failEdit=false;assert.equal((await f.done()).exitCode,0);proveCurrent(f,artifact(f));
});

test('artifact write failure is disclosed without stopping create or an informational body refresh',async t=>{
  const f=fixture(t);mkdirSync(join(f.run.runDir,'test-inventory.json'));writeFileSync(join(f.root,'test/a.mjs'),changed);
  const created=await f.done();assert.equal(created.exitCode,0,created.message);assert.match(created.message,/full test inventory report was not saved/);
  assert.match(f.prs[0].body,/full test inventory report was not saved/);assert.ok(f.prs[0].body.includes('Tests vs base:'));assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));
  f.failEdit=true;writeFileSync(join(f.root,'test/a.mjs'),`test.todo('unsaved');\n`);const updated=await f.done();assert.equal(updated.exitCode,0);
  assert.match(updated.message,/current full report was not saved locally/);assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));
});

test('replay-enabled updates retain pending-before-push and final-edit failures while including the current inventory',async t=>{
  const f=fixture(t,{workflow:'feature',opted:true});writeFileSync(join(f.root,'test/a.mjs'),changed);
  assert.equal((await f.done()).exitCode,0);assert.ok(f.prs[0].body.includes('Test inventory commits:'));const replayAt=f.prs[0].body.indexOf('Code replay'),inventoryAt=f.prs[0].body.indexOf('Test inventory commits:');assert.ok(replayAt>=0&&replayAt<inventoryAt);
  f.events=[];writeFileSync(join(f.root,'test/a.mjs'),`test('last', () => {});\n`);assert.equal((await f.done()).exitCode,0);proveCurrent(f,artifact(f));
  const edits=f.events.map((e,i)=>e.kind==='gh'&&e.args[1]==='edit'?i:-1).filter(i=>i>=0),push=f.events.findIndex(e=>e.kind==='git'&&e.args[0]==='push');assert.ok(edits[0]<push&&push<edits[1]);
  f.failEdit=true;writeFileSync(join(f.root,'test/a.mjs'),`test('held', () => {});\n`);const before=f.remoteHead(),failed=await f.done();assert.equal(failed.exitCode,1);assert.equal(f.remoteHead(),before);assert.match(failed.message,/No source was pushed/);
  f.failEdit=false;f.failEditAt=f.editAttempts+2;const finalFailed=await f.done();assert.equal(finalFailed.exitCode,1);assert.notEqual(f.remoteHead(),before);assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));assert.match(finalFailed.message,/Source was pushed; the PR stays publication-pending/);assert.ok(f.prs[0].body.includes('Publication pending;'));assert.ok(f.prs[0].body.includes('Code replay: BLOCKED'));
});

test('an unavailable comparison cannot block first publication and is visibly unavailable in its body and artifact',async t=>{
  const f=fixture(t);const run=f.record();run.baseSha='f'.repeat(40);writeRun(run,f.ports);writeFileSync(join(f.root,'test/a.mjs'),changed);
  const result=await f.done();assert.equal(result.exitCode,0,result.message);assert.match(f.prs[0].body,/Tests vs base: unavailable/);
  assert.equal(artifact(f).available,false);assert.equal(artifact(f).baseSha,'f'.repeat(40));assert.equal(artifact(f).headSha,f.remoteHead());
});

test('PR 1 omits inventory collection and its artifact while the later code PR includes the report',async t=>{
  const f=fixture(t,{promptPr:true});writeFileSync(join(f.root,'test/a.mjs'),changed);
  const first=await f.done();assert.equal(first.exitCode,0,first.message);assert.ok(!f.prs[0].body.includes('Test inventory commits:'));assert.equal(f.events.some(e=>e.kind==='git'&&e.args.includes('--name-status')),false);
  assert.equal(existsSync(join(f.run.runDir,'test-inventory.json')),false);
  // Promote the saved test fixture to its separately authorized code area;
  // no approval command is invoked by this test.
  const run=f.record();run.areas.push({name:'code',steps:['formal'],optional:[],gate:'pr'});run.area=1;run.done={};run.state='running';run.branch='code-topic';run.prBase='topic';f.git('checkout','-qb','code-topic');f.git('update-ref','refs/remotes/origin/topic',f.git('rev-parse','topic'));writeRun(run,f.ports);
  // The existing fake GitHub listing needs the same selectors as real gh.
  f.prs=[];writeFileSync(join(f.root,'test/a.mjs'),`test('code', () => {});\n`);
  const code=await f.done();assert.equal(code.exitCode,0,code.message);assert.match(f.prs[0].body,/Test inventory commits:/);assert.ok(existsSync(join(run.runDir,'test-inventory.json')));
});
