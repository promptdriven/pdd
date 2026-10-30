import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync, existsSync, realpathSync, chmodSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFile as callbackExec, execFileSync } from 'node:child_process';
import { promisify } from 'node:util';
import { stepDone } from '../src/workflow-runner.mjs';
import { inventoryModule } from './workflow-inventory-replay-helper.mjs';
import { codeLiteral as span } from './workflow-inventory-code-spans-oracle.mjs';
import { readRun, writeRun } from '../src/workflow-runs.mjs';

const exec = promisify(callbackExec);
const initial=`test('keep', () => {\nassert.equal(value, 1);\n});\ntest('gone', () => {});\n`;
const changed=`test('keep', () => {\nassert.equal(value, 2);\n});\ntest.todo('later');\n`;
// Git is never stubbed. Only network addressing for real push/ls-remote is
// routed to a disposable local bare repository; identity reads see GitHub.
function fixture(t,{workflow='small-change',opted=false,promptPr=false,before=initial}={}) {
  const directory=realpathSync(mkdtempSync(join(tmpdir(),'pdd-inventory-pr-')));t.after(()=>rmSync(directory,{recursive:true,force:true}));
  const root=join(directory,'checkout'),remote=join(directory,'remote.git');mkdirSync(root);
  const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8'}).trim();
  git('init','--bare','-q',remote);git('init','-q','-b','main');git('config','user.email','test@example.invalid');git('config','user.name','Inventory Test');
  git('remote','add','origin','https://github.com/example/project.git');mkdirSync(join(root,'test'));writeFileSync(join(root,'test/a.mjs'),before);git('add','.');git('commit','-qm','base');
  const baseSha=git('rev-parse','HEAD');git('push','-q',remote,'main');git('update-ref','refs/remotes/origin/main',baseSha);
  git('checkout','-qb','prompt');writeFileSync(join(root,'prompt.txt'),'published prompt\n');git('add','.');git('commit','-qm','prompt');const promptSha=git('rev-parse','HEAD');git('push','-q',remote,'prompt');git('update-ref','refs/remotes/origin/prompt',promptSha);
  git('checkout','-qb','topic');
  const commonDir=git('rev-parse','--path-format=absolute','--git-common-dir'),runDir=join(commonDir,'pdd/runs/17'),stateDir=join(directory,'state');
  const area={name:promptPr?'prompt-pr':'code',steps:['reproduce','scope','build','verify','review','formal'],optional:[],gate:'pr',...(promptPr?{then:'ask-code'}:{}),...(opted?{replay_evidence:'pdd.replay-evidence.v1'}:{})};
  const areas=workflow==='small-change'||promptPr?[area]:[{name:'prompt-pr',steps:['check'],optional:[],gate:'pr',then:'ask-code'},area];
  const run={runId:'inventory-run',workflow,repo:'example/project',number:17,issue:{number:17,title:'Inventory review',url:'https://github.com/example/project/issues/17'},root,sourceRoot:root,branch:'topic',baseBranch:'main',baseSha,commonDir,runDir,state:'running',areas,area:areas.length-1,done:Object.fromEntries(area.steps.filter(step=>step!=='formal').map(step=>[step,{summary:'completed'}])),chats:[],pr:workflow==='small-change'||promptPr?[]:[{stage:'prompt-pr',number:22,url:'https://github.com/example/project/pull/22',branch:'prompt',base:'main'}],...(workflow==='small-change'?{}:{prBase:'prompt'})};
  const f={root,remote,git,run,baseSha,promptSha,prs:[],events:[],edits:[],failCreate:false,failEdit:false};
  const ports={stateDir,env:{HOME:directory},now:()=>Date.now(),execFile:async(file,args,opts)=>{
    if(file==='git') {
      f.events.push({kind:'git',args:[...args]});
      const route=['push','ls-remote','fetch'].includes(args[0]);
      return exec('git',route?['-c',`url.${remote}.insteadOf=https://github.com/example/project.git`,...args]:args,{...opts,encoding:args[0]==='cat-file'?'buffer':'utf8'});
    }
    assert.equal(file,'gh');f.events.push({kind:'gh',args:[...args],...(args[1]==='edit'?{remote:git('--git-dir',remote,'rev-parse','refs/heads/topic'),body:opts.input}:{})});
    const flag=name=>args[args.indexOf(name)+1];
    if(args[0]==='repo')return {stdout:JSON.stringify({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'})};
    if(args[1]==='list')return {stdout:JSON.stringify(f.prs)};
    if(args[1]==='create') {
      if(f.failCreate)return {stdout:'',stderr:'GraphQL: temporarily denied (createPullRequest)',code:1};
      assert.equal(flag('--body-file'),'-');assert.equal(typeof opts.input,'string');
      const body=opts.input,headRefOid=git('rev-parse','HEAD');
      const pr={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid,body,isCrossRepository:false,headRepositoryOwner:{login:'example'},headRepository:{name:'project'},mergeCommit:null};
      f.prs.push(pr);return {stdout:pr.url};
    }
    if(args[1]==='edit') {
      f.editAttempts=(f.editAttempts??0)+1;
      if(f.failEdit || f.editAttempts===f.failEditAt)return {stdout:'',stderr:'GraphQL: body update denied',code:1};
      assert.equal(flag('--body-file'),'-');assert.equal(typeof opts.input,'string');
      const body=opts.input;f.edits.push(body);f.prs[0].body=body;return {stdout:''};
    }
    assert.fail(`Unexpected gh ${args.join(' ')}`);
  }};
  writeRun(run,ports);f.ports=ports;f.record=()=>readRun(runDir);
  f.done=(summary='formal done')=>{
    const rows=summary.split('\n');
    for(const [step,select] of [['review',r=>r.startsWith('Review:')],['verify',r=>/^(?:Not fixed yet:|Proof \()/.test(r)],[workflow==='bug'?'reproduce':'scope',r=>/^(?:Defect:|Not caught because:)/.test(r)]]){
      const text=rows.filter(select).join('\n');if(text){const path=join(runDir,step+'.md');const warning=step==='verify'&&existsSync(path)?readFileSync(path,'utf8').split('\n').filter(row=>row.startsWith('✗ ')).join('\n'):'';writeFileSync(path,[warning,text].filter(Boolean).join('\n'));}
    }
    return stepDone({cwd:root,step:'formal',summary},ports);
  };
  f.remoteHead=()=>git('--git-dir',remote,'rev-parse','refs/heads/topic');
  return f;
}
function artifact(f){const path=join(f.run.runDir,'test-inventory.json');assert.ok(existsSync(path),'publication saved its inventory artifact');return JSON.parse(readFileSync(path,'utf8'));}
function missingProofBeforeInventory(body, proof = 'Old-code proof: not run.') {
  assert.equal(body.split('\n')[0], proof);
  const proofAt=body.indexOf(proof),inventoryAt=body.indexOf('Tests vs base:'),issueAt=body.search(/\n(?:Closes|Refs) #17\n/);
  assert.ok(proofAt<inventoryAt && inventoryAt<issueAt,'machine proof precedes complete inventory, then issue prose');
}
function proveCurrent(f,report) {
  const head=f.git('rev-parse','HEAD');assert.equal(report.baseSha,f.baseSha);assert.equal(report.headSha,head);assert.equal(f.remoteHead(),head);
  const prefix=`Test inventory commits: ${f.baseSha.slice(0,7)} → ${head.slice(0,7)}.`;
  if(f.run.areas.at(-1).replay_evidence) {
    assert.ok(f.prs[0].body.includes(prefix));
    const body=f.prs[0].body;assert.ok(body.indexOf('Old-code proof:')<body.indexOf('Tests vs base:')&&body.indexOf('Test inventory commits:')<body.indexOf('Code replay'));
  } else missingProofBeforeInventory(f.prs[0].body);
  assert.ok(f.prs[0].body.includes(report.text.trimEnd()+'\n'+prefix));
  assert.deepEqual(Object.keys(f.record().testInventory).sort(),['baseSha','headSha','saved','text']);
  assert.deepEqual(f.record().testInventory,{text:report.text,baseSha:report.baseSha,headSha:head,saved:report.saved});
  assert.equal((f.prs[0].body.match(/<!-- pdd-workflow:/g)??[]).length,1);
}

test('small-change publication commits first, pushes to a real bare remote and places current inventory before runtime evidence',async t=>{
  const f=fixture(t);writeFileSync(join(f.root,'test/a.mjs'),changed);
  const result=await f.done('Runtime check: ✓ 1/1 criteria');assert.equal(result.exitCode,0,result.message);
  assert.match(f.prs[0].body,/Tests vs base: "test\/a.mjs" 2 → 2 tests. Removed: 1 \(`"gone"`\)/);
  const inventoryAt=f.prs[0].body.indexOf('Test inventory commits:'),runtimeAt=f.prs[0].body.indexOf('Runtime check:');
  assert.ok(inventoryAt>=0&&inventoryAt<runtimeAt);
  proveCurrent(f,artifact(f));assert.equal(artifact(f).saved,true);assert.ok(artifact(f).details.includes('assert.equal(value, 1)'));
});

test('feature and bug stacked code PRs compare the fetched original run branch merge-base, then refresh on every existing PR update without replay opt-in',async t=>{
  for(const workflow of ['feature','bug']) {
    const f=fixture(t,{workflow});writeFileSync(join(f.root,'test/a.mjs'),changed);assert.equal((await f.done()).exitCode,0);
    assert.equal(f.prs[0].baseRefName,'prompt');proveCurrent(f,artifact(f));assert.notEqual(artifact(f).baseSha,f.promptSha);
    const oldHead=artifact(f).headSha;writeFileSync(join(f.root,'test/a.mjs'),`test('keep', () => assert.ok(value));\n`);
    f.events=[];const result=await f.done();assert.equal(result.exitCode,0,result.message);assert.equal(f.edits.length,2);
    const edits=f.events.filter(e=>e.kind==='gh'&&e.args[1]==='edit'),push=f.events.findIndex(e=>e.kind==='git'&&e.args[0]==='push');
    assert.ok(f.events.indexOf(edits[0])<push&&push<f.events.indexOf(edits[1]));
    assert.equal(edits[0].remote,oldHead);assert.equal(edits[1].remote,artifact(f).headSha);
    assert.match(edits[0].body,/Old-code proof: publication-pending/);assert.doesNotMatch(edits[0].body,/Old-code proof: ✓/);
    assert.notEqual(artifact(f).headSha,oldHead);proveCurrent(f,artifact(f));assert.match(f.prs[0].body,/2 → 1 tests/);
    const pushes=f.events.filter(e=>e.kind==='git'&&e.args[0]==='push');assert.equal(pushes.at(-1).args[2],`${artifact(f).headSha}:refs/heads/topic`);
  }
});

test('failed create retry recollects from its newly committed SHA and preserves report-only unavailable comparisons',async t=>{
  const f=fixture(t);f.failCreate=true;writeFileSync(join(f.root,'test/a.mjs'),changed);
  const first=await f.done();assert.equal(first.exitCode,1);assert.equal(f.prs.length,0);
  const oldHead=f.git('rev-parse','HEAD');f.failCreate=false;writeFileSync(join(f.root,'test/a.mjs'),`test.todo('next');\n`);
  const result=await f.done();assert.equal(result.exitCode,0,result.message);assert.notEqual(f.git('rev-parse','HEAD'),oldHead);proveCurrent(f,artifact(f));
  f.git('--git-dir',f.remote,'update-ref','-d','refs/heads/main');writeFileSync(join(f.root,'test/a.mjs'),`test('again', () => {});\n`);
  assert.equal((await f.done()).exitCode,0);assert.equal(artifact(f).available,false);assert.match(f.prs[0].body,/Tests vs base: unavailable/);assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));
});

test('combined changed-source pending failure stops push, preserves the old body, and retry converges inventory and remote',async t=>{
  const f=fixture(t);writeFileSync(join(f.root,'test/a.mjs'),changed);assert.equal((await f.done()).exitCode,0);
  const previous=f.prs[0].body,oldHead=f.remoteHead();f.failEdit=true;f.events=[];writeFileSync(join(f.root,'test/a.mjs'),`test('third', () => {});\n`);
  const result=await f.done();assert.equal(result.exitCode,1,result.message);assert.equal(f.prs[0].body,previous);assert.ok(previous.includes(oldHead.slice(0,7)));
  assert.match(result.message,/body update denied/);assert.match(result.message,/No source was pushed/);assert.match(result.message,/run done formal again/);
  assert.equal(f.events.some(e=>e.kind==='git'&&e.args[0]==='push'),false);assert.equal(f.remoteHead(),oldHead);
  assert.equal(artifact(f).headSha,f.git('rev-parse','HEAD'));assert.notEqual(artifact(f).headSha,f.remoteHead());
  f.failEdit=false;assert.equal((await f.done()).exitCode,0);proveCurrent(f,artifact(f));
});

test('combined unchanged-source inventory-only refresh failure warns and retains its previous visible report',async t=>{
  const f=fixture(t);writeFileSync(join(f.root,'test/a.mjs'),changed);assert.equal((await f.done()).exitCode,0);
  const previous=f.prs[0].body,oldHead=f.remoteHead();f.failEdit=true;f.events=[];
  const result=await f.done();assert.equal(result.exitCode,0,result.message);assert.equal(f.prs[0].body,previous);assert.equal(f.remoteHead(),oldHead);
  assert.match(result.message,/still shows the previous inventory/);assert.ok(result.message.includes(`${f.baseSha.slice(0,7)} → ${f.git('rev-parse','HEAD').slice(0,7)}`));
  assert.match(result.message,/was saved locally/);assert.match(result.message,/body update denied/);assert.match(result.message,/run done formal again/);
  assert.equal(f.events.filter(e=>e.kind==='gh'&&e.args[1]==='edit').length,1);assert.equal(artifact(f).headSha,f.remoteHead());
  f.failEdit=false;assert.equal((await f.done()).exitCode,0);proveCurrent(f,artifact(f));
});

test('combined non-opted final edit failure leaves real pushed source publication-pending',async t=>{
  const f=fixture(t);writeFileSync(join(f.root,'test/a.mjs'),changed);assert.equal((await f.done()).exitCode,0);
  const before=f.remoteHead();f.events=[];f.failEditAt=(f.editAttempts??0)+2;writeFileSync(join(f.root,'test/a.mjs'),`test('last', () => {});\n`);
  const result=await f.done();assert.equal(result.exitCode,1);assert.match(result.message,/body update denied/);assert.match(result.message,/Source was pushed; the PR stays publication-pending/);assert.match(result.message,/run done formal again/);
  assert.notEqual(f.remoteHead(),before);assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));assert.match(f.prs[0].body,/Old-code proof: publication-pending/);assert.doesNotMatch(f.prs[0].body,/Old-code proof: ✓/);
  const edits=f.events.filter(e=>e.kind==='gh'&&e.args[1]==='edit');assert.equal(edits.length,2);assert.equal(edits[0].remote,before);assert.equal(edits[1].remote,f.remoteHead());
  assert.equal(artifact(f).headSha,f.remoteHead());
});

test('artifact write failure is disclosed without stopping create or changed-source publication, while a separate pending failure stops push',async t=>{
  const f=fixture(t);mkdirSync(join(f.run.runDir,'test-inventory.json'));writeFileSync(join(f.root,'test/a.mjs'),changed);
  const created=await f.done();assert.equal(created.exitCode,0,created.message);assert.match(created.message,/full test inventory report was not saved/);
  assert.match(f.prs[0].body,/full test inventory report was not saved/);assert.ok(f.prs[0].body.includes('Tests vs base:'));assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));
  writeFileSync(join(f.root,'test/a.mjs'),`test.todo('unsaved');\n`);const updated=await f.done();assert.equal(updated.exitCode,0,updated.message);
  assert.match(updated.message,/full test inventory report was not saved/);assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));assert.equal(f.record().testInventory.saved,false);missingProofBeforeInventory(f.prs[0].body);
  const before=f.remoteHead();f.failEdit=true;f.events=[];writeFileSync(join(f.root,'test/a.mjs'),`test.todo('held');\n`);const failed=await f.done();assert.equal(failed.exitCode,1);assert.match(failed.message,/body update denied/);assert.match(failed.message,/No source was pushed/);assert.equal(f.remoteHead(),before);assert.equal(f.events.some(e=>e.kind==='git'&&e.args[0]==='push'),false);assert.equal(f.record().testInventory.saved,false);
});

test('replay-enabled updates retain pending-before-push and final-edit failures while including the current inventory',async t=>{
  const f=fixture(t,{workflow:'feature',opted:true});writeFileSync(join(f.root,'test/a.mjs'),changed);
  assert.equal((await f.done()).exitCode,0);assert.ok(f.prs[0].body.includes('Test inventory commits:'));const replayAt=f.prs[0].body.indexOf('Code replay'),inventoryAt=f.prs[0].body.indexOf('Test inventory commits:');assert.ok(replayAt>=0&&inventoryAt<replayAt);
  f.events=[];writeFileSync(join(f.root,'test/a.mjs'),`test('last', () => {});\n`);assert.equal((await f.done()).exitCode,0);proveCurrent(f,artifact(f));
  const edits=f.events.map((e,i)=>e.kind==='gh'&&e.args[1]==='edit'?i:-1).filter(i=>i>=0),push=f.events.findIndex(e=>e.kind==='git'&&e.args[0]==='push');assert.ok(edits[0]<push&&push<edits[1]);
  f.failEdit=true;writeFileSync(join(f.root,'test/a.mjs'),`test('held', () => {});\n`);const before=f.remoteHead(),failed=await f.done();assert.equal(failed.exitCode,1);assert.equal(f.remoteHead(),before);assert.match(failed.message,/No source was pushed/);
  f.failEdit=false;f.failEditAt=f.editAttempts+2;const finalFailed=await f.done();assert.equal(finalFailed.exitCode,1);assert.notEqual(f.remoteHead(),before);assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));assert.match(finalFailed.message,/Source was pushed; the PR stays publication-pending/);assert.ok(f.prs[0].body.includes('Publication pending;'));assert.ok(f.prs[0].body.includes('Code replay: BLOCKED'));
});

test('an unavailable comparison cannot block first publication and is visibly unavailable in its body and artifact',async t=>{
  const f=fixture(t,{workflow:'feature'});f.git('--git-dir',f.remote,'update-ref','-d','refs/heads/main');writeFileSync(join(f.root,'test/a.mjs'),changed);
  const result=await f.done();assert.equal(result.exitCode,0,result.message);assert.match(f.prs[0].body,/Tests vs base: unavailable/);
  assert.equal(artifact(f).available,false);assert.equal(artifact(f).baseSha,'');assert.ok(f.prs[0].body.includes('Test inventory commits: unavailable.'));assert.equal(f.record().baseSha,f.baseSha);assert.equal(artifact(f).headSha,f.remoteHead());
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

test('revision fetched original base merge excludes upstream changes while retaining stacked PR1 tests and immutable start SHA',async t=>{
  const f=fixture(t,{workflow:'feature'});
  // Put a test in PR 1 that must remain visible even though PR 2 targets it.
  f.git('checkout','prompt');writeFileSync(join(f.root,'test/prompt.mjs'),`test('from PR1', () => {});\n`);f.git('add','.');f.git('commit','-qm','PR1 tests');f.git('push','-q',f.remote,'prompt');
  f.git('checkout','topic');f.git('merge','--no-edit','prompt');
  // Advance the original base outside this topic, then merge it.
  f.git('checkout','main');writeFileSync(join(f.root,'test/upstream.mjs'),`test('upstream only', () => {});\n`);f.git('add','.');f.git('commit','-qm','upstream tests');const upstream=f.git('rev-parse','HEAD');f.git('push','-q',f.remote,'main');
  f.git('checkout','topic');f.git('merge','--no-edit','main');writeFileSync(join(f.root,'test/a.mjs'),changed);
  // A stale tracking ref must not supply the comparison, and PR1 is not its base.
  f.git('update-ref','refs/remotes/origin/main',f.baseSha);
  const result=await f.done();assert.equal(result.exitCode,0,result.message);
  const report=artifact(f);assert.equal(report.baseSha,upstream);assert.equal(report.headSha,f.remoteHead());assert.equal(f.prs[0].baseRefName,'prompt');
  assert.ok(report.details.includes('"test/prompt.mjs" 0 → 1 tests. Removed: none.'));
  assert.ok(!report.details.includes('test/upstream.mjs'));missingProofBeforeInventory(f.prs[0].body);
  assert.equal(f.record().baseSha,f.baseSha);assert.equal(f.record().baseBranch,'main');assert.equal(f.record().prBase,'prompt');
  assert.ok(f.events.some(event=>event.kind==='git'&&event.args[0]==='fetch'&&event.args[2]==='refs/heads/main:refs/remotes/origin/main'));
});

test('revision failed base fetch never reuses a stale tracking ref and still refreshes the informational PR body',async t=>{
  const f=fixture(t);writeFileSync(join(f.root,'test/a.mjs'),changed);assert.equal((await f.done()).exitCode,0);
  f.git('--git-dir',f.remote,'update-ref','-d','refs/heads/main');
  assert.equal(f.git('rev-parse','refs/remotes/origin/main'),f.baseSha);
  writeFileSync(join(f.root,'test/a.mjs'),`test('current', () => {});\n`);
  const result=await f.done();assert.equal(result.exitCode,0,result.message);
  const report=artifact(f);assert.equal(report.available,false);assert.equal(report.baseSha,'');assert.equal(report.headSha,f.remoteHead());
  missingProofBeforeInventory(f.prs[0].body,'Old-code proof: unavailable.');assert.match(f.prs[0].body,/^Tests vs base: unavailable/m);assert.ok(f.prs[0].body.includes('Test inventory commits: unavailable.'));
  assert.equal(f.record().baseSha,f.baseSha);assert.deepEqual(Object.keys(f.record().testInventory).sort(),['baseSha','headSha','saved','text']);
});

test('revision unrelated fetched base reports merge-base failure without a saved-base fallback or publication gate',async t=>{
  const f=fixture(t,{workflow:'feature'});
  f.git('checkout','--orphan','new-base');f.git('rm','-rf','.');writeFileSync(join(f.root,'new.txt'),'independent');f.git('add','.');f.git('commit','-qm','independent base');
  const independent=f.git('rev-parse','HEAD');f.git('push','-q',f.remote,`${independent}:refs/heads/different`);
  // This fixture selected different as its original base; its saved start SHA is
  // deliberately still reachable from topic, so a fallback would look healthy.
  f.git('checkout','topic');const run=f.record();run.baseBranch='different';writeRun(run,f.ports);
  writeFileSync(join(f.root,'test/a.mjs'),changed);const result=await f.done();assert.equal(result.exitCode,0,result.message);
  assert.equal(artifact(f).available,false);assert.equal(artifact(f).baseSha,'');assert.equal(artifact(f).headSha,f.remoteHead());
  assert.ok(f.prs[0].body.includes('Test inventory commits: unavailable.'));assert.equal(f.record().baseSha,f.baseSha);
});

async function defaultProcessProof(t, hostile = false, markers = false) {
  if (hostile || markers) await inventoryModule();
  const removed='  `<!-- pdd-workflow:removed:code --> pdd-workflow:repeat:code``  ';
  const kept='pdd-workflow:kept:code PDD-workflow:upper:code';
  const suite='pdd-workflow:suite:code pdd-workflow:again:code';
  const oldLine='  assert.equal(value, "pdd-workflow:old:code pdd-workflow:again:code"); // \t\u0001\u202e  \r';
  const nextLine='  assert.equal(value, "pdd-workflow:new:code pdd-workflow:again:code"); // ` `` @octocat Closes #17 &<>|:  \r';
  const skipLine='  t.skip("pdd-workflow:skip:code pdd-workflow:again:code"); // \r';
  const suiteLine=`describe.skip(${JSON.stringify(suite)}, () => {});`;
  const markerBefore=`test(${JSON.stringify(removed)}, () => {});\ntest(${JSON.stringify(kept)}, () => {\n${oldLine}\n});\ndescribe(${JSON.stringify(suite)}, () => {});\n`;
  const markerAfter=`test(${JSON.stringify(kept)}, () => {\n${nextLine}\n${skipLine}\n});\n${suiteLine}\n`;
  const f=fixture(t,{before:initial+(markers?markerBefore:'')}),commands=join(f.root,'..','commands'),state=join(f.root,'..','gh-state.json');mkdirSync(commands);
  const writeExecutable=(name,source)=>{const path=join(commands,name);writeFileSync(path,`#!${process.execPath}\n${source}`);chmodSync(path,0o755);};
  // This executable only routes network addresses; every Git result is produced
  // by /usr/bin/git over the fixture's real checkout and bare remote.
  writeExecutable('git',`
const {spawnSync}=require('node:child_process');
const args=process.argv.slice(2),route=['push','ls-remote','fetch'].includes(args[0]);
const reply=spawnSync('/usr/bin/git',route?['-c',${JSON.stringify(`url.${f.remote}.insteadOf=https://github.com/example/project.git`)},...args]:args,{stdio:'inherit'});
process.exit(reply.status??1);
`);
  writeFileSync(state,JSON.stringify({prs:[],bodies:[]}));
  writeExecutable('gh',`
const fs=require('node:fs'),{execFileSync}=require('node:child_process');
const path=${JSON.stringify(state)},s=JSON.parse(fs.readFileSync(path,'utf8')),args=process.argv.slice(2),flag=n=>args[args.indexOf(n)+1];
const save=()=>fs.writeFileSync(path,JSON.stringify(s));
if(args[0]==='repo')process.stdout.write(JSON.stringify({nameWithOwner:'example/project',defaultBranchRef:{name:'main'},url:'https://github.com/example/project'}));
else if(args[1]==='list')process.stdout.write(JSON.stringify(s.prs));
else if(args[1]==='create'||args[1]==='edit'){
  if(flag('--body-file')!=='-')throw Error('body must come from stdin');
  const body=fs.readFileSync(0,'utf8');s.bodies.push({action:args[1],body,source:flag('--body-file'),remote:execFileSync('/usr/bin/git',['--git-dir',${JSON.stringify(f.remote)},'rev-parse','refs/heads/topic'],{encoding:'utf8'}).trim()});
  if(args[1]==='create'){
    const pr={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:flag('--head'),baseRefName:flag('--base'),headRefOid:execFileSync('/usr/bin/git',['rev-parse','HEAD'],{encoding:'utf8'}).trim(),body,isCrossRepository:false,headRepositoryOwner:{login:'example'},headRepository:{name:'project'},mergeCommit:null};
    s.prs.push(pr);process.stdout.write(pr.url);
  }else s.prs[0].body=body;
  save();
}else throw Error('unexpected gh operation: '+args.join(' '));
`);
  const moduleUrl=new URL('../src/workflow-runner.mjs',import.meta.url).href;
  const driver=`const {stepDone}=await import(${JSON.stringify(moduleUrl)});const result=await stepDone({cwd:${JSON.stringify(f.root)},step:'formal',summary:'native stdin proof'},{stateDir:${JSON.stringify(f.ports.stateDir)}});console.log(JSON.stringify(result));`;
  const env={...process.env,PATH:`${commands}:${process.env.PATH}`};
  const name='  `@octocat #17 Closes #17``  ';
  const newAssertion='assert.equal(value, 2); // @octocat Closes #17 &<>|: ```  \r';
  const marker=`test.skip(${JSON.stringify(name)}, () => {}); // \t\u0001\u202e  \r`;
  const source=(hostile?changed.replace('assert.equal(value, 2);',newAssertion)+marker+'\n':changed)+(markers?markerAfter:'');
  writeFileSync(join(f.root,'test/a.mjs'),source);
  const created=JSON.parse((await exec(process.execPath,['--input-type=module','-e',driver],{env})).stdout);assert.equal(created.exitCode,0,created.message);
  let proof=JSON.parse(readFileSync(state,'utf8'));assert.equal(proof.bodies.length,1);assert.equal(proof.bodies[0].source,'-');missingProofBeforeInventory(proof.prs[0].body);
  assert.ok(proof.prs[0].body.includes('`"gone"`'));assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));
  if(hostile){
    assert.ok(proof.bodies[0].body.includes(span(newAssertion)));
    assert.ok(proof.bodies[0].body.includes(span(name)));
    assert.ok(proof.bodies[0].body.includes(span(marker)));
    if(process.env.PDD_INVENTORY_RENDER_EVIDENCE){
      mkdirSync(process.env.PDD_INVENTORY_RENDER_EVIDENCE,{recursive:true});
      writeFileSync(join(process.env.PDD_INVENTORY_RENDER_EVIDENCE,'default-process-body.md'),proof.bodies[0].body);
      writeFileSync(join(process.env.PDD_INVENTORY_RENDER_EVIDENCE,'default-process-inventory.json'),JSON.stringify(artifact(f),null,2)+'\n');
    }
  }
  if(markers){
    const body=proof.bodies[0].body,report=artifact(f);
    const expected=`Tests vs base: "test/a.mjs" 4 → 3 tests. Removed: 2 (${span('gone')}, ${span(removed)}).\nChanged assertions in kept tests: "test/a.mjs" ${span('keep')} ${span('assert.equal(value, 1);')} → ${span('assert.equal(value, 2);')}.\nChanged assertions in kept tests: "test/a.mjs" ${span(kept)} ${span(oldLine)} → ${span(nextLine)}.\nNew skips: "test/a.mjs" ${span('later')} ${span("test.todo('later');")}.\nNew skips: "test/a.mjs" ${span(kept)} ${span(skipLine)}.\nNew skips: "test/a.mjs" suite ${span(suite)} ${span(suiteLine)}.\nStatic inventory only; tests were not run.\n`;
    assert.equal(report.available,true);assert.equal(report.details,expected);assert.equal(report.text,expected);
    missingProofBeforeInventory(body);assert.ok(body.slice(body.indexOf('Tests vs base:')).startsWith(expected));
    assert.equal((body.match(/pdd-workflow:/g)??[]).length,1,'only the canonical raw ownership prefix survives');
    assert.equal((body.match(/<!-- pdd-workflow:inventory-run:code -->/g)??[]).length,1);
    assert.deepEqual([...report.details.matchAll(/(`+)("(?:[^"\\]|\\.)*")\1(?!`)/g)].map(match=>JSON.parse(match[2])),[
      'gone',removed,'keep','assert.equal(value, 1);','assert.equal(value, 2);',kept,oldLine,nextLine,'later',"test.todo('later');",kept,skipLine,suite,suiteLine,
    ]);
    if(process.env.PDD_INVENTORY_RENDER_EVIDENCE){
      mkdirSync(process.env.PDD_INVENTORY_RENDER_EVIDENCE,{recursive:true});
      writeFileSync(join(process.env.PDD_INVENTORY_RENDER_EVIDENCE,'default-process-marker-body.md'),body);
      writeFileSync(join(process.env.PDD_INVENTORY_RENDER_EVIDENCE,'default-process-marker-inventory.json'),JSON.stringify(report,null,2)+'\n');
    }
  }
  const before=f.remoteHead();writeFileSync(join(f.root,'test/a.mjs'),`test('current', () => {});\n`);
  const refreshed=JSON.parse((await exec(process.execPath,['--input-type=module','-e',driver],{env})).stdout);assert.equal(refreshed.exitCode,0,refreshed.message);
  proof=JSON.parse(readFileSync(state,'utf8'));assert.deepEqual(proof.bodies.map(row=>row.action),['create','edit','edit']);
  assert.equal(proof.bodies[1].source,'-');assert.equal(proof.bodies[2].source,'-');assert.match(proof.bodies[1].body,/Old-code proof: publication-pending/);assert.doesNotMatch(proof.bodies[1].body,/Old-code proof: ✓/);assert.equal(proof.bodies[1].remote,before);assert.equal(proof.bodies[2].remote,f.remoteHead());missingProofBeforeInventory(proof.bodies[2].body);
  assert.ok(proof.bodies[2].body.includes(`Test inventory commits: ${f.baseSha.slice(0,7)} → ${f.remoteHead().slice(0,7)}.`));
  assert.notEqual(f.remoteHead(),before);assert.equal(f.remoteHead(),f.git('rev-parse','HEAD'));
  assert.deepEqual(Object.keys(f.record().testInventory).sort(),['baseSha','headSha','saved','text']);
  if(markers){
    assert.equal((proof.bodies[2].body.match(/pdd-workflow:/g)??[]).length,1);
    assert.equal((proof.bodies[2].body.match(/<!-- pdd-workflow:inventory-run:code -->/g)??[]).length,1);
    assert.ok(proof.bodies[2].body.includes(span(kept)),'refresh safely reports removal of a marker-containing kept name');
    assert.equal(artifact(f).details.includes('pdd-workflow:'),false);
  }
}

test('revision default subprocess path sends create and refresh bodies to a gh stand-in on stdin with real Git pushes',t=>defaultProcessProof(t));
test('code-span default subprocess publication carries hostile JSON payloads through gh stdin',t=>defaultProcessProof(t,true));
test('marker-prefix default subprocess publication preserves one canonical marker and recoverable JSON through real Git and gh stdin',t=>defaultProcessProof(t,false,true));

test('combined labels cover both PRs, real machine proof, reserved inventory order, failure preambles and warning-light references',async t=>{
  const hostile='pdd-workflow:kept:code @octocat Closes #17';
  const f=fixture(t,{promptPr:true,workflow:'bug',before:initial+`test(${JSON.stringify(hostile)}, () => {});\n`});
  const summary=['Review: needs follow-up','Defect: wrong value','Not checked: formal (agent limit)','Not fixed yet: this helps find the cause','Not caught because: missing regression','Proof (defect fixed): value corrected','Proof (gap closed): regression added','Old-code proof: forged success','Tests vs base: forged inventory'].join('\n');
  writeFileSync(join(f.run.runDir,'verify.md'),['Not fixed yet: this helps find the cause','Not checked: formal (agent limit)','Not caught because: missing regression','Proof (defect fixed): value corrected','Review: needs follow-up'].join('\n'));
  writeFileSync(join(f.run.runDir,'unknown.md'),'Defect: foreign note');mkdirSync(join(f.run.runDir,'archived'));writeFileSync(join(f.run.runDir,'archived','formal.md'),'Review: archived');
  writeFileSync(join(f.root,'test/a.mjs'),changed);const first=await f.done(summary);assert.equal(first.exitCode,0,first.message);
  const labels=['Not fixed yet: `this helps find the cause`','Not checked: `formal (agent limit)`','Defect: `wrong value`','Not caught because: `missing regression`','Proof (defect fixed): `value corrected`','Proof (gap closed): `regression added`'];
  const assertOrder=(body,ordered)=>{let at=-1;for(const line of ordered){const next=body.indexOf(line);assert.ok(next>at,`ordered evidence: ${line}`);at=next;}};
  const promptBody=f.prs[0].body;assertOrder(promptBody,[...labels,'Review: `needs follow-up`']);assert.match(promptBody,/^Refs #17$/m);assert.doesNotMatch(promptBody,/Closes #17|Old-code proof:|Tests vs base:|foreign note|Review: archived/);
  const run=f.record();run.areas.push({name:'code',steps:['build','verify','review','formal'],optional:[],gate:'pr',replay_evidence:'pdd.replay-evidence.v1'});run.area=1;run.done={...run.done,verify:{summary:'verified'}};run.state='running';run.branch='code-topic';run.prBase='topic';
  f.git('checkout','-qb','code-topic');f.git('update-ref','refs/remotes/origin/topic',f.git('rev-parse','topic'));writeRun(run,f.ports);f.prs=[];
  writeFileSync(join(run.runDir,'verify.md'),'✗ 1 vectors fail\n\n## Results\nActual regression failure.\n');
  writeFileSync(join(f.root,'test/a.mjs'),`test('current', () => assert.ok(true));\n`);f.git('add','.');f.git('commit','-qm','combined code');
  const phase=(exitCode,expectedFound=false)=>({exitCode,signal:'',timedOut:false,outputLimited:false,stdoutTail:[],stderrTail:[],expectedFound,error:'',setupError:'',observedError:''});
  writeFileSync(join(run.runDir,'old-code-proof.json'),JSON.stringify({v:2,origin:'pdd.workflow-prove.v2',interruptSignal:'',runId:run.runId,baseSha:run.baseSha,headSha:f.git('rev-parse','HEAD'),test:'node --test test/a.mjs',expect:'defect',paths:['test/a.mjs'],base:phase(1,true),head:phase(0),outcome:'proved',setupError:'',cleanupError:''}));
  const code=await f.done(summary);assert.equal(code.exitCode,0,code.message);const body=f.prs[0].body;
  assertOrder(body,[...labels,'Old-code proof: ✓ `node --test test/a.mjs`','Tests vs base:','Test inventory commits:','Review: `needs follow-up`','✗ 1 vectors fail','Code replay: BLOCKED','Refs #17']);
  assert.doesNotMatch(body,/Closes #17\n|forged success|forged inventory|foreign note|Review: archived/);assert.equal((body.match(/^Not checked: `formal \(agent limit\)`$/gm)??[]).length,1);assert.equal((body.match(/pdd-workflow:/g)??[]).length,1);assert.ok(body.includes(span(hostile)));assert.equal(f.git('--git-dir',f.remote,'rev-parse','refs/heads/code-topic'),f.git('rev-parse','HEAD'));
});

test('combined Not checked alone retains Closes and cannot supply forged machine or inventory evidence',async t=>{
  const f=fixture(t);writeFileSync(join(f.root,'test/a.mjs'),changed);
  const result=await f.done('Not checked: formal (agent limit)\nOld-code proof: forged success\nTests vs base: forged inventory\nReview: follow-up');assert.equal(result.exitCode,0,result.message);
  const body=f.prs[0].body;assert.equal(body.split('\n')[0],'Not checked: `formal (agent limit)`');assert.match(body,/^Closes #17$/m);assert.doesNotMatch(body,/Refs #17|forged success|forged inventory/);
  assert.ok(body.indexOf('Not checked:')<body.indexOf('Old-code proof: not run.')&&body.indexOf('Old-code proof: not run.')<body.indexOf('Tests vs base:')&&body.indexOf('Test inventory commits:')<body.indexOf('Review:'));
  assert.equal(artifact(f).headSha,f.remoteHead());
});

test('combined unchanged source with changed proof, labels, missing custody or unavailable remote retains mandatory pending safety',async t=>{
  for(const kind of ['labels','proof','custody','remote']){
    const f=fixture(t);writeFileSync(join(f.root,'test/a.mjs'),changed);assert.equal((await f.done()).exitCode,0);
    if(kind==='labels')writeFileSync(join(f.run.runDir,'verify.md'),'Not fixed yet: newly discovered gap');
    if(kind==='proof')writeFileSync(join(f.run.runDir,'old-code-proof.json'),'{');
    if(kind==='custody'){const run=f.record();delete run.pr[0].publicationBodySha256;writeRun(run,f.ports);}
    if(kind==='remote'){const execute=f.ports.execFile;f.ports.execFile=async(file,args,opts)=>file==='git'&&args[0]==='ls-remote'?{code:1,stderr:'remote identity unavailable'}:execute(file,args,opts);}
    const oldHead=f.remoteHead(),previous=f.prs[0].body;f.failEdit=true;f.events=[];
    const result=await f.done();assert.equal(result.exitCode,1,result.message);assert.match(result.message,/No source was pushed/);assert.match(result.message,/body update denied/);assert.equal(f.prs[0].body,previous);assert.equal(f.remoteHead(),oldHead);assert.equal(f.events.some(e=>e.kind==='git'&&e.args[0]==='push'),false);
  }
});
