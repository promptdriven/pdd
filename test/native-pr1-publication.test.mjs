import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {nativeFixture,put,git} from './helpers/native-cli-fixture.mjs';
import {captureSource} from '../src/runtime-preflight.mjs';
import {prepareNativeEvidence} from '../src/workflow-results.mjs';
const {stepDone,approveRun,readEvidenceEligibility}=await import(process.env.PDD_NATIVE_RUNNER || new URL('../src/workflow-runner.mjs',import.meta.url).href);

// Git effects use a real local bare remote. GitHub and Herdr are synthetic actors.
async function publication(t) {
  const f=await nativeFixture(t,{workflow:'feature'}),remote=join(f.parent,'remote.git');
  git(f.root,'init','--bare','-q',remote);
  git(f.source,'push','-q',remote,'main:refs/heads/main');
  const route=`url.file://${remote}.insteadOf=https://github.com/example/project.git`;
  const original=f.ports.execFile;
  const state={pr:null,mode:null,pushes:0,edits:0},branch=f.readRun().branch;
  const remoteHead=()=>git(f.root,'--git-dir',remote,'rev-parse',`refs/heads/${branch}`);
  const ports={...f.ports,execFile:async(file,args,options)=>{
    if(file==='git'&&['push','fetch','ls-remote'].includes(args[0])) {
      if(args[0]==='push') {
        state.pushes++;
        if(state.mode==='push-failed')return {code:1,stderr:'Synthetic push refusal',stdout:''};
      }
      const result=spawnSync('git',['-c',route,...args],{cwd:options.cwd,encoding:'utf8',input:options.input});
      if(args[0]==='push'&&result.status===0&&state.pr)state.pr.headRefOid=remoteHead();
      return {stdout:result.stdout,stderr:result.stderr,code:result.status};
    }
    if(file==='gh'&&args[0]==='pr') {
      if(args[1]==='list') {
        if(state.mode==='unavailable')throw Error('Synthetic readback unavailable');
        const pr=structuredClone(state.pr);
        if(pr) {
          if(state.mode==='stale')pr.headRefOid=state.first;
          if(state.mode==='foreign')pr.headRepositoryOwner.login='another-owner';
          if(state.mode==='marker')pr.body='<!-- pdd-workflow:another-run:prompt-pr -->';
          if(state.mode==='different-pr'){pr.number=24;pr.url='https://github.com/example/project/pull/24';}
          if(state.mode==='missing-head')delete pr.headRefOid;
        }
        return {stdout:JSON.stringify(pr?[pr]:[])};
      }
      if(args[1]==='create') {
        const value=k=>args[args.indexOf(k)+1];
        state.pr={number:23,url:'https://github.com/example/project/pull/23',state:'OPEN',headRefName:value('--head'),baseRefName:value('--base'),headRefOid:remoteHead(),body:options.input,isCrossRepository:false,headRepository:{name:'project'},headRepositoryOwner:{login:'example'},mergeCommit:null};
        return {stdout:state.pr.url};
      }
      if(args[1]==='view')return {stdout:JSON.stringify(state.pr)};
      if(args[1]==='edit') {
        state.edits++;
        if(state.mode==='edit-failed')return {code:1,stderr:'Synthetic description refusal',stdout:''};
        state.pr.body=options.input;return {stdout:''};
      }
    }
    return original(file,args,options);
  }};
  for(const step of ['check','try']) {
    const r=await stepDone({step,summary:'Synthetic local publication regression.',cwd:f.root},ports);
    assert.equal(r.exitCode,0,r.message);
  }
  const r=await approveRun({ref:'17',said:'Approve synthetic local publication fixture.',cwd:f.root},ports);
  assert.equal(r.exitCode,0,r.message);
  const pr=()=>f.readRun().pr.find(pr=>pr.stage==='prompt-pr');
  state.first=remoteHead();assert.equal(pr().publishedHeadSha,state.first);
  const tests=['source.mjs',f.testPath,f.promptPath];
  const register=()=>f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','pr1','--test',...tests);
  const eligibility=sha=>readEvidenceEligibility({root:f.root,producerRoot:f.root,tests,source_sha256:sha,runId:f.readRun().runId,stage:'pr1'},{env:f.env});
  const update=()=>stepDone({step:'try',summary:'Synthetic local updated publication.',cwd:f.root},ports);
  return {...f,ports,state,pr,remoteHead,tests,register,eligibility,update};
}

test('normal initial and updated PR 1 publication admits its new canonical source through actual CLI',async t=>{
  const f=await publication(t);
  assert.equal(f.register().status,0);
  const first=f.readRun().evidenceAssociations.find(a=>a.stage==='pr1');
  assert.equal(f.eligibility(first.source_sha256).state,'eligible');
  put(f.root,'source.mjs','export const value=2;\n');
  const updated=await f.update();assert.equal(updated.exitCode,0,updated.message);
  const head=git(f.root,'rev-parse','HEAD');assert.notEqual(head,f.state.first);
  assert.equal(f.remoteHead(),head);
  assert.equal(f.pr().publishedHeadSha,head,'FINAL PUBLISHED PR1 HEAD MUST REFRESH BEFORE HISTORICAL ASSOCIATION');
  assert.notEqual(f.eligibility(first.source_sha256).state,'eligible','The superseded association cannot borrow the new anchor');
  const registered=f.register();assert.equal(registered.status,0,registered.stdout+registered.stderr);
  const association=f.readRun().evidenceAssociations.find(a=>a.stage==='pr1'&&a.sourceAnchor.head===head);
  assert.ok(association);
  const sha=captureSource(f.root,{tests:f.tests}).sha256;
  assert.equal(association.source_sha256,sha);
  assert.equal(f.eligibility(sha).state,'eligible');
  assert.equal(readFileSync(join(association.sourceAnchor.root,'source.mjs'),'utf8'),'export const value=2;\n');
  assert.equal(readFileSync(join(first.sourceAnchor.root,'source.mjs'),'utf8'),'export const value=1;\n','Prior frozen bytes stay intact');

  const dir=join(f.parent,'originals'),summaryFile=join(dir,'import.json');
  const save=(name,value)=>put(dir,name+'.json',value);
  const descriptor={schema:'pdd.native-evidence-import.v1',profileId:'native',storyPath:f.storyPath,originals:['report','source','selection','execution'].map(role=>({role,path:role+'.json'}))};
  const report={producer:'synthetic-test-runner',producerVersion:'1',runner:'synthetic-suite',runnerVersion:'1',runtimeVersion:'node-22',capture:{selectionComplete:true,terminalSeen:true,processEnded:true,eventRef:'original-report'},complete:true,exitCode:0,rows:[{occurrenceId:'a',testId:f.a,selected:true,started:true,outcome:'ok'},{occurrenceId:'b',testId:f.b,selected:true,started:true,outcome:'ok'}]};
  save('import',descriptor);save('report',report);for(const role of ['source','selection','execution'])save(role,{});
  const identity=prepareNativeEvidence({root:f.root,runDir:f.runDir,runId:f.readRun().runId,summaryFile}).assessment.identity;
  const source=Object.fromEntries(['sourceId','implementationId','testsId'].map(key=>[key,identity[key]]));
  const execution={sourceId:source.sourceId,stage:'pr1',processEnded:true,exitCode:0,producer:report.producer,producerVersion:'1',runner:report.runner,runnerVersion:'1',runtimeVersion:'node-22'};
  save('source',{producerRoot:f.root,tests:f.tests,source_sha256:sha,source,runId:f.readRun().runId,stage:'pr1'});
  save('selection',{sourceId:source.sourceId,stage:'pr1',complete:true,testIds:[f.a,f.b]});save('execution',execution);
  for(const role of ['import','report','source','selection','execution'])put(dir,'baseline/'+role+'.json',readFileSync(join(dir,role+'.json'),'utf8'));
  // Current code changes independently of the now admitted historical source.
  put(f.root,'source.mjs','export const value=3;\n');
  const next=prepareNativeEvidence({root:f.root,runDir:f.runDir,runId:f.readRun().runId,summaryFile}).assessment.identity;
  const current=Object.fromEntries(['sourceId','implementationId','testsId'].map(key=>[key,next[key]]));
  assert.equal(f.command('workflow','evidence-associate','17','--workspace',f.root,'--stage','current','--test',...f.tests).status,0);
  save('source',{producerRoot:f.root,tests:f.tests,source_sha256:captureSource(f.root,{tests:f.tests}).sha256,source:current,runId:f.readRun().runId,stage:'current'});
  save('selection',{sourceId:current.sourceId,stage:'current',complete:true,testIds:[f.a]});
  save('execution',{...execution,sourceId:current.sourceId,stage:'current'});
  save('report',{...report,rows:[report.rows[0],{...report.rows[0],occurrenceId:'duplicate-a'}]});
  save('import',{...descriptor,baseline:'baseline/import.json'});
  const imported=f.command('workflow','evidence','17','--summary',summaryFile);assert.equal(imported.status,0,imported.stdout+imported.stderr);
  const judge=()=>{const r=f.command('lint','native','--json');assert.equal(r.status,1,r.stdout+r.stderr);return JSON.parse(r.stdout).native_assessments[0].assessment;};
  const a=judge();assert.equal(a.identity.sourceId,current.sourceId);assert.equal(a.comparison.state,'comparable');assert.deepEqual(a.comparison.lostIds,[f.b]);
  assert.equal(f.eligibility(sha).state,'eligible');
  rmSync(join(association.sourceAnchor.root,'source.mjs'));
  const before=readFileSync(join(f.runDir,'status.json'));
  assert.equal(judge().comparison.state,'incomparable');
  assert.deepEqual(readFileSync(join(f.runDir,'status.json')),before);
});

for(const mode of ['unavailable','stale','foreign','marker','different-pr','missing-head','push-failed','edit-failed'])test(`normal PR 1 update refuses ${mode} without inventing a published anchor`,async t=>{
  const f=await publication(t),first=f.state.first;
  put(f.root,'source.mjs','export const value=2;\n');f.state.mode=mode;
  const r=await f.update();assert.equal(r.exitCode,1,r.message);
  assert.equal(f.pr().publishedHeadSha,first);
  const sha=captureSource(f.root,{tests:f.tests}).sha256;
  assert.equal(f.eligibility(sha).state,'ineligible');
  if(['push-failed','edit-failed'].includes(mode))assert.equal(f.remoteHead(),first);
  else assert.notEqual(f.remoteHead(),first,'A successful push alone cannot stamp a new head');
});

for(const changed of [false,true])test(`code approval sync retains validated PR 1 head (${changed?'new push':'already published'})`,async t=>{
  const f=await publication(t);
  if(changed){put(f.root,'source.mjs','export const value=2;\n');git(f.root,'add','.');git(f.root,'commit','-qm','Synthetic approved implementation source');}
  const r=await approveRun({ref:'17',said:'Start code for this synthetic local fixture.',cwd:f.root},f.ports);
  assert.equal(r.exitCode,0,r.message);
  assert.equal(f.readRun().areas[f.readRun().area].name,'code');
  assert.equal(f.pr().publishedHeadSha,f.remoteHead());
  assert.equal(f.pr().publishedHeadSha,git(f.root,'rev-parse','HEAD'));
  const registered=f.register();assert.equal(registered.status,0,registered.stdout+registered.stderr);
  assert.equal(f.eligibility(captureSource(f.root,{tests:f.tests}).sha256).state,'eligible');
});

for(const changed of [false,true])test(`code approval sync refuses unvalidated PR 1 (${changed?'pushed':'unchanged'}) before code entry`,async t=>{
  const f=await publication(t),before=f.readRun();
  if(changed){put(f.root,'source.mjs','export const value=2;\n');git(f.root,'add','.');git(f.root,'commit','-qm','Synthetic unconfirmed source');}
  f.state.mode='foreign';
  const r=await approveRun({ref:'17',said:'Start code for this synthetic local fixture.',cwd:f.root},f.ports);
  assert.equal(r.exitCode,1,r.message);
  assert.equal(f.readRun().area,before.area);
  assert.equal(f.readRun().branch,before.branch);
  assert.equal(f.pr().publishedHeadSha,f.state.first);
});
