// #2640 option B: a run finds the approved scenario files on its base by itself.
// Real temporary Git repositories; gh and Herdr stay boundary fakes.
import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {execFileSync} from 'node:child_process';
import {mkdirSync,mkdtempSync,readFileSync,realpathSync,rmSync,writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {performance} from 'node:perf_hooks';
import {dirname,join} from 'node:path';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {adoptedCorpusRun} from './helpers/workflow-concurrent-adoption.mjs';
import {startRun,stepDone,approveRun} from '../src/workflow-runner.mjs';
import {sourceFingerprint} from '../src/workflow-replay.mjs';

const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const check=(id,value)=>({criterion_id:id,target:'result',path:'/total',op:'equals',value});
const scenario=(story,prompt,checks,step='add')=>({schema_version:'prompt-runtime.program-scenario.v1',story_path:story,
  steps:[{step_id:step,entry_path:prompt,operation:'add',checks}]});
// The approved corpus on the base: two files of the add Story, one unrelated file.
const BASE={
  'prompts/add.prompt.md':'# Add\n','prompts/other.prompt.md':'# Other\n',
  'user_stories/add.md':'# Add\n## Acceptance criteria\n1. Adds.\n','user_stories/other.md':'# Other\n## Acceptance criteria\n1. Other.\n',
  'tests/add.json':JSON.stringify(scenario('user_stories/add.md','prompts/add.prompt.md',[check('AC1',3),check('AC1',3)])),
  'tests/add.empty.json':JSON.stringify(scenario('user_stories/add.md','prompts/add.prompt.md',[check('AC1',0)],'empty')),
  'tests/other.json':JSON.stringify(scenario('user_stories/other.md','prompts/other.prompt.md',[check('AC1',1)],'other')),
};
const BINDINGS=JSON.stringify({schema_version:'pdd.bindings.v1',modules:[{module:'value.mjs',stories:['user_stories/add.md'],prompt:'prompts/add.prompt.md'}]});
const CODE={name:'code',steps:['verify'],optional:[],gate:'pr',replay_evidence:'pdd.replay-evidence.v1'};
const PROMPT_AREAS=[{name:'story',steps:['scope'],optional:[],gate:'approve'},{name:'prompt-pr',steps:['check'],optional:[],gate:'pr',before:'approve',then:'ask-code'}];

function put(root,path,text){mkdirSync(dirname(join(root,path)),{recursive:true});writeFileSync(join(root,path),text);}
async function baseRun(t,{areas=[CODE],files=BASE}={}) {
  const f=await fixture(t,{name:'replay',agent:'codex'});
  put(f.source,'.agents/skills/pdd-replay/workflow.json',JSON.stringify({version:2,areas}));
  for(const [path,text] of Object.entries(files))put(f.source,path,text);
  f.git(f.source,'add','.');f.git(f.source,'commit','-qm','Approved corpus on main');
  const base=f.git(f.source,'rev-parse','HEAD');f.git(f.source,'update-ref','refs/remotes/origin/main',base);
  const out=await startRun({name:'replay',issue:'17',agent:'codex',cwd:f.source,packageRoot},f.ports);
  assert.equal(out.exitCode,0,out.message);
  return {f,run:f.record(),base};
}
// The agent's record for the current bytes of each named file: every check executed and passed.
function manifest(run,paths) {
  const vectors=[],checks=[],operations=[];
  for(const path of paths){
    const bytes=readFileSync(join(run.root,path)),doc=JSON.parse(bytes);vectors.push({path,sha256:hash(bytes)});
    for(const step of doc.steps){
      operations.push({vector:path,step_id:step.step_id,entry_path:step.entry_path,operation:step.operation,executed:true,outcome:'returned',boundary:{kind:'function',name:step.operation},command:'node --test test/add.vectors.test.mjs',exit_code:0});
      step.checks.forEach((c,check_index)=>checks.push({vector:path,step_id:step.step_id,check_index,entry_path:step.entry_path,operation:step.operation,criterion_id:c.criterion_id,target:c.target,path:c.path,op:c.op,outcome:'pass'}));
    }
  }
  return {schema_version:'pdd.replay-evidence.v1',run_id:run.runId,source:{kind:'git-content-v1',sha256:sourceFingerprint(run.root)},vectors,checks,operations,
    counts:{total:checks.length,pass:checks.length,fail:0,blocked:0,not_replayed:0},
    mutation:{kind:'semantic',description:'Return a wrong total',command:'node --test test/add.vectors.test.mjs --mutant',exit_code:1,outcome:'assertion_failure',failed_checks:[{vector:checks[0].vector,step_id:checks[0].step_id,check_index:0}]},
    formal:{result:'not_applicable',scope:'Public wiring',reason:'No formal rule',control_outcome:'not_run'}};
}
const record=(run,paths)=>writeFileSync(join(run.runDir,'replay-evidence.json'),JSON.stringify(manifest(run,paths)));
const baseBytes=(f,base,path)=>execFileSync('git',['cat-file','blob',`${base}:${path}`],{cwd:f.source});

test('2640 B: a code-only run adopts the linked approved base files, records provenance and counts them on the PR',async t=>{
  const {f,run,base}=await baseRun(t,{files:{...BASE,'pdd-bindings.json':BINDINGS}});
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');
  record(run,['tests/add.empty.json','tests/add.json']);
  const out=await stepDone({step:'verify',summary:'Replayed the approved cases',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);assert.equal(f.prs.length,1);
  const body=f.prs[0].body;
  assert.match(body,/^Code replay: PASS/m);
  assert.match(body,new RegExp(`^Anchor: 0 changed scenarios \\(0 checks\\) \\+ 2 linked approved on base ${base.slice(0,7)} \\(3 checks\\)\\.$`,'m'));
  const anchor=f.record().replayBaseline;
  assert.deepEqual(anchor.vectors.map(v=>v.path),['tests/add.empty.json','tests/add.json'],'the unlinked other.json stays out');
  assert.equal(anchor.base.commit,base);
  for(const vector of anchor.vectors){
    assert.equal(vector.base,base);assert.equal(vector.sha256,hash(baseBytes(f,base,vector.path)));
    assert.deepEqual(vector.checks.map(c=>[c.vector,c.step_id,c.check_index]),JSON.parse(baseBytes(f,base,vector.path)).steps[0].checks.map((_,i)=>[vector.path,vector.checks[0].step_id,i]));
  }
});

test('2640 B: base adoption never gives PASS by itself; unreplayed anchored checks stay NOT REPLAYED',async t=>{
  const {f,run}=await baseRun(t,{files:{...BASE,'pdd-bindings.json':BINDINGS}});
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');
  record(run,['tests/add.json']);
  const out=await stepDone({step:'verify',summary:'PASS in prose',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);assert.doesNotMatch(f.prs[0].body,/^Code replay: PASS/m);
  assert.match(f.prs[0].body,/^Code replay: (?:BLOCKED|NOT REPLAYED)/m);
});

test('2640 B: a repository with no recorded link adds nothing and says so honestly',async t=>{
  const {f,run,base}=await baseRun(t);
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');
  record(run,['tests/add.json']);
  const out=await stepDone({step:'verify',summary:'PASS in prose',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  const body=f.prs[0].body;
  assert.match(body,/^Code replay: BLOCKED — No approved original-vector anchor/m);
  assert.match(body,new RegExp(`^Anchor: 0 changed scenarios \\(0 checks\\) \\+ 0 linked approved on base ${base.slice(0,7)} \\(3 base scenario files, none names a prompt or Story that this run changed; no changed file names its prompt in a Generated from header; the base has no pdd-bindings\\.json to link changed code\\)\\.$`,'m'));
  assert.deepEqual(f.record().replayBaseline.vectors,[]);
});

test('2640 B: a base file changed in code space keeps its approved bytes and cannot pass on the old record',async t=>{
  const {f,run,base}=await baseRun(t,{files:{...BASE,'pdd-bindings.json':BINDINGS}});
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');
  record(run,['tests/add.empty.json','tests/add.json']);
  const edited=JSON.parse(readFileSync(join(run.root,'tests/add.json')));edited.steps[0].checks[0].value=99;
  writeFileSync(join(run.root,'tests/add.json'),JSON.stringify(edited));
  const out=await stepDone({step:'verify',summary:'PASS in prose',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  const body=f.prs[0].body;
  assert.doesNotMatch(body,/^Code replay: PASS/m);
  assert.match(body,/warning: Saved test values changed:/);
  const vector=f.record().replayBaseline.vectors.find(v=>v.path==='tests/add.json');
  assert.equal(vector.sha256,hash(baseBytes(f,base,'tests/add.json')),'the anchor keeps the base bytes');
  assert.equal(vector.snapshot.steps[0].checks[0].value,3);
});

test('2640 B: a base file removed in code space before a replay read blocks and stays in the anchor',async t=>{
  const {f,run,base}=await baseRun(t,{files:{...BASE,'pdd-bindings.json':BINDINGS}});
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');
  record(run,['tests/add.empty.json']);rmSync(join(run.root,'tests/add.json'));
  const out=await stepDone({step:'verify',summary:'PASS in prose',cwd:run.root},f.agentPorts());
  assert.match(f.record().replayEvidence.outcome,/^blocked$/,out.message);
  assert.doesNotMatch(f.prs.at(-1)?.body ?? '',/^Code replay: PASS/m);
  const anchor=f.record().replayBaseline;assert.ok(anchor,'the code-space anchor is saved');
  const vector=anchor.vectors.find(v=>v.path==='tests/add.json');
  assert.equal(vector?.sha256,hash(baseBytes(f,base,'tests/add.json')),'the removed file stays in the anchor');
});

test('2640 B: mixed run anchors the changed scenarios of PR 1 and the approved base files of the same prompt',async t=>{
  const {f,run,base}=await baseRun(t,{areas:[...PROMPT_AREAS,CODE]});
  put(run.root,'user_stories/refund.md','# Refund\n## Acceptance criteria\n1. Refunds.\n');
  put(run.root,'tests/refund.json',JSON.stringify(scenario('user_stories/refund.md','prompts/add.prompt.md',[check('AC1',-3)],'refund')));
  assert.equal((await stepDone({step:'scope',summary:'scoped',cwd:run.root},f.agentPorts())).exitCode,0);f.tick();
  assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  await stepDone({step:'check',summary:'Runtime check: ✓ 1 of 1 criteria',cwd:run.root},f.agentPorts());f.tick();
  const approved=await approveRun({ref:'17',cwd:f.source},f.ports);assert.equal(approved.exitCode,0,approved.message);
  assert.equal(f.record().areas[f.record().area].name,'code');
  const anchor=f.record().replayBaseline;
  assert.deepEqual(anchor.vectors.map(v=>[v.path,v.base??null]),[['tests/refund.json',null],['tests/add.empty.json',base],['tests/add.json',base]]);
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');
  record(run,['tests/refund.json','tests/add.empty.json','tests/add.json']);
  const out=await stepDone({step:'verify',summary:'Replayed',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  const body=f.prs.at(-1).body;
  assert.match(body,/^Code replay: PASS/m);
  assert.match(body,new RegExp(`^Anchor: 1 changed scenario \\(1 check\\) \\+ 2 linked approved on base ${base.slice(0,7)} \\(3 checks\\)\\.$`,'m'));
  assert.deepEqual(f.record().replayBaseline,anchor,'code space keeps the frozen anchor');
});

test('2640 B: the explicit --adopt-corpus route keeps its declared anchor and adds no base files',async t=>{
  const {f,vector,begin,bare}=await adoptedCorpusRun(t,{start:false});
  // A linked, undeclared scenario on the base: the declaration still defines the whole inventory.
  writeFileSync(join(f.source,'tests/extra.json'),JSON.stringify(vector));
  f.git(f.source,'add','.');f.git(f.source,'commit','-qm','Undeclared linked scenario');
  f.git(f.source,'update-ref','refs/remotes/origin/main',f.git(f.source,'rev-parse','HEAD'));f.git(f.source,'push','-q',bare,'HEAD:refs/heads/main');
  const started=await begin();assert.equal(started.exitCode,0,started.message);
  const run=f.record();assert.deepEqual(run.replayBaseline.vectors.map(v=>v.path),['tests/add.json']);assert.equal(run.replayBaseline.base,undefined);
  writeFileSync(join(run.root,'value.mjs'),'export const value=2;\n');record(run,['tests/add.json']);
  const out=await stepDone({step:'verify',summary:'Replayed',cwd:run.root},f.agentPorts());assert.equal(out.exitCode,0,out.message);
  assert.match(f.prs[0].body,/^Code replay: PASS/m);assert.match(f.prs[0].body,/Anchor adopted from example\/project@/);
  assert.doesNotMatch(f.prs[0].body,/approved on base/);assert.equal(f.record().replayBaseline.base,undefined);
});

// Direct boundary checks on real Git repositories.
async function api(){const module=await import('../src/workflow-replay.mjs');assert.equal(typeof module.pinRunAnchor,'function','pinRunAnchor is exported');return module;}
function repo(t,files) {
  const root=realpathSync(mkdtempSync(join(tmpdir(),'pdd-base-corpus-')));t.after(()=>rmSync(root,{recursive:true,force:true}));
  const git=(...args)=>execFileSync('git',args,{cwd:root,encoding:'utf8'}).trim();git('init','-q');
  for(const [path,text] of Object.entries(files))put(root,path,text);
  git('add','.');git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','base');
  return {root,git,base:git('rev-parse','HEAD')};
}

test('2640 B: very many linked base files are all counted; over the limit the anchor blocks and states the count',async t=>{
  const {pinRunAnchor}=await api(),files={'prompts/add.prompt.md':'# Add\n'};
  for(let i=0;i<201;i++)files[`tests/case-${String(i).padStart(3,'0')}.json`]=JSON.stringify(scenario(`user_stories/case-${i}.md`,'prompts/add.prompt.md',[check('AC1',i)]));
  const r=repo(t,files);put(r.root,'prompts/add.prompt.md','# Add, changed\n');
  const anchor=pinRunAnchor(r.root,{paths:[],commit:r.base,changed:['prompts/add.prompt.md'],scenarios:[]});
  assert.equal(anchor.outcome,'blocked');assert.deepEqual(anchor.vectors,[]);
  assert.equal(anchor.reason,`The anchor needs 201 scenario files (0 changed + 201 linked approved on base ${r.base.slice(0,7)}); the limit is 200.`);
  rmSync(join(r.root,'tests/case-200.json'));r.git('add','-A');r.git('-c','user.name=Test','-c','user.email=test@example.invalid','commit','-qm','200');
  const fits=pinRunAnchor(r.root,{paths:[],commit:r.git('rev-parse','HEAD'),changed:['prompts/add.prompt.md'],scenarios:[]});
  assert.equal(fits.outcome,undefined,fits.reason);assert.equal(fits.vectors.length,200);
});

test('2640 B: a malformed pdd-bindings.json adds no links and the note names it',async t=>{
  const {pinRunAnchor}=await api(),r=repo(t,{...BASE,'pdd-bindings.json':'{"schema_version":"pdd.bindings.v1","modules":[{"module":"value.mjs"}]}'});
  const anchor=pinRunAnchor(r.root,{paths:[],commit:r.base,changed:['value.mjs'],scenarios:[]});
  assert.equal(anchor.outcome,'not_replayed');assert.match(anchor.base.note,/pdd-bindings\.json on the base is malformed and was not used/);
  const blocked=pinRunAnchor(r.root,{commit:r.base,changed:['value.mjs'],codeSpace:true});
  assert.equal(blocked.outcome,'blocked');assert.match(blocked.reason,/^No approved original-vector anchor: 3 base scenario files, none names/);
});

test('2640 B: a linked base file that PR 1 removes blocks the anchor before code',async t=>{
  const {f,run}=await baseRun(t,{areas:[...PROMPT_AREAS,CODE]});
  put(run.root,'tests/refund.json',JSON.stringify(scenario('user_stories/add.md','prompts/add.prompt.md',[check('AC1',-3)],'refund')));
  rmSync(join(run.root,'tests/add.json'));
  assert.equal((await stepDone({step:'scope',summary:'scoped',cwd:run.root},f.agentPorts())).exitCode,0);f.tick();
  assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  await stepDone({step:'check',summary:'Runtime check: ✓ 1 of 1 criteria',cwd:run.root},f.agentPorts());f.tick();
  assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  const anchor=f.record().replayBaseline;
  assert.equal(anchor.outcome,'blocked',JSON.stringify(anchor));assert.deepEqual(anchor.vectors,[]);
});

// Repair 1 (B): a changed code file links through its own PDD "Generated from" header.
const HEADER=`// Generated from prompts/add.prompt.md (sha256: ${hash('# Add\n')}).\n`;
// A third base file of the add Story through another prompt: it shares the header prompt's Story.
const STORY_MATE={'prompts/cli.prompt.md':'# CLI\n','tests/add.cli.json':JSON.stringify(scenario('user_stories/add.md','prompts/cli.prompt.md',[check('AC1',7)],'cli'))};
// agent-link src/pdd_link/m1_policy.py names no prompt path in its "Generated from" line.
const M1_STYLE='"""Pure declared-fact assessments.\n\nGenerated from the canonical m1_policy prompt and its selected neutral contracts.\n"""\nVALUE = 1\n';

test('2640 repair B: a code-only change to a file with a Generated-from header adds its prompt\'s base scenarios and its Story',async t=>{
  const {f,run,base}=await baseRun(t,{files:{...BASE,...STORY_MATE,'value.mjs':`#!/usr/bin/env node\n${HEADER}export const value = 1;\n`}});
  writeFileSync(join(run.root,'value.mjs'),`#!/usr/bin/env node\n${HEADER}export const value = 2;\n`);
  record(run,['tests/add.cli.json','tests/add.empty.json','tests/add.json']);
  const out=await stepDone({step:'verify',summary:'Replayed the approved cases',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  const body=f.prs[0].body;
  assert.match(body,/^Code replay: PASS/m);
  assert.match(body,new RegExp(`^Anchor: 0 changed scenarios \\(0 checks\\) \\+ 3 linked approved on base ${base.slice(0,7)} \\(4 checks\\)\\.$`,'m'));
  const anchor=f.record().replayBaseline;
  assert.deepEqual(anchor.vectors.map(v=>[v.path,v.base]),[['tests/add.cli.json',base],['tests/add.empty.json',base],['tests/add.json',base]],'other.json stays out');
  assert.equal(anchor.base.select,'linked');
});

test('2640 repair B: header formats are exact; a "Generated from" line without a prompt path links nothing',async t=>{
  const {pinRunAnchor}=await api(),files={};
  for(const n of [1,2,3,4,5,6]){files[`prompts/p${n}.prompt.md`]=`# P${n}\n`;files[`tests/p${n}.json`]=JSON.stringify(scenario(`user_stories/p${n}.md`,`prompts/p${n}.prompt.md`,[check('AC1',n)]));}
  files['a.py']='# Generated from prompts/p1.prompt.md.\nVALUE = 1\n';
  files['d.py']=M1_STYLE.replace('m1_policy prompt','p4 prompt');
  files['e.mjs']=`${'// line\n'.repeat(10)}// Generated from prompts/p5.prompt.md.\n`;
  files['f.mjs']='const x = "Generated from prompts/p6.prompt.md.";\n';
  const r=repo(t,files);
  rmSync(join(r.root,'a.py'));// Removed in the run: its base header still counts.
  put(r.root,'b.py',`"""Generated from prompts/p2.prompt.md (sha256: ${hash('x')})."""\n`);// Added in the run.
  put(r.root,'c.html','<!doctype html>\n<!-- Generated from prompts/p3.prompt.md -->\n');
  for(const path of ['d.py','e.mjs','f.mjs'])put(r.root,path,readFileSync(join(r.root,path),'utf8')+'\n');
  const anchor=pinRunAnchor(r.root,{commit:r.base,changed:['a.py','b.py','c.html','d.py','e.mjs','f.mjs'],codeSpace:true});
  assert.equal(anchor.outcome,undefined,anchor.reason);
  assert.deepEqual(anchor.vectors.map(v=>v.path),['tests/p1.json','tests/p2.json','tests/p3.json']);
});

test('2640 repair B: a changed file with no prompt header and no bindings adds nothing; the line says why',async t=>{
  const {f,run,base}=await baseRun(t,{files:{...BASE,'src/m1_policy.py':M1_STYLE}});
  writeFileSync(join(run.root,'src/m1_policy.py'),M1_STYLE.replace('VALUE = 1','VALUE = 2'));
  record(run,['tests/add.json']);
  const out=await stepDone({step:'verify',summary:'PASS in prose',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  const body=f.prs[0].body;
  assert.match(body,/^Code replay: BLOCKED — No approved original-vector anchor/m);
  assert.match(body,new RegExp(`^Anchor: 0 changed scenarios \\(0 checks\\) \\+ 0 linked approved on base ${base.slice(0,7)} \\(3 base scenario files, none names a prompt or Story that this run changed; no changed file names its prompt in a Generated from header; the base has no pdd-bindings\\.json to link changed code\\)\\.$`,'m'));
  assert.deepEqual(f.record().replayBaseline.vectors,[]);
});

// Repair 1 (C): root pdd.json on the base commit can select every approved base scenario.
const ALL=JSON.stringify({autopilot:{mode:'off',trust:[]},replay:{base_scenarios:'all'}});

test('2640 repair C: base_scenarios "all" adds every approved base scenario and the PR line says so',async t=>{
  const {f,run,base}=await baseRun(t,{files:{...BASE,'pdd.json':ALL}});
  writeFileSync(join(run.root,'value.mjs'),'export const value = 2;\n');
  record(run,['tests/add.empty.json','tests/add.json','tests/other.json']);
  const out=await stepDone({step:'verify',summary:'Replayed every approved case',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  const body=f.prs[0].body;
  assert.match(body,/^Code replay: PASS/m);
  assert.match(body,new RegExp(`^Anchor: 0 changed scenarios \\(0 checks\\) \\+ all 3 approved on base ${base.slice(0,7)} \\(4 checks; pdd\\.json sets replay\\.base_scenarios to "all"\\)\\.$`,'m'));
  const anchor=f.record().replayBaseline;
  assert.deepEqual(anchor.vectors.map(v=>[v.path,v.base]),[['tests/add.empty.json',base],['tests/add.json',base],['tests/other.json',base]]);
  assert.equal(anchor.base.select,'all');
});

test('2640 repair C: "all" keeps the limits; over a limit the anchor blocks and states the count',async t=>{
  const {pinRunAnchor}=await api(),files={'pdd.json':ALL};
  for(let i=0;i<201;i++)files[`tests/case-${String(i).padStart(3,'0')}.json`]=JSON.stringify(scenario(`user_stories/case-${i}.md`,`prompts/case-${i}.prompt.md`,[check('AC1',i)]));
  const r=repo(t,files);
  const anchor=pinRunAnchor(r.root,{commit:r.base,changed:['value.mjs'],codeSpace:true});
  assert.equal(anchor.outcome,'blocked');assert.deepEqual(anchor.vectors,[]);
  assert.equal(anchor.reason,`The anchor needs 201 scenario files (0 changed + all 201 approved on base ${r.base.slice(0,7)}); the limit is 200.`);
  const many=n=>scenario('user_stories/many.md','prompts/many.prompt.md',Array.from({length:n},(_,i)=>check('AC1',i)),`many-${n}`);
  const c=repo(t,{'pdd.json':ALL,'tests/a.json':JSON.stringify(many(5001)),'tests/b.json':JSON.stringify(many(5001))});
  const checks=pinRunAnchor(c.root,{commit:c.base,changed:['value.mjs'],codeSpace:true});
  assert.equal(checks.outcome,'blocked');
  assert.equal(checks.reason,`The anchor needs 10002 checks and 2 steps in 2 scenario files (0 changed + all 2 approved on base ${c.base.slice(0,7)}); the limit is 10000 each.`);
});

test('2640 repair C: the default stays linked; the setting comes from the base commit; a bad value blocks',async t=>{
  const {pinRunAnchor}=await api();
  for(const config of [undefined,{autopilot:{mode:'auto',trust:[]}},{replay:{}},{replay:{base_scenarios:'linked'}}]){
    const r=repo(t,{...BASE,...(config?{'pdd.json':JSON.stringify(config)}:{})});
    put(r.root,'pdd.json',ALL);// The run's own copy does not count.
    const anchor=pinRunAnchor(r.root,{commit:r.base,changed:['value.mjs'],codeSpace:true});
    assert.equal(anchor.outcome,'blocked',JSON.stringify(config));assert.deepEqual(anchor.vectors,[]);
    assert.equal(anchor.base.select,'linked');assert.match(anchor.reason,/^No approved original-vector anchor: 3 base scenario files, none names/);
    const linked=pinRunAnchor(r.root,{commit:r.base,changed:['prompts/other.prompt.md'],codeSpace:true});
    assert.deepEqual(linked.vectors.map(v=>v.path),['tests/other.json'],'linked selection is unchanged');
  }
  for(const [bytes,reason] of [['{"replay":{"base_scenarios":"every"}}','replay.base_scenarios must be "linked" or "all"'],['{"replay":"all"}','replay.base_scenarios must be "linked" or "all"'],['{"replay":','is not valid JSON'],['[]','is not a JSON object']]){
    const r=repo(t,{...BASE,'pdd.json':bytes});
    const anchor=pinRunAnchor(r.root,{commit:r.base,changed:['prompts/add.prompt.md'],codeSpace:true});
    assert.equal(anchor.outcome,'blocked');assert.deepEqual(anchor.vectors,[]);
    assert.equal(anchor.reason,`pdd.json on base ${r.base.slice(0,7)}${reason.startsWith('replay')?': ':' '}${reason}.`);
  }
});

test('2640 repair C: with a prompt area, "all" adds every unchanged base file after the changed scenarios',async t=>{
  const {pinRunAnchor}=await api(),r=repo(t,{...BASE,'pdd.json':ALL});
  put(r.root,'tests/refund.json',JSON.stringify(scenario('user_stories/refund.md','prompts/refund.prompt.md',[check('AC1',-3)],'refund')));
  r.git('add','tests/refund.json');
  const edited=JSON.parse(readFileSync(join(r.root,'tests/other.json')));edited.steps[0].checks[0].value=2;put(r.root,'tests/other.json',JSON.stringify(edited));
  const anchor=pinRunAnchor(r.root,{paths:['tests/refund.json','tests/other.json'],commit:r.base,changed:['tests/refund.json','tests/other.json'],scenarios:['tests/refund.json','tests/other.json']});
  assert.equal(anchor.outcome,undefined,anchor.reason);
  assert.deepEqual(anchor.vectors.map(v=>[v.path,v.base??null]),[['tests/refund.json',null],['tests/other.json',null],['tests/add.empty.json',r.base],['tests/add.json',r.base]]);
  assert.equal(anchor.vectors[1].snapshot.steps[0].checks[0].value,2,'a base file that PR 1 changes keeps its PR 1 bytes');
});

// Repair 2: exercise the runner with real Git; only gh and Herdr are fakes.
test('2640 repair 2 M1: a PR 1 rename blocks like a delete, without pinning a phantom base file',async t=>{
  const {f,run}=await baseRun(t,{areas:[...PROMPT_AREAS,CODE]});
  put(run.root,'tests/refund.json',JSON.stringify(scenario('user_stories/add.md','prompts/add.prompt.md',[check('AC1',-3)],'refund')));
  f.git(run.root,'config','diff.renames','true');
  f.git(run.root,'mv','tests/add.json','tests/moved.json');
  assert.equal((await stepDone({step:'scope',summary:'scoped',cwd:run.root},f.agentPorts())).exitCode,0);f.tick();
  assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  await stepDone({step:'check',summary:'Runtime check: ✓ 1 of 1 criteria',cwd:run.root},f.agentPorts());f.tick();
  assert.equal((await approveRun({ref:'17',cwd:f.source},f.ports)).exitCode,0);
  const anchor=f.record().replayBaseline;
  assert.equal(anchor.outcome,'blocked','the renamed source must fail the changed-scenario inventory');
  assert.deepEqual(anchor.vectors,[],'the old path must not survive as an unchanged base file');
  put(run.root,'value.mjs','export const value=2;\n');
  record(run,['tests/moved.json','tests/add.empty.json','tests/refund.json']);
  await stepDone({step:'verify',summary:'Replay record supplied',cwd:run.root},f.agentPorts());
  assert.equal(f.record().replayEvidence.outcome,'blocked');
  assert.match(f.prs.at(-1).body,/^Code replay: BLOCKED/m);
});

test('2640 repair 2 F3: an unknown base replay key blocks and names the key and pdd.json',async t=>{
  for(const replay of [{base_scenario:'all'},{base_scenarios:'all',unexpected:true}]){
    const {f,run}=await baseRun(t,{files:{...BASE,'pdd.json':JSON.stringify({replay})}});
    put(run.root,'pdd.json',JSON.stringify({replay:{base_scenarios:'linked'}}));
    put(run.root,'prompts/add.prompt.md','# Add changed\n');
    record(run,['tests/add.empty.json','tests/add.json']);
    await stepDone({step:'verify',summary:'Replay record supplied',cwd:run.root},f.agentPorts());
    const anchor=f.record().replayBaseline,key=Object.keys(replay).find(key=>key!=='base_scenarios');
    assert.ok(anchor,'the runner must save the base-selection outcome');
    assert.equal(anchor.outcome,'blocked','unknown base replay keys must not fall back to linked');
    assert.deepEqual(anchor.vectors,[]);
    assert.ok(anchor.reason.includes(key),`the reason must name ${key}`);
    assert.match(anchor.reason,/pdd\.json/);
    const line=f.prs.at(-1).body.split('\n').find(line=>line.startsWith('Code replay:'));
    assert.ok(line.replaceAll('\\','').includes(key));assert.match(line,/pdd\.json/);
  }
});

test('2640 repair 2 F1: repo color settings cannot hide linked or all base scenarios',async t=>{
  for(const select of ['linked','all']){
    const {f,run}=await baseRun(t,{files:{...BASE,'pdd.json':JSON.stringify({replay:{base_scenarios:select}})}});
    for(const setting of ['color.ui','color.grep','color.diff'])f.git(run.root,'config',setting,'always');
    put(run.root,'prompts/add.prompt.md','# Add changed\n');
    const paths=['tests/add.empty.json','tests/add.json',...(select==='all'?['tests/other.json']:[])];
    record(run,paths);
    const out=await stepDone({step:'verify',summary:'Replayed base scenarios with color configured',cwd:run.root},f.agentPorts());
    assert.equal(out.exitCode,0,out.message);
    const anchor=f.record().replayBaseline;
    assert.ok(anchor,'the runner must save an anchor under repo color settings');
    assert.deepEqual(anchor.vectors.map(v=>v.path),paths,select);
    assert.match(f.prs.at(-1).body,/^Code replay: PASS/m);
    assert.doesNotMatch(f.prs.at(-1).body,/\x1b/);
  }
});

test('2640 repair 2 F2: 64 KiB whitespace and header-shaped lines do not delay replay reads',async t=>{
  const prefix='// Generated from prompts/other.prompt.md';
  const files={...BASE,'space.mjs':' '.repeat(65535)+'\n',
    'bad.mjs':prefix+' '.repeat(65534-prefix.length)+'x\n','good.mjs':HEADER+'export const value=1;\n'};
  const {f,run}=await baseRun(t,{files});
  for(const path of ['space.mjs','bad.mjs','good.mjs'])put(run.root,path,files[path]+'// changed\n');
  record(run,['tests/add.empty.json','tests/add.json']);
  const start=performance.now();
  const out=await stepDone({step:'verify',summary:'Replayed with long source lines',cwd:run.root},f.agentPorts());
  const elapsed=performance.now()-start;
  assert.ok(elapsed<4000,`header parsing must stay bounded: ${Math.round(elapsed)} ms`);
  assert.equal(out.exitCode,0,out.message);
  const anchor=f.record().replayBaseline;
  assert.ok(anchor,'the runner must save the header-selected anchor');
  assert.deepEqual(anchor.vectors.map(v=>v.path),['tests/add.empty.json','tests/add.json']);
  assert.match(f.prs.at(-1).body,/^Code replay: PASS/m);
  t.diagnostic(`Replay publication with two 64 KiB lines: ${Math.round(elapsed)} ms`);
});

test('2640 repair 2 F4: changing a prompt also selects base scenarios of its Stories through other prompts',async t=>{
  const {f,run}=await baseRun(t,{files:{...BASE,...STORY_MATE}});
  put(run.root,'prompts/add.prompt.md','# Add changed\n');
  const paths=['tests/add.cli.json','tests/add.empty.json','tests/add.json'];record(run,paths);
  const out=await stepDone({step:'verify',summary:'Replayed the prompt and its Stories',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  const anchor=f.record().replayBaseline;
  assert.ok(anchor,'the runner must save the changed-prompt anchor');
  assert.deepEqual(anchor.vectors.map(v=>v.path),paths,'the same Story expansion applies to changed prompts and header prompts');
  assert.match(f.prs.at(-1).body,/^Code replay: PASS/m);
});

test('2640 repair 2 F7: oversized linked search matches are named in the PR Anchor note with and without other selected files',async t=>{
  const large=JSON.stringify({...scenario('user_stories/add.md','prompts/add.prompt.md',[check('AC1',3)]),padding:' '.repeat(10*1024*1024)});
  // Two long canonical paths make the note exceed the ordinary metadata text limit.
  const parent=`tests/${'a'.repeat(180)}/${'b'.repeat(180)}/${'c'.repeat(180)}`;
  const paths=[`${parent}/large-1.json`,`${parent}/large-2.json`];
  for(const small of [false,true]){
    const {f,run}=await baseRun(t,{files:{...(small?BASE:{}),...Object.fromEntries(paths.map(path=>[path,large]))}});
    put(run.root,'prompts/add.prompt.md','# Add changed\n');
    if(small)record(run,['tests/add.empty.json','tests/add.json']);
    await stepDone({step:'verify',summary:'Oversized base file is visible in the report',cwd:run.root},f.agentPorts());
    const anchor=f.record().replayBaseline;
    assert.ok(anchor,'the runner must save the base-file selection note');
    assert.ok(!anchor.vectors.some(v=>paths.includes(v.path)),'do not load oversized blobs into the anchor');
    const line=f.prs.at(-1).body.split('\n').find(line=>line.startsWith('Anchor:'));
    for(const path of paths)assert.ok(line?.includes(path),'the Anchor line must name each skipped file without truncation');
    assert.ok(line.includes(String(Buffer.byteLength(large))),'the Anchor line must state the byte count');
    assert.match(line,/10 MiB/);
    if(small)assert.equal(anchor.vectors.length,2,'keep the readable linked files');
  }
});

for (const [kind, config] of [
  ['valid-all', JSON.stringify({replay:{base_scenarios:'all'}, padding:' '.repeat(10*1024*1024)})],
  ['broken', '{"replay":' + ' '.repeat(10*1024*1024)]
]) test(`2640 integration config: oversized ${kind} base config blocks publication replay`, async t => {
  const {f,run}=await baseRun(t,{files:{...BASE,'pdd.json':config,'pdd-bindings.json':BINDINGS}});
  put(run.root,'pdd.json',JSON.stringify({replay:{base_scenarios:'linked'}}));
  put(run.root,'value.mjs','export const value=2;\n');
  record(run,['tests/add.empty.json','tests/add.json']);
  const out=await stepDone({step:'verify',summary:'Linked record',cwd:run.root},f.agentPorts());
  assert.equal(out.exitCode,0,out.message);
  assert.equal(f.record().replayBaseline.outcome,'blocked');
  assert.match(f.record().replayBaseline.reason,/pdd\.json/);
  assert.equal(f.record().replayEvidence.outcome,'blocked');
  assert.doesNotMatch(f.prs.at(-1).body,/^Code replay: PASS/m);
});
