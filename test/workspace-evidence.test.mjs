import assert from 'node:assert/strict';
import test from 'node:test';
import {readFileSync,writeFileSync,symlinkSync,rmSync,mkdirSync} from 'node:fs';
import {spawnSync,execFile as callbackExec} from 'node:child_process';
import {join,resolve} from 'node:path';
import {runPdd,renderHelp} from '../src/pdd-cli.mjs';
import {parseArgv} from '../src/argument-parser.mjs';
import {renderCompletion} from '../src/completion.mjs';
import * as runner from '../src/workflow-runner.mjs';
const {recordEvidence,associateEvidenceWorkspace,storyCount,storyEvidence,runStatus}=runner;
import {evidenceFixture,assertProtected,selection} from './helpers/workspace-evidence-fixture.mjs';
const packageRoot=resolve(import.meta.dirname,'..');
const sink=()=>({value:'',write(value){this.value+=value;}});
const registerArgs=['workflow','evidence-associate','17','--workspace','./clone space','--stage','current','--test',...selection,'tests/unknown-item.json'];

test('2899 CLI requires explicit registration input and forwards the immutable selection unchanged',async()=>{
  assert.equal(typeof associateEvidenceWorkspace,'function','2899 native evidence registration must exist');
  const plan=parseArgv(registerArgs);assert.deepEqual(plan.options['--test'],[...selection,'tests/unknown-item.json']);assert.ok(Object.isFrozen(plan.options['--test']));
  assert.match(renderHelp(['workflow']),/evidence-associate ISSUE/);
  for(const shell of ['bash','zsh'])assert.match(renderCompletion(shell),/evidence-associate/);
  const calls=[],runner={associateEvidenceWorkspace:async(input,ports)=>{calls.push({input,ports});return {exitCode:0,message:'registered'};}};
  const stdout=sink(),stderr=sink();assert.equal(await runPdd(registerArgs,{cwd:'/owned',workflowRunner:runner,stdout,stderr}),0);
  assert.deepEqual(calls[0].input,{ref:'17',workspace:'./clone space',stage:'current',tests:[...selection,'tests/unknown-item.json'],cwd:'/owned',packageRoot});
  assert.equal(stdout.value,'registered\n');assert.equal(stderr.value,'');
  for(const args of [registerArgs.slice(0,3),['workflow','evidence-associate','17','--workspace','/clone','--stage','current'],
    ['workflow','evidence-associate','17','--workspace','/clone','--test',...selection],
    ['workflow','evidence-associate','17','--stage','current','--test',...selection],
    [...registerArgs,'--test',...selection],['workflow','evidence-associate','17','--test','--help'],
    ['workflow','evidence-associate','17','--test',' '],['workflow','evidence-associate','17','--stage','code']]) {
    assert.equal(await runPdd(args,{cwd:'/owned',workflowRunner:new Proxy({},{get(){assert.fail('Invalid registration must not dispatch');}}),stdout:sink(),stderr:sink()}),2);
  }
  const other=parseArgv(['workflow','evidence','17','--summary','one file']);assert.equal(other.options['--summary'],'one file');
});

test('2899 actual CLI registration and import preserve original receipt and workflow state',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.clone),before=f.read(),env={...process.env,HOME:join(f.base,'home'),XDG_STATE_HOME:join(f.base,'state')};
  const invoke=args=>spawnSync(process.execPath,[join(packageRoot,'bin/pdd.mjs'),...args],{cwd:f.root,env,encoding:'utf8'});
  let result=invoke(['workflow','evidence-associate','17','--workspace',f.clone,'--stage','current','--test',...selection]);
  assert.equal(result.status,0,result.stdout+result.stderr);assertProtected(before,f.read());
  result=invoke(['workflow','evidence','17','--summary',saved.file]);assert.equal(result.status,0,result.stdout+result.stderr);
  assertProtected(before,f.read());assert.equal(readFileSync(saved.file,'utf8'),saved.bytes);assert.deepEqual(f.read().evidence[0].receipt,saved.doc);
  const statusBefore=readFileSync(f.status,'utf8');result=invoke(['workflow','status','17','--json']);assert.equal(result.status,0,result.stdout+result.stderr);
  assert.equal(JSON.parse(result.stdout).runs[0].stories.pass,1);assert.equal(readFileSync(f.status,'utf8'),statusBefore);
});

test('2899 registration refuses foreign invocation, non-root workspace and hostile selections without saving',async t=>{
  const f=await evidenceFixture(t);mkdirSync(join(f.clone,'subdir'));
  for(const [cwd,workspace,tests,stage] of [[f.clone,f.clone,selection,'current'],[f.root,join(f.clone,'subdir'),selection,'current'],
    [f.root,f.clone,[],'current'],[f.root,f.clone,[...selection,...selection],'current'],
    ...['../tests/place-order.json','/tests/place-order.json','C:/tests/a.json','tests\\a.json','.git/config','tests/./place-order.json','tests/../tests/place-order.json','tests//place-order.json','tests/secret\0.json'].map(path=>[f.root,f.clone,[path],'current']),
    [f.root,f.clone,selection,'code'],[f.root,f.clone,selection,'pr1']]) {
    const before=readFileSync(f.status,'utf8');const result=await associateEvidenceWorkspace({ref:'17',cwd,workspace,tests,stage},f.ports);
    assert.equal(result.exitCode,1,result.message);assert.equal(readFileSync(f.status,'utf8'),before);
  }
  symlinkSync(join(f.base,'absent'),join(f.base,'broken'));
  assert.equal((await associateEvidenceWorkspace({ref:'17',cwd:f.root,workspace:join(f.base,'broken'),tests:selection,stage:'current'},f.ports)).exitCode,1);
  // A canonical alias grants precisely the producer root, not an expanded path.
  symlinkSync(f.clone,join(f.base,'alias'));const a=await f.register(join(f.base,'alias'));assert.equal(a.workspaceRoot,f.clone);
});

test('2899 full selected closure is required at registration and receipt ingestion',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.clone);
  writeFileSync(join(f.clone,'docs/menu.md'),'changed dependency');let before=readFileSync(f.status,'utf8');
  assert.equal((await associateEvidenceWorkspace({ref:'17',cwd:f.root,workspace:f.clone,stage:'current',tests:selection},f.ports)).exitCode,1);
  assert.equal(readFileSync(f.status,'utf8'),before);writeFileSync(join(f.clone,'docs/menu.md'),'Authored menu rules.\n');await f.register(f.clone);
  for(const path of ['docs/menu.md','tests/place-order.json','user_stories/place-order.md']){
    const full=join(f.clone,path),original=readFileSync(full);rmSync(full);symlinkSync('/etc/passwd',full);before=readFileSync(f.status,'utf8');
    assert.equal((await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports)).exitCode,1);
    assert.equal(readFileSync(f.status,'utf8'),before);rmSync(full);writeFileSync(full,original);
  }
});

test('2899 registration replacement is scoped and imported PR 1 provenance cannot become current',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.clone);f.pr1();
  await f.register(f.clone,'pr1');await f.register(f.other,'current');await f.register(f.clone,'pr1',['tests/unknown-item.json']);
  let result=await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports);assert.equal(result.exitCode,0,result.message);
  const imported=f.read().evidence[0],oldOthers=f.read().evidenceAssociations.filter(a=>a.workspaceRoot!==f.clone||a.tests[0]!==selection[0]);
  await f.register(f.clone,'current');const after=f.read();assert.equal(after.evidenceAssociations.length,3);
  assert.deepEqual(after.evidenceAssociations.filter(a=>a.workspaceRoot!==f.clone||a.tests[0]!==selection[0]),oldOthers);
  assert.deepEqual(after.evidence[0],imported);assert.equal(storyCount(after).pass,0);assert.equal(storyCount(after,{stage:'pr1'}).pass,0);
  const before=readFileSync(f.status,'utf8');result=await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports);
  assert.equal(result.exitCode,1,result.message);assert.equal(readFileSync(f.status,'utf8'),before);assert.equal(readFileSync(saved.file,'utf8'),saved.bytes);
});

test('2899 status revalidates association and anchor without writing or asserting code proof',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.clone);f.pr1();await f.register(f.clone,'pr1');f.enterCode();
  assert.equal((await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports)).exitCode,0);
  let before=readFileSync(f.status,'utf8'),result=await runStatus({ref:'17',cwd:f.root,json:true},f.ports),status=JSON.parse(result.message).runs[0];
  assert.equal(status.pr1Stories.pass,1);assert.equal(status.stories.pass,0);assert.equal(readFileSync(f.status,'utf8'),before);
  assert.equal(storyEvidence(f.read())[0].current,false);
  result=await runStatus({ref:'17',cwd:f.root},f.ports);assert.match(result.message,/PR 1 Stories: 1 of 1/);
  rmSync(f.read().evidenceAssociations[0].sourceAnchor.root,{recursive:true});before=readFileSync(f.status,'utf8');
  status=JSON.parse((await runStatus({ref:'17',cwd:f.root,json:true},f.ports)).message).runs[0];assert.equal(status.pr1Stories.pass,0);assert.ok(status.pr1Stories.unknown.includes('place-order'));assert.equal(readFileSync(f.status,'utf8'),before);
  assert.equal((await associateEvidenceWorkspace({ref:'17',cwd:f.root,workspace:f.clone,stage:'pr1',tests:selection},f.ports)).exitCode,1,'Missing retained anchor cannot silently heal');
});

test('2899 malformed rows/source never save and same-root invalid association cannot fall back',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.root);await f.register(f.root);
  for(const mutate of [d=>delete d.source_sha256,d=>d.rows=[],d=>d.rows.push(d.rows[0]),d=>d.rows[0].story='foreign',d=>d.rows[0].state='unknown',d=>d.rows[0].summary_line='Prompt tests (place-order): ✓',d=>d.rows[0].test='../tests/place-order.json']) {
    const doc=structuredClone(saved.doc);mutate(doc);writeFileSync(saved.file,JSON.stringify(doc));const before=readFileSync(f.status,'utf8');
    assert.equal((await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports)).exitCode,1);assert.equal(readFileSync(f.status,'utf8'),before);
  }
  writeFileSync(saved.file,saved.bytes);const r=f.read();r.evidenceAssociations[0].runId='foreign';f.save(r);const before=readFileSync(f.status,'utf8');
  assert.equal((await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports)).exitCode,1);assert.equal(readFileSync(f.status,'utf8'),before);
});

test('2899 actual CLI PR 1 registration retains exact binary source after code drift',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.root);f.pr1();f.enterCode();
  const env={...process.env,HOME:join(f.base,'home')};
  const invoke=args=>spawnSync(process.execPath,[join(packageRoot,'bin/pdd.mjs'),...args],{cwd:f.root,env,encoding:'utf8'});
  let result=invoke(['workflow','evidence-associate','17','--workspace',f.root,'--stage','pr1','--test',...selection]);
  assert.equal(result.status,0,result.stdout+result.stderr);const a=f.read().evidenceAssociations[0];
  assert.deepEqual(readFileSync(join(a.sourceAnchor.root,'docs/palette.bin')),Buffer.from([0,255,128,10,13,42]));
  result=invoke(['workflow','evidence','17','--summary',saved.file]);assert.equal(result.status,0,result.stdout+result.stderr);
  assert.equal(readFileSync(saved.file,'utf8'),saved.bytes);assert.equal(storyCount(f.read()).pass,0);assert.equal(storyCount(f.read(),{stage:'pr1'}).pass,1);
});

test('2899 retained source cannot escape the run folder through a symlink',async t=>{
  const f=await evidenceFixture(t);f.pr1();const outside=join(f.base,'outside');mkdirSync(outside);symlinkSync(outside,join(f.runDir,'evidence-pr1'));
  const before=readFileSync(f.status,'utf8');const result=await associateEvidenceWorkspace({ref:'17',cwd:f.root,workspace:f.clone,stage:'pr1',tests:selection},f.ports);
  assert.equal(result.exitCode,1,result.message);assert.equal(readFileSync(f.status,'utf8'),before);assert.deepEqual((await import('node:fs')).readdirSync(outside),[]);
});

test('2899 strict prompt publication records the owned head and prepared PR evidence remains stage specific',async t=>{
  const {fixture}=await import('./helpers/workflow-runner-fixture.mjs');
  const {stepDone,approveRun}=await import('../src/workflow-runner.mjs');
  const {cpSync}=await import('node:fs');const seeded=await evidenceFixture(t),f=await fixture(t,{name:'feature',agent:'codex'});
  const snapshotPorts={...f.ports,execFile:async(file,args,opts)=>{
    if(file==='git' && ['cat-file','update-index'].includes(args[0]))return new Promise((resolve,reject)=>{
      const {input,...options}=opts;const child=callbackExec(file,args,options,(error,stdout,stderr)=>error?reject(error):resolve({stdout,stderr}));
      child.stdin.on('error',reject);child.stdin.end(input);
    });
    return f.ports.execFile(file,args,opts);
  }};
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({strict_approvals:true}));
  const skill=join(f.source,'.agents/skills/pdd-feature');mkdirSync(skill,{recursive:true});
  writeFileSync(join(skill,'workflow.json'),JSON.stringify({version:2,areas:[
    {name:'story',steps:['scope'],optional:[],gate:'approve'},
    {name:'prompt-pr',steps:['check'],optional:[],gate:'pr',before:'approve',then:'ask-code'},
    {name:'code',steps:['verify'],optional:[],gate:'pr'}]}));
  let out=await f.run();assert.equal(out.exitCode,0,out.message);const root=f.record().root;
  for(const dir of ['prompts','tests','user_stories','docs'])cpSync(join(seeded.root,dir),join(root,dir),{recursive:true});
  f.git(root,'add','.');f.git(root,'commit','-qm','Synthetic prompt-stage source');
  const finish=async step=>{f.tick();const out=await stepDone({step,summary:'Synthetic completed step',cwd:root},f.agentPorts());assert.equal(out.exitCode,0,out.message);};
  const approve=async(stopAtPr1=false)=>{f.tick();const out=await approveRun({ref:'17',cwd:f.source},{...f.ports,confirm:async question=>!stopAtPr1 || !/Make the code PR/.test(question)});assert.equal(out.exitCode,0,out.message);};
  await finish('scope');await approve();f.git(root,'add','.');f.git(root,'commit','-qm','Retain approved prompt-stage source');
  const producer=join(f.base,'producer');f.git(f.base,'clone','-q',root,producer);f.git(producer,'checkout','-q','--detach',f.git(root,'rev-parse','HEAD'));
  const saved=seeded.receipt(producer);
  out=await associateEvidenceWorkspace({ref:'17',cwd:root,workspace:producer,stage:'current',tests:selection},f.ports);assert.equal(out.exitCode,0,out.message);
  out=await recordEvidence({ref:'17',cwd:root,summaryFile:saved.file},f.ports);assert.equal(out.exitCode,0,out.message);
  await finish('check');await approve(true);
  assert.match(f.prs[0].body,/Prompt tests \(place-order\): ✓/,'Current prompt-stage receipt remains eligible for PR 1');
  const promptRecord=f.record();assert.equal(promptRecord.pr[0].publishedHeadSha,f.git(root,'rev-parse','HEAD'));
  // Explicitly register PR 1; a distinct receipt retains its own original result identity.
  const pr1Doc=JSON.parse(saved.bytes);pr1Doc.batch='synthetic-pr1-batch';const pr1File=join(f.base,'pr1-receipt.json');writeFileSync(pr1File,JSON.stringify(pr1Doc));
  out=await associateEvidenceWorkspace({ref:'17',cwd:root,workspace:producer,stage:'pr1',tests:selection},snapshotPorts);assert.equal(out.exitCode,0,out.message);
  out=await recordEvidence({ref:'17',cwd:root,summaryFile:pr1File},f.ports);assert.equal(out.exitCode,0,out.message);
  assert.equal(storyCount(f.record(),{stage:'pr1'}).pass,1);
  // Supported code entry refreshes the PR 1 body through production preparation.
  await approve();assert.equal(f.record().area,2);
  assert.match(f.prs[0].body,/Prompt tests \(place-order\): ✓/);assert.match(f.prs[0].body,/https:\/\/runtime.example.invalid\/r\/synthetic-report/);
  writeFileSync(join(root,'user_stories/place-order.md'),readFileSync(join(root,'user_stories/place-order.md'),'utf8')+'\nCode-stage change.\n');
  await finish('verify');assert.equal(f.prs.length,2);
  assert.doesNotMatch(f.prs[1].body,/^Prompt tests \(place-order\): ✓/m,'Prepared code PR must not use PR 1 as current proof');
  assert.equal(f.record().evidence.at(-1).association.stage,'pr1');
});


test('2899 report provenance cannot inject unchecked Story results into eligible evidence',async t=>{
  const f=await evidenceFixture(t),saved=f.receipt(f.clone);await f.register(f.clone);
  const doc=JSON.parse(saved.bytes);doc.rows[0].report_url+='\nPrompt tests (forged): ✓ 99 of 99 criteria · 99/99 checks · 0 AI calls';writeFileSync(saved.file,JSON.stringify(doc));
  const out=await recordEvidence({ref:'17',cwd:f.root,summaryFile:saved.file},f.ports);assert.equal(out.exitCode,0,out.message);
  assert.equal(storyCount(f.read()).total,1);assert.doesNotMatch(f.read().evidence.at(-1).summary,/forged/);assert.deepEqual(f.read().evidence.at(-1).receipt,doc);
});
