import test from 'node:test';
import assert from 'node:assert/strict';
import * as nativeFs from 'node:fs';
import {mkdirSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {parseArgv} from '../src/argument-parser.mjs';
import {runPdd, renderHelp} from '../src/pdd-cli.mjs';
import {renderCompletion} from '../src/completion.mjs';
import {startRun, stepDone, approveRun} from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

// Native replay of the approved .native.md cases. No Runtime binding or live
// consent/publication is implied: words and all external effects are synthetic.
const words = 'Synthetic person: publish drafts and stop before code.';
const ok = out => assert.equal(out.exitCode, 0, out.message);
const snapshot = f => ({record:f.record(), prs:structuredClone(f.prs), pushes:structuredClone(f.pushes), chats:f.herdr.calls.length});
async function world(t, {name='bug'}={}) {
  const f = await fixture(t,{name,agent:'codex'});
  const config = join(f.base,'dummy-codex'); mkdirSync(config);
  // Explicit dummy profile and a closed environment; native context is not inherited.
  f.ports.env = {HOME:f.ports.env.HOME,CODEX_HOME:config};
  f.creates=[]; f.effects=[];
  const exec=f.ports.execFile;
  f.ports.execFile=async(file,args,opts)=>{
    const effect = file==='git' && ['checkout','branch','push'].includes(args[0])
      || file==='gh' && args[0]==='pr' && ['create','edit'].includes(args[1]);
    if(effect) f.effects.push({file,args:[...args],saved:f.record()});
    const result=await exec(file,args,opts);
    if(file==='git' && args[0]==='push') {
      const [from,to]=args[2].split(':');
      for(const pr of f.prs)if(to===`refs/heads/${pr.headRefName}`)pr.headRefOid=f.git(opts.cwd,'rev-parse',from);
    }
    if(file==='gh' && args[1]==='view' && args.at(-1)==='number,url,isDraft') {
      const pr=f.prs.find(pr=>pr.url===args[2]);
      return {stdout:JSON.stringify({number:pr?.number,url:pr?.url,isDraft:pr?.isDraft})};
    }
    if(file==='gh' && args[1]==='create') {
      f.creates.push([...args]);
      if(f.prs.at(-1)) f.prs.at(-1).isDraft=args.includes('--draft');
    }
    return result;
  };
  f.start=extra=>startRun({name,issue:'17',agent:'codex',cwd:f.source,packageRoot,...extra},f.ports);
  f.done=async(step)=>{f.tick();const out=await stepDone({step,summary:`Synthetic ${step}`,cwd:f.record().root},f.agentPorts());ok(out);return out;};
  f.approve=extra=>approveRun({ref:'17',cwd:f.source,said:words,...extra},f.agentPorts());
  f.commit=()=>{const r=f.record();writeFileSync(join(r.root,'value.mjs'),`export const value = ${f.clock};\n`);f.git(r.root,'add','.');f.git(r.root,'commit','-qm','Synthetic change');};
  f.story=async()=>{await f.done('reproduce');f.commit();await f.done('prompt-story');};
  f.prePr=async()=>{await f.story();ok(await f.approve());await f.done('check');await f.done('try');};
  return f;
}

test('N1/L2: actual parser, quiet alias, help/completion and CLI dispatch expose Boolean draft',async()=>{
  for(const verb of ['run','start']) {
    assert.equal(parseArgv(['workflow',verb,'bug','17','--draft']).options['--draft'],true);
    assert.equal(parseArgv(['workflow',verb,'bug','17']).options['--draft'],undefined);
  }
  assert.equal(parseArgv(['workflow','approve','17','--draft','--said',words]).options['--draft'],true);
  for(const argv of [
    ['workflow','run','bug','17','--draft','--draft'],['workflow','run','bug','17','--draft-only'],
    ['workflow','run','bug','17','--draft','true'],['workflow','approve','17','--draft','--draft'],
    ['workflow','approve','17','--draft','--said'],['workflow','approve','17','--draft','--said',' '],
    ['workflow','approve','17','--draft','extra'],
  ])assert.throws(()=>parseArgv(argv));
  assert.match(renderHelp(['workflow','run']),/\[--draft\]/);
  assert.match(renderHelp(['workflow','approve']),/\[--draft\]/);
  for(const shell of ['bash','zsh'])assert.match(renderCompletion(shell),/--draft/);
  for(const verb of ['run','start','approve'])for(const draft of [false,true]) {
    const calls=[],stdout={write(){}},stderr={write(){}},env={HOME:'/dummy',CODEX_HOME:'/dummy/codex'};
    const method=verb==='approve'?'approveRun':'startRun';
    const argv=verb==='approve'?['workflow',verb,'17','--said',words]:['workflow',verb,'bug','17'];
    if(draft)argv.push('--draft');
    const code=await runPdd(argv,{stdout,stderr,cwd:'/dummy',packageRoot,env,
      workflowAgents:{checkWorkflowAgents:async()=>({ok:true,agent:'codex',message:'synthetic'})},
      pathDiagnostic:async()=>[], workflowRunner:{[method]:async input=>{calls.push(input);return {exitCode:0,message:'synthetic'};}}});
    assert.equal(code,0);assert.equal(calls.length,1);
    assert.equal(calls[0].draft,draft?true:undefined);
  }
});

test('N2/N3/N7: saved draft precedes startup, survives reload, PR1 stops, separate code approval produces stacked draft PR2',async t=>{
  const f=await world(t);const herdr=f.ports.herdr;let startup;
  f.ports.herdr=async args=>{startup??=f.record().draft;return herdr(args);};
  ok(await f.start({draft:true}));assert.equal(startup,true);assert.equal(f.record().draft,true);assert.equal(f.prs.length,0);
  await f.prePr();ok(await f.approve({draft:false}));
  let r=f.record();assert.equal(r.draft,true);assert.equal(r.gate.kind,'ask-code');assert.equal(r.chats.length,2);assert.equal(f.prs.length,1);
  assert.equal(f.creates[0].includes('--draft'),true);assert.equal(f.prs[0].isDraft,true);
  assert.equal(f.effects.filter(e=>e.file==='git'&&e.args[0]==='checkout').length,0,'PR1 approval cannot start code branch');
  ok(await f.approve());r=f.record();assert.equal(r.draft,true);assert.equal(r.areas[r.area].name,'code');assert.equal(r.chats.length,3);
  f.commit();for(const step of ['build','verify','formal','review'])await f.done(step);
  r=f.record();assert.equal(r.draft,true);assert.equal(f.creates.length,2);assert.ok(f.creates.every(args=>args.includes('--draft')));
  assert.equal(f.prs[1].baseRefName,f.prs[0].headRefName);assert.equal(r.pr.length,2);
  for(const e of f.effects)assert.equal(e.saved.draft,true,'policy durable before effects');
});

test('N4/N5: legitimate story and small-change gates strengthen policy before the next chat and publication',async t=>{
  for(const name of ['bug','small-change']) {
    const f=await world(t,{name});ok(await f.start());assert.equal(f.record().draft,false);
    if(name==='bug')await f.story();else await f.done('scope');
    const old=f.record();ok(await f.approve({draft:true}));
    const r=f.record();assert.equal(r.draft,true);assert.equal(r.decisions.length,old.decisions.length+1);assert.equal(r.decisions.at(-1).gateId,old.gate.id);
    assert.equal(r.decisions.at(-1).evidence.words,words);
    if(name==='small-change') {f.commit();for(const step of ['change','verify','formal'])await f.done(step);assert.equal(f.prs.length,1);assert.equal(f.prs[0].isDraft,true);}
  }
});

test('N5/N6: prePR strengthening saves approval then policy before publication; same gate retry reuses decision/evidence/time',async t=>{
  const f=await world(t);ok(await f.start());await f.prePr();
  const gate=f.record().gate;f.createError='GraphQL: validation failed (createPullRequest)';
  assert.equal((await f.approve({draft:true})).exitCode,1);
  const first=f.record(),decision=first.decisions.at(-1);assert.equal(first.draft,true);assert.equal(first.gate.id,gate.id);
  const publication=f.effects.find(e=>e.file==='gh'&&e.args[1]==='create');
  assert.equal(publication.saved.draft,true);assert.deepEqual(publication.saved.decisions.at(-1),decision);
  f.tick();ok(await f.approve());const after=f.record();
  assert.deepEqual(after.decisions,first.decisions);assert.deepEqual(after.approvalRecord,first.approvalRecord);
  assert.equal(after.draft,true);assert.equal(f.prs.length,1);assert.equal(f.pushes.length,1,'known rejection retry reuses already-pushed SHA');
});

test('N7: omitted/false start and absent legacy policy preserve ready PR readback without isDraft',async t=>{
  for(const mode of ['omitted','false','legacy']) {
    const f=await world(t,{name:'small-change'});ok(await f.start(mode==='false'?{draft:false}:{}));assert.equal(f.record().draft,false);
    if(mode==='legacy'){const r=f.record();delete r.draft;writeRun(r,f.ports);}
    await f.done('scope');ok(await f.approve({draft:false}));f.commit();
    const exec=f.ports.execFile;f.ports.execFile=async(file,args,opts)=>{
      const result=await exec(file,args,opts);
    if(file==='git' && args[0]==='push') {
      const [from,to]=args[2].split(':');
      for(const pr of f.prs)if(to===`refs/heads/${pr.headRefName}`)pr.headRefOid=f.git(opts.cwd,'rev-parse',from);
    }
    if(file==='gh' && args[1]==='view' && args.at(-1)==='number,url,isDraft') {
      const pr=f.prs.find(pr=>pr.url===args[2]);
      return {stdout:JSON.stringify({number:pr?.number,url:pr?.url,isDraft:pr?.isDraft})};
    }
      if(file==='gh'&&args[1]==='list')return {stdout:JSON.stringify(JSON.parse(result.stdout).map(({isDraft,...row})=>row))};
      return result;
    };
    for(const step of ['change','verify','formal'])await f.done(step);
    assert.equal(f.prs.length,1);assert.equal(f.creates[0].includes('--draft'),false);assert.equal(f.prs[0].isDraft,false);
  }
});

for(const value of [null,0,1,'','true',{}])test(`L1: nonboolean incoming and saved draft ${JSON.stringify(value)} refuses without progress`,async t=>{
  const f=await world(t);let calls=0;const exec=f.ports.execFile;
  f.ports.execFile=async(...args)=>{calls++;return exec(...args);};
  assert.equal((await f.start({draft:value})).exitCode,1);assert.equal(calls,0);
  ok(await f.start());await f.story();let before=snapshot(f);
  assert.equal((await f.approve({draft:value})).exitCode,1);assert.deepEqual(snapshot(f),before);
  const r=f.record();r.draft=value;writeRun(r,f.ports);before=snapshot(f);
  assert.equal((await f.approve({draft:true})).exitCode,1);assert.deepEqual(snapshot(f),before);
  assert.equal((await f.start({draft:true})).exitCode,1);assert.deepEqual(snapshot(f),before);
});

for(const kind of ['missing-review','stale-review','changed-selection','missing-steps','strict','invalid-config','no-gate-terminal'])test(`L5: ${kind} never adopts policy or approval`,async t=>{
  const f=await world(t);ok(await f.start());await f.story();
  if(kind==='missing-review'){const r=f.record();delete r.gate.promptSnapshot;writeRun(r,f.ports);}
  if(kind==='stale-review'){const r=f.record();r.gate.promptSnapshot=[{path:'old.prompt.md',proseSha256:'a'.repeat(64)}];writeRun(r,f.ports);}
  if(kind==='changed-selection')writeFileSync(join(f.record().root,'new.prompt.md'),'New selection');
  if(kind==='missing-steps'){const r=f.record();delete r.done['reproduce'];writeRun(r,f.ports);}
  if(kind==='strict')writeFileSync(join(f.source,'pdd.json'),JSON.stringify({strict_approvals:true}));
  if(kind==='invalid-config')writeFileSync(join(f.source,'pdd.json'),'{');
  if(kind==='no-gate-terminal'){const r=f.record();r.gate=null;writeRun(r,f.ports);}
  const before=snapshot(f),out=kind==='no-gate-terminal'
    ? await approveRun({ref:'17',cwd:f.source,draft:true},f.ports):await f.approve({draft:true});
  assert.equal(out.exitCode,1,out.message);assert.deepEqual(snapshot(f),before);
});

test('L6: old distinct-gate decision cannot replace missing review; fresh review and normal approval allow repeated nonblank words',async t=>{
  const f=await world(t);ok(await f.start());await f.prePr();f.createError='GraphQL: validation failed (createPullRequest)';
  assert.equal((await f.approve()).exitCode,1);const prior=f.record().decisions.at(-1);
  const reopened=f.record();reopened.gate={...reopened.gate,id:'synthetic-reopened-gate'};delete reopened.gate.promptSnapshot;writeRun(reopened,f.ports);
  const before=snapshot(f);const out=await f.approve({draft:true});assert.equal(out.exitCode,1);assert.match(out.message,/no saved review/);assert.deepEqual(snapshot(f),before);
  await f.done('try');const reviewed=f.record().gate;assert.notEqual(reviewed.id,prior.gateId);assert.deepEqual(reviewed.promptSnapshot,[]);
  ok(await f.approve({draft:true}));const r=f.record();assert.deepEqual(r.decisions.at(-2),prior);assert.equal(r.decisions.at(-1).gateId,reviewed.id);assert.notEqual(r.decisions.at(-1).gateId,prior.gateId);
  assert.equal(r.decisions.at(-1).text,prior.text);assert.equal(r.draft,true);
});

for(const race of ['cancel','replace','gate'])test(`L7: ${race} during review validation prevents adoption/effects`,async t=>{
  const f=await world(t);ok(await f.start());await f.story();let raced=false,newest;
  const exec=f.ports.execFile;
  f.ports.execFile=async(file,args,opts)=>{
    if(!raced&&file==='git'&&args[0]==='diff') {
      raced=true;newest=f.record();
      if(race==='cancel')newest.state='cancelled';
      if(race==='replace')newest.runId='synthetic-new-owner';
      if(race==='gate')newest.gate.id='synthetic-new-gate';
      writeRun(newest,f.ports);
    }
    return exec(file,args,opts);
  };
  const out=await f.approve({draft:true});assert.equal(out.exitCode,1,out.message);assert.equal(raced,true);
  assert.deepEqual(f.record(),newest);assert.equal(f.prs.length,0);assert.equal(f.effects.length,0);
});

test('L7/E4: failed policy persistence retains legitimate approval and stops before effects',async t=>{
  const f=await world(t);ok(await f.start());await f.story();
  const before=f.record();let rejected=false;
  const out=await approveRun({ref:'17',cwd:f.source,said:words,draft:true},f.agentPorts({runFiles:{writeFileSync(path,data,options){
    if(String(path).includes('.status.json.')&&JSON.parse(data).draft===true){rejected=true;throw Error('synthetic policy persistence failure');}
    return writeFileSync(path,data,options);
  }}}));
  assert.equal(out.exitCode,1);assert.equal(rejected,true);assert.match(out.message,/not saved/);
  const after=f.record();assert.equal(after.draft,false);assert.equal(after.area,before.area);assert.deepEqual(after.gate,before.gate);
  assert.equal(after.decisions.length,before.decisions.length+1);assert.equal(after.decisions.at(-1).evidence.words,words);
  assert.equal(f.effects.length,0);assert.equal(after.chats.length,before.chats.length);
});

test('L8: start --draft cannot replace nondraft active run; published selected stage refuses strengthening',async t=>{
  const f=await world(t);ok(await f.start());const before=snapshot(f);
  const again=await f.start({draft:true});assert.equal(again.exitCode,1);assert.match(again.message,/workflow approve 17 --draft/);assert.deepEqual(snapshot(f),before);
  await f.prePr();ok(await f.approve());assert.equal(f.record().gate.kind,'ask-code');const published=snapshot(f);
  const out=await f.approve({draft:true});assert.equal(out.exitCode,1);assert.deepEqual(snapshot(f),published);assert.equal(f.prs[0].isDraft,false);
});


test('N3: merged former draft PR1 retains ordinary saved-base code entry and draft PR2',async t=>{
  const f=await world(t);ok(await f.start({draft:true}));await f.prePr();ok(await f.approve());
  const first=f.prs[0];first.isDraft=false;f.mergedNumbers.push(first.number);
  ok(await f.approve());const code=f.record();assert.equal(code.prBase,code.baseBranch);assert.equal(code.draft,true);
  assert.equal(f.git(code.root,'rev-parse','HEAD'),first.headRefOid);
  f.commit();for(const step of ['build','verify','formal','review'])await f.done(step);
  assert.equal(f.prs[1].baseRefName,code.baseBranch);assert.equal(f.prs[1].isDraft,true);
});

test('E4: failed approval journal save refuses policy and retains the selected gate',async t=>{
  const f=await world(t);ok(await f.start());await f.story();const before=snapshot(f);
  const out=await approveRun({ref:'17',cwd:f.source,said:words,draft:true},f.agentPorts({fs:{...nativeFs,writeFileSync(path,data,options){
    if(String(path).includes('/.approvals.'))throw Error('synthetic journal failure');
    return nativeFs.writeFileSync(path,data,options);
  }}}));
  assert.equal(out.exitCode,1);assert.match(out.message,/Approval failed/);assert.deepEqual(snapshot(f),before);
});

for(const action of ['done-update','code-sync'])test(`L4 runner ${action}: existing ready PR is unchanged before draft refusal`,async t=>{
  const f=await world(t);ok(await f.start({draft:true}));await f.prePr();ok(await f.approve());
  f.prs[0].isDraft=false;f.commit();const before={prs:structuredClone(f.prs),pushes:f.pushes.length,edits:f.edits.length,chats:f.record().chats.length};
  const out=action==='done-update'
    ? await stepDone({step:'try',summary:'Synthetic update to an existing PR',cwd:f.record().root},f.agentPorts())
    : await f.approve();
  assert.equal(out.exitCode,1,out.message);
  assert.equal(f.pushes.length,before.pushes,'existing ready PR receives no push');
  assert.equal(f.edits.length,before.edits,'existing ready PR receives no body edit');
  assert.deepEqual(f.prs,before.prs);assert.equal(f.record().chats.length,before.chats);assert.equal(f.creates.length,1);
});


for(const action of ['done-update','code-sync'])test(`L4 runner positive ${action}: existing draft accepts new committed head without duplicate`,async t=>{
  const f=await world(t);ok(await f.start({draft:true}));await f.prePr();ok(await f.approve());
  f.commit();const head=f.git(f.record().root,'rev-parse','HEAD'),pushes=f.pushes.length;
  const out=action==='done-update'
    ? await stepDone({step:'try',summary:'Synthetic draft update',cwd:f.record().root},f.agentPorts())
    : await f.approve();
  ok(out);assert.equal(f.pushes.length,pushes+1);assert.equal(f.prs[0].headRefOid,head);assert.equal(f.prs[0].isDraft,true);assert.equal(f.creates.length,1);
  if(action==='code-sync')assert.equal(f.record().areas[f.record().area].name,'code');
});

for(const failure of ['missing','malformed','unavailable','number','url','repository'])test(`L4 runner prewrite ${failure} readback refuses before auto-commit/push/edit`,async t=>{
  const f=await world(t);ok(await f.start({draft:true}));await f.prePr();ok(await f.approve());
  writeFileSync(join(f.record().root,'value.mjs'),'export const value = "uncommitted update";\n');
  const head=f.git(f.record().root,'rev-parse','HEAD'),before=structuredClone(f.prs),pushes=f.pushes.length,edits=f.edits.length;
  const exec=f.ports.execFile;
  f.ports.execFile=async(file,args,opts)=>{
    if(file==='gh'&&args[1]==='view'&&args.at(-1)==='number,url,isDraft'){
      if(failure==='unavailable')throw Error('Synthetic unavailable read');
      if(failure==='malformed')return {stdout:'{'};
      const pr=f.prs[0];return {stdout:JSON.stringify({number:failure==='number'?999:pr.number,
        url:failure==='url'?pr.url+'?wrong':failure==='repository'?'https://github.com/foreign/project/pull/23':pr.url,
        ...(failure==='missing'?{}:{isDraft:true})})};
    }
    return exec(file,args,opts);
  };
  const out=await stepDone({step:'try',summary:'Synthetic refused update',cwd:f.record().root},f.agentPorts());
  assert.equal(out.exitCode,1);assert.equal(f.git(f.record().root,'rev-parse','HEAD'),head);
  assert.equal(f.pushes.length,pushes);assert.equal(f.edits.length,edits);assert.deepEqual(f.prs,before);assert.equal(f.creates.length,1);
});
