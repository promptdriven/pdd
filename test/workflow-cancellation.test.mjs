import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { cancelRun, startRun, stepDone, approveRun } from '../src/workflow-runner.mjs';
import { allocateIssueWorktree, releaseIssueClaim } from '../src/workflow-worktree.mjs';
import { readRun, resolveRun, writeRun, allRuns } from '../src/workflow-runs.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { cancellationFixture, packageRoot } from './helpers/cancellation-fixture.mjs';

const bytes = file => readFileSync(file, 'utf8');
const input = f => ({ ref: f.old.runId, cwd: f.source });
const preserved = run => {
  const copy = structuredClone(run);
  for (const field of ['state','cancelled','gate','journalSeq','updatedAt','stage','steps','waitingFor','resumeDecisions','waitingDecision','stageAgent','runDir']) delete copy[field];
  return copy;
};

// Story AC1: absent/declined person confirmation forbids even a stop request.
test('CANCEL1: decline and closed input preserve real status, claim and files byte for byte', async t => {
  const f = await cancellationFixture(t), status = bytes(join(f.runDir, 'status.json')), claim = bytes(f.claim);
  for (const answer of [false, undefined]) {
    f.answer = answer;
    for (const request of [() => cancelRun(input(f), f.ports), () => f.start({ name: 'feature', replace: f.old.runId })]) {
      const out = await request(); assert.equal(out.exitCode, 0, out.message);
      assert.equal(bytes(join(f.runDir, 'status.json')), status); assert.equal(bytes(f.claim), claim);
      assert.ok(f.events.every(event => event[0] === 'confirm'));
    }
  }
});

// Story AC2/3/7 and order rule: real file save precedes exact claim release;
// archival, a fresh Git worktree and a confirmed start follow it.
test('CANCEL2: replacement preserves every unrelated field/file/PR and old identity, and late done cannot touch the new run', async t => {
  const f = await cancellationFixture(t), old = f.old;
  f.ports.releaseIssueClaim = async (request, ports) => {
    f.events.push(['release', request.runId]);
    const saved = f.read(); assert.equal(saved.state, 'cancelled'); assert.equal(saved.stage, null); assert.equal(saved.stageAgent, null);
    assert.equal(saved.journalSeq, old.journalSeq + 1); assert.deepEqual(saved.cancelled, { state: 'cancelled', at: 600000 });
    assert.deepEqual(preserved(saved), preserved(old));
    const index = JSON.parse(bytes(join(f.stateDir, 'runs.json')));
    assert.equal(index.runs.find(run => run.runDir === f.runDir).state, 'cancelled');
    return releaseIssueClaim(request, ports);
  };
  f.ports.allocateIssueWorktree = async (request, ports) => {
    f.events.push(['allocate', request.runId]); assert.equal(existsSync(f.claim), false);
    assert.equal(f.read().state, 'cancelled'); return allocateIssueWorktree(request, ports);
  };
  const out = await f.start({ name: 'feature', replace: old.runId }); assert.equal(out.exitCode, 0, out.message);
  const fresh = f.read(), archived = `${f.runDir}-cancelled-${old.runId.slice(0,8)}`, history = readRun(archived);
  assert.notEqual(fresh.runId, old.runId); assert.notEqual(fresh.root, old.root); assert.notEqual(fresh.branch, old.branch);
  assert.equal(JSON.parse(bytes(f.claim)).runId, fresh.runId); assert.equal(fresh.chats.length, 1);
  assert.equal(fresh.previous.at(-1).runId, old.runId); assert.equal(history.state, 'cancelled');
  assert.deepEqual(preserved(history), preserved(old));
  for (const [file, expected] of [[join(old.root,'work.txt'),'keep original work\n'],[join(old.root,'uncommitted.txt'),'keep uncommitted work\n'],[join(archived,'journal.md'),'keep journal bytes\n'],[join(archived,'evidence.txt'),'keep artifact bytes\n']]) assert.equal(bytes(file), expected);
  assert.ok(f.git('show-ref','--verify',`refs/heads/${old.branch}`));
  assert.equal((await resolveRun(old.runId, {cwd:f.source}, f.ports)).run.runDir, archived);
  assert.equal(allRuns({cancelled:true},f.ports).find(run=>run.runId===old.runId).state,'cancelled');
  const events = f.events.map(e=>e[0]); assert.ok(events.indexOf('confirm') < events.indexOf('herdr')); assert.ok(events.indexOf('herdr') < events.indexOf('save'));
  assert.ok(events.indexOf('save') < events.indexOf('release')); assert.ok(events.indexOf('release') < events.indexOf('allocate')); assert.ok(events.indexOf('allocate') < events.indexOf('start'));
  const before = bytes(join(f.runDir,'status.json')), claim = bytes(f.claim), journal = history.journalSeq;
  const late = await stepDone({step:'scope',summary:'late completion',cwd:old.root},f.ports); assert.match(late.message,/cancelled.*Stop/s);
  assert.equal((await cancelRun({ref:old.runId,cwd:f.source},f.ports)).exitCode,0);
  assert.equal(bytes(join(f.runDir,'status.json')),before); assert.equal(bytes(f.claim),claim); assert.equal(readRun(archived).journalSeq,journal);
  const stale = await f.start({name:'bug',replace:old.runId}); assert.equal(stale.exitCode,1); assert.equal(bytes(f.claim),claim);
});

// A stop port failure and both persistence/release failures must keep custody
// and never call allocation, even after confirmation.
for (const failure of ['unknown-stop','thrown-stop','save','release','allocation','startup']) {
  test(`CANCEL3: ${failure} preserves custody and reports the real failure`,async t=>{
    const f=await cancellationFixture(t), before=bytes(join(f.runDir,'status.json')), claim=bytes(f.claim);
    if(failure==='unknown-stop') f.ports.stopChats=async()=>({stopped:false,warnings:['inspection unavailable']});
    if(failure==='thrown-stop') f.ports.stopChats=async()=>{throw Error('lost stop receipt');};
    if(failure==='save') f.ports.writeRun=()=>{throw Error('disk refused save');};
    if(failure==='release') f.ports.releaseIssueClaim=async()=>({state:'recovery_required',message:'claim refused release'});
    if(failure==='allocation') f.ports.allocateIssueWorktree=async()=>({state:'recovery_required',message:'allocation unavailable'});
    if(failure==='startup') f.ports.startChat=async()=>{throw Object.assign(Error('startup unavailable'),{code:'server_unavailable'});};
    const out=await f.start({name:'feature',replace:f.old.runId}); assert.equal(out.exitCode,1,out.message);
    if(['unknown-stop','thrown-stop','save'].includes(failure)) {assert.equal(bytes(join(f.runDir,'status.json')),before);assert.equal(bytes(f.claim),claim);}
    if(failure==='release') {assert.equal(f.read().state,'cancelled');assert.equal(bytes(f.claim),claim);}
    if(failure==='allocation') {assert.equal(f.read().state,'cancelled');assert.equal(existsSync(f.claim),false);}
    if(failure==='startup') {assert.notEqual(f.read().runId,f.old.runId);assert.equal(f.read().state,'waiting');assert.equal(JSON.parse(bytes(f.claim)).runId,f.read().runId);}
    assert.equal(bytes(join(f.old.root,'uncommitted.txt')),'keep uncommitted work\n');
    if(failure!=='startup') assert.equal(f.chats.length,1);
  });
}

test('CANCEL4: concurrent replacements have one confirmation, one new allocation and one start',async t=>{
  const f=await cancellationFixture(t);let release,entered;
  const wait=new Promise(r=>{release=r;}), ready=new Promise(r=>{entered=r;});
  f.ports.confirm=async()=>{f.events.push(['confirm']);entered();await wait;return true;};
  const first=f.start({name:'feature',replace:f.old.runId});await ready;
  const second=await f.start({name:'bug',replace:f.old.runId});assert.equal(second.exitCode,1);assert.match(second.message,/custody/);
  const late=await stepDone({step:'scope',summary:'racing completion',cwd:f.old.root},f.ports);assert.equal(late.exitCode,1);
  release();assert.equal((await first).exitCode,0);assert.equal(f.chats.length,2);assert.equal(f.events.filter(e=>e[0]==='confirm').length,1);
});

for(const override of [false,true]) test(`CANCEL5: ${override?'two-step project override':'actual bundled small-change'} retains scope advice at its gate and later refusal`,async t=>{
  const f=await cancellationFixture(t,{override});
  const reason='Scope is too large; use feature instead.';
  const scope=await stepDone({step:'scope',summary:reason,cwd:f.old.root},f.ports);assert.equal(scope.exitCode,0);
  let gate=scope;
  if(override) {assert.equal(f.read().gate,null);gate=await stepDone({step:'change',summary:'Change completed without switching.',cwd:f.old.root},f.ports);}
  assert.equal(f.read().state,'waiting');assert.equal(f.read().gate.area,'plan');
  assert.ok(gate.message.includes(reason));assert.ok(gate.message.includes(`pdd workflow run feature 17 --replace ${f.old.runId}`));
  if(!override) {
    const approved=await approveRun({ref:'17',cwd:f.source},f.ports);assert.equal(approved.exitCode,0,approved.message);
    const change=await stepDone({step:'change',summary:'Change completed.',cwd:f.old.root},f.ports);assert.equal(change.exitCode,0,change.message);
  }
  const refusal=await f.start({name:'bug'});assert.equal(refusal.exitCode,1);assert.ok(refusal.message.includes(reason));
  for(const workflow of ['feature','bug']) assert.ok(refusal.message.includes(`pdd workflow run ${workflow} 17 --replace ${f.old.runId}`));
  assert.equal(f.read().workflow,'small-change');assert.equal(f.read().done.scope.summary,reason);
});

test('CANCEL6: archived duplicate IDs refuse ambiguity, and wrong/missing/cross-issue IDs have no effects',async t=>{
  const f=await cancellationFixture(t), before=bytes(join(f.runDir,'status.json')), claim=bytes(f.claim);
  for(const replace of ['missing-id','wrong-run']) {const out=await f.start({name:'feature',replace});assert.equal(out.exitCode,1);}
  const other={...f.old,runId:'cross-issue',number:18,repo:'other/project',runDir:join(f.commonDir,'pdd/runs/18')};writeRun(other,f.ports);
  assert.equal((await f.start({name:'feature',replace:other.runId})).exitCode,1);
  const duplicate={...f.old,runDir:join(f.commonDir,'pdd/runs/17-cancelled-abcdef12'),state:'cancelled'};writeRun(duplicate,f.ports);
  const ambiguous=await cancelRun(input(f),f.ports);assert.equal(ambiguous.exitCode,1);assert.match(ambiguous.message,/ambiguous/);
  assert.equal(bytes(join(f.runDir,'status.json')),before);assert.equal(bytes(f.claim),claim);assert.equal(f.events.filter(e=>e[0]==='confirm').length,0);
});

test('CANCEL7: parser accepts only the authorized run ID forms before runner dispatch',()=>{
  assert.equal(parseArgv(['workflow','cancel','run-id_1.2']).operands[0],'run-id_1.2');
  for(const ref of ['17','example/project#17','https://github.com/example/project/issues/17']) assert.equal(parseArgv(['workflow','cancel',ref]).operands[0],ref);
  assert.equal(parseArgv(['workflow','run','feature','17','--replace','run-id']).options['--replace'],'run-id');
  for(const args of [['workflow','run','feature','17','--replace'],['workflow','run','feature','17','--replace','x','--replace','y'],['workflow','run','feature','17','--replace','../unsafe'],['workflow','cancel','x','extra'],['workflow','cancel','bad id']]) assert.throws(()=>parseArgv(args),{exitCode:2});
});

test('CANCEL8: public CLI forwards replacement and run ID cancellation exactly once',async()=>{
  const {runPdd}=await import('../src/pdd-cli.mjs');const calls=[];const output={write(){}};
  const workflowRunner={startRun:async input=>{calls.push(['start',input]);return {exitCode:0,message:'started'};},cancelRun:async input=>{calls.push(['cancel',input]);return {exitCode:0,message:'cancelled'};}};
  for(const argv of [['workflow','run','feature','17','--base','alpha','--replace','old-run'],['workflow','cancel','old-run']]) assert.equal(await runPdd(argv,{workflowRunner,cwd:'/project',packageRoot:'/package',stdout:output,stderr:output}),0);
  assert.deepEqual(calls,[['start',{name:'feature',issue:'17',agent:'codex',base:'alpha',replace:'old-run',cwd:'/project',packageRoot:'/package'}],['cancel',{ref:'old-run',cwd:'/project',packageRoot:'/package'}]]);
});

test('CANCEL9: killed public CLI confirmation owner releases custody by native identity; live owner remains exclusive',async t=>{
  const {spawn}=await import('node:child_process');const f=await cancellationFixture(t),status=bytes(join(f.runDir,'status.json')),claim=bytes(f.claim);
  const launch=()=>{const child=spawn(process.execPath,[join(packageRoot,'bin/pdd.mjs'),'workflow','cancel',f.old.runId],{cwd:f.source,env:{...process.env,HOME:f.home,PDD_AGENT_SESSION:'',CLAUDECODE:'',CODEX_THREAD_ID:''},stdio:['pipe','pipe','pipe']});f.ownChild(child);return child;};
  const first=launch(),firstClosed=new Promise(resolve=>first.once('close',resolve));
  await new Promise((resolve,reject)=>{first.stderr.on('data',data=>{if(String(data).includes('(y/N)'))resolve();});first.once('exit',code=>reject(Error(`CLI exited before confirmation: ${code}`)));});
  const retry=async()=>{const child=launch();let output='';child.stdout.on('data',s=>output+=s);child.stderr.on('data',s=>output+=s);child.stdin.end('n\n');return {code:await new Promise(r=>child.once('close',r)),output};};
  const live=await retry();assert.equal(live.code,1);assert.match(live.output,/custody/);
  first.kill('SIGKILL');await firstClosed;
  const recovered=await retry();assert.equal(recovered.code,0,recovered.output);assert.match(recovered.output,/declined/);
  assert.equal(bytes(join(f.runDir,'status.json')),status);assert.equal(bytes(f.claim),claim);
});

for(const operation of ['approve','open','changes']) test(`CANCEL10: cancellation confirmation excludes concurrent ${operation} and preserves recorded history`,async t=>{
  const {openRun,changeRun}=await import('../src/workflow-runner.mjs');const f=await cancellationFixture(t);
  await stepDone({step:'scope',summary:'Reviewed scope.',cwd:f.old.root},f.ports);
  // Without custody these transports permit an actual public resume or prompt.
  // A control must expose the forbidden effect, not fail on an unbound fixture.
  const transport=f.ports.herdr,effects=[];
  f.ports.isTTY=operation!=='open';
  f.ports.findNativeSessions=async()=>[{id:'00000011-0000-4000-8000-000000000011'}];
  f.ports.herdr=async args=>{
    if(args[0]==='status'&&args[1]==='server')return {running:true};
    if(args[0]==='tab'&&['get','focus'].includes(args[1]))return {};
    if((args[0]==='pane'&&args[1]==='run')||(args[0]==='agent'&&args[1]==='prompt')){effects.push(args);return {};}
    return transport(args);
  };
  const prior=f.read();let release,entered;const wait=new Promise(r=>release=r),ready=new Promise(r=>entered=r);
  f.ports.confirm=async question=>{if(question.startsWith('Cancel run')){entered();await wait;}return true;};
  const cancellation=cancelRun(input(f),f.ports);await ready;
  const request=operation==='approve'?approveRun:operation==='open'?openRun:changeRun;
  const raced=await request({ref:'17',text:'Please revise this step.',cwd:f.source},f.ports);
  assert.equal(raced.exitCode,1,raced.message);assert.match(raced.message,/custody/);assert.equal(f.chats.length,1);assert.deepEqual(effects,[]);
  release();assert.equal((await cancellation).exitCode,0);assert.deepEqual(f.read().decisions,prior.decisions);assert.deepEqual(f.read().done,prior.done);assert.deepEqual(f.read().changes,prior.changes);assert.equal(f.read().chats.length,prior.chats.length);
});

test('CANCEL11: a real detached child writer forbids cancellation and matching claim release',async t=>{
  const {spawn}=await import('node:child_process'),{statSync}=await import('node:fs');const f=await cancellationFixture(t),root=f.old.root;
  const childScript=join(root,'codex-child.mjs'),parentScript=join(root,'codex-parent.mjs'),ticks=join(root,'child-writes');
  writeFileSync(childScript,`import{appendFileSync}from'node:fs';setInterval(()=>appendFileSync(${JSON.stringify(ticks)},'tick\\n'),10);`);
  // The parent owns and reaps its detached child before acknowledging teardown
  // by exiting. This also covers assertions that fail before reading child-pid.
  writeFileSync(parentScript,`import{spawn}from'node:child_process';import{writeFileSync}from'node:fs';let child,closed;process.on('SIGTERM',async()=>{child?.kill('SIGKILL');await closed;process.exit(0);});child=spawn(process.execPath,[${JSON.stringify(childScript)}],{cwd:${JSON.stringify(root)},detached:true,stdio:'ignore'});closed=new Promise(resolve=>child.once('close',resolve));writeFileSync(${JSON.stringify(join(root,'child-pid'))},String(child.pid));setInterval(()=>{},1000);`);
  const parent=spawn(process.execPath,[parentScript],{cwd:root,detached:true,stdio:'ignore'});
  f.ownChild(parent,'SIGTERM');
  for(let count=0;count<100&&!existsSync(ticks);count++)await new Promise(r=>setTimeout(r,10));assert.equal(existsSync(ticks),true);
  f.ports.herdr=async args=>{assert.deepEqual(args,['pane','process-info','--pane',f.old.chats[0].paneId]);return{result:{process_info:{shell_pid:process.pid,foreground_process_group_id:parent.pid,foreground_processes:[{pid:parent.pid,name:'node',argv:[process.execPath,parentScript],cwd:root}]}}};};
  const status=bytes(join(f.runDir,'status.json')),claim=bytes(f.claim),out=await cancelRun(input(f),f.ports);
  assert.equal(out.exitCode,1,out.message);assert.match(out.message,/native_descendants_unconfirmed/);
  assert.equal(bytes(join(f.runDir,'status.json')),status);assert.equal(bytes(f.claim),claim);
  const before=statSync(ticks).size;await new Promise(r=>setTimeout(r,50));assert.ok(statSync(ticks).size>before);
});

test('CANCEL12: an ordinary codex argument does not identify a foreground program as the saved agent',async t=>{
  const {spawn}=await import('node:child_process'),{statSync}=await import('node:fs');
  const f=await cancellationFixture(t),root=f.old.root,script=join(root,'ordinary-worker.mjs'),ticks=join(root,'ordinary-writes');
  writeFileSync(script,`import{appendFileSync}from'node:fs';setInterval(()=>appendFileSync(${JSON.stringify(ticks)},'tick\\n'),10);`);
  const child=spawn(process.execPath,[script,'codex'],{cwd:root,detached:true,stdio:'ignore'});
  let exited=false,signals=0,closed=false;child.on('exit',()=>{exited=true;});
  f.ownChild(child);
  for(let count=0;count<100&&!existsSync(ticks);count++)await new Promise(r=>setTimeout(r,10));
  assert.equal(existsSync(ticks),true,'Disposable worker started');
  f.ports.herdr=async args=>{
    if(args[0]==='tab'){closed=true;return {};}
    assert.deepEqual(args,['pane','process-info','--pane',f.old.chats[0].paneId]);
    return{result:{process_info:{shell_pid:process.pid,foreground_process_group_id:exited?process.pid:child.pid,
      foreground_processes:exited?[]:[{pid:child.pid,name:'node',argv:[process.execPath,script,'codex'],cwd:root}]}}};
  };
  f.ports.stopProcessGroup=async group=>{signals++;process.kill(-group,'SIGKILL');};
  const status=bytes(join(f.runDir,'status.json')),claim=bytes(f.claim),out=await cancelRun(input(f),f.ports);
  assert.equal(out.exitCode,1,out.message);assert.match(out.message,/native_identity_mismatch/);
  assert.equal(signals,0);assert.equal(closed,false);assert.equal(exited,false);
  assert.equal(bytes(join(f.runDir,'status.json')),status);assert.equal(bytes(f.claim),claim);
  const before=statSync(ticks).size;await new Promise(r=>setTimeout(r,50));assert.ok(statSync(ticks).size>before);
});
