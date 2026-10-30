import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, readFileSync} from 'node:fs';
import {join} from 'node:path';
import {cancelRun, stepDone} from '../src/workflow-runner.mjs';
import {releaseIssueClaim, allocateIssueWorktree} from '../src/workflow-worktree.mjs';
import {writeRun, readRun, allRuns} from '../src/workflow-runs.mjs';
import {cancellationFixture} from './helpers/cancellation-fixture.mjs';
import {stopChats} from '../src/workflow-chat.mjs';

const bytes = file => readFileSync(file,'utf8');
const keep = run => {
  const value=structuredClone(run);
  for(const key of ['state','cancelled','gate','journalSeq','updatedAt','stage','steps','waitingFor','resumeDecisions','waitingDecision','stageAgent','runDir']) delete value[key];
  return value;
};
// The public runner uses its REAL default stopChats; only outside observations
// are injected. Existing fixture supplies actual Git worktrees/store/claims.
async function fallback(t, mode='pane_not_found') {
  const f=await cancellationFixture(t);
  const healthy=f.ports.herdr;
  f.ports.herdr=async args=>{
    if(args[0]==='pane' && args[1]==='process-info') {f.events.push(['herdr',...args]);throw Object.assign(Error(`observed ${mode}`),{code:mode});}
    return healthy(args);
  };
  if(mode==='no-pane') {f.old.chats=[];writeRun(f.old,f.ports);f.old=f.read();f.events.length=0;}
  f.observation={currentUid:123,complete:true,processes:[],reason:''};
  f.ports.inspectMachineProcesses=async input=>{f.events.push(['inspect',input]);assert.equal(input.root,f.old.root);return structuredClone(f.observation);};
  f.ports.stopProcessGroup=()=>assert.fail('Fallback never signals a process');
  assert.equal(f.ports.stopChats,undefined,'Do not replace the production owner with a boolean');
  return f;
}
const request=(f, action, options={})=>action==='cancel'?cancelRun({ref:f.old.runId,cwd:f.source},f.ports):f.start({name:'feature',replace:f.old.runId,...options});
for(const mode of ['pane_not_found','server_not_running','no-pane']) for(const action of ['cancel','replace']) {
  test(`D1 linked ${mode} ${action}: complete empty proof precedes durable cancellation and matching release`,async t=>{
    const f=await fallback(t,mode), old=f.old;
    f.ports.releaseIssueClaim=async(input,ports)=>{
      f.events.push(['release',input]);
      const saved=f.read();assert.equal(saved.state,'cancelled');assert.deepEqual(saved.cancelled,{state:'cancelled',at:600000});
      assert.equal(saved.stage,null);assert.equal(saved.stageAgent,null);assert.equal(saved.gate,null);assert.equal(saved.journalSeq,old.journalSeq+1);
      assert.deepEqual(keep(saved),keep(old));
      const index=JSON.parse(bytes(join(f.stateDir,'runs.json')));assert.equal(index.runs.find(x=>x.runDir===f.runDir).state,'cancelled');
      assert.equal(JSON.parse(bytes(f.claim)).runId,old.runId);
      return releaseIssueClaim(input,ports);
    };
    f.ports.allocateIssueWorktree=async(input,ports)=>{f.events.push(['allocate',input]);assert.equal(existsSync(f.claim),false);assert.equal(f.read().state,'cancelled');return allocateIssueWorktree(input,ports);};
    const out=await request(f,action);assert.equal(out.exitCode,0,out.message);
    const fresh=f.read(), archived=action==='replace'?`${f.runDir}-cancelled-${old.runId.slice(0,8)}`:f.runDir, history=readRun(archived);
    assert.equal(history.state,'cancelled');assert.deepEqual(keep(history),keep(old));
    assert.equal(bytes(join(archived,'journal.md')),'keep journal bytes\n');assert.equal(bytes(join(archived,'evidence.txt')),'keep artifact bytes\n');
    assert.equal(bytes(join(old.root,'uncommitted.txt')),'keep uncommitted work\n');assert.equal(bytes(join(old.root,'work.txt')),'keep original work\n');
    assert.ok(f.git('show-ref','--verify',`refs/heads/${old.branch}`));assert.equal(allRuns({cancelled:true},f.ports).find(x=>x.runId===old.runId).state,'cancelled');
    const names=f.events.map(x=>x[0]);assert.ok(names.indexOf('confirm')<names.indexOf('inspect'));assert.ok(names.indexOf('inspect')<names.indexOf('save'));assert.ok(names.indexOf('save')<names.indexOf('release'));
    if(action==='replace') {
      assert.notEqual(fresh.runId,old.runId);assert.notEqual(fresh.root,old.root);assert.notEqual(fresh.branch,old.branch);assert.equal(fresh.previous.at(-1).runId,old.runId);
      assert.equal(JSON.parse(bytes(f.claim)).runId,fresh.runId);assert.ok(names.indexOf('release')<names.indexOf('allocate'));assert.ok(names.indexOf('allocate')<names.indexOf('start'));
      const status=bytes(join(f.runDir,'status.json')),claim=bytes(f.claim);
      assert.match((await stepDone({step:'scope',summary:'late completion',cwd:old.root},f.ports)).message,/cancelled.*Stop/s);
      assert.equal(bytes(join(f.runDir,'status.json')),status);assert.equal(bytes(f.claim),claim);
    } else assert.equal(existsSync(f.claim),false);
  });
}
for(const kind of ['ordinary','detached','idle-shell','caller','descendant','unreadable','unknown-uid','unknown-current','unknown-command','unknown-birth','incomplete','blocker-plus-unknown']) for(const action of ['cancel','replace']) {
  test(`D1 linked ${action} ${kind}: full diagnostic and zero forbidden effects`,async t=>{
    const f=await fallback(t), row={pid:7002,uid:123,birth:'birth',command:kind==='idle-shell'?'zsh':kind==='caller'?'node pdd.mjs':'node writer.mjs',cwd:kind==='descendant'?join(f.old.root,'nested'):f.old.root};
    f.observation.processes=[row];
    if(kind==='unreadable') {row.cwd=null;f.observation.reason='EACCES actual cwd failure';f.observation.complete=false;}
    if(kind==='unknown-uid') row.uid=null;
    if(kind==='unknown-current') f.observation.currentUid=null;
    if(kind==='unknown-command') row.command=null;
    if(kind==='unknown-birth') row.birth=null;
    if(kind==='incomplete') {row.cwd=f.source;f.observation.complete=false;f.observation.reason='truncated ps output';}
    if(kind==='blocker-plus-unknown') {f.observation.complete=false;f.observation.reason='other unreadable identity';f.observation.processes.push({pid:7003,uid:123,birth:null,command:null,cwd:null});}
    const before=bytes(join(f.runDir,'status.json')),claim=bytes(f.claim),index=bytes(join(f.stateDir,'runs.json'));
    const options=action==='replace'?{issue:'example/project#17',base:'alpha',agent:'claude'}:{};
    // The synthetic GitHub resolver receives a qualified public selection.
    f.ports.resolveWorkflowIssue=async()=>({repository:'example/project',defaultBranch:'alpha',issue:{number:17,title:'Synthetic',url:'https://github.com/example/project/issues/17'}});
    const out=await request(f,action,options);assert.equal(out.exitCode,1,out.message);
    if(kind!=='incomplete') {assert.ok(out.message.includes('7002'),out.message);if(row.command) assert.ok(out.message.includes(row.command),out.message);}
    if(f.observation.reason)assert.ok(out.message.includes(f.observation.reason),out.message);
    assert.match(out.message,/outside the worktree/);
    assert.ok(out.message.includes(action==='cancel'?`Retry: pdd workflow cancel ${f.old.runId}`:`Retry: pdd workflow run feature example/project#17 --replace ${f.old.runId} --base alpha --agent claude`),out.message);
    if(['idle-shell','caller'].includes(kind)) {assert.match(out.message,/cd.*exit/);assert.doesNotMatch(out.message,/kill -TERM 7002/);}
    assert.equal(bytes(join(f.runDir,'status.json')),before);assert.equal(bytes(f.claim),claim);assert.equal(bytes(join(f.stateDir,'runs.json')),index);
    assert.equal(bytes(join(f.old.root,'uncommitted.txt')),'keep uncommitted work\n');
    assert.ok(!f.events.some(([name,...args])=>['save','release','allocate','start'].includes(name)||name==='herdr'&&args[0]==='tab'&&args[1]==='close'));
  });
}
for(const failure of ['save-before','save-after','wrong-owner','release','allocation']) test(`D1 linked fault ${failure}: retain custody/history at its real persistence boundary`,async t=>{
  const f=await fallback(t), before=bytes(join(f.runDir,'status.json')),claim=bytes(f.claim);
  if(failure==='save-before')f.ports.writeRun=()=>{throw Error('disk failure before save');};
  if(failure==='save-after')f.ports.writeRun=(run,ports)=>{writeRun(run,ports);throw Error('lost reply after durable save');};
  if(failure==='wrong-owner') {const {writeFileSync}=await import('node:fs');const value=JSON.parse(claim);value.runId='other-owner';writeFileSync(f.claim,JSON.stringify(value));}
  if(failure==='release')f.ports.releaseIssueClaim=()=>{throw Error('release permission failure');};
  if(failure==='allocation')f.ports.allocateIssueWorktree=()=>({state:'recovery_required',message:'allocation failure'});
  const actualClaim=bytes(f.claim),out=await request(f,'replace');assert.equal(out.exitCode,1,out.message);
  if(failure==='save-before')assert.equal(bytes(join(f.runDir,'status.json')),before);else assert.equal(f.read().state,'cancelled');
  if(failure==='allocation')assert.equal(existsSync(f.claim),false);else assert.equal(bytes(f.claim),actualClaim);
  assert.equal(f.chats.length,1);assert.equal(bytes(join(f.old.root,'uncommitted.txt')),'keep uncommitted work\n');
});

test('D1 linked decline precedes every inspection; close warning is forwarded after proof',async t=>{
  const f=await fallback(t);f.answer=false;assert.equal((await request(f,'cancel')).exitCode,0);assert.deepEqual(f.events.map(x=>x[0]),['confirm']);
  f.answer=true;const healthy=f.ports.herdr;
  f.ports.herdr=async args=>{if(args[0]==='tab'&&args[1]==='close')throw Object.assign(Error('close transport unavailable'),{code:'server_not_running'});return healthy(args);};
  const out=await request(f,'replace');assert.equal(out.exitCode,0,out.message);assert.match(out.message,/warning: Herdr did not close tab/);
});

for(const action of ['cancel','replace']) test(`D1 linked ${action} excludes foreign metadata and a prefix sibling`,async t=>{
  const f=await fallback(t);
  f.observation.processes=[{pid:7001,uid:456,birth:null,command:null,cwd:null},{pid:7002,uid:123,birth:'birth',command:'node',cwd:f.old.root+'-sibling'}];
  const out=await request(f,action);assert.equal(out.exitCode,0,out.message);
});

for(const kind of ['birth-null','changed-identity','UID-null']) test(`D1 linked ${kind} inside has no invented safe signal target`,async t=>{
  const f=await fallback(t);
  f.observation.processes=[{pid:7002,uid:kind==='UID-null'?null:123,birth:kind==='birth-null'?null:'birth',command:'node writer.mjs',cwd:f.old.root}];
  if(kind==='changed-identity'){f.observation.complete=false;f.observation.reason='PID 7002 birth changed during inspection';}
  const out=await request(f,'cancel');assert.equal(out.exitCode,1);assert.match(out.message,/7002.*node writer/);assert.doesNotMatch(out.message,/kill -TERM 7002/);assert.match(out.message,/inspecting.*identity/);
});

for(const normal of [false,true]) test(`proved ${normal?'normal':'fallback'} quiescence survives an outside close rejection`,async()=>{
  const root='/synthetic-worktree',ports={
    herdr:normal?async()=>({result:{process_info:{shell_pid:7001,foreground_process_group_id:7001,foreground_processes:[]}}}):async()=>{throw Object.assign(Error('closed pane'),{code:'pane_not_found'});},
    nativeProcesses:async()=>[],inspectMachineProcesses:async()=>({currentUid:123,complete:true,processes:[],reason:''}),
    closeChats:async()=>{throw Object.assign(Error('lost close reply'),{code:'server_not_running'});},
  };
  const out=await stopChats({root,state:'waiting',chats:[{paneId:'pane',tabId:'tab'}]},ports);
  assert.equal(out.stopped,true,JSON.stringify(out));assert.match(out.warnings[0],/warning.*lost close reply/);
});
