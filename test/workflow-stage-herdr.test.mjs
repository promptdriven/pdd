import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtemp, rm, realpath } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { EventEmitter } from 'node:events';
import { createHash } from 'node:crypto';
import { AsyncLocalStorage } from 'node:async_hooks';
import { runHerdrStage, inspectHerdrStage, attachHerdrStage, closeHerdrStage } from '../src/workflow-stage-herdr.mjs';

const runId = '12345678-1234-4123-8123-123456789abc';
const sessionFor = id => `pdd-${createHash('sha256').update(id.toLowerCase()).digest('hex').slice(0,20)}`;
const attemptId = '87654321-4321-4321-8321-cba987654321';
function harness(cwd, options = {}) {
  const calls = [], checkpoints = [];
  let clock = 0, running = Boolean(options.preexisting), prompted = false, started = false, poll = 0, agentName, closed = false;
  const ws=options.workspaceId??'w2',tab=ws+':t1',pane=ws+':p1',terminal=options.terminalId??'term-real';
  const session = sessionFor(options.runId ?? runId);
  const agent = (state = 'idle', seq = 10) => ({ workspace_id: ws, tab_id: tab, pane_id: pane, terminal_id: terminal,
    name: agentName, agent: options.agent ?? 'codex', cwd, agent_status: state, state_change_seq: seq,
    interactive_ready: state === 'idle' || state === 'done', launch_pending: false,
    agent_session: options.noNativeId ? null : { source: 'actual', agent: options.agent ?? 'codex', kind: 'id', value: options.nativeId ?? 'native-real' } });
  const encode = x => ({ stdout: JSON.stringify(x), stderr: '' });
  const ports = {
    withStageGuard: async (backend, action) => { calls.push(['GUARD',backend.runId,backend.cwd]);return action(); },
    now: () => clock, sleep: async ms => { clock += ms; }, pollMs: 1, startupMs: 4000, activityMs: 3, timeoutMs: 10,
    spawnServer: async (actual, actualCwd) => { calls.push(['SERVER',actual,actualCwd]);running = true; },
    spawnAttach: async (...args) => { calls.push(['ATTACH',...args]);return 17; },
    execFile: async (bin, argv, cfg) => {
      calls.push([bin,[...argv],cfg]);assert.equal(bin,'herdr');assert.equal(argv[0],'--session');assert.equal(argv[1],session);
      assert.equal(cfg.cwd,cwd);assert.equal(cfg.shell,false);assert.equal('env' in cfg,false);
      const a = argv.slice(2);
      if (a[0] === 'status') return encode({ running, session, compatible: true, endpoint_compatible: !options.incompatible,
        socket: '/actual-owned/socket', protocol: 22, version: '0.9.1' });
      if (a[0] === 'workspace' && a[1] === 'list') return encode({id:'cli:workspace:list',result:{type:'workspace_list',workspaces: options.capacity ? [{workspace_id:'seed'},{workspace_id:'occupied'}] : options.closeRemains && closed ? [{workspace_id:'seed'},{workspace_id:ws}] : [{workspace_id:'seed'}]}});
      if (a[0] === 'workspace' && a[1] === 'create') {
        assert.equal(checkpoints.at(-1).phase,'workspace_intent');
        assert.deepEqual(a,['workspace','create','--cwd',cwd,'--label','PDD check','--no-focus']);
        return encode({ result: { workspace: { workspace_id:ws },tab:{ tab_id:tab },root_pane:{pane_id:pane,terminal_id:terminal} } });
      }
      if (a[0] === 'agent' && a[1] === 'start') {
        assert.equal(checkpoints.at(-1).phase,'start_intent');assert.equal(checkpoints.at(-1).terminalId,terminal);
        agentName=a[2];started=true;
        if(options.requireNoDaemon && !a.includes('--no-daemon'))throw Object.assign(Error('unsupported daemon'),{code:1,stderr:JSON.stringify({error:{code:'agent_not_ready',message:'Cannot use the shared background server: api_key_model_discovery must be disabled'}})});
        if(options.requireTrust && a[a.indexOf('-c')+1]!==`projects={${JSON.stringify(cwd)}={trust_level="trusted"}}`)throw Object.assign(Error('folder trust required'),{code:1,stderr:JSON.stringify({error:{code:'agent_not_ready',message:'Trust this folder'}})});
        if(options.startBlocked)throw Object.assign(Error('pending'),{code:1,stderr:JSON.stringify({error:{code:'agent_not_ready',message:'Native startup awaits person'}})});
        assert.deepEqual(a.slice(3),['--kind',options.agent ?? 'codex','--pane',pane,'--timeout','4000',...((options.agent??'codex')==='codex'?['--','--no-daemon','--dangerously-bypass-approvals-and-sandbox','-c',`projects={${JSON.stringify(cwd)}={trust_level="trusted"}}`]:['--','--dangerously-skip-permissions'])]);
        return encode({result:{agent:options.startAck?options.startAck(agent()):agent()}});
      }
      if (a[0] === 'agent' && a[1] === 'prompt') {
        assert.equal(checkpoints.at(-1).phase,'prompt_intent');assert.ok(checkpoints.at(-1).promptDigest);
        assert.ok(a[3].startsWith('# Entire guide\n'));assert.ok(a[3].includes('Actual selected recipe'));assert.ok(a[3].includes('literal $(not shell)'));
        assert.equal(a.length,4);assert.equal(prompted,false);prompted=true;
        if (options.lostReply) throw Object.assign(Error('reply lost'),{code:'ETIMEDOUT'});
        return encode({result:{agent:agent()}});
      }
      if (a[0] === 'agent' && a[1] === 'get') {
        assert.equal(started,true);
        let value;
        if (!prompted) value=(options.startBlocked||options.actualBlocked)?{...agent('blocked',10),launch_pending:true}:agent();
        else if (options.stalled) value=agent('idle',10);
        else if (options.blocked) value=agent('blocked',11);
        else if (options.unknown) value=agent('unknown',11);
        else value=poll++===0 ? agent('working',11) : agent('done',12);
        if (options.replace && prompted) value.terminal_id='different';
        if (options.lostNative && prompted) value.agent_session=null;
        if (options.vanishBefore && !prompted || options.vanishAfter && prompted)value={...value,agent:null,name:null};
        if (options.after) value=options.after(value);
        return encode({result:{agent:value}});
      }
      if (a[0] === 'workspace' && a[1] === 'close') {
        assert.equal(checkpoints.at(-1).phase,'close_intent');assert.equal(a[2],ws);closed=true;return encode(Object.hasOwn(options,'closeReply') ? options.closeReply : {id:'cli:workspace:close',result:{type:'ok'}});
      }
      assert.fail('Unexpected effect '+JSON.stringify(a));
    }
  };
  const input={runId:options.runId??runId,attemptId:options.attemptId??attemptId,stageId:'check',agent:options.agent??'codex',cwd,
    context:'# Entire guide\nActual selected recipe',instructions:'literal $(not shell)',
    checkpoint:async snapshot=>{checkpoints.push(structuredClone(snapshot));if(options.checkpointFails===snapshot.phase)throw Error('Disk failure');}};
  return { input,ports,calls,checkpoints,options,setRunning:value=>{running=value;},closed:()=>closed,promptCount:()=>calls.filter(x=>x[0]==='herdr'&&x[1][2]==='agent'&&x[1][3]==='prompt').length };
}
async function temp(t, prefix='pdd-stage-') { const p=await realpath(await mkdtemp(join(tmpdir(),prefix)));t.after(()=>rm(p,{recursive:true,force:true}));return p; }
const acceptance = b => ({runId:b.runId,stageId:b.stageId,attemptId:b.attemptId,promptDigest:b.promptDigest,terminalId:b.terminalId,evidenceDigest:'a'.repeat(64)});

test('fresh owned stage checkpoints actual IDs before one full prompt, observes work then ready; accepted cleanup only',async t=>{
  const h=harness(await temp(t));const result=await runHerdrStage(h.input,h.ports);
  assert.equal(result.state,'settled');assert.deepEqual(result.evidence,{readySeq:10,workingSeq:11,settledSeq:12});
  assert.equal(result.backend.nativeSession.value,'native-real');assert.equal(h.promptCount(),1);assert.equal(h.closed(),false);
  const denied=await closeHerdrStage({backend:result.backend,acceptance:{},}, {...h.ports,checkpoint:h.input.checkpoint});
  assert.equal(denied.state,'recovery_required');assert.equal(h.closed(),false);
  const released=await closeHerdrStage({backend:result.backend,acceptance:acceptance(result.backend),}, {...h.ports,checkpoint:h.input.checkpoint});
  assert.equal(released.state,'closed');assert.equal(h.closed(),true);assert.equal(released.backend.nativeSession.value,'native-real');
});

test('reply loss retains original prompt intent; same attempt/repeated inspection never resends',async t=>{
  const h=harness(await temp(t),{lostReply:true});const first=await runHerdrStage(h.input,h.ports);
  assert.equal(first.state,'recovery_required');assert.equal(first.backend.phase,'prompt_intent');assert.equal(h.promptCount(),1);
  const second=await runHerdrStage({...h.input,backend:first.backend},h.ports);assert.equal(second.state,'recovery_required');
  const count=h.calls.length;await inspectHerdrStage({backend:first.backend,cwd:h.input.cwd},h.ports);
  assert.equal(h.promptCount(),1);assert.ok(h.calls.slice(count).every(x=>x[0]==='GUARD'||x[0]==='herdr'&&['status','agent'].includes(x[1][2])));
});

test('idle, blocked, unknown and identity loss cannot become transport settlement or trigger cleanup',async t=>{
  for(const options of [{stalled:true},{blocked:true},{unknown:true},{replace:true},{lostNative:true}]){
    const h=harness(await temp(t),options);const r=await runHerdrStage(h.input,h.ports);
    assert.equal(r.state,options.blocked?'blocked':'recovery_required');assert.equal(h.promptCount(),1);assert.equal(h.closed(),false);
  }
});

test('checkpoint failure fences corresponding effect; incompatible or unowned server never starts agent',async t=>{
  for(const phase of ['server_intent','workspace_intent','start_intent','prompt_intent']){
    const h=harness(await temp(t),{checkpointFails:phase});const r=await runHerdrStage(h.input,h.ports);
    assert.equal(r.state,'recovery_required');assert.equal(h.promptCount(),0);
    if(phase==='server_intent')assert.equal(h.calls.length,0);
    if(phase==='start_intent')assert.equal(h.calls.some(x=>x[0]==='herdr'&&x[1][3]==='start'),false);
  }
  for(const options of [{preexisting:true},{incompatible:true},{capacity:true}]){
    const h=harness(await temp(t),options);assert.equal((await runHerdrStage(h.input,h.ports)).state,'recovery_required');assert.equal(h.promptCount(),0);
  }
});

test('missing native session identity stays null; active attach uses exact target, closed stages never reopen',async t=>{
  const h=harness(await temp(t),{noNativeId:true});const r=await runHerdrStage(h.input,h.ports);
  assert.equal(r.backend.nativeSession,null);
  assert.equal(await attachHerdrStage({backend:r.backend},h.ports),17);
  const attach=h.calls.find(x=>x[0]==='ATTACH');assert.deepEqual(attach,['ATTACH',r.backend.session,r.backend.agentName,h.input.cwd]);
  const n=h.calls.length;assert.equal(await attachHerdrStage({backend:{...r.backend,phase:'closed'}},h.ports),2);assert.equal(h.calls.length,n);
});

test('cleanup refuses replacement, activity, or later sequence; no close of uncertain native work',async t=>{
  for(const transform of [a=>({...a,terminal_id:'different'}),a=>({...a,agent_status:'working',state_change_seq:13}),a=>({...a,agent_status:'blocked',state_change_seq:13}),a=>({...a,state_change_seq:14})]){
    const h=harness(await temp(t));const r=await runHerdrStage(h.input,h.ports);h.options.after=transform;
    const closed=await closeHerdrStage({backend:r.backend,acceptance:acceptance(r.backend),}, {...h.ports,checkpoint:h.input.checkpoint});
    assert.equal(closed.state,'recovery_required');assert.equal(h.closed(),false);
  }
});


test('missing guard refuses before provision; attach holds actual injected exclusion until detach',async t=>{
  const h=harness(await temp(t));const missing={...h.ports};delete missing.withStageGuard;
  assert.equal((await runHerdrStage(h.input,missing)).state,'recovery_required');assert.equal(h.calls.length,0);
  const r=await runHerdrStage(h.input,h.ports);
  assert.equal(await attachHerdrStage({backend:r.backend},missing),1);
  assert.equal((await closeHerdrStage({backend:r.backend,acceptance:acceptance(r.backend)},missing)).state,'recovery_required');
  const scope=new AsyncLocalStorage();let busy=false,detach,attachStarted;
  const attached=new Promise(resolve=>{attachStarted=resolve;});
  const guarded={...h.ports,withStageGuard:async(b,action)=>{
    if(scope.getStore())return action();
    if(busy)throw Object.assign(Error('Busy'),{code:'WORKFLOW_STAGE_BUSY'});
    busy=true;try{return await scope.run(true,action);}finally{busy=false;}
  },spawnAttach:async()=>{attachStarted();return new Promise(resolve=>{detach=resolve;});}};
  const operation=attachHerdrStage({backend:r.backend},guarded);await attached;
  const count=h.calls.length;
  const inspected=await inspectHerdrStage({backend:r.backend,cwd:h.input.cwd},guarded);
  assert.equal(inspected.state,'recovery_required');assert.equal(inspected.reason,'native_stage_active');
  assert.equal(h.calls.slice(count).some(c=>c[0]==='herdr'&&c[1][3]==='get'),false);
  const closed=await closeHerdrStage({backend:r.backend,acceptance:acceptance(r.backend)}, {...guarded,checkpoint:h.input.checkpoint});
  assert.equal(closed.state,'recovery_required');assert.equal(h.closed(),false);
  detach(0);assert.equal(await operation,0);assert.equal(busy,false);
  // Main may already hold the same guard over validation; nested close/inspect must reuse it.
  const accepted=await guarded.withStageGuard(r.backend,()=>closeHerdrStage({backend:r.backend,acceptance:acceptance(r.backend)}, {...guarded,checkpoint:h.input.checkpoint}));
  assert.equal(accepted.state,'closed');
});

test('two concurrent issue assignments keep actual cwd/backend and native kind separate',async t=>{
  const one=harness(await temp(t));const two=harness(await temp(t),{runId:'aaaaaaaa-bbbb-4ccc-8ddd-eeeeeeeeeeee',attemptId:'bbbbbbbb-cccc-4ddd-8eee-ffffffffffff',agent:'claude'});
  const [a,b]=await Promise.all([runHerdrStage(one.input,one.ports),runHerdrStage(two.input,two.ports)]);
  assert.equal(a.state,'settled');assert.equal(b.state,'settled');assert.notEqual(a.backend.cwd,b.backend.cwd);
  assert.notEqual(a.backend.session,b.backend.session);assert.notEqual(a.backend.agentName,b.backend.agentName);
  assert.equal(a.backend.agent,'codex');assert.equal(b.backend.agent,'claude');assert.equal(one.promptCount(),1);assert.equal(two.promptCount(),1);
});

test('actual default spawn boundary uses headless short-name server without environment changes and exact inherited attach',async t=>{
  const h=harness(await temp(t));const spawned=[];let unref=0;
  const ports={...h.ports,spawnServer:undefined,spawnAttach:undefined,spawn:(exe,args,opts)=>{
    const c=new EventEmitter();c.unref=()=>{unref++;};spawned.push({exe,args,opts});
    queueMicrotask(()=>{if(args.at(-1)==='server'){h.setRunning(true);c.emit('spawn');}else c.emit('close',7);});return c;
  }};
  const r=await runHerdrStage(h.input,ports);assert.equal(r.state,'settled');assert.equal(unref,1);
  assert.deepEqual(spawned[0],{exe:'herdr',args:['--session',r.backend.session,'server'],opts:{cwd:h.input.cwd,stdio:'ignore',detached:true,shell:false}});
  assert.equal(await attachHerdrStage({backend:r.backend},ports),7);
  assert.deepEqual(spawned[1],{exe:'herdr',args:['--session',r.backend.session,'agent','attach',r.backend.agentName],opts:{cwd:h.input.cwd,stdio:'inherit',shell:false}});
});


test('accepted predecessor reuses only owned run server; next stage gets fresh pane/native and one new prompt',async t=>{
  const cwd=await temp(t);const first=harness(cwd);const a=await runHerdrStage(first.input,first.ports);
  const closed=await closeHerdrStage({backend:a.backend,acceptance:acceptance(a.backend)}, {...first.ports,checkpoint:first.input.checkpoint});
  const second=harness(cwd,{preexisting:true,attemptId:'cccccccc-dddd-4eee-8fff-aaaaaaaaaaaa',workspaceId:'w3',terminalId:'term-next',nativeId:'native-next'});
  const b=await runHerdrStage({...second.input,backend:closed.backend},second.ports);
  assert.equal(b.state,'settled');assert.notEqual(a.backend.agentName,b.backend.agentName);assert.notEqual(a.backend.paneId,b.backend.paneId);assert.notEqual(a.backend.nativeSession.value,b.backend.nativeSession.value);assert.equal(a.backend.server.session,b.backend.server.session);
  assert.equal(second.calls.some(c=>c[0]==='SERVER'),false);assert.equal(second.promptCount(),1);
  const starts=second.calls.filter(c=>c[0]==='herdr'&&c[1][3]==='start');assert.equal(starts.length,1);
});


test('captured candidate cannot absorb later activity or uncertain cleanup into a new success',async t=>{
 const h=harness(await temp(t));const r=await runHerdrStage(h.input,h.ports);
 h.options.after=a=>({...a,state_change_seq:14});
 const later=await inspectHerdrStage({backend:r.backend,cwd:h.input.cwd},h.ports);
 assert.equal(later.state,'recovery_required');assert.equal(later.reason,'candidate_sequence_changed');
 assert.equal(later.backend.evidence.settledSeq,12);
 const before=h.calls.length;
 const cleanup=await inspectHerdrStage({backend:{...r.backend,phase:'close_intent'}},h.ports);
 assert.equal(cleanup.reason,'stage_cleanup_unconfirmed');assert.equal(h.calls.length,before);
});


test('P2 cleanup malformed/unrelated acknowledgements or contradictory inventory retain original close intent',async t=>{
  for(const options of [{closeReply:{}},{closeReply:[]},{closeReply:{result:{type:'workspace_created'}}},{closeReply:{id:'other',result:{type:'ok'}}},{closeReply:{id:'cli:workspace:close',result:{action:'workspace_closed'}}},{closeRemains:true}]){
    const h=harness(await temp(t),options);const r=await runHerdrStage(h.input,h.ports);
    const cleanup=await closeHerdrStage({backend:r.backend,acceptance:acceptance(r.backend)}, {...h.ports,checkpoint:h.input.checkpoint});
    assert.equal(cleanup.state,'recovery_required',JSON.stringify(options));assert.equal(cleanup.backend.phase,'close_intent');
    assert.equal(h.checkpoints.at(-1).phase,'close_intent');assert.equal(h.calls.filter(c=>c[0]==='herdr'&&c[1][2]==='workspace'&&c[1][3]==='close').length,1);
    await inspectHerdrStage({backend:cleanup.backend},h.ports);assert.equal(h.promptCount(),1);
    assert.equal(h.calls.filter(c=>c[0]==='herdr'&&c[1][2]==='workspace'&&c[1][3]==='close').length,1);
  }
});


test('proven pre-native server/list failure preserves structured error and same original bootstraps once',async t=>{
 const h=harness(await temp(t));const exec=h.ports.execFile;let first=true;
 h.ports.execFile=async(...args)=>{
  if(first && args[1][2]==='workspace' && args[1][3]==='list'){
   first=false;throw Object.assign(Error('DO NOT LEAK prompt or credentials'),{code:1,stderr:JSON.stringify({error:{code:'app_not_ready',message:'Workspace service not initialized'}})});
  }return exec(...args);
 };
 const failed=await runHerdrStage(h.input,h.ports);
 assert.equal(failed.reason,'app_not_ready');assert.equal(failed.backend.phase,'server_intent');assert.equal(failed.backend.nativeSession,null);
 assert.deepEqual(failed.detail,{operation:'workspace.list',code:'app_not_ready',message:'Workspace service not initialized'});
 assert.equal(JSON.stringify(failed).includes('DO NOT LEAK'),false);assert.equal(h.promptCount(),0);
 h.setRunning(false);const before=h.calls.length;
 await inspectHerdrStage({backend:failed.backend},h.ports);
 assert.equal(h.calls.slice(before).some(c=>c[0]==='SERVER'),false);assert.equal(h.promptCount(),0);
 const recovered=await runHerdrStage({...h.input,backend:failed.backend},h.ports);
 assert.equal(recovered.state,'settled');assert.equal(recovered.backend.runId,failed.backend.runId);
 assert.equal(recovered.backend.attemptId,failed.backend.attemptId);assert.equal(recovered.backend.promptDigest,failed.backend.promptDigest);
 assert.equal(h.promptCount(),1);assert.equal(h.calls.filter(c=>c[0]==='SERVER').length,2);
});

test('pre-native recovery refuses changed input/server and cannot reinterpret later intents or evidence',async t=>{
 const h=harness(await temp(t));const exec=h.ports.execFile;
 h.ports.execFile=async(...args)=>{if(args[1][2]==='workspace')throw Object.assign(Error('failed'),{code:'STOP'});return exec(...args);};
 const failed=await runHerdrStage(h.input,h.ports);assert.equal(failed.backend.phase,'server_intent');
 const saved=failed.backend;h.setRunning(false);
 for(const patch of [{phase:'workspace_intent'},{phase:'prompt_intent'},{nativeSession:{value:'actual'}},{workspaceId:'w2'},{evidence:{readySeq:10}},{lastSeq:0}]){
  const n=h.calls.filter(c=>c[0]==='SERVER').length;
  const result=await runHerdrStage({...h.input,backend:{...saved,...patch}},h.ports);
  assert.equal(result.state,'recovery_required');assert.equal(h.calls.filter(c=>c[0]==='SERVER').length,n);assert.equal(h.promptCount(),0);
 }
 const changed=await runHerdrStage({...h.input,context:'changed',backend:saved},h.ports);assert.equal(changed.reason,'stage_input_changed');
 h.ports.execFile=exec;h.setRunning(true);
 const mismatch=await runHerdrStage({...h.input,backend:{...saved,server:{...saved.server,socket:'/other'}}},h.ports);
 assert.equal(mismatch.reason,'herdr_server_changed');assert.equal(h.promptCount(),0);
});

test('legacy stopped pre-native original migrates short; legacy active or later phases never migrate',async t=>{
 const h=harness(await temp(t));const exec=h.ports.execFile;let failList=true;
 h.ports.execFile=async(...args)=>{if(failList&&args[1][2]==='workspace'){failList=false;throw Object.assign(Error('fail'),{code:'STOP'});}return exec(...args);};
 const failed=await runHerdrStage(h.input,h.ports);assert.equal(failed.backend.phase,'server_intent');
 const legacy={...failed.backend,session:`pdd-${runId}`,server:{...failed.backend.server,session:`pdd-${runId}`}};
 h.ports.execFile=async(bin,args,opts)=>args[1]===legacy.session
  ? {stdout:JSON.stringify({running:false,session:legacy.session})}:exec(bin,args,opts);
 h.setRunning(false);
 const r=await runHerdrStage({...h.input,backend:legacy},h.ports);
 assert.equal(r.state,'settled');assert.equal(r.backend.session,sessionFor(runId));assert.equal(r.backend.attemptId,attemptId);assert.equal(h.promptCount(),1);
 assert.ok(h.checkpoints.some(b=>b.session===sessionFor(runId)&&b.phase==='server_intent'&&!b.server));
 const other=harness(await temp(t));const base={...legacy,cwd:other.input.cwd};
 other.ports.execFile=async()=>({stdout:JSON.stringify({running:true,session:legacy.session})});
 const active=await runHerdrStage({...other.input,backend:base},other.ports);
 assert.equal(active.reason,'legacy_server_not_stopped');assert.equal(other.calls.some(c=>c[0]==='SERVER'),false);assert.equal(other.promptCount(),0);
});


test('fresh stages trust only the assigned worktree per invocation and retain authorized full access',async t=>{
 for(const agent of ['codex','claude']){
  const h=harness(await temp(t,'pdd-stage \"quoted\".back\\slash=chosen-'),{agent,requireNoDaemon:agent==='codex',requireTrust:agent==='codex'});const r=await runHerdrStage(h.input,h.ports);
  assert.equal(r.state,'settled');const args=h.calls.find(c=>c[0]==='herdr'&&c[1][3]==='start')[1];
  assert.equal(args.includes('--no-daemon'),agent==='codex');assert.equal(args.includes('-c'),agent==='codex');assert.ok(args.includes(agent==='codex'?'--dangerously-bypass-approvals-and-sandbox':'--dangerously-skip-permissions'));assert.equal(h.promptCount(),1);
 }
});

test('owned native startup choice is actionable; same original sends its first prompt after person clears menu',async t=>{
 const h=harness(await temp(t),{startBlocked:true});
 const paused=await runHerdrStage(h.input,h.ports);assert.equal(paused.state,'blocked');assert.equal(paused.reason,'native_start_person_action_required');
 assert.equal(paused.backend.phase,'start_intent');assert.equal(h.promptCount(),0);assert.ok(paused.detail.message.includes('pdd workflow attach '+runId));
 h.options.startBlocked=false;const starts=h.calls.filter(c=>c[0]==='herdr'&&c[1][3]==='start').length;
 const result=await runHerdrStage({...h.input,backend:paused.backend},h.ports);
 assert.equal(result.state,'settled');assert.equal(result.backend.attemptId,attemptId);assert.equal(h.promptCount(),1);
 assert.equal(h.calls.filter(c=>c[0]==='herdr'&&c[1][3]==='start').length,starts);
});

test('native disappearing before submit sends nothing; after submit preserves uncertain original without restart',async t=>{
 for(const when of ['vanishBefore','vanishAfter']){
  const h=harness(await temp(t),{[when]:true});const r=await runHerdrStage(h.input,h.ports);
  assert.equal(r.state,'recovery_required');assert.equal(r.reason,'native_agent_unavailable');
  assert.equal(h.promptCount(),when==='vanishBefore'?0:1);
  if(when==='vanishAfter'){
   const n=h.calls.length;await runHerdrStage({...h.input,backend:r.backend},h.ports);
   assert.equal(h.promptCount(),1);assert.equal(h.calls.slice(n).some(c=>c[0]==='SERVER'||c[0]==='herdr'&&c[1][3]==='start'),false);
  }
 }
});


test('a launch success snapshot cannot authorize prompt while live native startup is still pending',async t=>{
 const h=harness(await temp(t),{actualBlocked:true});
 const r=await runHerdrStage(h.input,h.ports);
 assert.equal(r.state,'blocked');assert.equal(r.reason,'native_start_person_action_required');assert.equal(h.promptCount(),0);
 assert.equal(r.backend.phase,'start_intent');assert.equal(r.backend.nativeSession.value,'native-real');
});


test('P2 launch snapshot pins supplied native session and sequence before live query; durability failure sends nothing',async t=>{
 for(const kind of ['replacement','reverse','checkpoint']){
  const options={startAck:a=>({...a,state_change_seq:20,agent_session:{...a.agent_session,value:'session-A'}})};
  if(kind==='replacement')options.after=a=>({...a,state_change_seq:21,agent_session:{...a.agent_session,value:'session-B'}});
  else options.after=a=>({...a,state_change_seq:19,agent_session:{...a.agent_session,value:'session-A'}});
  const h=harness(await temp(t),options);
  if(kind==='checkpoint'){
   const save=h.input.checkpoint;h.input.checkpoint=async b=>{await save(b);if(b.phase==='start_intent'&&b.lastSeq===20)throw Object.assign(Error('Disk unavailable'),{code:'CHECKPOINT_FAILED'});};
  }
  const r=await runHerdrStage(h.input,h.ports);assert.equal(r.state,'recovery_required');assert.equal(h.promptCount(),0);
  assert.equal(r.backend.nativeSession.value,'session-A');assert.equal(r.backend.lastSeq,20);
  assert.equal(r.reason,kind==='replacement'?'native_identity_changed':kind==='reverse'?'stage_sequence_reversed':'CHECKPOINT_FAILED');
  assert.ok(h.checkpoints.some(b=>b.phase==='start_intent'&&b.nativeSession?.value==='session-A'&&b.lastSeq===20));
 }
});

test('P2 blocked lookup retains actual native session and sequence before return and rejects replacement on same-start recovery',async t=>{
 const h=harness(await temp(t),{startBlocked:true});const r=await runHerdrStage(h.input,h.ports);
 assert.equal(r.state,'blocked');assert.equal(r.backend.nativeSession.value,'native-real');assert.equal(r.backend.lastSeq,10);
 assert.equal(h.checkpoints.at(-1).nativeSession.value,'native-real');assert.equal(h.checkpoints.at(-1).lastSeq,10);assert.equal(h.promptCount(),0);
 h.options.startBlocked=false;h.options.after=a=>({...a,agent_session:{...a.agent_session,value:'replacement'}});
 const recovered=await runHerdrStage({...h.input,backend:r.backend},h.ports);
 assert.equal(recovered.reason,'native_identity_changed');assert.equal(h.promptCount(),0);
 const starts=h.calls.filter(c=>c[0]==='herdr'&&c[1][3]==='start');assert.equal(starts.length,1);
});


test('ordinary viewer guard contention waits beyond activity watchdog then observes same original after detach',async t=>{
 const h=harness(await temp(t));const guard=h.ports.withStageGuard;let remaining=6,blockedReads=0;
 h.ports.withStageGuard=async(b,action)=>{
  if(b.phase==='submitted'&&remaining-->0){blockedReads++;throw Object.assign(Error('Viewer attached'),{code:'WORKFLOW_STAGE_BUSY'});}
  return guard(b,action);
 };
 const result=await runHerdrStage(h.input,h.ports);
 assert.equal(result.state,'settled');assert.equal(blockedReads,6);assert.equal(h.promptCount(),1);
 assert.equal(h.calls.filter(c=>c[0]==='herdr'&&c[1][3]==='start').length,1);assert.equal(h.closed(),false);
 assert.deepEqual(result.evidence,{readySeq:10,workingSeq:11,settledSeq:12});
});

test('persistent viewer contention remains bounded with original intent and no repeated prompt or cleanup',async t=>{
 const h=harness(await temp(t));const guard=h.ports.withStageGuard;
 h.ports.withStageGuard=async(b,action)=>{
  if(b.phase==='submitted')throw Object.assign(Error('Viewer attached'),{code:'WORKFLOW_STAGE_BUSY'});
  return guard(b,action);
 };
 const result=await runHerdrStage(h.input,h.ports);
 assert.equal(result.state,'recovery_required');assert.equal(result.reason,'stage_wait_timeout');
 assert.equal(h.promptCount(),1);assert.equal(h.closed(),false);assert.equal(result.backend.phase,'submitted');
 assert.deepEqual(result.evidence,{readySeq:10});
});
