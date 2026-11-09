import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {mkdirSync, writeFileSync, realpathSync, existsSync, readFileSync} from 'node:fs';
import {join} from 'node:path';
import {startRun, stepDone, approveRun, yieldAutomaticCapacity, changeRun} from '../src/workflow-runner.mjs';
import {writeRun} from '../src/workflow-runs.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const origin = {repository:'example/project',coordinatorId:'coordinator-a',machine:'machine-a',claim:{commentId:'11',labelEventId:'12'}};
const reply = value => ({json:JSON.stringify(value)});
async function ready(t) {
  const f=await fixture(t,{name:'bug',agent:'codex'});
  f.ports.env={HOME:f.ports.env.HOME,PDD_INTERPRETER_QUEUE:f.ports.env.PDD_INTERPRETER_QUEUE};
  assert.equal((await startRun({name:'bug',issue:'17',agent:'codex',cwd:f.source,packageRoot},f.ports)).exitCode,0);
  for(const step of ['reproduce','prompt-story']) { f.tick(); const r=await stepDone({step,summary:step,cwd:f.record().root},f.agentPorts()); assert.equal(r.exitCode,0,r.message); }
  const run=f.record(); run.automaticOrigin=structuredClone(origin); writeRun(run);
  const root=realpathSync(f.source), stateRoot=join(f.state,'autopilot'); mkdirSync(stateRoot,{recursive:true});
  writeFileSync(join(stateRoot,`${createHash('sha256').update(root).digest('hex').slice(0,20)}.json`),JSON.stringify({repo:run.repo,cwd:root,coordinatorId:origin.coordinatorId}));
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  const fixturePath=join(f.base,'reader.json'), logPath=join(f.base,'gh.log');
  const state={claimed:true};
  const {execFile: callback}=await import('node:child_process'); const {promisify}=await import('node:util'); const exec=promisify(callback);
  const original=f.ports.execFile;
  const execFile=(file,args,opts)=>file==='gh' && args[0]==='api' && args[1]==='--include' ? exec(process.execPath,[join(packageRoot,'test/helpers/continuation-fake-gh.mjs'),...args],{...opts,env:{...process.env,READER_FIXTURE_FILE:fixturePath,READER_GH_LOG:logPath}}) : original(file,args,opts);
  const ports=()=>{
    writeFileSync(fixturePath,JSON.stringify({labels:state.claimed?['pdd:working']:[],events:[{id:12,event:'labeled',label:{name:'pdd:working'},actor:{login:'example'}}],comments:[{id:11,user:{login:'example'},body:JSON.stringify({repository:origin.repository,coordinatorId:origin.coordinatorId,machine:origin.machine,labelEventId:'12'})}]}));
    return {...f.agentPorts(),execFile,autopilotStateRoot:stateRoot};
  };
  return {f,state,ports};
}

test('current native reader denies removed label before approval or chat, then permits matching claim',async t=>{
  const {f,state,ports}=await ready(t); state.claimed=false;
  const before=f.record(), calls=f.herdr.calls.filter(call => call[0] === 'pane' && call[1] === 'run').length;
  const denied=await approveRun({ref:'17',cwd:f.record().root,said:'I approve'},ports());
  assert.equal(denied.exitCode,1); assert.match(denied.message,/claim ownership/); assert.deepEqual(f.record(),before); assert.equal(f.herdr.calls.filter(call => call[0] === 'pane' && call[1] === 'run').length,calls);
  state.claimed=true;
  const accepted=await approveRun({ref:'17',cwd:f.record().root,said:'I approve'},ports());
  assert.equal(accepted.exitCode,0,accepted.message); assert.equal(f.record().area,before.area+1); assert.deepEqual(f.record().automaticOrigin,origin);
});

test('malformed origin and mismatched claims fail closed; absent origin keeps legacy behavior',async t=>{
  const {f,ports}=await ready(t); const before=f.record();
  for(const value of [null,{}, {...origin,extra:true}, {...origin,repository:'other/project'}, {...origin,coordinatorId:'other'}, {...origin,machine:'other'}, {...origin,machine:''}, {...origin,claim:{...origin.claim,commentId:'wrong'}}, {...origin,claim:{...origin.claim,labelEventId:'wrong'}}, {...origin,claim:{commentId:'11'}}, {...origin,claim:{...origin.claim,extra:true}}]) {
    const r=f.record(); r.automaticOrigin=value; writeRun(r); const snapshot=f.record();
    assert.equal((await approveRun({ref:'17',cwd:f.source,said:'I approve'},ports())).exitCode,1); assert.deepEqual(f.record(),snapshot);
  }
  const r=f.record(); delete r.automaticOrigin; writeRun(r);
  const result=await approveRun({ref:'17',cwd:f.source,said:'I approve'},ports()); assert.equal(result.exitCode,0,result.message); assert.equal(f.record().area,before.area+1);
});

test('automatic startup refuses incomplete binding',async t=>{
  const f=await fixture(t,{name:'bug',agent:'codex'});
  const result=await startRun({name:'bug',issue:'17',agent:'codex',cwd:f.source,packageRoot},{...f.ports,env:{...f.ports.env,PDD_AUTOPILOT_CONTEXT:'{}'}});
  assert.equal(result.exitCode,1); assert.match(result.message,/invalid automatic start context/i);
});

for (const mode of ['direct', 'environment', 'envelope']) test(`injected admission consumer persists origin from ${mode}`,async t=>{
  const f=await fixture(t,{name:'bug',agent:'codex'});
  const root=realpathSync(f.source), stateRoot=join(f.state,'autopilot'); mkdirSync(stateRoot,{recursive:true});
  writeFileSync(join(f.source,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  writeFileSync(join(stateRoot,`${createHash('sha256').update(root).digest('hex').slice(0,20)}.json`),JSON.stringify({enabled:true,repo:'example/project',cwd:root,coordinatorId:origin.coordinatorId,machine:origin.machine,activatedAt:'activation',startAction:{command:'pdd autopilot start',repository:'example/project',mode:'auto'}}));
  const fixturePath=join(f.base,'reader.json'), logPath=join(f.base,'gh.log');
  writeFileSync(fixturePath,JSON.stringify({labels:['pdd:working'],events:[{id:12,event:'labeled',label:{name:'pdd:working'},actor:{login:'example'}}],comments:[{id:11,user:{login:'example'},body:JSON.stringify({repository:origin.repository,coordinatorId:origin.coordinatorId,machine:origin.machine,labelEventId:'12'})}]}));
  const {execFile: callback}=await import('node:child_process'); const {promisify}=await import('node:util'); const exec=promisify(callback);
  const original=f.ports.execFile;
  const execFile=(file,args,opts)=>file==='gh' && args[0]==='api' && args[1]==='--include' ? exec(process.execPath,[join(packageRoot,'test/helpers/continuation-fake-gh.mjs'),...args],{...opts,env:{...process.env,READER_FIXTURE_FILE:fixturePath,READER_GH_LOG:logPath}}) : original(file,args,opts);
  let admitted=0;
  const coordinator={...origin,activation:'activation'};
  const input = mode === 'envelope' ? {version:'pdd.autopilot-coordinator.v1',repository:origin.repository,coordinatorId:origin.coordinatorId,machine:origin.machine,activation:'activation'} : coordinator;
  const result=await startRun({name:'bug',issue:'17',agent:'codex',cwd:f.source,packageRoot,...(mode === 'environment' ? {} : {coordinator:input})},{...f.ports,env:{...f.ports.env,...(mode === 'environment' ? {PDD_AUTOPILOT_CONTEXT:JSON.stringify(input)} : {})},execFile,autopilotStateRoot:stateRoot,checkDependencyStart:async value=>{admitted++; assert.deepEqual(value.coordinator,coordinator); return {allowed:true,reason:'ok'};}});
  assert.equal(result.exitCode,0,result.message); assert.equal(admitted,1); assert.deepEqual(f.record().automaticOrigin,origin);
  const run=f.record(), initial=readFileSync(join(run.runDir,'story-start.md'),'utf8');
  assert.equal(existsSync(join(run.root,'pdd.json')),false); assert.match(initial,/operator invoked pdd autopilot start/); assert.match(initial,/steps\/autopilot\.md/); assert.match(initial,/example\/project.*auto mode/);
  const delivery=await changeRun({ref:'17',cwd:f.source,text:'Read the owner handoff.',packageRoot},{...f.ports,autopilotStateRoot:stateRoot});
  assert.equal(delivery.exitCode,0,delivery.message); const packet=f.herdr.paneOf(run.chats[0]).agent.prompts.at(-1); assert.match(packet,/Submitted request: Read the owner handoff/); assert.doesNotMatch(packet,/The person asks for changes|then show the result and ask again/); assert.ok(packet.includes(join(packageRoot,'bin','pdd.mjs')));
  if (mode === 'direct') {
    const agentPorts={...f.ports,autopilotStateRoot:stateRoot};
    assert.equal((await stepDone({step:'reproduce',summary:'Reproduced',cwd:run.root,packageRoot},agentPorts)).exitCode,0);
    const gate=await stepDone({step:'prompt-story',summary:'Drafted',cwd:run.root,packageRoot},agentPorts);
    assert.equal(gate.exitCode,0,gate.message); assert.match(gate.message,/operator invoked pdd autopilot start/); assert.match(gate.message,/scoped automatic overlay/); assert.doesNotMatch(gate.message,/Gate: show the person the result/);
  }
});

test('invalid automatic inputs are refused before allocating a run',async t=>{
  const f=await fixture(t,{name:'bug',agent:'codex'});
  const base={name:'bug',issue:'17',agent:'codex',cwd:f.source,packageRoot};
  const context={...origin,activation:'activation'};
  for(const [args,env] of [[{automaticOrigin:origin},{}],[{coordinator:{}},{}],[{coordinator:context},{PDD_AUTOPILOT_CONTEXT:'{}'}],[{}, {PDD_AUTOPILOT_CONTEXT:'not json'}]]) {
    const result=await startRun({...base,...args},{...f.ports,env:{...f.ports.env,...env}});
    assert.equal(result.exitCode,1); assert.match(result.message,/invalid automatic start context/i);
    assert.equal(f.herdr.calls.filter(call=>call[0]==='pane' && call[1]==='run').length,0);
  }
  const result=await startRun({...base,coordinator:context},f.ports);
  assert.equal(result.exitCode,1); assert.match(result.message,/admission binding is incomplete/i);
  assert.equal(f.herdr.calls.filter(call=>call[0]==='pane' && call[1]==='run').length,0);
});

 test('explicit capacity handoff observes the stopped worker before requesting a wake',async t=>{
  const {f,state,ports}=await ready(t); const run=f.record(); let requests=[];
  const p={...ports(),requestAutopilotCompletion:async args=>{requests.push(args);return {state:'reconciled'};}};
  let result=await yieldAutomaticCapacity({ref:'17',cwd:f.source},p);
  assert.equal(result.exitCode,1); assert.equal(requests.length,0);
  const chat=run.chats.find(chat=>chat.area===run.areas[run.area].name);
  const pane=f.herdr.paneOf(chat); pane.agent.agent_status='done';
  state.claimed=false;
  result=await yieldAutomaticCapacity({ref:'17',cwd:f.source},{...ports(),requestAutopilotCompletion:p.requestAutopilotCompletion});
  assert.equal(result.exitCode,1); assert.match(result.message,/claim ownership/); assert.equal(requests.length,0);
  state.claimed=true; ports();
  result=await yieldAutomaticCapacity({ref:'17',cwd:f.source},p);
  assert.equal(result.exitCode,0,result.message); assert.equal(requests.length,1);
  assert.equal(requests[0].cwd,run.sourceRoot); assert.deepEqual(f.record(),run);
  assert.equal(f.herdr.paneOf(chat),pane); assert.equal(pane.agent.agent_status,'done');
  requests=[];
  const registeredAgent=pane.agent;
  f.herdr.paneOf(chat).agent=null; f.clock+=120000;
  result=await yieldAutomaticCapacity({ref:'17',cwd:f.source},p);
  assert.equal(result.exitCode,0,result.message); assert.equal(requests.length,1);
  assert.equal(requests[0].cwd,run.sourceRoot); assert.deepEqual(f.record(),run);
  // Normal post-merge ordering: the issue label has already been removed.
  const completed=f.record(); completed.state='completed'; writeRun(completed);
  state.claimed=false; pane.agent={...pane.agent, agent_status:'done'};
  // Restore the registered native session in the same pane after the absence phase.
  pane.agent=registeredAgent;
  const common=f.git(f.source,'rev-parse','--path-format=absolute','--git-common-dir');
  const index=join(common,'pdd','worktree-assignments','issues','17.json');
  const assignment=join(common,'pdd','worktree-assignments','runs',run.runId+'.json');
  const history=readFileSync(assignment,'utf8'); assert.ok(existsSync(index));
  const calls=f.herdr.calls.length; const ghBefore=readFileSync(join(f.base,'gh.log'),'utf8'); requests=[];
  result=await yieldAutomaticCapacity({ref:'17',cwd:f.source},{...ports(),requestAutopilotCompletion:p.requestAutopilotCompletion});
  assert.equal(result.exitCode,0,result.message); assert.equal(requests.length,1);
  assert.equal(existsSync(index),false); assert.equal(readFileSync(assignment,'utf8'),history);
  assert.ok(existsSync(run.root)); assert.deepEqual(f.record(),completed);
  assert.equal(readFileSync(join(f.base,'gh.log'),'utf8'),ghBefore);
  assert.equal(f.herdr.calls.slice(calls).filter(call=>call[0]==='pane' && ['run','close'].includes(call[1])).length,0);
});
