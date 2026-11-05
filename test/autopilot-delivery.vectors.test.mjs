import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, mkdtempSync, readFileSync, writeFileSync, readdirSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {after} from 'node:test';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';

// External read-only product controls. All writes are under this evidence folder.
// The injected ports never execute a process, timer, agent, or live Herdr command.
const evidence = mkdtempSync(join(tmpdir(), 'pdd-delivery-vectors-'));
after(() => rmSync(evidence, {recursive:true, force:true}));
const vectors = JSON.parse(readFileSync(new URL('./autopilot-delivery/cases.json', import.meta.url), 'utf8'));
const expected = id => vectors.cases.find(row => row.id === id).expect;
const product = fileURLToPath(new URL('..', import.meta.url));
const {runAutopilotLauncher, tickAutopilot} = await import(`${product}/src/autopilot-launcher.mjs`);
const {writeRun, readRun, allRuns} = await import(`${product}/src/workflow-runs.mjs`);
const {sendToChat: guardedSend} = await import(`${product}/src/workflow-chat.mjs`);
const observations = [];
const absent = () => Object.assign(Error('No native agent'), {code:'agent_not_found'});
const issue = number => ({number, state:'open', title:`Synthetic issue ${number}`, body:'Synthetic trusted work.', user:{login:'owner'}, created_at:'2026-11-04T00:01:00Z', updated_at:'2026-11-04T00:01:00Z', comments:0, labels:[], html_url:`https://github.com/owner/repo/issues/${number}`});

function fixture(name, {native='absent', afterLaunch='blocked', screen='Ready\n› '} = {}) {
  const dir = join(evidence, 'worlds', name), cwd = join(dir, 'repo'), home = join(dir, 'home');
  mkdirSync(cwd, {recursive:true}); mkdirSync(home, {recursive:true});
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({autopilot:{mode:'observe', trust:[]}}));
  const f = {name, dir, cwd, home, native, afterLaunch, screen, issues:[issue(101)], calls:[], packets:[], time:Date.parse('2026-11-04T00:00:00Z')};
  f.ports = {
    stateRoot:join(dir,'launcher-state'), platform:'darwin', now:()=>f.time,
    env:{HOME:home, PATH:'/synthetic/no-executables', CODEX_HOME:undefined, CLAUDE_CONFIG_DIR:undefined, GEMINI_CLI_HOME:undefined},
    selectAgent:async()=>({id:'codex',kind:'codex',command:'codex',env:{}}),
    pathDiagnostic:()=>[], timer:async()=>true, warn:()=>{},
    queryIssues:async()=>({status:200,etag:'synthetic',issues:structuredClone(f.issues)}),
    run:async(command,args)=>{
      f.calls.push({port:'process',command,args});
      if(command==='git') return {code:0,stdout:cwd+'\n',stderr:''};
      if(command==='gh' && args[0]==='repo') return {code:0,stdout:'{"nameWithOwner":"owner/repo"}',stderr:''};
      if(command==='gh' && args[0]==='auth') return {code:0,stdout:'',stderr:''};
      if(command==='herdr' && args[0]==='--version') return {code:0,stdout:'synthetic',stderr:''};
      throw Error(`Unexpected process port: ${command} ${args.join(' ')}`);
    },
    herdr:async args=>{
      f.calls.push({port:'herdr',args});
      if(args[0]==='workspace') return {result:{workspace:{workspace_id:'w'},root_pane:{pane_id:'p'}}};
      if(args[0]==='status') return {running:true};
      if(args[0]==='agent' && args[1]==='get') {
        if(f.native==='absent') throw absent();
        return {result:{agent:{agent_status:f.native}}};
      }
      if(args[0]==='pane' && args[1]==='run') {
        f.native=f.afterLaunch;
        return {result:{type:'ok'}};
      }
      if(args[0]==='pane' && args[1]==='read') {
        if(f.screen instanceof Error) throw f.screen;
        return f.screen;
      }
      if(args[0]==='agent' && args[1]==='prompt') {
        f.packets.push(JSON.parse(args[3].trim().split('\n').at(-1)));
        return {result:{type:'ok'}};
      }
      throw Error(`Unexpected Herdr port: ${args.join(' ')}`);
    }
  };
  f.start = async runs => {
    const result = await runAutopilotLauncher({command:'start',cwd,packageRoot:product,env:f.ports.env,...(runs?{runs}:{})},f.ports);
    assert.equal(result.exitCode,0,`Control setup must complete: ${result.message}`);
    f.stateFile=join(f.ports.stateRoot,readdirSync(f.ports.stateRoot).find(x=>x.endsWith('.json')));
    return result;
  };
  f.state=()=>JSON.parse(readFileSync(f.stateFile,'utf8'));
  f.tick=()=>tickAutopilot(f.stateFile,f.ports);
  f.saveObservation=extra=>{
    const value={name,...extra,state:f.state(),calls:f.calls,packets:f.packets};
    observations.push(value);writeFileSync(join(dir,'observation.json'),JSON.stringify(value,null,2)+'\n');
  };
  return f;
}

for(const [name,status] of [['startup-no-agent','absent'],['startup-blocked','blocked'],['startup-unknown','unknown']]) {
  test(`${name}: accepted pane launch must retain first recipe and issue`,async()=>{
    const f=fixture(name,{afterLaunch:status});await f.start();
    const state=f.state();f.saveObservation({nativeAfterLaunch:status});
    assert.equal(Boolean(state.recipeDelivered),expected('empty-owner-then-idle').consumedBeforeReady.includes('recipe'),'A pane acknowledgement is not a successful ready-agent delivery');
    assert.equal(state.seen?.[101],undefined,'Issue must remain pending');
  });
}

test('startup lost work does not return when the native agent later becomes ready',async()=>{
  const f=fixture('startup-recovery',{afterLaunch:'blocked'});await f.start();
  f.native='idle';const before=f.packets.length;await f.tick();f.saveObservation({laterPacketCount:f.packets.length-before});
  assert.equal(f.packets.length-before,1,'The first ready tick must receive pending work');
});

for(const status of ['working','blocked','unknown']) {
  test(`existing ${status} agent preserves pending work`,async()=>{
    const f=fixture(`existing-${status}`,{native:status});await f.start();f.saveObservation({nativeStatus:status});
    assert.equal(f.state().recipeDelivered,undefined);assert.equal(f.state().seen?.[101],undefined);
    assert.equal(f.packets.length,0);
  });
}

for(const [name,screen] of [
  ['model-dialog','Switch model\nPress enter to confirm or esc to go back'],
  ['usage-dialog','Account usage limit reached\nEnter to confirm · Esc to cancel'],
  ['screen-unavailable',Object.assign(Error('unreadable'),{code:'screen_failed'})]
]) {
  test(`existing idle ${name} must not receive a packet`,async()=>{
    const f=fixture(name,{native:'idle',screen});await f.start();
    f.saveObservation({screen:typeof screen==='string'?screen:'screen read would fail',screenReads:f.calls.filter(x=>x.args?.[0]==='pane'&&x.args?.[1]==='read').length});
    assert.equal(f.packets.length,expected('dialog-and-unreadable').submissions,'Keep the packet until the safe delivery boundary allows submission');
  });
  test(`existing workflow safe delivery refuses ${name}`,async()=>{
    let submitted=0,at=0;
    const result=await guardedSend({paneId:'p',startedAt:0},'Synthetic task',{now:()=>at,elapsedNow:()=>at,sleep:async ms=>{at+=ms;},herdr:async args=>{
      if(args[0]==='agent'&&args[1]==='get')return {result:{agent:{agent_status:'idle'}}};
      if(args[0]==='pane'&&args[1]==='read'){if(screen instanceof Error)throw screen;return screen;}
      if(args[0]==='agent'&&args[1]==='prompt'){submitted++;return {};}
      throw Error('Unexpected safe-delivery port');
    }});
    observations.push({name:`guard-${name}`,result,submitted});
    assert.equal(result.ok,false);assert.equal(submitted,0);
  });
}

test('ready idle submission consumes work once',async()=>{
  const f=fixture('idle-positive',{native:'idle',screen:'Ready\n› '});await f.start();
  assert.equal(f.packets.length,expected('empty-owner-then-idle').submissions);assert.equal(f.state().recipeDelivered,true);assert.ok(f.state().seen[101]);
  await f.tick();assert.equal(f.packets.length,1);f.saveObservation({});
});


// The JSON files remain the authority for these native authoring cases.
const handoff = JSON.parse(readFileSync(new URL('./autopilot-workflow-handoff/cases.json', import.meta.url), 'utf8'));
const handoffExpected = id => handoff.cases.find(row => row.id === id).expect;

test('safe done owner receives acknowledged work', async () => {
  const f=fixture('done-positive',{native:'done'}); await f.start();
  assert.equal(f.packets.length,expected('safe-done').submissions);
  assert.equal(f.state().recipeDelivered,expected('safe-done').acknowledged);
});

test('rejected submission retains work and uncertain submission is not resent', async () => {
  for (const uncertain of [false,true]) {
    const f=fixture(`submission-${uncertain}`,{native:'idle'}), original=f.ports.herdr; let attempts=0;
    f.ports.herdr=async args=>{ if(args[0]==='agent'&&args[1]==='prompt') { attempts++; throw Object.assign(Error('submission failed'),{code: uncertain?'transport_lost':'agent_not_found'}); } return original(args); };
    await f.start(); assert.equal(f.state().recipeDelivered,undefined); assert.equal(f.state().seen?.[101],undefined);
    const intent=Boolean(f.state().deliveryIntent); await f.tick();
    if(uncertain) { assert.equal(intent,true); assert.equal(f.state().deliveryIntent != null,expected('uncertain-custody').custody==='uncertain'); assert.equal(attempts,1); }
    else { assert.equal(intent,false); assert.equal(attempts,2); }
  }
});

test('confirmed launch rejection retries pending work; uncertain launch retains custody', async () => {
  for (const confirmed of [true, false]) {
    const f=fixture(`launch-retry-${confirmed}`,{afterLaunch:'idle'}), original=f.ports.herdr; let launches=0;
    // Exercise the native adapter: structured error reply versus an ambiguous transport failure.
    delete f.ports.herdr;
    const run=f.ports.run;
    f.ports.run=async (command,args)=>{
      if(command!=='herdr' || args[0]!=='--session') return run(command,args);
      const request=args.slice(2);
      if(request[0]==='pane' && request[1]==='run' && ++launches===1) {
        if(confirmed) return {code:1,stdout:'',stderr:JSON.stringify({error:{code:'permission_denied',message:'Denied'}})};
        throw Error('transport lost');
      }
      const reply=await original(request);
      return {code:0,stdout:typeof reply==='string'?reply:JSON.stringify(reply),stderr:''};
    };
    await f.start();
    assert.equal(Boolean(f.state().ownerLaunch),!confirmed);
    assert.equal(f.state().recipeDelivered,undefined); assert.equal(f.state().seen?.[101],undefined);
    await f.tick();
    assert.equal(launches,confirmed?2:1);
    if(confirmed) { assert.equal(f.state().recipeDelivered,true); assert.ok(f.state().seen[101]); assert.equal(f.packets.length,1); }
    else { assert.equal(f.state().recipeDelivered,undefined); assert.equal(f.state().seen?.[101],undefined); assert.equal(f.packets.length,0); }
  }
});

test('new owner admission respects the original launch window through submission', async () => {
  for (const mode of ['before-boundary', 'launch-expired', 'screen-expired', 'recheck-expired', 'transport-expired', 'backward-clock']) {
    const f=fixture(`deadline-${mode}`,{afterLaunch:'idle'}), original=f.ports.herdr;
    let elapsed=0, launched=false, inspections=0;
    f.ports.elapsedNow=()=>elapsed;
    if(mode==='transport-expired') f.ports.now=()=>{
      let files=[]; try { files=readdirSync(f.ports.stateRoot, {withFileTypes:true}).filter(x=>x.name.endsWith('.json')); } catch (error) { if(error.code!=='ENOENT') throw error; }
      if(files.some(x=>JSON.parse(readFileSync(join(f.ports.stateRoot,x.name),'utf8')).deliveryIntent)) return f.time+30000;
      return f.time;
    };
    f.ports.herdr=async args=>{
      if(args[0]==='pane' && args[1]==='run') {
        const result=await original(args); launched=true;
        if(mode==='before-boundary') { f.time+=29999; elapsed=29999; }
        if(mode==='launch-expired') { f.time+=30000; elapsed=30000; }
        if(mode==='backward-clock') { f.time-=1000; elapsed=30000; }
        return result;
      }
      if(launched && args[0]==='agent' && args[1]==='get' && ++inspections===2 && mode==='recheck-expired') { f.time+=30000; elapsed=30000; }
      if(launched && args[0]==='pane' && args[1]==='read' && mode==='screen-expired') { f.time+=30000; elapsed=30000; }
      return original(args);
    };
    const anchor=f.time;
    await f.start();
    const admitted=mode==='before-boundary';
    assert.equal(f.state().ownerLaunch.startedAt,anchor,mode);
    assert.equal(f.packets.length,Number(admitted),mode);
    assert.equal(Boolean(f.state().recipeDelivered),admitted,mode);
    assert.equal(Boolean(f.state().seen?.[101]),admitted,mode);
    assert.equal(Boolean(f.state().deliveryIntent),false,mode);
  }
});

test('packet carries bundled command and selected profile without unrelated values', async () => {
  const f=fixture('metadata',{native:'idle'});
  f.ports.env.CODEX_HOME='/selected/config'; f.ports.env.SECRET_VALUE='private';
  await f.start(); const packet=f.packets[0], e=handoffExpected('bundled-command-and-family');
  assert.equal(packet.workflow.pddBin,join(product,'bin/pdd.mjs')); assert.equal(packet.workflow.agent,e.agent);
  assert.equal(packet.workflow.home,f.home); assert.equal(packet.workflow.configHome.path,'/selected/config');
  assert.equal(JSON.stringify(packet).includes('private'),handoffExpected('metadata-and-environment-boundary').packetIncludesCredentials);
  assert.equal(packet.issues[0].body,'Synthetic trusted work.');
});

test('absent saved config stays absent in packet after caller changes', async () => {
  const f=fixture('absent-config',{native:'blocked'}); await f.start();
  f.ports.env={HOME:'/later/home',CODEX_HOME:'/later/config'}; f.native='idle'; await f.tick();
  assert.equal(f.packets[0].workflow.configHome,handoffExpected('absent-config').packetConfigPath);
  assert.equal(f.packets[0].workflow.home,f.home);
});

// Skill execution is an interactive agent responsibility, not a launcher operation.
for (const id of ['normal-workflow-order','reuse-normal-workflow']) {
  test.todo(`${id}: interactive skill execution is not replayed by native launcher ports`);
}

test('recreated pane retains pending work and saved bindings', async () => {
  const f=fixture('recreation',{afterLaunch:'blocked'}); f.ports.env.CODEX_HOME='/selected/config'; await f.start();
  const original=f.ports.herdr; let missing=true;
  f.ports.herdr=async args=>{if(missing&&args[0]==='agent'&&args[1]==='get'){missing=false;throw Object.assign(Error('missing'),{code:'pane_not_found'});} return original(args);};
  f.ports.env={HOME:'/later/home',CODEX_HOME:'/later/config'}; await f.tick();
  const runs=f.calls.filter(c=>c.args?.[0]==='pane'&&c.args?.[1]==='run');
  assert.equal(runs.length,2); assert.match(runs[1].args[3],/\/selected\/config/); assert.match(runs[1].args[3],new RegExp(f.home));
  assert.equal(f.state().recipeDelivered,undefined); assert.equal(f.state().seen?.[101],undefined);
  f.native='idle'; await f.tick(); assert.equal(f.packets[0].workflow.home,f.home);
  assert.equal(f.packets[0].workflow.configHome.path,'/selected/config');
  assert.equal(expected('recreate').session,'pdd-autopilot');
});

test('replacement target is not sent the original packet', async () => {
  const f=fixture('replacement',{native:'idle'}), original=f.ports.herdr; let reads=0;
  f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='get') { reads++; return {result:{agent:{agent_status:'idle',agent_session:reads>1?'replacement':'original'}}}; } return original(args);};
  await f.start(); assert.equal(f.packets.length,expected('target-replaced').replacementSubmissions);
  assert.equal(f.state().recipeDelivered,undefined);
});

test('existing owner retains null or absent session identity', async () => {
  for (const initial of ['null', 'absent']) for (const replacement of [false, true]) {
    const f=fixture(`existing-${initial}-${replacement}`,{native:'idle'}), original=f.ports.herdr; let reads=0;
    f.ports.herdr=async args=>{
      if(args[0]==='agent' && args[1]==='get') {
        reads++;
        const agent={agent_status:'idle'};
        if(replacement && reads>1) agent.agent_session='replacement';
        else if(initial==='null') agent.agent_session=null;
        return {result:{agent}};
      }
      return original(args);
    };
    await f.start();
    assert.equal(f.packets.length,replacement?0:1,`${initial}: replacement must not receive packet`);
  }
});

test('new owner acquires its first session and retains that identity', async () => {
  for (const replacement of [false,true]) {
    const f=fixture(`new-identity-${replacement}`,{afterLaunch:'idle'}), original=f.ports.herdr; let launched=false, reads=0;
    f.ports.herdr=async args=>{
      if(args[0]==='pane' && args[1]==='run') { launched=true; return original(args); }
      if(launched && args[0]==='agent' && args[1]==='get') {
        reads++;
        return {result:{agent:{agent_status:reads===1?'starting':'idle',agent_session:reads===1?null:replacement && reads>2?'replacement':'first'}}};
      }
      return original(args);
    };
    await f.start();
    assert.equal(f.packets.length,replacement?0:1,`new owner: ${replacement?'replacement refused':'first session accepted'}`);
  }
});

test('launch identity is saved before empty dispatch', async () => {
  const f=fixture('launch-identity'), original=f.ports.herdr; let saved;
  f.ports.herdr=async args=>{if(args[0]==='pane'&&args[1]==='run') {const file=join(f.ports.stateRoot,readdirSync(f.ports.stateRoot).find(x=>x.endsWith('.json')));saved=JSON.parse(readFileSync(file));}return original(args);};
  await f.start(); assert.equal(Boolean(saved.ownerLaunch?.startedAt),expected('launch-identity').originalLaunchTimePersistedBeforeDispatch);
  assert.equal(f.calls.filter(c=>c.args?.[0]==='pane'&&c.args?.[1]==='run').length,expected('launch-identity').emptyLaunches);
  assert.equal(f.packets.length,0);
});

test('changed launcher family requires explicit start and preserves work', async () => {
  const f=fixture('family-mismatch',{afterLaunch:'blocked'});
  const config=join(f.home,'.config','pdd'); mkdirSync(config,{recursive:true});
  const definition={name:'selected',kind:'codex',command:'codex',env:{}};
  writeFileSync(join(config,'agents.json'),JSON.stringify({include_defaults:false,agents:[definition]}));
  const {loadAgentDefinitions}=await import('../src/agent-config.mjs');
  f.ports.selectAgent=async()=>loadAgentDefinitions({cwd:f.cwd,env:f.ports.env})[0];
  const warnings=[]; f.ports.warn=msg=>warnings.push(msg); await f.start();
  definition.kind='claude'; writeFileSync(join(config,'agents.json'),JSON.stringify({include_defaults:false,agents:[definition]}));
  const original=f.ports.herdr; let missing=true;
  f.ports.herdr=async args=>{if(missing&&args[0]==='agent'&&args[1]==='get'){missing=false;throw Object.assign(Error('missing'),{code:'pane_not_found'});}return original(args);};
  await f.tick(); assert.equal(f.calls.filter(c=>c.args?.[0]==='pane'&&c.args?.[1]==='run').length,1);
  assert.equal(f.state().recipeDelivered,undefined); assert.ok(warnings.some(x=>x.includes('pdd autopilot start')));
  const restarted=await runAutopilotLauncher({command:'start',cwd:f.cwd,packageRoot:product,env:f.ports.env},f.ports);
  assert.equal(restarted.exitCode,0); assert.equal(f.state().agent.kind,'claude');
});

test('failed launch leaves recipe and issue pending', async () => {
  const f=fixture('launch-failure'), original=f.ports.herdr;
  f.ports.herdr=async args=>{if(args[0]==='pane'&&args[1]==='run') throw Object.assign(Error('failed'),{code:'pane_not_found'});return original(args);};
  const result=await runAutopilotLauncher({command:'start',cwd:f.cwd,packageRoot:product,env:f.ports.env},f.ports);
  assert.equal(result.exitCode,0); // Timer installation succeeds even when the immediate tick warns.
  f.stateFile=join(f.ports.stateRoot,readdirSync(f.ports.stateRoot).find(x=>x.endsWith('.json')));
  assert.equal(f.state().recipeDelivered,undefined); assert.equal(f.state().seen?.[101],undefined);
});

test('recreated owner unsets absent config even when later environment supplies it', async () => {
  const f=fixture('recreation-absent',{afterLaunch:'blocked'}); await f.start();
  f.ports.env={HOME:'/later/home',CODEX_HOME:'/later/config'};
  const original=f.ports.herdr; let missing=true;
  f.ports.herdr=async args=>{if(missing&&args[0]==='agent'&&args[1]==='get'){missing=false;throw Object.assign(Error('missing'),{code:'pane_not_found'});}return original(args);};
  await f.tick(); const run=f.calls.filter(c=>c.args?.[0]==='pane'&&c.args?.[1]==='run').at(-1).args[3];
  assert.match(run,/-u CODEX_HOME/); assert.doesNotMatch(run,/\/later\/config/); assert.match(run,new RegExp(f.home));
  assert.equal(f.state().recipeDelivered,undefined);
});

test('saved definition home reloads native command and non-profile environment on recreation', async () => {
  const f=fixture('definition-reload',{afterLaunch:'blocked'}), config=join(f.home,'.config','pdd'); mkdirSync(config,{recursive:true});
  const selectedHome=join(f.dir,'selected-home'), selectedConfig=join(f.dir,'selected-config'), log=join(f.dir,'child.jsonl');
  const command=join(f.dir,'native-stub');
  writeFileSync(command,`#!${process.execPath}\nrequire('node:fs').appendFileSync(${JSON.stringify(log)}, JSON.stringify({home:process.env.HOME,config:process.env.CODEX_HOME,other:process.env.VECTOR_VALUE,argv:process.argv.slice(2)})+'\\n');\n`,{mode:0o755});
  const definition={name:'selected',kind:'codex',command,env:{HOME:selectedHome,CODEX_HOME:selectedConfig,VECTOR_VALUE:'original'}};
  const writeDefinition=()=>writeFileSync(join(config,'agents.json'),JSON.stringify({include_defaults:false,agents:[definition]})); writeDefinition();
  const {loadAgentDefinitions}=await import('../src/agent-config.mjs'); f.ports.selectAgent=async()=>loadAgentDefinitions({cwd:f.cwd,env:f.ports.env})[0];
  const original=f.ports.herdr; let missing=false;
  f.ports.herdr=async args=>{if(missing&&args[0]==='agent'&&args[1]==='get'){missing=false;throw Object.assign(Error('missing'),{code:'pane_not_found'});} const reply=await original(args); if(args[0]==='pane'&&args[1]==='run') execFileSync('/bin/sh',['-c',args[3]],{cwd:f.cwd,env:{HOME:'/caller',CODEX_HOME:'/caller-config',PATH:'/usr/bin:/bin'}});return reply;};
  await f.start(); definition.env.CODEX_HOME='/changed-config'; definition.env.VECTOR_VALUE='reloaded'; writeDefinition();
  f.ports.env={HOME:'/later',CODEX_HOME:'/later-config'}; missing=true; await f.tick();
  const children=readFileSync(log,'utf8').trim().split('\n').map(JSON.parse); assert.equal(children.length,2);
  assert.equal(children[1].home,selectedHome); assert.equal(children[1].config,selectedConfig); assert.equal(children[1].other,'reloaded');
  assert.equal(f.state().recipeDelivered,undefined); f.native='idle'; await f.tick();
  assert.equal(f.packets[0].workflow.home,selectedHome); assert.equal(f.packets[0].workflow.configHome.path,selectedConfig);
  assert.equal(JSON.stringify(f.packets[0]).includes('reloaded'),false);
});
