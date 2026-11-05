import test, {after} from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, mkdtempSync, readFileSync, writeFileSync, readdirSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
const evidence = mkdtempSync(join(tmpdir(), 'pdd-formal-'));
after(() => rmSync(evidence, {recursive:true, force:true}));
const product = fileURLToPath(new URL('..', import.meta.url));
const {runAutopilotLauncher, tickAutopilot} = await import(`${product}/src/autopilot-launcher.mjs`);
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

// Oracle: the Story permits submission only to the same ready coordinator on
// a readable, dialog-free screen; only acknowledgement consumes the work.
test('bounded delivery decisions preserve pending work', async () => {
  let n=0;
  for (const status of ['idle','done','working','blocked','unknown']) {
    for (const screen of ['Ready\n› ', 'Switch model\nPress enter to confirm or esc to go back', Object.assign(Error('unreadable'),{code:'screen_failed'})]) {
      const f=fixture(`decision-${n++}`,{native:status,screen}); await f.start();
      const permitted = ['idle','done'].includes(status) && screen === 'Ready\n› ';
      assert.equal(f.packets.length, Number(permitted), `${status} / ${String(screen)}`);
      assert.equal(Boolean(f.state().recipeDelivered), permitted);
      assert.equal(Boolean(f.state().seen?.[101]), permitted);
    }
  }
});

test('bounded launch, identity and acknowledgement outcomes', async () => {
  for (const mode of ['launch','replacement','reject','uncertain','ack']) {
    const f=fixture(`outcome-${mode}`,{native:mode==='launch'?'absent':'idle',afterLaunch:'blocked'});
    const original=f.ports.herdr; let reads=0, attempts=0;
    f.ports.herdr=async args=>{
      if(mode==='replacement' && args[0]==='agent' && args[1]==='get') return {result:{agent:{agent_status:'idle',agent_session:++reads>1?'replacement':'original'}}};
      if(args[0]==='agent' && args[1]==='prompt') {
        attempts++;
        if(mode==='reject'||mode==='uncertain') throw Object.assign(Error('submission failed'),{code:mode==='reject'?'agent_not_found':'transport_lost'});
      }
      return original(args);
    };
    await f.start();
    assert.equal(Boolean(f.state().recipeDelivered),mode==='ack',mode);
    assert.equal(Boolean(f.state().seen?.[101]),mode==='ack',mode);
    if(mode==='replacement') assert.equal(attempts,0);
    if(mode==='launch') { f.native='idle'; await f.tick(); assert.equal(f.packets.length,1); }
    if(mode==='reject'||mode==='uncertain') {
      await f.tick();
      assert.equal(attempts,mode==='reject'?2:1,mode);
      assert.equal(Boolean(f.state().deliveryIntent),mode==='uncertain',mode);
    }
    if(mode==='ack') { await f.tick(); assert.equal(attempts,1); }
  }
});

// A definite refusal leaves launch retryable; a lost reply may have started it.
test('bounded launch rejection and uncertain custody', async () => {
  for (const confirmed of [true, false]) {
    const f=fixture(`launch-custody-${confirmed}`,{afterLaunch:'idle'});
    const herdr=f.ports.herdr, run=f.ports.run; let launches=0;
    delete f.ports.herdr;
    f.ports.run=async (command,args)=>{
      if(command!=='herdr' || args[0]!=='--session') return run(command,args);
      const request=args.slice(2);
      if(request[0]==='pane' && request[1]==='run' && ++launches===1) {
        if(confirmed) return {code:1,stdout:'',stderr:JSON.stringify({error:{code:'permission_denied',message:'Denied'}})};
        throw Error('transport lost');
      }
      const reply=await herdr(request);
      return {code:0,stdout:typeof reply==='string'?reply:JSON.stringify(reply),stderr:''};
    };
    await f.start();
    assert.equal(Boolean(f.state().recipeDelivered),false);
    assert.equal(Boolean(f.state().seen?.[101]),false);
    await f.tick();
    assert.equal(launches,confirmed?2:1);
    assert.equal(Boolean(f.state().recipeDelivered),confirmed);
    assert.equal(Boolean(f.state().seen?.[101]),confirmed);
    if(confirmed) {
      await f.tick();
      assert.equal(f.packets.length,1);
      assert.equal(Boolean(f.state().recipeDelivered),true);
      assert.equal(Boolean(f.state().seen?.[101]),true);
    }
  }
});

// Approved first-launch rule: readiness remains bounded by the original launch,
// and only the original idle/done owner on a readable screen receives work.
test('bounded first launch continues safely in the same tick', async () => {
  for (const mode of ['delayed-idle','delayed-done','blocked','dialog','unreadable','absent','unknown','replacement','uncertain']) {
    const f=fixture(`first-${mode}`);
    const herdr=f.ports.herdr, warnings=[]; let inspections=0, attempts=0, launched=false;
    f.ports.warn=message=>warnings.push(message);
    f.ports.herdr=async args=>{
      if(args[0]==='pane' && args[1]==='run') { launched=true; return herdr(args); }
      if(launched && args[0]==='agent' && args[1]==='get') {
        inspections++;
        if(mode==='absent') { f.time+=30001; throw absent(); }
        if(mode==='unknown') { f.time+=30001; return {result:{agent:{agent_status:'unknown',agent_session:'original'}}}; }
        if(mode==='replacement') return {result:{agent:{agent_status:'idle',agent_session:inspections===1?'original':'replacement'}}};
        const status=mode==='blocked'?'blocked':(['delayed-idle','delayed-done'].includes(mode) && inspections===1?'starting':mode==='delayed-done'?'done':'idle');
        return {result:{agent:{agent_status:status,agent_session:'original'}}};
      }
      if(args[0]==='pane' && args[1]==='read') {
        if(mode==='dialog') return 'Switch model\nPress enter to confirm or esc to go back';
        if(mode==='unreadable') throw Error('screen unavailable');
      }
      if(args[0]==='agent' && args[1]==='prompt') {
        attempts++;
        if(mode==='uncertain') throw Object.assign(Error('transport lost'),{code:'transport_lost'});
      }
      return herdr(args);
    };
    const startTime=f.time;
    await f.start();
    const ready=mode==='delayed-idle'||mode==='delayed-done';
    assert.equal(f.packets.length,Number(ready),`${mode}: first start packet`);
    assert.equal(Boolean(f.state().recipeDelivered),ready,`${mode}: recipe custody`);
    assert.equal(Boolean(f.state().seen?.[101]),ready,`${mode}: issue custody`);
    assert.equal(f.state().ownerLaunch.startedAt,startTime,`${mode}: original anchor`);
    assert.equal(f.calls.filter(c=>c.port==='herdr' && c.args[0]==='pane' && c.args[1]==='run').length,1,`${mode}: one launch`);
    if(!ready) assert.ok(warnings.some(w=>/pending/i.test(w)),`${mode}: plain pending reason`);
    if(mode==='uncertain') { assert.equal(attempts,1); assert.ok(f.state().deliveryIntent); }
    else if(!ready) assert.equal(attempts,0,`${mode}: no unsafe submission`);
    if(ready) { assert.equal(f.packets[0].workflow.home,f.home); assert.equal(f.packets[0].workflow.agent,'codex'); }
  }
});

// The original startup window permits submission strictly before its deadline.
// Exercise expiry at launch completion, screen read, and final target read.
test('bounded first-launch deadline gates submission', async () => {
  for (const stage of ['launch','screen','target']) {
    for (const clock of ['wall','elapsed-rewind']) {
      for (const age of [29999,30000,30001]) {
        const f=fixture(`deadline-${stage}-${clock}-${age}`,{afterLaunch:'idle'});
        const herdr=f.ports.herdr, warnings=[]; let elapsed=0, launched=false, gets=0;
        f.ports.elapsedNow=()=>elapsed;
        f.ports.warn=message=>warnings.push(message);
        const advance=()=>{ if(clock==='wall') f.time+=age; else { f.time-=1000; elapsed=age; } };
        f.ports.herdr=async args=>{
          const reply=await herdr(args);
          if(args[0]==='pane' && args[1]==='run') { launched=true; if(stage==='launch') advance(); }
          if(launched && args[0]==='pane' && args[1]==='read' && stage==='screen') advance();
          if(launched && args[0]==='agent' && args[1]==='get' && ++gets===2 && stage==='target') advance();
          return reply;
        };
        await f.start();
        const allowed=age<30000;
        assert.equal(f.packets.length,Number(allowed),`${stage}/${clock}/${age}: packet`);
        assert.equal(Boolean(f.state().recipeDelivered),allowed,`${stage}/${clock}/${age}: recipe`);
        assert.equal(Boolean(f.state().seen?.[101]),allowed,`${stage}/${clock}/${age}: issue`);
        if(!allowed) assert.ok(warnings.some(w=>/pending/i.test(w)),`${stage}/${clock}/${age}: pending reason`);
      }
    }
  }
});

// An existing owner has an observed identity even when its session is absent.
// A newly launched owner may acquire its first actual session during startup.
test('bounded owner identity remains tied to the observed coordinator', async () => {
  for (const initial of ['absent','null','known']) {
    for (const target of ['same','replacement']) {
      const f=fixture(`identity-existing-${initial}-${target}`,{native:'idle'});
      const herdr=f.ports.herdr; let gets=0;
      const agent=(value)=>({result:{agent:{agent_status:'idle',...(value==='absent'?{}:{agent_session:value==='null'?null:value})}}});
      f.ports.herdr=async args=>{
        if(args[0]==='agent' && args[1]==='get') return agent(++gets===1?initial:(target==='same'?initial:'replacement'));
        return herdr(args);
      };
      await f.start();
      const allowed=target==='same';
      assert.equal(f.packets.length,Number(allowed),`${initial}/${target}: packet`);
      assert.equal(Boolean(f.state().recipeDelivered),allowed,`${initial}/${target}: recipe`);
      assert.equal(Boolean(f.state().seen?.[101]),allowed,`${initial}/${target}: issue`);
    }
  }
  for (const target of ['same','replacement']) {
    const f=fixture(`identity-new-${target}`); const herdr=f.ports.herdr; let launched=false, gets=0;
    f.ports.herdr=async args=>{
      if(args[0]==='pane' && args[1]==='run') { launched=true; return herdr(args); }
      if(launched && args[0]==='agent' && args[1]==='get') {
        gets++;
        return {result:{agent:gets===1?{agent_status:'starting'}:{agent_status:'idle',agent_session:gets===2||target==='same'?'original':'replacement'}}};
      }
      return herdr(args);
    };
    await f.start();
    const allowed=target==='same';
    assert.equal(f.packets.length,Number(allowed),`new/${target}: packet`);
    assert.equal(Boolean(f.state().recipeDelivered),allowed,`new/${target}: recipe`);
    assert.equal(Boolean(f.state().seen?.[101]),allowed,`new/${target}: issue`);
  }
});
