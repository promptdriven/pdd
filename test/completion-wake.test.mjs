import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { createHash } from 'node:crypto';
import { runPdd } from '../src/pdd-cli.mjs';
import { autopilotLaunchFingerprint } from '../src/autopilot-launcher.mjs';

const capture = () => ({ text: '', write(s) { this.text += s; } });

test('completion preserves intake output and asks once after acceptance', async () => {
  for (const reply of ['complete', 'pending']) for (const outcome of [{state:'reconciled'}, {state:'busy'}, {}, new Error('failure')]) {
    const stdout = capture(), stderr = capture(), calls = [];
    const code = await runPdd(['dependencies','complete','--input','-'], { cwd:'/repo', env:{HOME:'/home'}, stdin:'{}', stdout, stderr,
      dependencyIntake:{runDependencyIntake:async () => { calls.push('intake'); return {exitCode:0,message:reply+'\n'}; }},
      autopilotLauncher:{requestAutopilotCompletion:async input => { calls.push(input); if (outcome instanceof Error) throw outcome; return outcome; }} });
    assert.equal(code,0); assert.equal(stdout.text,reply+'\n'); assert.equal(calls.length,2); assert.equal(calls[0],'intake');
    assert.deepEqual(calls[1],{cwd:'/repo',env:{HOME:'/home'}});
    if (outcome.state === 'reconciled') assert.equal(stderr.text,''); else assert.match(stderr.text,/reconciliation.*not confirmed/i);
  }
});

test('prepare and rejected completion do not request wake', async () => {
  for (const args of [['dependencies','prepare'],['dependencies','complete','--input','-']]) {
    let wakes=0; const stdout=capture(),stderr=capture();
    await runPdd(args,{cwd:'/repo',stdin:'{}',stdout,stderr,dependencyIntake:{runDependencyIntake:async()=>({exitCode:2,message:'rejected\n'})},autopilotLauncher:{requestAutopilotCompletion:async()=>{wakes++;}}});
    assert.equal(wakes,0);
  }
});

test('default launcher reads current state and reconciles completion under its existing tick lock', async t => {
  const dir=mkdtempSync(join(tmpdir(),'pdd-completion-')); t.after(()=>rmSync(dir,{recursive:true,force:true}));
  const cwd=join(dir,'repo'),home=join(dir,'home'),stateRoot=join(dir,'state'); mkdirSync(cwd); mkdirSync(home); mkdirSync(stateRoot);
  const id=createHash('sha256').update(cwd).digest('hex').slice(0,20),file=join(stateRoot,id+'.json');
  writeFileSync(join(cwd,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',trust:[]}}));
  let calls=[]; const ports={stateRoot,allocationCheck:async()=>({state:'ready',message:''}),run:async(cmd)=>cmd==='git'?{code:0,stdout:cwd+'\n'}:{code:0,stdout:''},queryIssues:async()=>({status:304}),reconcileDependencyIntake:async input=>{calls.push(input);return {queued:[],eligible:[],skipped:[],pending:false};}};
  const {requestAutopilotCompletion}=await import('../src/autopilot-launcher.mjs');
  assert.deepEqual(await requestAutopilotCompletion({cwd,env:{HOME:home}},ports),{state:'inactive'});
  writeFileSync(file,JSON.stringify({enabled:true,cwd,repo:'example/project',stateFile:file,coordinatorId:'c',machine:'m',agent:{id:'codex',kind:'codex',command:'codex'},recipeDelivered:true,environment:{HOME:home}}));
  const stdout=capture(), stderr=capture();
  assert.equal(await runPdd(['dependencies','complete','--input','-'], {cwd,env:{HOME:home},stdin:'{}',stdout,stderr,dependencyIntake:{runDependencyIntake:async()=>({exitCode:0,message:'accepted\n'})},autopilotLauncherPorts:ports}),0);
  assert.equal(stdout.text,'accepted\n'); assert.equal(stderr.text,'');
  assert.equal(calls.length,1); assert.equal(calls[0].trigger,'completion'); assert.equal(calls[0].mode,'auto');
  const activation='2026-01-01T00:00:00Z', coordinator={version:'pdd.autopilot-coordinator.v1',repository:'example/project',coordinatorId:'c',machine:'m',activation};
  const saved=JSON.parse(readFileSync(file,'utf8'));
  writeFileSync(file,JSON.stringify({...saved,activatedAt:activation,paneId:'p',workspaceId:'w',ownerLaunch:{paneId:'p',startedAt:1,coordinator,profile:{agent:{id:'codex',kind:'codex'},home,definitionHome:home,configHome:null},fingerprint:autopilotLaunchFingerprint({cwd,agent:{kind:"codex"}})}}));
  let idle=false, resume, sent=[];
  const row={number:7,state:'open',title:'Issue',body:'Work',user:{login:'example'},created_at:activation,updated_at:activation,comments:0,labels:[],html_url:'https://github.com/example/project/issues/7'};
  const activePorts={...ports,run:async cmd=>cmd==='git'?{code:0,stdout:cwd+'\n'}:{code:0,stdout:JSON.stringify({nameWithOwner:'example/project',url:'https://github.com/example/project'})},now:()=>Date.parse('2026-01-02T00:00:00Z'),warn:()=>{},queryIssues:async()=>({status:200,issues:[row]}),reconcileDependencyIntake:async()=>({queued:[],eligible:[row.html_url],skipped:[],pending:false}),wait:async()=>{idle=true;},armCoordinatorIdle:(_identity,options)=>{resume=options.resume;},herdr:async args=>{
    const live={pane_id:'p',workspace_id:'w',cwd,foreground_cwd:cwd,tab_id:'t',terminal_id:'term',agent:'codex',agent_status:idle?'idle':'working',agent_session:'session'};
    if(args[0]==='agent'&&args[1]==='get') return {result:{type:'agent_info',agent:live}};
    if(args[0]==='pane'&&args[1]==='get') return {result:{type:'pane_info',pane:live}};
    if(args[0]==='workspace'&&args[1]==='get') return {result:{type:'workspace_info',workspace:{workspace_id:'w'}}};
    if(args[0]==='pane'&&args[1]==='read') return '';
    if(args[0]==='agent'&&args[1]==='prompt') { const text=args.at(-1), match=/Artifact path: (.+)/.exec(text);sent.push(match?readFileSync(JSON.parse(match[1]),'utf8'):text); return {}; }
    throw Error(args.join(' '));
  }};
  assert.deepEqual(await requestAutopilotCompletion({cwd,env:{HOME:home}},activePorts),{state:'reconciled'});
  assert.equal(typeof resume,'function'); assert.equal(sent.length,0); await resume();
  assert.equal(sent.length,1); assert.match(sent[0], /"number":7,/);
  assert.deepEqual(await requestAutopilotCompletion({cwd,env:{HOME:home}},activePorts),{state:'reconciled'});
  assert.equal(sent.length,2); assert.match(sent[1], /\"number\":7,/);
  writeFileSync(file,JSON.stringify(saved));
  writeFileSync(file+'.lock',String(process.pid));
  assert.deepEqual(await requestAutopilotCompletion({cwd,env:{HOME:home}},ports),{state:'busy'}); assert.equal(calls.length,1);
  rmSync(file+'.lock');
  const state=JSON.parse((await import('node:fs')).readFileSync(file,'utf8'));
  writeFileSync(file,JSON.stringify({...state,retryAt:Date.now()+60000}));
  assert.deepEqual(await requestAutopilotCompletion({cwd,env:{HOME:home}},ports),{state:'unknown'}); assert.equal(calls.length,1);
  writeFileSync(file,JSON.stringify({...state,enabled:false}));
  assert.deepEqual(await requestAutopilotCompletion({cwd,env:{HOME:home}},ports),{state:'inactive'});
  writeFileSync(file,JSON.stringify(state));
  writeFileSync(join(cwd,'pdd.json'),JSON.stringify({autopilot:{mode:'off',trust:[]}}));
  assert.deepEqual(await requestAutopilotCompletion({cwd,env:{HOME:home}},ports),{state:'inactive'}); assert.equal(calls.length,1);
});
