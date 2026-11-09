import './helpers/test-home.mjs';
import test from 'node:test';
import {mkdtempSync,rmSync,existsSync,mkdirSync,writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {runAutopilotDoctor} from '../src/autopilot-doctor.mjs';
import {runPdd} from '../src/pdd-cli.mjs';
import {runAutopilotLauncher} from '../src/autopilot-launcher.mjs';
import {doctorFixture} from './helpers/doctor-fixture.mjs';
import {checkRuntimeHealth} from '../src/runtime-client.mjs';

const invoke=async(f,command='doctor')=>{
  let stdout='',stderr='';
  const code=await runPdd(['autopilot',command],{...f.input,stdout:{write:s=>stdout+=s},stderr:{write:s=>stderr+=s},autopilotLauncherPorts:{doctorPorts:f.ports,run:async()=>f.answer('',1),stateRoot:'/forbidden-state'},autopilotGithubPorts:{github:{repository:()=>assert.fail('No GitHub publication')}}});
  return {code,text:stdout+stderr};
};
const check=(result,id,status)=>assert.match(result.text,new RegExp(`(?:^|\\n)${status} ${id}:`));

test('doctor: all checks are read-only and each line includes a command',async()=>{
  const f=doctorFixture(),r=await invoke(f);
  assert.equal(r.code,0,r.text);check(r,'path','PASS');check(r,'interpreter','PASS');
  assert.equal(r.text.trim().split('\n').length,20);
  for(const line of r.text.trim().split('\n'))assert.match(line,/^(PASS|WARN|FAIL) [a-z-]+:.*; fix: .+/);
  assert.ok(f.calls.every(c=>!c.args || !(c.args.includes('POST')||c.args.includes('exec')||c.args.includes('start'))));
  const reads=f.calls.filter(c=>c.url);assert.equal(reads.length,1);assert.match(reads[0].url,/\/v1\/capacity$/);assert.equal(reads[0].options.method,'GET');
  assert.ok(!r.text.includes('FAKE_TOKEN'));
  for (const origin of ['https://GitHub.com/example/project.git','https://github.com:443/example/project.git','git@github.com:example/project.git']) {
    f.origin=origin;assert.equal((await invoke(f)).code,0,origin);
  }
});

test('doctor: stale PATH and missing sign-in accumulate; start returns identical report before effects',async()=>{
  const f=doctorFixture();f.signedIn=false;
  f.ports.files.realpathSync=path=>path;
  const doctor=await invoke(f),start=await invoke(f,'start');
  assert.equal(doctor.code,1);assert.equal(start.code,1);assert.equal(start.text,doctor.text);
  check(doctor,'path','FAIL');check(doctor,'agent','FAIL');
  assert.match(doctor.text,/\/node.*\/install\/bin\/pdd.mjs.*autopilot doctor/);assert.match(doctor.text,/codex.*login/);
});

test('doctor: required failures refuse start; warnings permit readiness',async()=>{
  for(const fault of ['node','permission','merge','usage','setup','interpreter','timers','budget']) {
    const f=doctorFixture();
    if(fault==='node')f.ports.nodeVersion='22.19.9';
    if(fault==='permission')f.permission='READ';
    if(fault==='merge')f.merge=false;
    if(fault==='usage')f.limited=true;
    if(fault==='setup')f.paths.delete('/project/AGENTS.md');
    if(fault==='interpreter')f.ports.fetch=async()=>new Response('{}',{status:403});
    if(fault==='timers'){const run=f.ports.run;f.ports.run=(file,args,o)=>file==='systemctl'?f.answer('',1):run(file,args,o);}
    if(fault==='budget')f.input.env.PDD_HERDR_PANE_BUDGET='1',f.panes=[{}];
    const r=await invoke(f,'start');assert.equal(r.code,1,`${fault}: ${r.text}`);
  }
  const f=doctorFixture();f.tracked='one.prompt.md\0';f.paths.set('/project/one.prompt.md','# Draft');f.ports.codexLimits=async()=>({state:'unknown'});
  const r=await invoke(f);assert.equal(r.code,0,r.text);check(r,'draft-prompts','WARN');check(r,'agent-usage','WARN');
});

test('doctor: Claude on macOS probes auth and launchctl without generation',async()=>{
  const f=doctorFixture({kind:'claude',platform:'darwin'}),r=await invoke(f);
  assert.equal(r.code,0,r.text);check(r,'agent','PASS');check(r,'agent-usage','WARN');check(r,'sleep','PASS');
  assert.ok(f.calls.some(c=>c.file==='claude'&&c.args.join(' ')==='auth status --json'));
  assert.ok(f.calls.some(c=>c.file==='launchctl'&&c.args.join(' ')==='print gui/501'));
  assert.ok(!f.calls.some(c=>['systemctl','loginctl'].includes(c.file)));
});

test('doctor: stopped Herdr needs no pane allocation; missing CLI and unreadable rules stay visible',async()=>{
  const f=doctorFixture();f.server=false;
  const run=f.ports.run;f.ports.run=(file,args,o)=>file==='gh'&&args[0]==='api'?f.answer('',1):run(file,args,o);
  const r=await invoke(f);assert.equal(r.code,0,r.text);check(r,'herdr-room','PASS');check(r,'merge-rules','WARN');
  assert.ok(!f.calls.some(c=>c.file==='herdr'&&c.args.includes('pane')));
  const report=await runAutopilotDoctor(f.input,f.ports);assert.match(report.checks.find(c=>c.id==='merge-rules').fix,/gh auth login/);
});

test('doctor: network failure never prints secrets and CLI rejects doctor operands',async()=>{
  const f=doctorFixture();f.ports.fetch=async()=>{throw Error('FAKE_TOKEN');};
  const r=await invoke(f);assert.equal(r.code,1);check(r,'interpreter','FAIL');assert.ok(!r.text.includes('FAKE_TOKEN'));
  const result=await runAutopilotLauncher({...f.input,command:'doctor'},{doctorPorts:f.ports,run:async()=>f.answer('',1)});
  const invalid=await runPdd(['autopilot','doctor','extra'],{...f.input,stdout:{write:()=>{}},stderr:{write:()=>{}},autopilotLauncherPorts:{run:()=>assert.fail('invalid input must not probe')}});
  assert.equal(invalid,2);
  assert.equal(result.exitCode,1);assert.ok(Array.isArray(result.checks),'doctor must expose diagnostic checks');assert.equal(result.checks.find(c=>c.id==='interpreter').status,'fail');
});


test('start: missing sign-in refuses before creating the local state folder',async t=>{
  const folder=mkdtempSync(join(tmpdir(),'pdd-doctor-start-'));
  t.after(()=>rmSync(folder,{recursive:true,force:true}));
  const f=doctorFixture({cwd:folder,home:join(folder,'home')});f.signedIn=false;
  const stateRoot=join(folder,'state');
  const r=await runAutopilotLauncher({...f.input,command:'start'},{doctorPorts:f.ports,stateRoot,run:async()=>f.answer(folder)});
  assert.equal(existsSync(stateRoot),false,'failed preflight must not create local state');
  assert.equal(r.exitCode,1);
  assert.match(r.message,/(?:^|\n)FAIL agent:/);
});

for (const overrides of [{CLAUDE_CONFIG_DIR:'/profiles/claude custom'}, {HOME:'/profiles/custom home'}, {HOME:'/profiles/custom home',CLAUDE_CONFIG_DIR:'/profiles/claude custom'}]) test(`doctor: custom Claude profile ${Object.keys(overrides).join('+')} owns all checks`,async()=>{
  const f=doctorFixture({kind:'claude'});
  for (const path of [...f.paths.keys()]) if(path.includes('/skills/')) {
    const content=f.paths.get(path);f.paths.delete(path);
    const root=overrides.CLAUDE_CONFIG_DIR??join(overrides.HOME,'.claude');
    f.paths.set(path.replace('/home/fake/.claude',root),content);
  }
  f.ports.agentDefinitions=()=>[{id:'custom',kind:'claude',command:'claude',env:overrides}];
  const result=await invoke(f);
  assert.equal(result.code,0,result.text);check(result,'setup-skills','PASS');check(result,'agent','PASS');
  for(const call of f.calls.slice(1).filter(c=>c.options?.env)) for(const [name,value] of Object.entries(overrides)) assert.equal(call.options.env[name],value,`${call.file}: ${name}`);
});

test('doctor: repair commands run with selected HOME, PATH and provider directories without exposing secret overrides',async t=>{
  const folder=mkdtempSync(join(tmpdir(),'pdd-doctor-command-'));t.after(()=>rmSync(folder,{recursive:true,force:true}));
  const home=join(folder,"profile ' one"),config=join(folder,'Claude config');
  writeFileSync(join(folder,'claude'),'#!/bin/sh\nprintf "%s\\n" "$HOME" "$CLAUDE_CONFIG_DIR" "${CODEX_HOME-unset}" "$PATH" "$CUSTOM_SETTING"\n',{mode:0o700});
  const f=doctorFixture({kind:'claude'});
  f.input.env.CODEX_HOME='/caller/codex';
  f.ports.agentDefinitions=()=>[{id:'custom',kind:'claude',command:'claude',env:{HOME:home,CLAUDE_CONFIG_DIR:config,CODEX_HOME:'/selected/codex',PATH:folder,CUSTOM_SETTING:'custom value',API_TOKEN:'SECRET_VALUE'}}];
  const r=await runAutopilotDoctor(f.input,f.ports),fix=r.checks.find(c=>c.id==='agent').fix;
  assert.ok(!r.message.includes('SECRET_VALUE'));
  const output=execFileSync('/bin/sh',['-c',fix],{env:{HOME:'/caller',CODEX_HOME:'/caller/codex',CLAUDE_CONFIG_DIR:'/caller/claude',PATH:folder+':/usr/bin:/bin',API_TOKEN:'selected-secret'},encoding:'utf8'});
  assert.deepEqual(output.trim().split('\n'),[home,config,'/selected/codex',folder,'custom value']);
});

test('doctor: malformed agents.json identifies its file and a repair without configuration content',async t=>{
  const folder=mkdtempSync(join(tmpdir(),'pdd-doctor-config-'));t.after(()=>rmSync(folder,{recursive:true,force:true}));
  const f=doctorFixture({home:folder}),path=join(folder,'.config','pdd','agents.json');
  mkdirSync(join(folder,'.config','pdd'),{recursive:true});writeFileSync(path,'{"SECRET_VALUE":');
  delete f.ports.agentDefinitions;
  const result=await runAutopilotDoctor(f.input,f.ports),line=result.checks.find(c=>c.id==='agent-config');
  assert.equal(result.exitCode,1);assert.equal(line?.status,'fail');assert.ok(line.detail.includes(path));assert.match(line.fix,/vi /);assert.ok(!result.message.includes('SECRET_VALUE'));
});

test('doctor: invalid runtime address and unavailable user session give repair commands',async()=>{
  const f=doctorFixture();f.input.env.PDD_RUNTIME_URL='http://invalid/path?SECRET_VALUE';
  f.ports.agentDefinitions=()=>[{id:'codex',kind:'codex',command:'codex',env:{PDD_RUNTIME_URL:'https://user:SECRET_VALUE@example.invalid/?token=SECRET_VALUE'}}];
  f.ports.runtimeHealth=()=>assert.fail('invalid origin must not reach health port');
  const run=f.ports.run;f.ports.run=(file,args,o)=>file==='systemctl'?f.answer('',1):run(file,args,o);
  const result=await runAutopilotDoctor(f.input,f.ports),runtime=result.checks.find(c=>c.id==='interpreter'),timers=result.checks.find(c=>c.id==='user-timers');
  assert.equal(result.exitCode,1);assert.equal(runtime.status,'fail');assert.match(runtime.detail,/PDD_RUNTIME_URL/);assert.match(runtime.fix,/unset PDD_RUNTIME_URL/);assert.match(timers.fix,/systemctl start/);assert.ok(!result.message.includes('SECRET_VALUE'));
});


test('doctor: saved profile overrides changed definition directories for sign-in, usage and all checks',async()=>{
  const f=doctorFixture();
  f.input.profile={agent:{id:'codex',kind:'codex'},home:'/home/fake',definitionHome:'/definitions',configHome:'/saved/codex'};
  f.input.env.CODEX_HOME='/signed-out-caller';
  f.ports.agentDefinitions=({env})=>{assert.equal(env.HOME,'/definitions');return [{id:'codex',kind:'codex',command:'codex',env:{HOME:'/changed-home',CODEX_HOME:'/changed-profile',CLAUDE_CONFIG_DIR:'/unrelated/claude'}}];};
  f.ports.codexLimits=async({env})=>{assert.equal(env.HOME,'/home/fake');assert.equal(env.CODEX_HOME,'/saved/codex');assert.ok(!Object.hasOwn(env,'CLAUDE_CONFIG_DIR'));return {state:'healthy'};};
  const result=await runAutopilotDoctor(f.input,f.ports);
  assert.equal(result.exitCode,0,result.message);
  for(const call of f.calls.filter(c=>c.options?.env)) {assert.equal(call.options.env.HOME,'/home/fake');assert.equal(call.options.env.CODEX_HOME,'/saved/codex');}
});

for (const reuse of [true,false]) test(`doctor: full pane budget ${reuse?'reuses the coordinator':'defers potential reclamation to guarded admission'}`,async()=>{
  const f=doctorFixture();f.input.env.PDD_HERDR_PANE_BUDGET='1';f.panes=[{pane_id:'personal',workspace_id:'workspace',tab_id:'tab',terminal_id:'terminal'}];
  if(reuse){f.input.coordinatorPaneId='saved';f.coordinatorPanes=[{pane_id:'saved'}];f.ports.coordinatorHealth=async()=>({state:'idle'});}
  else f.ports.reclaimablePanes=async({env,panes})=>{assert.equal(env.HOME,f.input.env.HOME);assert.deepEqual(panes,f.panes);return 1;};
  const result=await runAutopilotDoctor(f.input,f.ports),capacity=result.checks.find(c=>c.id==='herdr-room');
  assert.equal(result.exitCode,0,result.message);assert.equal(capacity.status,reuse?'pass':'warn');
  assert.ok(f.calls.every(c=>!c.args || !c.args.includes('close')));
  if(reuse)assert.ok(!f.calls.some(c=>c.file==='herdr'&&c.args[1]==='pdd'));
});

const healthCases=[
  {name:'JSON 200',status:200,body:'{}',state:'healthy'},
  {name:'optional endpoint JSON 404',status:404,body:'{"error":{"code":"not-found"}}',state:'healthy'},
  {name:'HTML 404',status:404,body:'<html>missing</html>',state:'access'},
  {name:'malformed JSON 200',status:200,body:'{',state:'access'},
  {name:'array 200',status:200,body:'[]',state:'access'},
  {name:'auth denied',status:401,body:'{}',state:'access'},
  {name:'access denied',status:403,body:'{}',state:'access'},
  {name:'redirect',status:302,body:'{}',state:'access'},
  {name:'service down',status:503,body:'{}',state:'unavailable'},
  {name:'maintenance',status:200,body:'{"maintenance":{"until":"2099-01-01T00:00:00Z"}}',state:'unavailable'},
  {name:'network failure',state:'unavailable'},
];
for(const row of healthCases)test(`doctor: runtime admission uses native health for ${row.name}`,async()=>{
  const f=doctorFixture();f.input.env.PDD_RUNTIME_URL='https://runtime.example.test';
  f.ports.fetch=async()=>{if(!row.status)throw Error('network');return new Response(row.body,{status:row.status});};
  const native=await checkRuntimeHealth({env:f.input.env},{gh:()=>({status:0,stdout:'synthetic-token'}),fetch:f.ports.fetch});
  assert.equal(native.state,row.state);
  const result=await runAutopilotDoctor(f.input,f.ports);
  assert.equal(result.checks.find(c=>c.id==='interpreter').status,row.state==='healthy'?'pass':'fail');
  assert.equal(result.exitCode,row.state==='healthy'?0:1,result.message);
});

test('doctor: successful repository checks print read-only inspection commands',async()=>{
  const f=doctorFixture(),result=await runAutopilotDoctor(f.input,f.ports);
  for(const id of ['github-permission','merge-method']) {
    const line=result.checks.find(c=>c.id===id);
    assert.equal(line.status,'pass');assert.match(line.fix,/gh repo view /);
    assert.doesNotMatch(line.fix,/gh repo (?:fork|edit) /);
  }
});
