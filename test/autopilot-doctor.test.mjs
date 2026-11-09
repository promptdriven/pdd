import './helpers/test-home.mjs';
import test from 'node:test';
import {mkdtempSync,rmSync,existsSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import assert from 'node:assert/strict';
import {runPdd} from '../src/pdd-cli.mjs';
import {runAutopilotLauncher} from '../src/autopilot-launcher.mjs';
import {doctorFixture} from './helpers/doctor-fixture.mjs';

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
