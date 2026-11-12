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
  const code=await runPdd(['autopilot',command,...(command==='start'?['--label','pdd:autopilot']:[])],{...f.input,stdout:{write:s=>stdout+=s},stderr:{write:s=>stderr+=s},autopilotLauncherPorts:{doctorPorts:f.ports,run:async()=>f.answer('',1),stateRoot:'/forbidden-state'},autopilotGithubPorts:{github:{repository:()=>assert.fail('No GitHub publication')}}});
  return {code,text:stdout+stderr};
};
const check=(result,id,status)=>assert.match(result.text,new RegExp(`(?:^|\\n)${status} ${id}:`));

test('doctor: all checks are read-only; a PASS line shows no fix and a WARN line shows its fix',async()=>{
  const f=doctorFixture(),r=await invoke(f);
  assert.equal(r.code,0,r.text);check(r,'path','PASS');check(r,'interpreter','PASS');check(r,'git-identity','PASS');check(r,'settings-github','PASS');
  const lines=r.text.trim().split('\n');
  assert.deepEqual(lines.map(line=>line.split(':')[0]),['PASS path','PASS node','PASS git','PASS repository','PASS github-cli','PASS github-auth','PASS github-permission','PASS merge-method','PASS merge-rules','PASS git-identity','PASS agent','PASS agent-usage','PASS setup-block','PASS setup-skills','PASS setup-mode','PASS settings-github','PASS draft-prompts','PASS interpreter','PASS user-timers','PASS linger']);
  for(const line of lines)assert.doesNotMatch(line,/; fix: /,line);
  const g=doctorFixture();g.permission='READ';g.signedIn=false;
  const report=await runAutopilotDoctor(g.input,g.ports);
  for(const row of report.checks)assert.ok(row.fix.length>0,`${row.id} keeps its fix in checks`);
  const failing=await invoke(g);
  assert.match(failing.text,/(?:^|\n)WARN github-permission: .*; fix: gh repo fork 'example\/project' --clone(?:\n|$)/);
  assert.match(failing.text,/(?:^|\n)FAIL agent: .*; fix: 'codex' login(?:\n|$)/);
  assert.ok(failing.text.split('\n').includes('PASS node: Node 22.20.0; requires 22.20.0 or newer'),failing.text);
  assert.ok(![...f.calls,...g.calls].some(c=>c.file==='herdr'),'doctor makes no Herdr call');
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
  check(doctor,'path','WARN');check(doctor,'agent','FAIL');
  assert.match(doctor.text,/\/node.*\/install\/bin\/pdd.mjs.*autopilot doctor/);assert.match(doctor.text,/codex.*login/);
});

test('doctor: non-agent findings warn; warnings permit readiness',async()=>{
  for(const fault of ['node','permission','merge','setup','timers','identity','settings']) {
    const f=doctorFixture();
    if(fault==='node')f.ports.nodeVersion='22.19.9';
    if(fault==='permission')f.permission='READ';
    if(fault==='merge')f.merge=false;
    if(fault==='setup')f.paths.delete('/project/AGENTS.md');
    if(fault==='timers'){const run=f.ports.run;f.ports.run=(file,args,o)=>file==='systemctl'?f.answer('',1):run(file,args,o);}
    if(fault==='identity')f.identity={};
    if(fault==='settings')f.remote=null;
    const r=await invoke(f);assert.equal(r.code,0,`${fault}: ${r.text}`);
    check(r,{node:'node',permission:'github-permission',merge:'merge-method',setup:'setup-block',timers:'user-timers',identity:'git-identity',settings:'settings-github'}[fault],'WARN');
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

test('doctor: unreadable rules and GitHub settings stay visible as warnings',async()=>{
  const f=doctorFixture();
  const run=f.ports.run;f.ports.run=(file,args,o)=>file==='gh'&&args[0]==='api'?f.answer('',1):run(file,args,o);
  const r=await invoke(f);assert.equal(r.code,0,r.text);check(r,'merge-rules','WARN');check(r,'settings-github','WARN');
  const report=await runAutopilotDoctor(f.input,f.ports);assert.match(report.checks.find(c=>c.id==='merge-rules').fix,/gh auth login/);
  const settings=report.checks.find(c=>c.id==='settings-github');
  assert.match(settings.detail,/unproved/);assert.equal(settings.fix,"gh auth login && gh api 'repos/example/project/contents/pdd.json?ref=main' -H 'Accept: application/vnd.github.raw'");
});

test('doctor: network failure never prints secrets and CLI rejects doctor operands',async()=>{
  const f=doctorFixture();f.ports.fetch=async()=>{throw Error('FAKE_TOKEN');};
  const r=await invoke(f);assert.equal(r.code,0);check(r,'interpreter','WARN');assert.ok(!r.text.includes('FAKE_TOKEN'));
  const result=await runAutopilotLauncher({...f.input,command:'doctor'},{doctorPorts:f.ports,run:async()=>f.answer('',1)});
  const invalid=await runPdd(['autopilot','doctor','extra'],{...f.input,stdout:{write:()=>{}},stderr:{write:()=>{}},autopilotLauncherPorts:{run:()=>assert.fail('invalid input must not probe')}});
  assert.equal(invalid,2);
  assert.equal(result.exitCode,0);assert.ok(Array.isArray(result.checks),'doctor must expose diagnostic checks');assert.equal(result.checks.find(c=>c.id==='interpreter').status,'warn');
});


test('start: missing sign-in refuses before creating the local state folder',async t=>{
  const folder=mkdtempSync(join(tmpdir(),'pdd-doctor-start-'));
  t.after(()=>rmSync(folder,{recursive:true,force:true}));
  const f=doctorFixture({cwd:folder,home:join(folder,'home')});f.signedIn=false;
  const stateRoot=join(folder,'state');
  const r=await runAutopilotLauncher({...f.input,command:'start',label:'pdd:autopilot'},{doctorPorts:f.ports,stateRoot,run:async()=>f.answer(folder)});
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
  assert.equal(result.exitCode,0);assert.equal(line?.status,'warn');assert.ok(line.detail.includes(path));assert.match(line.fix,/vi /);assert.ok(!result.message.includes('SECRET_VALUE'));
});

test('doctor: invalid runtime address and unavailable user session give repair commands',async()=>{
  const f=doctorFixture();f.input.env.PDD_RUNTIME_URL='http://invalid/path?SECRET_VALUE';
  f.ports.agentDefinitions=()=>[{id:'codex',kind:'codex',command:'codex',env:{PDD_RUNTIME_URL:'https://user:SECRET_VALUE@example.invalid/?token=SECRET_VALUE'}}];
  f.ports.runtimeHealth=()=>assert.fail('invalid origin must not reach health port');
  const run=f.ports.run;f.ports.run=(file,args,o)=>file==='systemctl'?f.answer('',1):run(file,args,o);
  const result=await runAutopilotDoctor(f.input,f.ports),runtime=result.checks.find(c=>c.id==='interpreter'),timers=result.checks.find(c=>c.id==='user-timers');
  assert.equal(result.exitCode,0);assert.equal(runtime.status,'warn');assert.equal(timers.status,'warn');assert.match(runtime.detail,/PDD_RUNTIME_URL/);assert.match(runtime.fix,/unset PDD_RUNTIME_URL/);assert.match(timers.fix,/systemctl start/);assert.ok(!result.message.includes('SECRET_VALUE'));
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

for (const engine of [undefined,'core','full']) test(`doctor: no Herdr check or call with engine ${engine??'unset'}, a saved coordinator pane and a full pane budget`,async()=>{
  const f=doctorFixture();f.input.env.PDD_HERDR_PANE_BUDGET='1';
  Object.assign(f.input,{engine,coordinatorPaneId:'saved'});
  f.ports.coordinatorHealth=()=>assert.fail('doctor must not read the coordinator');
  const result=await runAutopilotDoctor(f.input,f.ports);
  assert.equal(result.exitCode,0,result.message);
  assert.ok(!result.checks.some(c=>/herdr/.test(c.id)),result.message);assert.doesNotMatch(result.message,/herdr/i);
  assert.ok(!f.calls.some(c=>c.file==='herdr'));
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
  assert.equal(result.checks.find(c=>c.id==='interpreter').status,row.state==='healthy'?'pass':'warn');
  assert.equal(result.exitCode,0,result.message);
});

test('doctor: successful repository checks print read-only inspection commands',async()=>{
  const f=doctorFixture(),result=await runAutopilotDoctor(f.input,f.ports);
  for(const id of ['github-permission','merge-method']) {
    const line=result.checks.find(c=>c.id===id);
    assert.equal(line.status,'pass');assert.match(line.fix,/gh repo view /);
    assert.doesNotMatch(line.fix,/gh repo (?:fork|edit) /);
  }
});

for (const fault of ['agent limit','interpreter outage']) test(`doctor: recoverable capacity warns without refusal for ${fault}`,async()=>{
  const f=doctorFixture();
  const id=fault==='agent limit'?'agent-usage':'interpreter';
  if(fault==='agent limit')f.limited=true;
  if(fault==='interpreter outage')f.ports.fetch=async()=>new Response('{}',{status:503});
  const result=await invoke(f);
  assert.equal(result.code,0,result.text);check(result,id,'WARN');
  const line=(await runAutopilotDoctor(f.input,f.ports)).checks.find(c=>c.id===id);
  assert.ok(line.fix.length>0);
  assert.match(line.fix,/autopilot doctor/);
  assert.ok(f.calls.every(c=>!c.args||!c.args.some(arg=>['close','start','exec'].includes(arg))));
});

test('doctor: a fix is the plain command when the selected environment is the caller environment',async()=>{
  const f=doctorFixture();f.ports.agentDefinitions=()=>[{id:'codex',kind:'codex',command:'codex',env:{HOME:'/home/fake',PATH:'/tools'}}];
  const result=await runAutopilotDoctor(f.input,f.ports);
  for(const row of result.checks)assert.doesNotMatch(row.fix,/^env |\/bin\/sh -c/,row.id);
  assert.equal(result.checks.find(c=>c.id==='node').fix,'nvm install 22.20.0 && nvm use 22.20.0');
});

test('doctor: a fix binds only the names that differ from the caller environment',async()=>{
  const f=doctorFixture();f.input.env.CLAUDE_CONFIG_DIR='/caller/claude';f.input.env.API_TOKEN='caller-token';
  f.input.profile={agent:{id:'codex',kind:'codex'},home:'/home/fake',definitionHome:'/home/fake',configHome:'/saved/codex'};
  f.ports.agentDefinitions=()=>[{id:'codex',kind:'codex',command:'codex',env:{PATH:'/tools',API_TOKEN:'SECRET_VALUE'}}];
  const result=await runAutopilotDoctor(f.input,f.ports),fix=result.checks.find(c=>c.id==='node').fix;
  assert.equal(fix,`env -u CLAUDE_CONFIG_DIR CODEX_HOME='/saved/codex' API_TOKEN="\${API_TOKEN:?Set API_TOKEN for the selected profile}" /bin/sh -c 'nvm install 22.20.0 && nvm use 22.20.0'`);
  assert.ok(!result.message.includes('SECRET_VALUE'));
});

test('doctor: git identity warns for each missing value and accepts Git environment names',async()=>{
  const missing=doctorFixture();missing.identity={'user.email':'fake@example.com'};
  const row=(await runAutopilotDoctor(missing.input,missing.ports)).checks.find(c=>c.id==='git-identity');
  assert.deepEqual(row,{id:'git-identity',status:'warn',detail:'Git user.name and user.email are needed for Autopilot commits; missing: user.name',fix:'git config --global user.name "Your Name"'});
  assert.ok(missing.calls.some(c=>c.file==='git'&&c.args.join(' ')==='config user.name'&&c.options.cwd==='/project'));
  const none=doctorFixture();none.identity={};
  const both=await runAutopilotDoctor(none.input,none.ports);
  assert.equal(both.exitCode,0);
  assert.match(both.message,/(?:^|\n)WARN git-identity: Git user\.name and user\.email are needed for Autopilot commits; missing: user\.name, user\.email; fix: git config --global user\.name "Your Name" && git config --global user\.email "you@example\.com"(?:\n|$)/);
  const environment=doctorFixture();environment.identity={};
  Object.assign(environment.input.env,{GIT_AUTHOR_NAME:'Env User',GIT_COMMITTER_NAME:'Env User',GIT_AUTHOR_EMAIL:'env@example.com',GIT_COMMITTER_EMAIL:'env@example.com'});
  const present=(await runAutopilotDoctor(environment.input,environment.ports)).checks.find(c=>c.id==='git-identity');
  assert.equal(present.status,'pass');assert.equal(present.fix,'git config user.name && git config user.email');
  const author=doctorFixture();author.identity={'user.email':'fake@example.com'};author.input.env.GIT_AUTHOR_NAME='Env User';
  assert.equal((await runAutopilotDoctor(author.input,author.ports)).checks.find(c=>c.id==='git-identity').status,'warn','a commit also needs the committer name');
});

const settingsRow=async f=>(await runAutopilotDoctor(f.input,f.ports)).checks.find(c=>c.id==='settings-github');
test('doctor: GitHub settings warn when only this checkout has pdd.json',async()=>{
  const f=doctorFixture();f.remote=null;
  const row=await settingsRow(f);
  assert.deepEqual(row,{id:'settings-github',status:'warn',detail:'pdd.json is only in this checkout; GitHub (main) has none, so other machines and Autopilot job worktrees do not see it',fix:'git add pdd.json && git commit -m "Add PDD settings" && git push # or pdd autopilot auto'});
  assert.ok(f.calls.some(c=>c.file==='gh'&&c.args.join(' ')==='api repos/example/project/contents/pdd.json?ref=main'));
  assert.ok(f.calls.filter(c=>c.file==='gh').every(c=>!c.args.some(arg=>['POST','PUT','PATCH','DELETE','--method','--input'].includes(arg))),'doctor makes no GitHub write');
  f.paths.set('/project/pdd.json',JSON.stringify({autopilot:{mode:'off'}}));
  assert.equal((await settingsRow(f)).fix,'git add pdd.json && git commit -m "Add PDD settings" && git push');
  f.paths.delete('/project/pdd.json');
  assert.deepEqual(await settingsRow(f),{id:'settings-github',status:'warn',detail:'pdd.json is missing in this checkout and on GitHub (main)',fix:'pdd setup'});
});

test('doctor: GitHub settings warn when the mode or trust names differ, and pass when only case and order differ',async()=>{
  const f=doctorFixture();
  f.paths.set('/project/pdd.json',JSON.stringify({autopilot:{mode:'auto',trust:['Alice','bob']}}));
  f.remote=JSON.stringify({autopilot:{mode:'observe',trust:['alice','carol']},engine:'core'});
  assert.deepEqual(await settingsRow(f),{id:'settings-github',status:'warn',detail:'GitHub: observe, trust alice, carol; this checkout: auto, trust Alice, bob; Autopilot jobs use the GitHub copy',fix:'pdd autopilot auto && pdd autopilot trust bob && pdd autopilot untrust carol'});
  f.remote=JSON.stringify({autopilot:{mode:'off',trust:['bob','ALICE']}});
  assert.equal((await settingsRow(f)).fix,'pdd autopilot auto');
  f.remote=JSON.stringify({autopilot:{mode:'auto',trust:['BOB','alice']},testCommand:'npm test'});
  assert.deepEqual(await settingsRow(f),{id:'settings-github',status:'pass',detail:'GitHub (main) has the same Autopilot settings: auto, trust Alice, bob',fix:"gh api 'repos/example/project/contents/pdd.json?ref=main' -H 'Accept: application/vnd.github.raw'"});
});

test('doctor: GitHub settings are unproved for an unreadable GitHub file, and name the GitHub copy when this checkout has none',async()=>{
  const f=doctorFixture();f.remote='not json';
  const unreadable=await settingsRow(f);
  assert.equal(unreadable.status,'warn');assert.match(unreadable.detail,/unproved/);assert.match(unreadable.fix,/^gh auth login && gh api /);
  f.remote=JSON.stringify({autopilot:{mode:'observe',trust:[]}});f.paths.delete('/project/pdd.json');
  assert.deepEqual(await settingsRow(f),{id:'settings-github',status:'warn',detail:'pdd.json is only on GitHub (main): observe, trust (none); this checkout has none',fix:'git fetch origin && git checkout origin/main -- pdd.json'});
  f.paths.set('/project/pdd.json','[]');
  assert.deepEqual(await settingsRow(f),{id:'settings-github',status:'warn',detail:'pdd.json in this checkout is not a JSON object; the GitHub comparison is unproved',fix:'vi pdd.json'});
});

// Wrong (#3242): doctor warns on a machine that has the seven skills but not the retired coordinator skills, or passes
// a machine that lacks one of the seven.
test('doctor: the skill bundle is the seven shipped skills; the retired skills are not required',async()=>{
  const f=doctorFixture();
  assert.equal([...f.paths.keys()].some(path=>/pdd-(?:autopilot|check|merge)\//.test(path)),false);
  check(await invoke(f),'setup-skills','PASS');
  f.paths.delete(join('/home/fake','.agents','skills','pdd-graph','SKILL.md'));
  check(await invoke(f),'setup-skills','WARN');
});
