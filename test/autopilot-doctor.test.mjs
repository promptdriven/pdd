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
import {checkRuntimeHealth, runtimePreflightSlice} from '../src/runtime-seam.mjs';

const {proseSha256} = runtimePreflightSlice();

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

test('doctor: advisory findings warn; warnings permit readiness; critical prerequisites fail with exit 1',async()=>{
  for(const fault of ['permission','merge','setup','timers','identity','settings']) {
    const f=doctorFixture();
    if(fault==='permission')f.permission='READ';
    if(fault==='merge')f.merge=false;
    if(fault==='setup')f.paths.delete('/project/AGENTS.md');
    if(fault==='timers'){const run=f.ports.run;f.ports.run=(file,args,o)=>file==='systemctl'?f.answer('',1):run(file,args,o);}
    if(fault==='identity')f.identity={};
    if(fault==='settings')f.remote=null;
    const r=await invoke(f);assert.equal(r.code,0,`${fault}: ${r.text}`);
    check(r,{permission:'github-permission',merge:'merge-method',setup:'setup-block',timers:'user-timers',identity:'git-identity',settings:'settings-github'}[fault],'WARN');
    if(fault==='setup')assert.match(r.text,/WARN setup-block: .*; fix: pdd init(?:\n|$)/);
  }
  const offMode=doctorFixture();offMode.paths.set('/project/pdd.json',JSON.stringify({autopilot:{mode:'off'}}));
  const offReport=await runAutopilotDoctor(offMode.input,offMode.ports);
  const modeRow=offReport.checks.find(c=>c.id==='setup-mode');
  assert.equal(modeRow.status,'warn');
  assert.match(modeRow.detail,/pdd autopilot observe or pdd autopilot auto/);
  assert.equal(modeRow.fix,'pdd autopilot observe');
  for(const critical of ['node','git','github-cli','platform']) {
    const f=doctorFixture();
    if(critical==='node')f.ports.nodeVersion='22.19.9';
    if(critical==='git'){const run=f.ports.run;f.ports.run=(file,args,o)=>file==='git'&&args[0]==='--version'?f.answer('',1):run(file,args,o);}
    if(critical==='github-cli'){const run=f.ports.run;f.ports.run=(file,args,o)=>file==='gh'&&args[0]==='--version'?f.answer('',1):run(file,args,o);}
    if(critical==='platform')f.ports.platform='win32';
    const r=await invoke(f);
    assert.equal(r.code,1,`critical ${critical} must exit 1: ${r.text}`);
    check(r,critical,'FAIL');
  }
  // Plain-Markdown and valid frontmatter kind: native-only prompts are ready as is (even with leftover strict_approvals).
  const plainText='# Plain prompt\n\nReturn ok.\n';
  const plain=doctorFixture();plain.tracked='one.prompt.md\0';plain.paths.set('/project/one.prompt.md',plainText);
  const prPlain=await invoke(plain);assert.equal(prPlain.code,0,prPlain.text);check(prPlain,'draft-prompts','PASS');
  plain.paths.set('/project/pdd.json',JSON.stringify({autopilot:{mode:'auto',trust:[]},strict_approvals:true}));
  const prStrict=await invoke(plain);assert.equal(prStrict.code,0,prStrict.text);check(prStrict,'draft-prompts','PASS');
  assert.doesNotMatch(prStrict.text,/strict person-terminal|pdd approve/);
  const nativeText='---\nkind: native-only\nreason: direct host clock binding\n---\n# Clock\n\nRead clock.\n';
  const nat=doctorFixture();nat.tracked='clock.prompt.md\0';nat.paths.set('/project/clock.prompt.md',nativeText);
  check(await invoke(nat),'draft-prompts','PASS');
  // Malformed native-only frontmatter (missing reason) warns with pdd files --json fix.
  const badFmText='---\nkind: native-only\n---\n# Bad native\n';
  const badFm=doctorFixture();badFm.tracked='bad.prompt.md\0';badFm.paths.set('/project/bad.prompt.md',badFmText);
  const badFmRes=await invoke(badFm);check(badFmRes,'draft-prompts','WARN');assert.match(badFmRes.text,/fix: pdd files --json/);
  // Conflicting frontmatter + embedded block and duplicate embedded blocks warn.
  const conflict=doctorFixture();conflict.tracked='c.prompt.md\0';conflict.paths.set('/project/c.prompt.md','---\nkind: native-only\nreason: x\n---\n# Both\n\n<details><summary>Runtime interface</summary>\n\n```json\n{"status":"approved"}\n```\n</details>\n');
  check(await invoke(conflict),'draft-prompts','WARN');
  const dupBlock=doctorFixture();dupBlock.tracked='d.prompt.md\0';dupBlock.paths.set('/project/d.prompt.md','# Two\n\n<details><summary>Runtime interface</summary>\n\n```json\n{"status":"approved"}\n```\n</details>\n\n<details><summary>Runtime interface</summary>\n\n```json\n{"status":"approved"}\n```\n</details>\n');
  check(await invoke(dupBlock),'draft-prompts','WARN');
  // Legacy embedded block: approved with current prose_sha256 passes; missing/stale prose_sha256 or invalid JSON warns.
  const legBase='# Legacy\n\nDo work.\n\n<details><summary>Runtime interface</summary>\n\n```json\n{"status":"approved","prose_sha256":"PLACEHOLDER"}\n```\n</details>\n';
  const legOk=legBase.replace('PLACEHOLDER',proseSha256(legBase));
  const leg=doctorFixture();leg.tracked='leg.prompt.md\0';leg.paths.set('/project/leg.prompt.md',legOk);
  check(await invoke(leg),'draft-prompts','PASS');
  leg.paths.set('/project/leg.prompt.md',legBase.replace('PLACEHOLDER','0'.repeat(64)));
  check(await invoke(leg),'draft-prompts','WARN');
  leg.paths.set('/project/leg.prompt.md','# Legacy\n\n<details><summary>Runtime interface</summary>\n\n```json\n{"status":"approved"}\n```\n</details>\n');
  check(await invoke(leg),'draft-prompts','WARN');
  leg.paths.set('/project/leg.prompt.md','# Legacy\n\n<details><summary>Runtime interface</summary>\n\n```json\n{bad json\n```\n</details>\n');
  check(await invoke(leg),'draft-prompts','WARN');
  // Symlinked tracked prompt is rejected as unreadable.
  const sym=doctorFixture();sym.tracked='sym.prompt.md\0';sym.paths.set('/project/sym.prompt.md',plainText);
  sym.ports.files.lstatSync=p=>p==='/project/sym.prompt.md'?{isSymbolicLink:()=>true,isFile:()=>false}:{isSymbolicLink:()=>false,isFile:()=>true};
  const symRes=await invoke(sym);check(symRes,'draft-prompts','WARN');assert.match(symRes.text,/unreadable: sym\.prompt\.md/);
  // Legacy embedded draft block still warns with pdd files --json fix (never pdd approve).
  const f=doctorFixture();f.tracked='one.prompt.md\0';f.paths.set('/project/one.prompt.md','# Draft\n\n<details><summary>Runtime interface</summary>\n\n```json\n{"status":"draft"}\n```\n</details>\n');f.ports.codexLimits=async()=>({state:'unknown'});
  const r=await invoke(f);assert.equal(r.code,0,r.text);check(r,'draft-prompts','WARN');check(r,'agent-usage','WARN');
  assert.doesNotMatch(r.text,/pdd approve/);
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
  assert.equal(result.exitCode,1);assert.equal(line?.status,'fail');assert.ok(line.detail.includes(path));assert.match(line.fix,/vi /);assert.ok(!result.message.includes('SECRET_VALUE'));
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
  assert.deepEqual(await settingsRow(f),{id:'settings-github',status:'warn',detail:'pdd.json is missing in this checkout and on GitHub (main)',fix:'pdd autopilot observe'});
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

// Wrong (#3242): doctor warns on a machine that has the shipped pdd skill but not the retired coordinator skills, or passes
// a machine that lacks the shipped pdd skill.
test('doctor: the skill bundle is the single shipped pdd skill; retired skills are not required',async()=>{
  const f=doctorFixture();
  assert.equal([...f.paths.keys()].some(path=>/pdd-(?:autopilot|check|merge)\//.test(path)),false);
  check(await invoke(f),'setup-skills','PASS');
  f.paths.delete(join('/home/fake','.agents','skills','pdd','SKILL.md'));
  check(await invoke(f),'setup-skills','WARN');
});

test('#3252 doctor: saved agy profile binds ANTIGRAVITY_APP_DATA_DIR, non-agy profiles strip it, and Gemini matches login-pool auth modes',async()=>{
  // 1. Saved agy profile preserves ANTIGRAVITY_APP_DATA_DIR and strips CODEX_HOME.
  const f=doctorFixture();
  f.input.env.CODEX_HOME='/caller/codex';
  f.input.env.ANTIGRAVITY_APP_DATA_DIR='/caller/agy';
  f.input.profile={agent:{id:'agy-work',kind:'agy'},home:'/home/fake',definitionHome:'/home/fake',configHome:'/saved/agy'};
  const origRun=f.ports.run;
  f.ports.run=(file,args,opts)=>{
    if (file==='agy'&&args[0]==='models') { f.calls.push({file,args,options:opts}); return f.answer('gemini-2.5-pro\n'); }
    return origRun(file,args,opts);
  };
  const agyRes=await runAutopilotDoctor(f.input,f.ports);
  assert.equal(agyRes.exitCode,0,agyRes.message);
  assert.equal(agyRes.checks.find(c=>c.id==='agent').detail,'agy signed in');
  const agyCall=f.calls.find(c=>c.file==='agy');
  assert.equal(agyCall.options.env.ANTIGRAVITY_APP_DATA_DIR,'/saved/agy');
  assert.equal(Object.hasOwn(agyCall.options.env,'CODEX_HOME'),false);
  assert.match(agyRes.checks.find(c=>c.id==='node').fix,/-u CODEX_HOME.*ANTIGRAVITY_APP_DATA_DIR='\/saved\/agy'/);

  // 2. Switching to saved codex profile strips caller ANTIGRAVITY_APP_DATA_DIR.
  const c=doctorFixture();
  c.input.env.ANTIGRAVITY_APP_DATA_DIR='/caller/agy';
  c.input.profile={agent:{id:'codex',kind:'codex'},home:'/home/fake',definitionHome:'/home/fake',configHome:'/saved/codex'};
  const codexRes=await runAutopilotDoctor(c.input,c.ports);
  assert.equal(codexRes.exitCode,0,codexRes.message);
  assert.match(codexRes.checks.find(c=>c.id==='node').fix,/-u ANTIGRAVITY_APP_DATA_DIR/);

  // 3. Gemini sign-in accepts flat <GEMINI_CLI_HOME>/oauth_creds.json, GOOGLE_GENAI_USE_GCA=true, and GOOGLE_GENAI_USE_VERTEXAI=true, and rejects false without creds.
  for (const mode of ['flat-oauth','gca','vertex','gca-false']) {
    const g=doctorFixture();
    const geminiHome='/profiles/gemini';
    if (mode==='flat-oauth') g.paths.set(join(geminiHome,'oauth_creds.json'),JSON.stringify({refresh_token:'GEM_REFRESH_SECRET'}));
    const extraEnv=mode==='gca'?{GOOGLE_GENAI_USE_GCA:'true'}:mode==='vertex'?{GOOGLE_GENAI_USE_VERTEXAI:'true'}:mode==='gca-false'?{GOOGLE_GENAI_USE_GCA:'false'}:{};
    g.input.profile={agent:{id:'gemini-work',kind:'gemini'},home:'/home/fake',definitionHome:'/home/fake',configHome:geminiHome};
    g.ports.agentDefinitions=()=>[{id:'gemini-work',kind:'gemini',command:'gemini',env:extraEnv}];
    const gRun=g.ports.run;
    g.ports.run=(file,args,opts)=>file==='gemini'&&args[0]==='--version'?g.answer('0.5.0\n'):gRun(file,args,opts);
    const gRes=await runAutopilotDoctor(g.input,g.ports);
    assert.equal(gRes.exitCode,mode==='gca-false'?1:0,`${mode}: ${gRes.message}`);
    assert.ok(!gRes.message.includes('GEM_REFRESH_SECRET'));
  }
});

test('doctor: setup-skills hints pdd setup and warns advisories on unmarked retired skill folders only',async t=>{
  const f=doctorFixture();
  f.paths.delete(join('/home/fake','.agents','skills','pdd','SKILL.md'));
  const missingSkill=await runAutopilotDoctor(f.input,f.ports);
  assert.equal(missingSkill.checks.find(c=>c.id==='setup-skills').fix,'pdd setup');

  // Unmarked retired skill folders with pdd-skills: frontmatter warn with quoted mv backup and exitCode 0.
  const u=doctorFixture({home:"/home/o'neil user"});
  u.paths.set(join("/home/o'neil user",'.agents','skills','pdd-autopilot','SKILL.md'),'---\nname: pdd-autopilot\nmetadata:\n  pdd-skills: 0.1.28\n---\n');
  u.paths.set(join("/home/o'neil user",'.claude','skills','pdd-merge','SKILL.md'),'---\nname: pdd-merge\npdd-skills: 0.1.25\n---\n');
  // Marked copy (.pdd-skill.json) and unrelated user skill (no pdd-skills: frontmatter) are ignored.
  u.paths.set(join("/home/o'neil user",'.agents','skills','pdd-check','SKILL.md'),'---\nname: pdd-check\npdd-skills: 0.1.28\n---\n');
  u.paths.set(join("/home/o'neil user",'.agents','skills','pdd-check','.pdd-skill.json'),'{"name":"pdd-check"}');
  u.paths.set(join("/home/o'neil user",'.claude','skills','pdd-autopilot','SKILL.md'),'---\nname: pdd-autopilot\ndescription: custom user skill\n---\n');
  const warned=await runAutopilotDoctor(u.input,u.ports);
  assert.equal(warned.exitCode,0,warned.message);
  const row=warned.checks.find(c=>c.id==='retired-skills');
  assert.ok(row,'expected retired-skills warning');
  assert.equal(row.status,'warn');
  assert.match(row.detail,/pdd-autopilot/);
  assert.match(row.detail,/pdd-merge/);
  assert.doesNotMatch(row.detail,/pdd-check/);
  assert.ok(row.fix.includes("mkdir -p '/home/o'\\''neil user/.agents/skills/.pdd-retired' && mv '/home/o'\\''neil user/.agents/skills/pdd-autopilot' '/home/o'\\''neil user/.agents/skills/.pdd-retired/'"), row.fix);

  // Symlinked retired skill directory on real filesystem is ignored (not flagged).
  const { mkdtempSync, mkdirSync, writeFileSync: wf, symlinkSync, rmSync, lstatSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const tmp=mkdtempSync(join(tmpdir(),'pdd-doc-retired-'));
  t.after(()=>rmSync(tmp,{recursive:true,force:true}));
  const target=join(tmp,'target-skill'), agentsSkills=join(tmp,'home','.agents','skills');
  mkdirSync(target,{recursive:true});
  mkdirSync(agentsSkills,{recursive:true});
  wf(join(target,'SKILL.md'),'---\nname: pdd-autopilot\npdd-skills: 0.1.28\n---\n');
  symlinkSync(target,join(agentsSkills,'pdd-autopilot'));
  const s=doctorFixture({home:join(tmp,'home')});
  s.paths.set(join(agentsSkills,'pdd-autopilot','SKILL.md'),'---\nname: pdd-autopilot\npdd-skills: 0.1.28\n---\n');
  s.ports.files.lstatSync=path=>lstatSync(path);
  const symRes=await runAutopilotDoctor(s.input,s.ports);
  assert.equal(symRes.checks.find(c=>c.id==='retired-skills'),undefined);
});

test('doctor: warns when Linux AppArmor restricts unprivileged userns and bwrap is missing for Codex, and stays quiet when bwrap is on PATH',async()=>{
  const missing=doctorFixture({kind:'codex',platform:'linux'});
  missing.paths.set('/proc/sys/kernel/apparmor_restrict_unprivileged_userns','1\n');
  const resMissing=await runAutopilotDoctor(missing.input,missing.ports);
  assert.equal(resMissing.exitCode,0,resMissing.message);
  const warnRow=resMissing.checks.find(c=>c.id==='codex-sandbox');
  assert.ok(warnRow,'expected codex-sandbox warning');
  assert.equal(warnRow.status,'warn');
  assert.equal(warnRow.fix,'sudo apt-get install -y bubblewrap');

  const present=doctorFixture({kind:'codex',platform:'linux'});
  present.paths.set('/proc/sys/kernel/apparmor_restrict_unprivileged_userns','1\n');
  present.ports.files.accessSync=path=>{if(path!=='/tools/pdd'&&path!=='/tools/bwrap')throw Error('missing');};
  const resPresent=await runAutopilotDoctor(present.input,present.ports);
  assert.equal(resPresent.checks.find(c=>c.id==='codex-sandbox'),undefined);
});

test('doctor: private-repo HTTP 403 plan-gated branch rulesets and HTTP 404 branch not protected pass without gh auth login advice',async()=>{
  const planGated=doctorFixture({permission:'ADMIN'});
  planGated.permission='ADMIN';
  const baseRun=planGated.ports.run;
  planGated.ports.run=(file,args,o)=>{
    if(file==='gh'&&args[0]==='api'&&args[1]==='repos/example/project/rules/branches/main'){
      return Promise.resolve({
        code:1,
        stdout:'{"message":"Upgrade to GitHub Pro or make this repository public to enable this feature.","documentation_url":"https://docs.github.com/rest/repos/rules#get-rules-for-a-branch","status":"403"}',
        stderr:'gh: Upgrade to GitHub Pro or make this repository public to enable this feature. (HTTP 403)',
      });
    }
    return baseRun(file,args,o);
  };
  const r403=await invoke(planGated);
  assert.equal(r403.code,0,r403.text);
  check(r403,'merge-rules','PASS');
  assert.doesNotMatch(r403.text,/WARN merge-rules:/);
  const rep403=await runAutopilotDoctor(planGated.input,planGated.ports);
  const row403=rep403.checks.find(c=>c.id==='merge-rules');
  assert.equal(row403.status,'pass');
  assert.match(row403.detail,/Branch rules: none/);
  assert.doesNotMatch(row403.fix,/gh auth login/);

  const notProtected=doctorFixture();
  const baseRun404=notProtected.ports.run;
  notProtected.ports.run=(file,args,o)=>{
    if(file==='gh'&&args[0]==='api'&&args[1]==='repos/example/project/rules/branches/main'){
      return Promise.resolve({
        code:1,
        stdout:'{"message":"Branch not protected","status":"404"}',
        stderr:'gh: Branch not protected (HTTP 404)',
      });
    }
    return baseRun404(file,args,o);
  };
  const r404=await invoke(notProtected);
  assert.equal(r404.code,0,r404.text);
  check(r404,'merge-rules','PASS');
  const rep404=await runAutopilotDoctor(notProtected.input,notProtected.ports);
  assert.doesNotMatch(rep404.checks.find(c=>c.id==='merge-rules').fix,/gh auth login/);

  // Other HTTP 403 errors (for example rate limits or missing token scopes) remain visible warnings.
  const rateLimited=doctorFixture();
  const baseRunLimit=rateLimited.ports.run;
  rateLimited.ports.run=(file,args,o)=>{
    if(file==='gh'&&args[0]==='api'&&args[1]==='repos/example/project/rules/branches/main'){
      return Promise.resolve({
        code:1,
        stdout:'{"message":"API rate limit exceeded","status":"403"}',
        stderr:'gh: API rate limit exceeded (HTTP 403)',
      });
    }
    return baseRunLimit(file,args,o);
  };
  const rLimit=await invoke(rateLimited);
  assert.equal(rLimit.code,0,rLimit.text);
  check(rLimit,'merge-rules','WARN');
});


test('doctor: Cloud-only teammate without ~/.codex/auth.json passes codex login status via pddManagedCodexHome', async () => {
  const { accountsStatePath, managedCodexAuthPath, pddManagedCodexHome } = await import('../src/login-pool.mjs');
  const f = doctorFixture();
  const statePath = accountsStatePath(f.input.env);
  const managedAuth = managedCodexAuthPath(f.input.env);
  const managedHome = pddManagedCodexHome(f.input.env);
  f.paths.set(statePath, JSON.stringify({
    version: 1,
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc_cloud_only', label: 'team-cx', provider: 'codex', state: 'ready' } },
  }));
  f.paths.set(managedAuth, JSON.stringify({ auth_mode: 'chatgpt', tokens: { access_token: 'pddg_lse_1_tok', refresh_token: '' } }));
  f.ports.files.statSync = path => {
    if (f.paths.has(path)) return { isFile: () => true };
    throw Object.assign(new Error('ENOENT'), { code: 'ENOENT' });
  };
  const origRun = f.ports.run;
  f.ports.run = (file, args, opts) => {
    if (file === 'codex' && args[0] === 'login' && args[1] === 'status') {
      f.calls.push({ file, args, options: opts });
      return opts?.env?.CODEX_HOME === managedHome
        ? f.answer('Logged in using ChatGPT\n', 0)
        : f.answer('Not logged in\n', 1);
    }
    return origRun(file, args, opts);
  };

  const docRes = await invoke(f, 'doctor');
  assert.equal(docRes.code, 0, docRes.text);
  check(docRes, 'agent', 'PASS');
  const codexCall = f.calls.find(c => c.file === 'codex' && c.args[0] === 'login');
  assert.equal(codexCall?.options?.env?.CODEX_HOME, managedHome);

  // Without managed auth.json on disk, Cloud-only fallback does not bind a non-existent CODEX_HOME
  f.paths.delete(managedAuth);
  const missingRes = await invoke(f, 'doctor');
  assert.equal(missingRes.code, 1);
  check(missingRes, 'agent', 'FAIL');
});

test('#3426 doctor: Cloud-only --agent codex profile and isolated Cloud Claude settings pass doctor', async () => {
  const {
    accountsStatePath,
    managedClaudeSettingsPath,
    managedCodexAuthPath,
    pddManagedCodexHome,
  } = await import('../src/login-pool.mjs');

  // 1. `--agent codex` creates a profile with configHome: null; Cloud-only teammate must still bind pddManagedCodexHome.
  const fCx = doctorFixture();
  const cxState = accountsStatePath(fCx.input.env);
  const cxAuth = managedCodexAuthPath(fCx.input.env);
  const cxHome = pddManagedCodexHome(fCx.input.env);
  fCx.paths.set(cxState, JSON.stringify({
    version: 1,
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc_cx_borrow', label: 'team-cx', provider: 'codex', state: 'ready' } },
  }));
  fCx.paths.set(cxAuth, JSON.stringify({ auth_mode: 'chatgpt', tokens: { access_token: 'pddg_lse_2_tok', refresh_token: '' } }));
  fCx.ports.files.statSync = p => {
    if (fCx.paths.has(p)) return { isFile: () => true };
    throw Object.assign(new Error('ENOENT'), { code: 'ENOENT' });
  };
  const origCxRun = fCx.ports.run;
  fCx.ports.run = (file, args, opts) => {
    if (file === 'codex' && args[0] === 'login' && args[1] === 'status') {
      fCx.calls.push({ file, args, options: opts });
      return opts?.env?.CODEX_HOME === cxHome
        ? fCx.answer('Logged in using ChatGPT\n', 0)
        : fCx.answer('Not logged in\n', 1);
    }
    return origCxRun(file, args, opts);
  };
  const cxProfileReport = await runAutopilotDoctor({
    ...fCx.input,
    profile: {
      agent: { id: 'codex', kind: 'codex' },
      home: fCx.input.env.HOME,
      definitionHome: fCx.input.env.HOME,
      configHome: null,
    },
  }, fCx.ports);
  assert.equal(cxProfileReport.exitCode, 0, cxProfileReport.message);
  assert.equal(cxProfileReport.checks.find(c => c.id === 'agent')?.status, 'pass');
  assert.equal(fCx.calls.find(c => c.file === 'codex' && c.args[0] === 'login')?.options?.env?.CODEX_HOME, cxHome);

  // 2. Isolated Cloud Claude settings ($PDD_STATE_DIR/claude-home/settings.json) pass doctor via --settings without ~/.claude/settings.json.
  const fCl = doctorFixture();
  const clState = accountsStatePath(fCl.input.env);
  const clSettings = managedClaudeSettingsPath(fCl.input.env);
  fCl.paths.set(clState, JSON.stringify({
    version: 1,
    enrolled: true,
    providers: ['claude'],
    active: { claude: { account_id: 'acc_cl_borrow', label: 'team-cl', provider: 'claude', state: 'ready' } },
  }));
  fCl.paths.set(clSettings, JSON.stringify({ env: { CLAUDE_CODE_OAUTH_TOKEN: 'pddg_cl_tok' } }));
  fCl.ports.files.statSync = p => {
    if (fCl.paths.has(p)) return { isFile: () => true };
    throw Object.assign(new Error('ENOENT'), { code: 'ENOENT' });
  };
  fCl.ports.agentDefinitions = async () => [{ id: 'claude', kind: 'claude', command: 'claude', env: {} }];
  const origClRun = fCl.ports.run;
  fCl.ports.run = (file, args, opts) => {
    if (file === 'claude') {
      fCl.calls.push({ file, args, options: opts });
      if (args[0] === '--settings' && args[1] === clSettings && args[2] === 'auth') {
        return fCl.answer(JSON.stringify({ loggedIn: true }), 0);
      }
      return fCl.answer(JSON.stringify({ loggedIn: false }), 1);
    }
    return origClRun(file, args, opts);
  };
  const clReport = await runAutopilotDoctor(fCl.input, fCl.ports);
  assert.equal(clReport.exitCode, 0, clReport.message);
  assert.equal(clReport.checks.find(c => c.id === 'agent')?.status, 'pass');
  assert.match(clReport.checks.find(c => c.id === 'agent')?.fix ?? '', /--settings '.*settings\.json' auth status --json/);
  assert.deepEqual(
    fCl.calls.find(c => c.file === 'claude')?.args,
    ['--settings', clSettings, 'auth', 'status', '--json'],
  );

  // Symlinked managed Claude settings file or parent directory must be rejected.
  const { dirname } = await import('node:path');
  fCl.ports.files.lstatSync = p => {
    if (p === clSettings) return { isSymbolicLink: () => true, isFile: () => true, isDirectory: () => false };
    if (p === dirname(clSettings)) return { isSymbolicLink: () => false, isFile: () => false, isDirectory: () => true };
    throw Object.assign(new Error('ENOENT'), { code: 'ENOENT' });
  };
  const clSymlinkLeaf = await runAutopilotDoctor(fCl.input, fCl.ports);
  assert.equal(clSymlinkLeaf.exitCode, 1, 'symlinked managed settings.json must be rejected');

  fCl.ports.files.lstatSync = p => {
    if (p === dirname(clSettings)) return { isSymbolicLink: () => true, isFile: () => false, isDirectory: () => true };
    if (p === clSettings) return { isSymbolicLink: () => false, isFile: () => true, isDirectory: () => false };
    throw Object.assign(new Error('ENOENT'), { code: 'ENOENT' });
  };
  const clSymlinkDir = await runAutopilotDoctor(fCl.input, fCl.ports);
  assert.equal(clSymlinkDir.exitCode, 1, 'symlinked managed claude-home directory must be rejected');
  delete fCl.ports.files.lstatSync;

  // Failing Cloud-only Codex sign-in must NOT emit CODEX_HOME=<pddManagedCodexHome> in its login fix command.
  fCx.ports.run = (file, args, opts) => {
    if (file === 'codex' && args[0] === 'login' && args[1] === 'status') {
      return fCx.answer('Not logged in\n', 1);
    }
    return origCxRun(file, args, opts);
  };
  const cxFailReport = await runAutopilotDoctor(fCx.input, fCx.ports);
  assert.equal(cxFailReport.exitCode, 1);
  assert.doesNotMatch(cxFailReport.checks.find(c => c.id === 'agent')?.fix ?? '', /codex-home/);

  // Without managed Claude settings on disk, Cloud-only Claude fails cleanly.
  fCl.paths.delete(clSettings);
  const clMissing = await runAutopilotDoctor(fCl.input, fCl.ports);
  assert.equal(clMissing.exitCode, 1);
  assert.equal(clMissing.checks.find(c => c.id === 'agent')?.status, 'fail');
});
