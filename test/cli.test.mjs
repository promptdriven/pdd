import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync, symlinkSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { execFileSync, spawnSync } from 'node:child_process';
import { EventEmitter } from 'node:events';
import { launchNativeSession } from '../src/native-session.mjs';
import { parseArgv, CommandInputError } from '../src/argument-parser.mjs';
import { PUBLIC_COMMAND_IDS, PUBLIC_COMMAND_MANIFEST } from '../src/command-catalog.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { listLocalWorkflows } from '../src/workflow-list.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const temp = t => { const p = mkdtempSync(join(tmpdir(), 'pdd-alpha-')); t.after(() => rmSync(p, { recursive: true, force: true })); return p; };
const capture = () => ({ text: '', write(value) { this.text += value; } });

// Wrong: deleting the adapter leaves private catalog/validator routes or unknown help succeeds.
test('ALPHA1: only local plans are admitted without Host disposition or forwarded arguments', () => {
  assert.deepEqual(PUBLIC_COMMAND_IDS, ['workflow.run', 'workflow.resume', 'workflow.attach', 'workflow.feature', 'workflow.bug', 'workflow.small-change', 'session', 'help', 'version', 'skill', 'completion', 'workflow.list']);
  for (const argv of [[], ['--help'], ['-h'], ['help'], ['--version'], ['--skill'], ['completion', 'bash'],
    ['completion', 'zsh'], ['session'], ['session','--agent','claude','Draft a prompt'], ['workflow','feature'], ['workflow','bug','--agent','claude'], ['workflow', 'list'], ['workflow', 'list', '--json'], ['workflow', '--help']]) {
    const input = [...argv], plan = parseArgv(input);
    assert.equal(plan.hostArgv, undefined); assert.equal(plan.host, undefined); assert.deepEqual(input, argv);
  }
  for (const argv of [['session','--agent','unknown'], ['session','--agent'], ['session','--agent','codex','--agent','claude'], ['run', 'start', 'issue'], ['verify'], ['try'], ['lint'], ['runtime', 'discover'],
    ['replay'], ['call'], ['tests'], ['doctor'], ['phone'], ['machine'], ['repo'], ['agents'], ['workbench'],
    ['unknown', '--help'], ['session', '--dangerously-skip-permissions'], ['workflow', 'new', 'feature'], ['workflow', 'list', '--brief'],
    ['workflow', 'list', '--json', '--json'], ['workflow', 'list', 'extra'], ['completion', 'fish'],
    ['completion'], ['--version', 'extra'], ['--skill', '--json'], ['help', 'runtime'], ['--help', 'extra'], ['\0']]) {
    assert.throws(() => parseArgv(argv), CommandInputError, JSON.stringify(argv));
  }
});

// Wrong: --skill prints only navigational links, reads the guide after the skill, or reports a missing guide as success.
test('ALPHA2: full canonical guide precedes skill and nested references; missing guide fails before output', async t => {
  const packageRoot = temp(t), stdout = capture(), stderr = capture();
  mkdirSync(join(packageRoot, 'docs')); mkdirSync(join(packageRoot, 'skills/pdd/references/nested'), { recursive: true });
  const guide = '# Prompting guide\nFull method\nFinal guide paragraph\n';
  writeFileSync(join(packageRoot, 'docs/prompting-guide.md'), guide);
  writeFileSync(join(packageRoot, 'skills/pdd/SKILL.md'), '# PDD skill\nBefore Story\n');
  writeFileSync(join(packageRoot, 'skills/pdd/references/review.md'), '# Review reference\n');
  writeFileSync(join(packageRoot, 'skills/pdd/references/nested/cases.md'), '# Independent cases\n');
  assert.equal(await runPdd(['--skill'], { packageRoot, stdout, stderr }), 0);
  assert.ok(stdout.text.includes(guide));
  assert.ok(stdout.text.indexOf(guide) < stdout.text.indexOf('# PDD skill'));
  assert.ok(stdout.text.includes('# Review reference')); assert.ok(stdout.text.includes('# Independent cases'));
  assert.ok(stdout.text.includes(packageRoot)); assert.equal(stderr.text, '');
  rmSync(join(packageRoot, 'docs/prompting-guide.md')); stdout.text = '';
  assert.equal(await runPdd(['--skill'], { packageRoot, stdout, stderr }), 1); assert.equal(stdout.text, '');
});

// Wrong: local recipe discovery follows outside symlinks, installs defaults or executes an agent.
test('ALPHA3: project listing is sorted, empty when absent and never traverses symlinks', t => {
  const cwd = temp(t), outside = temp(t);
  assert.deepEqual(listLocalWorkflows({ cwd }), { workflows: [], default: null });
  for (const name of ['small-change', 'bug']) {
    mkdirSync(join(cwd, '.pdd/workflows', name), { recursive: true });
    writeFileSync(join(cwd, '.pdd/workflows', name, 'WORKFLOW.md'), '# Instructions\n');
  }
  mkdirSync(join(outside, 'outside')); writeFileSync(join(outside, 'outside/WORKFLOW.md'), '# Outside\n');
  symlinkSync(join(outside, 'outside'), join(cwd, '.pdd/workflows/linked'));
  assert.deepEqual(listLocalWorkflows({ cwd }), { workflows: [
    { name: 'bug', file: '.pdd/workflows/bug/WORKFLOW.md' },
    { name: 'small-change', file: '.pdd/workflows/small-change/WORKFLOW.md' }], default: null });
});

// Wrong: source-only smoke passes while packed dependencies, bin mappings or bundled guidance fail in a clean consumer.
test('ALPHA4: actual packed package runs every advertised local command without private Host network or auth', t => {
  const sandbox = temp(t), home = join(sandbox, 'home'), consumer = join(sandbox, 'consumer'), project = join(sandbox, 'project');
  for (const p of [home, consumer, project]) mkdirSync(p);
  const emptyConfig = join(sandbox, 'empty-user-npmrc'), globalConfig = join(sandbox, 'empty-global-npmrc');
  writeFileSync(emptyConfig, ''); writeFileSync(globalConfig, '');
  const env = { PATH: process.env.PATH, HOME: home, TMPDIR: sandbox,
    npm_config_cache: join(sandbox, 'cache'), npm_config_userconfig: emptyConfig, npm_config_globalconfig: globalConfig,
    npm_config_offline: 'true', npm_config_audit: 'false', npm_config_fund: 'false' };
  const pack = JSON.parse(execFileSync('npm', ['pack', '--ignore-scripts', '--json', '--pack-destination', sandbox],
    { cwd: root, env, encoding: 'utf8', timeout: 30000 }))[0];
  const archive = join(sandbox, pack.filename), names = pack.files.map(f => f.path);
  for (const required of ['bin/pdd.mjs', 'docs/prompting-guide.md', 'skills/pdd/SKILL.md', '.pdd/workflows/feature/WORKFLOW.md',
    '.pdd/workflows/bug/WORKFLOW.md', '.pdd/workflows/small-change/WORKFLOW.md', 'examples/ticket-status/README.md','src/workflow-definition-loader.mjs', '.pdd/workflows/feature/workflow.json']) assert.ok(names.includes(required), required);
  assert.equal(names.some(name => name.includes('host-adapter') || /^(?:test|ops|infra|ui)\//.test(name)), false);
  execFileSync('npm', ['install', '--prefix', consumer, archive, '--ignore-scripts', '--offline', '--no-audit', '--no-fund', '--package-lock=false'],
    { cwd: consumer, env, encoding: 'utf8', timeout: 30000 });
  const metadata = JSON.parse(readFileSync(join(root, 'package.json'))), packed = join(consumer, 'node_modules', metadata.name);
  const bin = join(consumer, 'node_modules/.bin/pdd'); assert.ok(existsSync(bin));
  const guard = join(sandbox, 'no-private-effects.mjs');
  writeFileSync(guard, `import fs from 'node:fs';import http from 'node:http';import https from 'node:https';import net from 'node:net';import child from 'node:child_process';import {syncBuiltinESMExports} from 'node:module';
const stop=()=>{throw Error('Forbidden private/network/process effect');};
for(const x of [http,https]){x.request=stop;x.get=stop;}net.connect=stop;net.createConnection=stop;globalThis.fetch=stop;
for(const key of ['spawn','spawnSync','exec','execFile','execSync','execFileSync','fork'])child[key]=stop;
for(const key of ['readFileSync','readdirSync','statSync','lstatSync']){const original=fs[key];fs[key]=function(path,...args){if(/(?:\\/pocket\\/|\\/\\.ssh(?:\\/|$)|\\/credentials(?:\\/|$)|\\/\\.npmrc$)/.test(String(path)))stop();return original.call(this,path,...args);};}syncBuiltinESMExports();`);
  const run = (args, cwd = project) => spawnSync(process.execPath, ['--import', guard, bin, ...args],
    { cwd, env, encoding: 'utf8', timeout: 5000 });
  for (const argv of [[], ['--help'], ['-h'], ['help'], ['workflow', '--help'], ['workflow', 'list', '--help'], ['completion', '--help'], ['session','--help'], ['workflow','run','--help'], ['workflow','resume','--help'], ['workflow','attach','--help']]) {
    const answer = run(argv); assert.equal(answer.status, 0, answer.stderr); assert.equal(answer.stderr, '');
    assert.ok(answer.stdout.includes('pdd')); assert.doesNotMatch(answer.stdout, /pdd (?:run|verify|try|lint|runtime|doctor|phone)\b/);
  }
  const version = run(['--version']); assert.equal(version.status, 0); assert.equal(version.stdout, `${metadata.version}\n`);
  const skill = run(['--skill']); assert.equal(skill.status, 0, skill.stderr);
  const guide = readFileSync(join(packed, 'docs/prompting-guide.md'), 'utf8'), skillText = readFileSync(join(packed, 'skills/pdd/SKILL.md'), 'utf8');
  assert.ok(skill.stdout.includes(guide)); assert.ok(skill.stdout.indexOf(guide) < skill.stdout.indexOf(skillText));
  for (const name of names.filter(name => name.startsWith('skills/pdd/references/') && name.endsWith('.md'))) {
    assert.ok(skill.stdout.includes(readFileSync(join(packed, name), 'utf8')), name);
  }
  const empty = run(['workflow', 'list', '--json']); assert.equal(empty.status, 0,empty.stderr);
  assert.deepEqual(JSON.parse(empty.stdout).workflows.map(w=>w.name),['bug','feature','small-change']);assert.equal(JSON.parse(empty.stdout).default,null);
  const recipes = run(['workflow', 'list', '--json'], packed); assert.equal(recipes.status, 0);
  assert.deepEqual(JSON.parse(recipes.stdout).workflows.map(w => w.name), ['bug', 'feature', 'small-change']);
  const human = run(['workflow', 'list'], packed); assert.equal(human.status, 0); assert.ok(human.stdout.includes('feature'));assert.ok(human.stdout.includes('Listing starts no work.'));
  for (const shell of ['bash', 'zsh']) {
    const result = run(['completion', shell]); assert.equal(result.status, 0, result.stderr);
    assert.doesNotMatch(result.stdout, /\b(?:runtime|doctor|verify|lint|phone|machine)\b/);
    const script = join(sandbox, `completion.${shell}`); writeFileSync(script, result.stdout);
    if (shell === 'bash') {
      const loaded = spawnSync('bash', ['--noprofile', '--norc', '-c', 'source "$1"; COMP_WORDS=(pdd workflow ""); COMP_CWORD=2; _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}"', 'test', script], { env, encoding: 'utf8' });
      assert.equal(loaded.status, 0, loaded.stderr); assert.ok(loaded.stdout.split('\n').includes('list'));
      const selected=spawnSync('bash',['--noprofile','--norc','-c','source "$1"; COMP_WORDS=(pdd workflow bug --agent ""); COMP_CWORD=4; _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}"','test',script],{env,encoding:'utf8'});
      assert.equal(selected.status,0,selected.stderr);assert.deepEqual(selected.stdout.trim().split('\n').sort(),['claude','codex']);
      const decisions=spawnSync('bash',['--noprofile','--norc','-c','source "$1"; COMP_WORDS=(pdd workflow resume a1234567-1234-4123-8123-123456789abc --decision ""); COMP_CWORD=5; _pdd_complete; printf "%s\\n" "${COMPREPLY[@]}"','test',script],{env,encoding:'utf8'});
      assert.equal(decisions.status,0,decisions.stderr);assert.deepEqual(decisions.stdout.trim().split('\n').sort(),['approve','skip']);
    } else {
      const loaded = spawnSync('zsh', ['-f', '-c', 'autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; [[ $_comps[pdd] == _pdd ]] || exit 3; _describe() { print -rl -- "${choices[@]}"; }; words=(pdd workflow ""); CURRENT=3; _pdd', 'test', script], { env, encoding: 'utf8' });
      assert.equal(loaded.status, 0, loaded.stderr); assert.ok(loaded.stdout.split('\n').includes('list'));
      const selected=spawnSync('zsh',['-f','-c','autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; _describe() { print -rl -- "${choices[@]}"; }; words=(pdd workflow feature --agent ""); CURRENT=5; _pdd','test',script],{env,encoding:'utf8'});
      assert.equal(selected.status,0,selected.stderr);assert.deepEqual(selected.stdout.trim().split('\n').sort(),['claude','codex']);
      const decisions=spawnSync('zsh',['-f','-c','autoload -Uz compinit; compinit -D -i || exit 1; source "$1"; _describe() { print -rl -- "${choices[@]}"; }; words=(pdd workflow resume a1234567-1234-4123-8123-123456789abc --decision ""); CURRENT=6; _pdd','test',script],{env,encoding:'utf8'});
      assert.equal(decisions.status,0,decisions.stderr);assert.deepEqual(decisions.stdout.trim().split('\n').sort(),['approve','skip']);
    }
  }
  for (const word of ['run', 'verify', 'try', 'lint', 'runtime', 'replay', 'call', 'tests', 'doctor', 'phone', 'machine', 'repo', 'agents', 'workbench', 'unknown']) {
    for (const args of [[word], [word, '--help'], [word, '-h']]) {
      const result = run(args); assert.equal(result.status, 2, JSON.stringify(args)); assert.equal(result.stdout, ''); assert.ok(result.stderr.trim());
    }
  }
  const fakeBin = join(sandbox, 'native-bin'); mkdirSync(fakeBin);
  const nativeScript = `#!${process.execPath}
import fs from 'node:fs';
const input=fs.readFileSync(0,'utf8');
console.log(JSON.stringify({executable:process.argv[1],argv:process.argv.slice(2),cwd:process.cwd(),input,setting:process.env.NATIVE_SETTING_EXAMPLE}));
process.exit(Number(process.env.NATIVE_FIXTURE_EXIT||0));
`;
  for (const name of ['codex','claude']) writeFileSync(join(fakeBin,name), nativeScript, {mode:0o755});
  const nativeEnv = {...env, PATH:fakeBin+':'+env.PATH,NATIVE_SETTING_EXAMPLE:'unchanged'};
  const request = 'Help with this project; $(touch must-not-exist) "quoted"';
  for (const agent of ['codex','claude']) {
    const launched = spawnSync(process.execPath,[bin,'session','--agent',agent,request],
      {cwd:project,env:nativeEnv,input:'native stdin is inherited\n',encoding:'utf8',timeout:5000});
    assert.equal(launched.status,0,launched.stderr);const observed=JSON.parse(launched.stdout);
    assert.equal(observed.executable,join(fakeBin,agent));assert.equal(observed.argv.length,agent==='codex'?5:2); assert.ok(observed.argv.at(-1).includes(request));
    assert.ok(observed.argv.at(-1).includes(guide));assert.ok(observed.argv.at(-1).indexOf(guide)<observed.argv.at(-1).indexOf(skillText));
    for(const name of names.filter(name=>name.startsWith('.pdd/workflows/')&&name.endsWith('.md')))
      assert.ok(observed.argv.at(-1).includes(readFileSync(join(packed,name),'utf8')),name);
    assert.ok(observed.argv.at(-1).includes(readFileSync(join(packed,'docs/workflows.md'),'utf8')));
    assert.equal(observed.cwd,project);assert.equal(observed.input,'native stdin is inherited\n');assert.equal(observed.setting,'unchanged');
  }
  for (const name of ['feature','bug','small-change']) {
    for (const agent of [null,'codex','claude']) {
      const args=[bin,'workflow',name,...(agent?['--agent',agent]:[]),'--',request+' --help'];
      const launched=spawnSync(process.execPath,args,{cwd:project,env:nativeEnv,input:'selected recipe input',encoding:'utf8',timeout:5000});
      assert.equal(launched.status,0,launched.stderr);const observed=JSON.parse(launched.stdout),payload=observed.argv.at(-1);
      assert.equal(observed.executable,join(fakeBin,agent??'codex'));assert.equal(observed.argv.length,(agent??'codex')==='codex'?5:2);assert.ok(payload.includes(guide));assert.ok(payload.includes(request+' --help'));
      assert.equal(observed.cwd,project);assert.equal(observed.input,'selected recipe input');assert.equal(observed.setting,'unchanged');
      const entry=`.pdd/workflows/${name}/WORKFLOW.md`,entryText=readFileSync(join(packed,entry),'utf8');
      assert.ok(payload.includes(entryText));assert.ok(payload.indexOf(guide)<payload.indexOf(entryText));
      for(const file of names.filter(file=>file.startsWith(`.pdd/workflows/${name}/`)&&file.endsWith('.md')))
        assert.ok(payload.includes(readFileSync(join(packed,file),'utf8')),file);
      for(const other of ['feature','bug','small-change'].filter(other=>other!==name))
        assert.equal(payload.includes(`--- ${join(packed,'.pdd/workflows',other,'WORKFLOW.md')} ---`),false);
    }
  }
  for(const args of [['workflow','unknown'],['workflow','../feature'],['workflow','/feature'],['workflow','unknown','--help'],['workflow','feature','--agent','other']]){
    const refused=run(args);assert.equal(refused.status,2);assert.equal(refused.stdout,'');
  }
  for(const args of [['workflow','feature','--help'],['help','workflow','bug']]){
    const helped=run(args);assert.equal(helped.status,0);assert.equal(helped.stderr,'');
  }
  const selectedExit=spawnSync(process.execPath,[bin,'workflow','bug'],{cwd:project,env:{...nativeEnv,NATIVE_FIXTURE_EXIT:'9'},input:'',encoding:'utf8',timeout:5000});assert.equal(selectedExit.status,9);
  const missingEntry=join(packed,'.pdd/workflows/feature/WORKFLOW.md');rmSync(missingEntry);
  const selectedMissing=spawnSync(process.execPath,[bin,'workflow','feature'],{cwd:project,env:nativeEnv,input:'',encoding:'utf8',timeout:5000});assert.equal(selectedMissing.status,1);assert.equal(selectedMissing.stdout,'');
  const exited=spawnSync(process.execPath,[bin,'session'],{cwd:project,env:{...nativeEnv,NATIVE_FIXTURE_EXIT:'7'},input:'',encoding:'utf8',timeout:5000});
  assert.equal(exited.status,7);assert.equal(JSON.parse(exited.stdout).argv.length,5);
  const missing=spawnSync(process.execPath,[bin,'session','--agent','claude'],{cwd:project,env:{...env,PATH:home},input:'',encoding:'utf8',timeout:5000});
  assert.equal(missing.status,127);assert.equal(missing.stdout,'');assert.ok(missing.stderr.includes('claude'));
  rmSync(join(packed,'docs/prompting-guide.md'));
  const missingGuide=spawnSync(process.execPath,[bin,'session'],{cwd:project,env:nativeEnv,input:'',encoding:'utf8',timeout:5000});
  assert.equal(missingGuide.status,1);assert.equal(missingGuide.stdout,'');
  assert.equal(existsSync(join(project,'must-not-exist')),false);
  assert.deepEqual(readdirSync(home), []); assert.deepEqual(readdirSync(project), []);
  assert.ok(PUBLIC_COMMAND_MANIFEST.length > 0);
});

// Wrong: launch uses shell interpolation/config overrides, drops cwd/stdio, retries, or duplicates terminal Ctrl-C.
test('ALPHA5: native argv and process lifetime preserve settings exits and directed signal semantics', async () => {
  for (const agent of ['codex','claude']) {
    const child=new EventEmitter(), signals=new EventEmitter(),calls=[],kills=[];
    child.kill=name=>kills.push(name);
    const context='# Full guide\nquoted "value"\nFull manual recipes';
    const promise=launchNativeSession({agent,cwd:'/project with spaces',context,request:'x; $(command)',stderr:capture()},
      {spawn:(...args)=>{calls.push(args);return child;},signals,stdinIsTTY:false});
    assert.equal(calls.length,1);assert.equal(calls[0][0],agent);assert.equal(calls[0][1].length,agent==='codex'?5:2);
    assert.deepEqual(calls[0][1].slice(0,-1),agent==='codex'?['--no-daemon','--dangerously-bypass-approvals-and-sandbox','-c','projects={"/project with spaces"={trust_level="trusted"}}']:['--dangerously-skip-permissions']);
    assert.ok(calls[0][1].at(-1).includes(context));assert.ok(calls[0][1].at(-1).includes('x; $(command)'));
    assert.deepEqual(calls[0][2],{cwd:'/project with spaces',stdio:'inherit',shell:false});
    signals.emit('SIGINT');signals.emit('SIGTERM');signals.emit('SIGHUP');assert.deepEqual(kills,['SIGINT','SIGTERM','SIGHUP']);
    let resolved=false;promise.then(()=>{resolved=true;});
    // Native process exit alone can precede stdio close; neither a turn nor a handoff is a completion signal.
    child.emit('exit',19,null);await new Promise(resolve=>setImmediate(resolve));assert.equal(resolved,false);
    child.emit('close',19,null);assert.equal(await promise,19);
    for(const name of ['SIGINT','SIGTERM','SIGHUP'])assert.equal(signals.listenerCount(name),0);
  }
  const child=new EventEmitter(),signals=new EventEmitter();child.kill=()=>assert.fail('Terminal already delivered SIGINT');
  const done=launchNativeSession({agent:'codex',cwd:'/project',context:'Full guide',stderr:capture()},
    {spawn:()=>child,signals,stdinIsTTY:true});signals.emit('SIGINT');child.emit('close',null,'SIGINT');assert.equal(await done,130);
  assert.equal(signals.listenerCount('SIGINT'),0);
});

// Wrong: workflow names remain unavailable, load all recipes, or are treated as untrusted paths/native arguments.
test('ALPHA6: direct workflow selects exactly one bundled recipe before one unchanged native launch',async t=>{
  for(const name of ['feature','bug','small-change']){
    const stdout=capture(),stderr=capture(),calls=[];
    const code=await runPdd(['workflow',name,'--agent','claude','--','--dangerously-not-a-flag'],
      {packageRoot:root,cwd:'/chosen project',stdout,stderr,nativeSession:async input=>{calls.push(input);return 17;}});
    assert.equal(code,17);assert.equal(calls.length,1);const input=calls[0];
    assert.equal(input.agent,'claude');assert.equal(input.cwd,'/chosen project');assert.equal(input.request,'--dangerously-not-a-flag');
    assert.ok(input.context.includes(`Selected bundled workflow: ${name}.`));
    assert.ok(input.context.includes(readFileSync(join(root,'.pdd/workflows',name,'WORKFLOW.md'),'utf8')));
    const plan=parseArgv(['workflow',name]);assert.equal(plan.workflowName,name);assert.equal(plan.local,'session');
  }
  for(const words of [['workflow','unknown'],['workflow','../bug'],['workflow','feature/../../bug'],['workflow','unknown','--help']]){
    assert.equal(await runPdd(words,{packageRoot:'/absent',stdout:capture(),stderr:capture(),nativeSession:()=>assert.fail('No native')}),2);
  }
  assert.equal(await runPdd(['workflow','bug','--help'],{packageRoot:'/absent',stdout:capture(),stderr:capture(),nativeSession:()=>assert.fail('No native')}),0);
});

// Wrong: workflow.run reuses the one-conversation shortcut, preloads resume identity, or leaks a structured object instead of its actual message.
test('ALPHA7: run and resume dispatch structured owner API with exact existing ports and saved identity owned by runner',async()=>{
  const uuid='a1234567-1234-4123-8123-123456789abc';
  for(const issue of ['42','owner/repo#42','https://github.com/owner/repo/issues/42']){
    const output=capture(),errors=capture(),calls=[];
    const runner={runWorkflow:async(input,ports)=>{calls.push({input,ports});return {exitCode:2,state:'waiting',runId:uuid,stage:'approve',message:'waiting '+uuid+' approve'};}};
    const code=await runPdd(['workflow','run','feature',issue,'--agent','claude'],{workflowRunner:runner,cwd:'/chosen',packageRoot:'/bundle',stdout:output,stderr:errors});
    assert.equal(code,2);assert.equal(calls.length,1);assert.deepEqual(calls[0].input,{name:'feature',issue,agent:'claude',cwd:'/chosen',packageRoot:'/bundle'});
    assert.equal(typeof calls[0].ports.loadGuidance,'function');assert.equal(calls[0].ports.launchNativeSession,launchNativeSession);
    assert.equal(calls[0].ports.stdout,output);assert.equal(calls[0].ports.stderr,errors);assert.equal(calls[0].input.context,undefined);
    assert.equal(output.text,'waiting '+uuid+' approve\n');assert.equal(errors.text,'');
  }
  for(const decision of [undefined,'approve','skip']){
    const output=capture(),calls=[];
    const code=await runPdd(['workflow','resume',uuid,...(decision?['--decision',decision]:[])],{
      cwd:'/chosen',packageRoot:'/absent-guide',stdout:output,stderr:capture(),workflowRunner:{resumeWorkflow:async(input,ports)=>{
        calls.push(input);assert.equal(typeof ports.loadGuidance,'function');return {exitCode:0,state:'completed',runId:uuid,stage:'wait-merge',message:'completed '+uuid};}}});
    assert.equal(code,0);assert.deepEqual(calls,[{runId:uuid,cwd:'/chosen',packageRoot:'/absent-guide',...(decision?{decision}:{})}]);
    assert.equal(output.text,'completed '+uuid+'\n');
  }
  const calls=[];assert.equal(await runPdd(['workflow','run','small-change','1'],{stdout:capture(),stderr:capture(),workflowRunner:{runWorkflow:async input=>{
    calls.push(input);return {exitCode:1,state:'recovery_required',runId:uuid,stage:'change',message:'recovery_required '+uuid};}}}),1);
  assert.equal(calls[0].agent,'codex');assert.equal(calls.length,1);
});


test('0.1.0 warns once when another pdd is first on PATH without changing dispatch', async t => {
  const fake = temp(t); const earlier = join(fake, 'pdd'); writeFileSync(earlier, '#!/bin/sh\necho 0.0.310\n'); execFileSync('chmod', ['700', earlier]);
  const stdout = capture(), stderr = capture();
  assert.equal(await runPdd(['--version'], {packageRoot: root, env: {PATH: fake}, stdout, stderr}), 0);
  assert.equal(stdout.text, '0.1.0\n'); assert.equal(stderr.text, `Another pdd is first on PATH: ${earlier}\n`);
});

test('workflow run and malformed resume explain the missing workflow name', async () => {
  const expected = 'Name the workflow: pdd workflow run small-change 81 (or bug, feature). See: pdd workflow list.\n';
  for (const args of [['workflow', 'run'], ['workflow', 'run', '81'], ['workflow', 'run', 'Small-change', '81'],
    ['workflow', 'run', 'small-change'], ['workflow', 'resume'], ['workflow', 'resume', 'not-a-run']]) {
    const stderr = capture();
    assert.equal(await runPdd(args, { packageRoot: root, stdout: capture(), stderr }), 2);
    assert.equal(stderr.text, expected);
  }
});

// Wrong: malformed references/options reach effects, omitted resume decision dispatches native directly, or an owner failure is automatically retried.
test('ALPHA8: runner argument failures and invalid replies are finite without native effects or a second call',async()=>{
  const uuid='a1234567-1234-4123-8123-123456789abc';
  const invalid=[['workflow','run'],['workflow','run','../unknown','1'],['workflow','run','feature','0'],['workflow','run','bug','../issue'],
    ['workflow','run','feature','https://example.com/o/r/issues/1'],['workflow','run','feature','42','extra'],
    ['workflow','run','small-change','81','--replace'],
    ['workflow','run','feature','42','--agent','other'],['workflow','resume','../run'],['workflow','resume',uuid,'--agent','claude'],
    ['workflow','resume',uuid,'--decision','yes'],['workflow','resume',uuid,'--decision','skip','--decision','approve']];
  for(const args of invalid){assert.equal(await runPdd(args,{packageRoot:'/absent',stdout:capture(),stderr:capture(),workflowRunner:{
    runWorkflow:()=>assert.fail('No runner'),resumeWorkflow:()=>assert.fail('No runner')}}),2);}
  for(const answer of [undefined,{exitCode:0,state:'invented',message:'no'}, {exitCode:NaN,state:'completed',message:'no'}, {exitCode:0,state:'completed',message:''}]){
    let calls=0;assert.equal(await runPdd(['workflow','run','feature','42'],{stdout:capture(),stderr:capture(),workflowRunner:{runWorkflow:async()=>{calls++;return answer;}}}),1);assert.equal(calls,1);
  }
  let calls=0;assert.equal(await runPdd(['workflow','resume',uuid],{stdout:capture(),stderr:capture(),workflowRunner:{resumeWorkflow:async()=>{calls++;throw Error('possible effect, no retry');}}}),1);assert.equal(calls,1);
});
