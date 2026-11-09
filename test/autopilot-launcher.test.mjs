import './helpers/test-home.mjs';
import { isolatedCheckCapacity } from './helpers/check-machine.mjs';
import {healthyDoctorPorts} from './helpers/doctor-fixture.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
import test from 'node:test';
import * as nativeFs from 'node:fs';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync, utimesSync, existsSync, realpathSync, renameSync, symlinkSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { execFileSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { loadAgentDefinitions } from '../src/agent-config.mjs';
import { codexConfigs, tomlBasicString } from './helpers/codex-config-args.mjs';
import { automaticFixture } from './helpers/autopilot-run-base-fixture.mjs';

const root = resolve('.');
const capture = () => ({ text: '', write(s) { this.text += s; } });
async function fixture(t, options = {}) {
  const dir = mkdtempSync(join(tmpdir(), options.tempPrefix ?? 'pdd-autopilot-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, options.cwdName ?? 'repo'), home = join(dir, 'home');
  mkdirSync(cwd); mkdirSync(home);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: options.mode ?? 'auto', trust: ['helper'] } }));
  const f = { dir, cwd, home, time: Date.parse('2026-11-04T00:00:00Z'), polls: [], prompts: [], runs: [], timers: [], comments: [], ack: [], issues: [], etag: '"one"', active: false };
  f.ports = {
    ...healthyMachine, checkCapacityPorts: isolatedCheckCapacity(dir), stateRoot: join(home, 'state'), now: () => f.time,
    // These fakes stand for a checkout where pdd workflows can start (#3050).
    allocationCheck: async () => ({ state: 'ready', message: '' }),
    readRunProgress: async () => f.runProgress ?? [],
    warn: text => { (f.warnings ??= []).push(text); },
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }),
    pathDiagnostic: () => [],
    run: async (command, args) => {
      f.runs.push([command, args]);
      if (command === 'git') return { code: 0, stdout: (args.includes('--git-common-dir') ? join(cwd, '.git') : cwd) + '\n', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo","defaultBranchRef":{"name":"trunk"},"url":"https://github.com/owner/repo"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api') { if (args.some(x => String(x).includes('/reviews?'))) return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n[]', stderr: '' }; if (args.some(x => String(x).includes('/permission'))) return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n{"permission":"none"}', stderr: '' }; f.ack.push(args); return { code: 0, stdout: '{}', stderr: '' }; }
      if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
      throw Error(`unexpected process ${command} ${args}`);
    },
    timer: async (action, state) => { f.timers.push([action, structuredClone(state)]); if (action === 'start') f.active = true; if (action === 'stop') f.active = false; return f.active; },
    queryIssues: async (state) => { f.polls.push(state.etag); return { status: f.status ?? 200, etag: f.etag, issues: structuredClone(f.issues) }; },
    comments: async number => { f.comments.push(number); return f.issueComments?.[number] ?? []; },
    reconcileDependencyIntake: async () => ({ eligible: f.issues.map(issue => issue.html_url), queued: [], skipped: [] }),
    herdr: async args => {
      f.herdrCalls ??= []; f.herdrCalls.push(args);
      if (args[0] === 'status') return { running: f.serverRunning !== false };
      const live = { pane_id:'p1', workspace_id:'w1', cwd, foreground_cwd:cwd, tab_id:'t1', terminal_id:'term1', agent:'codex', agent_status:f.agentStatus ?? 'idle', agent_session:'session' };
      if (args[0] === 'pane' && args[1] === 'list') return {result:{type:'pane_list',panes:f.agentStarted?[live]:[]}};
      if (args[0] === 'workspace') return { result: { type:'workspace_info', workspace: { workspace_id: 'w1' }, root_pane: { pane_id: 'p1' } } };
      if (args[0] === 'pane' && args[1] === 'get') return { result: { type:'pane_info', pane:live } };
      if (args[0] === 'agent' && args[1] === 'get') {
        if (!f.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' });
        return { result: { type:'agent_info', agent:live } };
      }
      if (args[0] === 'pane' && args[1] === 'run') { f.agentStarted = true; return {}; }
      if (args[0] === 'pane' && args[1] === 'read') return '';
      if (args[0] === 'agent' && args[1] === 'prompt') {
        const instruction = args.at(-1), match = /Artifact path: (.+)/.exec(instruction);
        f.prompts.push(match ? readFileSync(JSON.parse(match[1]), 'utf8') : instruction);
      }
      return {};
    },
  };
  // Use the same selected definition and fake account as launcher admission.
  f.ports.doctorPorts=input=>{
    const ports=healthyDoctorPorts(input),run=ports.run;
    let definitions=[];
    ports.agentDefinitions=async ({env})=>definitions=f.ports.selectAgent
      ? [await f.ports.selectAgent({cwd}, {...f.ports,env}) ?? {id:'codex',kind:'codex',command:'codex',env:{}}]
      : loadAgentDefinitions({cwd,env});
    const read=ports.files.readFileSync;
    ports.files.readFileSync=path=>path.includes('/skills/')?'skill':path.endsWith('/.gemini/oauth_creds.json')?(f.ports.selectAgent?'{"refresh_token":"fixture"}':nativeFs.readFileSync(path,'utf8')):read(path);
    ports.run=async(file,args,options)=>{
      if (!f.ports.selectAgent && ['codex','claude','agy','gemini'].includes(file)) return f.ports.run(file,args,options);
      if (args[0]==='models' || args[0]==='--version' && file!=='git' && file!=='gh' && file!=='herdr' && !file.endsWith('/pdd')) return {code:definitions.some(def=>def.command===file)?0:1,stdout:'fixture',stderr:''};
      if (args.join(' ')==='login status' || args.join(' ')==='auth status --json') {
        (f.doctorAccounts??=[]).push({...options.env});
        const ready=!f.accountReady || f.accountReady(options.env);
        return {code:ready?0:1,stdout:args[0]==='auth'?JSON.stringify({loggedIn:ready}):ready?'Logged in using ChatGPT':'Not logged in',stderr:''};
      }
      return run(file,args,options);
    };
    return ports;
  };
  f.module = await import('../src/autopilot-launcher.mjs');
  f.invoke = async (command, extra = {}) => f.module.runAutopilotLauncher({ command, cwd, env: { HOME: home, PATH: process.env.PATH }, packageRoot: root, issues: [], ...extra }, f.ports);
  f.stateFile = () => join(f.ports.stateRoot, readdirSync(f.ports.stateRoot).find(x => x.endsWith('.json')));
  f.state = () => JSON.parse(readFileSync(f.stateFile(), 'utf8'));
  f.tick = () => f.module.tickAutopilot(f.stateFile(), f.ports);
  return f;
}
const issue = (number, extra = {}) => ({ number, state: 'open', title: `Issue ${number}`, body: 'trusted body', user: { login: 'owner' }, author_association: 'OWNER', created_at: '2026-11-04T00:01:00Z', updated_at: '2026-11-04T00:01:00Z', comments: 0, labels: [], html_url: `https://github.com/owner/repo/issues/${number}`, ...extra });

// Native startup cases use the public launcher with fake programs, never live agents.
async function nativeStartup(t, { kind = 'codex', custom = false, cwdName, body = 'Please fix this synthetic startup case.', seed, codexHome = true } = {}) {
  const f = await fixture(t, { mode: 'observe', cwdName });
  const bin = join(f.dir, 'bin'), profile = join(f.home, 'profile chosen');
  mkdirSync(bin); mkdirSync(profile);
  f.ports.stateRoot = join(f.dir, 'state');
  const record = join(f.dir, 'native.jsonl');
  const script = `#!${process.execPath}\nconst fs = require('node:fs'); fs.appendFileSync(${JSON.stringify(record)}, JSON.stringify({command:process.argv[1],argv:process.argv.slice(2),cwd:process.cwd(),env:{CODEX_HOME:process.env.CODEX_HOME,CLAUDE_CONFIG_DIR:process.env.CLAUDE_CONFIG_DIR,STARTUP_TEST_VALUE:process.env.STARTUP_TEST_VALUE,PDD_AUTOPILOT_CONTEXT:process.env.PDD_AUTOPILOT_CONTEXT}})+'\\n');\n`;
  for (const name of ['codex', 'fake-provider', 'chosen codex wrapper']) writeFileSync(join(bin, name), script, { mode: 0o755 });
  const env = { PDD_SUITE_QUEUE: undefined, PDD_VM_SUITE_LOCK: undefined, HOME: f.home, PATH: `${bin}:/usr/bin:/bin`, CODEX_HOME: profile, XDG_CONFIG_HOME: join(f.home, '.config') };
  if (!codexHome) env.CODEX_HOME = undefined; // Mask the launcher's ambient fallback too.
  f.ports.env = env;
  const value = 'a b\'c"d\\e$HOME';
  env.CLAUDE_CONFIG_DIR = join(f.home, value);
  let selected = { id: kind, kind, command: kind === 'codex' ? 'codex' : join(bin, 'fake-provider'), env: {} };
  if (custom) {
    const folder = join(f.home, '.config', 'pdd'); mkdirSync(folder, { recursive: true });
    writeFileSync(join(folder, 'agents.json'), JSON.stringify({ include_defaults: false, agents: [{ name: 'Chosen startup fixture', kind, command: join(bin, 'chosen codex wrapper'), env: { CODEX_HOME: profile, STARTUP_TEST_VALUE: value } }] }));
    [selected] = loadAgentDefinitions({ cwd: f.cwd, env });
  }
  writeFileSync(join(profile, 'config.toml'), `model="gpt-6.1-sol"\nmodel_reasoning_effort="high"\ncheck_for_update_on_startup=true\n[projects.${JSON.stringify(f.cwd)}]\ntrust_level="untrusted"\n[projects.${JSON.stringify(join(f.dir, 'unrelated'))}]\ntrust_level="untrusted"\n`);
  const snapshot = folder => Object.fromEntries(readdirSync(folder, { recursive: true, withFileTypes: true }).filter(x => x.isFile()).map(x => {
    const path = join(x.parentPath ?? x.path, x.name);
    return [path, readFileSync(path)];
  }));
  const saved = snapshot(f.home), parentEnv = { ...process.env };
  f.ports.selectAgent = async () => selected;
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    const reply = await herdr(args);
    if (args[0] === 'pane' && args[1] === 'run') execFileSync('/bin/sh', ['-c', args[3]], { cwd: f.cwd, env, timeout: 10000 });
    return reply;
  };
  f.issues = [issue(101, { body })];
  // A saved coordinator identity (no saved agent) lets a case choose the context values.
  if (seed) { mkdirSync(f.ports.stateRoot); writeFileSync(join(f.ports.stateRoot, `${createHash('sha256').update(f.cwd).digest('hex').slice(0, 20)}.json`), JSON.stringify(seed)); }
  const result = await f.invoke('start', { env, runs: '1' });
  assert.equal(result.exitCode, 0, result.message);
  const calls = existsSync(record) ? readFileSync(record, 'utf8').trim().split('\n').map(JSON.parse) : [];
  assert.equal(calls.length, 1, 'one selected fake executable runs');
  const [call] = calls;
  assert.equal(call.command, selected.command === 'codex' ? join(bin, 'codex') : selected.command);
  // process.cwd() resolves the temporary directory's /var symlink on macOS.
  assert.equal(call.cwd, realpathSync(f.cwd));
  assert.equal(call.env.CODEX_HOME, codexHome ? profile : undefined); assert.equal(call.env.CLAUDE_CONFIG_DIR, env.CLAUDE_CONFIG_DIR);
  assert.equal(call.env.STARTUP_TEST_VALUE, custom ? value : undefined);
  assert.ok(Object.keys(process.env).length === Object.keys(parentEnv).length && Object.entries(parentEnv).every(([key, value]) => process.env[key] === value), 'parent environment is unchanged');
  assert.deepEqual(snapshot(f.home), saved, 'agent settings and file inventory remain unchanged');
  const configs = [], operands = [];
  for (let i = 0; i < call.argv.length; i++) {
    if (call.argv[i] === '-c' || call.argv[i] === '--config') configs.push(call.argv[++i]);
    else if (!call.argv[i].startsWith('-')) operands.push(call.argv[i]);
  }
  assert.equal(operands.length, 0, 'the interactive process starts before its first message');
  const packet = JSON.parse(f.prompts[0].trimEnd().split('\n').at(-1));
  assert.equal(packet.issues[0].body, body); assert.equal(packet.recipeFirst, true); assert.equal(packet.runs, 1);
  assert.equal(f.timers.filter(([action]) => action === 'start').length, 1);
  assert.equal(f.state().nextTick, f.time + 30 * 60 * 1000);
  f.status = 304; await f.tick();
  assert.equal(f.prompts.length, 1, 'unchanged tick sends no extra packet');
  assert.equal(f.herdrCalls.filter(args => args[0] === 'pane' && args[1] === 'run').length, 1);
  assert.equal(existsSync(join(f.dir, 'PDD_SENTINEL')), false);
  assert.equal(existsSync(join(f.cwd, 'PDD_SENTINEL')), false);
  return { ...f, call, configs };
}

function codexStartupConfig({ cwd, call, configs }) {
  assert.ok(call.argv.includes('--no-daemon'));
  assert.ok(call.argv.includes('--dangerously-bypass-approvals-and-sandbox'));
  // Decode the public Codex inline-table config; do not compare the shell command.
  const trust = configs.find(value => /^projects\s*=/.test(value));
  assert.ok(trust, 'invocation config must include project trust');
  const table = trust.match(/^projects\s*=\s*\{\s*("(?:\\.|[^"\\])*")\s*=\s*\{\s*trust_level\s*=\s*("(?:\\.|[^"\\])*")\s*\}\s*\}$/);
  assert.ok(table, 'trust config must name one project key');
  assert.equal(tomlBasicString(table[1]), cwd); assert.equal(JSON.parse(table[2]), 'trusted');
  assert.ok(configs.some(value => /^check_for_update_on_startup\s*=\s*false$/.test(value)));
  assert.equal(configs.some(value => /^(?:model|model_reasoning_effort|profile)\s*=/.test(value)), false);
  assert.equal(call.argv.some(value => ['-m', '--model', '-p', '--profile'].includes(value)), false);
  // Every Codex start, fresh or saved, gives its chat commands the process context and Codex profile folder.
  const { set } = codexConfigs(call.argv);
  assert.equal(JSON.parse(set.PDD_AUTOPILOT_CONTEXT).version, 'pdd.autopilot-coordinator.v1');
  assert.equal(set.PDD_AUTOPILOT_CONTEXT, call.env.PDD_AUTOPILOT_CONTEXT);
  assert.equal(set.CODEX_HOME, call.env.CODEX_HOME);
}

test('native startup: normal Codex uses invocation trust and no update check', async t => {
  codexStartupConfig(await nativeStartup(t));
});

test('native startup: configured Codex wrapper keeps its environment and saved model', async t => {
  codexStartupConfig(await nativeStartup(t, { custom: true }));
});

test('native startup: cwd and first message keep shell syntax literal', async t => {
  const literal = "space 'single' \"double\" \\slash $HOME $(touch PDD_SENTINEL) `touch PDD_SENTINEL` ;";
  codexStartupConfig(await nativeStartup(t, { cwdName: `repo ${literal}`, body: `Keep ${literal}\nsecond line` }));
});

test('native startup: invocation overrides leave saved update and trust settings unchanged', async t => {
  codexStartupConfig(await nativeStartup(t));
});

test('native startup: Codex chat commands get the Autopilot context under any shell environment policy', async t => {
  // Issue 3031: inherit = "core" or "none" drops the process value; `set` applies after `inherit`.
  // Shell and TOML syntax in a context value must reach Codex unchanged.
  const machine = "mac 'single' \"double\" \\slash $HOME $(touch PDD_SENTINEL) `touch PDD_SENTINEL` ; \u007f é";
  const f = await nativeStartup(t, { seed: { coordinatorId: 'coordinator-3031', machine, activatedAt: '2026-11-04T00:00:00.000Z' } });
  codexStartupConfig(f);
  const envelope = { version: 'pdd.autopilot-coordinator.v1', repository: 'owner/repo', coordinatorId: 'coordinator-3031', machine, activation: '2026-11-04T00:00:00.000Z', runs: 1 };
  const { set } = codexConfigs(f.call.argv);
  assert.ok(Object.hasOwn(set, 'PDD_AUTOPILOT_CONTEXT'), `expected -c shell_environment_policy.set.PDD_AUTOPILOT_CONTEXT=..., got -c values ${JSON.stringify(f.configs)}`);
  assert.deepEqual(JSON.parse(set.PDD_AUTOPILOT_CONTEXT), envelope);
  assert.equal(set.PDD_AUTOPILOT_CONTEXT, f.call.env.PDD_AUTOPILOT_CONTEXT, 'chat commands get the same text as the coordinator process');
  assert.deepEqual(Object.keys(set), ['PDD_AUTOPILOT_CONTEXT', 'CODEX_HOME'], 'no Herdr value that the launcher cannot know');
  assert.equal(f.configs.filter(value => /^shell_environment_policy\./.test(value)).length, 2, 'no other policy key changes');
});

test('native startup: Codex chat commands keep an explicit CODEX_HOME and get none without one', async t => {
  // Under inherit = "core", a pdd workflow run from the coordinator must keep the coordinator's Codex profile.
  const explicit = await nativeStartup(t);
  assert.equal(codexConfigs(explicit.call.argv).set.CODEX_HOME, join(explicit.home, 'profile chosen'));
  const none = await nativeStartup(t, { codexHome: false });
  codexStartupConfig(none);
  assert.equal(Object.hasOwn(codexConfigs(none.call.argv).set, 'CODEX_HOME'), false, 'no invented profile folder');
});

test('native startup: a cwd with a control character stays one valid TOML project key', async t => {
  codexStartupConfig(await nativeStartup(t, { cwdName: 'repo \u007f\t del' }));
});

for (const [kind, flags] of [
  ['claude', ['--dangerously-skip-permissions']],
  ['gemini', ['--yolo']],
  ['agy', ['--dangerously-skip-permissions']],
]) test(`native startup: ${kind} keeps its interactive launch without Codex config`, async t => {
  const { call, configs } = await nativeStartup(t, { kind, custom: kind !== 'agy' });
  for (const flag of flags) assert.ok(call.argv.includes(flag));
  if (kind === 'gemini' || kind === 'agy') assert.equal(call.argv.includes('--prompt-interactive'), false);
  assert.equal(configs.length, 0);
});

test('autopilot routes parse and dispatch without setup or a runtime call', async () => {
  const stdout = capture(), stderr = capture(); let seen;
  assert.equal(parseArgv(['autopilot', 'start', '--runs', '1200000']).local, 'autopilot-start');
  assert.equal(await runPdd(['autopilot', 'start', '--runs', '3'], { cwd: '/repo', stdout, stderr, autopilotGithubPorts: { github: {} }, autopilotLauncher: { runAutopilotLauncher: async input => { seen = input; return { exitCode: 0, message: 'started' }; } } }), 0);
  assert.equal(seen.command, 'start'); assert.equal(seen.runs, '3');
  assert.equal(await runPdd(['autopilot','start','--resume-custody','owner.json'], {cwd:'/repo',stdout:capture(),stderr:capture(),autopilotGithubPorts:{github:{}},autopilotLauncher:{runAutopilotLauncher:async input=>{seen=input;return {exitCode:0,message:'started'};}}}),0); assert.equal(seen.resumeCustody,'owner.json');
  assert.equal(stdout.text, 'started\n'); assert.equal(stderr.text, '');
  assert.deepEqual(parseArgv(['autopilot', 'add', '12', '15']).operands, ['12', '15']);
});

test('start installs a timer and runs the recipe immediately; unchanged empty ticks wake no AI', async t => {
  const f = await fixture(t);
  const profile=join(f.home,'original-profile');
  f.ports.selectAgent=async()=>({id:'codex',kind:'codex',command:'codex',env:{CODEX_HOME:profile}});
  f.accountReady=env=>env.CODEX_HOME===profile;
  assert.equal((await f.invoke('start')).exitCode, 0);
  assert.equal(f.polls.length, 1); assert.equal(f.prompts.length, 1);
  assert.match(f.prompts[0], /"recipeFirst":true/);
  const context = JSON.parse(f.prompts[0].trim().split('\n').at(-1));
  assert.deepEqual(context.startAction, { command: 'pdd autopilot start', repository: 'owner/repo', mode: 'auto' });
  assert.equal(context.currentMode, 'auto');
  assert.match(f.prompts[0], /ordinary eligible work and automatic merge under the repository review, testing, strict approval and other rules/);
  assert.equal(f.state().runs, undefined);
  assert.equal(f.state().nextTick, f.time + 1800000);
  f.status = 304; await f.tick(); await f.tick();
  assert.equal(f.prompts.length, 1); assert.deepEqual(f.polls, [undefined, '"one"', '"one"']);
  const prior=f.state(), configured=prior.environment.CODEX_HOME;
  f.ports.selectAgent=async (_state, ports)=>{ assert.equal(ports.env.CODEX_HOME,configured); return {id:'codex',kind:'codex',command:'codex',env:{}}; };
  const restarted=await f.invoke('start',{env:{HOME:f.home,PATH:process.env.PATH,CODEX_HOME:join(f.dir,'unrelated-profile')}});
  assert.equal(restarted.exitCode,0,restarted.message); assert.equal(f.state().coordinatorId,prior.coordinatorId); assert.deepEqual(f.state().ownerLaunch,prior.ownerLaunch); assert.equal(f.state().environment.CODEX_HOME,configured);
  const original=f.state(), replacement=structuredClone(original), history=[{kind:'legacy-uncertain',payloadDigest:'kept'}];
  replacement.enabled=false; replacement.coordinatorId='replacement'; replacement.agent={id:'agy',kind:'agy',command:'agy'}; replacement.uncertainDeliveryHistory=history; replacement.runs=3;
  replacement.ownerLaunch={...replacement.ownerLaunch,coordinator:{...replacement.ownerLaunch.coordinator,coordinatorId:'replacement'},profile:{agent:{id:'agy',kind:'agy'},home:f.home,definitionHome:f.home,configHome:null}};
  writeFileSync(f.stateFile(),JSON.stringify(replacement));
  const launch=original.ownerLaunch, artifact=join(f.dir,'custody.json');
  writeFileSync(artifact,JSON.stringify({repository:original.repo,sourceRoot:f.cwd,coordinatorId:original.coordinatorId,machine:original.machine,activation:original.activatedAt,paneId:original.paneId,workspaceId:original.workspaceId,agent:launch.profile.agent,home:launch.profile.home,definitionHome:launch.profile.definitionHome,configHome:launch.profile.configHome,launchStartedAt:launch.startedAt}));
  f.ports.selectAgent=async()=>({id:'codex',kind:'codex',command:'codex',env:{}});
  f.ports.listRuns=async()=>[{number:17,repo:original.repo,state:'waiting',issue:{url:'https://github.com/owner/repo/issues/17'},automaticOrigin:{repository:original.repo,coordinatorId:original.coordinatorId,machine:original.machine,claim:{commentId:'11',labelEventId:'12'}}}];
  f.ports.owners={read:async()=>({json:JSON.stringify({claims:[{issue:'https://github.com/owner/repo/issues/17',active:true,owner:original.coordinatorId,coordinatorId:original.coordinatorId,machine:original.machine,commentId:'11',labelEventId:'12'}]})})};
  const oldHerdr=f.ports.herdr; f.ports.herdr=async args=>{
    const live={pane_id:original.paneId,workspace_id:original.workspaceId,cwd:f.cwd,foreground_cwd:f.cwd,tab_id:'t1',terminal_id:'term1',agent:'codex',agent_status:'idle',agent_session:'session'};
    if(args[0]==='pane'&&args[1]==='get')return {result:{type:'pane_info',pane:live}};
    if(args[0]==='workspace'&&args[1]==='get')return {result:{type:'workspace_info',workspace:{workspace_id:original.workspaceId}}};
    if(args[0]==='agent'&&args[1]==='get')return {result:{type:'agent_info',agent:live}};
    return oldHerdr(args);
  };
  const recovered=await f.invoke('start',{resumeCustody:artifact,env:{HOME:f.home,PATH:process.env.PATH,CODEX_HOME:join(f.dir,'signed-out-caller')}}); assert.equal(recovered.exitCode,0,recovered.message);
  assert.ok(f.doctorAccounts.length>=3);assert.ok(f.doctorAccounts.every(env=>env.CODEX_HOME===profile));
  const restored=f.state(); assert.equal(restored.coordinatorId,original.coordinatorId); assert.equal(restored.agent.kind,'codex'); assert.deepEqual(restored.uncertainDeliveryHistory,history); assert.equal(restored.runs,undefined);
  f.ports.listRuns=async()=>[]; const semanticOnly=await f.invoke('start',{resumeCustody:artifact}); assert.equal(semanticOnly.exitCode,0,semanticOnly.message); assert.equal(f.state().coordinatorId,original.coordinatorId); assert.deepEqual(f.state().uncertainDeliveryHistory,history); assert.equal(f.state().runs,undefined);
});

test('old and new issues are eligible; claimed work is distinguished and closed issues excluded', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(1), issue(2, { created_at: '2026-01-01T00:00:00Z' }), issue(3, { created_at: '2026-01-01T00:00:00Z', labels: [{ name: 'pdd:autopilot' }] }), issue(4, { pull_request: {} }), issue(5, { state: 'closed' }), issue(6, { labels: [{ name: 'pdd:working' }] })];
  await f.tick();
  const prompt = f.prompts.at(-1);
  assert.match(prompt, /"number":1,/); assert.match(prompt, /"number":2,/); assert.match(prompt, /"number":3,/);
  for (const n of [4, 5, 6]) assert.doesNotMatch(prompt, new RegExp(`"number":${n},`));
  await f.tick(); assert.equal(f.prompts.length, 3); // Auto reconsiders still-unclaimed ready work.
  await f.invoke('stop'); f.time += 3600000; await f.invoke('start');
  assert.equal(f.state().activatedAt, '2026-11-04T00:00:00.000Z');
});

test('a GitHub owner spelled with capitals matches the canonical lowercase eligibility URL (#3035)', async t => {
  const f = await fixture(t);
  const run = f.ports.run;
  f.ports.run = async (command, args, opts) => command === 'gh' && args[0] === 'repo'
    ? { code: 0, stdout: '{"nameWithOwner":"Serhan-Asad/PDD-Sandbox","defaultBranchRef":{"name":"main"},"url":"https://github.com/Serhan-Asad/PDD-Sandbox"}', stderr: '' }
    : run(command, args, opts);
  // GitHub spells html_url with the owner's capitals; the dependency graph stores canonical lowercase keys.
  const mixed = number => issue(number, { user: { login: 'Serhan-Asad' }, html_url: `https://github.com/Serhan-Asad/PDD-Sandbox/issues/${number}` });
  f.issues = [mixed(1), mixed(2), mixed(3)];
  f.ports.reconcileDependencyIntake = async () => ({ eligible: ['https://github.com/serhan-asad/pdd-sandbox/issues/1', 'https://github.com/serhan-asad/pdd-sandbox/issues/3'], queued: [], skipped: [] });
  const started = await f.invoke('start');
  assert.equal(started.exitCode, 0, started.message);
  const packet = JSON.parse(f.prompts.at(-1).trim().split('\n').at(-1));
  assert.deepEqual(packet.issues.map(item => [item.number, item.eligible]), [[1, true], [3, true]]);
  assert.equal(packet.issues[0].url, 'https://github.com/Serhan-Asad/PDD-Sandbox/issues/1', 'the offered item keeps GitHub spelling');
  assert.deepEqual(f.state().seen[2].selectionReasons, ['dependency-not-ready'], 'an issue absent from eligible still waits');
});

test('stranger text never reaches AI; a trusted comment admits only trusted text; acknowledgement once', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(8, { title: 'STRANGER TITLE', body: 'STRANGER BODY', user: { login: 'outside' }, author_association: 'NONE' })];
  await f.tick(); await f.tick();
  assert.equal(f.prompts.length, 1); assert.equal(f.ack.length, 1);
  f.issues[0].comments = 3; f.issues[0].updated_at = '2026-11-04T00:02:00Z';
  f.issueComments = { 8: [
    { body: 'STRANGER COMMENT', user: { login: 'outside' }, author_association: 'NONE' },
    { body: 'thanks, a maintainer will look\n\n<!-- pdd:autopilot:thanks -->', user: { login: 'owner' }, author_association: 'OWNER' },
    { body: 'Please fix the broken login', user: { login: 'helper' }, author_association: 'NONE' },
  ] };
  await f.tick();
  assert.equal(f.prompts.length, 2);
  assert.match(f.prompts[1], /Please fix the broken login/);
  assert.doesNotMatch(f.prompts[1], /STRANGER|thanks, a maintainer/);
});

test('trusted issue comments are filtered, and failed delivery is retried', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(9, { comments: 1 })];
  f.issueComments = { 9: [{ body: 'OUTSIDER', user: { login: 'outside' }, author_association: 'NONE' }] };
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => { if (args[1] === 'prompt') throw Error('delivery failed'); return herdr(args); };
  await assert.rejects(f.tick(), /delivery failed/);
  f.ports.herdr = herdr; await f.tick();
  assert.match(f.prompts[1], /trusted body/); assert.doesNotMatch(f.prompts[1], /OUTSIDER/);
});

test('stop disables only the timer; status does not poll GitHub; runs is optional, never fixed', async t => {
  const f = await fixture(t); await f.invoke('start', { runs: '7' });
  assert.match(f.prompts[0], /"runs":7/);
  const polls = f.polls.length;
  const status = await f.invoke('status'); assert.match(status.message, /owner\/repo.*codex/); assert.match(status.message, /2026-11-04T00:30:00/);
  const before = f.herdrCalls.length;
  await f.invoke('stop'); await f.tick(); await f.invoke('stop');
  assert.equal(f.herdrCalls.length, before); assert.equal(f.polls.length, polls);
  const stoppedStatus = (await f.invoke('status')).message;
  assert.match(stoppedStatus, /Autopilot disabled/); assert.match(stoppedStatus, /timer inactive/);
  assert.equal((await f.invoke('start', { runs: '0' })).exitCode, 2);
});

test('add marks every named old issue with exactly pdd:autopilot', async t => {
  const f = await fixture(t);
  assert.equal((await f.invoke('add', { issues: ['12', '15'] })).exitCode, 0);
  assert.equal(f.ack.filter(args => args.some(x => String(x).includes('pdd:autopilot'))).length, 3);
});

test('off and missing dependencies give one actionable line without starting an agent', async t => {
  const f = await fixture(t, { mode: 'off' });
  const result = await f.invoke('start'); assert.equal(result.exitCode, 0); assert.match(result.message, /off/);
  assert.equal(f.prompts.length, 0); assert.equal(f.timers.length, 0);
  writeFileSync(join(f.cwd, 'pdd.json'), '{"autopilot":{"mode":"auto","trust":[]}}');
  f.ports.selectAgent = async () => null;
  const missing = await f.invoke('start'); assert.equal(missing.message.split('\n').length, 1); assert.match(missing.message, /sign in/i);
});

test('two machine launchers offer the same issue to the skill without making a competing claim', async t => {
  const a = await fixture(t), b = await fixture(t);
  a.issues = [issue(21)]; b.issues = [issue(21)];
  await a.invoke('start'); await b.invoke('start');
  assert.match(a.prompts[0], /"number":21,/); assert.match(b.prompts[0], /"number":21,/);
  assert.equal(a.ack.length + b.ack.length, 0);
  assert.match(a.prompts[0], /pdd:working/);
  // The bundled skill owns the cross-machine claim; this proves separate launcher state.
});

test('native Linux and macOS user timers pin Node, script, state and environment without a shell', async t => {
  for (const platform of ['linux', 'darwin']) {
    const f = await fixture(t, {tempPrefix: 'pdd-autopilot-sh-'}); delete f.ports.timer; f.ports.platform = platform; f.ports.uid = 123;
    // Keep both platform branches independent of the host's XDG paths and user services.
    const env = { HOME: f.home, PATH: '/fixture/bin', XDG_CONFIG_HOME: join(f.home, '.config') };
    const run = f.ports.run, serviceCalls = [];
    f.ports.run = async (command, args, opts) => {
      if (['systemctl', 'launchctl', 'loginctl'].includes(command)) {
        assert.equal(opts.env.HOME, env.HOME);
        assert.equal(opts.env.XDG_CONFIG_HOME, env.XDG_CONFIG_HOME);
        serviceCalls.push([command, args]);
        return { code: 0, stdout: command === 'loginctl' ? 'yes\n' : '', stderr: '' };
      }
      return run(command, args, opts);
    };
    const started = await f.invoke('start', { env });
    assert.equal(started.exitCode, 0, started.message);
    if (platform === 'linux') {
      const folder = join(f.home, '.config', 'systemd', 'user');
      const service = readdirSync(folder).find(x => x.endsWith('.service'));
      const text = readFileSync(join(folder, service), 'utf8');
      assert.ok(text.includes(process.execPath)); assert.ok(text.includes('/src/autopilot-launcher.mjs'));
      assert.ok(text.includes(f.stateFile())); assert.match(text, /Environment="PATH=/);
      assert.match(text, /^KillMode=process$/m);
      assert.doesNotMatch(text, /^ExecStart="?(?:[^"\s]*\/)?(?:sh|bash|dash|zsh|ksh|fish)"?(?:\s|$)/m);
      assert.doesNotMatch(text, /TOKEN|API_KEY/);
      assert.match(readFileSync(join(folder, service.replace('.service', '.timer')), 'utf8'), /OnActiveSec=30min/);
      assert.deepEqual(serviceCalls.filter(([command]) => command === 'systemctl').map(([, args]) => args), [
        ['--user', 'daemon-reload'], ['--user', 'enable', service.replace('.service', '.timer')],
        ['--user', 'restart', service.replace('.service', '.timer')],
      ]);
      assert.equal(serviceCalls.some(([command]) => command === 'launchctl'), false);
    } else {
      const folder = join(f.home, 'Library', 'LaunchAgents');
      const text = readFileSync(join(folder, readdirSync(folder)[0]), 'utf8');
      assert.ok(text.includes(process.execPath)); assert.match(text, /<integer>1800<\/integer>/);
      assert.match(text, /EnvironmentVariables/); assert.ok(text.includes(f.stateFile()));
      const name = readdirSync(folder)[0];
      assert.deepEqual(serviceCalls, [
        ['launchctl', ['bootout', `gui/123/${name.slice(0, -6)}`]],
        ['launchctl', ['bootstrap', 'gui/123', join(folder, name)]],
      ]);
    }
    assert.equal((await f.invoke('stop', { env })).exitCode, 0);
    assert.equal(f.state().enabled, false);
    const definitions = platform === 'linux' ? join(f.home, '.config', 'systemd', 'user') : join(f.home, 'Library', 'LaunchAgents');
    assert.deepEqual(readdirSync(definitions), []);
  }
});

test('native HTTP tick uses ETags and revalidates cached later pages, including a close', async t => {
  const f = await fixture(t); delete f.ports.queryIssues;
  f.ports.reconcileDependencyIntake = async () => ({ eligible: [issue(31).html_url], queued: [], skipped: [] });
  let phase = 0; const queries = [];
  const run = f.ports.run;
  f.ports.run = async (command, args, opts) => {
    if (command === 'gh' && args[0] === 'api' && args.includes('--include')) {
      queries.push(args);
      const second = args[4]?.includes('page=2');
      if (phase === 0) return { code: 0, stderr: '', stdout: second
        ? `HTTP/2.0 200 OK\r\nETag: "second"\r\n\r\n${JSON.stringify([issue(31)])}`
        : 'HTTP/2.0 200 OK\r\nETag: "first"\r\nLink: <https://api.github.com/repos/owner/repo/issues?page=2>; rel="next"\r\n\r\n[]' };
      return { code: 0, stderr: '', stdout: second ? 'HTTP/2.0 200 OK\r\nETag: "closed"\r\n\r\n[]' : 'HTTP/2.0 304 Not Modified\r\n\r\n' };
    }
    return run(command, args, opts);
  };
  await f.invoke('start'); assert.match(f.prompts[0], /"number":31,/);
  // Between full reads a tick reads only changed issues (#3046); the full read 6 hours later revalidates every page.
  phase = 1; f.time += 6 * 60 * 60 * 1000; await f.tick();
  assert.equal(f.prompts.length, 1); assert.equal(f.state().cachedIssues.length, 0);
  assert.ok(queries[2].includes('If-None-Match: "first"'));
  assert.ok(queries[3].includes('If-None-Match: "second"'));
});

test('native empty 304 tick makes exactly one GitHub request and no model request', async t => {
  const f = await fixture(t); delete f.ports.queryIssues;
  const run = f.ports.run; let queries = 0;
  f.ports.run = async (command, args, opts) => {
    if (command === 'gh' && args.includes('--include')) return { code: 0, stderr: '', stdout: ++queries === 1 ? 'HTTP/2.0 200 OK\nETag: "empty"\n\n[]' : 'HTTP/2.0 304 Not Modified\n\n' };
    return run(command, args, opts);
  };
  await f.invoke('start'); await f.tick();
  assert.equal(queries, 2); assert.equal(f.prompts.length, 1);
});

test('rate limit reset is saved and no GitHub retry happens before it', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.ports.queryIssues = async () => { f.polls.push('limited'); return { status: 429, resetAt: f.time + 7200000 }; };
  await f.tick(); const polls = f.polls.length;
  await f.tick(); f.time += 1800000; await f.tick();
  assert.equal(f.polls.length, polls);
  f.time += 5400000; await f.tick(); assert.equal(f.polls.length, polls + 1);
});

test('association alone cannot admit a read-only collaborator or a forged acknowledgement', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(41, { user: { login: 'reader' }, author_association: 'COLLABORATOR', body: 'READ ONLY', comments: 1 })];
  f.issueComments = { 41: [{ user: { login: 'reader' }, author_association: 'MEMBER', body: 'thanks, a maintainer will look\n\n<!-- pdd:autopilot:thanks -->' }] };
  const run = f.ports.run;
  f.ports.run = async (cmd, args, opts) => args.some(x => String(x).endsWith('/reader/permission')) ? { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n{"permission":"read"}', stderr: '' } : run(cmd, args, opts);
  await f.tick(); assert.equal(f.prompts.length, 1); assert.equal(f.ack.length, 1);
  f.ports.run = async (cmd, args, opts) => args.some(x => String(x).endsWith('/reader/permission')) ? { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n{"permission":"write"}', stderr: '' } : run(cmd, args, opts);
  await f.tick(); assert.equal(f.prompts.length, 2); assert.match(f.prompts[1], /READ ONLY/);
});

test('native sign-in probes choose each supported interactive provider without a model call', async t => {
  for (const provider of ['codex', 'claude', 'agy', 'gemini']) {
    const f = await fixture(t); delete f.ports.selectAgent;
    if (provider === 'gemini') { mkdirSync(join(f.home, '.gemini')); writeFileSync(join(f.home, '.gemini', 'oauth_creds.json'), '{"refresh_token":"synthetic-test-token"}'); }
    const run = f.ports.run; const probes = [];
    f.ports.run = async (command, args, opts) => {
      if (['codex', 'claude', 'agy', 'gemini'].includes(command)) {
        probes.push([command, args]);
        const stdout = command === 'codex' ? 'Logged in using ChatGPT' : command === 'claude' ? '{"loggedIn":true}' : command === 'agy' ? 'default agent' : '1.0';
        return { code: command === provider ? 0 : 1, stdout: command === provider ? stdout : '', stderr: '' };
      }
      return run(command, args, opts);
    };
    assert.equal((await f.invoke('start')).exitCode, 0); assert.equal(f.state().agent.kind, provider);
    assert.ok(probes.every(([, args]) => ['login', 'auth', 'models', '--version'].includes(args[0])));
    assert.doesNotMatch(readFileSync(f.stateFile(), 'utf8'), /synthetic-test-token/);
    const launch = f.herdrCalls.find(args => args[0] === 'pane' && args[1] === 'run')[3];
    assert.doesNotMatch(launch, /\bexec\b|--print|\s-p\b/);
  }
});

test('a missing Gemini sign-in is not inferred from a successful version command', async t => {
  const f = await fixture(t); delete f.ports.selectAgent; const run = f.ports.run;
  f.ports.run = async (command, args, opts) => ['codex', 'claude', 'agy', 'gemini'].includes(command) ? { code: command === 'gemini' ? 0 : 1, stdout: 'installed', stderr: '' } : run(command, args, opts);
  const result = await f.invoke('start'); assert.equal(result.exitCode, 1); assert.match(result.message, /Sign in/);
  assert.equal(f.prompts.length, 0);
});

test('failed timer installation leaves stopped state and launches no agent', async t => {
  const f = await fixture(t); f.ports.timer = async () => { throw Error('no user bus'); };
  const result = await f.invoke('start'); assert.equal(result.exitCode, 1); assert.match(result.message, /user session/);
  assert.equal(f.state().enabled, false); assert.equal(f.prompts.length, 0);
});

test('fresh setup and mode/trust commands feed the launcher and bundled skills without a settings stub', async t => {
  const f = await fixture(t); rmSync(join(f.cwd, 'pdd.json'));
  execFileSync('git', ['init', '--quiet', f.cwd]);
  const stdout = capture(), stderr = capture();
  const env = { HOME: f.home, PATH: process.env.PATH };
  // A GitHub stub for the pdd.json copy on GitHub: no real gh runs.
  const dependencies = { cwd: f.cwd, packageRoot: root, env, stdout, stderr, autopilotGithubPorts: { github: { repository: async () => { throw Error('Tests never call GitHub'); } } } };
  assert.equal(await runPdd(['setup'], { ...dependencies, stdin: { isTTY: false },
    pathDiagnostic: () => [], workflowAgents: { checkWorkflowAgents: async () => ({ ok: true, agent: 'codex', message: '' }) }, setupAgentMcp: async () => 0 }), 0, stderr.text);
  assert.ok(readFileSync(join(f.cwd, 'AGENTS.md'), 'utf8').includes('pdd:start'));
  for (const skill of ['pdd-autopilot', 'pdd-check', 'pdd-merge']) {
    assert.equal(readFileSync(join(f.home, '.agents', 'skills', skill, 'SKILL.md'), 'utf8'), readFileSync(join(root, 'skills', skill, 'SKILL.md'), 'utf8'));
  }
  assert.equal(await runPdd(['autopilot', 'auto'], dependencies), 0, stderr.text);
  assert.equal(await runPdd(['autopilot', 'trust', 'Helper', 'helper'], dependencies), 0, stderr.text);
  const saved = readFileSync(join(f.cwd, 'pdd.json'), 'utf8');
  assert.deepEqual(JSON.parse(saved).autopilot, { mode: 'auto', trust: ['Helper'] });
  f.issues = [issue(60, { user: { login: 'helper' }, author_association: 'NONE' })];
  assert.equal(await runPdd(['autopilot', 'start'], { ...dependencies, autopilotLauncherPorts: f.ports }), 0, stderr.text);
  assert.match(f.prompts[0], /"recipeFirst":true/);
  assert.match(f.prompts[0], /"number":60,/);
  assert.ok(f.prompts[0].includes(JSON.stringify(join(root, 'skills', 'pdd-autopilot', 'SKILL.md'))));
  assert.equal(readFileSync(join(f.cwd, 'pdd.json'), 'utf8'), saved, 'Launcher settings reads must not write');
  assert.equal(await runPdd(['autopilot', 'untrust', 'HELPER'], dependencies), 0);
  await f.tick(); assert.equal(f.prompts.length, 1, 'Removed explicit trust must be reflected on the next tick');
  assert.equal(await runPdd(['autopilot', 'off'], dependencies), 0);
  const polls = f.polls.length; await f.tick(); assert.equal(f.polls.length, polls);
});

test('launcher preserves the shared settings module invalid-value notice and saved bytes', async t => {
  const f = await fixture(t);
  for (const value of ['auto', { mode: 'turbo' }]) {
    const text = JSON.stringify({ keep: true, autopilot: value });
    writeFileSync(join(f.cwd, 'pdd.json'), text);
    const result = await f.invoke('start');
    assert.equal(result.exitCode, 0); assert.match(result.message, /invalid/);
    assert.equal(readFileSync(join(f.cwd, 'pdd.json'), 'utf8'), text);
    assert.equal(f.prompts.length, 0); assert.equal(f.timers.length, 0);
  }
});

test('permission lookup rate limiting defers all work without sending the outsider reply', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(55, { user: { login: 'writer' }, author_association: 'MEMBER' }), issue(56, { user: { login: 'other' }, author_association: 'NONE' })];
  const run = f.ports.run; let permissionReads = 0;
  const resetAt = f.time + 3600000;
  f.ports.run = async (command, args, opts) => {
    if (args.some(x => String(x).endsWith('/permission'))) { permissionReads++; return { code: 1, stderr: '', stdout: `HTTP/2.0 403 Forbidden\r\nx-ratelimit-reset: ${resetAt / 1000}\r\n\r\n{"message":"API rate limit exceeded"}` }; }
    return run(command, args, opts);
  };
  await f.tick(); assert.equal(f.state().retryAt, resetAt); assert.equal(permissionReads, 1);
  assert.equal(f.ack.length, 0); assert.equal(f.prompts.length, 1);
  await f.tick(); assert.equal(permissionReads, 1);
});

test('an unavailable trust lookup does not misclassify a writer and send a reply', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(57, { user: { login: 'writer' }, author_association: 'MEMBER' })];
  const run = f.ports.run;
  f.ports.run = async (command, args, opts) => args.some(x => String(x).endsWith('/permission'))
    ? { code: 1, stderr: '', stdout: 'HTTP/2.0 503 Unavailable\r\n\r\n{}' } : run(command, args, opts);
  assert.match((await f.tick()).message, /Deferred #57:.*lookup unavailable/);
  assert.equal(f.ack.length, 0); assert.equal(f.prompts.length, 1);
});

test('a removed Herdr pane is replaced, then queued work is delivered', async t => {
  const f = await fixture(t); await f.invoke('start'); f.issues = [issue(58)];
  const herdr = f.ports.herdr; let missing = true;
  f.ports.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'get' && missing) { missing = false; throw Object.assign(Error('pane removed'), { code: 'pane_not_found' }); }
    if (args[0] === 'workspace') return { result: { workspace: { workspace_id: 'w2' }, root_pane: { pane_id: 'p2' } } };
    return herdr(args);
  };
  await f.tick(); assert.equal(f.state().paneId, 'p2');
  assert.ok(f.herdrCalls.some(args => args[0] === 'pane' && args[2] === 'p2'));
  assert.match(f.prompts.at(-1), /"number":58,/);
});

test('rate limiting on the static reply also waits for reset', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(59, { user: { login: 'outside' }, author_association: 'NONE' })];
  const run = f.ports.run; const resetAt = f.time + 3600000;
  f.ports.run = async (command, args, opts) => args.includes('POST') && args.some(x => String(x).endsWith('/comments'))
    ? { code: 1, stderr: '', stdout: `HTTP/2.0 429 Too Many Requests\r\nx-ratelimit-reset: ${resetAt / 1000}\r\n\r\n{}` } : run(command, args, opts);
  await f.tick(); assert.equal(f.state().retryAt, resetAt);
  const polls = f.polls.length; await f.tick(); assert.equal(f.polls.length, polls);
  assert.equal(f.state().acknowledged[59], undefined);
});

test('a later stop retries timer cleanup after a transient failure', async t => {
  const f = await fixture(t); await f.invoke('start');
  const timer = f.ports.timer; let attempts = 0;
  f.ports.timer = async (action, state) => { if (action === 'stop' && ++attempts === 1) throw Error('transient user bus failure'); return timer(action, state); };
  assert.equal((await f.invoke('stop')).exitCode, 1); assert.equal(f.state().enabled, false);
  assert.equal((await f.invoke('stop')).exitCode, 0); assert.equal(attempts, 2);
  assert.equal(f.state().timerInstalled, false);
});

test('claimed work wakes the skill only after a trusted change', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(61, { labels: [{ name: 'pdd:working' }] })];
  f.time += 3600000; await f.tick();
  assert.equal(f.prompts.length, 1);
  f.issues[0].body = 'Please inspect this stalled run'; await f.tick();
  assert.equal(f.prompts.length, 2);
  const packet = JSON.parse(f.prompts[1].trim().split('\n').at(-1));
  assert.equal(packet.issues[0].number, 61); assert.equal(packet.issues[0].claimed, true);
  assert.equal(packet.recipeFirst, false);
});

test('agy sign-in uses the merged non-model readiness probe, not an unsigned agent listing', async t => {
  const f = await fixture(t); delete f.ports.selectAgent; const run = f.ports.run; const probes = [];
  f.ports.run = async (command, args, opts) => {
    if (['codex', 'claude', 'agy', 'gemini'].includes(command)) {
      probes.push([command, args]);
      if (command === 'agy' && args[0] === 'agents') return { code: 0, stdout: 'default agent', stderr: '' };
      return { code: 1, stdout: '', stderr: 'Please sign in to view available models.' };
    }
    return run(command, args, opts);
  };
  const result = await f.invoke('start');
  assert.equal(result.exitCode, 1); assert.match(result.message, /Sign in/);
  assert.deepEqual(probes.filter(([command]) => command === 'agy'), [['agy', ['models']]]);
  assert.equal(f.prompts.length, 0);
});

const pr = (number, issueNumber, extra = {}) => issue(number, { pull_request: { url: `https://api.github.com/repos/owner/repo/pulls/${number}` }, body: `Fixes #${issueNumber}`, ...extra });
for (const kind of ['stuck', 'code-pending', 'own working', 'observe PR waiting']) test(`${kind}: four unchanged 304 ticks send zero prompts`, async t => {
  const f = await fixture(t, { mode: kind === 'observe PR waiting' ? 'observe' : 'auto' });
  const labels = kind === 'observe PR waiting' ? [] : [{ name: `pdd:${kind === 'own working' ? 'working' : kind}` }];
  f.issues = [issue(70, { labels })];
  if (kind === 'observe PR waiting') {
    f.issues.push(pr(90, 70));
    f.ports.pullRequest = async () => ({ state: 'open', draft: false, merged: false, head: { sha: 'a' } });
  }
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  if (kind === 'own working') f.agentStatus = 'working';
  for (let tick = 0; tick < 4; tick++) { f.time += 1800000; await f.tick(); }
  assert.equal(f.prompts.length, 0);
});

test('observe mode deduplicates an ordinary open issue until trusted changes', async t => {
  const f = await fixture(t, {mode:'observe'}); f.issues = [issue(71)]; await f.invoke('start');
  f.prompts.length = 0; f.status = 304;
  for (let tick = 0; tick < 4; tick++) await f.tick();
  assert.equal(f.prompts.length, 0);
  await f.invoke('start'); assert.equal(f.prompts.length, 0);
  f.status = 200; f.issues[0].comments = 1; f.issues[0].updated_at = '2026-11-04T01:00:00Z';
  f.issueComments = { 71: [{ id: 1, body: 'STRANGER', user: { login: 'outside' } }] };
  await f.tick(); assert.equal(f.prompts.length, 0);
  f.issues[0].comments = 2; f.issues[0].updated_at = '2026-11-04T02:00:00Z';
  f.issueComments[71].push({ id: 2, body: 'Please also handle refresh', user: { login: 'owner' } });
  await f.tick(); assert.equal(f.prompts.length, 1);
  f.status = 304; for (let tick = 0; tick < 4; tick++) await f.tick();
  assert.equal(f.prompts.length, 1);
});

test('new work stays pending while the agent is busy and is coalesced when idle', async t => {
  const f = await fixture(t); await f.invoke('start'); f.prompts.length = 0;
  f.agentStatus = 'working'; f.issues = [issue(72)];
  for (let tick = 0; tick < 4; tick++) { await f.tick(); f.status = 304; }
  assert.equal(f.prompts.length, 0);
  f.agentStatus = 'idle'; await f.tick(); assert.equal(f.prompts.length, 1);
  await f.tick(); assert.equal(f.prompts.length, 2);
});

test('trusted PR head and closure changes wake an observe issue once each', async t => {
  const f = await fixture(t, { mode: 'observe' }); f.issues = [issue(73), pr(91, 73)];
  let detail = { state: 'open', draft: false, merged: false, head: { sha: 'a' } }, queries = 0;
  f.ports.pullRequest = async () => { queries++; return detail; };
  await f.invoke('start'); f.prompts.length = 0;
  detail = { ...detail, head: { sha: 'b' } }; f.issues[1].updated_at = '2026-11-04T01:00:00Z';
  await f.tick(); assert.equal(f.prompts.length, 1);
  assert.equal(JSON.parse(f.prompts[0].trim().split('\n').at(-1)).issues[0].pullRequests[0].head, 'b');
  f.status = 304; for (let tick = 0; tick < 4; tick++) await f.tick();
  assert.equal(f.prompts.length, 1); assert.equal(queries, 2);
  f.status = 200; f.issues.pop(); detail = { ...detail, state: 'closed', merged: true };
  await f.tick(); assert.equal(f.prompts.length, 2);
  f.status = 304; await f.tick(); assert.equal(f.prompts.length, 2); assert.equal(queries, 3);
});

test('add rejects every foreign reference before mutating any label and accepts local qualified references', async t => {
  const f = await fixture(t);
  for (const ref of ['other/repo#12', 'https://github.com/other/repo/issues/12']) {
    const result = await f.invoke('add', { issues: ['15', ref] });
    assert.equal(result.exitCode, 2); assert.match(result.message, /owner\/repo/);
    assert.equal(result.message.split('\n').length, 1); assert.equal(f.ack.length, 0);
  }
  assert.equal((await f.invoke('add', { issues: ['OWNER/REPO#12', 'https://github.com/owner/repo/issues/15'] })).exitCode, 0);
  assert.equal(f.ack.length, 3);
});

test('empty and malformed owner locks do not block later ticks', async t => {
  const f = await fixture(t); await f.invoke('start'); f.issues = [issue(74)];
  for (const owner of ['', 'not-a-pid', '0', '-1']) {
    writeFileSync(f.stateFile() + '.lock', owner);
    f.issues[0].body += '!'; await f.tick();
  }
  assert.equal(f.prompts.length, 5);
});

test('a forbidden permission lookup with remaining quota defers only that issue', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(75, { user: { login: 'writer' } }), issue(76)];
  const run = f.ports.run;
  f.ports.run = async (cmd, args, opts) => args.some(x => String(x).endsWith('/writer/permission'))
    ? { code: 1, stderr: '', stdout: `HTTP/2.0 403 Forbidden\r\nx-ratelimit-remaining: 1499\r\nx-ratelimit-reset: ${f.time / 1000 + 3600}\r\n\r\n{"message":"Resource not accessible"}` } : run(cmd, args, opts);
  const result = await f.tick();
  assert.equal(f.state().retryAt, undefined); assert.match(result.message, /75/); assert.match(f.warnings[0], /75/);
  assert.match(f.prompts.at(-1), /"number":76,/); assert.doesNotMatch(f.prompts.at(-1), /"number":75,/);
});

test('Linux start warns about logout when lingering is not enabled; status detects missing Herdr', async t => {
  const f = await fixture(t); const run = f.ports.run;
  f.ports.platform = 'linux';
  f.ports.run = async (cmd, args, opts) => cmd === 'loginctl' ? { code: 0, stdout: 'no\n', stderr: '' } : run(cmd, args, opts);
  const result = await f.invoke('start'); assert.equal(result.exitCode, 0); assert.match(result.message, /loginctl enable-linger/);
  f.serverRunning = false; const status = await f.invoke('status');
  assert.doesNotMatch(status.message, /Autopilot running/); assert.match(status.message, /Herdr/);
});

test('status reports the saved coordinator state without waking it or querying GitHub', async t => {
  for (const coordinatorStatus of ['working', 'starting', 'idle', 'blocked', 'done']) {
    const f = await fixture(t); await f.invoke('start');
    f.agentStatus = coordinatorStatus;
    const polls = f.polls.length, prompts = f.prompts.length, timerCalls = f.timers.length;
    const status = await f.invoke('status');
    assert.equal(status.exitCode, 0);
    assert.match(status.message, new RegExp(`coordinator ${coordinatorStatus}`));
    assert.equal(f.polls.length, polls);
    assert.equal(f.prompts.length, prompts);
    assert.ok(f.timers.slice(timerCalls).every(([action]) => action === 'status'));
    assert.ok(f.herdrCalls.some(args => args[0] === 'agent' && args[1] === 'get'));
  }
});

test('status shows a working saved coordinator after stop without restarting or querying GitHub', async t => {
  const f = await fixture(t); await f.invoke('start'); await f.invoke('stop');
  f.agentStatus = 'working';
  const timers = f.timers.length, prompts = f.prompts.length, herdrCalls = f.herdrCalls.length;
  const gitHubCalls = f.runs.filter(([command]) => command === 'gh').length;
  const status = await f.invoke('status');
  assert.equal(status.exitCode, 0);
  assert.match(status.message, /Autopilot disabled/); assert.match(status.message, /timer inactive/);
  assert.match(status.message, /Herdr running/); assert.match(status.message, /coordinator working/);
  assert.ok(f.timers.slice(timers).every(([action]) => action === 'status'));
  assert.ok(f.herdrCalls.slice(herdrCalls).some(args => args[0] === 'agent' && args[1] === 'get'));
  assert.equal(f.runs.filter(([command]) => command === 'gh').length, gitHubCalls);
  assert.equal(f.prompts.length, prompts);
  assert.equal(f.herdrCalls.slice(herdrCalls).some(args => args[0] === 'pane' && args[1] === 'run'), false);
});

test('status shows a missing saved coordinator after stop without restarting or querying GitHub', async t => {
  const f = await fixture(t); await f.invoke('start'); await f.invoke('stop');
  f.agentStarted = false;
  const timers = f.timers.length, prompts = f.prompts.length, herdrCalls = f.herdrCalls.length;
  const gitHubCalls = f.runs.filter(([command]) => command === 'gh').length;
  const status = await f.invoke('status');
  assert.equal(status.exitCode, 0);
  assert.match(status.message, /Autopilot disabled/); assert.match(status.message, /timer inactive/);
  assert.match(status.message, /Herdr running/); assert.match(status.message, /coordinator unavailable/);
  assert.match(status.message, /missing/);
  assert.doesNotMatch(status.message, /coordinator (?:working|starting|idle|blocked|done)/);
  assert.ok(f.timers.slice(timers).every(([action]) => action === 'status'));
  assert.ok(f.herdrCalls.slice(herdrCalls).some(args => args[0] === 'agent' && args[1] === 'get'));
  assert.equal(f.runs.filter(([command]) => command === 'gh').length, gitHubCalls);
  assert.equal(f.prompts.length, prompts);
  assert.equal(f.herdrCalls.slice(herdrCalls).some(args => args[0] === 'pane' && args[1] === 'run'), false);
});

test('status does not call a live Herdr server a running repo coordinator when the saved agent is gone', async t => {
  const f = await fixture(t); await f.invoke('start'); f.agentStarted = false;
  const status = await f.invoke('status');
  assert.equal(status.exitCode, 0);
  assert.match(status.message, /coordinator unavailable \(missing\)/i);
  assert.doesNotMatch(status.message, /Autopilot running/);
});

test('status reports an unrecorded or mismatched coordinator as unavailable', async t => {
  const f = await fixture(t); await f.invoke('start');
  const state = f.state(); delete state.paneId; delete state.workspaceId;
  writeFileSync(f.stateFile(), JSON.stringify(state));
  let status = await f.invoke('status');
  assert.match(status.message, /coordinator unavailable \(not recorded\)/i);
  assert.doesNotMatch(status.message, /Autopilot running/);

  state.paneId = 'p1'; state.workspaceId = 'w1'; writeFileSync(f.stateFile(), JSON.stringify(state));
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    if (args[0] === 'agent' && args[1] === 'get') return { result: { type: 'agent_info', agent: {
      pane_id: 'p1', workspace_id: 'w1', cwd: join(f.dir, 'other-repo'), agent: 'codex', agent_status: 'idle'
    } } };
    return herdr(args);
  };
  status = await f.invoke('status');
  assert.match(status.message, /coordinator unavailable \(saved target does not match\)/i);
  assert.doesNotMatch(status.message, /Autopilot running/);
});

test('macOS start does not check Linux lingering or warn about loginctl', async t => {
  const f = await fixture(t); const run = f.ports.run;
  f.ports.platform = 'darwin';
  let lingerChecks = 0;
  f.ports.run = async (cmd, args, opts) => {
    if (cmd === 'loginctl') { lingerChecks++; return { code: 0, stdout: 'no\n', stderr: '' }; }
    return run(cmd, args, opts);
  };
  const result = await f.invoke('start');
  assert.equal(result.exitCode, 0); assert.equal(lingerChecks, 0);
  assert.doesNotMatch(result.message, /loginctl enable-linger/);
});

test('overlapping ticks cannot deliver twice from a snapshot read before lock acquisition', async t => {
  const f = await fixture(t); await f.invoke('start'); f.prompts.length = 0; f.issues = [issue(77)];
  // Keep the existing native-operation barrier separate from optional telemetry lookup.
  f.ports.metricsContext = async () => ({toplevel:f.cwd,commonDir:f.cwd});
  const query = f.ports.queryIssues; let reads = 0, release;
  f.ports.queryIssues = async state => {
    if (++reads === 2) await new Promise(resolve => { release = resolve; });
    return query(state);
  };
  const first = f.tick(), second = f.tick(); await first; release?.(); await second;
  assert.equal(f.prompts.length, 1);
  f.prompts.length = 0;
  let entered, unblock, resume;
  const enteredScan = new Promise(resolve => { entered = resolve; });
  f.ports.queryIssues = async state => { entered(); await new Promise(resolve => { unblock = resolve; }); return query(state); };
  f.ports.armStartScan = (_identity, options) => { resume = options.resume; };
  f.ports.waitForScan = async () => {};
  const oldScan = f.tick(); await enteredScan;
  assert.equal((await f.invoke('start')).exitCode, 0); assert.equal(typeof resume, 'function');
  assert.equal(f.prompts.length, 0); unblock(); await oldScan;
  f.ports.queryIssues = query; await resume();
  assert.equal(f.prompts.length, 1); assert.match(f.prompts[0], /\"number\":77,/);
});

test('trusted PR comments wake a waiting issue once; outsider PR comments stay quiet', async t => {
  const f = await fixture(t, { mode: 'observe' }); f.issues = [issue(78), pr(92, 78)];
  f.ports.pullRequest = async () => ({ state: 'open', head: { sha: 'a' } });
  await f.invoke('start'); f.prompts.length = 0;
  f.issues[1].comments = 1; f.issues[1].updated_at = '2026-11-04T01:00:00Z';
  f.issueComments = { 92: [{ id: 1, body: 'STRANGER PR COMMENT', user: { login: 'outside' } }] };
  await f.tick(); assert.equal(f.prompts.length, 0);
  f.issues[1].comments = 2; f.issues[1].updated_at = '2026-11-04T02:00:00Z';
  f.issueComments[92].push({ id: 2, body: 'Please revise the timeout', user: { login: 'owner' } });
  await f.tick(); assert.equal(f.prompts.length, 1);
  assert.match(f.prompts[0], /Please revise the timeout/); assert.doesNotMatch(f.prompts[0], /STRANGER PR COMMENT/);
  f.status = 304; for (let tick = 0; tick < 4; tick++) await f.tick();
  assert.equal(f.prompts.length, 1);
});

test('a forbidden issue query with quota remaining has no rate-limit cooldown', async t => {
  const f = await fixture(t); await f.invoke('start'); delete f.ports.queryIssues;
  const run = f.ports.run;
  f.ports.run = async (cmd, args, opts) => cmd === 'gh' && args.some(x => String(x).includes('/issues?'))
    ? { code: 1, stderr: '', stdout: `HTTP/2.0 403 Forbidden\r\nx-ratelimit-remaining: 1499\r\nx-ratelimit-reset: ${f.time / 1000 + 3600}\r\n\r\n{"message":"Resource not accessible"}` } : run(cmd, args, opts);
  await assert.rejects(f.tick(), /GitHub issue check failed/);
  assert.equal(f.state().retryAt, undefined);
});

test('a zero-remaining 403 defers until reset even without a rate-limit message', async t => {
  const f = await fixture(t); await f.invoke('start'); f.issues = [issue(79, { user: { login: 'writer' } })];
  const run = f.ports.run, resetAt = f.time + 3600000;
  f.ports.run = async (cmd, args, opts) => args.some(x => String(x).endsWith('/writer/permission'))
    ? { code: 1, stderr: '', stdout: `HTTP/2.0 403 Forbidden\r\nx-ratelimit-remaining: 0\r\nx-ratelimit-reset: ${resetAt / 1000}\r\n\r\n{"message":"Forbidden"}` } : run(cmd, args, opts);
  await f.tick(); assert.equal(f.state().retryAt, resetAt);
});

test('a live lock owner still excludes another tick', async t => {
  const f = await fixture(t); await f.invoke('start'); const polls = f.polls.length;
  writeFileSync(f.stateFile() + '.lock', String(process.pid));
  assert.match((await f.tick()).message, /already running/); assert.equal(f.polls.length, polls);
});

test('native related PR metadata is fetched once and cached across unchanged ticks', async t => {
  const f = await fixture(t, { mode: 'observe' }); f.issues = [issue(80), pr(93, 80)];
  const run = f.ports.run; let reads = 0;
  f.ports.run = async (cmd, args, opts) => {
    if (cmd === 'gh' && args.includes('repos/owner/repo/pulls/93')) {
      reads++; assert.ok(args.includes('GET'));
      return { code: 0, stderr: '', stdout: 'HTTP/2.0 200 OK\r\n\r\n{"state":"open","draft":false,"head":{"sha":"a"}}' };
    }
    return run(cmd, args, opts);
  };
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  for (let tick = 0; tick < 4; tick++) await f.tick();
  assert.equal(reads, 1); assert.equal(f.prompts.length, 0);
});

test('cached PR comments are revalidated after explicit trust or write access is revoked', async t => {
  for (const authority of ['explicit', 'write']) {
    const f = await fixture(t, { mode: 'observe' }); f.issues = [issue(81), pr(94, 81, { comments: 1 })];
    f.issueComments = { 94: [{ id: 1, body: 'REVOKED COMMENT', user: { login: 'helper' } }] };
    f.ports.pullRequest = async () => ({ state: 'open', head: { sha: 'a' } });
    let permission = 'write'; const run = f.ports.run;
    if (authority === 'write') {
      writeFileSync(join(f.cwd, 'pdd.json'), '{"autopilot":{"mode":"observe","trust":[]}}');
      f.ports.run = async (cmd, args, opts) => args.some(x => String(x).endsWith('/helper/permission'))
        ? { code: 0, stderr: '', stdout: `HTTP/2.0 200 OK\r\n\r\n{"permission":"${permission}"}` } : run(cmd, args, opts);
    }
    await f.invoke('start'); f.prompts.length = 0;
    if (authority === 'explicit') writeFileSync(join(f.cwd, 'pdd.json'), '{"autopilot":{"mode":"observe","trust":[]}}');
    else permission = 'read';
    f.issues[0].body = 'New instruction from the owner'; await f.tick();
    assert.equal(f.prompts.length, 1); assert.match(f.prompts[0], /New instruction from the owner/);
    assert.doesNotMatch(f.prompts[0], /REVOKED COMMENT/);
  }
});

test('trust removal and outsider-only updates stay quiet for issue and PR discussions', async t => {
  for (const channel of ['issue', 'PR']) {
    const f = await fixture(t, { mode: channel === 'PR' ? 'observe' : 'auto' });
    f.issues = [issue(82, { comments: channel === 'issue' ? 1 : 0 })];
    const number = channel === 'PR' ? 95 : 82;
    if (channel === 'PR') { f.issues.push(pr(95, 82, { comments: 1 })); f.ports.pullRequest = async () => ({ state: 'open', head: { sha: 'a' } }); }
    f.issueComments = { [number]: [{ id: 1, body: 'REVOKED TEXT', user: { login: 'helper' } }] };
    await f.invoke('start'); f.prompts.length = 0;
    writeFileSync(join(f.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: channel === 'PR' ? 'observe' : 'auto', trust: [] } }));
    const run = f.ports.run; let permissions = 0;
    f.ports.run = async (cmd, args, opts) => { if (args.some(x => String(x).endsWith('/permission'))) permissions++; return run(cmd, args, opts); };
    f.status = 304; for (let tick = 0; tick < 4; tick++) await f.tick();
    if (channel === 'PR') { assert.equal(f.prompts.length, 0); assert.equal(permissions, 0, 'Quiet ticks must not refresh cached permissions'); }
    else { assert.equal(f.prompts.length, 4); for (const packet of f.prompts) assert.doesNotMatch(packet, /REVOKED TEXT/); f.prompts.length = 0; }
    f.status = 200; const changed = f.issues.find(x => x.number === number); changed.comments = 2; changed.updated_at = '2026-11-04T01:00:00Z';
    f.issueComments[number].push({ id: 2, body: 'OUTSIDER ONLY', user: { login: 'outside' } });
    await f.tick(); if (channel === 'PR') assert.equal(f.prompts.length, 0); else { assert.equal(f.prompts.length, 1); assert.doesNotMatch(f.prompts[0], /REVOKED TEXT|OUTSIDER ONLY/); f.prompts.length = 0; }
    changed.comments = 3; changed.updated_at = '2026-11-04T02:00:00Z';
    f.issueComments[number].push({ id: 3, body: 'New owner feedback', user: { login: 'owner' } });
    await f.tick(); assert.equal(f.prompts.length, 1);
    assert.match(f.prompts[0], /New owner feedback/); assert.doesNotMatch(f.prompts[0], /REVOKED TEXT|OUTSIDER ONLY/);
  }
});

test('revoking a PR author does not make its unchanged waiting issue newly actionable', async t => {
  const f = await fixture(t, { mode: 'observe' });
  f.issues = [issue(83), pr(96, 83, { user: { login: 'helper' } })];
  f.ports.pullRequest = async () => ({ state: 'open', head: { sha: 'a' } });
  await f.invoke('start'); f.prompts.length = 0;
  writeFileSync(join(f.cwd, 'pdd.json'), '{"autopilot":{"mode":"observe","trust":[]}}');
  f.issues[1].comments = 1; f.issues[1].updated_at = '2026-11-04T01:00:00Z';
  f.issueComments = { 96: [{ id: 1, body: 'OUTSIDER ONLY', user: { login: 'outside' } }] };
  await f.tick(); assert.equal(f.prompts.length, 0);
});

for (const change of ['unclaim with waiting PR', 'auto with stuck issue']) test(`${change} does not wake an issue that still waits`, async t => {
  const f = await fixture(t, { mode: 'observe' });
  f.issues = [issue(84, { labels: [{ name: change.startsWith('unclaim') ? 'pdd:working' : 'pdd:stuck' }] }), pr(97, 84)];
  f.ports.pullRequest = async () => ({ state: 'open', head: { sha: 'a' } });
  f.ports.reconcileDependencyIntake = async () => ({ eligible: [], queued: [], skipped: [] });
  await f.invoke('start'); f.prompts.length = 0;
  if (change.startsWith('unclaim')) f.issues[0].labels = [];
  else writeFileSync(join(f.cwd, 'pdd.json'), '{"autopilot":{"mode":"auto","trust":[]}}');
  for (let tick = 0; tick < 4; tick++) await f.tick();
  assert.equal(f.prompts.length, 0);
});

const packet = f => JSON.parse(f.prompts.at(-1).trim().split('\n').at(-1));
const hour = 60 * 60 * 1000;

for (const rule of ['run', 'claim']) test(`time rule: ${rule} wakes once at 60 minutes and a later activity can become due again`, async t => {
  const f = await fixture(t); const changedAt = f.time;
  if (rule === 'run') f.runProgress = [{ number: 101, changedAt }];
  else f.issues = [issue(101, { labels: [{ name: 'pdd:working' }], updated_at: new Date(changedAt).toISOString() })];
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  f.time = changedAt + hour - 1; await f.tick(); assert.equal(f.prompts.length, 0);
  f.time++; await f.tick(); assert.equal(f.prompts.length, 1);
  const event = packet(f).timeRules[0];
  assert.equal(event.number, 101);
  assert.equal(event.reason.split('\n').length, 1);
  assert.match(event.reason, rule === 'run' ? /no progress.*60 minutes.*pdd:stuck/ : /pdd:working.*about 1 hour.*takeover/);
  if (rule === 'claim') assert.equal(packet(f).issues[0].claimed, true);
  for (let i = 0; i < 3; i++) { f.time += hour; await f.tick(); }
  await f.invoke('stop'); await f.invoke('start');
  assert.equal(f.prompts.length, 1, 'An unchanged due event stays consumed across restart');
  const refreshedAt = f.time;
  if (rule === 'run') f.runProgress[0].changedAt = refreshedAt;
  else { f.status = 200; f.issues[0].updated_at = new Date(refreshedAt).toISOString(); }
  await f.tick(); const count = f.prompts.length;
  f.time += hour - 1; await f.tick(); assert.equal(f.prompts.length, count);
  f.time++; await f.tick(); assert.equal(f.prompts.length, count + 1);
  await f.tick(); assert.equal(f.prompts.length, count + 1);
});

for (const status of ['working', 'blocked', 'unknown']) test(`time rules stay pending while ${status} and coalesce when idle`, async t => {
  const f = await fixture(t); const changedAt = f.time;
  f.runProgress = [{ number: 102, changedAt }];
  f.issues = [issue(103, { labels: [{ name: 'pdd:working' }], updated_at: new Date(changedAt).toISOString() })];
  await f.invoke('start'); f.prompts.length = 0; f.status = 304; f.agentStatus = status;
  f.time += hour;
  for (let i = 0; i < 3; i++) await f.tick();
  assert.equal(f.prompts.length, 0);
  f.agentStatus = 'idle'; await f.tick();
  assert.equal(f.prompts.length, 1);
  assert.deepEqual(packet(f).timeRules.map(event => event.number).sort(), [102, 103]);
  await f.tick(); assert.equal(f.prompts.length, 1);
});

test('time rules retry failed delivery and discard refreshed pending events', async t => {
  const f = await fixture(t); const changedAt = f.time;
  f.runProgress = [{ number: 104, changedAt }];
  await f.invoke('start'); f.prompts.length = 0; f.status = 304; f.time += hour;
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => { if (args[0] === 'agent' && args[1] === 'prompt') throw Error('delivery failed'); return herdr(args); };
  await assert.rejects(f.tick(), /delivery failed/);
  f.ports.herdr = herdr; await f.tick(); assert.equal(f.prompts.length, 1);
  f.runProgress[0].changedAt = f.time; f.time += hour; f.agentStatus = 'working'; await f.tick();
  f.runProgress[0].changedAt = f.time; f.agentStatus = 'idle'; await f.tick();
  assert.equal(f.prompts.length, 1, 'Progress while busy cancels the old due event');
  f.time += hour; await f.tick(); assert.equal(f.prompts.length, 2);
});

test('time rule uses cached comment activity and never adds a GitHub query on unchanged ticks', async t => {
  const f = await fixture(t); const changedAt = f.time;
  f.issues = [issue(105, { labels: [{ name: 'pdd:working' }], comments: 1, updated_at: new Date(changedAt).toISOString() })];
  f.issueComments = { 105: [{ id: 1, body: 'Claim refreshed on this machine', user: { login: 'owner' }, created_at: new Date(changedAt).toISOString(), updated_at: new Date(changedAt + hour / 2).toISOString() }] };
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  const processes = f.runs.length, commentReads = f.comments.length;
  f.time += hour; await f.tick(); assert.equal(f.prompts.length, 0);
  f.time += hour / 2; await f.tick(); assert.equal(f.prompts.length, 1);
  await f.tick(); assert.equal(f.prompts.length, 1);
  assert.equal(f.comments.length, commentReads);
  assert.ok(f.runs.slice(processes).every(([command,args]) => command === 'git' || command === 'herdr' && JSON.stringify(args) === JSON.stringify(['--session','pdd','pane','list'])), 'No extra network or model process');
});

test('time rule revalidates trust on a cached due claim without forwarding stranger text', async t => {
  const f = await fixture(t);
  f.issues = [issue(106, { title: 'REVOKED TITLE', body: 'REVOKED BODY', user: { login: 'helper' }, labels: [{ name: 'pdd:working' }], updated_at: new Date(f.time).toISOString() })];
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  writeFileSync(join(f.cwd, 'pdd.json'), '{"autopilot":{"mode":"auto","trust":[]}}');
  f.time += hour; await f.tick(); assert.equal(f.prompts.length, 0);
});

test('time rules read active status file modification times from the Git common directory', async t => {
  const f = await fixture(t); delete f.ports.readRunProgress;
  f.ports.env = {HOME: f.home, PDD_SUITE_QUEUE: join(f.dir, 'suite-queue'), PDD_INTERPRETER_QUEUE: join(f.dir, 'interpreter-queue')};
  const invoke = f.invoke;
  f.invoke = (command, extra = {}) => invoke(command, {env: f.ports.env, ...extra});
  const changedAt = f.time;
  // A foreign finished ticket must not hide this checkout's progress.
  mkdirSync(f.ports.env.PDD_SUITE_QUEUE, { recursive: true });
  writeFileSync(join(f.ports.env.PDD_SUITE_QUEUE, 'ticket-1.json'), JSON.stringify({
    ticket: 1, pid: process.pid, cwd: join(f.dir, 'unrelated'), state: 'finished',
    queuedAt: changedAt - hour, startedAt: changedAt - hour, finishedAt: changedAt - 1, reason: null,
  }));
  const record = (number, state = 'running', repo = 'owner/repo') => {
    const folder = join(f.cwd, '.git', 'pdd', 'runs', String(number)); mkdirSync(folder, { recursive: true });
    const file = join(folder, 'status.json');
    writeFileSync(file, JSON.stringify({ v: 1, number, repo, root: join(f.dir, `run-${number}`), state, updatedAt: changedAt - hour }));
    utimesSync(file, new Date(changedAt), new Date(changedAt));
    return file;
  };
  const active = record(107); record(108, 'completed'); record(109, 'cancelled'); record(110, 'running', 'owner/other');
  const broken = record(111); writeFileSync(broken, 'incomplete');
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  f.time += hour - 1; await f.tick(); assert.equal(f.prompts.length, 0, 'Use file change time, not stale embedded metadata');
  f.time++; await f.tick(); assert.equal(f.prompts.length, 1);
  assert.deepEqual(packet(f).timeRules.map(event => event.number), [107]);
  await f.tick(); assert.equal(f.prompts.length, 1);
  f.agentStatus = 'working'; utimesSync(active, new Date(f.time), new Date(f.time)); f.time += hour; await f.tick();
  writeFileSync(active, JSON.stringify({ v: 1, number: 107, repo: 'owner/repo', state: 'completed' }));
  f.agentStatus = 'idle'; await f.tick(); assert.equal(f.prompts.length, 1);
});

test('an unchanged empty tick with no local progress or usage data still sends zero prompts', async t => {
  const f = await fixture(t); await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  for (let i = 0; i < 4; i++) { f.time += hour; await f.tick(); }
  assert.equal(f.prompts.length, 0);
});

test('a claim with no readable activity time never invents a due event', async t => {
  const f = await fixture(t);
  f.issues = [issue(112, { labels: [{ name: 'pdd:working' }], updated_at: undefined })];
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  for (let i = 0; i < 3; i++) { f.time += hour; await f.tick(); }
  assert.equal(f.prompts.length, 0);
});

// Issue 3037: a coordinator chat keeps the launch settings it started with, so a chat that this package
// would launch differently is relaunched at an idle moment. A stateful fake of the Herdr calls the
// launcher makes: each workspace holds one pane, and `pane close` ends that pane, as Herdr 0.9.1 does
// for the only pane of a workspace. `pane run` runs the launch text in /bin/sh with a fake codex
// that records the arguments it gets. No live Herdr, agent, GitHub or model call.
// With `shellStartup`, a `cd` in the person's shell startup file (issue 2903) puts each new pane's shell in
// `f.elsewhere`. Then `pane run` runs the line in that shell's folder, the shell keeps the folder that the line
// leaves it in, and Herdr reports the shell's folder as `cwd` and the agent's folder as `foreground_cwd`, as Herdr 0.9.1 does.
async function relaunchFixture(t, options = {}) {
  const f = await fixture(t, options);
  const bin = join(f.dir, 'bin'), record = join(f.dir, 'codex.jsonl'), folders = join(f.dir, 'codex-cwd.txt');
  mkdirSync(bin);
  writeFileSync(join(bin, 'codex'), `#!${process.execPath}\nconst fs = require('node:fs'); fs.appendFileSync(${JSON.stringify(record)}, JSON.stringify(process.argv.slice(2))+'\\n'); fs.appendFileSync(${JSON.stringify(folders)}, process.cwd()+'\\n');\n`, { mode: 0o755 });
  const lines = file => existsSync(file) ? readFileSync(file, 'utf8').trim().split('\n') : [];
  if (options.shellStartup) { f.elsewhere = join(f.dir, 'elsewhere'); mkdirSync(f.elsewhere); }
  f.env = { HOME: f.home, PATH: `${bin}:/usr/bin:/bin` };
  f.invoke = async (command, extra = {}) => f.module.runAutopilotLauncher({ command, cwd: f.cwd, env: f.env, packageRoot: root, issues: [], ...extra }, f.ports);
  const panes = new Map(); let workspaces = 0;
  f.launches = []; f.closed = []; f.delivered = []; f.armed = [];
  f.ports.armWorkerCompletion = identity => f.armed.push(identity);
  f.ports.allRuns = () => f.savedRuns ?? [];
  const missing = (code, id) => Object.assign(Error(`${id} not found`), { code, confirmedRejection: true });
  f.ports.herdr = async args => {
    f.herdrCalls ??= []; f.herdrCalls.push(args);
    const [group, action, id] = args;
    if (group === 'status') return { running: true };
    if (group === 'pane' && action === 'list') return {result:{type:'pane_list',panes:[...panes.values()].filter(p=>!p.closed)}};
    if (group === 'workspace' && action === 'create') {
      const n = ++workspaces, pane = { pane_id: `w${n}:p1`, workspace_id: `w${n}`, tab_id: `w${n}:t1`, terminal_id: `term${n}`, session: `session-${n}`, agent: false, closed: false, shell: f.elsewhere ?? null, agentCwd: null };
      panes.set(pane.pane_id, pane);
      return { id: 'cli:workspace:create', result: { type: 'workspace_created', workspace: { workspace_id: pane.workspace_id }, root_pane: { pane_id: pane.pane_id } } };
    }
    const pane = panes.get(id);
    if (!pane || pane.closed) throw missing(group === 'agent' ? 'agent_not_found' : 'pane_not_found', id);
    const live = { pane_id: pane.pane_id, workspace_id: pane.workspace_id, cwd: pane.shell ?? f.cwd, foreground_cwd: pane.agentCwd ?? pane.shell ?? f.cwd, tab_id: pane.tab_id, terminal_id: pane.terminal_id, agent: 'codex', agent_status: f.agentStatus ?? 'idle', agent_session: pane.session };
    if (group === 'pane' && action === 'get') return { result: { type: 'pane_info', pane: live } };
    if (group === 'agent' && action === 'get') { if (!pane.agent) throw missing('agent_not_found', id); return { result: { type: 'agent_info', agent: live } }; }
    if (group === 'pane' && action === 'run') {
      const before = lines(record).length;
      if (pane.shell) {
        const pwd = join(f.dir, 'shell-pwd.txt');
        execFileSync('/bin/sh', ['-c', `${args[3]}\nprintf '%s' "$PWD" > ${JSON.stringify(pwd)}`], { cwd: pane.shell, env: { PATH: '/usr/bin:/bin', HOME: f.home }, timeout: 10000 });
        pane.shell = readFileSync(pwd, 'utf8');
        if (lines(record).length === before) return {};
        pane.agentCwd = lines(folders)[before];
      } else execFileSync('/bin/sh', ['-c', args[3]], { cwd: f.cwd, env: { PATH: '/usr/bin:/bin', HOME: f.home }, timeout: 10000 });
      pane.agent = true; f.launches.push({ pane: id, argv: JSON.parse(lines(record)[before]) });
      return {};
    }
    if (group === 'pane' && action === 'close') { pane.closed = true; f.closed.push(id); return { id: 'cli:pane:close', result: { type: 'ok' } }; }
    if (group === 'pane' && action === 'read') return '';
    if (group === 'agent' && action === 'prompt') {
      const instruction = args.at(-1), match = /Artifact path: (.+)/.exec(instruction);
      f.prompts.push(match ? readFileSync(JSON.parse(match[1]), 'utf8') : instruction); f.delivered.push(id);
      return {};
    }
    return {};
  };
  f.panes = panes;
  f.live = () => [...panes.values()].filter(pane => pane.agent && !pane.closed).map(pane => pane.pane_id);
  f.packet = (index = -1) => JSON.parse(f.prompts.at(index).trimEnd().split('\n').at(-1));
  f.context = launch => JSON.parse(codexConfigs(launch.argv).set.PDD_AUTOPILOT_CONTEXT);
  f.saveState = change => { const state = f.state(); change(state); writeFileSync(f.stateFile(), JSON.stringify(state)); };
  f.githubWrites = () => f.runs.filter(([command, args]) => command === 'gh' && args.some((value, i) => args[i - 1] === '--method' && value !== 'GET'));
  return f;
}
const herdrSince = (f, from, group, action) => f.herdrCalls.slice(from).filter(args => args[0] === group && args[1] === action);

test('relaunch: an idle chat launched without a launch fingerprint is replaced with current arguments; claims stay', async t => {
  const f = await relaunchFixture(t);
  f.issues = [issue(64, { labels: [{ name: 'pdd:working' }] })];
  assert.equal((await f.invoke('start')).exitCode, 0);
  const original = f.state();
  f.savedRuns = [{ runId: 'run-64', number: 64, repo: 'owner/repo', state: 'running', sourceRoot: f.cwd, automaticOrigin: { repository: 'owner/repo', coordinatorId: original.coordinatorId, machine: original.machine, claim: { commentId: '11', labelEventId: '12' } }, areas: [{ name: 'code' }], area: 0, chats: [{ area: 'code', paneId: 'worker-pane', startedAt: 5 }] }];
  // A chat that an older package launched has no saved fingerprint.
  f.saveState(state => { delete state.ownerLaunch.fingerprint; });
  const calls = f.herdrCalls.length, writes = f.githubWrites().length, prompts = f.prompts.length;
  f.status = 304; f.time += 60 * 1000; await f.tick();
  assert.deepEqual(f.closed, ['w1:p1'], 'only the saved coordinator pane is closed');
  assert.deepEqual(herdrSince(f, calls, 'pane', 'run').map(args => args[2]), ['w2:p1']);
  const after = f.state();
  assert.equal(after.paneId, 'w2:p1'); assert.equal(after.workspaceId, 'w2');
  assert.equal(after.coordinatorId, original.coordinatorId, 'claims stay with the same coordinator');
  assert.equal(after.machine, original.machine); assert.equal(after.activatedAt, original.activatedAt);
  assert.deepEqual(after.seen, original.seen, 'saved progress stays');
  assert.equal(typeof after.ownerLaunch.fingerprint, 'string');
  assert.equal(after.ownerLaunch.paneId, 'w2:p1');
  assert.deepEqual(f.context(f.launches.at(-1)), { version: 'pdd.autopilot-coordinator.v1', repository: 'owner/repo', coordinatorId: original.coordinatorId, machine: original.machine, activation: original.activatedAt });
  assert.equal(f.prompts.length, prompts + 1); assert.equal(f.delivered.at(-1), 'w2:p1');
  assert.equal(f.packet().recipeFirst, true, 'the fresh chat gets the start-up recipe');
  assert.equal(f.githubWrites().length, writes, 'no claim label or comment changes');
  assert.equal(f.armed.at(-1).coordinatorPaneId, 'w2:p1', 'worker completion follows the fresh coordinator pane');
  const quiet = f.herdrCalls.length; await f.tick(); await f.tick();
  assert.equal(herdrSince(f, quiet, 'pane', 'close').length, 0); assert.equal(herdrSince(f, quiet, 'pane', 'run').length, 0);
  assert.equal(f.prompts.length, prompts + 1);
});

test('relaunch: a working chat with another fingerprint gets no input; status shows the pending relaunch until it is idle', async t => {
  const f = await relaunchFixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  const original = f.state();
  f.saveState(state => { state.ownerLaunch.fingerprint = 'launched-by-another-package'; });
  f.agentStatus = 'working'; f.issues = [issue(72)];
  const calls = f.herdrCalls.length, prompts = f.prompts.length;
  for (let tick = 0; tick < 2; tick++) { await f.tick(); f.status = 304; }
  assert.equal(f.prompts.length, prompts, 'no input reaches the working chat');
  assert.equal(herdrSince(f, calls, 'agent', 'prompt').length, 0);
  assert.equal(herdrSince(f, calls, 'pane', 'close').length, 0, 'a working turn is never interrupted');
  assert.equal(herdrSince(f, calls, 'pane', 'run').length, 0);
  assert.equal(f.state().paneId, 'w1:p1');
  const pending = await f.invoke('status');
  assert.equal(pending.exitCode, 0);
  assert.match(pending.message, /coordinator working/);
  assert.equal(pending.message.split('\n').filter(text => /^Coordinator relaunch pending after upgrade/.test(text)).length, 1, pending.message);
  f.agentStatus = 'idle'; await f.tick();
  assert.deepEqual(f.closed, ['w1:p1']);
  assert.equal(f.state().paneId, 'w2:p1'); assert.equal(f.state().coordinatorId, original.coordinatorId);
  assert.equal(f.delivered.at(-1), 'w2:p1');
  assert.match(f.prompts.at(-1), /"number":72,/, 'pending work reaches the fresh chat');
  assert.ok(Object.hasOwn(codexConfigs(f.launches.at(-1).argv).set, 'PDD_AUTOPILOT_CONTEXT'));
  const done = await f.invoke('status');
  assert.doesNotMatch(done.message, /relaunch pending/);
});

test('relaunch: a chat with the current fingerprint is reused across ticks and an ordinary restart', async t => {
  const f = await relaunchFixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  const launch = f.state().ownerLaunch;
  assert.equal(typeof launch.fingerprint, 'string');
  f.status = 304; await f.tick(); await f.tick();
  f.issues = [issue(81)]; f.status = 200; await f.tick();
  assert.equal(f.delivered.at(-1), 'w1:p1'); assert.match(f.prompts.at(-1), /"number":81,/);
  // Another caller PATH at start and the timer's saved environment are ordinary.
  assert.equal((await f.invoke('stop')).exitCode, 0);
  f.env = { ...f.env, PATH: `${f.env.PATH}:${join(f.dir, 'elsewhere')}` };
  assert.equal((await f.invoke('start')).exitCode, 0);
  f.status = 304; await f.tick();
  assert.equal(f.closed.length, 0);
  assert.equal(f.launches.length, 1, 'one native launch');
  assert.deepEqual(f.state().ownerLaunch, launch);
  assert.doesNotMatch((await f.invoke('status')).message, /relaunch pending/);
});

test('relaunch: the fingerprint covers an explicit CODEX_HOME launch argument and stays the same across ticks and a restart', async t => {
  const f = await relaunchFixture(t);
  const profile = join(f.home, "codex 'profile'"); mkdirSync(profile);
  f.env = { ...f.env, CODEX_HOME: profile };
  assert.equal((await f.invoke('start')).exitCode, 0);
  const state = f.state(), launch = state.ownerLaunch;
  assert.equal(state.environment.CODEX_HOME, profile);
  assert.equal(launch.fingerprint, f.module.autopilotLaunchFingerprint(state));
  const { CODEX_HOME, ...withoutProfile } = state.environment;
  assert.notEqual(launch.fingerprint, f.module.autopilotLaunchFingerprint({ ...state, environment: withoutProfile }), 'the CODEX_HOME argument is in the fingerprint');
  f.status = 304; await f.tick(); await f.tick();
  f.issues = [issue(82)]; f.status = 200; await f.tick();
  assert.equal(f.delivered.at(-1), 'w1:p1');
  assert.equal((await f.invoke('stop')).exitCode, 0);
  assert.equal((await f.invoke('start')).exitCode, 0);
  f.status = 304; await f.tick();
  assert.equal(f.closed.length, 0);
  assert.equal(f.launches.length, 1, 'one native launch');
  assert.deepEqual(f.state().ownerLaunch, launch);
});

test('relaunch: stop and start with an upgraded package gives the fresh chat the context override', async t => {
  const f = await relaunchFixture(t);
  const older = join(f.dir, 'pdd-older');
  mkdirSync(older); writeFileSync(join(older, 'package.json'), JSON.stringify({ name: 'pdd', version: '0.0.1' }));
  assert.equal((await f.invoke('start', { packageRoot: older })).exitCode, 0);
  const original = f.state();
  assert.equal(original.paneId, 'w1:p1'); assert.equal(f.launches.length, 1);
  assert.equal((await f.invoke('stop')).exitCode, 0);
  const started = await f.invoke('start');
  assert.equal(started.exitCode, 0, started.message);
  assert.deepEqual(f.closed, ['w1:p1']);
  assert.equal(f.launches.length, 2); assert.equal(f.launches[1].pane, 'w2:p1');
  const { set } = codexConfigs(f.launches[1].argv);
  assert.ok(Object.hasOwn(set, 'PDD_AUTOPILOT_CONTEXT'), `fresh chat argv: ${JSON.stringify(f.launches[1].argv)}`);
  assert.deepEqual(JSON.parse(set.PDD_AUTOPILOT_CONTEXT), { version: 'pdd.autopilot-coordinator.v1', repository: 'owner/repo', coordinatorId: original.coordinatorId, machine: original.machine, activation: original.activatedAt });
  const after = f.state();
  assert.equal(after.coordinatorId, original.coordinatorId); assert.equal(after.packageRoot, root);
  assert.equal(f.delivered.at(-1), 'w2:p1');
  assert.ok(f.prompts.at(-1).includes(JSON.stringify(join(root, 'skills', 'pdd-autopilot', 'SKILL.md'))), 'the fresh chat reads the upgraded skill');
  assert.equal(f.packet().recipeFirst, true);
});

// Issue 3037 review M1: a failure after the relaunch `pane close` leaves the saved state naming the
// closed pane. Herdr answers `agent_not_found` for that pane, so only `pane get` shows that it is gone.
// Each case stops the relaunch at one point after the close; a later tick or start must replace the pane.
const afterClose = {
  'a Herdr error': f => {
    const real = f.ports.herdr; let closed = false;
    f.ports.herdr = async args => {
      if (closed && args[0] === 'pane' && args[1] === 'get') { closed = false; throw Object.assign(Error('Herdr timed out'), { code: 'timeout' }); }
      const reply = await real(args);
      if (args[0] === 'pane' && args[1] === 'close') closed = true;
      return reply;
    };
    return () => { f.ports.herdr = real; };
  },
  'a failed state save': f => {
    // The state file is a folder for the one save after the close, so that save fails.
    const real = f.ports.herdr, warn = f.ports.warn, file = f.stateFile(), aside = `${file}.aside`; let closed = false, swapped = false;
    f.ports.herdr = async args => {
      if (closed && args[0] === 'pane' && args[1] === 'get') { closed = false; renameSync(file, aside); mkdirSync(file); swapped = true; }
      const reply = await real(args);
      if (args[0] === 'pane' && args[1] === 'close') closed = true;
      return reply;
    };
    f.ports.warn = text => { if (swapped) { rmSync(file, { recursive: true }); renameSync(aside, file); swapped = false; } warn(text); };
    return () => { assert.equal(swapped, false); f.ports.herdr = real; f.ports.warn = warn; };
  },
  'a process end': f => {
    // Nothing after the close runs or reaches the disk: the saved state stays as it was at the close.
    const real = f.ports.herdr, file = f.stateFile(); let snapshot = null;
    f.ports.herdr = async args => {
      if (snapshot) throw Object.assign(Error('process ended'), { code: 'process_ended' });
      const reply = await real(args);
      if (args[0] === 'pane' && args[1] === 'close') snapshot = readFileSync(file);
      return reply;
    };
    return () => { writeFileSync(file, snapshot); f.ports.herdr = real; };
  },
};
for (const [failure, inject] of Object.entries(afterClose)) for (const recovery of ['a plain tick', 'stop and start']) {
  test(`relaunch: after ${failure} after the close, ${recovery} replaces the gone pane for the same coordinator`, async t => {
    const f = await relaunchFixture(t);
    assert.equal((await f.invoke('start')).exitCode, 0);
    const original = f.state();
    f.saveState(state => { delete state.ownerLaunch.fingerprint; });
    const finish = inject(f), prompts = f.prompts.length;
    f.issues = [issue(90)]; f.time += 60 * 1000;
    try { await f.tick(); } catch { /* A simulated process end may end the tick. */ }
    finish();
    assert.deepEqual(f.closed, ['w1:p1']);
    assert.equal(f.state().paneId, 'w1:p1', 'the saved state still names the closed pane');
    assert.equal(f.launches.length, 1); assert.equal(f.prompts.length, prompts);
    // GitHub still lists issue 90; a lost ETag gets the full list again.
    f.time += 30 * 60 * 1000;
    if (recovery === 'a plain tick') await f.tick();
    else {
      assert.equal((await f.invoke('stop')).exitCode, 0);
      const started = await f.invoke('start');
      assert.equal(started.exitCode, 0, started.message);
    }
    const after = f.state();
    assert.deepEqual(f.launches.map(launch => launch.pane), ['w1:p1', 'w2:p1']);
    assert.equal(after.paneId, 'w2:p1'); assert.equal(after.ownerLaunch.paneId, 'w2:p1');
    assert.equal(after.coordinatorId, original.coordinatorId, 'claims stay with the same coordinator');
    assert.equal(after.machine, original.machine); assert.equal(after.activatedAt, original.activatedAt);
    assert.equal(after.ownerLaunch.terminalId, 'term2');
    assert.equal(f.context(f.launches.at(-1)).coordinatorId, original.coordinatorId);
    assert.equal(f.delivered.at(-1), 'w2:p1'); assert.match(f.prompts.at(-1), /"number":90,/);
    assert.equal(f.packet().recipeFirst, true, 'the fresh chat gets the start-up recipe');
    assert.deepEqual(f.live(), ['w2:p1'], 'one coordinator chat');
    const quiet = f.herdrCalls.length; f.status = 304; await f.tick();
    for (const [group, action] of [['workspace', 'create'], ['pane', 'run'], ['pane', 'close']]) assert.equal(herdrSince(f, quiet, group, action).length, 0, `${group} ${action}`);
    assert.doesNotMatch((await f.invoke('status')).message, /coordinator unavailable|relaunch (pending|held)/);
  });
}

// Issue 3037 review F1: a Herdr server restart can give the saved pane id to a new terminal. The
// saved terminal identity keeps the relaunch from closing it and keeps work out of it.
const otherTerminal = {
  'another chat has': f => { Object.assign(f.panes.get('w1:p1'), { terminal_id: 'term-restarted' }); },
  'an empty restored pane has': f => { Object.assign(f.panes.get('w1:p1'), { terminal_id: 'term-restarted', agent: false }); },
  'another chat gets just before the close': f => {
    const real = f.ports.herdr; let gets = 0;
    f.ports.herdr = async args => {
      if (args[0] === 'agent' && args[1] === 'get' && args[2] === 'w1:p1' && ++gets === 2) Object.assign(f.panes.get('w1:p1'), { terminal_id: 'term-restarted' });
      return real(args);
    };
  },
};
for (const [variant, restart] of Object.entries(otherTerminal)) for (const due of [true, false]) {
  if (!due && variant.endsWith('before the close')) continue;
  test(`relaunch: a saved pane id that ${variant} after a Herdr restart stays open and gets no work${due ? ' when a relaunch is due' : ''}; the coordinator gets a fresh pane`, async t => {
    const f = await relaunchFixture(t);
    assert.equal((await f.invoke('start')).exitCode, 0);
    const original = f.state();
    if (due) f.saveState(state => { delete state.ownerLaunch.fingerprint; });
    restart(f);
    const restarted = (await f.invoke('status')).message;
    const calls = f.herdrCalls.length, prompts = f.prompts.length;
    f.issues = [issue(97)]; f.time += 60 * 1000; await f.tick();
    assert.deepEqual(f.closed, [], 'the other pane is never closed');
    assert.equal(f.panes.get('w1:p1').closed, false);
    for (const [group, action] of [['agent', 'prompt'], ['pane', 'run'], ['pane', 'close']]) assert.equal(herdrSince(f, calls, group, action).filter(args => args[2] === 'w1:p1').length, 0, `${group} ${action}`);
    const after = f.state();
    assert.equal(after.paneId, 'w2:p1'); assert.equal(after.coordinatorId, original.coordinatorId);
    assert.deepEqual(f.launches.map(launch => launch.pane), ['w1:p1', 'w2:p1']);
    assert.equal(f.prompts.length, prompts + 1); assert.equal(f.delivered.at(-1), 'w2:p1');
    assert.match(f.prompts.at(-1), /"number":97,/); assert.equal(f.packet().recipeFirst, true);
    assert.equal(f.state().relaunchTargets, undefined, 'a replaced pane is not a relaunch');
    assert.equal(original.ownerLaunch.terminalId, 'term1', 'the launch saves the terminal identity');
    if (!variant.endsWith('before the close')) assert.match(restarted, /coordinator unavailable \((saved target does not match|missing)\)/, 'status does not report the other terminal as the coordinator');
    assert.match((await f.invoke('status')).message, /coordinator idle/);
  });
}

// Issue 3037 second review M1: the relaunch saves a state with no owner launch, and the fresh launch
// saves a new one a few Herdr calls later. Autopilot can stop between these two saves. Stop and start
// must then launch the fresh chat for the same coordinator, as the next tick does.
const afterClear = {
  'the terminal read of the fresh pane fails': f => {
    const real = f.ports.herdr; let failed = false;
    f.ports.herdr = async args => {
      if (!failed && args[0] === 'pane' && args[1] === 'get' && args[2] === 'w2:p1') { failed = true; throw Object.assign(Error('Herdr timed out'), { code: 'timeout' }); }
      return real(args);
    };
    return () => { assert.equal(failed, true); f.ports.herdr = real; };
  },
  'the fresh workspace create fails': f => {
    const real = f.ports.herdr; let failed = false;
    f.ports.herdr = async args => {
      if (!failed && f.closed.length && args[0] === 'workspace' && args[1] === 'create') { failed = true; throw Object.assign(Error('Herdr timed out'), { code: 'timeout' }); }
      return real(args);
    };
    return () => { assert.equal(failed, true); f.ports.herdr = real; };
  },
  'the process ends after the clear': f => {
    // Nothing after the clear runs or reaches the disk: the saved state stays as the clear saved it.
    const real = f.ports.herdr, file = f.stateFile(); let snapshot = null;
    f.ports.herdr = async args => {
      if (!snapshot && f.closed.length && args[0] === 'workspace' && args[1] === 'create') snapshot = readFileSync(file);
      if (snapshot) throw Object.assign(Error('process ended'), { code: 'process_ended' });
      return real(args);
    };
    return () => { writeFileSync(file, snapshot); f.ports.herdr = real; };
  },
  'a person stops Autopilot during the relaunch tick': f => {
    // Stop does not wait for the tick lock, so the tick's next guard sees the disabled state.
    const real = f.ports.herdr; let stopped = null;
    f.ports.herdr = async args => {
      if (!stopped && args[0] === 'pane' && args[1] === 'get' && args[2] === 'w2:p1') stopped = await f.invoke('stop');
      return real(args);
    };
    return () => { assert.equal(stopped?.exitCode, 0); f.ports.herdr = real; };
  },
};
for (const [failure, inject] of Object.entries(afterClear)) {
  test(`relaunch: when ${failure}, stop and start launch the fresh chat for the same coordinator`, async t => {
    const f = await relaunchFixture(t);
    assert.equal((await f.invoke('start')).exitCode, 0);
    const original = f.state();
    // A state that an older package saved: an owner launch with no fingerprint and no launchProfile.
    f.saveState(state => { delete state.ownerLaunch.fingerprint; delete state.launchProfile; });
    const finish = inject(f), prompts = f.prompts.length;
    f.issues = [issue(90)]; f.time += 60 * 1000;
    try { await f.tick(); } catch { /* A Herdr error or a simulated process end may end the tick. */ }
    finish();
    assert.deepEqual(f.closed, ['w1:p1']);
    assert.equal(f.state().ownerLaunch, undefined, 'the clear saved no owner launch');
    assert.equal(f.launches.length, 1); assert.deepEqual(f.live(), []); assert.equal(f.prompts.length, prompts);
    f.time += 30 * 60 * 1000;
    assert.equal((await f.invoke('stop')).exitCode, 0);
    const started = await f.invoke('start');
    assert.equal(started.exitCode, 0, started.message);
    const after = f.state();
    assert.deepEqual(f.launches.map(launch => launch.pane), ['w1:p1', 'w2:p1']);
    assert.deepEqual(f.live(), ['w2:p1'], 'one coordinator chat');
    assert.equal(after.paneId, 'w2:p1'); assert.equal(after.ownerLaunch.paneId, 'w2:p1');
    assert.equal(after.coordinatorId, original.coordinatorId, 'claims stay with the same coordinator');
    assert.equal(after.machine, original.machine); assert.equal(after.activatedAt, original.activatedAt);
    assert.equal(f.context(f.launches.at(-1)).coordinatorId, original.coordinatorId);
    assert.equal(f.delivered.at(-1), 'w2:p1'); assert.match(f.prompts.at(-1), /"number":90,/);
    assert.equal(f.packet().recipeFirst, true, 'the fresh chat gets the start-up recipe');
    const quiet = f.herdrCalls.length; f.status = 304; await f.tick();
    for (const [group, action] of [['workspace', 'create'], ['pane', 'run'], ['pane', 'close']]) assert.equal(herdrSince(f, quiet, group, action).length, 0, `${group} ${action}`);
    assert.match((await f.invoke('status')).message, /coordinator idle/);
  });
}

test('relaunch: an older state with no owner launch and no launch profile still refuses an ordinary start', async t => {
  const f = await relaunchFixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  assert.equal((await f.invoke('stop')).exitCode, 0);
  f.saveState(state => { delete state.ownerLaunch; delete state.launchProfile; });
  const calls = f.herdrCalls.length;
  const started = await f.invoke('start');
  assert.equal(started.exitCode, 1);
  assert.match(started.message, /saved coordinator profile cannot be verified/);
  assert.equal(herdrSince(f, calls, 'pane', 'run').length, 0); assert.equal(f.state().enabled, false);
});

// Issue 3037 second review F1: recovery after an uncertain send uses the saved pane, so the saved
// terminal must still be there; a pane id that another terminal has gets no recovery prompt.
test('relaunch: uncertain-send recovery never prompts a saved pane id that another terminal has', async t => {
  const f = await relaunchFixture(t);
  const real = f.ports.herdr;
  // Recovery also reads the saved workspace.
  f.ports.herdr = async args => args[0] === 'workspace' && args[1] === 'get' ? { result: { type: 'workspace_info', workspace: { workspace_id: args[2] } } } : real(args);
  assert.equal((await f.invoke('start')).exitCode, 0);
  f.saveState(state => { state.deliveryIntent = { version: 2, paneId: state.paneId, workspaceId: state.workspaceId, at: f.time - 1000, fingerprint: null, payloadDigest: 'earlier' }; });
  Object.assign(f.panes.get('w1:p1'), { terminal_id: 'term-restarted', session: 'session-restarted' });
  const calls = f.herdrCalls.length;
  f.issues = [issue(96)]; f.time += 60 * 1000; await f.tick();
  assert.equal(herdrSince(f, calls, 'agent', 'prompt').length, 0, 'no recovery prompt reaches the other terminal');
  for (const [group, action] of [['pane', 'run'], ['pane', 'close'], ['workspace', 'create']]) assert.equal(herdrSince(f, calls, group, action).length, 0, `${group} ${action}`);
  assert.ok(f.state().deliveryIntent, 'the uncertain custody stays');
  // Control: with the saved terminal, the same recovery prompts the saved pane.
  assert.ok(f.warnings.includes('Autopilot recovery waits: the saved target is not safely idle and unchanged.'), f.warnings.join('\n'));
  Object.assign(f.panes.get('w1:p1'), { terminal_id: 'term1' });
  f.time += 30 * 60 * 1000; await f.tick();
  assert.deepEqual(herdrSince(f, calls, 'agent', 'prompt').map(args => args[2]), ['w1:p1']);
  assert.match(f.prompts.at(-1), /fresh current-state reconciliation/);
});

test('relaunch: a saved delivery with uncertain custody blocks the relaunch', async t => {
  const f = await relaunchFixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  f.saveState(state => {
    delete state.ownerLaunch.fingerprint;
    state.deliveryIntent = { version: 2, paneId: state.paneId, workspaceId: state.workspaceId, at: f.time - 1000, fingerprint: null, payloadDigest: 'earlier' };
  });
  const calls = f.herdrCalls.length;
  f.issues = [issue(93)]; f.time += 60 * 1000; await f.tick();
  assert.deepEqual(f.closed, []);
  assert.equal(herdrSince(f, calls, 'pane', 'run').length, 0);
  assert.equal(herdrSince(f, calls, 'workspace', 'create').length, 0);
  assert.equal(f.state().paneId, 'w1:p1');
  assert.doesNotMatch((await f.invoke('status')).message, /relaunch (pending|held)/);
});

test('relaunch: the hold rechecks the chat just before the close and closes nothing when it is working', async t => {
  const f = await relaunchFixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  f.saveState(state => { delete state.ownerLaunch.fingerprint; });
  const real = f.ports.herdr; let gets = 0;
  // The first `agent get` in the wake sees an idle chat; the recheck inside the hold sees a new turn.
  f.ports.herdr = async args => { if (args[0] === 'agent' && args[1] === 'get' && ++gets === 2) f.agentStatus = 'working'; return real(args); };
  const calls = f.herdrCalls.length, prompts = f.prompts.length;
  f.issues = [issue(94)]; f.time += 60 * 1000; await f.tick();
  assert.equal(gets, 2);
  assert.deepEqual(f.closed, []); assert.equal(f.prompts.length, prompts);
  assert.equal(herdrSince(f, calls, 'pane', 'run').length, 0);
  assert.ok(f.warnings.some(text => /could not be closed safely/.test(text)));
  f.ports.herdr = real; f.agentStatus = 'idle'; f.status = 304; await f.tick();
  assert.deepEqual(f.closed, ['w1:p1']); assert.equal(f.delivered.at(-1), 'w2:p1');
  assert.match(f.prompts.at(-1), /"number":94,/);
});

test('relaunch: a blocked chat is not closed and gets no input; status shows the pending relaunch', async t => {
  const f = await relaunchFixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  f.saveState(state => { delete state.ownerLaunch.fingerprint; });
  f.agentStatus = 'blocked';
  const calls = f.herdrCalls.length, prompts = f.prompts.length;
  f.issues = [issue(95)]; f.time += 60 * 1000; await f.tick();
  assert.deepEqual(f.closed, []); assert.equal(f.prompts.length, prompts);
  assert.equal(herdrSince(f, calls, 'pane', 'run').length, 0);
  const status = (await f.invoke('status')).message;
  assert.match(status, /coordinator blocked/);
  assert.equal(status.split('\n').filter(text => /^Coordinator relaunch pending after upgrade/.test(text)).length, 1, status);
  f.agentStatus = 'idle'; f.status = 304; await f.tick();
  assert.deepEqual(f.closed, ['w1:p1']); assert.equal(f.delivered.at(-1), 'w2:p1');
});

test('relaunch: a second relaunch for the same fingerprint is held; the current chat gets work and status shows one line', async t => {
  const f = await relaunchFixture(t);
  const older = join(f.dir, 'pdd-other-install');
  mkdirSync(older); writeFileSync(join(older, 'package.json'), JSON.stringify({ name: 'pdd', version: '0.0.1' }));
  // Starts from two installs alternate, so the fingerprint changes on each start.
  for (const packageRoot of [older, root, older]) assert.equal((await f.invoke('start', { packageRoot })).exitCode, 0);
  const original = f.state();
  assert.deepEqual(f.closed, ['w1:p1', 'w2:p1']); assert.equal(f.launches.length, 3);
  const writes = f.githubWrites().length, prompts = f.prompts.length;
  const started = await f.invoke('start');
  assert.equal(started.exitCode, 0, started.message);
  assert.deepEqual(f.closed, ['w1:p1', 'w2:p1'], 'no third relaunch');
  assert.equal(f.launches.length, 3);
  assert.equal(f.prompts.length, prompts + 1); assert.equal(f.delivered.at(-1), 'w3:p1', 'the current chat gets work');
  assert.equal(f.warnings.filter(text => /did not relaunch the coordinator chat again/.test(text)).length, 1);
  const held = (await f.invoke('status')).message;
  assert.equal(held.split('\n').filter(text => /^Coordinator relaunch held/.test(text)).length, 1, held);
  assert.doesNotMatch(held, /relaunch pending/);
  assert.equal(original.relaunchTargets.length, 2, 'the relaunch record');
  f.status = 304; await f.tick();
  assert.equal(f.launches.length, 3); assert.equal(f.closed.length, 2);
  assert.equal(f.warnings.filter(text => /did not relaunch the coordinator chat again/.test(text)).length, 1, 'one warning');
  assert.equal(f.githubWrites().length, writes);
  // A person closes the coordinator pane: a fresh chat starts with the current settings.
  f.panes.get('w3:p1').closed = true;
  f.issues = [issue(98)]; f.status = 200; f.time += 60 * 1000; await f.tick();
  assert.equal(f.launches.at(-1).pane, 'w4:p1'); assert.equal(f.delivered.at(-1), 'w4:p1');
  assert.equal(f.state().ownerLaunch.fingerprint, f.module.autopilotLaunchFingerprint(f.state()));
  assert.equal(f.state().coordinatorId, original.coordinatorId);
  assert.doesNotMatch((await f.invoke('status')).message, /relaunch (pending|held)/);
});

// Issue 2903: a `cd` in the person's shell startup file moves each new Herdr pane's shell out of the repository.
test('2903: with a shell startup cd, the coordinator chat starts in the repository, gets its work and status sees it', async t => {
  const f = await relaunchFixture(t, { shellStartup: true, cwdName: "my repo 'q' $HOME" });
  f.issues = [issue(64)];
  assert.equal((await f.invoke('start')).exitCode, 0);
  const [launch] = herdrSince(f, 0, 'pane', 'run');
  assert.match(launch[3], /^cd '.+' && env /, 'the launch line starts with its own cd');
  assert.equal(f.panes.get('w1:p1').agentCwd, realpathSync(f.cwd), 'the coordinator agent runs in the repository, not in the shell startup folder');
  assert.equal(f.delivered.at(-1), 'w1:p1'); assert.match(f.prompts.at(-1), /"number":64,/);
  assert.match((await f.invoke('status')).message, /coordinator idle/);
});

test('2903: a coordinator chat that an older launch started in the shell startup folder is replaced at an idle moment', async t => {
  const f = await relaunchFixture(t, { shellStartup: true });
  assert.equal((await f.invoke('start')).exitCode, 0);
  const original = f.state();
  // An older package typed no cd: its chat runs in the shell startup folder, and it saved no launch fingerprint.
  Object.assign(f.panes.get('w1:p1'), { shell: f.elsewhere, agentCwd: realpathSync(f.elsewhere) });
  f.saveState(state => { delete state.ownerLaunch.fingerprint; });
  f.status = 304; f.time += 60 * 1000; await f.tick();
  assert.deepEqual(f.closed, ['w1:p1'], 'the relaunch closes the saved chat although its folder moved');
  const after = f.state();
  assert.equal(after.paneId, 'w2:p1'); assert.equal(after.coordinatorId, original.coordinatorId);
  assert.equal(f.panes.get('w2:p1').agentCwd, realpathSync(f.cwd), 'the fresh chat runs in the repository');
  assert.match((await f.invoke('status')).message, /coordinator idle/);
  // The cd is part of the launch, so its folder is in the fingerprint for every provider.
  const fingerprint = cwd => f.module.autopilotLaunchFingerprint({ ...after, cwd, agent: { ...after.agent, kind: 'claude' } });
  assert.notEqual(fingerprint(f.cwd), fingerprint(f.elsewhere));
});

test('2903: with a shell startup cd, uncertain-send recovery checks the repository in its saved path and prompts the saved chat', async t => {
  const f = await relaunchFixture(t, { shellStartup: true });
  const real = f.ports.herdr, run = f.ports.run, repoViews = [];
  // Recovery also reads the saved workspace.
  f.ports.herdr = async args => args[0] === 'workspace' && args[1] === 'get' ? { result: { type: 'workspace_info', workspace: { workspace_id: args[2] } } } : real(args);
  f.ports.run = async (command, args, options) => { if (command === 'gh' && args[0] === 'repo') repoViews.push(options?.cwd); return run(command, args, options); };
  assert.equal((await f.invoke('start')).exitCode, 0);
  // Herdr names the repository with another spelling (a symlink): the folder matches, but only the saved path is this repository's path.
  const link = join(f.dir, 'repo link'); symlinkSync(f.cwd, link);
  Object.assign(f.panes.get('w1:p1'), { shell: link, agentCwd: link });
  f.saveState(state => { state.deliveryIntent = { version: 2, paneId: state.paneId, workspaceId: state.workspaceId, at: f.time - 1000, fingerprint: null, payloadDigest: 'earlier' }; });
  const calls = f.herdrCalls.length, views = repoViews.length;
  f.issues = [issue(96)]; f.time += 60 * 1000; await f.tick();
  assert.deepEqual(herdrSince(f, calls, 'agent', 'prompt').map(args => args[2]), ['w1:p1'], f.warnings?.join('\n'));
  assert.match(f.prompts.at(-1), /fresh current-state reconciliation/);
  assert.ok(repoViews.length > views && repoViews.slice(views).every(cwd => cwd === f.cwd), `gh repo view runs in the saved path, not in ${link}: ${JSON.stringify(repoViews)}`);
});

test('2903: the relaunch close compares the folder when no terminal id is saved, and trusts a matching saved terminal id', async t => {
  // An old chat whose launch saved no terminal id, and the next tick wants to relaunch it.
  const unproved = async (folder = null) => {
    const f = await relaunchFixture(t, { shellStartup: true });
    assert.equal((await f.invoke('start')).exitCode, 0);
    if (folder) { const path = folder(f); Object.assign(f.panes.get('w1:p1'), { shell: path, agentCwd: path }); }
    f.saveState(state => { delete state.ownerLaunch.fingerprint; state.ownerLaunch.terminalId = null; });
    f.status = 304; f.time += 60 * 1000; await f.tick();
    return f;
  };
  // The saved pane id now names an idle chat of another repository in the shared session: it stays open.
  const other = await unproved(f => { const path = join(f.dir, 'other repository'); mkdirSync(path); return path; });
  assert.deepEqual(other.closed, [], 'a chat in another repository folder is never closed');
  assert.equal(other.launches.length, 1, 'no relaunch');
  assert.equal(other.state().paneId, 'w1:p1');
  // Control: the same saved state with the chat in this repository is closed and relaunched.
  const same = await unproved();
  assert.deepEqual(same.closed, ['w1:p1']); assert.equal(same.state().paneId, 'w2:p1');
  // A saved terminal id that Herdr still reports proves the chat: it is closed although its shell moved.
  const f = await relaunchFixture(t, { shellStartup: true });
  assert.equal((await f.invoke('start')).exitCode, 0);
  assert.equal(f.state().ownerLaunch.terminalId, 'term1');
  Object.assign(f.panes.get('w1:p1'), { shell: f.elsewhere, agentCwd: realpathSync(f.elsewhere) });
  f.saveState(state => { delete state.ownerLaunch.fingerprint; });
  f.status = 304; f.time += 60 * 1000; await f.tick();
  assert.deepEqual(f.closed, ['w1:p1']); assert.equal(f.state().paneId, 'w2:p1');
});

for (const state of ['waiting', 'running']) test(`full-suite ${state} does not emit stuck or idle-claim rules`, async t => {
  const f = await fixture(t);
  const hour = 60 * 60 * 1000, changedAt = f.time - 2 * hour;
  f.issues = [issue(101, {labels:['pdd:working'], updated_at:new Date(changedAt).toISOString()})];
  f.runProgress = [{number:101,changedAt,suite:{state,position:state === 'waiting' ? 4 : null,queuedAt:changedAt,startedAt:state === 'running' ? changedAt : null,finishedAt:null,reason:null,pausedMs:2*hour}}];
  const result = await f.invoke('start'); assert.equal(result.exitCode, 0, result.message);
  const rules = f.prompts.flatMap(text => JSON.parse(text.trim().split('\n').at(-1)).timeRules ?? []);
  assert.equal(rules.some(rule => rule.number === 101 && ['stuck-run','idle-claim'].includes(rule.kind)), false, 'suite activity pauses inactivity rules');
});

test('a suite timeout emits its own reason once, without a stuck issue rule', async t => {
  const f = await fixture(t), hour = 60 * 60 * 1000, changedAt = f.time - 2 * hour;
  f.issues = [issue(101, {labels:['pdd:working'],updated_at:new Date(changedAt).toISOString()})];
  f.runProgress = [{number:101,changedAt,suite:{state:'finished',position:null,queuedAt:changedAt,startedAt:changedAt,finishedAt:f.time - 1,reason:'per-file timeout: test/slow.test.mjs',pausedMs:hour}}];
  const result = await f.invoke('start'); assert.equal(result.exitCode, 0, result.message);
  const rules = () => f.prompts.flatMap(text => JSON.parse(text.trim().split('\n').at(-1)).timeRules ?? []);
  assert.equal(rules().filter(rule => rule.number === 101 && rule.kind === 'suite-failed').length, 1);
  assert.match(rules().find(rule => rule.kind === 'suite-failed').reason, /per-file timeout.*slow/);
  assert.equal(rules().some(rule => ['stuck-run','idle-claim'].includes(rule.kind)), false);
  await f.tick(); assert.equal(rules().filter(rule => rule.kind === 'suite-failed').length, 1);
});

test('native progress reader pauses the stuck clock and resumes its remaining time after a suite', async t => {
  const f = await fixture(t); await f.invoke('start'); f.prompts.length = 0;
  delete f.ports.readRunProgress;
  const folder = join(f.cwd,'.git','pdd','runs','101'), worktree = join(f.dir,'worktree'), queue = join(f.dir,'suite-queue');
  mkdirSync(folder,{recursive:true}); mkdirSync(worktree); mkdirSync(queue);
  const changedAt=f.time, statusFile=join(folder,'status.json');
  writeFileSync(statusFile,JSON.stringify({v:1,number:101,repo:'owner/repo',state:'running',root:worktree}));
  utimesSync(statusFile,new Date(changedAt),new Date(changedAt));
  const row={ticket:1,pid:process.pid,childPid:null,cwd:worktree,state:'waiting',queuedAt:changedAt+10*60_000,startedAt:null,finishedAt:null,reason:null};
  const file=join(queue,'ticket-1.json'); writeFileSync(file,JSON.stringify(row));
  f.ports.env={HOME:f.home,PDD_SUITE_QUEUE:queue}; f.time=changedAt+2*hour;
  await f.tick(); assert.equal(f.prompts.length,0,'waiting time does not make a run stuck');
  row.state='finished'; row.finishedAt=f.time; writeFileSync(file,JSON.stringify(row));
  f.time+=49*60_000; await f.tick(); assert.equal(f.prompts.length,0,'ten minutes before waiting plus 49 after is below the threshold');
  f.time+=60_000; await f.tick();
  assert.equal(packet(f).timeRules.filter(rule=>rule.kind==='stuck-run'&&rule.number===101).length,1,'only time outside the queue counts');
});


test('different failed suite tickets with the same finish time each get one failure event', async t => {
  const f=await fixture(t);
  const suite={ticket:1,state:'finished',position:null,queuedAt:f.time-100,startedAt:f.time-50,finishedAt:f.time,reason:'suite exit 1',pausedMs:100};
  f.runProgress=[{number:101,changedAt:f.time,suite}];
  assert.equal((await f.invoke('start')).exitCode,0);
  suite.ticket=2; await f.tick(); await f.tick();
  const rules=f.prompts.flatMap(text=>JSON.parse(text.trim().split('\n').at(-1)).timeRules??[]);
  assert.equal(rules.filter(rule=>rule.kind==='suite-failed').length,2);
});

for (const selector of ['PDD_SUITE_QUEUE', 'PDD_VM_SUITE_LOCK']) test(`shared suite selector ${selector} survives native launch and a later tick`, async t => {
  const f = await fixture(t, {mode:'observe'}), selected = join(f.dir, "shared 'queue' $()"), bin = join(f.dir,'bin');
  mkdirSync(bin);
  const output = join(f.dir,'native-queue.json');
  writeFileSync(join(bin,'codex'), `#!${process.execPath}\nrequire('node:fs').writeFileSync(${JSON.stringify(output)},JSON.stringify({queue:process.env.PDD_SUITE_QUEUE??null,legacy:process.env.PDD_VM_SUITE_LOCK??null,argv:process.argv.slice(2)}));\n`, {mode:0o755});
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    const result = await herdr(args);
    if (args[0] === 'pane' && args[1] === 'run') execFileSync('/bin/sh',['-c',args[3]],{cwd:f.cwd,env:{HOME:f.home,PATH:`${bin}:/usr/bin:/bin`,PDD_SUITE_QUEUE:'/stale-server-queue',PDD_VM_SUITE_LOCK:'/stale-server-lock'},timeout:10000});
    return result;
  };
  const result = await f.invoke('start',{env:{HOME:f.home,PATH:`${bin}:/usr/bin:/bin`,PDD_SUITE_QUEUE:undefined,PDD_VM_SUITE_LOCK:undefined,[selector]:selected}});
  assert.equal(result.exitCode,0,result.message);
  const actual = JSON.parse(readFileSync(output,'utf8'));
  assert.equal(actual[selector === 'PDD_SUITE_QUEUE' ? 'queue' : 'legacy'],selected,'native coordinator inherits the exported queue selector');
  assert.equal(actual[selector === 'PDD_SUITE_QUEUE' ? 'legacy' : 'queue'],null,'the other selector cannot come from the Herdr server');
  assert.equal(codexConfigs(actual.argv).set[selector],selected,'coordinator commands forward the queue selector to worker launches');
  assert.equal(f.state().environment[selector],selected,'saved environment retains queue selection');
  assert.equal(f.timers.find(([action])=>action==='start')[1].environment[selector],selected,'timer retains queue selection');
  const folder=join(f.cwd,'.git','pdd','runs','101'),worktree=join(f.dir,'worktree');
  const queue=selector==='PDD_SUITE_QUEUE'?selected:`${selected}.queue`;
  mkdirSync(folder,{recursive:true}); mkdirSync(worktree); mkdirSync(queue);
  const changedAt=f.time-2*hour,statusFile=join(folder,'status.json');
  writeFileSync(statusFile,JSON.stringify({v:1,number:101,repo:'owner/repo',state:'running',root:worktree}));
  utimesSync(statusFile,new Date(changedAt),new Date(changedAt));
  writeFileSync(join(queue,'ticket-1.json'),JSON.stringify({ticket:1,pid:process.pid,childPid:null,cwd:worktree,state:'waiting',queuedAt:changedAt,startedAt:null,finishedAt:null,reason:null}));
  delete f.ports.readRunProgress; f.prompts.length=0;
  // Only saved startup state selects the queue. Mask the unrelated ambient selector.
  f.ports.env = {[selector === 'PDD_SUITE_QUEUE' ? 'PDD_VM_SUITE_LOCK' : 'PDD_SUITE_QUEUE']: undefined};
  await f.tick();
  const rules=f.prompts.flatMap(text=>JSON.parse(text.trim().split('\n').at(-1)).timeRules??[]);
  assert.equal(rules.some(rule=>rule.number===101&&['stuck-run','idle-claim'].includes(rule.kind)),false,'later tick observes the configured queue');
});

for (const damage of ['malformed', 'unreadable']) test(`unavailable suite queue (${damage}) retains progress and defers inactivity until recovery`, async t => {
  const f=await fixture(t); await f.invoke('start'); f.prompts.length=0;
  delete f.ports.readRunProgress;
  const worktree=join(f.dir,'worktree'),queue=join(f.dir,'queue'),folder=join(f.cwd,'.git','pdd','runs','101');
  mkdirSync(worktree); mkdirSync(queue); mkdirSync(folder,{recursive:true});
  const changedAt=f.time-2*hour,statusFile=join(folder,'status.json');
  writeFileSync(statusFile,JSON.stringify({v:1,number:101,repo:'owner/repo',state:'running',root:worktree}));
  utimesSync(statusFile,new Date(changedAt),new Date(changedAt));
  const ticket=join(queue,'ticket-unrelated.json');
  if(damage==='malformed') writeFileSync(ticket,'{'); else mkdirSync(ticket);
  f.ports.env={HOME:f.home,PDD_SUITE_QUEUE:queue};
  f.issues=[issue(101,{labels:['pdd:working'],updated_at:new Date(changedAt).toISOString()})];
  await f.tick();
  const rules=()=>f.prompts.flatMap(text=>JSON.parse(text.trim().split('\n').at(-1)).timeRules??[]);
  assert.equal(rules().some(rule=>rule.number===101&&['stuck-run','idle-claim','suite-failed'].includes(rule.kind)),false,'unknown queue activity cannot establish inactivity or a failed suite');
  assert.ok(f.warnings.some(text=>/101/.test(text)&&/queue.*unavailable/i.test(text)),'queue uncertainty and affected run are visible');
  assert.ok(f.warnings.some(text=>damage==='malformed'?/JSON|Unexpected/i.test(text):/EISDIR|directory/i.test(text)),'warning retains the read cause');
  const before=readFileSync(statusFile); rmSync(ticket,{recursive:true});
  await f.tick();
  assert.ok(rules().some(rule=>rule.number===101&&rule.kind==='stuck-run'),'recovered queue restores normal run inactivity checks');
  assert.ok(rules().some(rule=>rule.number===101&&rule.kind==='idle-claim'),'recovered queue restores claim inactivity checks');
  assert.deepEqual(readFileSync(statusFile),before,'observing queue uncertainty does not mutate run progress');
});

test('native timer definitions retain both exported shared suite selectors', async t => {
  for (const platform of ['linux','darwin']) {
    const f=await fixture(t,{mode:'observe'}); delete f.ports.timer; f.ports.platform=platform; f.ports.uid=123;
    const selectors={PDD_SUITE_QUEUE:join(f.dir,'selected-queue'),PDD_VM_SUITE_LOCK:join(f.dir,'legacy-lock')};
    const env={HOME:f.home,PATH:'/fixture/bin',XDG_CONFIG_HOME:join(f.home,'.config'),...selectors};
    const run=f.ports.run;
    f.ports.run=async(command,args,options)=>['systemctl','launchctl','loginctl'].includes(command)
      ? {code:0,stdout:command==='loginctl'?'yes\n':'',stderr:''} : run(command,args,options);
    const result=await f.invoke('start',{env}); assert.equal(result.exitCode,0,result.message);
    const folder=platform==='linux'?join(f.home,'.config','systemd','user'):join(f.home,'Library','LaunchAgents');
    const file=readdirSync(folder).find(name=>name.endsWith(platform==='linux'?'.service':'.plist'));
    const definition=readFileSync(join(folder,file),'utf8');
    for(const [name,value] of Object.entries(selectors)) {
      assert.ok(definition.includes(name),`${platform} timer records ${name}`);
      assert.ok(definition.includes(value),`${platform} timer records the selected path`);
    }
  }
});

// #3067: capacity reads use the same fake machine on start, tick and status.
test('machine capacity follows resize on an empty tick without an AI wake', async t => {
  const f=await fixture(t), {checkMachine}=await import('./helpers/check-machine.mjs');
  const fake=checkMachine({count:64});
  f.ports.checkCapacityPorts={...fake.ports,queueRoot:join(f.dir,'machine-checks')};
  assert.equal((await f.invoke('start')).exitCode,0);
  assert.deepEqual([f.state().checkCapacity.checks,f.state().checkCapacity.runs],[5,10]);
  const owner=f.state().ownerLaunch, prompts=f.prompts.length;
  fake.machine.count=8;f.status=304;
  assert.equal((await f.tick()).exitCode,0);
  assert.deepEqual([f.state().checkCapacity.checks,f.state().checkCapacity.runs],[1,2]);
  assert.deepEqual(f.state().ownerLaunch,owner,'capacity does not change coordinator custody');
  assert.equal(f.prompts.length,prompts,'an empty resize tick makes no AI call');
  const status=await f.invoke('status');
  assert.match(status.message,/check slots:\s*0 busy of 1, 0 waiting, cores per check 8/);
  assert.match(status.message,/checks:\s*calculated 1, chosen 1; runs:\s*calculated 2, chosen 2/);
});

test('start saves check and run overrides and CLI forwards checks', async t => {
  const f=await fixture(t);
  for(const value of ['0','-1','1.2','9007199254740992','Infinity']) assert.equal((await f.invoke('start',{checks:value})).exitCode,2);
  assert.equal((await f.invoke('start',{checks:'2',runs:'9'})).exitCode,0);
  assert.deepEqual([f.state().checks,f.state().runs,f.state().checkCapacity.checks,f.state().checkCapacity.runs],[2,9,2,9]);
  f.status=304;await f.tick();
  assert.deepEqual([f.state().checkCapacity.checks,f.state().checkCapacity.runs],[2,9]);
  const status=await f.invoke('status');assert.match(status.message,/checks:\s*calculated 3, chosen 2; runs:\s*calculated 4, chosen 9/);
  let received;
  const code=await runPdd(['autopilot','start','--checks','4','--runs','11'],{cwd:f.cwd,stdout:capture(),stderr:capture(),
    autopilotLauncher:{runAutopilotLauncher:async input=>{received=input;return {exitCode:0,message:'started'};}},
    autopilotGithub:{checkAutopilotSettings:async()=>({warning:''})}});
  assert.equal(code,0);assert.deepEqual([received.checks,received.runs],['4','11']);
  assert.equal((await f.invoke('start')).exitCode,0);
  assert.equal(f.state().checks,undefined);assert.equal(f.state().runs,undefined);
  assert.deepEqual([f.state().checkCapacity.checks,f.state().checkCapacity.runs],[3,6]);
});

test('stopping a launcher removes its shared capacity while leaving check tickets alone',async t=>{
  const f=await fixture(t);
  assert.equal((await f.invoke('start',{checks:'1'})).exitCode,0);
  const capacityFile=join(f.ports.checkCapacityPorts.queueRoot,'capacity.json');
  assert.equal(JSON.parse(readFileSync(capacityFile)).owner,f.stateFile());
  const ticketFile=join(f.ports.checkCapacityPorts.queueRoot,'ticket-1.json');
  const ticket={ticket:1,pid:process.pid,childPid:process.pid,cwd:f.cwd,state:'running',queuedAt:f.time,startedAt:f.time,finishedAt:null,reason:null,cpuIds:[0]};
  writeFileSync(ticketFile,JSON.stringify(ticket));
  assert.equal((await f.invoke('stop')).exitCode,0);
  assert.equal(existsSync(capacityFile),false);assert.deepEqual(JSON.parse(readFileSync(ticketFile)),ticket);
});


test('repair 1: repository status displays the latest shared owner limits',async t=>{
  const a=await fixture(t), b=await fixture(t), {checkMachine}=await import('./helpers/check-machine.mjs');
  const shared={...checkMachine({count:64}).ports,queueRoot:join(a.dir,'shared-checks')};
  a.ports.checkCapacityPorts=shared;b.ports.checkCapacityPorts=shared;
  assert.equal((await a.invoke('start',{checks:'1',runs:'7'})).exitCode,0);
  assert.equal((await b.invoke('start',{checks:'3',runs:'19'})).exitCode,0);
  const before=readFileSync(join(shared.queueRoot,'capacity.json'));
  const status=await a.invoke('status');assert.equal(status.exitCode,0);
  const numbers=/check slots:\s*(\d+) busy of (\d+), (\d+) waiting, cores per check (\d+)/.exec(status.message);
  assert.ok(numbers);assert.deepEqual(numbers.slice(1).map(Number),[0,3,0,21]);
  assert.match(status.message,/checks:\s*calculated 5, chosen 3; runs:\s*calculated 6, chosen 19/);
  assert.match(status.message,/repository overrides: checks 1, runs 7/);
  assert.deepEqual(readFileSync(join(shared.queueRoot,'capacity.json')),before);
});

test('native attention digest includes parallel automatic runs without waking the coordinator', async t => {
  const f = await fixture(t);
  const digests = [];
  f.ports.sendDigest = async (input, ports) => {
    digests.push(structuredClone(input));
    assert.equal((await ports.repository()).nameWithOwner, 'owner/repo');
    assert.equal(ports.hostname(), f.state().machine);
    return { exitCode: 0, message: 'recorded' };
  };
  assert.equal((await f.invoke('start')).exitCode, 0);
  const machine = f.state().machine, common = join(f.cwd, '.git');
  const seed = (number, extra = {}) => {
    const runDir = join(common, 'pdd', 'runs', String(number));
    mkdirSync(runDir, { recursive: true });
    writeFileSync(join(runDir, 'status.json'), JSON.stringify({ v: 1, number, runDir, repo: 'owner/repo', state: 'running',
      automaticOrigin: { machine }, ...extra }));
    return { number, runDir };
  };
  const runs = [seed(41, { state: 'stuck', parkReason: 'Required check unavailable' }),
    seed(42, { state: 'paused', runtimeWait: { reason: 'Interpreter busy' } }),
    seed(43, { state: 'question', question: { at: 2, text: 'Choose retention' } }),
    seed(44, { automaticOrigin: null, state: 'stuck' }),
    seed(45, { state: 'stuck', automaticOrigin: { machine: 'other-machine' } }),
    seed(46, { repo: 'other/project', state: 'stuck' }),
    seed(47, { state: 'cancelled' }), seed(48, { state: 'completed' }),
    seed(49, { state: 'completed', gate: { kind: 'ask-code', at: 3 }, question: { at: 1, text: 'Old question' } })];
  const index = join(f.home, '.local', 'state', 'pdd');
  mkdirSync(index, { recursive: true });
  writeFileSync(join(index, 'runs.json'), JSON.stringify({ version: 1, runs }));
  const prompts = f.prompts.length;
  f.time += 30 * 60 * 1000;
  assert.equal((await f.tick()).exitCode, 0);
  assert.equal(digests.length, 2, 'every enabled tick must attempt the native digest before considering AI work');
  assert.deepEqual(digests.at(-1).attention, [
    { number: 41, category: 'stuck', cause: 'Required check unavailable' },
    { number: 42, category: 'parked', cause: 'Interpreter busy' },
    { number: 43, category: 'decision', cause: 'Choose retention' },
    { number: 49, category: 'decision', cause: 'ask-code' }]);
  assert.equal(f.prompts.length, prompts, 'digest collection must not wake an AI agent');
  const saved = JSON.parse(readFileSync(join(common, 'pdd', 'runs', '41', 'status.json'), 'utf8'));
  assert.equal(saved.state, 'stuck');
  assert.equal(saved.parkReason, 'Required check unavailable');
});

test('digest runs before rate-limit retry and its failure does not stop the launcher', async t => {
  const f = await fixture(t);
  let attempts = 0;
  f.ports.readAttention = () => [{ number: 41, category: 'stuck', cause: 'Check unavailable' }];
  f.ports.sendDigest = async input => { attempts++; assert.equal(input.attention[0].number, 41); throw Error('synthetic delivery failure'); };
  assert.equal((await f.invoke('start')).exitCode, 0);
  const saved = f.state(); saved.retryAt = f.time + 60 * 60 * 1000;
  writeFileSync(f.stateFile(), JSON.stringify(saved));
  const polls = f.polls.length;
  assert.equal((await f.tick()).exitCode, 0);
  assert.equal(attempts, 2, 'a GitHub retry must not suppress the native attention digest');
  assert.equal(f.polls.length, polls);
  writeFileSync(join(f.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'off', trust: [] } }));
  await f.tick();
  assert.equal(attempts, 2, 'off mode must not send a digest');
});
for (const state of ['running', 'waiting']) test(`cost polling cannot postpone the native stalled-run rule for ${state} runs`, async t => {
  const f = await fixture(t); delete f.ports.readRunProgress;
  f.ports.env = {HOME: f.home, PDD_SUITE_QUEUE: join(f.dir, 'suite-queue'), PDD_INTERPRETER_QUEUE: join(f.dir, 'interpreter-queue')};
  const invoke = f.invoke;
  f.invoke = (command, extra = {}) => invoke(command, {env: f.ports.env, ...extra}); f.ports.skipMetricsDelivery = true;
  const { updateRun } = await import('../src/workflow-runs.mjs');
  const changedAt = f.time, commonDir = join(f.cwd, '.git'), runDir = join(commonDir, 'pdd', 'runs', '117');
  mkdirSync(runDir, { recursive: true });
  const file = join(runDir, 'status.json');
  const original = { v: 1, number: 117, repo: 'owner/repo', state, runDir, commonDir, root: f.cwd, sourceRoot: f.cwd,
    runId: 'cost-polling', startedAt: changedAt, updatedAt: changedAt, journalSeq: 4, areas: [], area: 0, done: {}, chats: [] };
  writeFileSync(file, JSON.stringify(original)); utimesSync(file, new Date(changedAt), new Date(changedAt));
  const saved = () => JSON.parse(readFileSync(file, 'utf8'));
  f.ports.costRuns = async () => [saved()];
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  for (const minute of [20, 40, 59]) {
    f.time = changedAt + minute * 60000;
    assert.equal((await f.invoke('status', { json: true })).exitCode, 0);
    await f.tick(); assert.equal(f.prompts.length, 0);
  }
  f.time = changedAt + hour; await f.tick();
  assert.equal(f.prompts.length, 1);
  assert.deepEqual(packet(f).timeRules.map(event => event.number), [117]);
  assert.equal(saved().updatedAt, original.updatedAt); assert.equal(saved().journalSeq, original.journalSeq);
  assert.deepEqual(saved().done, original.done); assert.equal(saved().state, state);
  updateRun(runDir, run => { run.done = { build: { at: f.time, summary: 'completed' } }; return run; }, { ...f.ports, env: { HOME: f.home } });
  utimesSync(file, new Date(f.time), new Date(f.time));
  const progressedAt = f.time;
  assert.equal(saved().progressAt, undefined);
  f.time = progressedAt + hour - 1;
  assert.equal((await f.invoke('status', { json: true })).exitCode, 0);
  await f.tick(); assert.equal(f.prompts.length, 1);
  f.time++; await f.tick(); assert.equal(f.prompts.length, 2);
});
test('interpreter queue waiting and unavailable ownership cannot trigger the stuck rule', async t => {
  const f = await fixture(t), changedAt = f.time;
  f.runProgress = [{ number: 3066, changedAt, interpreter: { state: 'waiting', position: 2, pausedMs: 0 } }];
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  f.time += 2 * hour; await f.tick();
  assert.equal(f.prompts.length, 0, 'machine queue waiting must pause the stuck rule');
  f.runProgress[0].interpreter.state = 'unavailable'; await f.tick();
  assert.equal(f.prompts.length, 0, 'unreadable queue ownership cannot prove no progress');
  f.runProgress[0] = { number: 3066, changedAt: f.time - hour / 2, interpreter: { state: 'finished', pausedMs: 1.5 * hour } };
  await f.tick(); assert.equal(f.prompts.length, 0);
  f.time += hour / 2; await f.tick();
  assert.deepEqual(packet(f).timeRules.filter(row => row.kind === 'stuck-run').map(row => row.number), [3066]);
});

test('native run progress subtracts saved interpreter waiting after a launcher restart', async t => {
  const f = await fixture(t); delete f.ports.readRunProgress;
  f.ports.env = {HOME: f.home, PDD_SUITE_QUEUE: join(f.dir, 'suite-queue'), PDD_INTERPRETER_QUEUE: join(f.dir, 'interpreter-queue')};
  const invoke = f.invoke;
  f.invoke = (command, extra = {}) => invoke(command, {env: f.ports.env, ...extra});
  const changedAt = f.time, folder = join(f.cwd, '.git', 'pdd', 'runs', '3066'); mkdirSync(folder, { recursive: true });
  const file = join(folder, 'status.json');
  writeFileSync(file, JSON.stringify({ v: 1, number: 3066, repo: 'owner/repo', state: 'running', root: f.cwd }));
  utimesSync(file, new Date(changedAt), new Date(changedAt));
  f.ports.readInterpreterProgress = ({ cwd, since }) => {
    assert.equal(cwd, f.cwd); assert.equal(since, changedAt);
    return { state: 'finished', position: null, pausedMs: hour };
  };
  await f.invoke('start'); f.prompts.length = 0; f.status = 304;
  f.time += hour; await f.tick();
  assert.equal(f.prompts.length, 0, 'saved interpreter wait must be excluded after restart');
  f.time += hour; await f.tick();
  assert.deepEqual(packet(f).timeRules.filter(row => row.kind === 'stuck-run').map(row => row.number), [3066]);
});
test('2709: a full pane budget holds fresh intake and the next tick can release the hold', async t => {
  const f = await fixture(t), warnings = [];
  let count = 55, sweeps = 0;
  f.ports.warn = text => warnings.push(text);
  f.ports.tidyRuns = async () => {sweeps++; return {closed:0,kept:0,exitCode:0,message:'sweep'};};
  f.ports.workflowHerdr = async args => {
    assert.deepEqual(args,['pane','list']);
    return {result:{type:'pane_list',panes:Array.from({length:count},(_,i)=>({pane_id:`p${i}`,workspace_id:`w${i}`,tab_id:`t${i}`,terminal_id:`term${i}`}))}};
  };
  f.issues = [issue(2709)];
  assert.equal((await f.invoke('start')).exitCode,0);
  count = 56; await f.tick();
  assert.deepEqual(f.state().githubIntake.eligible,[]);
  assert.ok(warnings.some(text=>text.includes('panes'))); assert.ok(sweeps >= 1);
  count = 1; f.status = 304;
  assert.equal((await f.tick()).exitCode,0);
  assert.deepEqual(f.state().githubIntake.eligible,[f.issues[0].html_url]);
});
test('status shows saved group size, cause and umbrella without GitHub reads', async t => {
  const f = await fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  const group = { area: 'cli', rootCause: 'shared-context', umbrella: 'https://github.com/owner/repo/issues/100', members: ['https://github.com/owner/repo/issues/1','https://github.com/owner/repo/issues/2','https://github.com/owner/repo/issues/3'] };
  f.ports.reconcileDependencyIntake = async () => ({ eligible: [], queued: [], skipped: [], groups: [group] });
  await f.tick();
  const before = f.runs.filter(([file]) => file === 'gh').length;
  const result = await f.invoke('status');
  assert.equal(result.exitCode, 0);
  assert.ok(result.message.includes('3 issues'));
  assert.ok(result.message.includes(group.rootCause));
  assert.ok(result.message.includes(group.umbrella));
  assert.equal(f.runs.filter(([file]) => file === 'gh').length, before);
});

for (const configured of [undefined, 'develop/topic']) test(`3071 launcher selects and caches base ${configured ?? 'default'}`, async t => {
  const f = await fixture(t);
  writeFileSync(join(f.cwd, 'pdd.json'), JSON.stringify({autopilot:{mode:'auto', ...(configured ? {base:configured} : {})}}));
  writeFileSync(join(f.cwd, 'CONTRIBUTING.md'), 'Use alpha for all PRs.');
  const expected = configured ?? 'trunk';
  const start = await f.invoke('start');
  assert.equal(start.exitCode, 0, start.message);
  assert.equal(f.state().baseBranch, expected);
  assert.equal(f.state().defaultBranch, 'trunk');
  assert.ok(start.message.includes(expected));
  const packet = JSON.parse(f.prompts[0].trimEnd().split('\n').at(-1));
  assert.equal(packet.baseBranch, expected); assert.equal(packet.workflow.baseBranch, expected);
  const reads = () => f.runs.filter(([command,args]) => command === 'gh' && args[0] === 'repo').length;
  assert.equal(reads(), 1);
  f.status = 304;
  await f.tick(); await f.tick();
  const status = await f.invoke('status');
  assert.equal(status.exitCode, 0); assert.ok(status.message.includes(expected)); assert.equal(reads(), 1);
  const all = await f.invoke('status', {all:true}); assert.ok(all.message.includes(expected)); assert.equal(reads(),1);
  writeFileSync(join(f.cwd, 'pdd.json'), JSON.stringify({autopilot:{mode:'auto',base:'integration'}}));
  await f.tick();
  assert.equal(f.state().baseBranch, 'integration'); assert.equal(reads(),1);
  const updated = JSON.parse(f.prompts.at(-1).trimEnd().split('\n').at(-1));
  assert.equal(updated.baseBranch, 'integration');
});

test('3071 old launcher state reads default metadata once on tick', async t => {
  const f = await fixture(t); assert.equal((await f.invoke('start')).exitCode,0);
  const state=f.state(); delete state.defaultBranch; delete state.baseBranch;
  writeFileSync(f.stateFile(),JSON.stringify(state));
  f.status=304;
  await f.tick(); await f.tick();
  assert.equal(f.state().baseBranch,'trunk');
  assert.equal(f.runs.filter(([cmd,args])=>cmd==='gh' && args[0]==='repo').length,2);
});

for (const stop of [false, true]) for (const configured of [undefined, 'integration/topic']) {
  test(`3071 repair start refreshes default with stop=${stop}, base=${configured ?? 'default'}`, async t => {
    const f = await fixture(t);
    writeFileSync(join(f.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', ...(configured ? { base: configured } : {}) } }));
    assert.equal((await f.invoke('start')).exitCode, 0);
    const original = f.ports.run;
    let metadataReads = 0;
    f.ports.run = async (command, args, options) => {
      if (command === 'gh' && args[0] === 'repo') {
        metadataReads++;
        return { code: 0, stdout: JSON.stringify({ nameWithOwner: 'owner/repo', defaultBranchRef: { name: 'new-default' } }), stderr: '' };
      }
      return original(command, args, options);
    };
    f.status = 304;
    const packetsBefore = f.prompts.length;
    if (stop) assert.equal((await f.invoke('stop')).exitCode, 0);
    const started = await f.invoke('start');
    assert.equal(started.exitCode, 0, started.message);
    assert.equal(f.state().defaultBranch, 'new-default');
    const expected = configured ?? 'new-default';
    assert.equal(f.state().baseBranch, expected);
    assert.ok(started.message.includes(expected));
    if (!configured) assert.equal(f.prompts.length, packetsBefore + 1, 'changed base reaches the coordinator with unchanged issues');
    const packet = JSON.parse(f.prompts.at(-1).trimEnd().split('\n').at(-1));
    assert.equal(packet.baseBranch, expected);
    assert.equal(packet.workflow.baseBranch, expected);
    await f.tick(); await f.tick();
    for (const all of [false, true]) {
      const status = await f.invoke('status', { all });
      assert.equal(status.exitCode, 0, status.message);
      assert.ok(status.message.includes(expected));
    }
    assert.equal(metadataReads, 1, 'one refresh per explicit start; ticks and status reuse it');
  });
}

test('3071 repair failed default refresh refuses restart without using saved metadata', async t => {
  const f = await fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  assert.equal((await f.invoke('stop')).exitCode, 0);
  const saved = f.state(), packets = f.prompts.length, starts = f.timers.filter(([action]) => action === 'start').length;
  const original = f.ports.run;
  f.ports.run = (command, args, options) => command === 'gh' && args[0] === 'repo'
    ? Promise.resolve({ code: 1, stdout: '', stderr: 'synthetic metadata failure' })
    : original(command, args, options);
  assert.equal((await f.invoke('start')).exitCode, 1);
  assert.deepEqual(f.state(), saved);
  assert.equal(f.prompts.length, packets);
  assert.equal(f.timers.filter(([action]) => action === 'start').length, starts);
});

test('3071 repair refreshed packet base agrees with automatic workflow startup', async t => {
  const f = await fixture(t), workflow = await automaticFixture(t);
  const original = f.ports.run;
  let defaultBranch = 'main';
  f.ports.run = (command, args, options) => command === 'gh' && args[0] === 'repo'
    ? Promise.resolve({ code: 0, stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: defaultBranch } }), stderr: '' })
    : original(command, args, options);
  assert.equal((await f.invoke('start')).exitCode, 0);
  assert.equal((await f.invoke('stop')).exitCode, 0);
  defaultBranch = 'new-default'; f.status = 304;
  workflow.git(workflow.source, 'update-ref', 'refs/remotes/origin/new-default', workflow.git(workflow.source, 'rev-parse', 'HEAD'));
  const workflowExec = workflow.automaticPorts.execFile;
  workflow.automaticPorts.execFile = (file, args, options) => file === 'gh' && args[0] === 'repo'
    ? Promise.resolve({ stdout: JSON.stringify({ nameWithOwner: 'example/project', defaultBranchRef: { name: defaultBranch }, url: 'https://github.com/example/project' }) })
    : workflowExec(file, args, options);
  const restarted = await f.invoke('start');
  assert.equal(restarted.exitCode, 0, restarted.message);
  const packet = JSON.parse(f.prompts.at(-1).trimEnd().split('\n').at(-1));
  const started = await workflow.begin({ base: packet.workflow.baseBranch });
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(workflow.record().baseBranch, 'new-default');
  assert.equal(packet.baseBranch, workflow.record().baseBranch);
  assert.equal(workflow.record().baseSha, workflow.git(workflow.source, 'rev-parse', 'refs/remotes/origin/new-default'));
});

// #3091 native discovery must not turn incomplete saved rows into a tick failure.
for (const [name, root] of [['absent', undefined], ['null', null], ['number', 42], ['object', {}]])
  test(`3091 integration verdict scan keeps incomplete ${name} root rows unknown`, async t => {
    const f = await fixture(t);
    f.ports.env = {HOME: f.home, PDD_SUITE_QUEUE: join(f.dir, 'suite-queue'), PDD_INTERPRETER_QUEUE: join(f.dir, 'interpreter-queue')};
    assert.equal((await f.invoke('start', {env: f.ports.env})).exitCode, 0);
    const folder = join(f.cwd, '.git', 'pdd', 'runs', '901'); mkdirSync(folder, {recursive: true});
    const file = join(folder, 'status.json');
    const bytes = JSON.stringify({v: 1, number: 901, repo: 'owner/repo', state: 'running', root});
    writeFileSync(file, bytes);
    const before = f.prompts.length;
    f.time += 30 * 60 * 1000;
    await assert.doesNotReject(async () => {assert.equal((await f.tick()).exitCode, 0);});
    assert.equal(f.prompts.length, before);
    assert.equal(f.state().interpreterPattern.streak, 0);
    assert.equal(f.state().interpreterPattern.verdictAt, undefined);
    assert.equal(readFileSync(file, 'utf8'), bytes);
  });


for(const damage of ['missing','non-boolean'])test(`3138 repair 1: discovery alerts once for ${damage} recommendation and keeps intake`,async t=>{
  const f=await fixture(t);assert.equal((await f.invoke('start')).exitCode,0);
  const state=f.state(),runDir=join(f.dir,'audit-run'),folder=join(runDir,'audits'),file=join(folder,'23.json');
  mkdirSync(folder,{recursive:true});
  const record={schema:'pdd.audit.v1',runId:'audit-run',pr:23,merge:'a'.repeat(40),parent:'b'.repeat(40),at:f.time,state:'recorded',completedAt:f.time,
    chat:{agent:'codex',configDir:null,startedAt:f.time,session:{id:'11111111-1111-4111-8111-111111111111'}},
    result:{verdict:'BAD',kind:'',summary:'Synthetic gap',evidence:'Missing scope',...(damage==='non-boolean'?{revert:'false'}:{})},
    comment:{state:'unknown',at:f.time},revert:{state:'unknown',at:f.time}};
  const bytes=JSON.stringify(record);writeFileSync(file,bytes);writeFileSync(`${file}.revert`,'');
  const run={number:17,repo:state.repo,commonDir:join(f.cwd,'.git'),sourceRoot:f.cwd,root:f.cwd,baseBranch:'trunk',runDir,runId:record.runId,
    state:'completed',automaticOrigin:{repository:state.repo,machine:state.machine,coordinatorId:state.coordinatorId},pr:[{number:23,state:'merged'}]};
  f.ports.listRuns=async()=>[run];f.ports.auditStateRoot=join(f.dir,'audit-state');
  const alerts=[];f.ports.sendAlert=async input=>{alerts.push(input);return {exitCode:0,message:`Alert sent for #${input.issue} ${input.kind}; the webhook confirmed it.`};};
  f.issues=[issue(18)];f.time+=1000;
  for(let n=0;n<2;n++)assert.equal((await f.tick()).exitCode,0);
  assert.equal(alerts.length,1,'DISCOVERY_MUST_SEND_ONE_RECOMMENDATION_DECISION_ALERT');
  assert.equal(alerts[0].kind,'decision');
  const alert=JSON.parse(alerts[0].text);assert.match(alert.cause,/recommendation.*(missing|unavailable)/i);
  assert.match(alert.need,/keep.*merge.*finish/i);assert.ok(alert.need.includes(`git revert -m 1 ${record.merge}`));assert.ok(alert.need.includes(run.baseBranch));
  assert.deepEqual(f.state().auditHolds,[{number:17,pr:23,cause:'audit-evidence-invalid'}]);
  const packets=f.prompts.map(text=>JSON.parse(text.trim().split('\n').at(-1)));
  assert.ok(packets.some(p=>p.issues?.some(i=>i.number===18&&i.eligible)));
  assert.equal(packets.some(p=>p.timeRules?.some(r=>r.kind==='post-merge-audit')),false);
  assert.equal(readFileSync(file,'utf8'),bytes);assert.deepEqual(readdirSync(folder).sort(),['23.json','23.json.revert']);
  assert.equal(f.runs.filter(([command,args])=>command==='git'&&args.includes('revert')||command==='gh'&&args.includes('create')).length,0);
});

test('3138 repair 2: discovery retains each damaged PR hold and sends each decision once',async t=>{
  const f=await fixture(t);assert.equal((await f.invoke('start')).exitCode,0);
  const state=f.state(),runDir=join(f.dir,'audit-run'),folder=join(runDir,'audits');mkdirSync(folder,{recursive:true});
  const run={number:17,repo:state.repo,commonDir:join(f.cwd,'.git'),sourceRoot:f.cwd,root:f.cwd,baseBranch:'trunk',runDir,runId:'audit-run',
    state:'completed',automaticOrigin:{repository:state.repo,machine:state.machine,coordinatorId:state.coordinatorId},
    pr:[23,24].map(number=>({number,state:'merged',mergeSha:String(number===23?'a':'c').repeat(40)}))};
  const originals=run.pr.map(pr=>{
    const record={schema:'pdd.audit.v1',runId:run.runId,pr:pr.number,merge:pr.mergeSha,parent:'b'.repeat(40),at:f.time,state:'recorded',completedAt:f.time,
      chat:{agent:'codex',configDir:null,startedAt:f.time,session:{id:'11111111-1111-4111-8111-111111111111'}},
      result:{verdict:'BAD',kind:'',summary:'Synthetic gap',evidence:'Missing scope'}};
    const file=join(folder,`${pr.number}.json`),bytes=JSON.stringify(record);writeFileSync(file,bytes);writeFileSync(`${file}.revert`,'');return {file,bytes};
  });
  f.ports.listRuns=async()=>[run];f.ports.auditStateRoot=join(f.dir,'audit-state');
  const alerts=[];f.ports.sendAlert=async input=>{alerts.push(input);return {exitCode:0,message:`Alert sent for #${input.issue} ${input.kind}; the webhook confirmed it.`};};
  f.issues=[issue(18)];f.time+=1000;
  for(let n=0;n<2;n++)assert.equal((await f.tick()).exitCode,0);
  assert.equal(alerts.length,2,'DISCOVERY_NEEDS_EACH_PR_DECISION_ALERT');
  for(const pr of run.pr)assert.equal(alerts.filter(a=>JSON.parse(a.text).cause.includes(`PR #${pr.number} (${pr.mergeSha})`)).length,1);
  assert.deepEqual(f.state().auditHolds,run.pr.map(pr=>({number:17,pr:pr.number,cause:'audit-evidence-invalid'})));
  const packets=f.prompts.map(text=>JSON.parse(text.trim().split('\n').at(-1)));
  assert.ok(packets.some(p=>p.issues?.some(i=>i.number===18&&i.eligible)));
  assert.equal(packets.some(p=>p.timeRules?.some(r=>r.kind==='post-merge-audit')),false);
  for(const {file,bytes} of originals){assert.equal(readFileSync(file,'utf8'),bytes);assert.equal(readFileSync(`${file}.revert`,'utf8'),'');}
  assert.equal(f.runs.filter(([command,args])=>command==='git'&&args.includes('revert')||command==='gh'&&args.includes('create')).length,0);
});

for (const damage of ['json','schema','attempt','file','folder']) test(`3111 repair 2: ${damage} audit evidence holds without blocking tick delivery`, async t => {
  const f = await fixture(t);await f.invoke('start');
  const state=f.state(),runDir=join(f.dir,'audit-run'),folder=join(runDir,'audits'),file=join(folder,'23.json');
  mkdirSync(folder,{recursive:true});
  const record={schema:'pdd.audit.v1',runId:'audit-run',pr:23,merge:'a'.repeat(40),parent:'b'.repeat(40),at:f.time,state:'recorded',completedAt:f.time,chat:{agent:'codex',configDir:null,startedAt:f.time,session:{id:'11111111-1111-4111-8111-111111111111'}},result:{verdict:'OK',kind:'',summary:'Observed',evidence:'Synthetic evidence',revert:false},comment:{state:'sent',at:f.time,value:'confirmed'}};
  writeFileSync(file,JSON.stringify(record));
  if(damage==='json')writeFileSync(file,'{');
  if(damage==='schema')writeFileSync(file,'null');
  if(damage==='attempt')writeFileSync(file,JSON.stringify({...record,runId:'other-attempt'}));
  f.ports.fs={...nativeFs,
    readFileSync:(path,...args)=>{if(damage==='file' && path===file)throw Object.assign(Error('synthetic denied'),{code:'EACCES'});return nativeFs.readFileSync(path,...args);},
    readdirSync:(path,...args)=>{if(damage==='folder' && path===folder)throw Object.assign(Error('synthetic denied'),{code:'EACCES'});return nativeFs.readdirSync(path,...args);},
  };
  f.ports.listRuns=async()=>[{number:17,repo:state.repo,sourceRoot:f.cwd,runDir,runId:'audit-run',state:'completed',automaticOrigin:{repository:state.repo,machine:state.machine,coordinatorId:state.coordinatorId},pr:[{number:23,state:'merged'},{number:24,state:'merged'}]}];
  const cause=damage==='file'?'audit-evidence-unreadable':damage==='folder'?'audit-folder-unreadable':damage==='attempt'?'audit-attempt-mismatch':'audit-evidence-invalid';
  const expected=[{number:17,pr:23,cause},...(damage!=='attempt'?[{number:17,pr:24,cause}]:[])];
  f.issues=[issue(18)];f.time+=1000;
  for(let n=0;n<2;n++) {
    const tick=await f.tick().catch(error=>({exitCode:1,message:error.message}));
    assert.equal(tick.exitCode,0,'AUDIT_SCAN_INTAKE: evidence damage must not abort the tick');
    assert.deepEqual(f.state().auditHolds,expected);
  }
  const packets=f.prompts.flatMap(text=>{try{return [JSON.parse(text.trim().split('\n').at(-1))];}catch{return [];}});
  assert.ok(packets.some(p=>p.issues?.some(i=>i.number===18 && i.eligible)));
  const rules=packets.flatMap(p=>p.timeRules??[]).filter(r=>r.kind==='post-merge-audit');
  assert.ok(rules.every(r=>r.pr!==23));
  assert.equal(rules.some(r=>r.pr===24),damage==='attempt');
  for(const options of [{},{all:true}]) {
    const status=await f.invoke('status',options);assert.equal(status.exitCode,0);assert.ok(status.message.includes(cause));
  }
  const json=await f.invoke('status',{json:true});
  assert.deepEqual(JSON.parse(json.message).auditHolds,[{repository:state.repo,cwd:f.cwd,holds:expected}]);
  assert.equal(readFileSync(file,'utf8'),damage==='json'?'{':damage==='schema'?'null':JSON.stringify({...record,...(damage==='attempt'?{runId:'other-attempt'}:{})}));
  f.ports.fs=nativeFs;writeFileSync(file,JSON.stringify(record));
  await f.tick();assert.deepEqual(f.state().auditHolds,[]);
});

for (const owner of ['current','previous']) for(const saved of [false,true]) test(`review: pending completed audit survives ${owner} coordinator with saved verdict ${saved}`,async t=>{
  const f=await fixture(t);assert.equal((await f.invoke('start')).exitCode,0);
  const state=f.state(),runDir=join(f.dir,'completed-run');mkdirSync(runDir);
  f.ports.listRuns=async()=>[{number:17,repo:state.repo,sourceRoot:f.cwd,root:f.cwd,runDir,runId:'previous-completed-run',state:'completed',automaticOrigin:{repository:state.repo,machine:state.machine,coordinatorId:owner==='current'?state.coordinatorId:'previous-coordinator'},pr:[{number:23,state:'merged'}]}];
  if(saved) {
    mkdirSync(join(runDir,'audits'));
    writeFileSync(join(runDir,'audits','23.json'),JSON.stringify({schema:'pdd.audit.v1',repository:state.repo.toLowerCase(),runId:'previous-completed-run',pr:23,merge:'a'.repeat(40),parent:'b'.repeat(40),at:f.time,state:'recorded',completedAt:f.time,chat:{agent:'codex',configDir:null,startedAt:f.time,session:{id:'11111111-1111-4111-8111-111111111111'}},result:{verdict:'BAD',kind:'',summary:'Synthetic defect',evidence:'Native assertion fails',revert:true},comment:{state:'sent',at:f.time,value:'confirmed'}}));
  }
  f.issues=[issue(18)];f.time+=1000;
  assert.equal((await f.tick()).exitCode,0);
  const packets=f.prompts.flatMap(text=>{try{return [JSON.parse(text.trim().split('\n').at(-1))];}catch{return [];}});
  const rules=packets.flatMap(p=>p.timeRules??[]).filter(r=>r.kind==='post-merge-audit');
  assert.ok(rules.some(r=>r.number===17&&r.pr===23),'PREVIOUS_COORDINATOR_MUST_NOT_LOSE_COMPLETED_AUDIT');
});

for(const boundary of ['disabled','foreign-repository','foreign-checkout','foreign-machine','shared-reservation']) test(`completed audit replacement retains ${boundary} guard`,async t=>{
  const f=await fixture(t);assert.equal((await f.invoke('start')).exitCode,0);
  const state=f.state(),runDir=join(f.dir,'completed-run');mkdirSync(runDir);
  const run={number:17,repo:state.repo,sourceRoot:f.cwd,root:f.cwd,runDir,runId:'previous-completed-run',state:'completed',automaticOrigin:{repository:state.repo,machine:state.machine,coordinatorId:'previous-coordinator'},pr:[{number:23,state:'merged'}]};
  if(boundary==='disabled')writeFileSync(join(f.cwd,'pdd.json'),JSON.stringify({autopilot:{mode:'auto',audit:false}}));
  if(boundary==='foreign-repository')run.automaticOrigin.repository='other/repo';
  if(boundary==='foreign-checkout')run.sourceRoot=join(f.dir,'other-checkout');
  if(boundary==='foreign-machine')run.automaticOrigin.machine='other-machine';
  let authority;
  if(boundary==='shared-reservation') {
    const record={schema:'pdd.audit.v1',repository:state.repo.toLowerCase(),runId:run.runId,pr:23,merge:'a'.repeat(40),parent:'b'.repeat(40),at:f.time,state:'unknown',chat:{agent:'codex',configDir:null,startedAt:f.time}};
    const folder=join(f.dir,'shared-audits');f.ports.auditStateRoot=folder;mkdirSync(join(folder,'records'),{recursive:true});
    authority=join(folder,'records',createHash('sha256').update(JSON.stringify([record.runId,record.pr,record.merge])).digest('hex')+'.json');
    writeFileSync(authority,JSON.stringify(record));
  }
  const before=authority?readFileSync(authority,'utf8'):null;
  f.ports.listRuns=async()=>[run];f.issues=[issue(18)];f.time+=1000;
  assert.equal((await f.tick()).exitCode,0);
  const packets=f.prompts.flatMap(text=>{try{return [JSON.parse(text.trim().split('\n').at(-1))];}catch{return [];}});
  assert.equal(packets.flatMap(p=>p.timeRules??[]).some(r=>r.kind==='post-merge-audit'),false);
  if(authority)assert.equal(readFileSync(authority,'utf8'),before);
});


test('audit tick discovers completed runs through the injected Git executor', async t => {
  const f = await fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  const state = f.state(), commonDir = join(f.cwd, '.git'), runDir = join(commonDir, 'pdd', 'runs', '17');
  mkdirSync(runDir, {recursive: true});
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({v: 1, number: 17,
    repo: state.repo, sourceRoot: f.cwd, root: f.cwd, commonDir, runDir,
    runId: 'synthetic-completed-audit', state: 'completed', areas: [], chats: [],
    automaticOrigin: {repository: state.repo, coordinatorId: 'previous', machine: state.machine},
    pr: [{number: 23, state: 'merged'}]}));
  f.prompts.length = 0;
  const before = f.runs.length;
  assert.equal((await f.tick()).exitCode, 0);
  const rules = f.prompts.flatMap(text => JSON.parse(text.trim().split('\n').at(-1)).timeRules ?? []);
  assert.ok(rules.some(row => row.kind === 'post-merge-audit' && row.number === 17 && row.pr === 23));
  assert.ok(f.runs.slice(before).some(([file, args]) => file === 'git' && args.includes('--git-common-dir')));
  assert.equal(f.runs.slice(before).filter(([file]) => file === 'gh').length, 0, 'local audit discovery needs no GitHub read');
});


test('start: custody preflight uses the original healthy profile with a signed-out caller',async t=>{
  const f=await fixture(t),profile=join(f.home,'original-profile');
  f.ports.selectAgent=async()=>({id:'codex',kind:'codex',command:'codex',env:{CODEX_HOME:profile}});
  f.accountReady=env=>env.CODEX_HOME===profile;
  assert.equal((await f.invoke('start')).exitCode,0);
  const original=f.state(),launch=original.ownerLaunch,artifact=join(f.dir,'custody.json');
  writeFileSync(artifact,JSON.stringify({repository:original.repo,sourceRoot:f.cwd,coordinatorId:original.coordinatorId,machine:original.machine,activation:original.activatedAt,paneId:original.paneId,workspaceId:original.workspaceId,agent:launch.profile.agent,home:launch.profile.home,definitionHome:launch.profile.definitionHome,configHome:launch.profile.configHome,launchStartedAt:launch.startedAt}));
  f.ports.listRuns=async()=>[];
  f.ports.selectAgent=async()=>({id:'codex',kind:'codex',command:'codex',env:{}});
  const r=await f.invoke('start',{resumeCustody:artifact,env:{HOME:f.home,PATH:process.env.PATH,CODEX_HOME:join(f.dir,'signed-out-caller')}});
  assert.equal(r.exitCode,0,r.message);
  assert.equal(f.state().coordinatorId,original.coordinatorId);assert.equal(f.state().environment.CODEX_HOME,profile);
  assert.ok(f.doctorAccounts.every(env=>env.CODEX_HOME===profile));
});

test('start: a custom Claude definition supplies HOME and config environment to doctor and startup checks',async t=>{
  const f=await fixture(t),home=join(f.dir,'invocation home'),config=join(f.dir,'Claude config');
  mkdirSync(join(f.home,'.config','pdd'),{recursive:true});
  writeFileSync(join(f.home,'.config','pdd','agents.json'),JSON.stringify({include_defaults:false,agents:[{name:'Claude profile',kind:'claude',command:'claude',env:{HOME:home,CLAUDE_CONFIG_DIR:config,CODEX_HOME:join(home,'codex')}}]}));
  delete f.ports.selectAgent;
  const run=f.ports.run;
  f.ports.run=async(file,args,options)=>{
    if(file==='claude')return {code:0,stdout:'{"loggedIn":true}',stderr:''};
    if(file==='gh' && args[0]==='auth') {assert.equal(options.env.HOME,home);assert.equal(options.env.CLAUDE_CONFIG_DIR,config);}
    return run(file,args,options);
  };
  const r=await f.invoke('start');assert.equal(r.exitCode,0,r.message);
  assert.equal(f.state().agent.kind,'claude');assert.equal(f.state().environment.HOME,home);assert.equal(f.state().environment.CLAUDE_CONFIG_DIR,config);assert.equal(f.state().definitionHome,f.home);
});


test('start: an absent selected provider directory masks an unrelated ambient profile',async t=>{
  const f=await fixture(t),ambient=process.env.CODEX_HOME;
  process.env.CODEX_HOME=join(f.dir,'ambient-profile');
  t.after(()=>{if(ambient===undefined)delete process.env.CODEX_HOME;else process.env.CODEX_HOME=ambient;});
  const run=f.ports.run;
  f.ports.run=async(file,args,options)=>{
    if(file==='gh' && args[0]==='auth')assert.equal(options.env.CODEX_HOME,undefined);
    return run(file,args,options);
  };
  const r=await f.invoke('start');assert.equal(r.exitCode,0,r.message);
  assert.equal(f.state().environment.CODEX_HOME,undefined);
});

// Native-start outcomes are the preservation contract. An optional disposable
// base checkout repeats the same states against its real public launcher too.
const admissionStates=[
  {name:'fresh with room',baseAdmitted:true},
  {name:'fresh with full workflow session',panes:1,budget:'1',baseAdmitted:false},
  {name:'fresh with unlimited workflow session',panes:2,budget:'0',baseAdmitted:true},
  {name:'fresh with invalid budget',budget:'invalid',baseAdmitted:false},
  {name:'fresh with malformed workflow inventory',invalidInventory:true,baseAdmitted:false},
  {name:'fresh with unreadable status but native inventory available',statusUnavailable:true,baseAdmitted:true},
  {name:'saved idle coordinator and full workflow session',restart:true,panes:1,budget:'1',baseAdmitted:true},
  {name:'saved working coordinator and overfull workflow session',restart:true,status:'working',panes:2,budget:'1',baseAdmitted:true},
  {name:'saved blocked coordinator and invalid budget',restart:true,status:'blocked',budget:'invalid',baseAdmitted:true},
  {name:'saved coordinator and unreadable workflow inventory',restart:true,invalidInventory:true,baseAdmitted:true},
  {name:'saved target observation unavailable',restart:true,unavailable:true,panes:1,budget:'1',baseAdmitted:true},
  {name:'optional capacity endpoint returns JSON 404',runtime404:true,baseAdmitted:true},
  {name:'saved coordinator with JSON 404 and full workflow session',restart:true,runtime404:true,panes:1,budget:'1',baseAdmitted:true},
  {name:'missing sign-in is the new preflight refusal',signedOut:true,baseAdmitted:true},
];
for(const row of admissionStates)test(`start admission parity: ${row.name}`,async t=>{
  const prepare=async module=>{
    const f=await fixture(t);if(module)f.module=module;
    f.ports.allRuns=()=>[];
    f.ports.tidyRuns=async()=>({closed:0});
    f.ports.workflowHerdr=async args=>{
      if(args[0]==='status') {
        if(row.statusUnavailable)throw Object.assign(Error('unreadable'),{code:'transport_error'});
        return {running:true};
      }
      assert.deepEqual(args.filter(a=>a!=='--json'),['pane','list']);
      return {result:{type:'pane_list',panes:f.workflowPanes??[]}};
    };
    const original=f.ports.doctorPorts;
    f.ports.doctorPorts=input=>{
      const p=original(input),run=p.run;
      p.run=async(file,args,options)=>{
        if(file==='herdr'&&args[0]==='--session') {
          assert.ok(['pdd','pdd-autopilot'].includes(args[1]));
          (f.sessionReads??=[]).push(args);
          try {
            const value=await (args[1]==='pdd'?f.ports.workflowHerdr:f.ports.herdr)(args.slice(2));
            return {code:0,stdout:JSON.stringify(value),stderr:''};
          } catch(error) {return {code:1,stdout:'',stderr:JSON.stringify({error:{code:error.code}})};}
        }
        return run(file,args,options);
      };
      if(row.runtime404)p.fetch=async()=>new Response('{"error":{"code":"not-found"}}',{status:404});
      return p;
    };
    const env={HOME:f.home,PATH:'/synthetic/bin'};
    if(row.restart)assert.equal((await f.invoke('start',{env})).exitCode,0);
    const prior=row.restart?f.state():null;
    f.agentStatus=row.status;
    if(row.unavailable) {
      const herdr=f.ports.herdr;
      f.ports.herdr=async args=>{if(args[0]==='agent'&&args[1]==='get')throw Object.assign(Error('unreadable'),{code:'transport_error'});return herdr(args);};
    }
    f.workflowPanes=row.invalidInventory?[{}]:Array.from({length:row.panes??0},(_,i)=>({pane_id:`personal-${i}`,workspace_id:'personal',tab_id:`tab-${i}`,terminal_id:`terminal-${i}`}));
    if(row.signedOut)f.accountReady=()=>false;
    const result=await f.invoke('start',{env:{...env,...(row.budget===undefined?{}:{PDD_HERDR_PANE_BUDGET:row.budget})}});
    if(prior&&result.exitCode===0) {
      assert.equal(f.state().paneId,prior.paneId);assert.equal(f.state().coordinatorId,prior.coordinatorId);
    }
    return result;
  };
  let baseAdmitted=row.baseAdmitted;
  if(process.env.PDD_ADMISSION_BASE_ROOT) {
    const {pathToFileURL}=await import('node:url');
    const base=await import(pathToFileURL(join(process.env.PDD_ADMISSION_BASE_ROOT,'src/autopilot-launcher.mjs')));
    const result=await prepare(base);
    baseAdmitted=result.exitCode===0;
    assert.equal(baseAdmitted,row.baseAdmitted,`native base: ${result.message}`);
  }
  const result=await prepare();
  assert.equal(result.exitCode===0,baseAdmitted&&!row.signedOut,result.message);
});


test('start: guarded cleanup reclaims a finished workflow shell after its chat has closed',async t=>{
  const {fixture:workflowFixture}=await import('./helpers/workflow-runner-fixture.mjs');
  const {tidyRuns}=await import('../src/workflow-runner.mjs');
  const {allRuns}=await import('../src/workflow-runs.mjs');
  const w=await workflowFixture(t);
  assert.equal((await w.run()).exitCode,0);
  const run=w.record();run.state='completed';run.chats[0].endedAt=w.clock;
  writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run));
  w.tick(16*60_000);w.herdr.idle();
  const shell=w.herdr.paneOf(run.layout);shell.agent={agent:'codex',agent_status:'working'};
  const cleaned=await tidyRuns({},w.ports);
  assert.equal(cleaned.closed,1);assert.equal(cleaned.kept,1);
  assert.ok(!w.herdr.paneOf(run.chats[0]));assert.ok(w.herdr.paneOf(run.layout));
  shell.agent=null;
  const paneCount=w.herdr.panes.length;
  assert.ok(paneCount>0);
  const f=await fixture(t);
  f.ports.stateDir=w.state;
  assert.equal(allRuns({cancelled:true},{stateDir:w.state}).length,1);
  f.ports.tidyRuns=options=>tidyRuns(options,w.ports);
  f.ports.workflowHerdr=w.herdr.herdr;
  const original=f.ports.doctorPorts;
  f.ports.doctorPorts=input=>{
    const p=original(input),read=p.run;
    p.run=async(file,args,options)=>{
      if(file==='herdr'&&args[0]==='--session'&&args[1]==='pdd')return {code:0,stdout:JSON.stringify(await w.herdr.herdr(args.slice(2))),stderr:''};
      return read(file,args,options);
    };
    return p;
  };
  const result=await f.invoke('start',{env:{HOME:f.home,PATH:process.env.PATH,PDD_HERDR_PANE_BUDGET:String(paneCount)}});
  assert.equal(result.exitCode,0,result.message);
  assert.equal(w.herdr.panes.length,paneCount-1);
  assert.ok(!w.herdr.paneOf(run.layout));
});
