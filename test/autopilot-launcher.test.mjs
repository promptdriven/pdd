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
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: options.mode ?? 'auto', trust: ['helper'], label: 'pdd:autopilot' } }));
  const f = { dir, cwd, home, time: Date.parse('2026-11-04T00:00:00Z'), polls: [], prompts: [], runs: [], timers: [], comments: [], ack: [], issues: [], etag: '"one"', active: false };
  f.ports = {
    ...healthyMachine, checkCapacityPorts: isolatedCheckCapacity(dir), stateRoot: join(home, 'state'), now: () => f.time,
    // These fakes stand for a checkout where pdd workflows can start (#3050).
    allocationCheck: async () => ({ state: 'ready', message: '' }),
    readRunProgress: async () => f.runProgress ?? [],
    warn: text => { (f.warnings ??= []).push(text); },
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }),
    pathDiagnostic: () => [],
    run: async (command, args, options = {}) => {
      f.runs.push([command, args]);
      if (command === 'git') return { code: 0, stdout: (args.includes('--git-common-dir') ? join(cwd, '.git') : cwd) + '\n', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo","defaultBranchRef":{"name":"trunk"},"url":"https://github.com/owner/repo"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api' && args.includes('graphql')) {
        const {query,variables} = JSON.parse(options.input ?? '{}');
        if (typeof query === 'string' && !/\bmutation\b/.test(query)) {
          const rows = {};
          for (const [name,number] of Object.entries(variables ?? {})) if (/^n\d+$/.test(name)) {
            const row = f.issues.find(row=>row.number===number);
            rows[`i${name.slice(1)}`] = row ? {url:row.html_url,number:row.number,labels:{nodes:row.labels.map(label=>({name:typeof label==='string'?label:label.name})),pageInfo:{hasNextPage:false}}} : null;
          }
          return {code:0,stdout:JSON.stringify({data:{repository:rows}}),stderr:''};
        }
      }
      if (command === 'gh' && args[0] === 'api' && /^repos\/[^/]+\/[^/]+\/issues\/[1-9]\d*$/.test(args.find(arg => String(arg).startsWith('repos/')) ?? '')) {
        const number = Number(args.find(arg => String(arg).startsWith('repos/')).split('/').at(-1));
        return {code:0,stdout:'HTTP/2.0 200 OK\r\n\r\n'+JSON.stringify(f.issues.find(row => row.number === number) ?? {number,labels:[]}),stderr:''};
      }
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

test('add marks every named old issue with exactly pdd:autopilot', async t => {
  const f = await fixture(t);
  assert.equal((await f.invoke('add', { issues: ['12', '15'] })).exitCode, 0);
  assert.equal(f.ack.filter(args => args.some(x => String(x).includes('pdd:autopilot'))).length, 3);
});

test('a missing Gemini sign-in is not inferred from a successful version command', async t => {
  const f = await fixture(t); delete f.ports.selectAgent; const run = f.ports.run;
  f.ports.run = async (command, args, opts) => ['codex', 'claude', 'agy', 'gemini'].includes(command) ? { code: command === 'gemini' ? 0 : 1, stdout: 'installed', stderr: '' } : run(command, args, opts);
  const result = await f.invoke('start'); assert.equal(result.exitCode, 1); assert.match(result.message, /Sign in/);
  assert.equal(f.prompts.length, 0);
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

test('a later stop retries timer cleanup after a transient failure', async t => {
  const f = await fixture(t); await f.invoke('start');
  const timer = f.ports.timer; let attempts = 0;
  f.ports.timer = async (action, state) => { if (action === 'stop' && ++attempts === 1) throw Error('transient user bus failure'); return timer(action, state); };
  assert.equal((await f.invoke('stop')).exitCode, 1); assert.equal(f.state().enabled, false);
  assert.equal((await f.invoke('stop')).exitCode, 0); assert.equal(attempts, 2);
  assert.equal(f.state().timerInstalled, false);
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

const packet = f => JSON.parse(f.prompts.at(-1).trim().split('\n').at(-1));
const hour = 60 * 60 * 1000;

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
// Issue 3037 second review F1: recovery after an uncertain send uses the saved pane, so the saved
// terminal must still be there; a pane id that another terminal has gets no recovery prompt.
// Issue 2903: a `cd` in the person's shell startup file moves each new Herdr pane's shell out of the repository.
// #3067: capacity reads use the same fake machine on start, tick and status.
// #3091 native discovery must not turn incomplete saved rows into a tick failure.
// Native-start outcomes are the preservation contract. An optional disposable
// base checkout repeats the same states against its real public launcher too.
const admissionStates=[
  {name:'fresh with room',baseAdmitted:true},
  ...['observe','auto'].flatMap(mode=>[
    {name:`different PATH install in ${mode}`,mode,prerequisite:'path',baseAdmitted:true},
    {name:`read-only repository in ${mode}`,mode,prerequisite:'github-permission',baseAdmitted:true},
    {name:`disabled merge methods in ${mode}`,mode,prerequisite:'merge-method',baseAdmitted:true},
  ]),
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
test('#3231 start --share: the timer files run Autopilot at the lowest priority (CPUWeight 1, or 100 at a share of 100) with MemoryHigh at the share; a bad share changes nothing', async t => {
  for (const [platform, share] of [['darwin', undefined], ['linux', undefined], ['linux', '70'], ['linux', '100']]) {
    const f = await fixture(t, {tempPrefix: 'pdd-autopilot-nice-'}); delete f.ports.timer; f.ports.platform = platform; f.ports.uid = 123;
    const env = { HOME: f.home, PATH: '/fixture/bin', XDG_CONFIG_HOME: join(f.home, '.config') };
    const run = f.ports.run;
    f.ports.run = async (command, args, opts) => ['systemctl', 'launchctl', 'loginctl'].includes(command) ? { code: 0, stdout: command === 'loginctl' ? 'yes\n' : '', stderr: '' } : run(command, args, opts);
    assert.equal((await f.invoke('start', { env, label: 'pdd:autopilot', ...(share ? { share } : {}) })).exitCode, 0);
    const folder = platform === 'linux' ? join(f.home, '.config', 'systemd', 'user') : join(f.home, 'Library', 'LaunchAgents');
    const text = () => readFileSync(join(folder, readdirSync(folder).find(x => x.endsWith(platform === 'linux' ? '.service' : '.plist'))), 'utf8');
    if (platform === 'darwin') { assert.match(text(), /<key>Nice<\/key><integer>19<\/integer>/); continue; }
    assert.match(text(), /^Nice=19$/m); assert.match(text(), new RegExp(`^CPUWeight=${share === '100' ? 100 : 1}$`, 'm')); assert.match(text(), /^KillMode=process$/m);
    assert.match(text(), new RegExp(`^MemoryHigh=${share ?? 50}%$`, 'm'));
    assert.equal(f.state().share, share ? Number(share) : undefined);
    if (share === '70') {
      assert.equal((await f.invoke('start', { env, label: 'pdd:autopilot' })).exitCode, 0);
      assert.equal(f.state().share, 70, 'a later start without --share keeps it'); assert.match(text(), /^MemoryHigh=70%$/m);
      for (const bad of ['0', '101', '7.5', 'half']) {
        const refused = await f.invoke('start', { env, label: 'pdd:autopilot', share: bad });
        assert.equal(refused.exitCode, 2, bad); assert.match(refused.message, /--share with a whole percent from 1 to 100/);
        assert.equal(f.state().share, 70, `${bad} changes nothing`);
      }
    }
  }
});
