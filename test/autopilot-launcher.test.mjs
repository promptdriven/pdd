import './helpers/test-home.mjs';
import { isolatedCheckCapacity } from './helpers/check-machine.mjs';
import {healthyDoctorPorts} from './helpers/doctor-fixture.mjs';
import { healthyMachine } from './helpers/healthy-machine.mjs';
import test from 'node:test';
import * as nativeFs from 'node:fs';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync, statSync, utimesSync, existsSync, realpathSync, renameSync, symlinkSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
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
    ports.files.readFileSync=path=>path.includes('/skills/')?'skill':path.endsWith('/oauth_creds.json')?(f.ports.selectAgent?'{"refresh_token":"fixture"}':nativeFs.readFileSync(path,'utf8')):read(path);
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
  f.stateFile = () => join(f.ports.stateRoot, readdirSync(f.ports.stateRoot).find(x => /^[0-9a-f]{20}\.json$/.test(x)));
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

test('#3230 start with explicit --agent, profile folder env, or --pool overwrites saved coordinator profile and clears stale pause/cooldowns', async t => {
  const f = await fixture(t, { tempPrefix: 'pdd-autopilot-override-' });
  delete f.ports.selectAgent;
  const origRun = f.ports.run;
  f.ports.run = async (command, args, opts = {}) => {
    if (command === 'codex' || command === 'claude' || command === 'gemini') {
      if (args[0] === '--version') return { code: 0, stdout: `${command} 1.0.0\n`, stderr: '' };
      if (args.join(' ') === 'login status') return { code: 0, stdout: 'Logged in using ChatGPT\n', stderr: '' };
      if (args.join(' ') === 'auth status --json') return { code: 0, stdout: '{"loggedIn":true}\n', stderr: '' };
    }
    return origRun(command, args, opts);
  };
  f.ports.codexLimits = async () => ({ state: 'healthy', resetAt: null, usedPercent: 10 });
  const baseEnv = { HOME: f.home, PATH: '/fixture/bin' };

  // 1. Initial start saves codex profile.
  const first = await f.invoke('start', { env: baseEnv, label: 'pdd:autopilot' });
  assert.equal(first.exitCode, 0, first.message);
  assert.equal(f.state().agent.kind, 'codex');

  // Seed a stale machine pause and pool cooldown in <stateFile>-core/.
  const coreDir = f.stateFile().replace(/\.json$/, '-core');
  mkdirSync(coreDir, { recursive: true });
  writeFileSync(join(coreDir, 'core.json'), JSON.stringify({
    streak: 3,
    hours: 2,
    pausedUntil: f.time + 3600_000,
    pausedHours: 1,
    poolOut: { since: f.time - 60_000, at: f.time, resetAt: f.time + 3600_000, reason: 'usage-limit', issue: 9 },
  }));
  writeFileSync(join(coreDir, 'login-pool.json'), JSON.stringify({
    logins: { 'codex-old': { until: f.time + 3600_000, resetAt: f.time + 3600_000, reason: 'quota', at: f.time } },
  }));

  // 2. Plain start without override preserves saved codex profile and leaves core.json pause intact.
  const plain = await f.invoke('start', { env: baseEnv, label: 'pdd:autopilot' });
  assert.equal(plain.exitCode, 0, plain.message);
  assert.equal(f.state().agent.kind, 'codex');
  assert.equal(JSON.parse(readFileSync(join(coreDir, 'core.json'), 'utf8')).streak, 3);

  // 3. Explicit --agent claude + CLAUDE_CONFIG_DIR immediately replaces saved profile and clears pause/cooldowns!
  const claudeDir = join(f.home, '.claude-team');
  mkdirSync(claudeDir, { recursive: true });
  const switched = await f.invoke('start', {
    env: { ...baseEnv, CLAUDE_CONFIG_DIR: claudeDir },
    label: 'pdd:autopilot',
    agent: 'claude',
  });
  assert.equal(switched.exitCode, 0, switched.message);
  assert.match(switched.message, /Account changed from codex to claude/);
  assert.equal(f.state().agent.kind, 'claude');
  assert.equal(f.state().environment.CLAUDE_CONFIG_DIR, claudeDir);
  assert.equal(f.state().launchProfile.agent.kind, 'claude');
  assert.equal(f.state().launchProfile.configHome, claudeDir);
  const clearedCore = JSON.parse(readFileSync(join(coreDir, 'core.json'), 'utf8'));
  assert.equal(clearedCore.streak, 0);
  assert.equal(clearedCore.pausedUntil, null);
  assert.equal(clearedCore.poolOut, null);
  assert.equal(existsSync(join(coreDir, 'login-pool.json')), false);

  // 4. Explicit config folder override (CLAUDE_CONFIG_DIR=/new) without --agent also updates saved profile!
  const claudeDir2 = join(f.home, '.claude-alt');
  mkdirSync(claudeDir2, { recursive: true });
  const folderOverride = await f.invoke('start', {
    env: { ...baseEnv, CLAUDE_CONFIG_DIR: claudeDir2 },
    label: 'pdd:autopilot',
  });
  assert.equal(folderOverride.exitCode, 0, folderOverride.message);
  assert.match(folderOverride.message, /Account changed from claude \(.*claude-team\) to claude \(.*claude-alt\)/);
  assert.equal(f.state().environment.CLAUDE_CONFIG_DIR, claudeDir2);
  assert.equal(f.state().launchProfile.configHome, claudeDir2);

  // 5. Explicit --pool <path> activates ordered pool and saves poolPath; bad --agent or --pool exits 2 without mutating state.
  const poolFile = join(f.dir, 'pool.json');
  writeFileSync(poolFile, JSON.stringify({
    reset: 'never',
    logins: [
      { id: 'codex-pro', kind: 'codex', codexHome: join(f.home, '.codex-pro') },
      { id: 'claude-alt', kind: 'claude', claudeConfigDir: claudeDir2 },
    ],
  }));
  const pooled = await f.invoke('start', { env: baseEnv, label: 'pdd:autopilot', pool: poolFile });
  assert.equal(pooled.exitCode, 0, pooled.message);
  assert.match(pooled.message, /Login pool: codex-pro -> claude-alt \(2 login\(s\)\)/);
  assert.equal(f.state().poolPath, poolFile);
  assert.equal(f.state().agent.id, 'codex-pro');

  const badAgent = await f.invoke('start', { env: baseEnv, label: 'pdd:autopilot', agent: 'bogus' });
  assert.equal(badAgent.exitCode, 2);
  assert.equal(f.state().poolPath, poolFile, 'bad --agent leaves saved state untouched');

  const badPool = await f.invoke('start', { env: baseEnv, label: 'pdd:autopilot', pool: join(f.dir, 'missing-pool.json') });
  assert.equal(badPool.exitCode, 2);
  assert.equal(f.state().poolPath, poolFile, 'bad --pool leaves saved state untouched');

  // 6. Pool start with Gemini login authenticated via flat <geminiCliHome>/oauth_creds.json passes both pool selection and doctor preflight!
  const geminiDir = join(f.home, '.gemini-flat');
  mkdirSync(geminiDir, { recursive: true });
  writeFileSync(join(geminiDir, 'oauth_creds.json'), JSON.stringify({ refresh_token: 'gemini-flat-refresh-token' }));
  const geminiPool = join(f.dir, 'gemini-pool.json');
  writeFileSync(geminiPool, JSON.stringify({
    reset: 'never',
    logins: [{ id: 'gemini-flat', kind: 'gemini', geminiCliHome: geminiDir }],
  }));
  const geminiStart = await f.invoke('start', { env: baseEnv, label: 'pdd:autopilot', pool: geminiPool });
  assert.equal(geminiStart.exitCode, 0, geminiStart.message);
  assert.equal(f.state().agent.id, 'gemini-flat');
  assert.equal(f.state().agent.kind, 'gemini');
  assert.equal(f.state().environment.GEMINI_CLI_HOME, geminiDir);

  // 7. Active intake refuses gemini-only --agent and gemini-only --pool, and succeeds when --pool includes codex or claude alongside gemini!
  const refusedGeminiAgent = await f.invoke('start', { env: baseEnv, intake: 'active', agent: 'gemini' });
  assert.equal(refusedGeminiAgent.exitCode, 1);
  assert.match(refusedGeminiAgent.message, /Active intake needs a codex or claude login for sandboxed read-only card checks/);

  const refusedGeminiPool = await f.invoke('start', { env: baseEnv, intake: 'active', pool: geminiPool });
  assert.equal(refusedGeminiPool.exitCode, 1);
  assert.match(refusedGeminiPool.message, /Active intake needs a codex or claude login for sandboxed read-only card checks/);

  const mixedPool = join(f.dir, 'mixed-pool.json');
  writeFileSync(mixedPool, JSON.stringify({
    reset: 'never',
    logins: [
      { id: 'gemini-flat', kind: 'gemini', geminiCliHome: geminiDir },
      { id: 'codex-pro', kind: 'codex', codexHome: join(f.home, '.codex-pro') },
    ],
  }));
  const mixedActiveStart = await f.invoke('start', { env: baseEnv, intake: 'active', pool: mixedPool });
  assert.equal(mixedActiveStart.exitCode, 0, mixedActiveStart.message);
  assert.equal(f.state().agent.id, 'gemini-flat');
  assert.equal(f.state().poolPath, mixedPool);
  assert.equal(f.state().intake, 'active');
});

test('inspectMachineJobs counts still-running jobs in disabled repos and inventories child roles without inflating issue slots', async t => {
  const { startAgentJob, stopAgentJob } = await import('../src/agent-job.mjs');
  const f = await fixture(t, { tempPrefix: 'pdd-autopilot-jobs-' });
  const stateRoot = f.ports.stateRoot;
  mkdirSync(stateRoot, { recursive: true });

  // Repo A: disabled while issue #11 still has live build + suite child processes, #12 is parked with no live PID, and #19 runs intake.
  const idA = 'a'.repeat(20), coreA = join(stateRoot, `${idA}-core`);
  mkdirSync(join(coreA, 'jobs'), { recursive: true });
  mkdirSync(join(coreA, 'intake', 'jobs'), { recursive: true });
  mkdirSync(join(coreA, 'logs'), { recursive: true });
  writeFileSync(join(stateRoot, `${idA}.json`), JSON.stringify({ repo: 'owner/disabled-repo', cwd: f.cwd, enabled: false, engine: 'core' }));

  const liveBuild = startAgentJob({ id: '11-build', dir: join(coreA, 'logs'), cwd: f.dir, command: '/bin/sh', args: ['-c', 'sleep 10'], env: { PATH: process.env.PATH } });
  const liveSuite = startAgentJob({ id: '11-suite', dir: join(coreA, 'logs'), cwd: f.dir, command: '/bin/sh', args: ['-c', 'sleep 10'], env: { PATH: process.env.PATH } });
  const liveIntake = startAgentJob({ id: '19-intake', dir: join(coreA, 'logs'), cwd: f.dir, command: '/bin/sh', args: ['-c', 'sleep 10'], env: { PATH: process.env.PATH } });
  t.after(() => { stopAgentJob(liveBuild); stopAgentJob(liveSuite); stopAgentJob(liveIntake); });

  writeFileSync(join(coreA, 'jobs', '11.json'), JSON.stringify({
    issue: 11, phase: 'pr', role: 'build', agent: liveBuild, suite: { agent: liveSuite },
  }));
  writeFileSync(join(coreA, 'jobs', '12.json'), JSON.stringify({
    issue: 12, phase: 'pr', role: 'build',
  }));
  writeFileSync(join(coreA, 'intake', 'jobs', '19.json'), JSON.stringify({
    issue: 19, stage: 'card', job: liveIntake,
  }));

  // Repo B: enabled with 1 active repair/review/vectors/runtime job (#21) using injected jobAlive for remaining roles.
  const idB = 'b'.repeat(20), coreB = join(stateRoot, `${idB}-core`);
  mkdirSync(join(coreB, 'jobs'), { recursive: true });
  writeFileSync(join(stateRoot, `${idB}.json`), JSON.stringify({ repo: 'owner/enabled-repo', cwd: f.cwd, enabled: true, engine: 'core' }));
  const fakePart = (id, pid) => ({ id, pid, token: `tok-${id}`, exit: join(coreA, 'logs', `missing-${id}.exit.json`) });
  writeFileSync(join(coreB, 'jobs', '21.json'), JSON.stringify({
    issue: 21, phase: 'pr', role: 'repair',
    agent: fakePart('21-repair', 9001),
    review: { agent: fakePart('21-review', 9002) },
    vectors: { agent: fakePart('21-vectors', 9003) },
    runtimeWait: { head: 'abc', state: 'sent', agent: fakePart('21-runtime', 9004) },
  }));

  // 1. Real native process check (unmocked aliveCheck reading /proc/<pid>/cmdline on Linux) detects liveBuild, liveSuite, and liveIntake!
  const nativeCheck = f.module.inspectMachineJobs(stateRoot);
  assert.equal(nativeCheck.counts.build, 1);
  assert.equal(nativeCheck.counts.suite, 1);
  assert.equal(nativeCheck.counts.intake, 1);

  const realOnly = f.module.inspectMachineJobs(stateRoot, {
    jobAlive: (pid, token) => [9001, 9002, 9003, 9004].includes(pid) ? true : [liveBuild.pid, liveSuite.pid, liveIntake.pid].includes(pid) && Boolean(token),
  });
  assert.equal(realOnly.slotJobs, 2, '1 finishing issue in disabled repo + 1 issue in enabled repo; child roles and intake never inflate slots');
  assert.deepEqual(realOnly.counts, { build: 1, repair: 1, review: 1, suite: 1, vectors: 1, runtime: 1, intake: 1 });
  assert.equal(realOnly.totalProcesses, 7);

  // 2. Stopping the disabled repo workers frees its slot reservation once processes exit.
  stopAgentJob(liveBuild); stopAgentJob(liveSuite); stopAgentJob(liveIntake);
  const deadline = Date.now() + 5000;
  while (Date.now() < deadline && (!existsSync(liveBuild.exit) || !existsSync(liveSuite.exit) || !existsSync(liveIntake.exit))) {
    await new Promise(r => setTimeout(r, 40));
  }
  const afterStop = f.module.inspectMachineJobs(stateRoot, { jobAlive: pid => [9001, 9002, 9003, 9004].includes(pid) });
  assert.equal(afterStop.slotJobs, 1, 'disabled repo slot drops to 0 after workers finish');
  assert.equal(afterStop.counts.build, 0);
  assert.equal(afterStop.counts.suite, 0);
  assert.equal(afterStop.counts.intake, 0);

  // 3. PID <= 1 (e.g. PID 1 init/systemd or PID 0) is rejected before probing liveness.
  writeFileSync(join(coreA, 'jobs', '13.json'), JSON.stringify({
    issue: 13, phase: 'running', role: 'build',
    agent: fakePart('13-init', 1),
    suite: { agent: fakePart('13-zero', 0) },
  }));
  const probedPids = [];
  const pidGuard = f.module.inspectMachineJobs(stateRoot, {
    jobAlive: pid => { probedPids.push(pid); return true; },
  });
  assert.equal(probedPids.includes(1), false, 'PID 1 is never probed');
  assert.equal(probedPids.includes(0), false, 'PID 0 is never probed');
  assert.equal(pidGuard.byRole.build.some(j => j.issue === 13), false);
});

test('status --all and status --json read local cached loginPool only (zero gh/HTTP/timer in --json, zero fabricated 0%) and wire conversion drops', async t => {
  const { accountsStatePath } = await import('../src/login-pool.mjs');
  const f = await fixture(t, { tempPrefix: 'pdd-autopilot-obs-' });
  const stateRoot = f.ports.stateRoot;
  mkdirSync(stateRoot, { recursive: true });

  const id = createHash('sha256').update(f.cwd).digest('hex').slice(0, 20);
  const stateFile = join(stateRoot, `${id}.json`), coreDir = join(stateRoot, `${id}-core`);
  mkdirSync(join(coreDir, 'jobs'), { recursive: true });
  mkdirSync(join(coreDir, 'intake', 'cards'), { recursive: true });
  writeFileSync(stateFile, JSON.stringify({
    repo: 'owner/repo', cwd: f.cwd, baseBranch: 'trunk', mode: 'observe', enabled: true, engine: 'core', runs: 8, share: 50,
  }));
  writeFileSync(join(coreDir, 'jobs', '42.json'), JSON.stringify({
    issue: 42, phase: 'running', role: 'build',
    agent: { id: '42-build', pid: 7771, token: 'tok-42', exit: join(coreDir, 'missing.exit.json') },
  }));
  writeFileSync(join(coreDir, 'intake', 'cards', '42.json'), JSON.stringify({ issue: 42, card: { class: 'ready', confidence: 0.9, reason: 'clear' } }));
  writeFileSync(join(coreDir, 'history.jsonl'), [
    JSON.stringify({ at: f.time - 3000, issue: 10, outcome: 'merged', pr: 101, text: 'merged cleanly' }),
    JSON.stringify({ at: f.time - 2000, issue: 11, outcome: 'would-merge', pr: 102, text: 'green in observe mode' }),
    JSON.stringify({ at: f.time - 1500, issue: 12, strike: true, owner: 'issue' }),
    JSON.stringify({ at: f.time - 1000, issue: 12, outcome: 'ended', pr: null, poolExhausted: true, text: 'all accounts cooling' }),
    JSON.stringify({ at: f.time - 500, issue: 13, outcome: 'ended', pr: 103, owner: 'pdd', text: 'review loop ended' }),
  ].join('\n') + '\n');

  const cloudStateFile = accountsStatePath({ HOME: f.home });
  mkdirSync(dirname(cloudStateFile), { recursive: true });
  writeFileSync(cloudStateFile, JSON.stringify({
    enrolled: true,
    accounts: [
      { account_id: 'acc-1', label: 'codex-alpha', provider: 'codex', state: 'ready', five_hour_used_percent: 35, five_hour_reset_at: '2026-11-04T03:00:00Z', weekly_used_percent: 62, weekly_reset_at: '2026-11-08T00:00:00Z' },
      { account_id: 'acc-2', label: 'claude-beta', provider: 'claude', state: 'cooling', five_hour_used_percent: 100, five_hour_reset_at: '2026-11-04T02:00:00Z', weekly_used_percent: null, weekly_reset_at: null },
      { account_id: 'acc-3', label: 'codex-expired', provider: 'codex', state: 'reauth_required', five_hour_used_percent: null, weekly_used_percent: null },
    ],
  }));

  f.ports.jobAlive = pid => pid === 7771;
  f.ports.machineGuard = async input => ({
    share: input.share ?? 50, shareSource: 'default', slots: input.runs ?? 8, requestedSlots: 8, hardwareSlots: 16,
    limiter: 'runs', limiterDetail: '--runs 8', readyLogins: input.readyLogins ?? null, source: 'this machine, --runs 8',
    auto: 6, room: { ok: true, reason: null, free: 7 }, use: { jobs: input.jobs, rss: 1024 ** 3, cores: 1 },
    line: `Machine: share 50% (default) · slots 8 · jobs ${input.jobs} · new work: ok`,
  });

  const ghCallsBefore = f.runs.filter(([cmd]) => cmd === 'gh').length;
  const textRes = await f.invoke('status', { all: true });
  assert.equal(textRes.exitCode, 0, textRes.message);
  assert.match(textRes.message, /Autopilot on this machine \(1\):/);
  assert.match(textRes.message, /Machine: share 50% \(default\) · slots 8 · jobs 1 · new work: ok/);
  assert.match(textRes.message, /Active jobs: 1 issue slot · roles build 1 \(#42\), repair 0, review 0, suite 0, vectors 0, runtime 0, intake 0/);
  assert.match(textRes.message, /Suite queue: 0 running, 0 waiting/);
  assert.match(textRes.message, /Login pool \(cloud\): ready 1, cooling 1, reauth_required 1/);
  assert.match(textRes.message, /claude-beta \[claude cooling, 5H 100% \(2026-11-04T02:00Z\), 7D \?\]/);
  assert.ok(textRes.message.includes('Conversion: claimed 4 → clear-spec 4 → PR 3 → merged/would-merge 2 (dropped 2: pdd 1, quota_or_service 1; pending drafts 0; intake cards 1)'), textRes.message);

  // status --json spawns zero timer/gh/herdr probes!
  const prevTimer = f.ports.timer;
  f.ports.timer = async () => assert.fail('status --json must never probe user timers');
  const jsonRes = await f.invoke('status', { json: true });
  f.ports.timer = prevTimer;
  assert.equal(jsonRes.exitCode, 0);
  const payload = JSON.parse(jsonRes.message);
  assert.equal(payload.schema, 'pdd.cost-report.v1');
  assert.equal(payload.costs.schema, 'pdd.cost-report.v1');
  assert.equal(payload.repositories.length, 1);
  assert.equal(payload.repositories[0].repo, 'owner/repo');
  assert.equal(payload.machineGuard.slots, 8);
  assert.equal(payload.machineGuard.readyLogins, 1);
  assert.equal(payload.activeJobs.issueSlots, 1);
  assert.equal(payload.activeJobs.counts.build, 1);
  assert.equal(payload.suiteQueue.busyChecks, 0);
  assert.deepEqual(payload.loginPool.counts, { total: 3, ready: 1, cooling: 1, reauth_required: 1 });
  assert.equal(payload.loginPool.accounts[1].weeklyUsedPercent, null, 'unknown window stays null, never fabricated 0%');
  assert.deepEqual(payload.conversion.totals, { backlog: 4, claimable: 4, claimed: 4, clearSpec: 4, prOpened: 3, mergedOrWouldMerge: 2, dropped: 2 });
  assert.equal(payload.conversion.dropsByOwner.quota_or_service.count, 1);
  assert.equal(payload.conversion.dropsByOwner.pdd.count, 1);
  assert.equal(f.runs.filter(([cmd]) => cmd === 'gh').length, ghCallsBefore, 'status makes zero GitHub calls');

  // Enrolled with active lease metadata only (no full pool count): shows cached lease windows while keeping readyLogins null.
  writeFileSync(cloudStateFile, JSON.stringify({
    enrolled: true,
    providers: ['codex'],
    active: { codex: { account_id: 'acc-lease', label: 'codex-lease', provider: 'codex', five_hour_used_percent: 45, weekly_used_percent: null } },
    cooling: {},
  }));
  const leaseJson = JSON.parse((await f.invoke('status', { json: true })).message);
  assert.equal(leaseJson.loginPool.readyLogins, null, 'lease-only cache leaves readyLogins null so autoSlots is not lowered');
  assert.equal(leaseJson.loginPool.accounts[0].fiveHourUsedPercent, 45);
  assert.equal(leaseJson.loginPool.accounts[0].weeklyUsedPercent, null);

  // Enrolled with no cached account entries on disk: reports unavailable with zero fabricated 0% values.
  writeFileSync(cloudStateFile, JSON.stringify({ enrolled: true, providers: ['codex'], active: {}, cooling: {} }));
  const offlineText = await f.invoke('status', { all: true });
  assert.equal(offlineText.exitCode, 0);
  assert.match(offlineText.message, /Login pool \(cloud\): unavailable/);
  assert.doesNotMatch(offlineText.message, /Login pool.*0%/);
  const offlineJson = JSON.parse((await f.invoke('status', { json: true })).message);
  assert.deepEqual(offlineJson.loginPool, { source: 'cloud', state: 'unavailable', counts: null, readyLogins: null, accounts: [] });
});

test('status --all and status --json create or modify zero files on disk, and tickAutopilot agrees with status on login-scaled slots', async t => {
  const { execFileSync } = await import('node:child_process');
  const { readMachineGuard } = await import('../src/machine-guard.mjs');
  const f = await fixture(t, { tempPrefix: 'pdd-autopilot-ro-' });
  const stateRoot = f.ports.stateRoot;
  mkdirSync(stateRoot, { recursive: true });

  // Configure a 5-login local pool (scales automatic slots from 4 -> 2 * 5 = 10 on a 64-core server).
  const logins = [];
  for (let i = 1; i <= 5; i++) {
    const cHome = join(f.home, `.codex-p${i}`);
    mkdirSync(cHome, { recursive: true });
    writeFileSync(join(cHome, 'auth.json'), JSON.stringify({ tokens: { access_token: `tok-${i}` } }));
    logins.push({ id: `codex-${i}`, kind: 'codex', codexHome: cHome });
  }
  const poolFile = join(f.dir, 'five-pool.json');
  writeFileSync(poolFile, JSON.stringify({ reset: 'never', logins }));

  const id = createHash('sha256').update(f.cwd).digest('hex').slice(0, 20);
  const stateFile = join(stateRoot, `${id}.json`);
  writeFileSync(stateFile, JSON.stringify({
    enabled: true, cwd: f.cwd, repo: 'owner/repo', defaultBranch: 'main', baseBranch: 'main',
    coordinatorId: 'coord-ro', machine: 'machine-ro', engine: 'core', mode: 'observe',
    label: 'pdd:autopilot', poolPath: poolFile,
    agent: { id: 'codex-1', kind: 'codex', command: 'codex' },
    packageRoot: f.packageRoot,
  }));

  // Initialize a real git repo in f.cwd and seed .git/pdd/runs/17/status.json + ~/.local/state/pdd/runs.json to prove localCosts writes zero files!
  execFileSync('git', ['init', '-q'], { cwd: f.cwd });
  const gitCommonDir = execFileSync('git', ['rev-parse', '--path-format=absolute', '--git-common-dir'], { cwd: f.cwd, encoding: 'utf8' }).trim();
  const runDir = join(gitCommonDir, 'pdd', 'runs', '17');
  mkdirSync(runDir, { recursive: true });
  const savedRun = {
    v: 1, runId: 'run-ro-17', number: 17, repo: 'owner/repo', startedAt: f.time - 60000, updatedAt: f.time - 30000,
    runDir, commonDir: gitCommonDir, sourceRoot: f.cwd, root: f.cwd, state: 'running', workflow: 'feature',
    agent: 'codex', chats: [], pr: [], areas: [{ name: 'code' }],
  };
  writeFileSync(join(runDir, 'status.json'), JSON.stringify(savedRun, null, 2) + '\n');
  const runsIndexDir = join(f.home, '.local', 'state', 'pdd');
  mkdirSync(runsIndexDir, { recursive: true });
  writeFileSync(join(runsIndexDir, 'runs.json'), JSON.stringify({ runs: [{ number: 17, repo: 'owner/repo', runDir }] }));

  const GiB = 1024 ** 3;
  const server = {
    cpuCount: 64, load: 1, memory: { available: 200 * GiB, total: 251 * GiB }, pressure: { io: 0, memory: 0, level: null },
    disk: { available: 500 * GiB, total: 1000 * GiB }, cgroup: { cpus: null, memoryMax: null, memoryFree: null },
    check: { cpuIds: Array.from({ length: 64 }, (_, i) => i), platform: 'linux', battery: false, virtualized: true, taskset: '/usr/bin/taskset' },
  };
  f.ports.machineGuard = input => readMachineGuard(input, {
    machineResources: async () => server,
    autopilotUse: async () => ({ rss: GiB, cores: 1 }),
  });

  // 1. Recursive filesystem snapshot before status --all & status --json: zero creates, deletes, or mutations!
  const snapshotTree = rootDir => {
    const entries = [];
    const walk = cur => {
      for (const name of readdirSync(cur).sort()) {
        const full = join(cur, name);
        const st = statSync(full);
        if (st.isDirectory()) { entries.push(`D:${full}`); walk(full); }
        else entries.push(`F:${full}:${st.size}:${st.mtimeMs}:${createHash('sha256').update(readFileSync(full)).digest('hex')}`);
      }
    };
    walk(rootDir);
    return entries;
  };

  const beforeSnap = snapshotTree(f.dir);
  const allRes = await f.invoke('status', { all: true });
  assert.equal(allRes.exitCode, 0, allRes.message);
  const jsonRes = await f.invoke('status', { json: true });
  assert.equal(jsonRes.exitCode, 0);
  const jsonAllRes = await f.invoke('status', { json: true, all: true });
  assert.equal(jsonAllRes.exitCode, 0);
  const afterSnap = snapshotTree(f.dir);
  assert.deepEqual(afterSnap, beforeSnap, 'status --all and status --json must create or modify zero files on disk');

  // 2. Also verify real CLI subprocess for status --json spawns zero gh/herdr/systemctl/launchctl even with enrolled accounts-state.json!
  const { accountsStatePath } = await import('../src/login-pool.mjs');
  const enrolledPath = accountsStatePath({ HOME: f.home });
  mkdirSync(dirname(enrolledPath), { recursive: true });
  writeFileSync(enrolledPath, JSON.stringify({ enrolled: true, providers: ['codex'], active: {}, cooling: {} }));
  const deniedBin = join(f.dir, 'denied-bin'), deniedMarker = join(f.dir, 'denied-called');
  mkdirSync(deniedBin, { recursive: true });
  for (const prog of ['gh', 'herdr', 'systemctl', 'launchctl']) {
    writeFileSync(join(deniedBin, prog), `#!/bin/sh\nprintf "%s\n" "${prog}" >> "${deniedMarker}"\nexit 99\n`, { mode: 0o755 });
  }
  const cliBin = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
  const rawCliJson = execFileSync(process.execPath, [cliBin, 'autopilot', 'status', '--json'], {
    cwd: f.cwd, encoding: 'utf8',
    env: { HOME: f.home, PATH: `${deniedBin}:${process.env.PATH}` },
  });
  assert.equal(existsSync(deniedMarker), false, 'real CLI status --json must spawn zero gh/herdr/systemctl/launchctl subprocesses');
  assert.equal(JSON.parse(rawCliJson).loginPool.state, 'unavailable');
  rmSync(enrolledPath, { force: true });

  // 3. Consistent 10-slot login-scaled capacity across repo status, status --all, status --json, and tickAutopilot (coreGuard)!
  const repoStatus = await f.invoke('status');
  assert.equal(repoStatus.exitCode, 0, repoStatus.message);
  assert.match(repoStatus.message, /Jobs: 0 of 10 slots busy/);
  assert.match(repoStatus.message, /→ 10 \(automatic, limited by 2 × 5 ready logins = 10\)/);
  assert.match(allRes.message, /→ 10 \(automatic, limited by 2 × 5 ready logins = 10\)/);
  assert.equal(JSON.parse(jsonRes.message).machineGuard.slots, 10);

  f.ports.corePorts = { checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true };
  const tickRes = await f.module.tickAutopilot(stateFile, f.ports);
  assert.equal(tickRes.exitCode, 0, tickRes.message);
  assert.match(tickRes.message, /0 of 10 slots busy/, 'tickAutopilot uses the exact same 10 login-scaled slots as status');
});

test('paused local pool login reports readyLogins: 0 and holds admission across status and tickAutopilot', async t => {
  const { readMachineGuard } = await import('../src/machine-guard.mjs');
  const f = await fixture(t, { tempPrefix: 'pdd-autopilot-paused-pool-' });
  const stateRoot = f.ports.stateRoot;
  mkdirSync(stateRoot, { recursive: true });

  const cHome = join(f.home, '.codex-paused');
  mkdirSync(cHome, { recursive: true });
  writeFileSync(join(cHome, 'auth.json'), JSON.stringify({ tokens: { access_token: 'tok-paused' } }));
  const poolFile = join(f.dir, 'paused-pool.json');
  writeFileSync(poolFile, JSON.stringify({
    reset: 'never',
    logins: [{ id: 'codex-paused', kind: 'codex', paused: true, codexHome: cHome }],
  }));

  const id = createHash('sha256').update(f.cwd).digest('hex').slice(0, 20);
  const stateFile = join(stateRoot, `${id}.json`);
  writeFileSync(stateFile, JSON.stringify({
    enabled: true, cwd: f.cwd, repo: 'owner/repo', defaultBranch: 'main', baseBranch: 'main',
    coordinatorId: 'coord-paused', machine: 'machine-paused', engine: 'core', mode: 'observe',
    label: 'pdd:autopilot', poolPath: poolFile,
    agent: { id: 'codex-paused', kind: 'codex', command: 'codex' },
    packageRoot: f.packageRoot,
  }));

  const GiB = 1024 ** 3;
  const server = {
    cpuCount: 64, load: 1, memory: { available: 200 * GiB, total: 251 * GiB }, pressure: { io: 0, memory: 0, level: null },
    disk: { available: 500 * GiB, total: 1000 * GiB }, cgroup: { cpus: null, memoryMax: null, memoryFree: null },
    check: { cpuIds: Array.from({ length: 64 }, (_, i) => i), platform: 'linux', battery: false, virtualized: true, taskset: '/usr/bin/taskset' },
  };
  f.ports.machineGuard = input => readMachineGuard(input, {
    machineResources: async () => server,
    autopilotUse: async () => ({ rss: 0, cores: 0 }),
  });

  const jsonRes = await f.invoke('status', { json: true });
  assert.equal(jsonRes.exitCode, 0);
  const payload = JSON.parse(jsonRes.message);
  assert.equal(payload.loginPool.source, 'local-pool');
  assert.equal(payload.loginPool.state, 'paused');
  assert.equal(payload.loginPool.readyLogins, 0);
  assert.deepEqual(payload.loginPool.counts, { total: 1, ready: 0, cooling: 0, paused: 1, reauth_required: 0 });
  assert.equal(payload.machineGuard.slots, 0);
  assert.deepEqual(payload.machineGuard.room, { ok: false, reason: 'no ready Cloud or local logins', free: 0 });

  const allRes = await f.invoke('status', { all: true });
  assert.equal(allRes.exitCode, 0);
  assert.match(allRes.message, /Login pool \(local\): ready 0, cooling 0, paused 1 of 1/);
  assert.match(allRes.message, /held \(no ready Cloud or local logins\)/);

  const repoRes = await f.invoke('status');
  assert.equal(repoRes.exitCode, 0);
  assert.match(repoRes.message, /held \(no ready Cloud or local logins\)/);
});

test('cross-repository --runs 8 lifts whole-machine capacity consistently across status and sibling repo coreGuard', async t => {
  const { execFileSync } = await import('node:child_process');
  const { readMachineGuard } = await import('../src/machine-guard.mjs');
  const f = await fixture(t, { tempPrefix: 'pdd-autopilot-cross-runs-' });
  const stateRoot = f.ports.stateRoot;
  mkdirSync(stateRoot, { recursive: true });

  // Repo A: enabled with --runs 8 and 5 active jobs.
  const cwdA = join(f.dir, 'repo-a'), cwdB = f.cwd;
  mkdirSync(cwdA, { recursive: true });
  execFileSync('git', ['init', '-q'], { cwd: cwdA });
  execFileSync('git', ['init', '-q'], { cwd: cwdB });
  writeFileSync(join(cwdB, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'observe', trust: [], engine: 'core', testCommand: 'npm test' } }));

  const idA = createHash('sha256').update(realpathSync(cwdA)).digest('hex').slice(0, 20);
  const idB = createHash('sha256').update(realpathSync(cwdB)).digest('hex').slice(0, 20);
  const stateFileA = join(stateRoot, `${idA}.json`), coreA = join(stateRoot, `${idA}-core`);
  const stateFileB = join(stateRoot, `${idB}.json`);
  mkdirSync(join(coreA, 'jobs'), { recursive: true });

  writeFileSync(stateFileA, JSON.stringify({
    enabled: true, cwd: realpathSync(cwdA), repo: 'owner/repo-a', defaultBranch: 'main', baseBranch: 'main',
    coordinatorId: 'coord-a', machine: 'machine-ab', engine: 'core', mode: 'observe', runs: 8,
    label: 'pdd:autopilot', agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: f.packageRoot,
  }));
  writeFileSync(stateFileB, JSON.stringify({
    enabled: true, cwd: realpathSync(cwdB), repo: 'owner/repo-b', defaultBranch: 'main', baseBranch: 'main',
    coordinatorId: 'coord-b', machine: 'machine-ab', engine: 'core', mode: 'observe',
    label: 'pdd:autopilot', agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: f.packageRoot,
  }));
  for (let i = 1; i <= 5; i++) {
    writeFileSync(join(coreA, 'jobs', `${i}.json`), JSON.stringify({ issue: i, phase: 'running', role: 'build' }));
  }

  const GiB = 1024 ** 3;
  const server = {
    cpuCount: 64, load: 1, memory: { available: 200 * GiB, total: 251 * GiB }, pressure: { io: 0, memory: 0, level: null },
    disk: { available: 500 * GiB, total: 1000 * GiB }, cgroup: { cpus: null, memoryMax: null, memoryFree: null },
    check: { cpuIds: Array.from({ length: 64 }, (_, i) => i), platform: 'linux', battery: false, virtualized: true, taskset: '/usr/bin/taskset' },
  };
  f.ports.machineGuard = input => readMachineGuard(input, {
    machineResources: async () => server,
    autopilotUse: async () => ({ rss: 3 * GiB, cores: 3 }),
  });

  // 1. With 5 jobs in Repo A (--runs 8) and 0 jobs in Repo B (default 4), BOTH global status AND Repo B status/coreGuard agree 3 machine slots remain free!
  const globalJson = JSON.parse((await f.invoke('status', { json: true, all: true })).message);
  assert.equal(globalJson.machineGuard.machineSlots, 8);
  assert.deepEqual(globalJson.machineGuard.room, { ok: true, reason: null, free: 3 });

  const repoBStatus = await f.invoke('status');
  assert.equal(repoBStatus.exitCode, 0, repoBStatus.message);
  assert.match(repoBStatus.message, /Jobs: 0 of 4 slots busy/);
  assert.match(repoBStatus.message, /→ 4 \(automatic, machine max 8\) · .* · new work: ok/);

  f.ports.queryIssues = async () => ({ status: 200, issues: [{ number: 77, title: 'Ready issue', body: 'Fix x', labels: [{ name: 'pdd:autopilot' }] }], etag: '"e1"' });
  f.ports.corePorts = {
    checkBase: async () => ({ exitCode: 0, message: 'ok' }),
    agentReady: async () => true,
    intake: async () => ({ started: 0, skipped: 0 }),
  };
  const tickBOpen = await f.module.tickAutopilot(stateFileB, f.ports);
  assert.equal(tickBOpen.exitCode, 0, tickBOpen.message);
  assert.doesNotMatch(tickBOpen.message, /intake held:/, 'Repo B coreGuard must not hold at 5 of 4 when Repo A configured --runs 8');

  // 2. When Repo A reaches 8 active jobs, BOTH global status AND Repo B status hold at 8 of 8!
  for (let i = 6; i <= 8; i++) {
    writeFileSync(join(coreA, 'jobs', `${i}.json`), JSON.stringify({ issue: i, phase: 'running', role: 'build' }));
  }
  const globalFull = JSON.parse((await f.invoke('status', { json: true, all: true })).message);
  assert.deepEqual(globalFull.machineGuard.room, { ok: false, reason: '8 of 8 Autopilot jobs on this machine run (all repositories, 50% share)', free: 0 });

  const repoBFull = await f.invoke('status');
  assert.match(repoBFull.message, /held \(8 of 8 Autopilot jobs on this machine run \(all repositories, 50% share\)\)/);
});
