import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, readdirSync, rmSync, existsSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { execFileSync } from 'node:child_process';
import { runPdd } from '../src/pdd-cli.mjs';
import { parseArgv } from '../src/argument-parser.mjs';
import { loadAgentDefinitions } from '../src/agent-config.mjs';

const root = resolve('.');
const capture = () => ({ text: '', write(s) { this.text += s; } });
async function fixture(t, options = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-autopilot-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const cwd = join(dir, options.cwdName ?? 'repo'), home = join(dir, 'home');
  mkdirSync(cwd); mkdirSync(home);
  writeFileSync(join(cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: options.mode ?? 'auto', trust: ['helper'] } }));
  const f = { dir, cwd, home, time: Date.parse('2026-11-04T00:00:00Z'), polls: [], prompts: [], runs: [], timers: [], comments: [], ack: [], issues: [], etag: '"one"', active: false };
  f.ports = {
    stateRoot: join(home, 'state'), now: () => f.time,
    warn: text => { (f.warnings ??= []).push(text); },
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex', env: {} }),
    pathDiagnostic: () => [],
    run: async (command, args) => {
      f.runs.push([command, args]);
      if (command === 'git') return { code: 0, stdout: cwd + '\n', stderr: '' };
      if (command === 'gh' && args[0] === 'repo') return { code: 0, stdout: '{"nameWithOwner":"owner/repo"}', stderr: '' };
      if (command === 'gh' && args[0] === 'auth') return { code: 0, stdout: '', stderr: '' };
      if (command === 'gh' && args[0] === 'api') { if (args.some(x => String(x).includes('/permission'))) return { code: 0, stdout: 'HTTP/2.0 200 OK\r\n\r\n{"permission":"none"}', stderr: '' }; f.ack.push(args); return { code: 0, stdout: '{}', stderr: '' }; }
      if (command === 'herdr') return { code: 0, stdout: '1.0', stderr: '' };
      throw Error(`unexpected process ${command} ${args}`);
    },
    timer: async (action, state) => { f.timers.push([action, structuredClone(state)]); if (action === 'start') f.active = true; if (action === 'stop') f.active = false; return f.active; },
    queryIssues: async (state) => { f.polls.push(state.etag); return { status: f.status ?? 200, etag: f.etag, issues: structuredClone(f.issues) }; },
    comments: async number => { f.comments.push(number); return f.issueComments?.[number] ?? []; },
    herdr: async args => {
      f.herdrCalls ??= []; f.herdrCalls.push(args);
      if (args[0] === 'status') return { running: f.serverRunning !== false };
      if (args[0] === 'workspace') return { result: { workspace: { workspace_id: 'w1' }, root_pane: { pane_id: 'p1' } } };
      if (args[0] === 'agent' && args[1] === 'get') {
        if (!f.agentStarted) throw Object.assign(Error('agent_not_found'), { code: 'agent_not_found' });
        return { result: { agent: { agent_status: f.agentStatus ?? 'idle' } } };
      }
      if (args[0] === 'pane' && args[1] === 'run') f.agentStarted = true;
      if (args[0] === 'pane' && args[1] === 'read') return 'Ready\n› ';
      if (args[0] === 'agent' && args[1] === 'prompt') f.prompts.push(args[3] ?? args[2]);
      return {};
    },
  };
  f.module = await import('../src/autopilot-launcher.mjs');
  f.invoke = async (command, extra = {}) => {
    const result = await f.module.runAutopilotLauncher({ command, cwd, env: { HOME: home, PATH: process.env.PATH }, packageRoot: root, issues: [], ...extra }, f.ports);
    if (command === 'start' && result.exitCode === 0 && f.agentStarted) await f.module.tickAutopilot(f.stateFile(), f.ports);
    return result;
  };
  f.stateFile = () => join(f.ports.stateRoot, readdirSync(f.ports.stateRoot).find(x => x.endsWith('.json')));
  f.state = () => JSON.parse(readFileSync(f.stateFile(), 'utf8'));
  f.tick = () => f.module.tickAutopilot(f.stateFile(), f.ports);
  return f;
}
const issue = (number, extra = {}) => ({ number, state: 'open', title: `Issue ${number}`, body: 'trusted body', user: { login: 'owner' }, author_association: 'OWNER', created_at: '2026-11-04T00:01:00Z', updated_at: '2026-11-04T00:01:00Z', comments: 0, labels: [], html_url: `https://github.com/owner/repo/issues/${number}`, ...extra });

// Native startup cases use the public launcher with fake programs, never live agents.
async function nativeStartup(t, { kind = 'codex', custom = false, cwdName, body = 'Please fix this synthetic startup case.' } = {}) {
  const f = await fixture(t, { mode: 'observe', cwdName });
  const bin = join(f.dir, 'bin'), profile = join(f.home, 'profile chosen');
  mkdirSync(bin); mkdirSync(profile);
  f.ports.stateRoot = join(f.dir, 'state');
  const record = join(f.dir, 'native.jsonl');
  const script = `#!${process.execPath}\nconst fs = require('node:fs'); fs.appendFileSync(${JSON.stringify(record)}, JSON.stringify({command:process.argv[1],argv:process.argv.slice(2),cwd:process.cwd(),env:{CODEX_HOME:process.env.CODEX_HOME,CLAUDE_CONFIG_DIR:process.env.CLAUDE_CONFIG_DIR,STARTUP_TEST_VALUE:process.env.STARTUP_TEST_VALUE}})+'\\n');\n`;
  for (const name of ['codex', 'fake-provider', 'chosen codex wrapper']) writeFileSync(join(bin, name), script, { mode: 0o755 });
  const env = { HOME: f.home, PATH: `${bin}:/usr/bin:/bin`, CODEX_HOME: profile, XDG_CONFIG_HOME: join(f.home, '.config') };
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
  const result = await f.invoke('start', { env, runs: '1' });
  assert.equal(result.exitCode, 0, result.message);
  const calls = existsSync(record) ? readFileSync(record, 'utf8').trim().split('\n').map(JSON.parse) : [];
  assert.equal(calls.length, 1, 'one selected fake executable runs');
  const [call] = calls;
  assert.equal(call.command, selected.command === 'codex' ? join(bin, 'codex') : selected.command);
  // process.cwd() resolves the temporary directory's /var symlink on macOS.
  assert.equal(call.cwd, realpathSync(f.cwd));
  assert.equal(call.env.CODEX_HOME, profile); assert.equal(call.env.CLAUDE_CONFIG_DIR, env.CLAUDE_CONFIG_DIR);
  assert.equal(call.env.STARTUP_TEST_VALUE, custom ? value : undefined);
  assert.ok(Object.keys(process.env).length === Object.keys(parentEnv).length && Object.entries(parentEnv).every(([key, value]) => process.env[key] === value), 'parent environment is unchanged');
  assert.deepEqual(snapshot(f.home), saved, 'agent settings and file inventory remain unchanged');
  const configs = [], operands = [];
  for (let i = 0; i < call.argv.length; i++) {
    if (call.argv[i] === '-c' || call.argv[i] === '--config') configs.push(call.argv[++i]);
    else if (!call.argv[i].startsWith('-')) operands.push(call.argv[i]);
  }
  assert.equal(operands.length, 0, 'native owner starts without a packet');
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
  assert.equal(JSON.parse(table[1]), cwd); assert.equal(JSON.parse(table[2]), 'trusted');
  assert.ok(configs.some(value => /^check_for_update_on_startup\s*=\s*false$/.test(value)));
  assert.equal(configs.some(value => /^(?:model|model_reasoning_effort|profile)\s*=/.test(value)), false);
  assert.equal(call.argv.some(value => ['-m', '--model', '-p', '--profile'].includes(value)), false);
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

for (const [kind, flags] of [
  ['claude', ['--dangerously-skip-permissions']],
  ['gemini', ['--yolo']],
  ['agy', ['--dangerously-skip-permissions']],
]) test(`native startup: ${kind} keeps its interactive launch without Codex config`, async t => {
  const { call, configs } = await nativeStartup(t, { kind, custom: kind !== 'agy' });
  for (const flag of flags) assert.ok(call.argv.includes(flag));
  assert.equal(configs.length, 0);
});

test('autopilot routes parse and dispatch without setup or a runtime call', async () => {
  const stdout = capture(), stderr = capture(); let seen;
  assert.equal(parseArgv(['autopilot', 'start', '--runs', '1200000']).local, 'autopilot-start');
  assert.equal(await runPdd(['autopilot', 'start', '--runs', '3'], { cwd: '/repo', stdout, stderr, autopilotLauncher: { runAutopilotLauncher: async input => { seen = input; return { exitCode: 0, message: 'started' }; } } }), 0);
  assert.equal(seen.command, 'start'); assert.equal(seen.runs, '3');
  assert.equal(stdout.text, 'started\n'); assert.equal(stderr.text, '');
  assert.deepEqual(parseArgv(['autopilot', 'add', '12', '15']).operands, ['12', '15']);
});

test('start installs a timer and runs the recipe immediately; unchanged empty ticks wake no AI', async t => {
  const f = await fixture(t);
  assert.equal((await f.invoke('start')).exitCode, 0);
  assert.equal(f.polls.length, 2); assert.equal(f.prompts.length, 1);
  assert.match(f.prompts[0], /"recipeFirst":true/);
  assert.equal(f.state().runs, undefined);
  assert.equal(f.state().nextTick, f.time + 1800000);
  f.status = 304; await f.tick(); await f.tick();
  assert.equal(f.prompts.length, 1); assert.deepEqual(f.polls, [undefined, '"one"', '"one"', '"one"']);
});

test('new and named issues are eligible; claimed work is distinguished and closed/old issues excluded', async t => {
  const f = await fixture(t); await f.invoke('start');
  f.issues = [issue(1), issue(2, { created_at: '2026-01-01T00:00:00Z' }), issue(3, { created_at: '2026-01-01T00:00:00Z', labels: [{ name: 'pdd:autopilot' }] }), issue(4, { pull_request: {} }), issue(5, { state: 'closed' }), issue(6, { labels: [{ name: 'pdd:working' }] })];
  await f.tick();
  const prompt = f.prompts.at(-1);
  assert.match(prompt, /"number":1,/); assert.match(prompt, /"number":3,/);
  for (const n of [2, 4, 5, 6]) assert.doesNotMatch(prompt, new RegExp(`"number":${n},`));
  await f.tick(); assert.equal(f.prompts.length, 2); // Already-seen work must stay quiet.
  await f.invoke('stop'); f.time += 3600000; await f.invoke('start');
  assert.equal(f.state().activatedAt, '2026-11-04T00:00:00.000Z');
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
  f.ports.herdr = async args => { if (args[1] === 'prompt') throw Object.assign(Error('blocked'), { code: 'agent_blocked' }); return herdr(args); };
  await f.tick();
  f.ports.herdr = herdr; await f.tick();
  assert.match(f.prompts[1], /trusted body/); assert.doesNotMatch(f.prompts[1], /OUTSIDER/);
});

test('stop disables only the timer and status is local; runs is optional, never fixed', async t => {
  const f = await fixture(t); await f.invoke('start', { runs: '7' });
  assert.match(f.prompts[0], /"runs":7/);
  const polls = f.polls.length;
  const status = await f.invoke('status'); assert.match(status.message, /owner\/repo.*codex/); assert.match(status.message, /2026-11-04T00:30:00/);
  const before = f.herdrCalls.length;
  await f.invoke('stop'); await f.tick(); await f.invoke('stop');
  assert.equal(f.herdrCalls.length, before); assert.equal(f.polls.length, polls);
  assert.match((await f.invoke('status')).message, /stopped/);
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
    const f = await fixture(t); delete f.ports.timer; f.ports.platform = platform; f.ports.uid = 123;
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
      assert.doesNotMatch(text, /\/bin\/.*sh|TOKEN|API_KEY/);
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
  phase = 1; await f.tick();
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
  assert.equal(queries, 3); assert.equal(f.prompts.length, 1);
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
  const dependencies = { cwd: f.cwd, packageRoot: root, env, stdout, stderr };
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
  await f.tick();
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
  await f.tick();
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

test('an ordinary open issue is delivered once; only unseen trusted changes wake it again', async t => {
  const f = await fixture(t); f.issues = [issue(71)]; await f.invoke('start');
  f.prompts.length = 0; f.status = 304;
  for (let tick = 0; tick < 4; tick++) await f.tick();
  assert.equal(f.prompts.length, 0);
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
  await f.tick(); assert.equal(f.prompts.length, 1);
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
    ? { code: 1, stderr: '', stdout: `HTTP/2.0 403 Forbidden\r\nx-ratelimit-remaining: 499\r\nx-ratelimit-reset: ${f.time / 1000 + 3600}\r\n\r\n{"message":"Resource not accessible"}` } : run(cmd, args, opts);
  const result = await f.tick();
  assert.equal(f.state().retryAt, undefined); assert.match(result.message, /75/); assert.match(f.warnings[0], /75/);
  assert.match(f.prompts.at(-1), /"number":76,/); assert.doesNotMatch(f.prompts.at(-1), /"number":75,/);
});

test('Linux start warns about logout when lingering is not enabled; status detects missing Herdr', async t => {
  const f = await fixture(t); const run = f.ports.run;
  f.ports.run = async (cmd, args, opts) => cmd === 'loginctl' ? { code: 0, stdout: 'no\n', stderr: '' } : run(cmd, args, opts);
  const result = await f.invoke('start'); assert.equal(result.exitCode, 0); assert.match(result.message, /loginctl enable-linger/);
  f.serverRunning = false; const status = await f.invoke('status');
  assert.doesNotMatch(status.message, /Autopilot running/); assert.match(status.message, /Herdr/);
});

test('overlapping ticks cannot deliver twice from a snapshot read before lock acquisition', async t => {
  const f = await fixture(t); await f.invoke('start'); f.prompts.length = 0; f.issues = [issue(77)];
  const run = f.ports.run; let reads = 0, release;
  f.ports.run = async (cmd, args, opts) => {
    if (cmd === 'git' && ++reads === 2) await new Promise(resolve => { release = resolve; });
    return run(cmd, args, opts);
  };
  const first = f.tick(), second = f.tick(); await first; release?.(); await second;
  assert.equal(f.prompts.length, 1);
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
    ? { code: 1, stderr: '', stdout: `HTTP/2.0 403 Forbidden\r\nx-ratelimit-remaining: 499\r\nx-ratelimit-reset: ${f.time / 1000 + 3600}\r\n\r\n{"message":"Resource not accessible"}` } : run(cmd, args, opts);
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
    assert.equal(f.prompts.length, 0); assert.equal(permissions, 0, 'Quiet ticks must not refresh cached permissions');
    f.status = 200; const changed = f.issues.find(x => x.number === number); changed.comments = 2; changed.updated_at = '2026-11-04T01:00:00Z';
    f.issueComments[number].push({ id: 2, body: 'OUTSIDER ONLY', user: { login: 'outside' } });
    await f.tick(); assert.equal(f.prompts.length, 0);
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
  await f.invoke('start'); f.prompts.length = 0;
  if (change.startsWith('unclaim')) f.issues[0].labels = [];
  else writeFileSync(join(f.cwd, 'pdd.json'), '{"autopilot":{"mode":"auto","trust":[]}}');
  for (let tick = 0; tick < 4; tick++) await f.tick();
  assert.equal(f.prompts.length, 0);
});
