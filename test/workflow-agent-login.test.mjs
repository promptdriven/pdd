// Issue 2901: a workflow chat uses the login of the person who runs pdd, never the Herdr server's old environment, and
// --agent also takes a ~/.config/pdd/agents.json entry name. Fake Herdr records pane commands; the test then runs each
// recorded command with a real /bin/sh in a "server" environment that holds stale login values, so fake agent programs
// show what a real chat would get. No real agent, account or Herdr session is used.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createHash, randomUUID } from 'node:crypto';
import { execFile as callback, execFileSync } from 'node:child_process';
import { chmodSync, existsSync, lutimesSync, mkdirSync, readFileSync, readdirSync, realpathSync, statSync, symlinkSync, utimesSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { promisify } from 'node:util';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
import { cancelRun, openRun, runStatus, startRun } from '../src/workflow-runner.mjs';
import { checkWorkflowAgents, LOGIN_VARIABLES } from '../src/workflow-agents.mjs';
import { runPdd } from '../src/pdd-cli.mjs';

const quote = value => `'${String(value).replace(/'/g, `'\\''`)}'`;
const SEEN = ['ANTHROPIC_API_KEY', 'ANTHROPIC_AUTH_TOKEN', 'CLAUDE_CODE_OAUTH_TOKEN', 'ANTHROPIC_BASE_URL', 'CLAUDE_CONFIG_DIR', 'ACCOUNT_MARK'];
// A fake agent program: `auth status` answers like Claude Code; any other call prints what the chat would get.
const program = name => `#!${process.execPath}
const seen = Object.fromEntries(${JSON.stringify(SEEN)}.map(key => [key, process.env[key] ?? null]));
if (process.argv[2] === 'auth' && process.argv[3] === 'status') {
  const ready = Boolean(process.env.CLAUDE_CODE_OAUTH_TOKEN) && process.env.ACCOUNT_MARK !== 'signed-out';
  process.stdout.write(JSON.stringify({ loggedIn: ready })); process.exitCode = ready ? 0 : 1;
} else process.stdout.write(JSON.stringify({ program: ${JSON.stringify(name)}, args: process.argv.slice(2), env: seen }));
`;
// The Herdr server environment: the terminal that first started it had other login values.
const STALE = { ANTHROPIC_API_KEY: 'stale-server-key', ANTHROPIC_AUTH_TOKEN: 'stale-server-auth', CLAUDE_CODE_OAUTH_TOKEN: 'stale-server-token',
  ANTHROPIC_BASE_URL: 'https://stale.invalid', CLAUDE_CONFIG_DIR: '/stale/claude-config' };

async function world(t) {
  const f = await fixture(t, { agent: 'claude' });
  const bin = join(f.base, 'bin'), wrappers = join(f.base, 'wrappers'), home = f.ports.env.HOME;
  for (const dir of [bin, wrappers]) mkdirSync(dir);
  writeFileSync(join(bin, 'claude'), program('claude'), { mode: 0o755 });
  f.wrapper = name => { const path = join(wrappers, name); writeFileSync(path, program(name), { mode: 0o755 }); return path; };
  f.agents = (agents, extra = {}) => {
    mkdirSync(join(home, '.config', 'pdd'), { recursive: true });
    writeFileSync(join(home, '.config', 'pdd', 'agents.json'), JSON.stringify({ agents, ...extra }));
  };
  f.serverEnv = { PATH: `${bin}:/usr/bin:/bin`, HOME: home, ...STALE };
  // Run a recorded pane command the way the pane shell would, in the server environment.
  f.execute = command => JSON.parse(execFileSync('/bin/sh', ['-c', command], { cwd: f.base, env: f.serverEnv, encoding: 'utf8' }));
  // Real Herdr sees the agent that a wrapper starts; the shared fake detects only a bare program name, so tell it the kind.
  f.commands = [];
  const fake = f.ports.herdr;
  f.ports.herdr = async args => {
    if (args[0] !== 'pane' || args[1] !== 'run') return fake(args);
    f.commands.push(args[3]);
    const custom = f.pendingCommand;
    return fake(custom ? [...args.slice(0, 3), args[3].replace(`${quote(custom)} `, `${quote(custom)} claude `)] : args);
  };
  f.start = agent => startRun({ name: 'small-change', issue: '17', agent, cwd: f.source, packageRoot }, f.ports);
  return f;
}
const loginFiles = f => readdirSync(f.record().runDir).filter(name => /^login-.*\.env$/.test(name));
const loginFileOf = command => /'([^']*\/login-[0-9a-f-]+\.env)'/.exec(command)?.[1] ?? null;

test('2901: a stale login in the Herdr server environment never reaches the chat of a caller without one', async t => {
  const f = await world(t);
  const started = await f.start('claude');
  assert.equal(started.exitCode, 0, started.message);
  const [command] = f.commands;
  for (const name of LOGIN_VARIABLES.claude) assert.ok(command.includes(` -u ${name} `), `${name} is unset in: ${command}`);
  assert.equal(loginFileOf(command), null, 'no login values, so no login file');
  assert.deepEqual(loginFiles(f), []);
  const seen = f.execute(command);
  assert.equal(seen.program, 'claude');
  assert.deepEqual(seen.env, { ANTHROPIC_API_KEY: null, ANTHROPIC_AUTH_TOKEN: null, CLAUDE_CODE_OAUTH_TOKEN: null, ANTHROPIC_BASE_URL: null,
    CLAUDE_CONFIG_DIR: f.record().configDir, ACCOUNT_MARK: null });
  assert.deepEqual(seen.args.slice(0, 3), ['--dangerously-skip-permissions', '--session-id', f.record().chats[0].session.id]);
});

test('2901: a run saved without a config folder unsets the server\'s CLAUDE_CONFIG_DIR in the chat', async t => {
  const f = await world(t);
  delete f.ports.env.CLAUDE_CONFIG_DIR;
  const started = await f.start('claude');
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(f.record().configDir, null);
  const [command] = f.commands;
  assert.ok(command.includes(' -u CLAUDE_CONFIG_DIR '), command);
  assert.equal(f.execute(command).env.CLAUDE_CONFIG_DIR, null);
});

test('2901: the caller\'s own token reaches the chat through a private one-time file, never through the shell line or the run record', async t => {
  const f = await world(t);
  f.ports.env.CLAUDE_CODE_OAUTH_TOKEN = "caller token 'a' $(touch broken)";
  const started = await f.start('claude');
  assert.equal(started.exitCode, 0, started.message);
  const [command] = f.commands, file = loginFileOf(command);
  assert.ok(file, `a login file in: ${command}`);
  assert.ok(!command.includes('caller token'), 'the token is not in the pane command');
  assert.ok(command.includes(' -u ANTHROPIC_API_KEY ') && !command.includes(' -u CLAUDE_CODE_OAUTH_TOKEN '));
  assert.ok(!readFileSync(join(f.record().runDir, 'status.json'), 'utf8').includes('caller token'), 'the run record keeps no token');
  assert.equal(statSync(file).mode & 0o777, 0o600);
  const seen = f.execute(command);
  assert.equal(seen.env.CLAUDE_CODE_OAUTH_TOKEN, "caller token 'a' $(touch broken)");
  assert.equal(seen.env.ANTHROPIC_API_KEY, null);
  assert.equal(seen.env.ANTHROPIC_BASE_URL, null);
  assert.equal(existsSync(file), false, 'the chat deletes the login file after it reads it');
  assert.equal(existsSync(join(f.base, 'broken')), false, 'the value is never shell syntax');
});

const ACCOUNTS = f => [
  { name: 'Claude (account-a)', kind: 'claude', command: f.wrapper('claude-account-a'), env: { ACCOUNT_MARK: 'a', CLAUDE_CODE_OAUTH_TOKEN: 'entry-token-a' } },
  { name: 'Claude (account-b)', kind: 'claude', command: f.wrapper('claude-account-b'), env: { ACCOUNT_MARK: 'b', CLAUDE_CODE_OAUTH_TOKEN: 'entry-token-b' } },
];
async function accounts(t, extra) {
  const f = await world(t);
  const entries = ACCOUNTS(f);
  f.agents(entries, extra);
  f.entries = entries;
  f.start = async agent => { f.pendingCommand = entries.find(entry => entry.name === agent)?.command; return startRun({ name: 'small-change', issue: '17', agent, cwd: f.source, packageRoot }, f.ports); };
  return f;
}

test('2901: an agents.json entry starts its own command with its env, saves only names, and reopen uses the saved entry', async t => {
  const f = await accounts(t);
  f.ports.env.ANTHROPIC_API_KEY = 'caller-key';
  const started = await f.start('Claude (account-a)');
  assert.equal(started.exitCode, 0, started.message);
  assert.match(started.message, /Claude \(agents\.json entry "Claude \(account-a\)"\) works in Herdr session pdd/);
  const run = f.record(), bytes = readFileSync(join(run.runDir, 'status.json'), 'utf8');
  assert.equal(run.agent, 'claude');
  assert.deepEqual(run.agentDefinition, { name: 'Claude (account-a)', kind: 'claude', command: f.entries[0].command, envNames: ['ACCOUNT_MARK', 'CLAUDE_CODE_OAUTH_TOKEN'] });
  for (const secret of ['entry-token-a', 'caller-key']) assert.ok(!bytes.includes(secret), `the run record keeps no ${secret}`);
  assert.match((await runStatus({ ref: '17', cwd: f.source }, f.ports)).message, /· small-change · claude "Claude \(account-a\)"\n/);
  const [first] = f.commands;
  assert.ok(first.includes(` ${quote(f.entries[0].command)} --dangerously-skip-permissions --session-id ${run.chats[0].session.id} `), first);
  assert.doesNotMatch(first, / claude --dangerously/);
  for (const secret of ['entry-token-a', 'caller-key']) assert.ok(!first.includes(secret));
  let seen = f.execute(first);
  assert.equal(seen.program, 'claude-account-a');
  assert.deepEqual([seen.env.ACCOUNT_MARK, seen.env.CLAUDE_CODE_OAUTH_TOKEN, seen.env.ANTHROPIC_API_KEY, seen.env.ANTHROPIC_AUTH_TOKEN], ['a', 'entry-token-a', 'caller-key', null]);

  // Reopen after the chat ended: the same entry, and its env values read again from agents.json (a rotated token).
  const chat = f.record().chats[0], pane = f.herdr.paneOf(chat);
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  pane.agent = null;
  f.agents([{ ...f.entries[0], env: { ACCOUNT_MARK: 'a', CLAUDE_CODE_OAUTH_TOKEN: 'entry-token-a-rotated' } }, f.entries[1]]);
  delete f.ports.env.ANTHROPIC_API_KEY;
  const reopened = await openRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' } });
  assert.equal(reopened.exitCode, 0, reopened.message);
  const resume = f.commands.at(-1);
  assert.ok(resume.includes(` ${quote(f.entries[0].command)} --dangerously-skip-permissions --resume '${chat.session.id}'`), resume);
  seen = f.execute(resume);
  assert.equal(seen.program, 'claude-account-a');
  assert.deepEqual([seen.env.ACCOUNT_MARK, seen.env.CLAUDE_CODE_OAUTH_TOKEN, seen.env.ANTHROPIC_API_KEY], ['a', 'entry-token-a-rotated', null]);
});

test('2901: a fresh session (--new) of an agents.json run starts the same entry', async t => {
  const f = await accounts(t);
  assert.equal((await f.start('Claude (account-a)')).exitCode, 0);
  const fresh = await openRun({ ref: '17', cwd: f.source, newSession: true }, f.ports);
  assert.equal(fresh.exitCode, 0, fresh.message);
  assert.equal(f.commands.length, 2);
  assert.ok(f.commands[1].includes(` ${quote(f.entries[0].command)} --dangerously-skip-permissions --session-id ${f.record().chats.at(-1).session.id} `), f.commands[1]);
  const seen = f.execute(f.commands[1]);
  assert.deepEqual([seen.program, seen.env.ACCOUNT_MARK, seen.env.CLAUDE_CODE_OAUTH_TOKEN, seen.env.ANTHROPIC_API_KEY], ['claude-account-a', 'a', 'entry-token-a', null]);
});

test('2901: a run whose agents.json entry is gone refuses to resume, and sends nothing', async t => {
  const f = await accounts(t);
  assert.equal((await f.start('Claude (account-a)')).exitCode, 0);
  const chat = f.record().chats[0], pane = f.herdr.paneOf(chat);
  assert.equal((await openRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  pane.agent = null;
  f.agents([f.entries[1]]);
  const before = f.commands.length;
  const reopened = await openRun({ ref: '17', cwd: f.source }, { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' } });
  assert.notEqual(reopened.exitCode, 0);
  assert.match(reopened.message, /This run uses the agents\.json entry "Claude \(account-a\)" \(claude\), but ~\/\.config\/pdd\/agents\.json has no such claude entry now\. Add it again, then retry\./);
  assert.equal(f.commands.length, before, 'no launch or resume was sent');
});

test('2901: the start sign-in check runs the entry command with its env, and a signed-out entry refuses without its command text', async t => {
  const f = await accounts(t);
  const env = { HOME: f.ports.env.HOME, PATH: `${join(f.base, 'bin')}:/usr/bin:/bin` };
  const ready = await checkWorkflowAgents({ cwd: f.source, env, requested: 'Claude (account-a)' });
  assert.deepEqual(ready, { ok: true, agent: 'claude', message: '', name: 'Claude (account-a)' });
  f.agents([{ ...f.entries[0], env: { ACCOUNT_MARK: 'signed-out', CLAUDE_CODE_OAUTH_TOKEN: 'x' } }]);
  const out = await checkWorkflowAgents({ cwd: f.source, env, requested: 'Claude (account-a)' });
  assert.deepEqual(out, { ok: false, agent: null, message: 'Claude Code (agents.json entry "Claude (account-a)") is not signed in. Sign in with that entry\'s command, then run the command again.' });
  assert.ok(!out.message.includes(f.entries[0].command));
  // Through the public command: the runner gets the entry name, after the same check.
  f.agents(f.entries);
  let given;
  const stderr = { text: '', write(value) { this.text += value; } };
  const code = await runPdd(['workflow', 'run', 'small-change', '17', '--agent', 'Claude (account-b)'], { cwd: f.source, env, stdout: { write() {} }, stderr,
    workflowRunner: { startRun: async input => { given = input.agent; return { exitCode: 0, message: 'started' }; } } });
  assert.equal(code, 0, stderr.text);
  assert.equal(given, 'Claude (account-b)');
});

test('2901: an unknown --agent name refuses with the available names before any effect', async t => {
  const f = await accounts(t);
  const env = { HOME: f.ports.env.HOME, PATH: `${join(f.base, 'bin')}:/usr/bin:/bin` };
  const expected = 'Unknown agent "Claude (account-c)". Choose --agent codex, --agent claude, --agent gemini or --agent agy, or a name from ~/.config/pdd/agents.json: "Claude (account-a)", "Claude (account-b)".';
  let called = false;
  const stderr = { text: '', write(value) { this.text += value; } };
  const code = await runPdd(['workflow', 'run', 'small-change', '17', '--agent', 'Claude (account-c)'], { cwd: f.source, env, stdout: { write() {} }, stderr,
    workflowRunner: { startRun: async () => { called = true; return { exitCode: 0, message: 'started' }; } } });
  assert.equal(code, 1);
  assert.ok(stderr.text.includes(expected), stderr.text);
  assert.equal(called, false);
  const direct = await f.start('Claude (account-c)');
  assert.deepEqual(direct, { exitCode: 1, message: expected });
  assert.deepEqual(f.herdr.calls, []);
  assert.deepEqual(f.commands, []);
});

test('2901: built-in names keep the built-in agent, also when agents.json has an entry with that name', async t => {
  const f = await world(t);
  const impostor = f.wrapper('not-claude');
  f.agents([{ name: 'claude', kind: 'claude', command: impostor, env: { ACCOUNT_MARK: 'impostor' } }], { include_defaults: false });
  const probes = [];
  const checked = await checkWorkflowAgents({ cwd: f.source, env: f.ports.env, requested: 'claude' },
    { run: async (command, args) => { probes.push([command, ...args]); return { code: 0, stdout: '{"loggedIn":true}', stderr: '' }; } });
  assert.deepEqual(checked, { ok: true, agent: 'claude', message: '' });
  assert.deepEqual(probes, [['claude', 'auth', 'status']]);
  const started = await f.start('claude');
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(Object.hasOwn(f.record(), 'agentDefinition'), false);
  const [command] = f.commands;
  assert.match(command, / claude --dangerously-skip-permissions --session-id [0-9a-f-]{36} /);
  assert.ok(!command.includes(impostor));
  const seen = f.execute(command);
  assert.equal(seen.program, 'claude');
  assert.equal(seen.env.ACCOUNT_MARK, null);
});

// An automatic start by the coordinator may pass an entry name; the same admission and ownership checks apply.
test('2901: an Autopilot coordinator start with an agents.json entry name keeps its automatic origin and starts the entry', async t => {
  const f = await accounts(t);
  const origin = { repository: 'example/project', coordinatorId: 'coordinator-a', machine: 'machine-a', claim: { commentId: '11', labelEventId: '12' } };
  const envelope = { version: 'pdd.autopilot-coordinator.v1', repository: origin.repository, coordinatorId: origin.coordinatorId, machine: origin.machine, activation: 'activation' };
  const root = realpathSync(f.source), stateRoot = join(f.state, 'autopilot'); mkdirSync(stateRoot, { recursive: true });
  writeFileSync(join(f.source, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [] } }));
  const state = { enabled: true, repo: origin.repository, cwd: root, coordinatorId: origin.coordinatorId, machine: origin.machine, activatedAt: 'activation',
    startAction: { command: 'pdd autopilot start', repository: origin.repository, mode: 'auto' }, paneId: 'coordinator-pane', ownerLaunch: { paneId: 'coordinator-pane', coordinator: envelope } };
  writeFileSync(join(stateRoot, `${createHash('sha256').update(root).digest('hex').slice(0, 20)}.json`), JSON.stringify(state));
  const fixturePath = join(f.base, 'reader.json'), logPath = join(f.base, 'gh.log');
  writeFileSync(fixturePath, JSON.stringify({ labels: ['pdd:working'], events: [{ id: 12, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'example' } }],
    comments: [{ id: 11, user: { login: 'example' }, body: JSON.stringify({ repository: origin.repository, coordinatorId: origin.coordinatorId, machine: origin.machine, labelEventId: '12' }) }] }));
  const exec = promisify(callback), original = f.ports.execFile;
  const execFile = (file, args, opts) => file === 'gh' && args[0] === 'api' && args[1] === '--include'
    ? exec(process.execPath, [join(packageRoot, 'test/helpers/continuation-fake-gh.mjs'), ...args], { ...opts, env: { ...process.env, READER_FIXTURE_FILE: fixturePath, READER_GH_LOG: logPath } })
    : original(file, args, opts);
  f.pendingCommand = f.entries[1].command;
  const result = await startRun({ name: 'small-change', issue: '17', agent: 'Claude (account-b)', cwd: f.source, packageRoot, origin: 'autopilot', decisionId: '11234567-89ab-4cde-8fab-123456789abc' },
    { ...f.ports, env: { ...f.ports.env, HERDR_SOCKET_PATH: '/fixture/sessions/pdd-autopilot/socket', HERDR_PANE_ID: 'coordinator-pane' }, execFile, autopilotStateRoot: stateRoot,
      checkDependencyStart: async () => ({ allowed: true, reason: 'ok' }) });
  assert.equal(result.exitCode, 0, result.message);
  assert.deepEqual(f.record().automaticOrigin, origin);
  assert.equal(f.record().agentDefinition.name, 'Claude (account-b)');
  assert.equal(f.execute(f.commands[0]).program, 'claude-account-b');
});

// Repair 1 of 2901: the login file must go before any of its values takes effect, a failed delete must stop the agent,
// shell-reserved entry env names refuse plainly, and files of launches that never ran do not stay.
test('2901: an entry PATH without rm cannot keep the login file: the chat deletes it before any value takes effect', async t => {
  const f = await accounts(t);
  const noRm = join(f.base, 'no-rm'); mkdirSync(noRm);
  f.agents([{ ...f.entries[0], env: { ...f.entries[0].env, PATH: noRm } }, f.entries[1]]);
  const started = await f.start('Claude (account-a)');
  assert.equal(started.exitCode, 0, started.message);
  const [command] = f.commands, file = loginFileOf(command);
  assert.ok(file && existsSync(file), `a login file in: ${command}`);
  assert.ok(!command.includes(noRm), 'the entry PATH is not in the pane command');
  const seen = f.execute(command);
  assert.deepEqual([seen.program, seen.env.ACCOUNT_MARK, seen.env.CLAUDE_CODE_OAUTH_TOKEN], ['claude-account-a', 'a', 'entry-token-a']);
  assert.equal(existsSync(file), false, 'the chat deleted the login file although the entry PATH has no rm');
  assert.deepEqual(loginFiles(f), []);
});

test('2901: when the chat cannot delete the login file, the agent does not start', { skip: process.getuid?.() === 0 && 'root can delete in a read-only folder' }, async t => {
  const f = await world(t);
  f.ports.env.CLAUDE_CODE_OAUTH_TOKEN = 'caller-token';
  assert.equal((await f.start('claude')).exitCode, 0);
  const [command] = f.commands, runDir = f.record().runDir, mode = statSync(runDir).mode & 0o777;
  chmodSync(runDir, 0o500);
  let error = null;
  try { f.execute(command); } catch (caught) { error = caught; } finally { chmodSync(runDir, mode); }
  assert.ok(error && error.status !== 0, 'the chat line fails');
  assert.ok(!String(error.stdout).includes('"program"'), 'the agent did not start');
  assert.equal(loginFiles(f).length, 1, 'the file stays for the next clean-up');
});

test('2901: an entry env with a shell-reserved name refuses with a clear message, at start and at a later launch', async t => {
  const f = await accounts(t);
  f.agents([{ ...f.entries[0], env: { ...f.entries[0].env, UID: '0' } }, f.entries[1]]);
  const expected = 'The agents.json entry "Claude (account-a)" sets names in env that the shell controls: UID. pdd cannot give them to the chat. Remove them from that entry\'s env, then run the command again.';
  assert.deepEqual(await f.start('Claude (account-a)'), { exitCode: 1, message: expected });
  assert.deepEqual(f.herdr.calls, []);
  assert.deepEqual(f.commands, []);
  const probes = [];
  const checked = await checkWorkflowAgents({ cwd: f.source, env: f.ports.env, requested: 'Claude (account-a)' },
    { run: async (...args) => { probes.push(args); return { code: 0, stdout: '{"loggedIn":true}', stderr: '' }; } });
  assert.deepEqual(checked, { ok: false, agent: null, message: expected });
  assert.deepEqual(probes, [], 'no sign-in probe for a refused entry');
  // A run that started with a clean entry refuses a later launch when the entry now sets reserved names.
  f.agents(f.entries);
  assert.equal((await f.start('Claude (account-a)')).exitCode, 0);
  f.agents([{ ...f.entries[0], env: { ...f.entries[0].env, PPID: '1', EUID: '0' } }, f.entries[1]]);
  const before = f.commands.length;
  const fresh = await openRun({ ref: '17', cwd: f.source, newSession: true }, f.ports);
  assert.notEqual(fresh.exitCode, 0);
  assert.ok(fresh.message.includes('The agents.json entry "Claude (account-a)" sets names in env that the shell controls: PPID, EUID. pdd cannot give them to the chat.'), fresh.message);
  assert.equal(f.commands.length, before, 'no launch was sent');
});

test('2901: stale login files go at the next status, launch and cancel of the run; nothing else in the run folder is touched', async t => {
  const f = await world(t);
  assert.equal((await f.start('claude')).exitCode, 0);
  const runDir = f.record().runDir, old = (Date.now() - 10 * 60_000) / 1000, names = () => readdirSync(runDir);
  const file = (name, stale = true) => { writeFileSync(join(runDir, name), "export CLAUDE_CODE_OAUTH_TOKEN='left'\n", { mode: 0o600 }); if (stale) utimesSync(join(runDir, name), old, old); return name; };
  const staleA = file(`login-${randomUUID()}.env`), fresh = file(`login-${randomUUID()}.env`, false);
  const others = [file('login-not-a-uuid.env'), file('notes.env'), file(`old-login-${randomUUID()}.env`)];
  const outside = join(f.base, 'outside.env'); writeFileSync(outside, 'keep');
  const link = `login-${randomUUID()}.env`; symlinkSync(outside, join(runDir, link)); lutimesSync(join(runDir, link), old, old);
  const folder = `login-${randomUUID()}.env`; mkdirSync(join(runDir, folder)); utimesSync(join(runDir, folder), old, old);
  const kept = [fresh, ...others, link, folder];

  assert.equal((await runStatus({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  assert.ok(!names().includes(staleA), 'status removes a stale login file');
  for (const name of kept) assert.ok(names().includes(name), `status keeps ${name}`);

  const staleB = file(`login-${randomUUID()}.env`);
  assert.equal((await openRun({ ref: '17', cwd: f.source, newSession: true }, f.ports)).exitCode, 0);
  assert.ok(!names().includes(staleB), 'a launch removes a stale login file');
  for (const name of kept) assert.ok(names().includes(name), `a launch keeps ${name}`);

  assert.equal((await cancelRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  assert.ok(!names().includes(fresh), 'cancel removes every login file, also a new one');
  for (const name of [...others, link, folder]) assert.ok(names().includes(name), `cancel keeps ${name}`);
  assert.equal(readFileSync(outside, 'utf8'), 'keep', 'the symlink target is untouched');
});
