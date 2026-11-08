import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, writeFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { chooseWorkflowAgent, checkWorkflowAgents } from '../src/workflow-agents.mjs';
import { setupWithWorkflowAgent } from '../src/workflow-setup.mjs';
import * as chat from '../src/workflow-chat.mjs';
const { chatCommand, ownSession } = chat;
import { runPdd } from '../src/pdd-cli.mjs';
import { stepDone, approveRun, openRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const result = (stdout, code = 0, stderr = '') => ({ code, stdout, stderr });
const missing = () => { throw Object.assign(Error('not installed'), { code: 'ENOENT', executableMissing: true }); };
const models = 'gemini-4-argon-high\tGemini 4 Argon (High)\n';
const signedOut = result('', 1, 'Fetching available models...\nError: Please sign in to view available models. Launch the CLI without arguments to sign in.');

test('a signed-in Antigravity CLI alone admits workflow selection and setup with one agy models probe', async () => {
  const env = { HOME: '/scratch/home', PATH: '/scratch/bin' }, calls = [];
  const run = async (command, args, options) => { calls.push([command, args]); assert.equal(options.env, env); return command === 'agy' ? result(models) : missing(); };
  assert.deepEqual(await checkWorkflowAgents({ env }, { run }), { ok: true, agent: 'agy', message: '' });
  let selected;
  assert.equal(await setupWithWorkflowAgent({ cwd: '/scratch', env }, { run, stderr: { write: () => assert.fail('no hint for agy') }, setup: async input => { selected = input.agent; return 0; } }), 0);
  assert.equal(selected, 'agy');
  assert.deepEqual(calls.filter(([c]) => c === 'agy').map(([, a]) => a), [['models'], ['models']]);
});

test('agy readiness: signed out gives the sign-in line, explicit agy never falls back, Codex/Claude/Gemini keep precedence', async () => {
  const out = await checkWorkflowAgents({ requested: 'agy' }, { run: async () => signedOut });
  assert.deepEqual(out, { ok: false, agent: null, message: 'Antigravity CLI is not signed in. Run: agy' });
  const odd = await checkWorkflowAgents({ requested: 'agy' }, { run: async () => result('', 2, 'boom') });
  assert.equal(odd.message, 'Antigravity CLI sign-in could not be checked. Run: agy models');
  assert.equal(chooseWorkflowAgent({ codex: 'ready', claude: 'ready', gemini: 'ready', agy: 'signed_out', requested: 'agy' }).ok, false);
  assert.equal(chooseWorkflowAgent({ codex: 'ready', claude: 'ready', gemini: 'ready', agy: 'ready' }).agent, 'codex');
  assert.equal(chooseWorkflowAgent({ codex: 'missing', claude: 'missing', gemini: 'ready', agy: 'ready' }).agent, 'gemini');
  const none = chooseWorkflowAgent({ codex: 'missing', claude: 'missing', gemini: 'missing', agy: 'missing' });
  assert.match(none.message, /^Install Codex, Claude Code, Gemini CLI or Antigravity CLI first\./);
  assert.match(none.message, /Antigravity CLI: https:\/\/antigravity\.google\/docs\/cli\//);
});

test('workflow run and product start accept --agent agy through the public command dispatch', async () => {
  let started, productAgent;
  const common = { cwd: packageRoot, env: { HOME: '/test' }, stdout: { write() {} }, stderr: { write() {} } };
  assert.equal(await runPdd(['workflow', 'run', 'small-change', '17', '--agent', 'agy'], { ...common,
    workflowAgents: { checkWorkflowAgents: async input => { assert.equal(input.requested, 'agy'); return { ok: true, agent: 'agy', message: '' }; } },
    workflowRunner: { startRun: async input => { started = input.agent; return { exitCode: 0, message: 'started' }; } } }), 0);
  assert.equal(started, 'agy');
  assert.equal(await runPdd(['product', 'start', 'G-1', '--agent', 'agy'], { ...common, product: { runProduct: async input => { productAgent = input.agent; return { exitCode: 0, message: 'started' }; } } }), 0);
  assert.equal(productAgent, 'agy');
});

test('agy shell launch: full access, pdd run and worktree folders in its workspace, literal message, resume by conversation id', t => {
  const root = mkdtempSync(join(tmpdir(), "pdd-agy 'launch'-")); t.after(() => rmSync(root, { recursive: true, force: true }));
  const bin = join(root, 'bin'); mkdirSync(bin);
  writeFileSync(join(bin, 'agy'), `#!${process.execPath}\nconsole.log(JSON.stringify({args:process.argv.slice(2),marker:process.env.PDD_AGENT_SESSION,codex:process.env.CODEX_HOME??null}));`, { mode: 0o755 });
  const run = { commonDir: join(root, 'clone/.git'), sourceRoot: join(root, 'clone'), runDir: join(root, 'clone/.git/pdd/runs/17'), root: join(root, 'clone.pdd-worktrees/17-fix') };
  mkdirSync(run.root, { recursive: true }); // The chat line starts with cd to the worktree, so the worktree exists.
  assert.equal(typeof chat.agentDirs, 'function');
  const dirs = chat.agentDirs(run);
  assert.deepEqual(dirs, [join(root, 'clone/.git/pdd/runs'), join(root, 'clone.pdd-worktrees')]);
  const messageFile = join(root, "start 'message'.md"), message = 'Use pdd-small-change.\nLiteral $(touch broken) `text`'; writeFileSync(messageFile, message);
  const launch = command => JSON.parse(execFileSync('/bin/sh', ['-c', command], { cwd: root, env: { HOME: root, PATH: `${bin}:/usr/bin:/bin` }, encoding: 'utf8' }));
  assert.deepEqual(launch(chatCommand({ agent: 'agy', cwd: run.root, messageFile, addDirs: dirs, configDir: '/ignored' })),
    { args: ['--dangerously-skip-permissions', '--settings', JSON.stringify({ trustedWorkspaces: [run.root] }), '--add-dir', dirs[0], '--add-dir', dirs[1], '--prompt-interactive', message], marker: '1', codex: null });
  const id = '11111111-1111-4111-8111-111111111111';
  assert.deepEqual(launch(chatCommand({ agent: 'agy', cwd: run.root, resumeId: id, addDirs: dirs })).args,
    ['--dangerously-skip-permissions', '--settings', JSON.stringify({ trustedWorkspaces: [run.root] }), '--add-dir', dirs[0], '--add-dir', dirs[1], '--conversation', id]);
  assert.deepEqual(chat.agentDirs({ runDir: run.runDir, root: run.root }), [], 'no folders without commonDir and sourceRoot');
  // Other agents ignore the folders.
  assert.doesNotMatch(chatCommand({ agent: 'claude', cwd: run.root, messageFile, sessionId: id, addDirs: dirs }), /--add-dir/);
});

test('agy run starts and reopens the same Herdr chat with its folders; recorded words approve without chat-file evidence', async t => {
  const f = await fixture(t, { agent: 'agy' });
  const herdr = f.ports.herdr; f.ports.herdr = async args => {
    const reply = await herdr(args);
    if (args[0] === 'pane' && args[1] === 'run' && args[3].includes(' agy ')) f.herdr.panes.find(p => p.pane_id === args[2]).agent = { agent: 'agy', agent_status: 'idle', prompts: [] };
    return reply;
  };
  f.ports.findNativeSessions = async () => assert.fail('agy has no native chat-file evidence reader');
  const started = await f.run();
  assert.equal(started.exitCode, 0, started.message); assert.match(started.message, /Antigravity works in Herdr session pdd/);
  let run = f.record(); assert.equal(run.agent, 'agy'); assert.equal(run.configDir, null);
  const launches = () => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run');
  const line = launches()[0][3];
  assert.ok(line.replace(/ PDD_BIN='[^']*'/, '').startsWith(`cd '${run.root}' && env PDD_AGENT_SESSION=1 agy --dangerously-skip-permissions --settings '{"trustedWorkspaces":[${JSON.stringify(run.root)}]}' --add-dir `), line);
  for (const dir of [join(run.commonDir, 'pdd/runs'), `${run.sourceRoot}.pdd-worktrees`]) assert.ok(line.includes(`--add-dir '${dir}'`), line);
  assert.match(line, /PDD_BIN='/);
  assert.ok(run.chats[0].messageFile.startsWith(dirname(run.runDir)));
  assert.match(readFileSync(run.chats[0].messageFile, 'utf8'), /pdd-small-change.*SKILL\.md/);
  assert.equal((await openRun({ ref: '17', cwd: run.root }, f.ports)).exitCode, 0); assert.equal(launches().length, 1);
  assert.equal((await stepDone({ step: 'scope', summary: 'Scope ready', cwd: run.root }, f.agentPorts())).exitCode, 0);
  const words = 'Yes, this scope is right.';
  const approved = await approveRun({ ref: '17', cwd: run.root, said: words }, f.agentPorts());
  assert.equal(approved.exitCode, 0, approved.message); run = f.record();
  assert.equal(run.decisions[0].evidence.route, 'said'); assert.equal(run.agent, 'agy');
  assert.deepEqual(await ownSession({ run, chat: run.chats[0], since: 0, ports: f.ports }), { kind: 'unknown' });
});

test('Gemini CLI selected without a paid key or Vertex setting prints one hint line to use Antigravity CLI', async () => {
  const run = async command => command === 'gemini' ? result('0.67.1') : missing();
  const free = await checkWorkflowAgents({ env: { HOME: '/h' } }, { run });
  assert.equal(free.agent, 'gemini'); assert.equal(free.hint, 'With a free or Google One account, Gemini CLI does not run; use Antigravity CLI: --agent agy.');
  for (const key of ['GEMINI_API_KEY', 'GOOGLE_API_KEY', 'GOOGLE_GENAI_USE_VERTEXAI', 'GOOGLE_GENAI_USE_GCA'])
    assert.deepEqual(await checkWorkflowAgents({ env: { HOME: '/h', [key]: 'x' } }, { run }), { ok: true, agent: 'gemini', message: '' });
  const err = { text: '', write(s) { this.text += s; } };
  assert.equal(await runPdd(['workflow', 'run', 'small-change', '17', '--agent', 'gemini'], { cwd: packageRoot, env: { HOME: '/h' }, stdout: { write() {} }, stderr: err,
    workflowAgentPorts: { run }, workflowRunner: { startRun: async () => ({ exitCode: 0, message: 'started' }) } }), 0);
  assert.equal(err.text.trim().split('\n').length, 1); assert.match(err.text, /--agent agy/);
});
