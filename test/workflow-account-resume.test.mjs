// Synthetic profile directories and injected Herdr only: no account files or native agents.
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, renameSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { homedir } from 'node:os';
import { join, relative } from 'node:path';
import { openRun, stepDone, approveRun, askPerson, changeRun, cancelRun } from '../src/workflow-runner.mjs';
import { restartChat, expandHome } from '../src/workflow-chat.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const quote = value => `'${value.replace(/'/g, `'\\''`)}'`;
// Admit only literal single-quoted chunks and escaped quotes, then let a real
// POSIX shell parse the recorded token. No expansion or command syntax is admitted.
function parsedSelectedPath(command) {
  const match = /(?:^| )CODEX_HOME=((?:'[^']*'|\\')+) codex /.exec(command);
  assert.ok(match, 'Recorded CODEX_HOME must consist only of shell literal chunks');
  return execFileSync('/bin/sh', ['-c', `printf '%s' ${match[1]}`], { encoding: 'utf8', env: {} });
}
const calls = (f, group, verb) => f.herdr.calls.filter(args => args[0] === group && args[1] === verb);
const effects = f => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run'
  || ['tab', 'workspace', 'worktree'].includes(args[0]) && ['create', 'close', 'open'].includes(args[1]));
const open = (f, input = {}, ports = f.ports) => openRun({ ref: '17', cwd: f.source, packageRoot, ...input }, ports);
const bytes = f => readFileSync(join(f.record().runDir, 'status.json'));
const journal = f => readFileSync(join(f.record().runDir, 'delivery-journal.json'));
const lost = () => Object.assign(Error('Synthetic lost reply'), { code: 'server_unavailable' });
const keptFields = ['runId', 'repo', 'number', 'workflow', 'root', 'sourceRoot', 'commonDir', 'branch', 'baseBranch', 'baseSha',
  'area', 'state', 'done', 'gate', 'question', 'approvalRecord', 'decisions', 'pr', 'previous'];
const progress = run => Object.fromEntries(keptFields.map(key => [key, run[key]]));
const folder = (f, name) => { const path = join(f.base, name); mkdirSync(path, { recursive: true }); return path; };

async function started(t, { saved = 'old', agent = 'codex' } = {}) {
  const f = await fixture(t, { agent });
  if (agent === 'codex' && saved !== null) f.ports.env.CODEX_HOME = folder(f, 'old-profile');
  assert.equal((await f.run()).exitCode, 0);
  f.oldConfig = f.record().configDir;
  f.work5 = folder(f, 'synthetic Work5');
  f.work6 = folder(f, 'synthetic Work6');
  f.herdr.calls.length = 0;
  return f;
}

async function advance(f) {
  f.tick(); // Later native sessions need a distinct launch window.
  const completed = await stepDone({ step: 'scope', summary: 'Keep approved scope and history.', cwd: f.record().root }, f.agentPorts());
  assert.equal(completed.exitCode, 0, completed.message);
  const approved = await approveRun({ ref: '17', cwd: f.source }, f.ports);
  assert.equal(approved.exitCode, 0, approved.message);
  assert.equal(f.record().area, 1);
}

// Interrupt an actual public checkpoint, without manufacturing saved run state.
function checkpointFault(f, phase, { persisted = true } = {}) {
  let fired = false;
  return { renameSync(from, to) {
    const selected = to === join(f.record().runDir, 'status.json')
      && JSON.parse(readFileSync(from, 'utf8')).chatReplacement?.phase === phase && !fired;
    if (selected && !persisted) { fired = true; throw Error(`Rejected ${phase} checkpoint`); }
    renameSync(from, to);
    if (selected) { fired = true; throw Error(`Interrupted after ${phase}`); }
  } };
}

for (const saved of [null, 'old']) test(`2907 saved ${saved} selects Work5 and later areas inherit it`, async t => {
  const f = await started(t, { saved }), before = f.record(), original = before.chats.at(-1);
  const originalBytes = readFileSync(original.messageFile);
  f.ports.env.CODEX_HOME = f.work5;
  f.tick(); // A fresh account session starts after the original session.
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  const after = f.record(), replacement = after.chats.at(-1);
  assert.equal(replacement.configDir, f.work5, '2907 replacement must use explicit Work5 CODEX_HOME');
  assert.equal(after.configDir, f.work5);
  assert.equal(after.chatReplacement.configDir, f.work5);
  assert.deepEqual(progress(after), progress(before));
  assert.equal(result.message, 'Started one fresh plan chat in Herdr session pdd. The run, completed work, gates and approvals are kept.');
  assert.notEqual(replacement.paneId, original.paneId);
  assert.notEqual(replacement.tabId, original.tabId);
  assert.deepEqual(calls(f, 'tab', 'close').map(args => args[2]), [original.tabId]);
  assert.equal(calls(f, 'pane', 'run').length, 1);
  const command = calls(f, 'pane', 'run')[0][3];
  assert.ok(command.includes(`CODEX_HOME=${quote(f.work5)}`));
  assert.equal(command.match(/CODEX_HOME=/g).length, 1);
  assert.match(command, /PDD_AGENT_SESSION=1.*PDD_BIN=.*codex --no-daemon --dangerously-bypass-approvals-and-sandbox/);
  assert.match(command, /trust_level="trusted"/);
  assert.doesNotMatch(command, /\bresume\b|--session-id|--resume/);
  assert.equal(after.abandonedChats.length, 1);
  const archived = after.abandonedChats[0];
  for (const key of ['configDir', 'tabId', 'paneId', 'terminalId', 'workspaceId']) assert.deepEqual(archived[key], original[key]);
  assert.ok(readFileSync(archived.messageFile).equals(originalBytes));
  assert.ok(archived.session.id, 'Archive the positively observed original session');
  f.ports.env.CODEX_HOME = f.work6;
  f.herdr.calls.length = 0;
  await advance(f);
  assert.equal(f.record().configDir, f.work5);
  assert.equal(f.record().chats.at(-1).configDir, f.work5);
  assert.ok(calls(f, 'pane', 'run')[0][3].includes(`CODEX_HOME=${quote(f.work5)}`));
});

test('2907 a missing original folder cannot veto a valid Work5 replacement', async t => {
  const f = await started(t);
  rmSync(f.oldConfig, { recursive: true });
  f.ports.env.CODEX_HOME = f.work5;
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.record().configDir, f.work5);
  assert.equal(f.record().abandonedChats[0].configDir, f.oldConfig);
});

for (const form of ['absolute', 'tilde-child', 'tilde-home', 'relative', 'quotes']) test(`2907 normalizes ${form} from invocation cwd and quotes it literally`, async t => {
  const f = await started(t);
  let incoming = f.work5, expected = f.work5;
  if (form === 'tilde-child') { expected = join(f.ports.env.HOME, 'work5'); mkdirSync(expected); incoming = '~/work5'; }
  if (form === 'tilde-home') { expected = f.ports.env.HOME; incoming = '~'; }
  if (form === 'relative') incoming = relative(f.source, f.work5);
  if (form === 'quotes') { expected = folder(f, "Work5 'quoted' $literal `text`"); incoming = expected; }
  f.ports.env.CODEX_HOME = incoming;
  assert.notEqual(f.source, f.record().root);
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.record().configDir, expected);
  assert.equal(f.record().chatReplacement.configDir, expected);
  assert.ok(calls(f, 'pane', 'run')[0][3].includes(`CODEX_HOME=${quote(expected)}`));
  assert.equal(parsedSelectedPath(calls(f, 'pane', 'run')[0][3]), expected, 'The actual shell parser must round-trip the selected path as literal bytes');
});

test('2907 HOME fallback uses the existing home expansion policy', () => {
  assert.equal(expandHome('~', {}), homedir());
  assert.equal(expandHome('~/work5', {}), join(homedir(), 'work5'));
});

test('2907 full replacement expands tilde with OS home when HOME is absent', async t => {
  const f = await started(t);
  delete f.ports.env.HOME; f.ports.env.CODEX_HOME = '~';
  // Test expansion and shell quoting without opening the host's account config.
  const configReads = [];
  f.ports.profileFs = {readFileSync(path) {
    configReads.push(path);
    throw Object.assign(Error('No synthetic account config'), {code:'ENOENT'});
  }};
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  assert.deepEqual(configReads, [join(homedir(), 'config.toml')]);
  assert.equal(f.record().configDir, homedir());
  assert.equal(f.record().chatReplacement.configDir, homedir());
  assert.equal(f.record().chats.at(-1).configDir, homedir());
  assert.equal(parsedSelectedPath(calls(f, 'pane', 'run')[0][3]), homedir());
});

for (const broken of [false, true]) test(`2907 selected ${broken ? 'broken' : 'directory'} symlink follows startup directory policy`, async t => {
  const f = await started(t), selected = join(f.base, 'Work5 profile link');
  symlinkSync(broken ? join(f.base, 'absent-target') : f.work5, selected, 'dir');
  f.ports.env.CODEX_HOME = selected;
  const before = bytes(f), result = await open(f, { newSession: true });
  assert.equal(result.exitCode, broken ? 1 : 0, result.message);
  if (broken) {
    assert.equal(result.message, `CODEX_HOME is "${selected}", but that folder does not exist. Fix CODEX_HOME and run the command again.`);
    assert.ok(bytes(f).equals(before)); assert.deepEqual(effects(f), []);
  } else {
    assert.equal(f.record().configDir, selected, 'Keep the selected symlink path without realpath account resolution');
    assert.equal(f.record().chatReplacement.configDir, selected);
    assert.equal(parsedSelectedPath(calls(f, 'pane', 'run')[0][3]), selected);
  }
});

test('2907 bounded profile-selection matrix (12 saved/selection/close combinations)', async t => {
  const inventory = JSON.parse(readFileSync(new URL('./fixtures/workflow-open-replacement.json', import.meta.url), 'utf8'));
  const domain = inventory.cases.find(row => row.id === 'codex-account-selection-matrix').input;
  // Oracle: Story AC2 and Rules to check. These are approved input bounds,
  // independent of the implementation's selection or checkpoint helpers.
  for (const saved of domain.savedProfiles) for (const incoming of domain.incomingSelections) for (const close of domain.closeOutcomes) {
    await t.test(`saved=${saved}, incoming=${incoming}, close=${close}`, async row => {
      const f = await started(row, { saved }), before = f.record(), original = before.chats.at(-1);
      const selected = incoming === 'Work5' ? f.work5 : f.oldConfig;
      if (incoming === 'unset') delete f.ports.env.CODEX_HOME;
      else f.ports.env.CODEX_HOME = incoming === 'empty' ? '' : f.work5;
      const healthy = f.ports.herdr;
      f.ports.herdr = async args => {
        if (args[0] === 'tab' && args[1] === 'close') {
          const attempt = f.record().chatReplacement;
          assert.equal(attempt.configDir, selected, 'Pin the selected profile before predecessor closure');
          assert.equal(f.record().configDir, f.oldConfig, 'Before launch installation, keep the inherited run profile');
          const reply = await healthy(args);
          if (close === 'unknown') throw lost();
          return reply;
        }
        if (args[0] === 'pane' && args[1] === 'run') {
          const installed = f.record();
          assert.equal(installed.chatReplacement.phase, 'launchRequested');
          assert.equal(installed.chatReplacement.configDir, selected);
          assert.equal(installed.chats.at(-1).configDir, selected);
          assert.equal(installed.configDir, selected, 'Commit inheritance with the active replacement before native dispatch');
          assert.equal(f.herdr.tabs.some(tab => tab.tab_id === original.tabId), false);
          if (selected === null) assert.doesNotMatch(args[3], /CODEX_HOME=/);
          else assert.equal(parsedSelectedPath(args[3]), selected, '2907 replacement must use explicit Work5 CODEX_HOME');
        }
        return healthy(args);
      };
      const result = await open(f, { newSession: true }), after = f.record();
      assert.equal(result.exitCode, close === 'confirmed' ? 0 : 1, result.message);
      assert.equal(after.chatReplacement.configDir, selected);
      assert.equal(after.configDir, close === 'confirmed' ? selected : f.oldConfig);
      assert.equal(after.chatReplacement.phase, close === 'confirmed' ? 'launched' : 'closeRequested');
      assert.equal(calls(f, 'pane', 'run').length, close === 'confirmed' ? 1 : 0);
      assert.equal(calls(f, 'tab', 'create').length, close === 'confirmed' ? 1 : 0);
      assert.deepEqual(progress(after), progress(before));
    });
  }
});

for (const invalid of ['missing', 'regular-file']) test(`2907 ${invalid} selected folder refuses before intent or effects`, async t => {
  const f = await started(t), selected = join(f.source, 'invalid-work5');
  if (invalid === 'regular-file') writeFileSync(selected, 'synthetic file');
  // Accept an actual pending request so the byte-preservation assertion covers custody too.
  f.herdr.paneOf(f.record().chats.at(-1)).agent.agent_status = 'blocked';
  assert.equal((await changeRun({ ref: '17', text: 'Keep this pending request', cwd: f.source }, f.ports)).exitCode, 1);
  f.herdr.calls.length = 0;
  const before = bytes(f), pending = journal(f);
  f.ports.env.CODEX_HOME = relative(f.source, selected);
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 1);
  assert.equal(result.message, `CODEX_HOME is "${selected}", but that folder does not exist. Fix CODEX_HOME and run the command again.`);
  assert.ok(bytes(f).equals(before));
  assert.ok(journal(f).equals(pending));
  assert.equal(f.record().chatReplacement, undefined);
  assert.deepEqual(f.herdr.calls, []);
});

for (const saved of [null, 'old']) for (const incoming of [undefined, '', 'same']) test(`2907 ${incoming ?? 'unset'} preserves saved ${saved} profile`, async t => {
  const f = await started(t, { saved });
  if (incoming === undefined || incoming === 'same' && saved === null) delete f.ports.env.CODEX_HOME;
  else f.ports.env.CODEX_HOME = incoming === 'same' ? f.oldConfig : incoming;
  assert.equal((await open(f, { newSession: true })).exitCode, 0);
  assert.equal(f.record().configDir, f.oldConfig);
  assert.equal(f.record().chatReplacement.configDir, f.oldConfig);
  assert.equal(f.record().chats.at(-1).configDir, f.oldConfig);
});

test('2907 missing saved profile still refuses without a replacement override', async t => {
  const f = await started(t);
  rmSync(f.oldConfig, { recursive: true }); delete f.ports.env.CODEX_HOME;
  const before = bytes(f), result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 1);
  assert.match(result.message, /This run uses CODEX_HOME/);
  assert.ok(bytes(f).equals(before)); assert.deepEqual(f.herdr.calls, []);
});

test('2907 replacement preserves completed work, questions, approvals, archives and pending delivery', async t => {
  const f = await started(t);
  await advance(f);
  assert.equal((await stepDone({ step: 'change', summary: 'Keep the completed change.', cwd: f.record().root }, f.agentPorts())).exitCode, 0);
  // An earlier real replacement supplies history that the account move must append to.
  assert.equal((await open(f, { newSession: true })).exitCode, 0);
  assert.equal((await askPerson({ text: 'Keep this question for the person?', cwd: f.record().root }, f.agentPorts())).exitCode, 0);
  f.herdr.paneOf(f.record().chats.at(-1)).agent.agent_status = 'blocked';
  assert.equal((await changeRun({ ref: '17', text: 'Retain my original answer', cwd: f.source }, f.ports)).exitCode, 1);
  const before = f.record(), pending = journal(f), message = readFileSync(before.chats.at(-1).messageFile);
  assert.equal(JSON.parse(pending).requests[0].state, 'pending');
  f.ports.env.CODEX_HOME = f.work5; f.herdr.calls.length = 0;
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  const after = f.record();
  assert.deepEqual(progress(after), progress(before));
  assert.deepEqual(after.abandonedChats.slice(0, -1), before.abandonedChats);
  assert.equal(after.abandonedChats.length, before.abandonedChats.length + 1);
  assert.ok(readFileSync(after.abandonedChats.at(-1).messageFile).equals(message));
  assert.ok(journal(f).equals(pending));
  assert.equal(calls(f, 'agent', 'prompt').length, 0);
  assert.match(readFileSync(after.chats.at(-1).messageFile, 'utf8'), /Keep this question for the person/);
});

test('2907 replacing at an approval gate preserves the gate and pending change target', async t => {
  const f = await started(t);
  assert.equal((await stepDone({ step: 'scope', summary: 'Keep the open approval gate.', cwd: f.record().root }, f.agentPorts())).exitCode, 0);
  assert.ok(f.record().gate);
  f.herdr.paneOf(f.record().chats.at(-1)).agent.agent_status = 'blocked';
  assert.equal((await changeRun({ ref: '17', text: 'Keep my requested revision pending', cwd: f.source }, f.ports)).exitCode, 1);
  const before = f.record(), pending = journal(f);
  assert.equal(JSON.parse(pending).requests[0].kind, 'change');
  f.ports.env.CODEX_HOME = f.work5; f.herdr.calls.length = 0;
  assert.equal((await open(f, { newSession: true })).exitCode, 0);
  assert.deepEqual(progress(f.record()), progress(before));
  assert.ok(journal(f).equals(pending));
  assert.equal(f.record().configDir, f.work5);
  assert.equal(calls(f, 'agent', 'prompt').length, 0);
});

for (const mode of ['live', 'resume', 'historical']) test(`2907 ordinary ${mode} open retains recorded profile with incoming Work5`, async t => {
  const f = await started(t);
  if (mode === 'historical') await advance(f);
  const before = f.record(), selected = before.chats[0];
  if (mode === 'resume') {
    assert.equal((await open(f)).exitCode, 0); // Observe the original native session through the public boundary.
    f.herdr.paneOf(selected).agent = null;
  }
  f.ports.env.CODEX_HOME = f.work5; f.herdr.calls.length = 0;
  const result = await open(f, mode === 'historical' ? { area: 'plan' } : {});
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.record().configDir, f.oldConfig);
  assert.equal(f.record().chats[0].configDir, f.oldConfig);
  assert.equal(calls(f, 'tab', 'close').length, 0);
  if (mode === 'resume') {
    assert.equal(calls(f, 'pane', 'run').length, 1);
    assert.match(calls(f, 'pane', 'run')[0][3], /\bresume\b/);
    assert.ok(calls(f, 'pane', 'run')[0][3].includes(`CODEX_HOME=${quote(f.oldConfig)}`));
  } else assert.equal(calls(f, 'pane', 'run').length, 0);
});

for (const agent of ['claude', 'gemini', 'agy']) test(`2907 ${agent} replacement ignores incoming CODEX_HOME`, async t => {
  const f = await started(t, { agent });
  f.ports.env.CODEX_HOME = join(f.base, 'missing-irrelevant');
  assert.equal((await open(f, { newSession: true })).exitCode, 0);
  assert.equal(f.record().configDir, f.oldConfig);
  assert.equal(f.record().chats.at(-1).configDir, f.oldConfig);
  assert.doesNotMatch(calls(f, 'pane', 'run')[0][3], /CODEX_HOME=/);
});

for (const phase of ['intent', 'closed', 'prepared', 'launchRequested']) test(`2907 durable ${phase} retry cannot retarget Work5 to Work6`, async t => {
  const f = await started(t), original = f.record().chats.at(-1);
  f.ports.env.CODEX_HOME = f.work5;
  const result = await open(f, { newSession: true }, { ...f.ports, runFiles: checkpointFault(f, phase) });
  assert.equal(result.exitCode, 1);
  const pending = f.record().chatReplacement;
  assert.equal(pending.phase, phase);
  assert.equal(pending.configDir, f.work5);
  assert.equal(f.record().configDir, phase === 'launchRequested' ? f.work5 : f.oldConfig);
  assert.equal(calls(f, 'pane', 'run').length, 0);
  f.ports.env.CODEX_HOME = f.work6;
  if (phase === 'launchRequested') {
    // A lost checkpoint acknowledgement remains unconfirmed, without evidence to dispatch again.
    assert.equal((await open(f, { newSession: true })).exitCode, 1);
    assert.equal(f.record().chatReplacement.id, pending.id);
    assert.equal(f.record().chatReplacement.configDir, f.work5);
    assert.equal(f.record().configDir, f.work5);
    assert.equal(calls(f, 'pane', 'run').length, 0);
    return;
  }
  const recovered = await open(f, { newSession: true });
  assert.equal(recovered.exitCode, 0, recovered.message);
  const after = f.record();
  assert.equal(after.chatReplacement.id, pending.id);
  assert.equal(after.chatReplacement.configDir, f.work5);
  assert.equal(after.abandonedChats.length, 1);
  if (phase === 'intent') {
    assert.equal(after.chatReplacement.phase, 'rolledBack');
    assert.equal(after.configDir, f.oldConfig);
    assert.equal(after.chats.at(-1).paneId, original.paneId);
    assert.equal(calls(f, 'pane', 'run').length, 0);
  } else {
    assert.equal(after.configDir, f.work5);
    assert.equal(after.chats.at(-1).configDir, f.work5);
    assert.equal(calls(f, 'pane', 'run').length, 1);
    assert.ok(calls(f, 'pane', 'run')[0][3].includes(`CODEX_HOME=${quote(f.work5)}`));
  }
});

test('2907 rejected launch checkpoint keeps original inheritance and dispatches nothing', async t => {
  const f = await started(t); f.ports.env.CODEX_HOME = f.work5;
  const result = await open(f, { newSession: true }, { ...f.ports, runFiles: checkpointFault(f, 'launchRequested', { persisted: false }) });
  assert.equal(result.exitCode, 1);
  assert.equal(f.record().chatReplacement.phase, 'prepared');
  assert.equal(f.record().chatReplacement.configDir, f.work5);
  assert.equal(f.record().configDir, f.oldConfig);
  assert.equal(calls(f, 'pane', 'run').length, 0);
});

for (const retry of ['Work6', 'invalid', 'unset']) test(`2907 lost launch keeps Work5 on ${retry} retry and positive observation confirms once`, async t => {
  const f = await started(t), healthy = f.ports.herdr;
  f.ports.env.CODEX_HOME = f.work5;
  f.ports.herdr = async args => { const reply = await healthy(args); if (args[0] === 'pane' && args[1] === 'run') {
    assert.equal(f.record().configDir, f.work5, 'Inheritance must commit before native dispatch');
    assert.equal(f.record().chatReplacement.phase, 'launchRequested');
    throw lost();
  } return reply; };
  assert.equal((await open(f, { newSession: true })).exitCode, 1);
  const pending = f.record().chatReplacement;
  assert.equal(pending.replacement.startUnconfirmed, true);
  f.ports.herdr = healthy;
  if (retry === 'unset') delete f.ports.env.CODEX_HOME;
  else f.ports.env.CODEX_HOME = retry === 'Work6' ? f.work6 : join(f.base, 'absent');
  assert.equal((await open(f, { newSession: true })).exitCode, 0);
  const after = f.record();
  assert.equal(after.configDir, f.work5); assert.equal(after.chatReplacement.configDir, f.work5);
  assert.equal(after.chatReplacement.id, pending.id);
  assert.equal(after.chats.at(-1).paneId, pending.replacement.paneId);
  assert.equal(after.chats.at(-1).startUnconfirmed, undefined);
  assert.equal(calls(f, 'pane', 'run').length, 1);
});

test('2907 missing pinned folder retains pending custody rather than selecting retry Work6', async t => {
  const f = await started(t); f.ports.env.CODEX_HOME = f.work5;
  assert.equal((await open(f, { newSession: true }, { ...f.ports, runFiles: checkpointFault(f, 'closed') })).exitCode, 1);
  const pending = f.record().chatReplacement, before = bytes(f);
  rmSync(f.work5, { recursive: true }); f.ports.env.CODEX_HOME = f.work6; f.herdr.calls.length = 0;
  assert.equal((await open(f, { newSession: true })).exitCode, 1);
  assert.equal(f.record().chatReplacement.id, pending.id);
  assert.ok(bytes(f).equals(before));
  assert.deepEqual(effects(f), []);
});

test('2907 original rollback resume uses original profile while attempt remains pinned to Work5', async t => {
  const f = await started(t); f.ports.env.CODEX_HOME = f.work5;
  assert.equal((await open(f, { newSession: true }, { ...f.ports, runFiles: checkpointFault(f, 'intent') })).exitCode, 1);
  const pending = f.record().chatReplacement;
  f.herdr.paneOf(pending.original).agent = null;
  f.ports.env.CODEX_HOME = f.work6; f.herdr.calls.length = 0;
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  assert.equal(f.record().configDir, f.oldConfig);
  assert.equal(f.record().chatReplacement.configDir, f.work5);
  assert.equal(f.record().chatReplacement.phase, 'rolledBack');
  assert.equal(calls(f, 'pane', 'run').length, 1);
  assert.ok(calls(f, 'pane', 'run')[0][3].includes(`CODEX_HOME=${quote(f.oldConfig)}`));
  assert.match(calls(f, 'pane', 'run')[0][3], /\bresume\b/);
  assert.ok(calls(f, 'pane', 'run')[0][3].includes(pending.original.session.id));
});

test('2907 unconfirmed replacement session lookup uses Work5 despite retry Work6', async t => {
  const f = await started(t), healthy = f.ports.herdr;
  f.ports.env.CODEX_HOME = f.work5;
  f.ports.herdr = async args => { const reply = await healthy(args); if (args[0] === 'pane' && args[1] === 'run') throw lost(); return reply; };
  assert.equal((await open(f, { newSession: true })).exitCode, 1);
  const pending = f.record().chatReplacement;
  f.herdr.paneOf(pending.replacement).agent = null;
  f.tick(31_000); f.ports.env.CODEX_HOME = f.work6; f.ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'process-info') throw Object.assign(Error('unavailable process proof'), {code:'herdr_failed'});
    return healthy(args);
  };
  const lookups = [];
  f.ports.findNativeSessions = async (stage, options) => { lookups.push({ stage, options }); return []; };
  f.herdr.calls.length = 0;
  assert.equal((await open(f, { newSession: true })).exitCode, 1, 'Absence and unavailable process proof cannot authorize another dispatch');
  assert.equal(lookups.length, 1);
  assert.equal(lookups[0].options.codexHome, f.work5);
  assert.equal(f.record().chatReplacement.id, pending.id);
  assert.equal(f.record().configDir, f.work5);
  assert.deepEqual(effects(f), []);
});

for (const fallback of ['saved-run', 'saved-null', 'original']) test(`2907 legacy intent without replacement pins ${fallback} fallback`, async t => {
  const f = await started(t); f.ports.env.CODEX_HOME = f.work5;
  assert.equal((await open(f, { newSession: true }, { ...f.ports, runFiles: checkpointFault(f, 'intent') })).exitCode, 1);
  // Compatibility input only: no existing run or journal is edited.
  const run = structuredClone(f.record()), pending = structuredClone(run.chatReplacement);
  delete pending.configDir;
  if (fallback === 'saved-null') run.configDir = null;
  if (fallback === 'original') delete run.configDir;
  const expected = fallback === 'saved-null' ? null : f.oldConfig, records = [];
  f.ports.env.CODEX_HOME = f.work6; f.herdr.calls.length = 0;
  await restartChat({ run, chat: pending.original, message: 'Continue.', pending }, {
    ...f.ports, checkpoint: async record => records.push(structuredClone(record)),
  });
  assert.equal(records[0].configDir, expected);
  assert.ok(records.every(record => record.configDir === expected));
  assert.equal(records.at(-1).phase, 'rolledBack');
  assert.deepEqual(effects(f), []);
});

for (const saved of [null, 'old']) test(`2907 legacy prepared envelope pins replacement ${saved} before effects`, async t => {
  const f = await started(t, { saved });
  delete f.ports.env.CODEX_HOME;
  assert.equal((await open(f, { newSession: true }, { ...f.ports, runFiles: checkpointFault(f, 'prepared') })).exitCode, 1);
  // Explicit compatibility input, derived from the actual public checkpoint.
  const pending = structuredClone(f.record().chatReplacement); delete pending.configDir;
  const records = [], run = { ...f.record(), configDir: f.work6 };
  f.ports.env.CODEX_HOME = f.work6; f.herdr.calls.length = 0;
  const replacement = await restartChat({ run, chat: pending.original, message: 'Continue approved work.', pending }, {
    ...f.ports, checkpoint: async record => { records.push(structuredClone(record)); },
    herdr: async args => {
      if (args[0] === 'pane' && args[1] === 'run') assert.equal(records[0]?.configDir, f.oldConfig, 'Pin legacy selection before dispatch');
      return f.ports.herdr(args);
    },
  });
  assert.equal(replacement.configDir, f.oldConfig);
  assert.ok(records.every(record => record.configDir === f.oldConfig));
  const command = calls(f, 'pane', 'run')[0][3];
  if (saved === null) assert.doesNotMatch(command, /CODEX_HOME=/);
  else assert.ok(command.includes(`CODEX_HOME=${quote(f.oldConfig)}`));
});

for (const malformed of ['', 42, 'inconsistent']) test(`2907 malformed attempt configuration ${malformed} refuses before effects`, async t => {
  const f = await started(t); f.ports.env.CODEX_HOME = f.work5;
  assert.equal((await open(f, { newSession: true }, { ...f.ports, runFiles: checkpointFault(f, 'prepared') })).exitCode, 1);
  const run = f.record(), pending = structuredClone(run.chatReplacement);
  pending.configDir = malformed === 'inconsistent' ? f.work6 : malformed;
  f.herdr.calls.length = 0;
  await assert.rejects(() => restartChat({ run, chat: pending.original, message: 'Continue.', pending }, {
    ...f.ports, checkpoint: async () => assert.fail('Malformed configuration cannot checkpoint'),
  }), /configuration/);
  assert.deepEqual(effects(f), []);
});

for (const action of ['advance', 'cancel']) test(`2907 historical ${action} recovery cannot commit the abandoned account selection`, async t => {
  const f = await started(t); f.ports.env.CODEX_HOME = f.work5;
  assert.equal((await open(f, { newSession: true }, { ...f.ports, runFiles: checkpointFault(f, 'closed') })).exitCode, 1);
  f.ports.env.CODEX_HOME = f.work6;
  if (action === 'advance') await advance(f);
  else assert.equal((await cancelRun({ ref: '17', cwd: f.source }, f.ports)).exitCode, 0);
  const before = f.record(); f.herdr.calls.length = 0;
  const result = await open(f, { newSession: true });
  assert.equal(result.exitCode, 0, result.message);
  assert.deepEqual(progress(f.record()), progress(before));
  assert.equal(f.record().configDir, f.oldConfig);
  assert.deepEqual(effects(f), []);
});

for (const delay of ['before-launch-checkpoint', 'after-native-dispatch']) test(`2907 delayed ${delay} preserves newer progress and excludes a competing account commit`, async t => {
  const f = await started(t), healthy = f.ports.herdr;
  f.ports.env.CODEX_HOME = f.work5;
  let enter, release, paused = false;
  const reached = new Promise(resolve => { enter = resolve; });
  const gate = new Promise(resolve => { release = resolve; });
  const opening = open(f, { newSession: true }, { ...f.ports, herdr: async args => {
    const attempt = f.record().chatReplacement;
    const target = attempt?.replacement;
    const selected = !paused && (delay === 'before-launch-checkpoint'
      ? args[0] === 'agent' && args[1] === 'get' && args[2] === target?.paneId && attempt.phase === 'prepared'
      : args[0] === 'pane' && args[1] === 'run');
    if (selected) {
      paused = true;
      if (delay === 'after-native-dispatch') await healthy(args);
      enter(); await gate;
      if (delay === 'after-native-dispatch') return {};
    }
    if (args[0] === 'pane' && args[1] === 'process-info') return {
      result: { type: 'pane_process_info', process_info: { pane_id: args[3], shell_pid: 41,
        foreground_process_group_id: 41, foreground_processes: [{ pid: 41, name: 'bash' }] } },
    };
    return healthy(args);
  } });
  let newer;
  try {
    assert.equal(await Promise.race([reached.then(() => true), opening.then(() => false)]), true, 'Replacement must reach the delayed native boundary');
    assert.equal(f.record().configDir, delay === 'before-launch-checkpoint' ? f.oldConfig : f.work5);
    f.ports.env.CODEX_HOME = f.work6;
    // The runner's "Failed chat startup and recovery" contract keeps durable
    // approval/progress when next-area startup fails. This replacement still
    // owns the shared layout lock, so that next chat cannot allocate yet.
    const done = await stepDone({ step: 'scope', summary: 'Keep approved progress during delayed replacement.', cwd: f.record().root }, f.agentPorts());
    assert.equal(done.exitCode, 0, done.message);
    const approved = await approveRun({ ref: '17', cwd: f.source }, f.ports);
    assert.equal(approved.exitCode, 1, approved.message);
    assert.match(approved.message, /Approved the plan area .* The build chat startup was not confirmed \(herdr_layout_busy\)/, approved.message);
    newer = f.record();
    assert.equal(newer.area, 1, 'Approval must durably advance progress despite the startup refusal');
    assert.equal(newer.configDir, delay === 'before-launch-checkpoint' ? f.oldConfig : f.work5, 'The approval terminal cannot select Work6');
    assert.ok(newer.done.scope);
    assert.ok(newer.approvalRecord);
    assert.equal(newer.decisions.length, 1);
    assert.equal(newer.state, 'waiting');
    assert.equal(newer.chatFailure.area, 'build');
    assert.equal(newer.chatFailure.code, 'herdr_layout_busy');
    assert.equal(newer.chats.some(chat => chat.area === 'build'), false, 'Unavailable layout ownership cannot fabricate a next-area chat');
    const refused = await open(f, { newSession: true });
    assert.equal(refused.exitCode, 1);
    assert.match(refused.message, /Another open operation/);
    assert.deepEqual(f.record(), newer, 'The competing account route cannot commit while replacement holds the run lock');
  } finally { release(); }
  const completed = await opening;
  assert.equal(completed.exitCode, 0, completed.message);
  const after = f.record();
  assert.deepEqual(progress(after), progress(newer));
  assert.equal(after.configDir, newer.configDir);
  assert.deepEqual(after.chats.filter(chat => chat.area === 'build'), newer.chats.filter(chat => chat.area === 'build'));
  assert.deepEqual(after.chatFailure, newer.chatFailure, 'An old-area checkpoint cannot clear the newer startup failure');
  assert.equal(calls(f, 'pane', 'run').filter(args => parsedSelectedPath(args[3]) === f.work5).length, delay === 'after-native-dispatch' ? 1 : 0,
    'Only an already dispatched replacement can use Work5 while the next-area start is refused');
  const recovered = await open(f);
  assert.equal(recovered.exitCode, 0, recovered.message);
  assert.equal(f.record().chats.at(-1).area, 'build');
  assert.equal(f.record().chats.at(-1).configDir, newer.configDir, 'Explicit recovery inherits the profile preserved during the delayed old checkpoint');
  assert.equal(f.record().configDir, newer.configDir);
  assert.equal(f.record().chatFailure, undefined);
  // Once the old writer has finished, a separate supported current-area account
  // selection can commit Work6; no saved-state account edits manufacture the race.
  const selected = await open(f, { newSession: true });
  assert.equal(selected.exitCode, 0, selected.message);
  assert.equal(f.record().configDir, f.work6);
  assert.equal(f.record().chats.at(-1).configDir, f.work6);
});

for (const guard of ['agent-caller', 'self-pane', 'unknown-caller', 'foreign-workspace', 'terminal', 'startup']) test(`2907 Work5 selection preserves ${guard} refusal and saved custody`, async t => {
  const f = await started(t), original = f.record().chats.at(-1);
  f.ports.env.CODEX_HOME = f.work5;
  if (guard === 'agent-caller') f.ports.env.PDD_AGENT_SESSION = '1';
  if (guard === 'self-pane' || guard === 'unknown-caller') Object.assign(f.ports.env, {
    HERDR_ENV: '1', HERDR_SOCKET_PATH: join(f.base, 'sessions/pdd/herdr.sock'),
    ...(guard === 'self-pane' ? { HERDR_PANE_ID: original.paneId } : {}),
  });
  if (guard === 'foreign-workspace') f.herdr.workspaces.find(w => w.workspace_id === original.workspaceId).worktree.checkout_path = f.source;
  if (guard === 'terminal') f.herdr.paneOf(original).terminal_id = 'foreign-terminal';
  if (guard === 'startup') {
    // An actual failed public launch provides an unconfirmed startup control.
    const healthy = f.ports.herdr;
    await cancelRun({ ref: '17', cwd: f.source }, f.ports);
    f.ports.herdr = async args => { if (args[0] === 'pane' && args[1] === 'run') throw lost(); return healthy(args); };
    assert.equal((await f.run()).exitCode, 1);
    f.ports.herdr = healthy;
  }
  const before = bytes(f); f.herdr.calls.length = 0;
  assert.equal((await open(f, { newSession: true })).exitCode, 1);
  assert.ok(bytes(f).equals(before));
  assert.deepEqual(effects(f), []);
});
