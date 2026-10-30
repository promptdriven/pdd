// Native protocol cases from restart-workflow-area-session AC2, AC5–AC7 and its owning prompts.
// Real isolated Git/files; injected Herdr records commands and never starts native agents.
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawn } from 'node:child_process';
import { once } from 'node:events';
import * as chatModule from '../src/workflow-chat.mjs';
import { openRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const vectors = JSON.parse(readFileSync(new URL('./fixtures/workflow-open-replacement.json', import.meta.url), 'utf8'));
const inputs = kind => vectors.cases.filter(c => c.input.kind === kind).map(c => c.input);
const phases = ['intent', 'closeRequested', 'closeRequested', 'closed', 'createRequested', 'prepared', 'launchRequested', 'launched'];
const lost = () => Object.assign(Error('Synthetic reply lost'), { code: 'server_unavailable' });
const copy = value => JSON.parse(JSON.stringify(value));
const effect = args => args[0] === 'pane' && args[1] === 'run' || ['tab', 'workspace', 'worktree'].includes(args[0]) && ['create', 'close', 'open'].includes(args[1]);
const calls = (f, group, verb) => f.herdr.calls.filter(a => a[0] === group && a[1] === verb);
async function started(t) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  f.herdr.calls.length = 0;
  f.saved = f.record(); f.original = f.saved.chats.at(-1);
  return f;
}
async function protocolStarted(t) {
  assert.equal(typeof chatModule.restartChat, 'function', 'AC2 requires public module function restartChat');
  return started(t);
}
async function restart(f, ports = {}) {
  assert.equal(typeof chatModule.restartChat, 'function', 'AC2 requires public module function restartChat');
  return chatModule.restartChat({ run: f.saved, chat: f.original, message: 'Continue saved work. Do not repeat completed steps.' }, { ...f.ports, checkpoint: async () => {}, ...ports });
}
const open = f => openRun({ ref: '17', cwd: f.source, packageRoot, newSession: true }, f.ports);

for (const { variant: mismatch } of inputs('ownership')) {
  test(`2627 restart refuses ${mismatch} ownership before native effects`, async t => {
    const f = await protocolStarted(t), h = f.herdr, original = f.original;
    const workspace = h.workspaces.find(w => w.workspace_id === original.workspaceId);
    if (mismatch === 'checkout') workspace.worktree.checkout_path = f.source;
    if (mismatch === 'repository') workspace.worktree.repo_key = f.source;
    if (mismatch === 'tab-workspace') h.tabs.find(x => x.tab_id === original.tabId).workspace_id = 'different-workspace';
    if (mismatch === 'terminal') { original.terminalId = h.paneOf(original).terminal_id; h.paneOf(original).terminal_id = 'different-terminal'; }
    if (mismatch === 'extra-pane') h.panes.push({ ...h.paneOf(original), pane_id: 'extra-pane' });
    const healthy = f.ports.herdr;
    const herdr = async args => {
      if (mismatch === 'unavailable' && args[0] === 'workspace' && args[1] === 'list') throw lost();
      if (mismatch === 'malformed' && args[0] === 'pane' && args[1] === 'list') return { result: { panes: null } };
      return healthy(args);
    };
    let checkpointed = false;
    await assert.rejects(() => restart(f, { herdr, checkpoint: async () => { checkpointed = true; } }));
    assert.equal(checkpointed, false, 'Verify ownership before persisting intent');
    assert.deepEqual(h.calls.filter(effect), [], 'Unverified ownership cannot close/create/launch');
  });
}

test('2627 restart refuses its own pdd pane and an unknown Herdr caller pane', async t => {
  const f = await protocolStarted(t);
  for (const pane of [f.original.paneId, undefined]) {
    const env = { ...f.ports.env, HERDR_ENV: '1', HERDR_SOCKET_PATH: join(f.base, 'sessions/pdd/herdr.sock'), ...(pane ? { HERDR_PANE_ID: pane } : {}) };
    await assert.rejects(() => restart(f, { env }));
    assert.deepEqual(f.herdr.calls.filter(effect), []);
  }
});

test('2627 unconfirmed original requires a positively observed same agent', async t => {
  const f = await protocolStarted(t);
  f.original.startUnconfirmed = true;
  f.herdr.paneOf(f.original).agent = null;
  await assert.rejects(() => restart(f));
  assert.deepEqual(f.herdr.calls.filter(effect), []);
});

test('2627 acknowledged closure and fresh tab/pane absence precede create and launch', async t => {
  const f = await protocolStarted(t), healthy = f.ports.herdr, records = [], sequence = [];
  const bytes = readFileSync(f.original.messageFile);
  let closed = false;
  const herdr = async args => {
    sequence.push(args.slice(0, 2).join(':'));
    if (effect(args)) {
      const expected = args[0] === 'tab' && args[1] === 'close' ? 'closeRequested' : args[0] === 'tab' && args[1] === 'create' ? 'createRequested' : 'launchRequested';
      assert.equal(records.at(-1)?.phase, expected, 'Checkpoint must resolve before native effect');
    }
    const reply = await healthy(args);
    if (args[0] === 'tab' && args[1] === 'close') closed = true;
    if (args[0] === 'tab' && args[1] === 'create') {
      assert.equal(closed, true);
      const closeAt = sequence.indexOf('tab:close');
      assert.ok(sequence.slice(closeAt + 1, -1).includes('tab:list'), 'Fresh tab absence check before create');
      assert.ok(sequence.slice(closeAt + 1, -1).includes('pane:list'), 'Fresh pane absence check before create');
    }
    return reply;
  };
  const replacement = await restart(f, { herdr, checkpoint: async record => {
    records.push(copy(record));
    assert.ok(readFileSync(record.original.messageFile).equals(bytes));
    assert.equal(record.original.originalMessageFile, f.original.messageFile);
  } });
  assert.deepEqual(records.map(r => r.phase), phases);
  assert.equal(new Set(records.map(r => r.id)).size, 1);
  assert.equal(new Set(records.map(r => r.at)).size, 1);
  assert.match(records[0].id, /^[0-9a-f-]{36}$/i);
  for (const r of records) { assert.equal(r.area, f.original.area); assert.equal(r.original.paneId, f.original.paneId); }
  assert.equal(records[0].replacement, undefined);
  const prepared = records.find(r => r.phase === 'prepared').replacement;
  for (const key of ['tabId', 'paneId', 'workspaceId', 'terminalId', 'area', 'agent', 'configDir', 'startedAt', 'label', 'messageFile']) assert.ok(prepared[key] !== undefined, `Prepared identity includes ${key}`);
  assert.equal(records.find(r => r.phase === 'launchRequested').replacement.startUnconfirmed, true);
  assert.equal(Boolean(records.at(-1).replacement.startUnconfirmed), false);
  assert.equal(replacement.paneId, prepared.paneId);
  assert.equal(calls(f, 'pane', 'run').length, 1);
  assert.doesNotMatch(calls(f, 'pane', 'run')[0][3], /--resume|codex resume/);
  assert.ok(readFileSync(f.original.messageFile).equals(bytes), 'Prior message path stays byte-for-byte unchanged');
  assert.notEqual(replacement.messageFile, f.original.messageFile);
  assert.notEqual(replacement.messageFile, records[0].original.messageFile);
});

for (const { phase } of inputs('checkpoint-rejection')) {
  test(`2627 rejected ${phase} checkpoint prevents the next effect`, async t => {
    const f = await protocolStarted(t), records = [];
    await assert.rejects(() => restart(f, { checkpoint: async r => { records.push(copy(r)); if (r.phase === phase) throw Error('Synthetic persistence rejection'); } }));
    assert.equal(records.at(-1)?.phase, phase);
    const position = [...new Set(phases)].indexOf(phase);
    assert.equal(calls(f, 'tab', 'close').length, position < 2 ? 0 : 1);
    assert.equal(calls(f, 'tab', 'create').length, position < 4 ? 0 : 1);
    assert.equal(calls(f, 'pane', 'run').length, 0, 'Never launch after rejected checkpoint');
  });
}

for (const { variant: response } of inputs('close-response')) {
  test(`2627 ${response} close acknowledgement blocks replacement`, async t => {
    const f = await protocolStarted(t), healthy = f.ports.herdr;
    const herdr = async args => {
      if (args[0] === 'tab' && args[1] === 'close') {
        if (response === 'still-present') return { result: { type: 'ok' } };
        await healthy(args);
        if (response === 'lost') throw lost();
        return {};
      }
      return healthy(args);
    };
    await assert.rejects(() => restart(f, { herdr }));
    assert.equal(calls(f, 'tab', 'create').length, 0);
    assert.equal(calls(f, 'pane', 'run').length, 0);
  });
}

test('2627 lost pane launch reply retains the exact checkpointed unconfirmed identity', async t => {
  const f = await protocolStarted(t), healthy = f.ports.herdr, records = [];
  let caught;
  try { await restart(f, { checkpoint: async r => records.push(copy(r)), herdr: async args => { const reply = await healthy(args); if (args[0] === 'pane' && args[1] === 'run') throw lost(); return reply; } }); }
  catch (error) { caught = error; }
  assert.ok(caught);
  assert.equal(records.at(-1)?.phase, 'launchRequested');
  assert.deepEqual(caught.chat, records.at(-1).replacement);
  assert.equal(caught.chat.startUnconfirmed, true);
  assert.equal(calls(f, 'pane', 'run').length, 1);
});

for (const { variant: loss } of inputs('runner-lost-reply')) {
  test(`2627 runner reconciles same attempt after lost ${loss} reply`, async t => {
    const f = await started(t), healthy = f.ports.herdr;
    f.ports.herdr = async args => {
      const selected = args[0] === 'tab' && args[1] === loss;
      if (selected) assert.equal(f.record().chatReplacement?.phase, loss === 'close' ? 'closeRequested' : 'createRequested', 'Persist native request before dispatch');
      const reply = await healthy(args);
      if (selected) throw lost();
      return reply;
    };
    assert.notEqual((await open(f)).exitCode, 0, 'Lost acknowledgement cannot report replacement success');
    const pending = copy(f.record().chatReplacement);
    assert.equal(pending?.phase, loss === 'close' ? 'closeRequested' : 'createRequested');
    f.ports.herdr = healthy;
    f.ports.findNativeSessions = async () => [{id:pending.original.session.id}];
    const beforeCreates = calls(f,'tab','create').length;
    const recovered = await open(f);
    assert.equal(recovered.exitCode,0,recovered.message);
    assert.equal(f.record().chatReplacement.id,pending.id);
    assert.equal(f.record().chatReplacement.phase,'launched');
    assert.equal(f.record().abandonedChats.length,1);
    assert.equal(calls(f,'tab','create').length,beforeCreates+(loss==='close'?1:0));
    assert.equal(calls(f,'pane','run').length,1);

  });
}

test('2627 runner observes a lost launch on --new retry without replacing it again', async t => {
  const f = await started(t), healthy = f.ports.herdr;
  f.ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'run') {
      const saved = f.record();
      assert.equal(saved.chatReplacement?.phase, 'launchRequested');
      assert.equal(saved.chats.at(-1).paneId, args[2]);
      await healthy(args); throw lost();
    }
    return healthy(args);
  };
  assert.notEqual((await open(f)).exitCode, 0);
  const pending = f.record().chatReplacement;
  assert.equal(pending?.phase, 'launchRequested');
  assert.equal(pending.replacement.startUnconfirmed, true);
  f.ports.herdr = healthy;
  assert.equal((await open(f)).exitCode, 0);
  const after = f.record();
  assert.equal(after.chatReplacement.id, pending.id);
  assert.equal(after.chatReplacement.phase, 'launched');
  assert.equal(after.chats.at(-1).paneId, pending.replacement.paneId);
  assert.equal(Boolean(after.chats.at(-1).startUnconfirmed), false);
  assert.equal(after.abandonedChats.length, 1);
  assert.equal(calls(f, 'pane', 'run').length, 1);
});

test('2627 absent replacement pane cannot clear a lost launch or launch again', async t => {
  const f = await started(t), healthy = f.ports.herdr;
  f.ports.herdr = async args => { const reply = await healthy(args); if (args[0] === 'pane' && args[1] === 'run') throw lost(); return reply; };
  assert.notEqual((await open(f)).exitCode, 0);
  const pending = copy(f.record().chatReplacement);
  assert.equal(pending?.phase, 'launchRequested');
  const replacement = pending.replacement;
  f.herdr.panes = f.herdr.panes.filter(p => p.pane_id !== replacement.paneId);
  f.herdr.tabs = f.herdr.tabs.filter(tab => tab.tab_id !== replacement.tabId);
  f.ports.herdr = healthy;
  const before = f.herdr.calls.filter(effect).length;
  assert.notEqual((await open(f)).exitCode, 0);
  assert.equal(f.herdr.calls.filter(effect).length, before);
  assert.deepEqual(f.record().chatReplacement, pending);
  assert.equal(f.record().chats.at(-1).paneId, replacement.paneId);
  assert.equal(f.record().chats.at(-1).startUnconfirmed, true);
  assert.equal(calls(f, 'pane', 'run').length, 1);
});

test('2627 concurrent same-run requests cannot both replace a chat', async t => {
  const f = await started(t), healthy = f.ports.herdr;
  let release, entered;
  const gate = new Promise(resolve => { release = resolve; });
  const reached = new Promise(resolve => { entered = resolve; });
  f.ports.herdr = async args => { if (args[0] === 'tab' && args[1] === 'close') { entered(); await gate; } return healthy(args); };
  const first = open(f);
  // Finish the wait when old code completes without reaching close; this remains an assertion failure.
  const didReach = await Promise.race([reached.then(() => true), first.then(() => false)]);
  assert.equal(didReach, true, 'Replacement reaches owned-tab close');
  try {
    const second = await open(f);
    assert.notEqual(second.exitCode, 0, 'Competing same-run owner refuses');
    assert.equal(f.record().chatReplacement?.phase, 'closeRequested');
  } finally { release(); }
  assert.equal((await first).exitCode, 0);
  assert.equal(calls(f, 'pane', 'run').length, 1);
  assert.equal(f.record().abandonedChats.length, 1);
});

// A real process is stopped immediately before its first close. The on-disk request survives it.
test('2627 process interruption leaves durable intent and retry cannot dispatch a second attempt', async t => {
  const f = await started(t), childFile = join(f.base, 'interrupt.mjs');
  const modulePath = join(packageRoot, 'src/workflow-runner.mjs');
  writeFileSync(childFile, `import { openRun } from ${JSON.stringify(modulePath)};
import { execFile as cb } from 'node:child_process'; import { promisify } from 'node:util';
const execFile=promisify(cb); const h=${JSON.stringify({ workspaces: f.herdr.workspaces, tabs: f.herdr.tabs, panes: f.herdr.panes })};
const herdr=async args=>{const [g,v]=args; const flag=n=>args[args.indexOf(n)+1];
if(g==='status')return {running:true,session:'pdd',compatible:true};
if(g==='workspace'&&v==='list')return {result:{type:'workspace_list',workspaces:h.workspaces}};
if(g==='tab'&&v==='list')return {result:{type:'tab_list',tabs:h.tabs.filter(t=>t.workspace_id===flag('--workspace'))}};
if(g==='pane'&&v==='list')return {result:{type:'pane_list',panes:h.panes.filter(p=>p.workspace_id===flag('--workspace'))}};
if(g==='tab'&&v==='get')return {result:{tab:h.tabs.find(t=>t.tab_id===args[2])}};
if(g==='agent'&&v==='get'){const p=h.panes.find(p=>p.pane_id===args[2]);return {result:{agent:{...p.agent,pane_id:p.pane_id}}};}
if(g==='tab'&&v==='close'){process.send({closing:true}); await new Promise(()=>{});}
if(g==='tab'&&v==='focus')return {result:{type:'ok'}};
throw Error('Unexpected synthetic Herdr call '+args.join(' '));};
const result=await openRun(${JSON.stringify({ ref: '17', cwd: f.source, packageRoot, newSession: true })}, {execFile,herdr,stateDir:${JSON.stringify(f.state)},layoutDirectory:${JSON.stringify(f.ports.layoutDirectory)},env:${JSON.stringify(f.ports.env)},isTTY:true});
process.send({result}); process.disconnect();`);
  const child = spawn(process.execPath, [childFile], { stdio: ['ignore', 'pipe', 'pipe', 'ipc'] });
  t.after(() => { if (child.exitCode === null) child.kill('SIGKILL'); });
  const message = await Promise.race([once(child, 'message').then(([m]) => m), once(child, 'exit').then(([code]) => ({ exited: code }))]);
  assert.equal(message.closing, true, 'Child reached a real pre-close interruption boundary');
  const pending = f.record().chatReplacement;
  assert.equal(pending?.phase, 'closeRequested');
  const exited = once(child, 'exit'); child.kill('SIGKILL'); await exited;
  assert.equal((await open(f)).exitCode, 0);
  assert.equal(f.record().chatReplacement.id, pending.id);
  assert.equal(f.record().chatReplacement.phase, 'rolledBack');
  assert.equal(f.herdr.calls.filter(effect).length, 0, 'Dead process recovery does not dispatch a fresh replacement');
  assert.equal(f.record().abandonedChats.length, 1);
});

for (const lostResume of [false, true]) {
  test(`2627 interrupted intent resumes the exact stopped original once${lostResume ? ' despite a lost reply' : ''}`, async t => {
    const f = await protocolStarted(t);
    await assert.rejects(() => restart(f, { checkpoint: async record => {
      const saved = f.record();
      saved.chatReplacement = copy(record);
      saved.abandonedChats = [{ ...record.original, replacementId: record.id, abandonedAt: record.at, reason: 'explicit-new-session' }];
      writeFileSync(join(saved.runDir, 'status.json'), JSON.stringify(saved));
      throw Error('Interrupted after durable intent');
    } }), /Interrupted after durable intent/);
    const pending = f.record().chatReplacement;
    const archivedBytes = readFileSync(pending.original.messageFile);
    f.herdr.paneOf(f.original).agent = null;
    const healthy = f.ports.herdr;
    f.ports.herdr = async args => {
      if (args[0] === 'pane' && args[1] === 'run') {
        assert.equal(f.record().chatReplacement.recovery?.resumeRequested, true, 'Persist the resume guard before dispatch');
        if (lostResume) { f.herdr.calls.push(args); throw lost(); }
      }
      return healthy(args);
    };
    const result = await open(f);
    if (lostResume) {
      assert.notEqual(result.exitCode, 0);
      assert.equal(f.record().chatReplacement.recovery?.resumeRequested, true);
      assert.notEqual((await open(f)).exitCode, 0);
      assert.notEqual((await open(f)).exitCode, 0);
      assert.equal(f.record().chatReplacement.phase, 'intent');
    } else {
      assert.equal(result.exitCode, 0, result.message);
      assert.equal(f.record().chatReplacement.phase, 'rolledBack');
      assert.equal(f.record().chats.at(-1).paneId, f.original.paneId);
      assert.equal(f.record().chats.at(-1).messageFile, f.original.messageFile);
    }
    const after = f.record();
    assert.equal(after.chatReplacement.id, pending.id);
    assert.equal(after.chatReplacement.at, pending.at);
    assert.deepEqual(after.chatReplacement.original, pending.original);
    assert.equal(after.abandonedChats.length, 1);
    assert.ok(readFileSync(pending.original.messageFile).equals(archivedBytes));
    const resumes = calls(f, 'pane', 'run');
    assert.equal(resumes.length, 1);
    assert.equal(resumes[0][2], pending.original.paneId);
    assert.equal(resumes[0][3].match(/--resume '([0-9a-f-]{36})'/)?.[1], pending.original.session.id);
    assert.equal(calls(f, 'tab', 'close').length, 0);
    assert.equal(calls(f, 'tab', 'create').length, 0);
  });
}
