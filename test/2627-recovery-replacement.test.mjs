// Public default recovery followed by explicit fresh-session replacement.
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { openRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/2627-runner-fixture.mjs';
const open = (f, input = {}) => openRun({ ref: '17', cwd: f.source, packageRoot, ...input }, f.ports);
const launches = f => f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');
test('2627 ordinary missing-tab recovery saves terminal custody for a later replacement', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const original = f.record().chats.at(-1), message = readFileSync(original.messageFile);
  f.herdr.tabs = f.herdr.tabs.filter(tab => tab.tab_id !== original.tabId);
  f.herdr.panes = f.herdr.panes.filter(pane => pane.pane_id !== original.paneId);
  // The shared fake parses unquoted launch IDs; native resume IDs are shell-quoted.
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    const reply = await herdr(args);
    const resumedId = args[0] === 'pane' && args[1] === 'run' && args[3].match(/--resume '([0-9a-f-]{36})'/)?.[1];
    if (resumedId) f.herdr.panes.find(pane => pane.pane_id === args[2]).agent.agent_session.value = resumedId;
    return reply;
  };
  f.herdr.calls.length = 0;
  const opened = await open(f);
  assert.equal(opened.exitCode, 0, opened.message);
  const recovered = f.record().chats.at(-1), pane = f.herdr.paneOf(recovered);
  assert.notEqual(recovered.tabId, original.tabId);
  assert.notEqual(recovered.paneId, original.paneId);
  assert.equal(recovered.terminalId, pane.terminal_id, 'Recovered chat must durably adopt its recreated terminal identity');
  assert.equal(recovered.session.id, original.session.id);
  assert.equal(launches(f).length, 1);
  assert.match(launches(f)[0][3], /--resume/);
  f.herdr.calls.length = 0;
  const replaced = await open(f, { newSession: true });
  assert.equal(replaced.exitCode, 0, replaced.message);
  const after = f.record(), replacement = after.chats.at(-1), archived = after.abandonedChats.at(-1);
  assert.notEqual(replacement.paneId, recovered.paneId);
  assert.equal(archived.tabId, recovered.tabId);
  assert.equal(archived.paneId, recovered.paneId);
  assert.equal(archived.terminalId, recovered.terminalId);
  assert.equal(archived.session.id, recovered.session.id);
  assert.ok(readFileSync(archived.messageFile).equals(message));
  assert.equal(launches(f).length, 1, 'Replacement dispatches exactly one fresh launch');
  assert.doesNotMatch(launches(f)[0][3], /--resume/);
  assert.deepEqual(f.herdr.calls.filter(args => args[0] === 'tab' && args[1] === 'close').map(args => args[2]), [recovered.tabId]);
});
