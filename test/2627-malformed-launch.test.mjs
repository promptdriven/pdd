// AC7: unknown native replies retain custody; only acknowledgement or same-agent observation confirms.
import test from 'node:test';
import assert from 'node:assert/strict';
import * as chatModule from '../src/workflow-chat.mjs';
import { openRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/2627-runner-fixture.mjs';

const copy = value => JSON.parse(JSON.stringify(value));
const isLaunch = args => args[0] === 'pane' && args[1] === 'run';
const effects = f => f.herdr.calls.filter(args => isLaunch(args) || ['tab', 'workspace', 'worktree'].includes(args[0]) && ['create', 'close', 'open'].includes(args[1]));
const open = f => openRun({ ref: '17', cwd: f.source, packageRoot, newSession: true }, f.ports);
async function started(t) {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  f.herdr.calls.length = 0;
  return f;
}

for (const [name, reply] of [['null', null], ['primitive', true], ['array', []], ['unknown object', { unexpected: true }]]) {
  test(`2627 ${name} launch reply retains exact unconfirmed checkpoint`, async t => {
    assert.equal(typeof chatModule.restartChat, 'function', 'Fresh replacement requires the public restartChat boundary');
    const f = await started(t), run = f.record(), healthy = f.ports.herdr, records = [];
    let dispatches = 0;
    await assert.rejects(() => chatModule.restartChat({ run, chat: run.chats.at(-1), message: 'Continue saved work.' }, {
      ...f.ports,
      checkpoint: async record => records.push(copy(record)),
      herdr: async args => { if (isLaunch(args)) { dispatches++; return reply; } return healthy(args); },
    }), error => {
      assert.equal(records.at(-1)?.phase, 'launchRequested');
      assert.deepEqual(error.chat, records.at(-1).replacement);
      assert.equal(error.chat.startUnconfirmed, true);
      return true;
    });
    assert.equal(dispatches, 1);
    assert.equal(records.some(record => record.phase === 'launched'), false);
  });
}

test('2627 documented empty launch acknowledgement confirms the prepared replacement', async t => {
  assert.equal(typeof chatModule.restartChat, 'function', 'Fresh replacement requires the public restartChat boundary');
  const f = await started(t), run = f.record(), records = [];
  const replacement = await chatModule.restartChat({ run, chat: run.chats.at(-1), message: 'Continue saved work.' }, {
    ...f.ports, checkpoint: async record => records.push(copy(record)),
  });
  assert.equal(records.at(-1).phase, 'launched');
  assert.equal(Boolean(replacement.startUnconfirmed), false);
  const requested = { ...records.find(record => record.phase === 'launchRequested').replacement };
  delete requested.startUnconfirmed;
  assert.deepEqual(replacement, requested);
  assert.equal(f.herdr.calls.filter(isLaunch).length, 1);
});

test('2627 malformed launch reply blocks retry and same-identity observation recovers even with --new', async t => {
  const f = await started(t), healthy = f.ports.herdr;
  let dispatches = 0;
  f.ports.herdr = async args => {
    if (isLaunch(args)) { dispatches++; return null; }
    return healthy(args);
  };
  assert.notEqual((await open(f)).exitCode, 0, 'A malformed launch reply must refuse success');
  const pending = copy(f.record().chatReplacement), installed = copy(f.record().chats.at(-1));
  assert.equal(pending.phase, 'launchRequested');
  assert.deepEqual(installed, pending.replacement);
  assert.equal(installed.startUnconfirmed, true);
  assert.equal(f.record().abandonedChats.length, 1);
  const priorEffects = effects(f).length;
  assert.notEqual((await open(f)).exitCode, 0, 'No observed agent leaves launch uncertainty unresolved');
  assert.deepEqual(f.record().chatReplacement, pending);
  assert.deepEqual(f.record().chats.at(-1), installed);
  assert.equal(f.record().abandonedChats.length, 1);
  assert.equal(dispatches, 1);
  assert.equal(effects(f).length, priorEffects);
  // Supply only an observation; never call pane run to simulate recovery.
  f.herdr.paneOf(installed).agent = { agent: installed.agent, agent_status: 'working',
    agent_session: { agent: installed.agent, kind: 'id', value: installed.session.id } };
  assert.equal((await open(f)).exitCode, 0);
  const after = f.record(), confirmed = { ...installed };
  delete confirmed.startUnconfirmed;
  assert.equal(after.chatReplacement.id, pending.id);
  assert.equal(after.chatReplacement.phase, 'launched');
  assert.deepEqual(after.chats.at(-1), confirmed);
  assert.deepEqual(after.chatReplacement.replacement, confirmed);
  assert.deepEqual(after.chatReplacement.original, pending.original);
  assert.equal(after.abandonedChats.length, 1);
  assert.equal(dispatches, 1);
  assert.equal(effects(f).length, priorEffects);
});
