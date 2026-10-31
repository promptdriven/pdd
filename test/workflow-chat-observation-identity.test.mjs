import test from 'node:test';
import assert from 'node:assert/strict';
import * as chatModule from '../src/workflow-chat.mjs';
import { openRun } from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';
const copy = value => JSON.parse(JSON.stringify(value));
const open = f => openRun({ ref: '17', cwd: f.source, packageRoot, newSession: true }, f.ports);
const effects = f => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run' || a[0] === 'tab' && ['create', 'close'].includes(a[1]));
const malformed = [
  ['invalid status', null],
  ['missing status', null],
  ['invalid UUID', { kind: 'id', value: 'not-a-uuid' }],
  ['missing ID', { kind: 'id' }],
  ['unknown descriptor', { kind: 'unexpected', value: 'ignored' }],
  ['primitive descriptor', false],
  ['contradictory UUID', { kind: 'id', value: '00000000-0000-4000-8000-000000000099' }],
];
for (const [name, metadata] of malformed) {
  test(`2627 pending replacement rejects ${name} without releasing launch custody`, async t => {
    assert.equal(typeof chatModule.restartChat, 'function');
    const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
    const healthy = f.ports.herdr;
    f.ports.herdr = args => args[0] === 'pane' && args[1] === 'run' ? Promise.reject(Object.assign(Error('lost'),{code:'server_unavailable'})) : healthy(args);
    assert.notEqual((await open(f)).exitCode, 0);
    const before = copy(f.record());
    assert.equal(before.chatReplacement.phase, 'launchRequested');
    const installed = before.chats.at(-1);
    f.herdr.paneOf(installed).agent = { agent: installed.agent, agent_status: name === 'invalid status' ? 'invented' : name === 'missing status' ? undefined : 'working', agent_session: metadata };
    const count = effects(f).length;
    for (let retry = 0; retry < 2; retry++) {
      assert.notEqual((await open(f)).exitCode, 0, 'Malformed observation must retain launch uncertainty');
      assert.deepEqual(f.record(), before, 'Retries retain the exact chat, error and pending replacement');
      assert.equal(effects(f).length, count, 'Retries never close, archive or dispatch again');
    }
  });
  test(`2627 original replacement inspection rejects ${name} before any checkpoint`, async t => {
    assert.equal(typeof chatModule.restartChat, 'function');
    const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
    const run = f.record(), chat = run.chats.at(-1); chat.startUnconfirmed = true;
    f.herdr.paneOf(chat).agent.agent_session = metadata;
    if (name.endsWith('status')) f.herdr.paneOf(chat).agent.agent_status = name === 'invalid status' ? 'invented' : undefined;
    const count = effects(f).length, checkpoints = [];
    await assert.rejects(() => chatModule.restartChat({ run, chat, message: 'Continue.' }, { ...f.ports, checkpoint: async record => checkpoints.push(record) }));
    assert.deepEqual(checkpoints, []);
    assert.equal(effects(f).length, count);
  });
}
for (const [name, metadata] of [['missing', undefined], ['null', null]]) {
  test(`2627 ${name} optional native metadata confirms same pending Claude identity`, async t => {
    assert.equal(typeof chatModule.restartChat, 'function');
    const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
    const healthy = f.ports.herdr;
    f.ports.herdr = args => args[0] === 'pane' && args[1] === 'run' ? Promise.reject(Object.assign(Error('lost'),{code:'server_unavailable'})) : healthy(args);
    assert.notEqual((await open(f)).exitCode, 0);
    const before = copy(f.record()), chat = before.chats.at(-1), count = effects(f).length;
    f.herdr.paneOf(chat).agent = { agent: chat.agent, agent_status: 'unknown', ...(metadata === undefined ? {} : { agent_session: metadata }) };
    assert.equal((await open(f)).exitCode, 0);
    const after = f.record(), expected = { ...chat }; delete expected.startUnconfirmed;
    assert.deepEqual(after.chats.at(-1), expected);
    assert.equal(after.chatReplacement.phase, 'launched');
    assert.equal(after.chatReplacement.id, before.chatReplacement.id);
    assert.deepEqual(after.abandonedChats, before.abandonedChats);
    assert.equal(effects(f).length, count);
  });
}
for (const [name, metadata] of [['missing', undefined], ['null', null]]) {
  test(`2627 original ${name} optional native metadata preserves archived Claude UUID`, async t => {
    assert.equal(typeof chatModule.restartChat, 'function');
    const f = await fixture(t); assert.equal((await f.run()).exitCode, 0);
    const before = f.record(), chat = before.chats.at(-1);
    if (metadata === undefined) delete f.herdr.paneOf(chat).agent.agent_session;
    else f.herdr.paneOf(chat).agent.agent_session = metadata;
    f.herdr.paneOf(chat).agent.agent_status = 'unknown';
    assert.equal((await open(f)).exitCode, 0);
    const after = f.record();
    assert.deepEqual(after.abandonedChats.at(-1).session, chat.session);
    assert.notEqual(after.chats.at(-1).session.id, chat.session.id);
  });
}
