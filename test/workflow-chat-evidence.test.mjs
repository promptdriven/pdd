// "Ended" needs evidence that the agent ran; elapsed time and an unreadable lookup are never evidence.
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import * as runner from '../src/workflow-runner.mjs';
import { fixture, packageRoot } from './helpers/workflow-runner-fixture.mjs';

const open = runner.openRunCommand ?? runner.openRun;
const launches = f => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run');
const stateLine = message => message.split('\n').find(line => line.startsWith('State:')) ?? '';
const CODEX_SESSION = '33333333-3333-4333-8333-333333333333';
async function started(t, agent) {
  const f = await fixture(t, { agent });
  if (agent === 'codex') { const dir = join(f.base, 'codexhome'); mkdirSync(dir); f.ports.env.CODEX_HOME = dir; }
  const herdr = f.ports.herdr;
  // Keep this test's acknowledged initial launch genuinely unobserved, including startup's own inspection.
  f.ports.herdr = async args => {
    const result = await herdr(args);
    if (args[0] === 'pane' && args[1] === 'run') f.herdr.panes.find(pane => pane.pane_id === args[2]).agent = null;
    return result;
  };
  assert.equal((await f.run()).exitCode, 0);
  f.ports.herdr = herdr;
  const chat = f.record().chats.at(-1);
  assert.ok(chat, 'The started chat is saved');
  // The launch was acknowledged, but Herdr never shows an agent in the pane.
  f.herdr.paneOf(chat).agent = null;
  return { f, chat };
}

for (const agent of ['claude', 'codex']) {
  test(`${agent}: an acknowledged launch that was never seen stays starting after the grace when no session of it exists`, async t => {
    const { f, chat } = await started(t, agent);
    f.ports.findNativeSessions = async () => [];
    f.tick(31_000);
    const status = await runner.runStatus({ ref: '17', cwd: f.source }, f.ports);
    assert.doesNotMatch(stateLine(status.message), /stopped|ended/);
    assert.equal(f.record().chats.at(-1).state, 'starting');
    assert.equal(f.record().chats.at(-1).evidence, undefined, 'Elapsed time is not end evidence');
    const before = launches(f).length;
    const result = await open({ ref: '17', cwd: f.source, packageRoot }, f.ports);
    assert.match(result.message, /starting, not confirmed/);
    assert.doesNotMatch(result.message, /ended|yourself/);
    assert.equal(launches(f).length, before, 'No launch or resume without evidence');
    assert.equal(f.record().chats.at(-1).state, 'starting');
    assert.equal(f.record().chats.at(-1).paneId, chat.paneId);
  });

  test(`${agent}: the chat's own native session plus an empty pane is end evidence, and open resumes that session`, async t => {
    const { f, chat } = await started(t, agent);
    const id = agent === 'claude' ? chat.session.id : CODEX_SESSION, lookups = [];
    f.ports.findNativeSessions = async (stage, ports) => { lookups.push([stage, ports]); return [{ id, startedAt: chat.startedAt + 1000 }]; };
    f.tick(31_000);
    const status = await runner.runStatus({ ref: '17', cwd: f.source }, f.ports);
    assert.match(stateLine(status.message), /the chat stopped/);
    const saved = f.record().chats.at(-1);
    assert.equal(saved.state, 'ended');
    assert.equal(saved.evidence.kind, 'pane-exit');
    assert.equal(saved.evidence.sessionId, id);
    assert.equal(saved.evidence.paneId, chat.paneId);
    const [stage, ports] = lookups[0];
    assert.equal(stage.agent, agent);
    assert.equal(stage.root, f.record().root);
    assert.equal(stage.startedAt, chat.startedAt);
    if (agent === 'claude') { assert.equal(stage.sessionId, chat.session.id); assert.equal(ports.claudeConfigDir, f.record().configDir); }
    else assert.equal(ports.codexHome, f.record().configDir);
    const before = launches(f).length;
    const result = await open({ ref: '17', cwd: f.source, packageRoot }, { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' } });
    assert.equal(result.exitCode, 0, result.message);
    const sent = launches(f).slice(before);
    assert.equal(sent.length, 1);
    assert.ok(sent[0][3].includes(id), 'Resume the exact session of this chat');
    assert.match(sent[0][3], agent === 'claude' ? /--resume/ : / resume /);
  });
}

for (const agent of ['claude', 'codex']) test(`${agent}: a resumed chat whose agent exits again is ended after the grace and resumed again, never stuck starting`, async t => {
  const { f, chat } = await started(t, agent);
  const id = agent === 'claude' ? chat.session.id : CODEX_SESSION;
  f.ports.findNativeSessions = async stage => stage.startedAt <= chat.startedAt ? [{ id, startedAt: chat.startedAt }] : [];
  f.tick(31_000);
  const inside = { ...f.ports, env: { ...f.ports.env, HERDR_ENV: '1' } };
  assert.equal((await open({ ref: '17', cwd: f.source, packageRoot }, inside)).exitCode, 0);
  // The resumed agent exits at once; its session started before the resume, so a window lookup cannot find it.
  f.herdr.paneOf(chat).agent = null;
  f.tick(31_000);
  const status = await runner.runStatus({ ref: '17', cwd: f.source }, f.ports);
  assert.match(stateLine(status.message), /the chat stopped/);
  assert.equal(f.record().chats.at(-1).state, 'ended');
  const before = launches(f).length;
  const again = await open({ ref: '17', cwd: f.source, packageRoot }, inside);
  assert.equal(again.exitCode, 0, again.message);
  assert.equal(launches(f).length, before + 1);
  assert.ok(launches(f).at(-1)[3].includes(id), 'Resume the same session again');
});

for (const malformed of [false, true]) test(`R4 with the real session lookup: ${malformed ? 'an unreadable' : 'a readable'} session file of this attempt ${malformed ? 'keeps the attempt pending' : 'is resumed'}`, async t => {
  const f = await fixture(t); await f.run();
  const healthy = f.herdr.herdr;
  f.ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'run') { await healthy(args); throw Object.assign(Error('lost reply'), { code: 'server_unavailable' }); }
    return healthy(args);
  };
  await open({ ref: '17', cwd: f.source, packageRoot, newSession: true }, f.ports);
  const pending = f.record().chatReplacement;
  assert.ok(pending?.replacement, 'A lost fresh launch retains replacement custody');
  const id = pending.replacement.session.id, root = f.record().root;
  f.herdr.paneOf(pending.replacement).agent = null;
  const dir = join(f.ports.env.CLAUDE_CONFIG_DIR, 'projects', root.replace(/[^a-zA-Z0-9]/g, '-'));
  mkdirSync(dir, { recursive: true });
  const row = { type: 'user', sessionId: id, cwd: root, timestamp: new Date(f.clock + 2000).toISOString(), message: { role: 'user', content: 'hi' } };
  writeFileSync(join(dir, `${id}.jsonl`), `${JSON.stringify(row)}\n${malformed ? '{"type":"assistant", BROKEN\n' : ''}${JSON.stringify({ ...row, type: 'assistant' })}\n`);
  f.ports.herdr = async args => args[0] === 'pane' && args[1] === 'process-info'
    ? { result: { type: 'pane_process_info', process_info: { pane_id: args[3], shell_pid: 41, foreground_process_group_id: 41, foreground_processes: [{ pid: 41, name: 'zsh' }] } } }
    : healthy(args);
  delete f.ports.findNativeSessions;
  f.tick(31_000);
  const before = launches(f).length;
  await open({ ref: '17', cwd: f.source, packageRoot, newSession: true }, f.ports);
  const sent = launches(f).slice(before);
  assert.equal(sent.filter(a => !/--resume/.test(a[3])).length, 0, 'Never a second fresh first message');
  if (malformed) {
    assert.equal(sent.length, 0, 'An unreadable lookup sends nothing');
    assert.equal(f.record().chatReplacement.id, pending.id);
    assert.equal(f.record().chatReplacement.phase, 'launchRequested');
  } else {
    assert.equal(sent.length, 1);
    assert.ok(sent[0][3].includes(id), 'Resume this attempt\'s session');
  }
});
