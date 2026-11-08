// Synthetic default/caller accounts; production native reader and runner, fake Herdr.
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync, mkdirSync, readFileSync, rmSync, statSync, utimesSync, writeFileSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {openRun, runStatus} from '../src/workflow-runner.mjs';
import {chatSession, ownSession} from '../src/workflow-chat.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const metadata = (id, cwd, at) => JSON.stringify({type:'session_meta', payload:{id, cwd, timestamp:new Date(at).toISOString()}}) + '\n';

async function defaultAccount(t, {delayed = false} = {}) {
  const f = await fixture(t, {agent:'codex'});
  assert.equal(Object.hasOwn(f.ports.env, 'CODEX_HOME'), false);
  const account = join(f.ports.env.HOME, '.codex'), caller = join(f.base, 'caller-account');
  for (const folder of [account, caller]) mkdirSync(join(folder, 'sessions'), {recursive:true});
  delete f.ports.findNativeSessions;
  const native = f.ports.herdr;
  const file = join(account, 'sessions', 'rollout-synthetic.jsonl');
  let started;
  f.ports.herdr = async args => {
    const reply = await native(args);
    if (args[0] === 'pane' && args[1] === 'run' && !started) {
      const pane = f.herdr.panes.find(row => row.pane_id === args[2]);
      started = metadata(pane.agent.agent_session.value, pane.cwd, f.clock);
      if (!delayed) {
        writeFileSync(file, started);
        utimesSync(file, f.clock / 1000, f.clock / 1000);
      }
    }
    return reply;
  };
  assert.equal((await f.run()).exitCode, 0);
  const original = f.record().chats.at(-1);
  assert.equal(original.configDir, null);
  assert.equal(original.launchProfile.configDir, null);
  return {f, native, file, caller, original, started};
}

for (const recovery of ['delayed binding', 'ended agent', 'closed workspace']) test(`2820 default account keeps its name through ${recovery} with another caller account`, async t => {
  const {f, native, file, caller, original, started} = await defaultAccount(t, {delayed:recovery === 'delayed binding'});
  if (recovery === 'delayed binding') {
    assert.equal(original.namingError?.code, 'chat_name_unverified');
    writeFileSync(file, started);
    utimesSync(file, f.clock / 1000, f.clock / 1000);
  } else {
    assert.equal((await runStatus({ref:'17', cwd:f.source, json:true}, f.ports)).exitCode, 0);
    assert.equal(f.record().chats.at(-1).namingError, undefined);
  }
  const saved = f.record().chats.at(-1), bytes = readFileSync(file), mtime = statSync(file).mtimeMs;
  const id = JSON.parse(started).payload.id;
  if (recovery !== 'delayed binding') assert.equal(saved.session?.id, id);
  f.tick(60_000);
  f.ports.env.CODEX_HOME = caller;
  if (recovery === 'closed workspace') await native(['workspace','close',saved.workspaceId]);
  if (recovery === 'ended agent') f.herdr.paneOf(saved).agent = null;
  f.herdr.calls.length = 0;
  const result = recovery === 'delayed binding'
    ? await runStatus({ref:'17', cwd:f.source, json:true}, f.ports)
    : await openRun({ref:'17', cwd:f.source, packageRoot}, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  const current = f.record().chats.at(-1);
  assert.equal(current.namingError, undefined, 'The saved default account must supply native naming evidence');
  assert.equal(current.configDir, null);
  assert.equal(current.launchProfile.configDir, null);
  assert.equal(f.record().launchProfile.configDir, null);
  assert.equal(current.session.id, id);
  assert.equal(current.herdrAgentName, saved.herdrAgentName);
  assert.equal((await native(['agent','get',saved.herdrAgentName])).result.agent.pane_id, current.paneId);
  const launches = f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');
  assert.equal(launches.length, recovery === 'delayed binding' ? 0 : 1);
  if (launches.length) {
    assert.ok(current.resumedAt > saved.startedAt);
    assert.match(launches[0][3], /\bresume\b/);
    assert.ok(launches[0][3].includes(saved.session.id));
    assert.match(launches[0][3], /\s-u CODEX_HOME\b/);
    assert.equal(launches[0][3].includes(caller), false);
    assert.equal(recovery === 'closed workspace' ? current.workspaceId !== saved.workspaceId : current.paneId === saved.paneId, true);
  }
  assert.deepEqual(readFileSync(file), bytes);
  assert.equal(statSync(file).mtimeMs, mtime);
});

test('2820 default account refuses matching naming evidence from the caller account', async t => {
  const {f, native, file, caller, started} = await defaultAccount(t);
  assert.equal((await runStatus({ref:'17', cwd:f.source, json:true}, f.ports)).exitCode, 0);
  const saved = f.record().chats.at(-1);
  assert.equal(saved.namingError, undefined);
  const occupant = f.herdr.paneOf(saved).agent;
  occupant.name = 'unbound';
  rmSync(file);
  const foreignFile = join(caller, 'sessions', 'rollout-synthetic.jsonl');
  writeFileSync(foreignFile, started);
  utimesSync(foreignFile, f.clock / 1000, f.clock / 1000);
  f.ports.env.CODEX_HOME = caller;
  f.herdr.calls.length = 0;
  const live = await chatSession(saved, {...f.ports, run:f.record()});
  assert.equal(live.alive, true);
  assert.equal(live.namingError?.code, 'chat_name_unverified');
  assert.equal(occupant.name, 'unbound');
  assert.equal(f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'rename').length, 0);
  assert.equal((await native(['agent','get',saved.paneId])).result.agent.agent_session.value, saved.session.id);
});

for (const agent of ['codex', 'claude']) test(`${agent} session discovery keeps a saved default account despite caller overrides`, async t => {
  const home = mkdtempSync(join(tmpdir(), 'pdd-default-evidence-'));
  t.after(() => rmSync(home, {recursive:true, force:true}));
  const root = join(home, 'work'), caller = join(home, 'caller-account');
  const id = 'aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa', since = Date.parse('2026-10-27T17:00:00Z');
  const relative = agent === 'codex' ? join('sessions', 'rollout-synthetic.jsonl')
    : join('projects', root.replace(/[^a-zA-Z0-9]/g, '-'), `${id}.jsonl`);
  const folder = join(home, agent === 'codex' ? '.codex' : '.claude');
  for (const path of [root, join(folder, relative, '..'), join(caller, relative, '..')]) mkdirSync(path, {recursive:true});
  const file = join(folder, relative);
  const row = agent === 'codex' ? metadata(id, root, since)
    : JSON.stringify({type:'user', sessionId:id, cwd:root, timestamp:new Date(since).toISOString(), message:{role:'user',content:'synthetic'}}) + '\n';
  writeFileSync(file, row); utimesSync(file, since / 1000, since / 1000);
  const ports = {env:{HOME:home, CODEX_HOME:caller, CLAUDE_CONFIG_DIR:caller}, now:() => since + 60_000};
  for (const configDir of [null, undefined, '']) {
    const own = await ownSession({run:{agent,root}, chat:{agent,configDir,session:{agent,id}}, since, ports});
    assert.deepEqual(own, {kind:'match',id});
  }
  // Identical metadata in the caller account cannot replace missing default-account evidence.
  rmSync(file); writeFileSync(join(caller, relative), row);
  utimesSync(join(caller, relative), since / 1000, since / 1000);
  assert.deepEqual(await ownSession({run:{agent,root}, chat:{agent,configDir:null,session:{agent,id}}, since, ports}), {kind:'none'});
});
