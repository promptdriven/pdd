// Real native-session files in synthetic accounts; all Herdr effects use the repo fake.
import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync, readFileSync, statSync, utimesSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {openRun, runStatus} from '../src/workflow-runner.mjs';
import {chatSession} from '../src/workflow-chat.mjs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';

const metadata = (id, cwd, at) => JSON.stringify({type:'session_meta', payload:{id, cwd, timestamp:new Date(at).toISOString()}}) + '\n';
const otherId = 'bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb';

for (const recovery of ['ended agent', 'closed workspace']) test(`2820 ${recovery} regains its name after elapsed time with original native metadata`, async t => {
  const f = await fixture(t, {agent:'codex'}), account = join(f.base, 'account');
  mkdirSync(join(account, 'sessions'), {recursive:true});
  f.ports.env.CODEX_HOME = account;
  // Exercise the production filesystem reader rather than the fixture's time-window fake.
  delete f.ports.findNativeSessions;
  const native = f.ports.herdr;
  let originalFile;
  f.ports.herdr = async args => {
    const reply = await native(args);
    if (args[0] === 'pane' && args[1] === 'run' && !originalFile) {
      const pane = f.herdr.panes.find(row => row.pane_id === args[2]);
      // The reader admits both native UUID filenames and rollout names without the UUID.
      const name = recovery === 'ended agent' ? 'synthetic' : `synthetic-${pane.agent.agent_session.value}`;
      originalFile = join(account, 'sessions', `rollout-${name}.jsonl`);
      writeFileSync(originalFile, metadata(pane.agent.agent_session.value, pane.cwd, f.clock));
      utimesSync(originalFile, f.clock / 1000, f.clock / 1000);
    }
    return reply;
  };
  assert.equal((await f.run()).exitCode, 0);
  assert.equal((await runStatus({ref:'17', cwd:f.source, json:true}, f.ports)).exitCode, 0);
  const original = f.record().chats.at(-1), bytes = readFileSync(originalFile), mtime = statSync(originalFile).mtimeMs;
  assert.ok(original.session?.id, 'Status must retain the original native UUID');
  // Another real session in the worktree must not obscure this known resumed UUID.
  writeFileSync(join(account, 'sessions', `rollout-other-${otherId}.jsonl`), metadata(otherId, f.record().root, f.clock + 1000));
  f.tick(60_000);
  if (recovery === 'closed workspace') await native(['workspace','close',original.workspaceId]);
  else f.herdr.paneOf(original).agent = null;
  f.herdr.calls.length = 0;
  const result = await openRun({ref:'17', cwd:f.source, packageRoot}, f.ports);
  assert.equal(result.exitCode, 0, result.message);
  const resumed = f.record().chats.at(-1);
  assert.ok(resumed.resumedAt > original.startedAt);
  assert.equal(resumed.namingError, undefined, 'A resumed owned UUID must bind despite older native metadata');
  assert.equal(resumed.session.id, original.session.id);
  assert.equal(resumed.herdrAgentName, original.herdrAgentName);
  assert.equal((await native(['agent','get',original.herdrAgentName])).result.agent.pane_id, resumed.paneId);
  const launches = f.herdr.calls.filter(args => args[0] === 'pane' && args[1] === 'run');
  assert.equal(launches.length, 1);
  assert.match(launches[0][3], /\bresume\b/);
  assert.ok(launches[0][3].includes(original.session.id));
  assert.equal(recovery === 'closed workspace' ? resumed.workspaceId !== original.workspaceId : resumed.paneId === original.paneId, true);
  assert.deepEqual(readFileSync(originalFile), bytes);
  assert.equal(statSync(originalFile).mtimeMs, mtime, 'Resume must accept the unchanged original evidence file');

  // The widened time window never replaces saved UUID, agent, account or worktree proof.
  const occupant = f.herdr.paneOf(resumed).agent;
  occupant.name = 'unnamed-again';
  const empty = join(f.base, 'empty-account'); mkdirSync(join(empty, 'sessions'), {recursive:true});
  for (const [chat, run] of [
    [{...resumed, session:{agent:'codex',id:otherId}}, f.record()],
    [{...resumed, agent:'claude'}, f.record()],
    [{...resumed, configDir:empty}, f.record()],
    [resumed, {...f.record(), root:f.source}],
    [{...resumed, startedAt:original.startedAt + 1}, f.record()],
  ]) {
    f.herdr.calls.length = 0;
    const live = await chatSession(chat, {...f.ports, run});
    assert.equal(live.alive, true);
    assert.equal(live.namingError?.code, 'chat_name_unverified');
    assert.equal(f.herdr.calls.filter(args => args[0] === 'agent' && args[1] === 'rename').length, 0);
    assert.equal(occupant.name, 'unnamed-again');
  }
  // A reader result for another UUID cannot authorize naming this saved session.
  const unrelated = await chatSession(resumed, {...f.ports, run:f.record(), findNativeSessions:async () => [{id:otherId}]});
  assert.equal(unrelated.namingError?.code, 'chat_name_unverified');
  assert.equal(occupant.name, 'unnamed-again');
});
