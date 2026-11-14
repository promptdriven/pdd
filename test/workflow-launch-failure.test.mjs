import test from 'node:test';
import assert from 'node:assert/strict';
import {writeFileSync, chmodSync, readFileSync, mkdirSync} from 'node:fs';
import {join} from 'node:path';
import {spawnSync} from 'node:child_process';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import {runStatus, openRun} from '../src/workflow-runner.mjs';
import {startChat, chatSession} from '../src/workflow-chat.mjs';

test('an agent that exits before detection leaves a private receipt and a durable status diagnostic', async t => {
  const f = await fixture(t, {agent:'codex', name:'feature'});
  const fake = join(f.base, 'codex');
  writeFileSync(fake, '#!/bin/sh\nprintf "Database unavailable\\n"\nexit 14\n'); chmodSync(fake, 0o755);
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    const result = await herdr(args);
    if (args[0] === 'pane' && args[1] === 'run') {
      const pane = f.herdr.panes.find(p => p.pane_id === args[2]);
      const shell = spawnSync('sh', ['-c', args[3]], {encoding:'utf8', env:{...process.env, PATH:`${f.base}:${process.env.PATH}`}});
      assert.equal(shell.status, 14);
      pane.screen = `user@host $ ${args[3]}\n${shell.stdout}Location: /tmp/state.sqlite\nCause: unable to open database file\n`;
      delete pane.agent;
    }
    return result;
  };
  const result = await f.run();
  assert.notEqual(result.exitCode, 0);
  assert.match(result.message, /agent_launch_failed/);
  const chat = f.record().chats[0];
  assert.equal(readFileSync(chat.launchExitFile, 'utf8').trim(), '14');
  assert.equal(chat.state, 'failed');
  assert.equal(chat.evidence.exitCode, 14);
  const status = await runStatus({ref:'17', cwd:f.source}, f.ports);
  assert.match(status.message, /Agent exited; inspect the chat pane for details/);
  assert.doesNotMatch(status.message, /Database unavailable|state\.sqlite|unable to open/);
  assert.doesNotMatch(status.message, /pdd_launch_exit|PDD_AGENT_SESSION/);
  assert.match(status.message, /open 17 --new/);
  assert.match(status.message, /^Next: pdd workflow open 17 --new$/m);
  assert.equal((await chatSession({...chat, resumedAt: chat.startedAt + 1}, {...f.ports, run:f.record()})).launchFailure, undefined);
  const previous = f.ports.herdr;
  f.ports.herdr = async args => { if (args[0] === 'agent' && args[1] === 'get') throw Object.assign(Error('offline'), {code:'server_unavailable'}); return previous(args); };
  assert.match((await runStatus({ref:'17', cwd:f.source}, f.ports)).message, /Agent exited; inspect the chat pane for details/);
  f.ports.herdr = previous;
  const failedReplacement = await openRun({ref:'17', cwd:f.source, packageRoot, newSession:true}, f.ports);
  assert.notEqual(failedReplacement.exitCode, 0);
  assert.match(failedReplacement.message, /agent_launch_failed.*Agent exited; inspect the chat pane for details.*exit 14/);
  const replacement = f.record().chats.at(-1);
  assert.notEqual(replacement.launchExitFile, chat.launchExitFile);
  assert.equal(readFileSync(replacement.launchExitFile, 'utf8').trim(), '14');
  assert.equal(replacement.state, 'failed');
  assert.equal(replacement.evidence.exitCode, 14);
  assert.equal(f.record().chatReplacement.phase, 'launched');
  assert.match((await runStatus({ref:'17', cwd:f.source}, f.ports)).message, /Agent exited; inspect the chat pane for details/);
  f.ports.herdr = herdr;
  const reopened = await openRun({ref:'17', cwd:f.source, packageRoot, newSession:true}, f.ports);
  assert.equal(reopened.exitCode, 0, reopened.message);
  assert.notEqual(f.record().chats.at(-1).paneId, chat.paneId);
});

test('a lost replacement launch reply recovers its failure receipt without redispatch', async t => {
  const f = await fixture(t, {agent:'codex', name:'feature'});
  const fake = join(f.base, 'codex');
  writeFileSync(fake, '#!/bin/sh\nprintf "Database unavailable\\n"\nexit 14\n'); chmodSync(fake, 0o755);
  const herdr = f.ports.herdr;
  let launches = 0;
  f.ports.herdr = async args => {
    const result = await herdr(args);
    if (args[0] === 'pane' && args[1] === 'run') {
      launches++;
      const shell = spawnSync('sh', ['-c', args[3]], {encoding:'utf8', env:{...process.env, PATH:`${f.base}:${process.env.PATH}`}});
      assert.equal(shell.status, 14);
      const pane = f.herdr.panes.find(p => p.pane_id === args[2]);
      pane.screen = shell.stdout; delete pane.agent;
      if (launches === 2) throw Object.assign(Error('reply lost'), {code:'herdr_failed'});
    }
    return result;
  };
  assert.notEqual((await f.run()).exitCode, 0);
  assert.notEqual((await openRun({ref:'17', cwd:f.source, packageRoot, newSession:true}, f.ports)).exitCode, 0);
  const pending = f.record().chatReplacement;
  assert.equal(pending.phase, 'launchRequested');
  const result = await openRun({ref:'17', cwd:f.source, packageRoot, newSession:true}, f.ports);
  assert.notEqual(result.exitCode, 0);
  assert.match(result.message, /agent_launch_failed.*Agent exited; inspect the chat pane for details.*exit 14/);
  assert.equal(launches, 2);
  assert.equal(f.record().chatReplacement.replacement.launchExitFile, pending.replacement.launchExitFile);
  assert.equal(f.record().chats.at(-1).state, 'failed');
});

for (const exitCode of [0, 1]) test(`receipt preserves exit ${exitCode} in a worktree with shell metacharacters`, async t => {
  const f = await fixture(t, {agent:'codex'});
  const root = join(f.base, "quoted ' && folder"), runDir = join(f.base, 'record');
  f.git(f.source, 'worktree', 'add', '-qb', `receipt-${exitCode}`, root);
  mkdirSync(runDir);
  const fake = join(f.base, 'codex');
  writeFileSync(fake, `#!/bin/sh\nexit ${exitCode}\n`); chmodSync(fake, 0o755);
  const run = {runId:`receipt-${exitCode}`, repo:'example/project', number:17, workflow:'feature', root, sourceRoot:f.source,
    commonDir:f.git(f.source, 'rev-parse', '--path-format=absolute', '--git-common-dir'), runDir, agent:'codex', chats:[], done:{}, pr:[]};
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => {
    const result = await herdr(args);
    if (args[0] === 'pane' && args[1] === 'run') {
      const shell = spawnSync('sh', ['-c', args[3]], {encoding:'utf8', env:{...process.env, PATH:`${f.base}:${process.env.PATH}`}});
      assert.equal(shell.status, exitCode, shell.stderr);
      delete f.herdr.panes.find(p => p.pane_id === args[2]).agent;
    }
    return result;
  };
  await assert.rejects(startChat({run, area:'story', message:'Start.'}, f.ports), error => {
    assert.equal(error.code, 'agent_launch_failed');
    assert.equal(error.chat.evidence.exitCode, exitCode);
    assert.equal(readFileSync(error.chat.launchExitFile, 'utf8').trim(), String(exitCode));
    return true;
  });
});

test('a pane without a receipt stays starting inside startup grace', async t => {
  const f = await fixture(t, {agent:'codex', name:'feature'});
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => { const result = await herdr(args); if (args[0] === 'pane' && args[1] === 'run') delete f.herdr.panes.find(p => p.pane_id === args[2]).agent; return result; };
  const result = await f.run();
  assert.equal(result.exitCode, 0);
  assert.match(result.message, /starting, not confirmed/);
  assert.match((await runStatus({ref:'17', cwd:f.source}, f.ports)).message, /starting, not confirmed/);
});

test('a briefly observed agent that exits with an error retains its diagnostic', async t => {
  const f = await fixture(t, {agent:'codex', name:'feature'});
  assert.equal((await f.run()).exitCode, 0);
  const chat = f.record().chats[0], pane = f.herdr.paneOf(chat);
  assert.equal(chat.state, 'running');
  writeFileSync(chat.launchExitFile, '14\n');
  pane.agent = null;
  pane.screen = 'Database unavailable\nCause: unable to open database file\n';
  const status = await runStatus({ref:'17', cwd:f.source}, f.ports);
  assert.match(status.message, /exit 14.*Agent exited; inspect the chat pane for details/);
  assert.equal(f.record().chats[0].evidence.kind, 'launch-exit');
  const json = JSON.parse((await runStatus({ref:'17', cwd:f.source, json:true}, f.ports)).message).runs[0];
  assert.equal(json.group, 'waiting');
  const herdr = f.ports.herdr;
  f.ports.herdr = async args => { if (args[0] === 'agent' && args[1] === 'get') throw Object.assign(Error('offline'), {code:'server_unavailable'}); return herdr(args); };
  assert.match((await runStatus({ref:'17', cwd:f.source}, f.ports)).message, /exit 14.*Agent exited; inspect the chat pane for details/);
});

test('exit evidence never reads or persists private pane content', async t => {
  const f = await fixture(t, {agent:'codex', name:'feature'});
  assert.equal((await f.run()).exitCode, 0);
  const chat = f.record().chats[0], pane = f.herdr.paneOf(chat);
  writeFileSync(chat.launchExitFile, '14\n');
  pane.agent = null;
  pane.screen = 'private customer prompt\nfile credential: file-password-123\nsplit-secret-part-one\nsplit-secret-part-two\n';
  const herdr = f.ports.herdr;
  let reads = 0;
  f.ports.herdr = async args => {
    if (args[0] === 'pane' && args[1] === 'read') reads++;
    return herdr(args);
  };
  const live = await chatSession(chat, {...f.ports, run:f.record()});
  assert.equal(reads, 0);
  assert.deepEqual(live.launchFailure, {exitCode:14, message:'Agent exited; inspect the chat pane for details.'});
  const status = await runStatus({ref:'17', cwd:f.source}, f.ports);
  assert.match(status.message, /exit 14.*Agent exited; inspect the chat pane for details/);
  const durable = JSON.stringify(f.record());
  for (const privateText of ['private customer prompt', 'file-password-123', 'split-secret-part-one', 'split-secret-part-two']) {
    assert.equal(status.message.includes(privateText), false);
    assert.equal(durable.includes(privateText), false);
  }
});
