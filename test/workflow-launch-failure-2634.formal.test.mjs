import test from 'node:test';
import assert from 'node:assert/strict';
import { writeFileSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { fixture } from './helpers/workflow-runner-fixture.mjs';
import { runStatus } from '../src/workflow-runner.mjs';

// Oracle: only a current fresh starting attempt with a matching nonzero exit
// and no live agent proves failure.
test('bounded launch attribution and observation', async t => {
  const f = await fixture(t, {agent:'codex', name:'feature'});
  await f.run();
  const original = f.record();
  const statusFile = join(original.runDir, 'status.json');
  const id = '11111111-1111-4111-8111-111111111111';
  const exitFile = join(original.runDir, `launch-${id}.exit.json`);
  for (const state of ['starting', 'running', 'ended']) {
    for (const resumed of [false, true]) {
      for (const live of [false, true]) {
        for (const receipt of ['missing', 'malformed', 'other', 'zero', 'valid']) {
          const label = `${state}/${resumed}/${live}/${receipt}`;
          const run = structuredClone(original), chat = run.chats.at(-1);
          Object.assign(chat, {state, launchAttempt:{id, exitFile}});
          if (resumed) chat.resumedAt = f.clock;
          else delete chat.resumedAt;
          writeFileSync(statusFile, JSON.stringify(run));
          rmSync(exitFile, {force:true});
          const content = {malformed:'{', other:JSON.stringify({attemptId:'other',exitCode:1}), zero:JSON.stringify({attemptId:id,exitCode:0}), valid:JSON.stringify({attemptId:id,exitCode:1})}[receipt];
          if (content) writeFileSync(exitFile, content);
          f.herdr.paneOf(chat).agent = live ? {kind:'codex',status:'working'} : null;
          const result = await runStatus({ref:'17',cwd:f.source}, f.ports);
          const failed = f.record().chats.at(-1).code === 'agent_launch_exited';
          assert.equal(failed, state === 'starting' && !resumed && !live && receipt === 'valid', label);
          if (failed) {
            assert.match(result.message, /code 1/, label);
            assert.match(result.message, /open 17 --new/, label);
          }
        }
      }
    }
  }
});
