import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync} from 'node:fs';
import {join} from 'node:path';
import {fixture} from './helpers/workflow-runner-fixture.mjs';
import {tidyRuns, runStatus} from '../src/workflow-runner.mjs';

async function finished(t) {
  const f = await fixture(t, {agent:'claude'});
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(); run.state = 'completed'; run.chats[0].endedAt = f.clock;
  writeFileSync(join(run.runDir, 'status.json'), JSON.stringify(run));
  f.tick(16*60_000); f.herdr.idle();
  return {f, run, chat:run.chats[0]};
}

test('3084 tidy: restart terminal refresh is saved before close', async t => {
  const {f, chat} = await finished(t);
  for (const pane of f.herdr.panes) { pane.terminal_id += '-restart'; pane.agent = null; }
  const terminal = f.herdr.paneOf(chat).terminal_id, herdr = f.ports.herdr;
  let checkpoint = false;
  f.ports.herdr = async args => {
    if (args[0] === 'tab' && args[1] === 'close') {
      checkpoint = true;
      assert.equal(f.record().chats[0].terminalId, terminal);
      assert.ok(f.record().chats[0].closed);
    }
    return herdr(args);
  };
  assert.equal((await tidyRuns({}, f.ports)).closed, 1, 'restart-close-count');
  assert.ok(checkpoint);
  assert.equal(f.herdr.paneOf(chat), undefined);
});

for (const guard of ['absent', 'busy', 'split', 'grace', 'caller', 'unknown']) {
  test(`3084 status: eligibility agrees with tidy (${guard})`, async t => {
    const {f, run, chat} = await finished(t), pane = f.herdr.paneOf(chat);
    if (guard === 'absent') await f.herdr.herdr(['workspace','close',chat.workspaceId]);
    if (guard === 'busy') pane.agent.agent_status = 'working';
    if (guard === 'split') f.herdr.panes.push({...pane, pane_id:'split', terminal_id:'split-term'});
    if (guard === 'grace') { run.chats[0].endedAt = f.clock; writeFileSync(join(run.runDir,'status.json'),JSON.stringify(run)); }
    if (guard === 'caller') f.ports.env.HERDR_PANE_ID = chat.paneId;
    if (guard === 'unknown') { const herdr=f.ports.herdr; f.ports.herdr=async args=>{
      if (args[0]==='agent' && args[1]==='get') throw Object.assign(Error('offline'),{code:'unavailable'});
      return herdr(args);
    }; }
    const bytes = readFileSync(join(run.runDir,'status.json'));
    f.herdr.calls.length = 0;
    const status = await runStatus({cwd:f.source,json:true},f.ports);
    assert.equal(status.exitCode,0);
    assert.equal(JSON.parse(status.message).herdr.finishedOpen, 0, 'eligible-chat-count');
    const text = await runStatus({cwd:f.source},f.ports);
    assert.equal(text.message.includes('pdd workflow tidy'),false,'eligible-tidy-hint');
    assert.deepEqual(readFileSync(join(run.runDir,'status.json')),bytes);
    assert.equal(f.herdr.calls.some(args=>['close','create','run'].includes(args[1])),false);
  });
}
