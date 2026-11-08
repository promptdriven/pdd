import test from 'node:test';
import assert from 'node:assert/strict';
import {existsSync, writeFileSync} from 'node:fs';
import {fixture, packageRoot} from './helpers/workflow-runner-fixture.mjs';
import * as runner from '../src/workflow-runner.mjs';
import {runPdd} from '../src/pdd-cli.mjs';

test('2709 replay: twenty completed runs release every run pane and retain reopenable native custody', async t => {
  const f = await fixture(t);
  const sink = {write(){}};
  for (let i=0;i<20;i++) {
    let reply = await f.run(); assert.equal(reply.exitCode,0,reply.message);
    const root = f.record().root;
    reply = await runner.stepDone({step:'scope',summary:'contained change',cwd:root},f.ports);
    assert.equal(reply.exitCode,0,reply.message); f.herdr.idle();
    reply = await runner.approveRun({ref:'17',cwd:f.source,packageRoot},f.ports);
    assert.equal(reply.exitCode,0,reply.message);
    const run = f.record();
    writeFileSync(`${root}/value.mjs`, 'export const value = 2;\n');
    f.git(root,'add','value.mjs'); f.git(root,'commit','-qm','change value');
    for (const step of run.areas[run.area].steps) {
      reply = await runner.stepDone({step,summary:`checked ${step}`,cwd:root,packageRoot},f.ports);
      assert.equal(reply.exitCode,0,reply.message);
    }
    f.merged = true; f.herdr.idle();
    reply = await runner.runStatus({ref:'17',cwd:f.source},f.ports);
    assert.equal(reply.exitCode,0,reply.message); assert.equal(f.record().state,'completed');
    f.tick(16*60_000);
    const exitCode = await runPdd(['workflow','tidy'],{cwd:f.source,env:f.ports.env,stdout:sink,stderr:sink,packageRoot,
      workflowRunner:{tidyRuns: input => runner.tidyRuns(input,f.ports)}});
    assert.equal(exitCode,0,'tidy must release completed runs');
    assert.equal(f.herdr.panes.length,1,`run ${i+1} leaves only the repository shell`);
    assert.ok(f.record().chats.every(chat => chat.closed && chat.session?.id && existsSync(chat.messageFile)));
  }
});

test('2709 repair replay: live run shell survives completion cleanup and a later failed close recovers', async t => {
  const f = await fixture(t);
  assert.equal((await f.run()).exitCode, 0);
  const run = f.record(), shell = f.herdr.paneOf(run.layout);
  run.state = 'completed'; run.chats[0].endedAt = f.clock;
  writeFileSync(`${run.runDir}/status.json`, JSON.stringify(run));
  f.tick(16 * 60_000); f.herdr.idle();
  shell.agent = {agent:'codex', agent_status:'working'};
  const retained = await runner.tidyRuns({}, f.ports);
  assert.equal(retained.closed, 1);
  assert.ok(f.herdr.paneOf(run.layout), 'completion must retain live work in the original shell');
  assert.equal(retained.kept, 1);
  assert.equal(f.record().cleanupKept[0].reason, 'run_shell_busy');

  shell.agent = null;
  const command = f.ports.herdr;
  f.ports.herdr = async args => {
    if (args[0] === 'workspace' && args[1] === 'close') throw Object.assign(Error('temporary refusal'), {code:'herdr_failed'});
    return command(args);
  };
  await runner.tidyRuns({}, f.ports);
  assert.equal(f.record().layout.phase, 'close_intent');
  assert.ok(f.herdr.paneOf(run.layout));
  f.ports.herdr = command;
  const retried = await runner.tidyRuns({}, f.ports);
  assert.equal(retried.kept, 0);
  assert.equal(f.record().layout.phase, 'closed');
  assert.equal(f.herdr.panes.length, 1, 'retry must release the run shell and keep the repository shell');
  assert.ok(f.record().chats[0].session.id);
  assert.ok(existsSync(run.root));
});
