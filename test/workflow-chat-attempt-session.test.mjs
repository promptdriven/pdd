import test from 'node:test';
import assert from 'node:assert/strict';
import {mkdirSync} from 'node:fs';
import * as runner from '../src/workflow-runner.mjs';
import {fixture,packageRoot} from './helpers/workflow-runner-fixture.mjs';
const open = runner.openRunCommand ?? runner.openRun;
const launches = f => f.herdr.calls.filter(a => a[0] === 'pane' && a[1] === 'run');
const shell = pane => ({result:{type:'pane_process_info',process_info:{pane_id:pane,shell_pid:41,foreground_process_group_id:41,foreground_processes:[{pid:41,name:'zsh'}]}}});
for (const agent of ['claude','codex']) for (const mode of ['unsent','session','unavailable','ambiguous']) {
  const dispatched = mode !== 'unsent';
  test(`${agent}: foreground shell reconciles this attempt session before fresh retry (${mode})`, async t => {
    const f = await fixture(t,{agent});
    if (agent === 'codex') { const dir = `${f.base}/codexhome`; mkdirSync(dir); f.ports.env.CODEX_HOME = dir; }
    await f.run();
    const owner = f.record();
    const healthy = f.herdr.herdr;
    f.ports.herdr = async args => {
      if (args[0] === 'pane' && args[1] === 'run') {
        if (dispatched) await healthy(args);
        throw Object.assign(Error('lost reply'),{code:'server_unavailable'});
      }
      return healthy(args);
    };
    await open({ref:'17',cwd:f.source,packageRoot,newSession:true},f.ports);
    const pending = f.record().chatReplacement;
    assert.ok(pending?.replacement, 'A lost fresh launch retains replacement custody');
    const saved = structuredClone(pending);
    if (dispatched) { const pane = f.herdr.paneOf(pending.replacement); assert.ok(pane,'Replacement pane exists'); pane.agent = null; }
    f.ports.herdr = args => args[0] === 'pane' && args[1] === 'process-info' ? shell(args[3]) : healthy(args);
    const lookups=[];
    f.ports.findNativeSessions = async (...args) => {
      lookups.push(args);
      if(mode==='unavailable')throw Object.assign(Error('lookup unavailable'),{code:'session_lookup_unavailable'});
      const id=pending.replacement.session?.id ?? '11111111-1111-4111-8111-111111111111';
      return mode==='ambiguous' ? [{id},{id:'22222222-2222-4222-8222-222222222222'}] : dispatched ? [{id}] : [];
    };
    f.tick(31_000);
    const before = launches(f).length;
    await open({ref:'17',cwd:f.source,packageRoot,newSession:true},f.ports);
    const fresh = launches(f).slice(before).filter(a => !/--resume|resume '/.test(a[3]));
    assert.equal(fresh.length,dispatched ? 0 : 1,'Attempt session evidence forbids a fresh first message');
    assert.ok(lookups.length > 0,'Native attempt evidence is inspected before any fresh retry');
    const [target,config]=lookups[0];
    assert.equal(target.agent,agent);
    assert.equal(target.root,owner.root);
    assert.equal(target.startedAt,pending.recovery?.latestLaunchRequest?.at ?? pending.replacement.startedAt);
    assert.equal(target.endedAt,f.clock);
    if(agent==='claude'){assert.equal(target.sessionId,pending.replacement.session.id);assert.equal(config.claudeConfigDir,owner.configDir);}
    else assert.equal(config.codexHome,owner.configDir);
    if(mode==='unavailable'||mode==='ambiguous'){assert.equal(f.record().chatReplacement.id,pending.id);assert.equal(f.record().chatReplacement.phase,'launchRequested');}
    assert.equal(f.record().runId,owner.runId);
    assert.equal(f.record().root,owner.root);
    assert.deepEqual(f.record().done,owner.done);
    assert.deepEqual(f.record().gate,owner.gate);
    assert.equal(saved.id,pending.id,'The retry retains this attempt identity');
  });
}
