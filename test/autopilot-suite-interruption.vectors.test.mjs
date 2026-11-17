import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { coreStatus } from '../src/autopilot-core.mjs';
import { coreWorld } from './helpers/core-world.mjs';

const endComments = (world, issue) => world.comments(issue).filter(body => body.includes('<!-- pdd:autopilot-core:end:'));
const NOT_RUN = 'Runtime: not run (no prompt changed)';

test('#3473 a waiting suite interrupted before admission is not run and uses only the runner retry budget', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, report: 'draft' } });
  const queue = join(w.dir, 'suite-queue'); mkdirSync(queue);
  const env = {...process.env, PDD_SUITE_QUEUE:queue};
  const tick = () => w.tick({env});
  w.suiteQueued = true;
  w.issue(17); await tick();
  const { head } = w.build(17, {body:`Fixes #17.\n\n${NOT_RUN}`,result:{promptChanged:false}}); await tick();
  w.review(17, 'PASS');
  const evidence = () => JSON.parse(readFileSync(join(w.root,'logs',`17-evidence-${head}.json`),'utf8')).suite;
  const status = () => coreStatus({state:w.state,settings:w.settings}, {root:w.root,now:w.now,env});
  const stateOf = (part, ticket, fields) => writeFileSync(join(queue,`ticket-${ticket}.json`), JSON.stringify({
    ticket, pid:process.pid, cwd:part.cwd, state:'waiting', outcome:'running', queuedAt:w.now(), startedAt:null,
    finishedAt:null, childPid:null, recorderPid:null, signal:null, exitCode:null, counts:null, reason:null, ...fields,
  }));
  for (let attempt = 1; attempt <= 3; attempt++) {
    const part = w.job(17,'suite');
    stateOf(part, attempt, {}); await tick();
    assert.equal(evidence().state, 'waiting');
    assert.match(status(), /suite waiting for a check slot/);
    if (attempt === 2) stateOf(part, attempt, {pid:2147483647});
    else stateOf(part, attempt, {state:'finished', outcome:'interrupted', finishedAt:w.now(), signal:'SIGTERM'});
    w.kill(17,'suite');
    writeFileSync(part.exit, JSON.stringify({code:null, signal:'SIGTERM', at:w.now()}));
    assert.match(status(), /suite interrupted before starting \(SIGTERM\)/);
    w.advance(1000); await tick();
    assert.equal(evidence().exit, null);
    assert.deepEqual(evidence().interruption, {ticket:attempt, signal:'SIGTERM', log:part.log.split('/').at(-1)});
    if (attempt < 3) {
      assert.notEqual(w.job(17,'suite').id, part.id);
      assert.match(status(), /last suite attempt interrupted before starting \(SIGTERM\)/);
    }
  }
  assert.equal(evidence().state, 'interrupted');
  assert.equal(w.started.filter(part => part.role === 'suite').length, 3);
  assert.equal(w.job(17,'repair'), undefined);
  assert.deepEqual(w.github.merges, []);
  assert.match(endComments(w,17)[0], /suite.*interrupted before starting.*SIGTERM.*3 tries/i);
});
