import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';

// Story oracle: a merge requires current proof, passing checks and behavior,
// and retained evidence for every behavioral finding from a repair.
test('bounded proof gate: 24 combinations plus absent proof', async t => {
  for (const freshness of ['current', 'earlier'])
    for (const check of ['pass', 'fail', 'missing'])
      for (const behavior of ['pass', 'fail'])
        for (const regression of ['present', 'missing']) {
          const w = await coreWorld(t, { settings: { runs: 1 } });
          w.issue(17); await w.tick(); w.build(17); await w.tick();
          const review = w.job(17, 'review');
          const path = join(w.root, 'jobs', '17.json');
          const saved = JSON.parse(readFileSync(path, 'utf8'));
          const finding = 'P2 src/a.js:3 drops a record';
          saved.repairFindings = [finding];
          writeFileSync(path, JSON.stringify(saved));
          const proof = {
            head: freshness === 'current' ? review.head : 'earlier-commit',
            checks: check === 'missing' ? [] : [{ command: 'node --test', result: check }],
            behavior: { result: behavior, detail: 'exercised app' },
            regressions: regression === 'present' ? [{ finding, result: 'pass', path: 'test/a.test.mjs', command: 'node --test test/a.test.mjs', before: 'failed on old code' }] : [],
          };
          w.finish(17, 'review', { result: { verdict: 'PASS', head: review.head, summary: 'Reviewed', mustFix: [], proof } });
          w.suite(17, 0); await w.tick(); await w.tick();
          const expected = freshness === 'current' && check === 'pass' && behavior === 'pass' && regression === 'present';
          assert.equal(w.github.merges.length > 0, expected, `forbidden merge or missing witness: ${freshness}, ${check}, ${behavior}, ${regression}`);
        }
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick(); w.build(17); await w.tick();
  const review = w.job(17, 'review');
  w.finish(17, 'review', { result: { verdict: 'PASS', head: review.head, summary: 'Reviewed', mustFix: [] } });
  w.suite(17, 0); await w.tick(); await w.tick();
  assert.equal(w.github.merges.length, 0, 'forbidden merge with absent proof');
});
