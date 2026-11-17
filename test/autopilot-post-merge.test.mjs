import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';
import { coreStatus } from '../src/autopilot-core.mjs';

const MIN = 60 * 1000;

test('Autopilot core detects post-merge reopened issues, records forensics, renders target-0 status, and reopens closed report issues instead of duplicating (#3182)', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, report: 'file' } });
  w.github.mergeMovesBase = true;

  // 1) Merge issue #17 cleanly.
  w.issue(17, { title: 'Fix config parse', body: 'Config parse crashes on empty file.' });
  await w.tick();
  const { pr: pr17 } = w.build(17);
  await w.tick();
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [pr17.number]);
  assert.equal(w.github.issues.get(17).state, 'closed');

  // 2) Next tick when #17 stays closed: post-merge check marks PR #100 ok (0 regressions, target 0).
  w.advance(5 * MIN);
  await w.tick();
  const healthyStatus = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, reportRoot: w.reportRoot, now: w.now });
  assert.match(healthyStatus, /Scorecard: 1\/1 \(100%\) zero-edit completion \(target 90-95%\); 1\/1 \(100%\) merged\/would-merge\./);
  assert.match(healthyStatus, /Post-merge: 0 regression\(s\) \(target 0: 0 reopened, 0 reverted, 0 CI; reopen\/revert 0%\) across 1 merged PR\(s\)\./);
  assert.equal(w.reports.issues.size, 0);

  // 3) A person reopens #17 on GitHub after merge because the fix did not hold.
  await w.gh(['api', '--include', '--method', 'PATCH', 'repos/acme/widgets/issues/17', '--input', '-'], {
    input: JSON.stringify({ state: 'open' }),
  });
  // Put pdd:stuck so intake does not immediately re-claim #17 during the post-merge forensic check assertion.
  w.github.label(17, 'pdd:stuck');

  // Advance past the 15-minute post-merge recheck interval and tick.
  w.advance(20 * MIN);
  await w.tick();

  const regressedStatus = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, reportRoot: w.reportRoot, now: w.now });
  assert.match(regressedStatus, /Post-merge: 1 regression\(s\) \(target 0: 1 reopened, 0 reverted, 0 CI; reopen\/revert 100%\) across 1 merged PR\(s\)\./);

  const historyLines = readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line));
  const forensic = historyLines.find(row => row.postMerge === true);
  assert.ok(forensic, 'appended post-merge forensic record to history.jsonl');
  assert.equal(forensic.issue, 17);
  assert.equal(forensic.pr, pr17.number);
  assert.equal(forensic.code, 'post-merge-reopen');
  assert.equal(forensic.report, 'promptdriven/pdd#1');
  assert.equal(forensic.reportState, 'filed');

  assert.equal(w.reports.issues.size, 1, 'filed one PDD post-merge-reopen report');
  const reportIssue = w.reports.issues.get(1);
  assert.equal(reportIssue.state, 'open');
  assert.match(reportIssue.title, /post-merge-reopen/);

  // 4) Close report #1, merge issue #18, and reopen #18 after merge:
  // Autopilot must REOPEN existing report #1 and append the new scrubbed forensic summary instead of creating #2!
  w.reports.close(1);
  assert.equal(w.reports.issues.get(1).state, 'closed');

  w.issue(18, { title: 'Fix trailing comma', body: 'Handle trailing comma.' });
  await w.tick();
  const { pr: pr18 } = w.build(18);
  await w.tick();
  w.review(18, 'PASS');
  w.suite(18, 0);
  await w.tick();
  assert.equal(w.github.issues.get(18).state, 'closed');

  await w.gh(['api', '--include', '--method', 'PATCH', 'repos/acme/widgets/issues/18', '--input', '-'], {
    input: JSON.stringify({ state: 'open' }),
  });
  w.github.label(18, 'pdd:stuck');

  w.advance(20 * MIN);
  await w.tick();

  assert.equal(w.reports.issues.size, 1, 'reused and reopened report #1 instead of filing a duplicate');
  assert.equal(w.reports.issues.get(1).state, 'open', 'existing closed report #1 was reopened');
  assert.equal(w.reports.issues.get(1).comments.length, 1, 'appended scrubbed forensic summary comment to reopened report #1');
  assert.match(w.reports.issues.get(1).comments[0].body, /Reopened automatically because this cause occurred again/);
  assert.match(w.reports.issues.get(1).comments[0].body, /- Error code: post-merge-reopen/);

  const twoRegressionsHistory = readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line));
  const secondForensic = twoRegressionsHistory.find(row => row.postMerge === true && row.issue === 18);
  assert.ok(secondForensic);
  assert.equal(secondForensic.pr, pr18.number);
  assert.equal(secondForensic.report, 'promptdriven/pdd#1');
  assert.equal(secondForensic.reportState, 'reopened');
});
