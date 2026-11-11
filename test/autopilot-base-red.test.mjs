import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync, mkdtempSync, rmSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
import { coreWorld } from './helpers/core-world.mjs';
import { coreStatus } from '../src/autopilot-core.mjs';
import { failingTestNames, baseRedFingerprint, mainRedRoute, MAIN_RED_LABEL } from '../src/autopilot-base-red.mjs';

// Expected results come from issue #3181, chaos row B7, ticket T03 and the group 3 design (section B).
const MIN = 60 * 1000;
const jobFile = (w, n) => JSON.parse(readFileSync(join(w.root, 'jobs', `${n}.json`), 'utf8'));
const mainRed = w => [...w.github.issues.values()].filter(issue => issue.labels.includes(MAIN_RED_LABEL));
const endComments = (w, n) => w.comments(n).filter(body => body.includes('<!-- pdd:autopilot-core:end:'));
const tipOf = w => w.git(w.cwd, 'ls-remote', w.remote, 'refs/heads/main').split('\t')[0];
const baseRuns = w => w.started.filter(job => job.issue === 'base');
const status = w => coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now });

test('failing test names: top-level TAP failures of node:test, no TODO or SKIP, no checkout root, at most 50', () => {
  const root = '/work/checkout';
  const log = ['TAP version 13', '# Subtest: top fails', 'not ok 1 - top fails', '    not ok 1 - child fails', 'not ok 2 - parent', 'not ok 3 - todo test # TODO',
    'not ok 4 - skipped test # SKIP', 'ok 5 - fine', `not ok 6 - ${root}/test/broken.test.mjs`, 'not ok 7 - top fails', 'not ok 8 -  ', '  not ok 9 - indented'].join('\r\n');
  assert.deepEqual(failingTestNames(log, { root }), { names: ['top fails', 'parent', 'test/broken.test.mjs'], more: false });
  const many = Array.from({ length: 60 }, (_, i) => `not ok ${i + 1} - test ${i}`).join('\n');
  const capped = failingTestNames(many);
  assert.equal(capped.names.length, 50); assert.equal(capped.more, true); assert.equal(capped.names[49], 'test 49');
  assert.deepEqual(failingTestNames(''), { names: [], more: false });
});

test('failing test names: the real node:test TAP output of a run', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-base-red-tap-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  writeFileSync(join(dir, 'a.test.mjs'), ["import test from 'node:test';", "test('passes', () => {});", "test('fails on main', () => { throw new Error('x'); });",
    "test('parent', async t => { await t.test('child', () => { throw new Error('y'); }); });", "test('later', { todo: true }, () => { throw new Error('z'); });", ''].join('\n'));
  const run = spawnSync(process.execPath, ['--test', '--test-reporter=tap', join(dir, 'a.test.mjs')], { encoding: 'utf8', env: Object.fromEntries(Object.entries(process.env).filter(([key]) => !['NODE_OPTIONS', 'NODE_TEST_CONTEXT'].includes(key))) });
  assert.notEqual(run.status, 0);
  assert.deepEqual(failingTestNames(run.stdout, { root: dir }).names, ['fails on main', 'parent']);
});

test('fingerprint: what and the names in any order, never the commit; the main-red issue goes to the work repository', () => {
  assert.equal(baseRedFingerprint('suite', ['b', 'a']), baseRedFingerprint('suite', ['a', 'b']));
  assert.notEqual(baseRedFingerprint('suite', ['a']), baseRedFingerprint('ci', ['a']));
  assert.notEqual(baseRedFingerprint('suite', ['a']), baseRedFingerprint('suite', ['a', 'b']));
  assert.match(baseRedFingerprint('ci', ['test']), /^[0-9a-f]{16}$/);
  for (const report of ['file', 'draft', 'off']) for (const mode of ['auto', 'observe']) assert.equal(mainRedRoute({ report, mode }), 'file');
});

test('B1 a CI check that fails once runs once more; it passes on the rerun: one rerun call, no repair, the PR merges', async t => {
  const w = await coreWorld(t);
  w.github.rerunnable = true;
  w.issue(17); await w.tick();
  const { pr, head } = w.build(17, { checks: false });
  w.github.setRun(head, { conclusion: 'failure' });
  await w.tick();
  assert.equal(w.github.reruns.length, 1); assert.match(w.github.reruns[0].route, /^\/actions\/jobs\/\d+\/rerun$/);
  assert.equal(w.job(17, 'repair'), undefined, 'a check that failed once gets no repair');
  assert.ok(w.job(17, 'review') && w.job(17, 'suite'), 'the review and the suite run while the rerun runs');
  w.review(17, 'PASS'); w.suite(17, 0);
  await w.tick();
  assert.equal(w.github.merges.length, 0, 'the rerun still runs: no merge');
  w.github.setRun(head, { conclusion: 'success' });
  await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.equal(w.github.reruns.length, 1, 'one rerun call in all');
  assert.equal(w.started.filter(job => job.role === 'repair').length, 0);
});

test('B2 a CI check red twice and green on the base tip is the PR\'s own red: one repair (other apps are rerequested; a pending base waits)', async t => {
  const w = await coreWorld(t);
  w.github.rerunnable = true;
  w.issue(17); await w.tick();
  const { head } = w.build(17, { checks: false });
  w.github.setRun(head, { name: 'lint', conclusion: 'failure', app: 'buildkite' });
  await w.tick();
  assert.equal(w.github.reruns.length, 1); assert.match(w.github.reruns[0].route, /^\/check-runs\/\d+\/rerequest$/);
  w.github.setRun(head, { name: 'lint', conclusion: 'failure', app: 'buildkite' });
  w.github.setRun(tipOf(w), { name: 'lint', status: 'in_progress', app: 'buildkite' });
  await w.tick();
  assert.equal(w.job(17, 'repair'), undefined, 'the same check still runs on the base tip: wait, no repair');
  w.github.setRun(tipOf(w), { name: 'lint', conclusion: 'success', app: 'buildkite' });
  await w.tick();
  const repairs = w.started.filter(job => job.role === 'repair');
  assert.equal(repairs.length, 1);
  assert.match(repairs[0].input, /CI check lint failed for head/); assert.doesNotMatch(repairs[0].input, /Also red on the base/);
  assert.equal(w.github.reruns.length, 1, 'one rerun per check name per head');
  assert.equal(mainRed(w).length, 0);
});

test('B2/B4 a CI check red twice and red on the base tip: no repair, no END, one main-red issue, no slot, the next issue starts; the base turns green and the issue closes: the PR refreshes and merges', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.github.rerunnable = true;
  const tip0 = tipOf(w);
  w.github.setRun(tip0, { conclusion: 'failure' });
  w.issue(17); w.issue(18);
  await w.tick();
  assert.equal(w.job(18, 'build'), undefined, 'one slot');
  const { pr, head } = w.build(17, { checks: false });
  w.github.setRun(head, { conclusion: 'failure' });
  await w.tick();
  assert.equal(w.github.reruns.length, 1);
  w.github.setRun(head, { conclusion: 'failure' });
  w.review(17, 'PASS'); w.suite(17, 0);
  await w.tick();
  assert.equal(w.started.filter(job => job.role === 'repair').length, 0, 'no repair for a red that is also on the base');
  assert.deepEqual(endComments(w, 17), []); assert.ok(!w.labels(17).includes('pdd:stuck')); assert.ok(w.labels(17).includes('pdd:working'));
  assert.equal(w.github.prs.get(pr.number).state, 'open');
  const filed = mainRed(w);
  assert.equal(filed.length, 1);
  assert.equal(filed[0].title, 'Main is red: ci');
  assert.match(filed[0].body, new RegExp(`at ${tip0}`)); assert.match(filed[0].body, /PR #100 \(issue #17\)/);
  assert.match(filed[0].body, new RegExp(`<!-- pdd:autopilot-core:base-red:${baseRedFingerprint('ci', ['ci'])} -->$`));
  const saved = jobFile(w, 17);
  assert.equal(saved.baseRed.what, 'ci'); assert.equal(saved.baseRed.tip, tip0); assert.equal(saved.baseRed.report.number, filed[0].number);
  assert.ok(w.job(18, 'build'), 'the job holds no slot: the next issue starts');
  assert.match(status(w), /Jobs: 1 of 1 slots busy/);
  assert.match(status(w), /#17 PR #100 at [0-9a-f]{7}: .*; main is red \(ci\) since 2026-11-10T\d\d:\d\d:\d\d\.\d{3}Z; no slot/);
  // The base moves, but the main-red issue is open: the PR waits. The issue closes: the PR refreshes onto the base.
  const tip1 = w.baseCommit('fix.txt', 'fixed\n');
  w.github.setRun(tip1, { conclusion: 'success' });
  w.progress(18, 'build'); await w.tick();
  assert.ok(jobFile(w, 17).baseRed, 'the issue is still open');
  w.github.close(filed[0].number);
  w.progress(18, 'build'); await w.tick();
  const refreshed = jobFile(w, 17);
  assert.equal(refreshed.baseRed, undefined); assert.notEqual(refreshed.head, head); assert.equal(refreshed.review.kept, true);
  w.github.setRun(refreshed.head, { conclusion: 'success' });
  w.progress(18, 'build'); await w.tick();
  w.suite(17, 0); w.progress(18, 'build'); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.equal(w.started.filter(job => job.role === 'repair').length, 0);
});

test('B3 a suite fails with X and the base suite at the merge base fails X: base-red; two jobs on one base share one base suite run and one main-red issue; one alert after the quiet period', async t => {
  const w = await coreWorld(t);
  w.issue(17); w.issue(18);
  await w.tick();
  w.build(17); w.build(18);
  await w.tick();
  for (const n of [17, 18]) { w.review(n, 'PASS'); w.say(n, 'suite', 'not ok 1 - validation saves full output\n# fail 1'); w.suite(n, 1); }
  await w.tick();
  assert.equal(baseRuns(w).length, 1, 'one base suite run for both jobs');
  const base = baseRuns(w)[0], mergeBase = tipOf(w);
  assert.equal(base.head, mergeBase); assert.equal(w.git(base.cwd, 'rev-parse', 'HEAD'), mergeBase);
  assert.deepEqual(base.args.slice(-5), ['suite', '--command', 'npm test', '--timeout', '0']); assert.equal(base.env.CI, 'true');
  assert.match(base.id, /^base-suite-/);
  assert.equal(w.started.filter(job => job.role === 'repair').length, 0, 'no repair before the compare');
  assert.equal(JSON.parse(readFileSync(join(w.root, 'base-suite', `${mergeBase}.json`), 'utf8')).state, 'running');
  w.say('base', 'suite', 'not ok 1 - validation saves full output\n# fail 1'); w.finish('base', 'suite', { code: 1 });
  await w.tick();
  assert.equal(w.started.filter(job => job.role === 'repair').length, 0);
  const filed = mainRed(w);
  assert.equal(filed.length, 1, 'the second job finds the first one\'s issue by its marker');
  assert.equal(filed[0].title, 'Main is red: validation saves full output');
  assert.match(filed[0].body, /- Failing tests: \n {2}- validation saves full output/); assert.match(filed[0].body, /Last lines of the base suite log/);
  for (const n of [17, 18]) { const saved = jobFile(w, n); assert.equal(saved.baseRed.what, 'suite'); assert.equal(saved.baseRed.sha, mergeBase); assert.equal(saved.baseRed.report.number, filed[0].number); }
  assert.equal(JSON.parse(readFileSync(join(w.root, 'base-suite', `${mergeBase}.json`), 'utf8')).state, 'fail');
  assert.equal(existsSync(base.cwd), false, 'the base checkout goes after the run');
  await w.tick();
  assert.ok(w.job(filed[0].number, 'build'), 'no job holds a slot: the next tick takes the main-red issue as Autopilot\'s own work');
  assert.equal(baseRuns(w).length, 1);
  const alerts = [];
  w.advance(50 * MIN); await w.tick({ alert: async a => { alerts.push(a); } });
  await w.tick({ alert: async a => { alerts.push(a); } });
  assert.deepEqual(alerts.map(a => [a.issue, a.kind]), [[17, 'stuck'], [18, 'stuck']], 'one alert per waiting job');
  assert.match(alerts[0].text, /PR #100 has waited 50 minutes because main is red \(validation saves full output\) \(issue #19\)/);
  assert.deepEqual([...endComments(w, 17), ...endComments(w, 18)], []);
});

test('B3 a suite fails with X and Y and the base fails only X: one repair whose red names Y and says X is also red on the base', async t => {
  const w = await coreWorld(t);
  w.issue(17); await w.tick();
  w.build(17); await w.tick();
  w.review(17, 'PASS'); w.say(17, 'suite', 'not ok 1 - X keeps the value\nnot ok 2 - Y saves the file'); w.suite(17, 1);
  await w.tick();
  assert.equal(w.job(17, 'repair'), undefined, 'the base suite runs first');
  w.say('base', 'suite', 'not ok 1 - X keeps the value'); w.finish('base', 'suite', { code: 1 });
  await w.tick();
  const repair = w.job(17, 'repair');
  assert.ok(repair);
  assert.match(repair.input, /The full test suite failed for head [0-9a-f]{7}/);
  assert.match(repair.input, /Failing tests from this change: Y saves the file\./);
  assert.match(repair.input, /Also red on the base \([0-9a-f]{7}\), not from this change: X keeps the value\./);
  assert.equal(mainRed(w).length, 0);
});

test('B3 a base suite that passes, or whose runner fails 3 times, leaves the suite red as the PR\'s own red', async t => {
  let w = await coreWorld(t);
  w.issue(17); await w.tick(); w.build(17); await w.tick();
  w.review(17, 'PASS'); w.say(17, 'suite', 'not ok 1 - X'); w.suite(17, 1); await w.tick();
  w.finish('base', 'suite', { code: 0 }); await w.tick();
  assert.doesNotMatch(w.job(17, 'repair').input, /Also red on the base|Failing tests from this change/);
  w = await coreWorld(t);
  w.issue(17); await w.tick(); w.build(17); await w.tick();
  w.review(17, 'PASS'); w.say(17, 'suite', 'not ok 1 - X'); w.suite(17, 1); await w.tick();
  for (let i = 0; i < 3; i++) { assert.equal(w.job(17, 'repair'), undefined); w.finish('base', 'suite', { code: 86 }); await w.tick(); }
  assert.equal(baseRuns(w).length, 3, 'a runner failure starts the base suite again, at most twice');
  assert.ok(w.job(17, 'repair')); assert.equal(mainRed(w).length, 0);
  assert.equal(JSON.parse(readFileSync(join(w.root, 'base-suite', `${tipOf(w)}.json`), 'utf8')).state, 'broken');
});

test('B4 a review FAIL with a base-red suite repairs only the review finding', async t => {
  const w = await coreWorld(t);
  w.issue(17); await w.tick(); w.build(17); await w.tick();
  w.review(17, 'FAIL', ['P2 change-17.txt:1 the value is wrong']); w.say(17, 'suite', 'not ok 1 - X'); w.suite(17, 1); await w.tick();
  assert.equal(w.job(17, 'repair'), undefined, 'no repair before the compare, also with a red review');
  w.say('base', 'suite', 'not ok 1 - X'); w.finish('base', 'suite', { code: 1 }); await w.tick();
  const repair = w.job(17, 'repair');
  assert.match(repair.input, /the value is wrong/); assert.doesNotMatch(repair.input, /full test suite failed/);
  assert.equal(mainRed(w).length, 0, 'not the only red: no hold and no main-red issue');
});

test('B4 the job of a main-red issue never gets base-red: its own red is red', async t => {
  const w = await coreWorld(t);
  w.github.rerunnable = true;
  w.github.setRun(tipOf(w), { conclusion: 'failure' });
  w.issue(30, { title: 'Main is red: ci', body: `Fix main.\n\n<!-- pdd:autopilot-core:base-red:${baseRedFingerprint('ci', ['ci'])} -->`, labels: [MAIN_RED_LABEL] });
  await w.tick();
  const { head } = w.build(30, { checks: false });
  w.github.setRun(head, { conclusion: 'failure' });
  await w.tick();
  assert.equal(w.github.reruns.length, 1, 'it still gets its one rerun');
  w.github.setRun(head, { conclusion: 'failure' }); await w.tick();
  assert.match(w.job(30, 'repair').input, /CI check ci failed/);
  assert.equal(jobFile(w, 30).baseRed, undefined);
});

test('chaos B7: a failing test merged to main no longer costs a repair or a pdd:stuck (the rerun call fails: the compare goes on at once)', async t => {
  const w = await coreWorld(t);
  const tip = w.baseCommit('test/bad.test.mjs', "test('sum is 3', () => assert.equal(1 + 1, 3));\n");
  w.github.setRun(tip, { name: 'test', conclusion: 'failure' });
  w.issue(12); await w.tick();
  const { pr, head } = w.build(12, { checks: false });
  w.github.setRun(head, { name: 'test', conclusion: 'failure' });
  await w.tick();
  assert.ok(w.github.writes.some(([method, route]) => method === 'POST' && /^\/actions\/jobs\/\d+\/rerun$/.test(route)), 'one rerun call');
  assert.equal(w.github.reruns.length, 0, 'GitHub refused it: no rerun');
  assert.equal(w.job(12, 'repair'), undefined);
  w.review(12, 'PASS'); w.say(12, 'suite', 'not ok 1 - sum is 3'); w.suite(12, 1);
  await w.tick();
  w.say('base', 'suite', 'not ok 1 - sum is 3'); w.finish('base', 'suite', { code: 1 });
  await w.tick();
  assert.equal(w.started.filter(job => job.role === 'repair').length, 0);
  assert.ok(!w.labels(12).includes('pdd:stuck')); assert.deepEqual(endComments(w, 12), []);
  assert.equal(w.github.prs.get(pr.number).state, 'open');
  assert.deepEqual(mainRed(w).map(issue => issue.title), ['Main is red: sum is 3'], 'the suite names the test');
  assert.equal(jobFile(w, 12).baseRed.what, 'suite');
});

test('stopChecks stops the base suite only when no other job waits for it, and removes its record', async t => {
  const w = await coreWorld(t);
  w.issue(17); w.issue(18); await w.tick();
  w.build(17); w.build(18); await w.tick();
  for (const n of [17, 18]) { w.review(n, 'PASS'); w.say(n, 'suite', 'not ok 1 - X'); w.suite(n, 1); }
  await w.tick();
  const base = baseRuns(w)[0], record = join(w.root, 'base-suite', `${tipOf(w)}.json`);
  assert.equal(jobFile(w, 17).baseSuite, tipOf(w));
  w.github.unlabel(17, 'pdd:working'); await w.tick();
  assert.equal(w.stopped.includes(base.id), false, 'job 18 still waits for it');
  w.github.unlabel(18, 'pdd:working'); await w.tick();
  assert.equal(w.stopped.includes(base.id), true);
  assert.equal(existsSync(record), false);
});
