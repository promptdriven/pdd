import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync, writeFileSync, mkdtempSync, rmSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';
import { spawnSync } from 'node:child_process';
import { coreWorld } from './helpers/core-world.mjs';
import { coreStatus, failingTests } from '../src/autopilot-core.mjs';
import { sameTest, baseRedFingerprint, mainRedRoute, fileMainRed, baseRedWait, ciVsBase, MAIN_RED_LABEL } from '../src/autopilot-base-red.mjs';

// Expected results come from issue #3181, chaos row B7, ticket T03 and the group 3 design (section B).
const MIN = 60 * 1000;
const jobFile = (w, n) => JSON.parse(readFileSync(join(w.root, 'jobs', `${n}.json`), 'utf8'));
const mainRed = w => [...w.github.issues.values()].filter(issue => issue.labels.includes(MAIN_RED_LABEL));
const endComments = (w, n) => w.comments(n).filter(body => body.includes('<!-- pdd:autopilot-core:end:'));
const tipOf = w => w.git(w.cwd, 'ls-remote', w.remote, 'refs/heads/main').split('\t')[0];
const baseRuns = w => w.started.filter(job => job.issue === 'base');
const status = w => coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now });

test('failing tests: TAP and spec lines at any depth, with the file when the log names it; no TODO or SKIP; a limit', () => {
  const tap = ['TAP version 13', '# Subtest: top fails', 'not ok 1 - top fails', '  ---', "  location: '/work/checkout/test/a.test.mjs:4:1'", '  ...',
    '# Subtest: parent', '    not ok 1 - child fails', '      ---', "      location: '/work/checkout/test/a.test.mjs:5:37'", '      ...', '    ok 2 - child ok',
    "      location: '/work/checkout/test/other.test.mjs:9:1'", 'not ok 2 - parent', 'not ok 3 - todo test # TODO', 'not ok 4 - skipped test # SKIP', 'ok 5 - fine',
    'not ok 6 - top fails', 'not ok 7 -  '].join('\r\n');
  assert.deepEqual(failingTests(tap), [{ name: 'top fails', file: '/work/checkout/test/a.test.mjs' }, { name: 'child fails', file: '/work/checkout/test/a.test.mjs' },
    { name: 'parent', file: null }]);
  const spec = ['\x1b[31m✖ top fails \x1b[90m(0.48ms)\x1b[39m\x1b[39m', '▶ parent', '  \x1b[31m✖ child fails \x1b[90m(0.16ms)\x1b[39m', '\x1b[31m✖ parent \x1b[90m(1.7ms)\x1b[39m',
    '\x1b[31m✖ todo fails \x1b[90m(0.07ms)\x1b[39m # TODO', '﹣ skipped (0.05ms) # SKIP', 'ℹ fail 3', '', '\x1b[31m✖ failing tests:\x1b[39m', '', 'test at test/a.test.mjs:4:1',
    '\x1b[31m✖ top fails \x1b[90m(0.48ms)\x1b[39m', '  Error: x'].join('\n');
  assert.deepEqual(failingTests(spec), [{ name: 'top fails', file: 'test/a.test.mjs' }, { name: 'child fails', file: null }, { name: 'parent', file: null }]);
  const many = Array.from({ length: 60 }, (_, i) => `not ok ${i + 1} - test ${i}`).join('\n');
  assert.equal(failingTests(many).length, 20, 'the core\'s limit is 20 by default'); assert.equal(failingTests(many, 50).length, 50); assert.equal(failingTests(many, 10)[9].name, 'test 9');
  assert.deepEqual(failingTests(''), []);
  assert.equal(sameTest({ name: 'a', file: 'x' }, { name: 'a', file: null }), true); assert.equal(sameTest({ name: 'a', file: 'x' }, { name: 'a', file: 'y' }), false);
});

test('failing tests: the real node:test output of a run, with the TAP and the spec reporter', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-base-red-tap-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  writeFileSync(join(dir, 'a.test.mjs'), ["import test from 'node:test';", "test('passes', () => {});", "test('fails on main', () => { throw new Error('x'); });",
    "test('parent', async t => { await t.test('child', () => { throw new Error('y'); }); });", "test('later', { todo: true }, () => { throw new Error('z'); });", ''].join('\n'));
  const env = Object.fromEntries(Object.entries(process.env).filter(([key]) => !['NODE_OPTIONS', 'NODE_TEST_CONTEXT'].includes(key)));
  const run = reporter => spawnSync(process.execPath, ['--test', `--test-reporter=${reporter}`, 'a.test.mjs'], { cwd: dir, encoding: 'utf8', env });
  const tap = run('tap');
  assert.notEqual(tap.status, 0);
  assert.deepEqual(failingTests(tap.stdout).map(x => x.name), ['fails on main', 'child', 'parent']);
  assert.match(failingTests(tap.stdout)[0].file, /a\.test\.mjs$/);
  const spec = run('spec');
  assert.deepEqual(failingTests(spec.stdout).map(x => x.name), ['fails on main', 'child', 'parent']);
  assert.match(failingTests(spec.stdout)[0].file, /a\.test\.mjs$/, 'the failure summary names the file');
});

// Review R1 (P2): one test name in two files is two failures, also in real node --test output.
const tapFailure = (cwd, n, name, file) => `not ok ${n} - ${name}\n  ---\n  duration_ms: 1.5\n  type: 'test'\n  location: '${cwd}/${file}:1:1'\n  failureType: 'testCodeFailure'\n  ...\n`;
test('R1 failing tests: one test name failing in two files is two tests (real node --test TAP output)', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-base-red-two-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  for (const file of ['a.test.mjs', 'b.test.mjs']) writeFileSync(join(dir, file), "import test from 'node:test';\ntest('saves the value', () => { throw Error('bad'); });\n");
  const env = Object.fromEntries(Object.entries(process.env).filter(([key]) => !['NODE_OPTIONS', 'NODE_TEST_CONTEXT'].includes(key)));
  const run = spawnSync(process.execPath, ['--test', '--test-reporter=tap', 'a.test.mjs', 'b.test.mjs'], { cwd: dir, env, encoding: 'utf8' });
  assert.equal(run.status, 1);
  const found = failingTests(run.stdout);
  assert.deepEqual(found.map(x => x.name), ['saves the value', 'saves the value']);
  assert.deepEqual(found.map(x => x.file.split('/').pop()), ['a.test.mjs', 'b.test.mjs']);
});

test('R1 a new failure with the same name as a base failure, in another file, is the PR\'s own red: a repair', async t => {
  const w = await coreWorld(t);
  w.issue(17); await w.tick(); w.build(17); await w.tick(); w.review(17, 'PASS');
  const head = w.job(17, 'suite');
  w.say(17, 'suite', tapFailure(head.cwd, 1, 'saves the value', 'test/a.test.mjs') + tapFailure(head.cwd, 2, 'saves the value', 'test/b.test.mjs'));
  w.suite(17, 1); await w.tick();
  const base = w.job('base', 'suite');
  w.say('base', 'suite', tapFailure(base.cwd, 1, 'saves the value', 'test/a.test.mjs')); w.finish('base', 'suite', { code: 1 }); await w.tick();
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'the failure in test/b.test.mjs is not on the base');
  assert.match(repair.input, /Failing tests from this change: saves the value \(test\/b\.test\.mjs\)\./);
  assert.match(repair.input, /Also red on the base \([0-9a-f]{7}\), not from this change: saves the value \(test\/a\.test\.mjs\)\./);
  assert.equal(jobFile(w, 17).baseRed, undefined); assert.equal(mainRed(w).length, 0);
});

// Review R1: two machines see no open main-red issue at once and both post. A small GitHub fake, both reads first.
function issueFake() {
  const issues = [], comments = [];
  const gh = {
    call: async (method, path) => ({ status: 200, value: issues.map(x => ({ ...x })), next: null }),
    ok: async (method, path, value) => {
      let m;
      if (method === 'POST' && /\/issues$/.test(path)) { const row = { ...value, number: issues.length + 1, state: 'open' }; issues.push(row); return row; }
      if (method === 'POST' && (m = /\/issues\/(\d+)\/comments$/.exec(path))) { comments.push({ issue: Number(m[1]), body: value.body }); return { id: comments.length }; }
      if (method === 'PATCH' && (m = /\/issues\/(\d+)$/.exec(path))) { Object.assign(issues[Number(m[1]) - 1], value); return issues[Number(m[1]) - 1]; }
      throw Error(`unexpected ${method} ${path}`);
    } };
  return { issues, comments, gh };
}
test('R1 two machines at once: both post, the newer issue closes as a duplicate of the older one, and both use the older one', async () => {
  const { issues, comments, gh } = issueFake();
  const ctx = { repo: 'acme/widgets', settings: { mode: 'auto' }, state: { baseBranch: 'main' }, publicBody: x => x, gh, now: () => 0, warn: () => {} };
  const red = { what: 'ci', sha: 'a'.repeat(40), names: ['tests'] };
  const results = await Promise.all([fileMainRed(ctx, { pr: 100, issue: 17 }, red), fileMainRed(ctx, { pr: 101, issue: 18 }, red)]);
  assert.deepEqual(results.map(r => r.number), [1, 1]);
  assert.deepEqual(issues.map(i => [i.number, i.state]), [[1, 'open'], [2, 'closed']]);
  assert.equal(issues[1].state_reason, 'not_planned');
  assert.deepEqual(comments, [{ issue: 2, body: 'Duplicate of #1.' }]);
});

test('R1 a job whose own issue closed as a duplicate waits on the open issue with the same marker when the base moves', async () => {
  const { issues, gh } = issueFake();
  const fingerprint = baseRedFingerprint('ci', ['tests']), body = `x\n<!-- pdd:autopilot-core:base-red:${fingerprint} -->`;
  issues.push({ number: 1, state: 'open', body }, { number: 2, state: 'closed', body });
  gh.call = async (method, path) => /\/issues\/2$/.test(path) ? { status: 200, value: { number: 2, state: 'closed' } } : { status: 200, value: issues.map(x => ({ ...x })), next: null };
  let refreshed = 0, saved = 0;
  const ctx = { repo: 'acme/widgets', settings: { mode: 'auto' }, state: { baseBranch: 'main' }, publicBody: x => x, gh, now: () => 1000, quiet: 45 * MIN, warn: () => {}, ports: {},
    git: async args => args[0] === 'rev-parse' ? 'b'.repeat(40) : '', saveJob: () => { saved++; } };
  const job = { issue: 18, pr: 101, phase: 'pr', baseRed: { what: 'ci', sha: 'a'.repeat(40), tip: 'a'.repeat(40), names: ['tests'], fingerprint, since: 900, report: { number: 2, ref: 'acme/widgets#2', found: false } } };
  await baseRedWait(ctx, job, { refreshBase: async () => { refreshed++; } });
  assert.equal(refreshed, 0, 'the red is not fixed: issue #1 is open');
  assert.equal(job.baseRed.report.number, 1); assert.ok(saved > 0);
});

// One parser (group lead, Nov 12): the core's failingTests. Before its fix it differed from the module's copy on each
// of these real node --test outputs; the expected results come from the outputs themselves.
test('the core parser on real node --test output: TAP, spec and spec with color; nested, two files with one name, TODO, SKIP, a # in a name', t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-base-red-parsers-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  writeFileSync(join(dir, 'a.test.mjs'), ["import test from 'node:test';", "test('passes', () => {});", "test('saves the value', () => { throw new Error('a'); });",
    "test('parent', async t => { await t.test('child fails', () => { throw new Error('c'); }); await t.test('child ok', () => {}); });",
    "test('later', { todo: true }, () => { throw new Error('todo'); });", "test('skipped one', { skip: true }, () => {});", "test('name with # hash', () => { throw new Error('h'); });", ''].join('\n'));
  writeFileSync(join(dir, 'b.test.mjs'), "import test from 'node:test';\ntest('saves the value', () => { throw new Error('b'); });\n");
  const env = Object.fromEntries(Object.entries(process.env).filter(([key]) => !['NODE_OPTIONS', 'NODE_TEST_CONTEXT', 'NO_COLOR', 'FORCE_COLOR'].includes(key)));
  const run = (reporter, color) => spawnSync(process.execPath, ['--test', `--test-reporter=${reporter}`, 'a.test.mjs', 'b.test.mjs'], { cwd: dir, encoding: 'utf8', env: { ...env, ...(color ? { FORCE_COLOR: '1' } : { NO_COLOR: '1' }) } }).stdout;
  const short = list => list.map(f => `${f.name} [${f.file ? f.file.split('/').pop() : '-'}]`);
  const names = ['saves the value [a.test.mjs]', 'child fails [a.test.mjs]', 'parent [a.test.mjs]', 'name with # hash [a.test.mjs]', 'saves the value [b.test.mjs]'];
  assert.deepEqual(short(failingTests(run('tap'), 50)), names);
  const spec = ['saves the value [a.test.mjs]', 'child fails [a.test.mjs]', 'parent [-]', 'name with # hash [a.test.mjs]', 'saves the value [b.test.mjs]'];
  assert.deepEqual(short(failingTests(run('spec'), 50)), spec, 'the spec summary gives the files; parent has no "test at" line');
  assert.match(run('spec', true), /\x1b\[/, 'the colored run has color codes');
  assert.deepEqual(short(failingTests(run('spec', true), 50)), spec);
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

test('B4 main red again after its issue closed: a new main-red issue that names the old one, and the waiting PR waits on the new one', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.github.setRun(tipOf(w), { conclusion: 'failure' });
  w.issue(17); await w.tick();
  const { head } = w.build(17, { checks: false });
  w.github.setRun(head, { conclusion: 'failure' });
  await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  const [first] = mainRed(w);
  assert.equal(jobFile(w, 17).baseRed.report.number, first.number);
  assert.doesNotMatch(first.body, /Earlier:/);
  // A person closes the issue and the base moves, but main is still red the same way.
  w.github.close(first.number);
  const tip1 = w.baseCommit('other.txt', 'not the fix\n');
  w.github.setRun(tip1, { conclusion: 'failure' });
  await w.tick();
  const refreshed = jobFile(w, 17);
  assert.equal(refreshed.baseRed, undefined); assert.notEqual(refreshed.head, head);
  w.github.setRun(refreshed.head, { conclusion: 'failure' });
  await w.tick();
  w.suite(17, 0); await w.tick();
  const filed = mainRed(w);
  assert.equal(filed.length, 2, 'a closed match is a new red event: a new issue');
  const second = filed.find(issue => issue.number !== first.number);
  assert.equal(second.state, 'open'); assert.equal(second.title, first.title);
  assert.match(second.body, new RegExp(`^- Earlier: #${first.number} \\(closed; the same failure came back\\)$`, 'm'));
  assert.equal(jobFile(w, 17).baseRed.report.number, second.number, 'the PR waits on the new issue');
  assert.equal(w.started.filter(job => job.role === 'repair').length, 0);
  // The base moves again while the new issue is open: the PR still waits.
  w.github.setRun(w.baseCommit('third.txt', 'more\n'), { conclusion: 'success' });
  await w.tick();
  assert.equal(jobFile(w, 17).baseRed.report.number, second.number);
});

test('B4 the main-red issue is filed in auto and observe mode and with report off; only auto mode adds the opt-in label', async t => {
  const labelsOf = async (mode, report) => {
    const w = await coreWorld(t, { settings: { mode, report, label: 'pdd:autopilot' } });
    w.github.setRun(tipOf(w), { conclusion: 'failure' });
    w.issue(17, { labels: ['pdd:autopilot'] }); await w.tick();
    const { head } = w.build(17, { checks: false });
    w.github.setRun(head, { conclusion: 'failure' }); await w.tick();
    w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
    assert.equal(w.started.filter(job => job.role === 'repair').length, 0);
    return mainRed(w).map(issue => issue.labels);
  };
  assert.deepEqual(await labelsOf('auto', 'off'), [[MAIN_RED_LABEL, 'pdd:autopilot']]);
  assert.deepEqual(await labelsOf('observe', 'off'), [[MAIN_RED_LABEL]]);
  assert.deepEqual(await labelsOf('observe', 'draft'), [[MAIN_RED_LABEL]]);
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
  assert.match(repair.input, /The full test suite failed for head [0-9a-f]{7} \(exit 1\)\. Log: /, 'the first line lists no base test');
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

// Review R1 (Claude). Expected results from the review items and the group lead's fixes.
test('R1 several jobs turn base-red in one tick while the main-red label list lags: one issue (the machine record)', async t => {
  const w = await coreWorld(t);
  w.issue(17); w.issue(18); await w.tick();
  w.build(17); w.build(18); await w.tick();
  for (const n of [17, 18]) { w.review(n, 'PASS'); w.say(n, 'suite', 'not ok 1 - validation saves full output\n# fail 1'); w.suite(n, 1); }
  await w.tick();
  w.say('base', 'suite', 'not ok 1 - validation saves full output\n# fail 1'); w.finish('base', 'suite', { code: 1 });
  // The lag: an issue made in this tick is not in the label list yet.
  const fresh = new Set(), real = w.ports();
  const gh = async (args, options) => {
    const r = await real.gh(args, options), ep = args.find(x => /^repos\//.test(String(x))) ?? '', method = args.includes('--method') ? args[args.indexOf('--method') + 1] : 'GET';
    if (method === 'POST' && /\/issues$/.test(ep)) fresh.add(JSON.parse(r.stdout.split('\r\n\r\n')[1]).number);
    if (method === 'GET' && /\/issues\?state=all&labels=pdd%3Amain-red/.test(ep)) {
      const [head, body] = r.stdout.split('\r\n\r\n');
      return { ...r, stdout: `${head}\r\n\r\n${JSON.stringify(JSON.parse(body).filter(row => !fresh.has(row.number)))}` };
    }
    return r;
  };
  await w.tick({ gh });
  assert.equal(mainRed(w).length, 1, 'one main-red issue for one failure');
  assert.equal(jobFile(w, 17).baseRed.report.number, jobFile(w, 18).baseRed.report.number);
  const number = mainRed(w)[0].number;
  assert.deepEqual(JSON.parse(readFileSync(join(w.root, 'main-red', `${jobFile(w, 17).baseRed.fingerprint}.json`), 'utf8')).number, number);
});

test('R1 S2 a check fails while another check of the head still runs: no rerun ask yet; it is asked once the run completes', async t => {
  const w = await coreWorld(t);
  w.github.rerunnable = true;
  w.issue(17); await w.tick();
  const { head } = w.build(17, { checks: false });
  w.github.setRun(head, { name: 'install-smoke', conclusion: 'failure' });
  w.github.setRun(head, { name: 'tests', status: 'in_progress' });
  // GitHub refuses a job rerun while its workflow run still runs.
  const real = w.ports(), refused = [];
  const gh = async (args, options) => {
    const ep = args.find(x => /^repos\//.test(String(x))) ?? '';
    if (/\/actions\/jobs\/\d+\/rerun$/.test(ep) && (w.github.checks.get(head) ?? []).some(r => r.status !== 'completed')) {
      refused.push(ep); return { code: 1, stdout: 'HTTP/2.0 403 Forbidden\r\n\r\n{"message":"This workflow run is not completed"}', stderr: 'gh: HTTP 403\n' };
    }
    return real.gh(args, options);
  };
  await w.tick({ gh });
  assert.deepEqual(refused, [], 'no rerun ask while the other check runs');
  assert.equal(w.started.filter(j => j.role === 'repair').length, 0);
  w.github.setRun(head, { name: 'tests', conclusion: 'success' });
  await w.tick({ gh });
  assert.equal(w.github.reruns.length, 1, 'the one rerun is asked once the run completes');
  assert.equal(w.started.filter(j => j.role === 'repair').length, 0);
});

test('R1 S1 a base-red suite while a CI check still runs is no hold yet; that check then fails on its own: a repair', async t => {
  const w = await coreWorld(t);
  w.issue(17); await w.tick();
  const { head } = w.build(17, { checks: false });
  w.github.setRun(head, { name: 'lint', status: 'in_progress' });
  await w.tick();
  w.review(17, 'PASS'); w.say(17, 'suite', 'not ok 1 - X'); w.suite(17, 1); await w.tick();
  w.say('base', 'suite', 'not ok 1 - X'); w.finish('base', 'suite', { code: 1 }); await w.tick();
  assert.equal(jobFile(w, 17).baseRed, undefined, 'lint still runs: no hold yet');
  assert.equal(mainRed(w).length, 0);
  w.github.setRun(head, { name: 'lint', conclusion: 'failure' });   // the PR's own red: lint has no run on the base
  await w.tick(); await w.tick();
  assert.equal(w.started.filter(j => j.role === 'repair').length, 1, 'the PR\'s own lint red gets a repair');
  assert.match(w.job(17, 'repair').input, /CI check lint failed/);
});

test('R1 S3 the main-red issue closed with no base move: the red check runs once more at the same head; green merges', async t => {
  const w = await coreWorld(t);
  w.github.rerunnable = true;
  w.github.setRun(tipOf(w), { conclusion: 'failure' });
  w.issue(17); await w.tick();
  const { pr, head } = w.build(17, { checks: false });
  w.github.setRun(head, { conclusion: 'failure' }); await w.tick();
  w.github.setRun(head, { conclusion: 'failure' }); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  const [filed] = mainRed(w);
  assert.ok(jobFile(w, 17).baseRed);
  w.github.close(filed.number);                  // closed as flaky; the base does not move
  await w.tick();
  assert.equal(jobFile(w, 17).baseRed, undefined); assert.equal(jobFile(w, 17).head, head, 'the same head');
  await w.tick();
  assert.equal(w.github.reruns.length, 2, 'one more rerun at the same head');
  w.github.setRun(head, { conclusion: 'success' }); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.equal(w.started.filter(j => j.role === 'repair').length, 0);
});

test('R1 S4 a cancelled, stale or action_required run on the base tip is no result: wait, never base-red; a red one then is', async t => {
  for (const conclusion of ['cancelled', 'stale', 'action_required']) {
    const w = await coreWorld(t);
    w.github.setRun(tipOf(w), { conclusion });
    w.issue(17); await w.tick();
    const { head } = w.build(17, { checks: false });
    w.github.setRun(head, { conclusion: 'failure' }); await w.tick();
    w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
    assert.equal(jobFile(w, 17).baseRed, undefined, conclusion); assert.equal(mainRed(w).length, 0, conclusion);
    assert.equal(w.started.filter(j => j.role === 'repair').length, 0, `${conclusion}: wait, no repair`);
    w.github.setRun(tipOf(w), { conclusion: 'failure' }); await w.tick();
    assert.ok(jobFile(w, 17).baseRed, `${conclusion}, then red on the tip: base-red`);
  }
});

test('R1 P3 a merge in this tick moves the base: the next compare reads the base tip again', async () => {
  const tips = ['a'.repeat(40), 'b'.repeat(40)], reads = [];
  const ctx = { repo: 'acme/widgets', state: { baseBranch: 'main' }, counts: { merged: 0 }, quiet: 45 * MIN, now: () => 0, saveJob: () => {},
    git: async args => args[0] === 'rev-parse' ? tips[ctx.counts.merged] : '',
    gh: { call: async () => ({ status: 404 }), ok: async (method, path) => { reads.push(path); return /check-runs/.test(path) ? { check_runs: [{ name: 'ci', status: 'completed', conclusion: 'failure' }] } : { statuses: [] }; } } };
  const red = job => ciVsBase(ctx, job, { state: 'red', failed: ['ci'], failedRuns: [], running: [], sig: 's' });
  assert.equal((await red({ head: 'c'.repeat(40) })).baseRed.sha, tips[0]);
  ctx.counts.merged = 1;
  assert.equal((await red({ head: 'd'.repeat(40) })).baseRed.sha, tips[1]);
  assert.ok(reads.some(path => path.includes(tips[1])), 'the new tip\'s checks are read');
});

// The core's still-running suite line (#3227 fix 4) with this machine's base-suite record for the merge base.
test('a still-running suite line names only the tests that the base record does not have; all of them on the base: no line', async t => {
  const run = async (headLines, baseTests) => {
    const w = await coreWorld(t);
    w.issue(17); await w.tick(); w.build(17); await w.tick();
    const sha = tipOf(w);
    mkdirSync(join(w.root, 'base-suite'), { recursive: true });
    writeFileSync(join(w.root, 'base-suite', `${sha}.json`), JSON.stringify({ sha, state: 'fail', tests: baseTests, more: false, tail: '', text: '', at: w.now() }));
    const suite = w.job(17, 'suite');
    w.say(17, 'suite', headLines(suite.cwd));
    w.review(17, 'FAIL', ['P2 change-17.txt:1 the value is wrong']); await w.tick();
    return { w, repair: w.job(17, 'repair'), sha };
  };
  let { repair, sha } = await run(cwd => tapFailure(cwd, 1, 'X keeps the value', 'test/x.test.mjs') + tapFailure(cwd, 2, 'Y saves the file', 'test/y.test.mjs'),
    [{ name: 'X keeps the value', file: 'test/x.test.mjs' }]);
  assert.match(repair.input, new RegExp(`already shows failed tests: Y saves the file \\(y\\.test\\.mjs\\)\\. Also red on the base \\(${sha.slice(0, 7)}\\), not from this change: X keeps the value \\(x\\.test\\.mjs\\)\\.`));
  ({ repair } = await run(cwd => tapFailure(cwd, 1, 'X keeps the value', 'test/x.test.mjs'), [{ name: 'X keeps the value', file: 'test/x.test.mjs' }]));
  assert.match(repair.input, /the value is wrong/); assert.doesNotMatch(repair.input, /already shows failed tests/);
  ({ repair } = await run(cwd => tapFailure(cwd, 1, 'X keeps the value', 'test/x.test.mjs'), [{ name: 'X keeps the value', file: 'test/other.test.mjs' }]));
  assert.match(repair.input, /already shows failed tests: X keeps the value \(x\.test\.mjs\)\./, 'another file is another test');
});
