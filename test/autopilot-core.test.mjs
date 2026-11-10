import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';
import { autopilotEngine, coreSettings, readyIssues, coreStatus } from '../src/autopilot-core.mjs';
import { listReportDrafts, sendReportDraft } from '../src/autopilot-reports.mjs';

const MIN = 60 * 1000, HOUR = 60 * MIN;
const endComments = (w, n) => w.comments(n).filter(body => body.includes('<!-- pdd:autopilot-core:end:'));
const claimComments = (w, n) => w.comments(n).filter(body => body.includes('"labelEventId"'));
const jobFiles = w => existsSync(join(w.root, 'jobs')) ? readdirSync(join(w.root, 'jobs')).filter(name => name.endsWith('.json')) : [];
const worktrees = w => w.git(w.cwd, 'worktree', 'list', '--porcelain').split('\n').filter(line => line.startsWith('worktree ')).length;
const runtimeFailure = { outcome: 'failed', kind: 'runtime', component: 'pdd test', code: 'no-verdict', cause: 'pdd test returned no verdict after 3 tries', detail: 'Error: no verdict (interpreter busy)' };

test('settings: engine switch, defaults and bounded values', () => {
  assert.equal(autopilotEngine({}), 'full');
  assert.equal(autopilotEngine({ autopilot: { engine: 'core' } }), 'core');
  assert.equal(autopilotEngine({ autopilot: { engine: 'turbo' } }), 'full');
  assert.deepEqual(coreSettings({ autopilot: { mode: 'auto', engine: 'core' } }), {
    engine: 'core', mode: 'auto', trust: [], runs: 2, label: null, jobTimeoutMinutes: 120, report: 'draft', repairs: 2, testCommand: null });
  const custom = coreSettings({ autopilot: { mode: 'auto', engine: 'core', runs: 3, label: 'pdd:autopilot', jobTimeoutMinutes: 30, report: 'file', repairs: 0, testCommand: 'make check', trust: ['Dana'] } });
  assert.deepEqual(custom, { engine: 'core', mode: 'auto', trust: ['Dana'], runs: 3, label: 'pdd:autopilot', jobTimeoutMinutes: 30, report: 'file', repairs: 0, testCommand: 'make check' });
  const invalid = coreSettings({ autopilot: { mode: 'auto', engine: 'core', runs: 0, jobTimeoutMinutes: -1, report: 'loud', repairs: 1.5, label: '' } });
  assert.deepEqual([invalid.runs, invalid.jobTimeoutMinutes, invalid.report, invalid.repairs, invalid.label], [2, 120, 'draft', 2, null]);
  assert.equal(coreSettings({ autopilot: { engine: 'core' } }, { scripts: { test: 'node --test' } }).testCommand, 'npm test');
});

test('easy issue: claim, build, review, suite, CI and base check lead to one merge', async t => {
  const w = await coreWorld(t);
  w.issue(17, { title: 'Use value two', body: 'The value must be 2.' });
  await w.tick();
  const build = w.job(17, 'build');
  assert.ok(build, 'a build job starts');
  assert.deepEqual(w.labels(17), ['pdd:working']);
  const claim = JSON.parse(claimComments(w, 17)[0].match(/```json\n([\s\S]*?)\n```/)[1]);
  assert.equal(claim.coordinatorId, 'coord-a'); assert.equal(claim.machine, 'machine-a'); assert.equal(claim.lastSeen, '');
  assert.match(build.input, /Use value two/); assert.match(build.input, /The value must be 2\./);
  assert.match(build.input, /https:\/\/github\.com\/acme\/widgets\/issues\/17/);
  assert.match(build.input, /npm test/); assert.match(build.input, /ONE PR/); assert.match(build.input, /Runtime: not run/);
  assert.match(build.input, /never merge/i); assert.match(build.input, new RegExp(build.result.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')));
  assert.equal(build.cwd.includes('worktrees'), true);
  assert.equal(w.git(build.cwd, 'rev-parse', '--abbrev-ref', 'HEAD'), build.branch);

  const { pr, head } = w.build(17);
  await w.tick();
  const review = w.job(17, 'review'), suite = w.job(17, 'suite');
  assert.ok(review && suite, 'review and suite jobs start for the PR head');
  assert.equal(review.head, head); assert.equal(suite.head, head);
  assert.match(review.input, /did not write/); assert.match(review.input, new RegExp(`#${pr.number}`));
  assert.deepEqual(suite.args.slice(-5), ['suite', '--command', 'npm test', '--timeout', '120']);
  assert.equal(w.git(suite.cwd, 'rev-parse', 'HEAD'), head);
  assert.equal(w.github.merges.length, 0, 'no merge before all checks are green');

  w.review(17, 'PASS'); w.suite(17, 0);
  const result = await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  const merge = w.github.writes.find(row => row[0] === 'merge');
  assert.ok(merge.includes('--merge') && merge.includes(head));
  assert.ok(pr.comments.some(c => c.body.includes('Review: PASS') && c.body.includes(head)), 'the tick posts the verdict on the PR');
  assert.equal(w.github.issues.get(17).state, 'closed');
  assert.deepEqual(w.labels(17), []);
  assert.deepEqual(jobFiles(w), []);
  assert.equal(worktrees(w), 1, 'job and check worktrees are removed');
  assert.match(result.message, /1 merged/);
});

test('a job that dies ends with one comment, pdd:stuck and a free slot', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); w.issue(18);
  await w.tick();
  assert.ok(w.job(17, 'build')); assert.equal(w.job(18), undefined, 'one slot');
  w.kill(17, 'build');
  await w.tick();
  const ends = endComments(w, 17);
  assert.equal(ends.length, 1);
  assert.match(ends[0], /no result/i); assert.match(ends[0], /\.log/); assert.match(ends[0], /remove `?pdd:stuck`?/i);
  assert.deepEqual(w.labels(17).sort(), ['pdd:stuck']);
  assert.ok(w.job(18, 'build'), 'the next issue starts in the same tick');
  assert.equal(w.reports.calls.length, 0, 'a job failure files no report');
  await w.tick();
  assert.equal(endComments(w, 17).length, 1, 'no repeat');
});

test('a job that runs past its time limit is stopped and ended', async t => {
  const w = await coreWorld(t, { settings: { jobTimeoutMinutes: 60 } });
  w.issue(17);
  await w.tick();
  w.advance(59 * MIN); await w.tick();
  assert.deepEqual(w.stopped, []); assert.equal(endComments(w, 17).length, 0);
  w.advance(2 * MIN); await w.tick();
  assert.deepEqual(w.stopped, [w.job(17, 'build').id]);
  assert.match(endComments(w, 17)[0], /time limit|60 minutes/i);
  assert.ok(w.labels(17).includes('pdd:stuck'));
});

test('claim race between two machines: one machine starts, the loser starts nothing', async t => {
  const a = await coreWorld(t, { settings: { runs: 1 } });
  const b = await a.peer();
  a.issue(17);
  await Promise.all([a.tick(), b.tick()]);
  const started = [...a.started, ...b.started].filter(job => job.issue === 17);
  assert.equal(started.length, 1, 'exactly one build job');
  assert.equal(claimComments(a, 17).length, 1, 'the loser removes its claim comment');
  const winner = a.started.length ? 'coord-a' : 'coord-b';
  assert.ok(claimComments(a, 17)[0].includes(winner));
  await Promise.all([a.tick(), b.tick()]);
  assert.equal([...a.started, ...b.started].filter(job => job.issue === 17).length, 1, 'no second start later');
});

test('suite red leads to one repair on the same branch, then the merge', async t => {
  const w = await coreWorld(t);
  w.issue(17);
  await w.tick();
  const first = w.build(17);
  await w.tick();
  w.review(17, 'PASS'); w.suite(17, 1);
  await w.tick();
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'a repair job starts');
  assert.equal(repair.branch, w.job(17, 'build').branch); assert.equal(repair.cwd, w.job(17, 'build').cwd);
  assert.match(repair.input, /full test suite/i); assert.match(repair.input, /#100/);
  assert.equal(w.github.merges.length, 0);
  const second = w.build(17, { role: 'repair' });
  assert.notEqual(second.head, first.head);
  await w.tick();
  assert.equal(w.job(17, 'review').head, second.head);
  w.review(17, 'PASS'); w.suite(17, 0);
  await w.tick();
  assert.deepEqual(w.github.merges, [first.pr.number]);
});

test('review FAIL after the last repair ends the job; no merge', async t => {
  const w = await coreWorld(t, { settings: { repairs: 1 } });
  w.issue(17);
  await w.tick(); w.build(17); await w.tick();
  w.review(17, 'FAIL', ['Test does not cover the issue case']); w.suite(17, 0);
  await w.tick();
  const repair = w.job(17, 'repair');
  assert.match(repair.input, /Test does not cover the issue case/);
  w.build(17, { role: 'repair' }); await w.tick();
  w.review(17, 'FAIL', ['Still missing']); w.suite(17, 0);
  await w.tick();
  assert.equal(w.github.merges.length, 0);
  const end = endComments(w, 17);
  assert.equal(end.length, 1); assert.match(end[0], /review/i); assert.match(end[0], /Still missing/);
  assert.ok(w.labels(17).includes('pdd:stuck'));
  assert.equal(w.started.filter(job => job.role === 'repair').length, 1);
});

test('a 5-hour tick gap: expired claims end cleanly and intake continues', async t => {
  const w = await coreWorld(t);
  w.issue(17); w.issue(18);
  await w.tick();
  assert.ok(w.job(17) && w.job(18));
  w.kill(17, 'build');                       // the laptop slept; one job died, one is still alive
  w.advance(5 * HOUR);
  w.issue(19);
  await w.tick();
  for (const n of [17, 18]) {
    assert.equal(endComments(w, n).length, 1, `#${n} ends with one comment`);
    assert.match(endComments(w, n)[0], /claim expired|tick gap|no heartbeat/i);
    assert.ok(w.labels(n).includes('pdd:stuck')); assert.ok(!w.labels(n).includes('pdd:working'));
  }
  assert.ok(w.stopped.includes(w.job(18, 'build').id), 'the still-running job is stopped');
  assert.ok(w.job(19, 'build'), 'new intake starts');
});

test('Runtime no verdict files one report, links it, and the next issue starts', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, report: 'file' } });
  w.issue(17); w.issue(18);
  await w.tick();
  w.finish(17, 'build', { result: runtimeFailure });
  await w.tick();
  const reports = [...w.reports.issues.values()];
  assert.equal(reports.length, 1);
  assert.deepEqual(reports[0].labels, ['pdd:runtime']);
  assert.deepEqual(reports[0].assignees, ['agarwal-ishaan']);
  assert.match(reports[0].body, /<!-- pdd:autopilot-report:runtime\.pdd-test\.no-verdict\.0\.1 -->/);
  assert.match(reports[0].body, /0\.1\.27/); assert.match(reports[0].body, /no verdict/); assert.match(reports[0].body, /Seen on this machine: 1/);
  assert.doesNotMatch(reports[0].body, /change-17|widgets/, 'no user code or repository text');
  assert.match(endComments(w, 17)[0], /Blocked by promptdriven\/pdd#1/);
  assert.ok(w.job(18, 'build'), 'the next issue starts');
});

test('the same failure twice: one report and one "seen again" comment per machine per day', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, report: 'file' } });
  for (const n of [17, 18, 19]) w.issue(n);
  await w.tick(); w.finish(17, 'build', { result: runtimeFailure }); await w.tick();
  w.finish(18, 'build', { result: runtimeFailure }); await w.tick();
  w.finish(19, 'build', { result: runtimeFailure }); await w.tick();
  const reports = [...w.reports.issues.values()];
  assert.equal(reports.length, 1);
  assert.equal(reports[0].comments.filter(c => /seen again/i.test(c.body)).length, 1);
  for (const n of [17, 18, 19]) assert.match(endComments(w, n)[0], /Blocked by promptdriven\/pdd#1/);
  w.advance(25 * HOUR); w.issue(20);
  await w.tick(); w.finish(20, 'build', { result: runtimeFailure }); await w.tick();
  assert.equal(reports[0].comments.filter(c => /seen again/i.test(c.body)).length, 2, 'one more the next day');
  assert.equal(w.reports.issues.size, 1);
});

test('report draft writes nothing to GitHub until a person sends it', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick(); w.finish(17, 'build', { result: runtimeFailure }); await w.tick();
  assert.equal(w.reports.calls.length, 0);
  const drafts = listReportDrafts({ root: w.reportRoot });
  assert.equal(drafts.length, 1); assert.equal(drafts[0].fingerprint, 'runtime.pdd-test.no-verdict.0.1');
  assert.match(endComments(w, 17)[0], /pdd autopilot report/);
  const sent = await sendReportDraft({ root: w.reportRoot, fingerprint: drafts[0].fingerprint, machine: 'machine-a' }, { gh: w.gh, now: w.now });
  assert.equal(sent.exitCode, 0); assert.equal(w.reports.issues.size, 1);
  assert.equal(listReportDrafts({ root: w.reportRoot }).length, 0);
});

test('report off: no report, no draft, the END comment still names the cause', async t => {
  const w = await coreWorld(t, { settings: { report: 'off' } });
  w.issue(17);
  await w.tick(); w.finish(17, 'build', { result: runtimeFailure }); await w.tick();
  assert.equal(w.reports.calls.length, 0); assert.equal(listReportDrafts({ root: w.reportRoot }).length, 0);
  assert.match(endComments(w, 17)[0], /no verdict/);
});

test('ready rule: assignee, stuck, blocked by link or body line, trust, live claim and opt-in label', async t => {
  const w = await coreWorld(t);
  w.issue(20, { assignees: ['person'] });
  w.issue(21, { labels: ['pdd:stuck'] });
  w.issue(22); w.issue(23); w.github.link(22, 23);
  w.issue(24, { body: 'Blocked by #25 until the API lands.' }); w.issue(25);
  w.issue(26, { body: 'blocked by #27' }); w.issue(27); w.github.close(27);
  w.issue(28, { user: 'outsider' });
  w.issue(29); w.github.claim(29, { coordinatorId: 'coord-b', machine: 'machine-b' });
  w.issue(30, { labels: ['pdd:autopilot'] });
  const ready = await readyIssues({ state: w.state, settings: w.settings }, w.ports());
  assert.deepEqual(ready, [23, 25, 26, 30]);
  const optIn = await readyIssues({ state: w.state, settings: { ...w.settings, label: 'pdd:autopilot' } }, w.ports());
  assert.deepEqual(optIn, [30]);
  w.advance(5 * HOUR);
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), [23, 25, 26, 29, 30], 'an expired claim is ready');
});

test('a PR whose head moved, a red CI check and a Runtime FAIL line each go to repair, not merge', async t => {
  const w = await coreWorld(t, { settings: { repairs: 3 } });
  w.issue(17);
  await w.tick();
  const { pr, head } = w.build(17, { checks: 'failure' });
  await w.tick();
  assert.match(w.job(17, 'repair').input, /CI check ci/i, 'a red CI check needs no review or suite first');
  w.build(17, { role: 'repair', body: 'Fix.\n\nRuntime: FAIL (2 of 3 Stories fail)' }); await w.tick();
  assert.match(w.job(17, 'repair').input, /Runtime: FAIL/, 'a Runtime FAIL line needs no review or suite first');
  assert.equal(w.started.filter(job => job.role === 'repair').length, 2);
  assert.equal(w.github.merges.length, 0);
  pr.head = 'e'.repeat(40);                // someone else pushed
  w.finish(17, 'repair', { result: { outcome: 'pr', pr: pr.number, head } });
  await w.tick();
  assert.match(endComments(w, 17)[0], /head/i);
  assert.equal(w.github.merges.length, 0);
});

test('Runtime not run with a Runtime cause files a report and the PR says Runtime: not run (#N)', async t => {
  const w = await coreWorld(t, { settings: { report: 'file' } });
  w.issue(17);
  await w.tick();
  const { pr } = w.build(17, { body: 'Fix.\n\nRuntime: not run (no verdict)', runtime: { state: 'not-run', kind: 'runtime', component: 'pdd test', code: 'no-verdict', cause: 'no verdict' } });
  await w.tick();
  assert.equal(w.reports.issues.size, 1);
  assert.match(pr.body, /Runtime: not run \(promptdriven\/pdd#1\)/);
  w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number], 'not run does not block the merge');
});

test('a person who closes the issue or removes pdd:working stops the local job without GitHub writes', async t => {
  const w = await coreWorld(t);
  w.issue(17); w.issue(18);
  await w.tick();
  w.github.close(17); w.github.unlabel(18, 'pdd:working');
  const writes = w.github.writes.length;
  await w.tick();
  assert.deepEqual(w.stopped.sort(), [w.job(17).id, w.job(18).id].sort());
  assert.equal(endComments(w, 17).length + endComments(w, 18).length, 0);
  assert.equal(w.github.writes.slice(writes).filter(row => /\/issues\/1[78]/.test(row[1])).length, 0);
  assert.deepEqual(jobFiles(w).filter(name => /^1[78]\./.test(name)), []);
});

test('observe mode reads only; no agent ready holds intake without touching issues', async t => {
  const w = await coreWorld(t, { settings: { mode: 'observe' } });
  w.issue(17);
  const observed = await w.tick();
  assert.equal(w.started.length, 0); assert.equal(w.github.writes.length, 0); assert.match(observed.message, /observe/i);
  w.settings = { ...w.settings, mode: 'auto' };
  const held = await w.tick({ agentReady: async () => false });
  assert.equal(w.started.length, 0); assert.equal(w.github.writes.length, 0); assert.match(held.message, /agent/i);
});

test('three jobs in a row without a result pause intake on this machine for one hour', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  for (const n of [17, 18, 19, 20]) w.issue(n);
  for (const n of [17, 18, 19]) { await w.tick(); w.finish(n, 'build', { code: 1 }); }
  const paused = await w.tick();
  assert.equal(w.job(20), undefined);
  assert.match(paused.message, /paused/i);
  w.advance(61 * MIN);
  await w.tick();
  assert.ok(w.job(20, 'build'));
});

test('status shows jobs, slots and the last END causes', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.issue(17); w.issue(18);
  await w.tick(); w.kill(18, 'build'); await w.tick();
  const text = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now, reportRoot: w.reportRoot });
  assert.match(text, /engine core/i);
  assert.match(text, /1 of 2 slots/);
  assert.match(text, /#17 build running/);
  assert.match(text, /#18 ended .*no result/i);
});

test('doctor does not require Herdr when the engine is core', async () => {
  const { runAutopilotDoctor } = await import('../src/autopilot-doctor.mjs');
  const { doctorFixture } = await import('./helpers/doctor-fixture.mjs');
  const f = doctorFixture();
  f.paths.set('/project/pdd.json', JSON.stringify({ autopilot: { mode: 'auto', trust: [], engine: 'core' } }));
  const run = f.ports.run;
  f.ports.run = (file, args, options) => file === 'herdr' ? assert.fail('Herdr must not be called') : run(file, args, options);
  const result = await runAutopilotDoctor(f.input, f.ports);
  assert.match(result.message, /PASS herdr: Not needed: autopilot\.engine is core/);
  assert.doesNotMatch(result.message, /herdr-room/);
  const full = doctorFixture(), shown = await runAutopilotDoctor(full.input, full.ports);
  assert.match(shown.message, /PASS herdr: Herdr installation/); assert.match(shown.message, /herdr-room/);
});

test('launcher: engine core ticks without Herdr or a coordinator; status and report read local files', async t => {
  const { tickAutopilot, runAutopilotLauncher } = await import('../src/autopilot-launcher.mjs');
  const { createHash } = await import('node:crypto');
  const { spawnSync } = await import('node:child_process');
  const { mkdirSync } = await import('node:fs');
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], engine: 'core', testCommand: 'npm test' } }));
  w.issue(17);
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  mkdirSync(stateRoot, { recursive: true });
  writeFileSync(stateFile, JSON.stringify({ enabled: true, cwd, repo: 'acme/widgets', defaultBranch: 'main', coordinatorId: 'coord-a', machine: 'machine-a',
    agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: join(w.dir, 'pkg') }));
  const seen = [];
  const ports = { stateRoot, now: w.now, env: { HOME: process.env.HOME, PATH: process.env.PATH }, timer: async () => true, warn: () => {},
    run: async (command, args, options = {}) => {
      seen.push(command);
      if (command === 'gh') return w.gh(args, options);
      if (command !== 'git') assert.fail(`unexpected program ${command}`);
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true } };
  const result = await tickAutopilot(stateFile, ports);
  assert.match(result.message, /Autopilot core: 1 started/);
  assert.ok(w.job(17, 'build'));
  assert.ok(!seen.includes('herdr'));
  const saved = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.match(saved.core.message, /1 started/); assert.ok(Array.isArray(saved.cachedIssues));
  const status = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env }, ports);
  assert.equal(status.exitCode, 0, status.message);
  assert.match(status.message, /Autopilot enabled; timer active/); assert.match(status.message, /engine core/); assert.match(status.message, /#17 build running/);
  assert.ok(!seen.includes('herdr'));
  const report = await runAutopilotLauncher({ command: 'report', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env, issues: [] }, ports);
  assert.equal(report.message, 'No local Autopilot report drafts.');
});

test('at most 3 new reports per machine per day; a 4th new cause stays a local draft', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, report: 'file' } });
  for (const n of [17, 18, 19, 20]) w.issue(n);
  for (const [n, code] of [[17, 'a'], [18, 'b'], [19, 'c'], [20, 'd']]) {
    await w.tick(); w.finish(n, 'build', { result: { ...runtimeFailure, kind: 'pdd', component: 'pdd lint', code: `crash-${code}` } });
  }
  await w.tick();
  assert.equal(w.reports.issues.size, 3);
  assert.ok([...w.reports.issues.values()].every(issue => issue.labels[0] === 'pdd:autopilot-report' && !issue.assignees.length));
  assert.deepEqual(listReportDrafts({ root: w.reportRoot }).map(d => d.fingerprint), ['pdd.pdd-lint.crash-d.0.1']);
  assert.match(endComments(w, 20)[0], /local draft/);
});

test('a merge check that keeps failing on GitHub ends at its time limit with a PDD report', async t => {
  const w = await coreWorld(t, { settings: { report: 'draft', jobTimeoutMinutes: 30 } });
  w.issue(17);
  await w.tick(); const { pr } = w.build(17);
  const gh = w.gh;
  w.gh = async (args, options) => args.some(a => String(a).includes(`/pulls/${pr.number}`)) && !args.includes('PATCH') ? { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}', stderr: '' } : gh(args, options);
  await w.tick();
  assert.match(JSON.parse(readFileSync(join(w.root, 'jobs', '17.json'), 'utf8')).lastError, /502/);
  w.advance(31 * MIN); await w.tick();
  assert.match(endComments(w, 17)[0], /did not finish within 30 minutes.*502/);
  assert.equal(listReportDrafts({ root: w.reportRoot })[0].fingerprint, 'pdd.autopilot-core.merge-check-tool.0.1');
});

test('an agent other than Codex or Claude holds intake without a claim', async t => {
  const w = await coreWorld(t);
  w.state.agent = { kind: 'gemini', command: 'gemini' };
  w.issue(17);
  const result = await w.tick();
  assert.equal(w.started.length, 0); assert.equal(w.github.writes.length, 0); assert.match(result.message, /Codex or Claude/);
});

test('an ended job holds no slot after a restart, and END and merge remove its per-issue files', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); w.issue(18);
  await w.tick();
  const first = w.job(17, 'build');
  w.kill(17, 'build');                                   // the machine restarted; the job process is gone
  let down = true;
  const gh = w.gh;
  w.gh = async (args, options) => down && args.includes('POST') && args.some(a => /\/issues\/17\/comments$/.test(a))
    ? { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}', stderr: '' } : gh(args, options);
  await w.tick();                                        // END cannot post its comment yet
  assert.equal(JSON.parse(readFileSync(join(w.root, 'jobs', '17.json'), 'utf8')).phase, 'ending');
  assert.ok(w.job(18, 'build'), 'a job that is only finishing its END holds no slot');
  down = false;
  await w.tick();
  assert.equal(endComments(w, 17).length, 1);
  const left = name => readdirSync(join(w.root, name)).filter(file => /^17(?:[-.]|$)/.test(file));
  assert.deepEqual(left('jobs'), []); assert.deepEqual(left('worktrees'), []);
  assert.deepEqual(left('logs'), [first.log.split('/').at(-1)], 'only the log named in the END comment stays');
  // A merged job leaves nothing either, and its slot is free for the next issue.
  w.issue(19);
  w.build(18); await w.tick(); w.review(18, 'PASS'); w.suite(18, 0); await w.tick();
  assert.deepEqual(w.github.merges.length, 1);
  const merged = name => readdirSync(join(w.root, name)).filter(file => /^18(?:[-.]|$)/.test(file) && !file.endsWith('.log'));
  assert.deepEqual([...merged('jobs'), ...merged('worktrees'), ...merged('logs')], []);
  assert.ok(w.job(19, 'build'), 'the merged slot is free in the same tick');
});
