import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readdirSync, readFileSync, writeFileSync, rmSync, mkdirSync } from 'node:fs';
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

test('a job that dies releases its claim with no mark, closes its own PR and cools the issue down; the 3rd counted no-result in 7 days ends it', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); w.issue(18);
  await w.tick();
  assert.ok(w.job(17, 'build')); assert.equal(w.job(18), undefined, 'one slot');
  w.kill(17, 'build');
  await w.tick();
  assert.equal(endComments(w, 17).length, 0); assert.deepEqual(w.labels(17), []);
  assert.ok(w.job(18, 'build'), 'the next issue starts in the same tick');
  w.build(18); await w.tick(); w.review(18, 'PASS'); w.suite(18, 0); await w.tick();
  assert.equal(w.started.filter(job => job.issue === 17).length, 1, '#17 cools down for 24 hours');
  for (let round = 2; round <= 3; round++) {
    w.advance(25 * HOUR); await w.tick();
    assert.equal(w.started.filter(job => job.issue === 17).length, round, `#17 runs again after the cooldown (${round})`);
    w.kill(17, 'build'); await w.tick();
    if (round === 2) { w.issue(19); await w.tick(); w.build(19); await w.tick(); }   // a result between the no-results
  }
  const ends = endComments(w, 17);
  assert.equal(ends.length, 1, 'the 3rd counted no-result in 7 days is a normal END');
  assert.match(ends[0], /no result/i); assert.match(ends[0], /\.log/); assert.match(ends[0], /remove `?pdd:stuck`?/i);
  assert.deepEqual(w.labels(17).sort(), ['pdd:stuck']);
  assert.equal(w.reports.calls.length, 0, 'a job failure files no report');
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

test('status shows jobs, slots and the last END causes', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.issue(17); w.issue(18);
  await w.tick(); w.kill(18, 'build'); await w.tick();
  const text = coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now, reportRoot: w.reportRoot });
  assert.match(text, /engine core/i);
  assert.match(text, /1 of 2 slots/);
  assert.match(text, /#17 build running/);
  assert.match(text, /#18 released .*no result/i);
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
  w.advance(31 * MIN); await w.tick(); await w.tick(); await w.tick();
  assert.match(endComments(w, 17)[0], /did not finish within 30 minutes.*502/, 'after 3 tries to read the PR, the END goes on');
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
  w.finish(17, 'build', { result: { outcome: 'failed', kind: 'job', code: 'unclear', cause: 'the issue is unclear' } });
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

test('a Runtime END in the report repository is blocked natively, returns when the report closes, and a repeat gets pdd:stuck', async t => {
  const w = await coreWorld(t, { repository: 'promptdriven/pdd', settings: { runs: 1, report: 'file' } });
  w.issue(17); w.issue(18);
  await w.tick(); w.finish(17, 'build', { result: runtimeFailure }); await w.tick();
  const report = [...w.github.issues.values()].find(issue => issue.labels.includes('pdd:runtime'));
  assert.ok(report, 'the report is filed in the same repository');
  assert.deepEqual(w.github.issues.get(17).blockedBy, [report.number], 'native blocked-by dependency');
  assert.ok(!w.labels(17).includes('pdd:stuck')); assert.ok(!w.labels(17).includes('pdd:working'));
  assert.match(endComments(w, 17)[0], new RegExp(`Blocked by #${report.number}`));
  assert.ok(w.job(18, 'build'), 'the next issue starts');
  w.kill(18, 'build'); await w.tick();
  assert.equal(w.started.filter(j => j.issue === 17).length, 1, '#17 waits while the report is open');
  w.github.close(report.number);
  await w.tick();
  assert.equal(w.started.filter(j => j.issue === 17).length, 2, '#17 is ready again when the report closes');
  w.finish(17, 'build', { result: runtimeFailure }); await w.tick();
  assert.ok(w.labels(17).includes('pdd:stuck'), 'the same cause after its report closed is a loop: pdd:stuck');
  assert.equal([...w.github.issues.values()].filter(issue => issue.labels.includes('pdd:runtime')).length, 1, 'a report closed less than 14 days ago is reused');
  assert.match(endComments(w, 17).at(-1), /came back after .*closed/i);
});

test('a Runtime END in another repository falls back to the hidden marker that the ready rule reads', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, report: 'file' } });
  w.issue(17); w.issue(18);
  await w.tick(); w.finish(17, 'build', { result: runtimeFailure }); await w.tick();
  assert.deepEqual(w.github.issues.get(17).blockedBy, [], 'the cross-repository native link was refused');
  assert.match(endComments(w, 17)[0], /<!-- pdd:core-blocked-by:promptdriven\/pdd#1:runtime\.pdd-test\.no-verdict\.0\.1 -->/);
  assert.ok(!w.labels(17).includes('pdd:stuck'));
  assert.ok(w.job(18, 'build'));
  w.finish(18, 'build', { result: { outcome: 'failed', kind: 'job', code: 'unclear', cause: 'the issue is unclear' } }); await w.tick();
  assert.equal(w.started.filter(j => j.issue === 17).length, 1, '#17 waits while promptdriven/pdd#1 is open');
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), []);
  w.reports.close(1);
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), [17]);
});

test('Runtime END without a filed report (draft) and job causes keep pdd:stuck; reports are never core work', async t => {
  const w = await coreWorld(t, { repository: 'promptdriven/pdd', settings: { runs: 1 } });
  w.issue(17);
  await w.tick(); w.finish(17, 'build', { result: runtimeFailure }); await w.tick();
  assert.ok(w.labels(17).includes('pdd:stuck'), 'nothing to wait on: a person decides');
  w.issue(30, { labels: ['pdd:autopilot-report'] }); w.issue(31, { labels: ['pdd:runtime'] });
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), [], 'report issues wait for the self-fix lane');
});

test('zero CI checks count as "CI: none" 10 minutes after the PR; pending checks still wait', async t => {
  const w = await coreWorld(t);
  w.issue(17); w.issue(18);
  await w.tick();
  const none = w.build(17, { checks: null }), pending = w.build(18, { checks: null });
  w.github.setChecks(pending.head, null, 'in_progress');
  await w.tick();
  for (const n of [17, 18]) { w.review(n, 'PASS'); w.suite(n, 0); }
  await w.tick();
  assert.equal(w.github.merges.length, 0, 'before 10 minutes a PR with no checks waits');
  w.advance(11 * MIN); await w.tick();
  assert.deepEqual(w.github.merges, [none.pr.number]);
  assert.ok(none.pr.comments.some(c => /CI: none/.test(c.body) && c.body.includes(none.head)), 'the merge comment says CI: none');
  assert.ok(!pending.pr.comments.some(c => /CI: none/.test(c.body)));
});

test('END with an open PR leaves it open as a draft and comments the cause on the PR', async t => {
  const w = await coreWorld(t, { settings: { repairs: 0 } });
  w.issue(17);
  await w.tick(); const { pr } = w.build(17); await w.tick();
  w.review(17, 'FAIL', ['Missing test']); w.suite(17, 0); await w.tick();
  assert.equal(pr.state, 'open'); assert.equal(pr.draft, true);
  const comments = pr.comments.filter(c => c.body.includes('<!-- pdd:autopilot-core:end-pr:'));
  assert.equal(comments.length, 1); assert.match(comments[0].body, /Missing test/);
  assert.ok(w.labels(17).includes('pdd:stuck'), 'a job cause keeps pdd:stuck');
});

// ---- Review 1 regressions (each failed on 08fcc5517) ----------------------------------------------------
test('R1 a Runtime FAIL line in a list, in bold or in any case blocks the merge, and so does a result state FAIL', async t => {
  for (const body of ['Fixes #17\n\n- Runtime: FAIL (2 of 3 Stories fail)', 'Fixes #17\n\n**Runtime:** FAIL', 'Fixes #17\n\n> runtime: **fail** (lint)', 'Fixes #17\n\n* `Runtime: Fail`']) {
    const w = await coreWorld(t);
    w.issue(17); await w.tick();
    w.build(17, { body }); await w.tick();
    assert.equal(w.github.merges.length, 0, body);
    assert.match(w.job(17, 'repair').input, /Runtime: FAIL/i, body);
  }
  const w = await coreWorld(t);
  w.issue(17); await w.tick();
  w.build(17, { body: 'Fixes #17', runtime: { state: 'FAIL', kind: 'runtime', component: 'pdd test', code: 'x', cause: 'y' } }); await w.tick();
  assert.equal(w.github.merges.length, 0); assert.ok(w.job(17, 'repair'));
  w.build(17, { role: 'repair', body: 'Fixes #17\n\nRuntime: PASS' }); await w.tick();
  assert.match(w.job(17, 'review').input, /Runtime FAIL line.*FAIL/i, 'the reviewer prompt says a Runtime FAIL line is a FAIL verdict');
});

test('R2 takeover race: a stale expired-claim read does not take over a fresh claim, and a lost claim never merges', async t => {
  const { createDependencyReadPorts } = await import('../src/issue-dependencies-github.mjs');
  const a = await coreWorld(t, { settings: { runs: 1 } });
  const b = await a.peer();
  a.issue(17);
  a.github.claim(17, { coordinatorId: 'coord-c', machine: 'machine-c' });
  a.advance(5 * HOUR);
  const stale = JSON.parse((await createDependencyReadPorts({ cwd: '' }, { execFile: (f, args, o) => a.gh(args, o), now: a.now })
    .owners.read({ repository: 'acme/widgets', issues: ['https://github.com/acme/widgets/issues/17'] })).json).claims;
  assert.equal(stale[0].expired, true);
  await a.tick();
  assert.ok(a.job(17, 'build'), 'A took over the expired claim');
  await b.tick({ owners: async () => stale });
  assert.equal(b.job(17), undefined, 'B sees that the winning label event changed and does not take over');
  // Force the worst case: B wins a new label era after A started. A must stop at its next heartbeat and never merge.
  a.github.unlabel(17, 'pdd:working'); b.github.claim(17, { coordinatorId: 'coord-b', machine: 'machine-b' });
  const { pr } = a.build(17);
  a.advance(30 * MIN); await a.tick();
  assert.ok(a.stopped.includes(a.job(17, 'build').id) || !existsSync(join(a.root, 'jobs', '17.json')), 'A stopped its job');
  assert.equal(existsSync(join(a.root, 'jobs', '17.json')), false);
  assert.equal(a.github.merges.length, 0);
  assert.equal(pr.draft, true, 'A leaves its own PR as a draft');
  assert.ok(!a.labels(17).includes('pdd:stuck'), 'no labels change on the issue the other machine owns');
});

test('R2b a claim lost after the checks passed is read right before the merge: no merge', async t => {
  const w = await coreWorld(t);
  w.issue(17); await w.tick();
  const { pr } = w.build(17); await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0);
  let lose = false;
  const result = await w.tick({ heartbeat: async () => ({ state: 'refreshed' }), owners: async numbers => {
    if (!lose) { lose = true; return [{ issue: 'https://github.com/acme/widgets/issues/17', active: true, coordinatorId: 'coord-a', machine: 'machine-a', commentId: JSON.parse(readFileSync(join(w.root, 'jobs', '17.json'), 'utf8')).claim.commentId }]; }
    return [{ issue: 'https://github.com/acme/widgets/issues/17', active: true, coordinatorId: 'coord-b', machine: 'machine-b', commentId: '1', labelEventId: '2' }];
  } });
  assert.equal(w.github.merges.length, 0, result.message);
  assert.equal(pr.state, 'open');
});

test('R3 a locked or unremovable leftover worktree fails only that issue; intake goes on', async t => {
  const { mkdirSync } = await import('node:fs');
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.issue(17); w.issue(18); w.issue(19);
  mkdirSync(join(w.root, 'worktrees'), { recursive: true });
  const path = join(w.root, 'worktrees', '17');
  w.git(w.cwd, 'worktree', 'add', '-q', '--detach', path, 'HEAD');
  w.git(w.cwd, 'worktree', 'lock', '--reason', 'initializing', path);
  await w.tick();
  assert.ok(w.job(17, 'build'), 'a locked leftover worktree of ours is removed and #17 starts');
  const v = await coreWorld(t, { settings: { runs: 2 } });
  v.issue(17); v.issue(18); v.issue(19);
  mkdirSync(join(v.root, 'worktrees', '17'), { recursive: true });
  const nativeFs = await import('node:fs');
  const fs = { ...nativeFs, rmSync: (p, o) => { if (String(p).endsWith('/worktrees/17')) throw Object.assign(Error('EACCES'), { code: 'EACCES' }); return nativeFs.rmSync(p, o); } };
  const r = await v.tick({ fs });
  assert.equal(v.job(17), undefined); assert.ok(v.job(18, 'build') && v.job(19, 'build'), r.message);
});

test('R4 a failed cleanup never keeps the job file, and END never runs on a merged issue', async t => {
  const nativeFs = await import('node:fs');
  const w = await coreWorld(t, { settings: { jobTimeoutMinutes: 30 } });
  let broken = false;
  const fs = { ...nativeFs, rmSync: (p, o) => { if (broken && String(p).includes('/worktrees/')) throw Object.assign(Error('EACCES'), { code: 'EACCES' }); return nativeFs.rmSync(p, o); } };
  const realGit = w.ports().git;
  const git = async (args, o) => broken && args[0] === 'worktree' && args[1] === 'remove' ? { code: 128, stdout: '', stderr: 'fatal: Permission denied' } : realGit(args, o);
  w.issue(17); await w.tick({ fs, git });
  const { pr } = w.build(17); await w.tick({ fs, git });
  w.review(17, 'PASS'); w.suite(17, 0);
  broken = true;
  const merged = await w.tick({ fs, git });
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.equal(nativeFs.existsSync(join(w.root, 'jobs', '17.json')), false, merged.message);
  w.advance(31 * MIN);
  const later = await w.tick({ fs, git });
  assert.match(later.message, /0 merged, 0 ended/);
  assert.equal(endComments(w, 17).length, 0); assert.ok(!w.labels(17).includes('pdd:stuck'));
  // A job whose PR merged while it was already ending finishes as merged, with no END comment.
  const v = await coreWorld(t);
  v.issue(17); await v.tick(); const second = v.build(17); await v.tick();
  const job = JSON.parse(readFileSync(join(v.root, 'jobs', '17.json'), 'utf8'));
  second.pr.state = 'closed'; second.pr.merged = true;
  nativeFs.writeFileSync(join(v.root, 'jobs', '17.json'), JSON.stringify({ ...job, phase: 'ending', end: { cause: { kind: 'job', code: 'timeout', text: 'x' }, at: v.now() } }));
  await v.tick();
  assert.equal(endComments(v, 17).length, 0); assert.equal(v.github.issues.get(17).state, 'closed');
});

test('R5 should-fix: a cleared tool error, a dead suite, a restart, a partial claim and a stuck END', async t => {
  // S1: one transient tool error, then pending CI to the deadline, is a job cause with no PDD report.
  let w = await coreWorld(t, { settings: { report: 'draft', jobTimeoutMinutes: 30 } });
  w.issue(17); await w.tick();
  const built = w.build(17, { checks: null }); w.github.setChecks(built.head, null, 'in_progress');
  let fail = true; const gh = w.gh;
  w.gh = async (args, o) => fail && args.some(x => String(x).includes(`/pulls/${built.pr.number}`)) ? (fail = false, { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}', stderr: '' }) : gh(args, o);
  await w.tick(); await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  w.advance(31 * MIN); await w.tick();
  assert.match(endComments(w, 17)[0], /Cause: job \/ checks-timeout/); assert.equal(listReportDrafts({ root: w.reportRoot }).length, 0);
  // S2: a dead suite run starts again and uses no repair.
  w = await coreWorld(t);
  w.issue(17); await w.tick(); w.build(17); await w.tick();
  w.review(17, 'PASS'); w.kill(17, 'suite'); await w.tick();
  assert.equal(w.job(17, 'repair'), undefined);
  assert.equal(w.started.filter(job => job.role === 'suite').length, 2);
  // S3 (now the breaker rule): 3 no-result ends in a row, also from a restart, open the breaker; no new job starts.
  w = await coreWorld(t, { settings: { runs: 3 } });
  for (const n of [17, 18, 19, 20]) w.issue(n);
  await w.tick(); for (const n of [17, 18, 19]) w.kill(n, 'build');
  const restarted = await w.tick();
  assert.match(restarted.message, /paused/); assert.equal(w.job(20), undefined);
  assert.deepEqual([17, 18, 19].map(n => w.labels(n)), [[], [], []], 'the three issues are only released');
  // S4: a claim that fails after the label add leaves no bare pdd:working.
  w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  const gh2 = w.gh;
  w.gh = async (args, o) => args.includes('POST') && args.some(x => /\/issues\/17\/comments$/.test(x)) ? { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}', stderr: '' } : gh2(args, o);
  await w.tick();
  assert.equal(w.job(17), undefined); assert.deepEqual(w.labels(17), []);
  // S5: an END that keeps failing is dropped after 6 tries with one alert.
  w = await coreWorld(t);
  w.issue(17); await w.tick(); w.finish(17, 'build', { result: { outcome: 'failed', kind: 'job', code: 'unclear', cause: 'the issue is unclear' } });
  const gh3 = w.gh, alerts = [];
  w.gh = async (args, o) => args.includes('POST') && args.some(x => /\/issues\/17\/comments$/.test(x)) ? { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}', stderr: '' } : gh3(args, o);
  for (let i = 0; i < 8; i++) { await w.tick({ alert: async input => alerts.push(input) }); w.advance(30 * MIN); }
  assert.equal(existsSync(join(w.root, 'jobs', '17.json')), false);
  assert.equal(alerts.length, 1); assert.equal(alerts[0].issue, 17); assert.match(alerts[0].text, /could not finish/);
  assert.match(readFileSync(join(w.root, 'history.jsonl'), 'utf8'), /"outcome":"abandoned"/);
});

// ---- Review 2 regressions (each failed on cdb09e95a) ----------------------------------------------------
test('R6 the Runtime gate is an allowlist: only PASS or "not run" lines and states merge', async t => {
  const blocked = ['Runtime: FAILED (2 of 3 Stories fail)', '## Runtime: FAIL (lint refused)', '| Runtime | FAIL |', 'Runtime: ❌ FAIL',
    'Tests: pass; Runtime: FAIL', 'Runtime: see the log', 'Runtime: PASS\nRuntime: not run (busy)'];
  for (const line of blocked) {
    const w = await coreWorld(t);
    w.issue(17); await w.tick();
    w.build(17, { body: `Fixes #17\n\n${line}` }); await w.tick();
    assert.equal(w.github.merges.length, 0, line);
    assert.ok(w.job(17, 'repair'), `${line}: a red Runtime line goes to repair`);
    assert.match(w.job(17, 'repair').input, /Runtime/, line);
  }
  for (const state of ['failed', 'error', 'unknown']) {
    const w = await coreWorld(t);
    w.issue(17); await w.tick();
    w.build(17, { runtime: { state, kind: 'runtime', component: 'pdd test', code: 'x', cause: 'y' } }); await w.tick();
    assert.equal(w.github.merges.length, 0, state); assert.ok(w.job(17, 'repair'), state);
  }
  const missing = await coreWorld(t);
  missing.issue(17); await missing.tick();
  missing.build(17, { body: 'Fixes #17' }); await missing.tick();
  assert.match(missing.job(17, 'repair').input, /no Runtime line/i, 'no Runtime line and no "no prompt changed" result is red');
  for (const [body, result] of [['Fixes #17\n\n- **Runtime:** ✅ PASS', {}], ['Fixes #17\n\nThe runtime check flow is unchanged.', { promptChanged: false }],
    ['Fixes #17\n\n> Runtime: not run (no prompt changed)', {}]]) {
    const w = await coreWorld(t);
    w.issue(17); await w.tick();
    const { pr } = w.build(17, { body, result }); await w.tick();
    w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
    assert.deepEqual(w.github.merges, [pr.number], body);
  }
});

test('R7 a job file with no agent record, or one whose advance keeps failing, ends and frees its slot and claim', async t => {
  const { readAgentJob } = await import('../src/agent-job.mjs');
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); w.issue(18);
  await w.tick();
  const job = JSON.parse(readFileSync(join(w.root, 'jobs', '17.json'), 'utf8'));
  delete job.agent; writeFileSync(join(w.root, 'jobs', '17.json'), JSON.stringify(job));
  await w.tick({ jobs: { ...w.jobs, read: spec => readAgentJob(spec) } });
  assert.equal(endComments(w, 17).length, 0); assert.deepEqual(w.labels(17), [], 'a job with no agent record releases its claim');
  assert.match(readFileSync(join(w.root, 'history.jsonl'), 'utf8'), /no agent record/);
  assert.ok(w.job(18, 'build'), 'the slot is free');
  // Advance throws on every tick: at the deadline plus 2 ticks the job ends; after the deadline it gets no heartbeat.
  const v = await coreWorld(t, { settings: { runs: 1, jobTimeoutMinutes: 60 } });
  v.issue(17); v.issue(18);
  await v.tick();
  const broken = { ...v.jobs, read: () => { throw Error('broken job record'); } };
  const beats = [];
  const heartbeat = async job => { if (job.issue === 17) beats.push(v.now()); return { state: 'refreshed' }; };
  for (let i = 0; i < 6; i++) { v.advance(20 * MIN); await v.tick({ jobs: broken, heartbeat }); }
  assert.equal(existsSync(join(v.root, 'jobs', '17.json')), false, 'ended within the deadline plus 2 ticks');
  assert.ok(!v.labels(17).includes('pdd:working'), 'its claim is released');
  assert.ok(beats.every(at => at < Date.parse('2026-11-10T12:00:00Z') + 60 * MIN), 'no heartbeat after the deadline');
  assert.ok(v.job(18, 'build'));
});

test('R8 a non-zero test exit is a red suite and gets a repair; only a runner failure is a broken suite', async t => {
  const w = await coreWorld(t);
  w.issue(17); await w.tick(); w.build(17); await w.tick();
  w.review(17, 'PASS'); w.suite(17, 2); await w.tick();
  assert.ok(w.job(17, 'repair'), 'exit 2 (make, pytest) is a red suite');
  const v = await coreWorld(t, { settings: { report: 'draft' } });
  v.issue(17); await v.tick(); v.build(17); await v.tick();
  v.review(17, 'PASS');
  for (let i = 0; i < 3; i++) { writeFileSync(v.job(17, 'suite').log, 'Test suite execution timeout after 120 minutes.\n'); v.suite(17, 124); await v.tick(); }
  assert.equal(v.job(17, 'repair'), undefined, 'a runner timeout never uses a repair');
  assert.match(endComments(v, 17)[0], /Cause: pdd \/ suite-broken/);
});

test('R9 a worktree that Git still lists but whose folder is gone does not block the review checkout', async t => {
  const w = await coreWorld(t, { settings: { jobTimeoutMinutes: 30 } });
  w.issue(17); await w.tick();
  const path = join(w.root, 'worktrees', '17-review');
  w.git(w.cwd, 'worktree', 'add', '-q', '--detach', path, 'HEAD');
  w.git(w.cwd, 'worktree', 'lock', path);
  rmSync(path, { recursive: true, force: true });
  w.build(17); await w.tick();
  assert.ok(w.job(17, 'review'), 'the review starts');
});

test('R10 a merge whose finish failed is finished as merged on the next tick, not as a person stop', async t => {
  const w = await coreWorld(t);
  w.issue(17); await w.tick();
  const { pr } = w.build(17); await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0);
  let fail = false; const gh = w.gh;
  w.gh = async (args, o) => {
    if (fail && args.some(x => /\/issues\/17$/.test(String(x)))) return { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}', stderr: '' };
    const r = await gh(args, o); if (args[0] === 'pr' && args[1] === 'merge' && r.code === 0) fail = true; return r;
  };
  await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  fail = false; w.github.close(17);
  await w.tick();
  const history = readFileSync(join(w.root, 'history.jsonl'), 'utf8');
  assert.match(history, /"outcome":"merged"/); assert.doesNotMatch(history, /"outcome":"stopped"/);
  assert.ok(!w.labels(17).includes('pdd:working'));
  assert.match(w.job(17, 'build').input, /do not assign/i, 'the agent is told not to assign the issue or change its labels');
});

test('R11 a loser claim comment that stays is removed by the winner, which then merges', async t => {
  const a = await coreWorld(t, { settings: { runs: 1 } });
  const b = await a.peer();
  a.issue(17);
  const noDelete = gh => async (args, o) => args.includes('DELETE') && args.some(x => /issues\/comments\/\d+$/.test(String(x))) && !noDelete.allow
    ? { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}', stderr: '' } : gh(args, o);
  const ghA = a.gh, ghB = b.gh;
  a.gh = noDelete(ghA); b.gh = noDelete(ghB);
  await Promise.all([a.tick(), b.tick()]);
  const win = a.job(17, 'build') ? a : b;
  assert.ok(win.job(17, 'build') && !(win === a ? b : a).job(17));
  assert.equal(a.comments(17).filter(c => c.includes('"labelEventId"')).length, 2, 'the loser comment stayed');
  noDelete.allow = true;
  const { pr } = win.build(17); await win.tick();
  win.review(17, 'PASS'); win.suite(17, 0);
  const r = await win.tick();
  assert.deepEqual(a.github.merges, [pr.number], r.message);
  assert.equal(a.comments(17).filter(c => c.includes('"labelEventId"')).length, 1);
});

test('R12 every text the core posts on GitHub is redacted and capped', async t => {
  const token = 'ghp_' + 'A1b2C3d4E5f6G7h8I9j0K1l2M3n4O5p6Q7r8';
  const w = await coreWorld(t, { settings: { repairs: 0 } });
  w.issue(17); w.issue(18);
  await w.tick();
  w.build(17); await w.tick();
  w.review(17, 'FAIL', [`Remove the token ${token} from config.js`, 'x'.repeat(5000)]); w.suite(17, 0); await w.tick();
  w.finish(18, 'build', { result: { outcome: 'failed', kind: 'job', code: 'x', cause: `push failed for https://user:${token}@github.com/acme/widgets.git` } }); await w.tick();
  const posted = [...w.github.issues.values()].flatMap(issue => issue.comments.map(c => c.body))
    .concat([...w.github.prs.values()].flatMap(pr => pr.comments.map(c => c.body)));
  assert.ok(posted.length >= 3);
  for (const body of posted) { assert.ok(!body.includes(token), body.slice(0, 200)); assert.ok(body.length <= 20000, `${body.length}`); }
});

test('R13 base drift: a PR behind the base is refreshed natively without a repair; a conflict starts a repair', async t => {
  const w = await coreWorld(t);
  w.issue(17); await w.tick();
  const first = w.build(17); await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0);
  w.baseCommit('other.txt', 'base moved\n');
  await w.tick();
  assert.equal(w.github.merges.length, 0, 'no merge of a head that lacks the base tip');
  const job = JSON.parse(readFileSync(join(w.root, 'jobs', '17.json'), 'utf8'));
  assert.notEqual(job.head, first.head); assert.equal(job.repairs, 0, 'a refresh is not a repair');
  await w.tick();
  assert.equal(first.pr.head, job.head, 'the refreshed head is pushed to the PR branch');
  assert.equal(w.job(17, 'review').head, job.head, 'the review runs again for the new head');
  assert.equal(w.job(17, 'suite').head, job.head, 'the suite runs again for the new head');
  w.github.setChecks(job.head); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  assert.deepEqual(w.github.merges, [first.pr.number]);
  const v = await coreWorld(t);
  v.issue(17); await v.tick();
  v.build(17); await v.tick();
  v.review(17, 'PASS'); v.suite(17, 0);
  v.baseCommit('change-17.txt', 'conflicting base text\n');
  await v.tick();
  assert.ok(v.job(17, 'repair'), 'a merge conflict with the base starts a repair job');
  assert.match(v.job(17, 'repair').input, /conflict/i);
});

test('R14 a machine engine and label saved by start win over pdd.json; status names the source', async t => {
  const { tickAutopilot, runAutopilotLauncher } = await import('../src/autopilot-launcher.mjs');
  const { createHash } = await import('node:crypto');
  const { spawnSync } = await import('node:child_process');
  const { mkdirSync } = await import('node:fs');
  const w = await coreWorld(t);
  writeFileSync(join(w.cwd, 'pdd.json'), JSON.stringify({ autopilot: { mode: 'auto', trust: [], testCommand: 'npm test' } }));
  w.issue(17); w.issue(18, { labels: ['pdd:autopilot'] });
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel'), stateRoot = join(w.dir, 'state');
  const stateFile = join(stateRoot, `${createHash('sha256').update(cwd).digest('hex').slice(0, 20)}.json`);
  mkdirSync(stateRoot, { recursive: true });
  writeFileSync(stateFile, JSON.stringify({ enabled: true, cwd, repo: 'acme/widgets', defaultBranch: 'main', coordinatorId: 'coord-a', machine: 'machine-a', engine: 'core', label: 'pdd:autopilot',
    agent: { id: 'codex', kind: 'codex', command: 'codex' }, packageRoot: join(w.dir, 'pkg') }));
  const ports = { stateRoot, now: w.now, env: { HOME: process.env.HOME, PATH: process.env.PATH }, timer: async () => true, warn: () => {},
    run: async (command, args, options = {}) => {
      if (command === 'gh') return w.gh(args, options);
      if (command !== 'git') assert.fail(`unexpected program ${command}`);
      const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' }); return { code: r.status, stdout: r.stdout, stderr: r.stderr };
    },
    corePorts: { jobs: w.jobs, checkBase: async () => ({ exitCode: 0, message: 'ok' }), agentReady: async () => true } };
  const result = await tickAutopilot(stateFile, ports);
  assert.match(result.message, /Autopilot core: 1 started/, 'the machine engine core wins over pdd.json (full)');
  assert.ok(w.job(18, 'build') && !w.job(17), 'the machine label wins over pdd.json (no label)');
  const status = await runAutopilotLauncher({ command: 'status', cwd, packageRoot: join(w.dir, 'pkg'), env: ports.env }, ports);
  assert.match(status.message, /engine core \(this machine: pdd autopilot start --engine core\)/);
  assert.match(status.message, /only issues with pdd:autopilot \(this machine\)/);
});

// ---- Review 3 regressions (each failed on f35571720) ----------------------------------------------------
test('R15 the machine pause: 3 no-result ends in a row pause new jobs for 1 h with one alert; then intake resumes; again 2 h; a result resets', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  for (let n = 1; n <= 20; n++) w.issue(n);
  const alerts = [], extra = { alert: async input => alerts.push(input) };
  const failAll = () => { for (const job of w.started) if (w.alive.has(job.pid)) w.finish(job.issue, job.role, { code: 1 }); };
  await w.tick(extra); failAll();                       // #1, #2 start and fail
  await w.tick(extra); failAll();                       // both released (2 in a row); #3, #4 start and fail
  const opened = await w.tick(extra);                   // #3 released: 3 in a row, the pause starts
  assert.match(opened.message, /paused/);
  assert.equal(w.started.length, 4);
  assert.equal(alerts.length, 1);
  assert.match(alerts[0].text, /Autopilot paused new jobs for 1 h: the agent ended \d+ jobs with no result\. Check sign-in and limits\./);
  assert.match(coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now }), /New jobs paused until \S+ \(1 h\)/);
  w.advance(30 * MIN); await w.tick(extra);
  assert.equal(w.started.length, 4, 'no new job while paused');
  w.advance(31 * MIN); await w.tick(extra);
  assert.equal(w.started.length, 6, 'after the pause, intake resumes normally (both slots)');
  assert.ok(!w.started.slice(4).some(job => job.issue === 1), 'the counted no-result (#1, the first after a result) cools down for 24 hours');
  failAll(); await w.tick(extra);                       // still no result: the next pause is 2 h
  assert.equal(alerts.length, 2); assert.match(alerts[1].text, /paused new jobs for 2 h/);
  w.advance(121 * MIN); await w.tick(extra);
  assert.equal(w.started.length, 8);
  w.build(w.started.at(-1).issue); await w.tick(extra);  // a result resets the streak and the pause length
  const machine = JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
  assert.deepEqual([machine.streak, machine.hours], [0, 1]);
  assert.match(coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now }), /No pause: 0 no-result end\(s\) in a row/);
  assert.equal([...w.github.issues.values()].filter(issue => issue.labels.includes('pdd:stuck')).length, 0, 'no healthy issue is stuck during the outage');
});

test('R15b the per-issue rule: 24 h cooldown after a counted no-result, the 3rd counted no-result in 7 days ends the issue, older ones do not count', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.issue(17);
  await w.tick(); w.finish(17, 'build', { code: 1 }); await w.tick();
  assert.equal(endComments(w, 17).length, 0); assert.deepEqual(w.labels(17), [], 'the first no-result only releases the issue');
  assert.equal(w.comments(17).filter(c => c.includes('"labelEventId"')).length, 0, 'the claim comment is removed');
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), [], 'cooldown: not ready for 24 hours');
  w.advance(25 * HOUR);
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), [17]);
  await w.tick(); w.build(17); await w.tick();           // a PR result: the streak is 0 again
  w.review(17, 'FAIL', ['fix']); w.suite(17, 0); await w.tick();
  w.finish(17, 'repair', { code: 1 }); await w.tick();   // the 2nd counted no-result: still a release
  assert.equal(endComments(w, 17).length, 0); assert.deepEqual(w.labels(17), []);
  w.advance(25 * HOUR); w.issue(18);
  await w.tick(); w.build(18); await w.tick();           // #18 gives a result before #17 fails again
  w.finish(17, 'build', { code: 1 }); await w.tick();
  assert.equal(endComments(w, 17).length, 1, 'the 3rd counted no-result in 7 days is a normal END'); assert.ok(w.labels(17).includes('pdd:stuck'));
  // Counted no-result ends older than 7 days do not count.
  const v = await coreWorld(t, { settings: { runs: 1 } });
  v.issue(17);
  for (let i = 0; i < 2; i++) { await v.tick(); v.kill(17, 'build'); await v.tick(); v.advance(25 * HOUR); }
  v.advance(6 * 24 * HOUR);
  await v.tick(); v.finish(17, 'build', { code: 1 }); await v.tick();
  assert.equal(endComments(v, 17).length, 0); assert.deepEqual(v.labels(17), []);
});

test('Q1 regression: with every job failing for 16 hours, the pause bounds the damage and marks no issue', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  for (let n = 1; n <= 20; n++) w.issue(n);
  const alerts = [];
  for (let i = 0; i < 32; i++) {
    await w.tick({ alert: async input => alerts.push(input) });
    for (const job of w.started) if (w.alive.has(job.pid)) w.finish(job.issue, job.role, { code: 1 });
    w.advance(30 * MIN);
  }
  const stuck = [...w.github.issues.values()].filter(issue => issue.labels.includes('pdd:stuck'));
  assert.ok(w.started.length <= 10, `jobs started: ${w.started.length}`);
  assert.equal(stuck.length, 0, `issues stuck: ${stuck.map(issue => issue.number)}`);
  assert.ok(alerts.length >= 3 && alerts.length <= 5, `alerts: ${alerts.length}`);
  assert.match(alerts.at(-1).text, /paused new jobs for 8 h/);
});

test('Q2 regression: a repair that always ends with no result runs at most 3 times, keeps at most one open PR, then ends', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  let openMax = 0;
  for (let cycle = 0; cycle < 5; cycle++) {
    await w.tick();
    if (w.job(17, 'build') && w.alive.has(w.job(17, 'build').pid)) {
      w.build(17); await w.tick();
      w.review(17, 'FAIL', ['fix the bug']); w.suite(17, 0); await w.tick();
      w.finish(17, 'repair', { code: 1 }); await w.tick();
    }
    openMax = Math.max(openMax, [...w.github.prs.values()].filter(pr => pr.state === 'open').length);
    w.advance(25 * HOUR);
  }
  const builds = w.started.filter(j => j.issue === 17 && j.role === 'build').length;
  assert.ok(builds <= 3, `builds: ${builds}`);
  assert.equal(endComments(w, 17).length, 1); assert.ok(w.labels(17).includes('pdd:stuck'));
  assert.ok(openMax <= 1, `open PRs at most ${openMax}`);
  assert.ok([...w.github.prs.values()].slice(0, -1).every(pr => pr.state === 'closed'), 'released runs close their own PR');
});

test('R16 a PR number written as a string is read as a number; a non-number is no result', async t => {
  const w = await coreWorld(t);
  w.issue(17); w.issue(18); await w.tick();
  const { pr } = w.build(17);
  const job = w.job(17, 'build'), r = JSON.parse(readFileSync(job.result, 'utf8'));
  writeFileSync(job.result, JSON.stringify({ ...r, pr: String(r.pr), head: r.head.toUpperCase() }));
  w.finish(18, 'build', { result: { outcome: 'pr', pr: 'the PR', head: 'a'.repeat(40) } });
  await w.tick();
  const saved = JSON.parse(readFileSync(join(w.root, 'jobs', '17.json'), 'utf8'));
  assert.equal(saved.phase, 'pr'); assert.equal(saved.pr, pr.number); assert.equal(saved.head, r.head);
  assert.equal(existsSync(join(w.root, 'jobs', '18.json')), false, 'a non-number PR is no result');
  assert.deepEqual(w.labels(18), []);
});

test('R17 "Runtime: not run" never files a Runtime report by itself', async t => {
  const w = await coreWorld(t, { settings: { report: 'file' } });
  w.issue(17); await w.tick();
  const { pr } = w.build(17, { body: 'Fixes #17\n\nRuntime: not run (no prompt changed)', runtime: { state: 'not-run', kind: 'runtime', component: 'pdd test', code: 'no-verdict', cause: 'no prompt changed' } });
  await w.tick();
  assert.equal(w.reports.issues.size, 0); assert.equal(w.reports.calls.length, 0);
  assert.match(pr.body, /Runtime: not run \(no prompt changed\)$/, 'the PR body is not rewritten');
  assert.doesNotMatch(w.job(17, 'build').input, /"kind":"runtime\|pdd\|job","component"[^}]*"code"[^}]*\}\}/, 'the success template has no Runtime kind');
  w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
});

test('R18 a failed asynchronous spawn ends that job as no result and never crashes the tick', async t => {
  const { startAgentJob, readAgentJob } = await import('../src/agent-job.mjs');
  const { mkdtempSync } = await import('node:fs');
  const { tmpdir } = await import('node:os');
  const dir = mkdtempSync(join(tmpdir(), 'pdd-r18-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  let uncaught = null;
  const listener = error => { uncaught = error; };
  process.on('uncaughtException', listener);
  t.after(() => process.off('uncaughtException', listener));
  const job = startAgentJob({ id: 'x-build-1', dir, cwd: join(dir, 'gone'), command: 'true' });
  await new Promise(resolve => setTimeout(resolve, 300));
  assert.equal(uncaught, null);
  const seen = readAgentJob(job);
  assert.equal(seen.state, 'exited'); assert.equal(seen.exit.code, 127); assert.equal(seen.result, null);
});

test('R19 a suite checkout with a lockfile installs dependencies first; an install failure is a runner failure', async t => {
  const w = await coreWorld(t, { settings: { report: 'draft' } });
  w.baseCommit('package.json', JSON.stringify({ name: 'x', scripts: { test: 'node --test' }, devDependencies: { leftpad: '1.0.0' } }));
  w.baseCommit('package-lock.json', JSON.stringify({ name: 'x', lockfileVersion: 3, packages: {} }));
  w.issue(17); await w.tick(); w.build(17); await w.tick();
  const suite = w.job(17, 'suite');
  assert.equal(suite.command, '/bin/sh');
  assert.match(suite.args.join(' '), /npm ci --ignore-scripts/);
  assert.deepEqual(suite.args.slice(-5), ['suite', '--command', 'npm test', '--timeout', '120']);
  w.review(17, 'PASS');
  for (let i = 0; i < 3; i++) { writeFileSync(w.job(17, 'suite').log, 'Autopilot core: dependency install failed\n'); w.suite(17, 86); await w.tick(); }
  assert.equal(w.job(17, 'repair'), undefined, 'an install failure never uses a repair');
  assert.match(endComments(w, 17)[0], /Cause: pdd \/ suite-broken/);
  const v = await coreWorld(t);
  v.issue(17); await v.tick(); v.build(17); await v.tick();
  assert.equal(v.job(17, 'suite').command, process.execPath, 'no lockfile, no install');
});

// ---- Review 5 regressions (each failed on 90ce9a05) ----------------------------------------------------
test('R20 a 5-hour agent outage marks no healthy issue stuck, and work starts again after it', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  for (let n = 1; n <= 20; n++) w.issue(n);
  const start = w.now(), down = () => w.now() - start < 5 * HOUR;
  for (let i = 0; i < 24; i++) {
    await w.tick();
    for (const job of [...w.started]) if (w.alive.has(job.pid) && job.role === 'build') { if (down()) w.finish(job.issue, job.role, { code: 1 }); else w.build(job.issue); }
    w.advance(30 * MIN);
  }
  assert.equal([...w.github.issues.keys()].filter(n => endComments(w, n).some(c => c.includes('/ no-result'))).length, 0, 'no issue ends with no-result');
  assert.ok(w.started.some(job => job.started >= start + 5 * HOUR), 'work starts again after the outage');
});

test('R21 a cut history line, with or without a newline, is skipped; the per-issue rule still ends a repair loop', async t => {
  for (const cut of ['{"at":1,"issue":5,"outcome":"mer\n', '{"at":1,"issue":5,"outcome":"mer']) {
    const w = await coreWorld(t, { settings: { runs: 1 } });
    w.issue(17);
    mkdirSync(w.root, { recursive: true });
    writeFileSync(join(w.root, 'history.jsonl'), cut);
    for (let cycle = 0; cycle < 5; cycle++) {
      await w.tick();
      if (w.job(17, 'build') && w.alive.has(w.job(17, 'build').pid)) {
        w.build(17); await w.tick();
        w.review(17, 'FAIL', ['fix the bug']); w.suite(17, 0); await w.tick();
        w.finish(17, 'repair', { code: 1 }); await w.tick();
      }
      w.advance(25 * HOUR);
    }
    assert.ok(w.started.filter(j => j.issue === 17 && j.role === 'build').length <= 3, JSON.stringify(cut));
    assert.equal(endComments(w, 17).length, 1, JSON.stringify(cut));
    assert.doesNotThrow(() => coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now }));
  }
});

test('R22 a start that throws is a no-result end: 3 in a row pause intake at once; no issue is marked', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  for (let n = 1; n <= 20; n++) w.issue(n);
  const lines = () => existsSync(join(w.root, 'history.jsonl')) ? readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line)).filter(row => row.outcome).length : 0;
  const r = await w.tick({ jobs: { ...w.jobs, start: () => { throw Error('ENOSPC: no space left on device'); } } });
  assert.ok(lines() <= 3, `at most 3 claims before the pause: ${lines()}`);
  assert.match(r.message, /paused/);
  assert.equal([...w.github.issues.values()].filter(issue => issue.labels.length).length, 0, 'no label stays');
});

test('R23 a reviewer that ends with no result is a no-result end: release and close its own PR, never pdd:stuck by itself', async t => {
  const w = await coreWorld(t);
  w.issue(17); await w.tick();
  const { pr } = w.build(17); await w.tick();
  w.finish(17, 'review', { code: 1 }); w.suite(17, 0); await w.tick();         // the reviewer starts again once
  w.finish(17, 'review', { code: 1 }); await w.tick();                         // and again no verdict
  assert.equal(endComments(w, 17).length, 0); assert.ok(!w.labels(17).includes('pdd:stuck'));
  assert.ok(!w.labels(17).includes('pdd:working'), 'the issue is released');
  assert.equal(pr.state, 'closed', 'its own PR is closed');
  assert.ok(pr.comments.some(c => /closed/i.test(c.body)), 'with one short note');
  assert.match(readFileSync(join(w.root, 'history.jsonl'), 'utf8'), /"outcome":"released"/);
});

test('R24 a core.json that is null, not an object or not JSON reads as not paused; a pause far in the future is broken', async t => {
  for (const text of ['null\n', '[1,2]\n', '{"pausedUntil":"x","streak":"x","hours":3}\n', '{not json', '{"breaker":{"state":"paused"}}\n', '{"pending":{"issue":"17","at":1}}\n', '{"pending":"x"}\n']) {
    const w = await coreWorld(t, { settings: { runs: 1 } });
    w.issue(17);
    mkdirSync(w.root, { recursive: true }); writeFileSync(join(w.root, 'core.json'), text);
    const r = await w.tick();
    assert.ok(w.job(17, 'build'), `${text}: ${r.message}`);
    assert.match(coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now }), /No pause/);
    if (text.includes('pending')) {                      // a broken pending end writes no strike line
      w.build(17); await w.tick();
      assert.doesNotMatch(existsSync(join(w.root, 'history.jsonl')) ? readFileSync(join(w.root, 'history.jsonl'), 'utf8') : '', /strike/);
    }
  }
  const w = await coreWorld(t, { settings: { runs: 2 } });
  for (let n = 1; n <= 20; n++) w.issue(n);
  w.advance(48 * HOUR);
  const failAll = () => { for (const job of w.started) if (w.alive.has(job.pid)) w.finish(job.issue, job.role, { code: 1 }); };
  await w.tick(); failAll(); await w.tick(); failAll(); await w.tick();
  w.advance(-48 * HOUR);
  let paused = 0;
  for (let i = 0; i < 40; i++) { const r = await w.tick(); if (/paused/.test(r.message)) paused++; w.advance(30 * MIN); }
  assert.ok(paused <= 3, `paused ticks after the clock went back: ${paused}`);
});

// ---- Review 6 regressions (each failed on e5c69aca) ----------------------------------------------------
const outage = async (t, { runs, until, poison = () => false, ticks = 24, prepare, issues = 20 } = {}) => {
  const w = await coreWorld(t, { settings: { runs } });
  for (let n = 1; n <= issues; n++) w.issue(n);
  if (prepare) await prepare(w);
  const start = w.now(), alerts = [];
  w.down = at => until(at);
  for (let i = 0; i < ticks; i++) {
    await w.tick({ alert: async a => alerts.push(a) });
    const at = (w.now() - start) / HOUR;
    for (const job of [...w.started]) if (w.alive.has(job.pid) && job.role === 'build') {
      if (until(at) || poison(job, at)) {
        if (poison(job, at)) w.github.openPr({ branch: job.branch, head: 'a'.repeat(40), body: `Fixes #${job.issue}` });
        w.finish(job.issue, job.role, { code: 1 });
      } else w.build(job.issue);
    }
    w.advance(30 * MIN);
  }
  return { w, start, alerts };
};
const stuckByNoResult = w => [...w.github.issues.values()].filter(i => i.labels.includes('pdd:stuck') && endComments(w, i.number).some(c => c.includes('/ no-result'))).map(i => i.number);

test('M1a runs 1, one 5-hour outage: no healthy issue becomes stuck', async t => {
  const { w } = await outage(t, { runs: 1, until: at => at < 5 });
  assert.deepEqual(stuckByNoResult(w), []);
});

test('M1b runs 2 with one slot held by a PR whose suite runs: the outage marks no issue', async t => {
  const { w } = await outage(t, { runs: 2, until: at => at < 5, prepare: async w => { await w.tick(); w.build(1); await w.tick(); w.kill(2, 'build'); } });
  assert.deepEqual(stuckByNoResult(w), []);
});

test('M1c two outages in one day (and a third two days later) mark no healthy issue stuck', async t => {
  const { w } = await outage(t, { runs: 2, ticks: 120, until: at => at < 5 || at >= 11 && at < 16 || at >= 40 && at < 45 });
  assert.deepEqual(stuckByNoResult(w), []);
});

// A full life cycle: while the agent is down, every agent job exits with no result at once. While it is up, a build
// takes `buildTicks` ticks, a review passes on the next tick and a suite passes at once.
async function lifeCycle(t, { runs = 2, issues = 20, hours, down, buildTicks = 1, poison = () => false, poisonPr = false } = {}) {
  const w = await coreWorld(t, { settings: { runs } });
  for (let n = 1; n <= issues; n++) w.issue(n);
  const start = w.now(), age = new Map();
  for (let i = 0; i < hours * 2; i++) {
    await w.tick();
    const at = (w.now() - start) / HOUR;
    for (const job of [...w.started]) {
      if (!w.alive.has(job.pid)) continue;
      if (job.role === 'suite') { w.suite(job.issue, 0); continue; }
      if (down(at) || poison(job, at)) {
        // A bad build can open its PR and then end with no result.
        if (poisonPr && job.role === 'build' && !down(at)) w.github.openPr({ branch: job.branch, head: 'a'.repeat(40), body: `Fixes #${job.issue}` });
        w.finish(job.issue, job.role, { code: 1 }); continue;
      }
      age.set(job.id, (age.get(job.id) ?? 0) + 1);
      if (age.get(job.id) < (job.role === 'review' ? 1 : buildTicks)) continue;
      if (job.role === 'build' || job.role === 'repair') w.build(job.issue, { role: job.role });
      else if (job.role === 'review') w.review(job.issue, 'PASS');
    }
    w.advance(30 * MIN);
  }
  return { w, start };
}
const stuckNoResult = w => [...w.github.issues.values()].filter(i => i.labels.includes('pdd:stuck') && endComments(w, i.number).some(c => c.includes('/ no-result'))).map(i => i.number);

// A bad issue: its no-results in the streak that the outage left only release it (at most one run); then its 3rd
// counted no-result is one END. The history has a strike line for each of the first two.
const strikes = (w, n) => readFileSync(join(w.root, 'history.jsonl'), 'utf8').split('\n').filter(Boolean).map(line => JSON.parse(line)).filter(row => row.issue === n && row.strike).length;
test('M2 one issue that always ends with no result runs at most 3 counted times, then one END; the pause always ends', async t => {
  let poisonIssue = null;
  const { w, start } = await lifeCycle(t, { runs: 2, issues: 60, hours: 80, buildTicks: 4, down: at => at < 3, poisonPr: true,
    poison: (job, at) => { if (poisonIssue === null && at >= 3 && job.role === 'build') poisonIssue = job.issue; return job.issue === poisonIssue; } });
  assert.ok(poisonIssue);
  assert.ok(w.started.filter(j => j.issue === poisonIssue && j.role === 'build' && j.started >= start + 3 * HOUR).length <= 4);
  assert.equal(strikes(w, poisonIssue), 2);
  assert.equal(endComments(w, poisonIssue).length, 1); assert.ok(w.labels(poisonIssue).includes('pdd:stuck'));
  const healthy = w.started.filter(j => j.role === 'build' && j.issue !== poisonIssue && j.started >= start + 3 * HOUR);
  assert.ok(healthy.length && (healthy[0].started - start) / HOUR < 6, `a healthy job starts soon after the outage: ${healthy[0] && (healthy[0].started - start) / HOUR}`);
  assert.ok([...w.github.prs.values()].filter(pr => pr.branch.startsWith(`pdd/core-${poisonIssue}-`) && pr.state === 'open').length <= 1);
  assert.deepEqual(stuckNoResult(w), [poisonIssue]);
});

test('M2b a 30-hour outage and an oldest issue that always fails: the pause ends, other work runs, the bad issue ends after 3 counted runs', async t => {
  const { w, start } = await lifeCycle(t, { runs: 2, issues: 60, hours: 110, buildTicks: 4, down: at => at < 30, poisonPr: true, poison: (job, at) => job.issue === 1 && at >= 30 });
  const after = w.started.filter(j => j.role === 'build' && j.started >= start + 30 * HOUR);
  assert.ok(after.some(j => j.issue !== 1), 'other issues run after the outage');
  assert.ok(w.started.filter(j => j.issue === 1 && j.role === 'build' && j.started >= start + 30 * HOUR).length <= 4, 'one run in the outage streak, then 3 counted runs');
  assert.equal(strikes(w, 1), 2);
  assert.equal(endComments(w, 1).length, 1); assert.ok(w.labels(1).includes('pdd:stuck'));
  assert.ok([...w.github.prs.values()].filter(pr => pr.branch.startsWith('pdd/core-1-') && pr.state === 'open').length <= 1, 'at most one open core PR for the issue');
  assert.deepEqual(stuckNoResult(w), [1]);
});

// ---- Review 7 regressions (each failed on d4673c4a) ----------------------------------------------------
test('R25 P1: one agent outage of any length marks no healthy issue stuck', async t => {
  for (const [runs, outage] of [[2, 52], [2, 72], [1, 56]]) {
    const { w } = await lifeCycle(t, { runs, hours: outage + 12, down: at => at < outage });
    assert.deepEqual(stuckNoResult(w), [], `runs ${runs}, outage ${outage} h`);
    assert.ok(w.github.merges.length >= 1, `work goes on after the ${outage} h outage`);
  }
});

test('R25c repeated short outages (random, or down 1 or 2 h of every 5 h) mark no healthy issue stuck', async t => {
  for (const seed of [1, 2, 3, 4]) {
    let x = seed * 7919;
    const rand = () => { x = (x * 48271) % 2147483647; return x / 2147483647; };
    const windows = [];
    for (let h = 0; h < 96;) { h += 4 + rand() * 8; const len = 1 + Math.round(rand() * 2) / 2; windows.push([h, h + len]); h += len; }
    const { w } = await lifeCycle(t, { runs: 2, issues: 30, hours: 96, buildTicks: 4, down: at => windows.some(([a, b]) => at >= a && at < b) });
    assert.deepEqual(stuckNoResult(w), [], `seed ${seed}`);
  }
  for (const up of [3, 4]) {
    const { w } = await lifeCycle(t, { runs: 2, hours: 70, buildTicks: 4, down: at => at % 5 >= up });
    assert.deepEqual(stuckNoResult(w), [], `down ${5 - up} h of every 5 h`);
  }
});

test('R25b a bad issue that fails between successes still ends after 3 counted no-results', async t => {
  const { w } = await lifeCycle(t, { runs: 2, issues: 60, hours: 80, down: () => false, poison: job => job.issue === 1 });
  assert.equal(endComments(w, 1).length, 1); assert.ok(w.labels(1).includes('pdd:stuck'));
  assert.ok(w.started.filter(job => job.issue === 1 && job.role === 'build').length <= 3);
});

test('R26 an END writes a reset line: a person retry starts with no cooldown and fresh counts', async t => {
  const w = await coreWorld(t, { settings: { runs: 2 } });
  w.issue(17);
  for (let i = 0; i < 3; i++) {                          // a helper issue gives a result before each no-result of #17
    w.issue(30 + i);
    await w.tick(); w.build(30 + i); w.kill(17, 'build'); await w.tick();
    w.advance(25 * HOUR);
  }
  assert.equal(endComments(w, 17).length, 1); assert.ok(w.labels(17).includes('pdd:stuck'));
  assert.match(readFileSync(join(w.root, 'history.jsonl'), 'utf8'), /"issue":17,"outcome":"ended"[^\n]*"reset":true/);
  w.github.unlabel(17, 'pdd:stuck');
  assert.ok((await readyIssues({ state: w.state, settings: w.settings }, w.ports())).includes(17), 'no cooldown after the END');
  w.issue(40); await w.tick(); w.build(40); w.kill(17, 'build'); await w.tick();
  assert.equal(endComments(w, 17).length, 1, 'one more no-result after the retry only releases');
  assert.ok(!w.labels(17).includes('pdd:stuck'));
});

test('R27 a failed PR close is retried on the next tick, and the note comes after the close', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick();
  const job = w.job(17, 'build');
  const first = w.github.openPr({ branch: job.branch, head: 'a'.repeat(40), body: 'Fixes #17' });
  w.finish(17, 'build', { code: 1 });
  let failed = 0;
  const gh = w.gh;
  w.gh = async (args, options) => (args.includes('PATCH') && args.some(a => /\/pulls\/\d+$/.test(a)) && !failed++)
    ? { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}', stderr: 'gh: HTTP 502' } : gh(args, options);
  await w.tick();
  assert.equal(first.state, 'open'); assert.equal(first.comments.length, 0, 'no "closed" note before the close');
  await w.tick();
  assert.equal(first.state, 'closed'); assert.equal(first.comments.filter(c => /closed/i.test(c.body)).length, 1);
});

test('R28 before a new build, other open core PRs of the issue close; a merged PR and another prefix stay', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  const old = w.github.openPr({ branch: 'pdd/core-17-old-aaaaaa', head: 'b'.repeat(40), body: 'Fixes #17' });
  const other = w.github.openPr({ branch: 'pdd/other-17', head: 'c'.repeat(40), body: 'Fixes #17' });
  const merged = w.github.openPr({ branch: 'pdd/core-17-done-bbbbbb', head: 'd'.repeat(40), body: 'Fixes #17' });
  merged.state = 'closed'; merged.merged = true;
  const neighbour = w.github.openPr({ branch: 'pdd/core-170-x-cccccc', head: 'e'.repeat(40), body: 'Fixes #170' });
  await w.tick();
  assert.ok(w.job(17, 'build'));
  assert.equal(old.state, 'closed'); assert.ok(old.comments.some(c => /closed/i.test(c.body)));
  assert.equal(other.state, 'open', 'a PR from another branch prefix stays');
  assert.equal(merged.state, 'closed'); assert.equal(merged.merged, true);
  assert.equal(neighbour.state, 'open', 'issue #170 is not #17');
});

test('R29 a review verdict and a merge count as results and reset the streak', async t => {
  const w = await coreWorld(t, { settings: { runs: 3 } });
  for (const n of [17, 18, 19, 20]) w.issue(n);
  const alerts = [], extra = { alert: async a => alerts.push(a.text) };
  await w.tick(extra);
  w.build(17); w.kill(18, 'build'); w.kill(19, 'build'); await w.tick(extra);
  w.review(17, 'PASS'); w.suite(17, 0); await w.tick(extra);
  w.kill(20, 'build'); await w.tick(extra);
  assert.equal(w.github.merges.length, 1); assert.equal(alerts.length, 0, 'no pause right after a merge');
  assert.equal(JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8')).streak, 1);
});

test('R30 a suite that died 3 times counts all its tries: 3 deaths are a no-result, a mix is suite-broken', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick();
  const { pr } = w.build(17); await w.tick();
  w.review(17, 'PASS');
  for (let i = 0; i < 3; i++) { w.kill(17, 'suite'); await w.tick(); }
  assert.equal(endComments(w, 17).length, 0); assert.equal(pr.state, 'closed');
  assert.match(readFileSync(join(w.root, 'history.jsonl'), 'utf8'), /"outcome":"released"/);
  const v = await coreWorld(t, { settings: { runs: 1, report: 'draft' } });
  v.issue(17); await v.tick(); v.build(17); await v.tick();
  v.review(17, 'PASS');
  for (let i = 0; i < 2; i++) { writeFileSync(v.job(17, 'suite').log, 'Autopilot core: dependency install failed\n'); v.suite(17, 86); await v.tick(); }
  v.kill(17, 'suite'); await v.tick();                  // only the last try died: not "died 3 times"
  assert.match(endComments(v, 17)[0] ?? '', /Cause: pdd \/ suite-broken/);
});
