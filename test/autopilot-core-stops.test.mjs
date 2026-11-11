// STOPS-0129 (#3238 A1): every stop where the time ran out has one owner (pdd, service, machine, issue). Only an
// issue stop gives a strike and one note on the issue; a pdd stop files one report, waits and never ENDs.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { existsSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';
import { coreStatus, readyIssues } from '../src/autopilot-core.mjs';
import { listReportDrafts, fileReport } from '../src/autopilot-reports.mjs';

const MIN = 60 * 1000, HOUR = 60 * MIN;
const endComments = (w, n) => w.comments(n).filter(body => body.includes('<!-- pdd:autopilot-core:end:'));
const notes = (w, n) => w.github.issues.get(n).comments.filter(c => c.body.includes(`<!-- pdd:autopilot-core:stop-note:${n} -->`));
const jobFile = (w, n) => existsSync(join(w.root, 'jobs', `${n}.json`)) ? JSON.parse(readFileSync(join(w.root, 'jobs', `${n}.json`), 'utf8')) : null;
const history = w => existsSync(join(w.root, 'history.jsonl')) ? readFileSync(join(w.root, 'history.jsonl'), 'utf8').split('\n').filter(Boolean).map(line => JSON.parse(line)) : [];
const machine = w => JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
const status = w => coreStatus({ state: w.state, settings: w.settings }, { root: w.root, reportRoot: w.reportRoot, now: w.now, fs: undefined });
const quiet = async (w, minutes, extra) => { for (let i = 0; i < minutes / 10; i++) { w.advance(10 * MIN); await w.tick(extra); } };
// A PR whose review and suite passed: the merge check is at its last steps.
const greenPr = async w => { w.issue(17); await w.tick(); const built = w.build(17); await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); return built; };

test('S01 #2892 replay: a base check that cannot verify for 45 minutes is a pdd stop: one report, no END, no strike, no note; it waits, tries again and merges', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  const { pr } = await greenPr(w);
  const message = 'Automatic merge refused: main: could not verify releases; retry the read before merging.';
  let ok = false, reads = 0;
  const checkBase = async () => { reads++; return ok ? { exitCode: 0, message: 'Base check ok.' } : { exitCode: 1, message }; };
  await w.tick({ checkBase });
  const comments = w.comments(17).length;
  await quiet(w, 50, { checkBase });
  let job = jobFile(w, 17);
  assert.equal(job.phase, 'pr', 'the job keeps its PR'); assert.deepEqual([job.stepStop.owner, job.stepStop.code, job.stepStop.count], ['pdd', 'base-check', 1]);
  assert.equal(job.stepStop.until - job.stepStop.at, 15 * MIN);
  assert.equal(endComments(w, 17).length, 0, 'never an END'); assert.ok(w.labels(17).includes('pdd:working')); assert.ok(!w.labels(17).includes('pdd:stuck'));
  assert.equal(w.comments(17).length, comments, 'no note on the issue');
  assert.equal(history(w).filter(row => row.issue === 17 && row.strike).length, 0, 'no strike');
  let drafts = listReportDrafts({ root: w.reportRoot });
  assert.equal(drafts.length, 1); assert.equal(drafts[0].fingerprint, 'pdd.autopilot-core.base-check.0.1'); assert.equal(drafts[0].stopped, true);
  assert.match(drafts[0].body, /stopped one of its own steps for one job: it made no progress\. The issue gets no strike/);
  assert.doesNotMatch(drafts[0].body, /could not verify/, 'the public body has fixed fields only');
  assert.equal(machine(w).streak, 1, 'a pdd stop counts toward the machine pause');
  assert.match(status(w), /#17 waits: pdd stop base-check: the PR checks made no progress for 45 minutes \(nothing ran and nothing changed\); last error: Automatic merge refused: main: could not verify releases.*; next try after \S+ \(try 2\)/);
  // The wait: no base check, the claim keeps its heartbeat; then the merge check runs again with a fresh quiet clock.
  const before = reads, beat = job.claim.lastSeen;
  w.advance(10 * MIN); await w.tick({ checkBase });
  assert.equal(reads, before, 'no merge check during the wait'); assert.ok(jobFile(w, 17).claim.lastSeen > beat, 'the heartbeat goes on');
  w.advance(10 * MIN); await w.tick({ checkBase });
  assert.equal(reads, before + 1, 'the step runs again after the wait'); assert.equal(jobFile(w, 17).stepStop.resumed, true);
  // The same fault again: a second stop with a 30-minute wait and the same report (counted on the draft).
  await quiet(w, 50, { checkBase });
  job = jobFile(w, 17);
  assert.deepEqual([job.stepStop.count, job.stepStop.until - job.stepStop.at], [2, 30 * MIN]);
  drafts = listReportDrafts({ root: w.reportRoot });
  assert.equal(drafts.length, 1, 'one deduplicated report'); assert.equal(drafts[0].count, 2);
  assert.equal(endComments(w, 17).length, 0);
  // The base check works again: the PR merges.
  ok = true;
  await quiet(w, 40, { checkBase });
  assert.deepEqual(w.github.merges, [pr.number]); assert.equal(jobFile(w, 17), null);
  assert.equal(history(w).filter(row => row.strike).length, 0);
});

test('S02 a GitHub 502 for the whole quiet period is a service stop: no report, no END, no streak; it merges when GitHub answers', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, quietMinutes: 30 } });
  const { pr } = await greenPr(w);
  const gh = w.gh;
  let down = true;
  w.gh = async (args, options) => down && args.some(a => String(a).includes(`/pulls/${pr.number}`)) && !args.includes('PATCH') ? { code: 1, stdout: 'HTTP/2.0 502 Bad Gateway\r\n\r\n{}', stderr: '' } : gh(args, options);
  for (let i = 0; i < 6; i++) { w.advance(8 * MIN); await w.tick(); }
  const job = jobFile(w, 17);
  assert.deepEqual([job.stepStop.owner, job.stepStop.code], ['service', 'merge-check-tool']); assert.match(job.stepStop.text, /502/);
  assert.equal(listReportDrafts({ root: w.reportRoot }).length, 0, 'a service stop files no report');
  assert.equal(machine(w).streak, 0); assert.equal(endComments(w, 17).length, 0); assert.ok(w.labels(17).includes('pdd:working'));
  down = false;
  await quiet(w, 30);
  assert.deepEqual(w.github.merges, [pr.number]);
});

test('S03 a planted sleeping agent is a machine stop: a release with no note, no strike and no pending strike', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick();
  await quiet(w, 50);
  const row = history(w).find(r => r.issue === 17 && r.outcome);
  assert.deepEqual([row.outcome, row.owner, row.noResult], ['released', 'machine', true]);
  assert.match(row.text, /the build agent made nothing new for 45 minutes/);
  assert.deepEqual(w.labels(17), []); assert.equal(w.comments(17).length, 0, 'no note, no END');
  assert.equal(machine(w).pending, null, 'a machine stop leaves no pending strike'); assert.equal(machine(w).streak, 1);
  assert.match(status(w), /#17 cools down until \S+ \(owner machine\): the build agent made nothing new/);
  assert.match(status(w), /#17 released \S+ \(owner machine\): /);
  // A later job result on this machine gives #17 no strike (the old pending rule gave one).
  w.issue(18); await w.tick(); w.build(18); await w.tick();
  assert.equal(history(w).filter(r => r.strike).length, 0);
});

test('S04 an account that is out: a service stop, no note, no strike, no cooldown', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick();
  w.say(17, 'build', JSON.stringify({ type: 'error', message: 'You are out of credits. Add credits to go on.' }));
  await quiet(w, 50);
  const row = history(w).find(r => r.issue === 17 && r.outcome);
  assert.deepEqual([row.outcome, row.owner, row.noResult], ['released', 'service', undefined]);
  assert.match(row.text, /the AI service said "You are out of credits/);
  assert.equal(w.comments(17).length, 0); assert.equal(history(w).filter(r => r.strike).length, 0); assert.equal(machine(w).streak, 1);
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), [17], 'no cooldown');
});

test('S05 the same command hangs twice at one head, then the agent is quiet: an issue stop with one note; the next build gets the hang', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick();
  const build = w.job(17, 'build'), head = w.git(build.cwd, 'rev-parse', 'HEAD');
  w.hang(17, 'build', { head, command: '/bin/bash -lc npm test -- test/duration.test.js' }); w.advance(10 * MIN); await w.tick();
  w.hang(17, 'build', { head, command: '/bin/bash -lc npm test -- test/duration.test.js' });
  await quiet(w, 50);
  const row = history(w).find(r => r.issue === 17 && r.outcome);
  assert.deepEqual([row.outcome, row.owner, row.noResult], ['released', 'issue', true]);
  const strikes = history(w).filter(r => r.strike);
  assert.equal(strikes.length, 1); assert.equal(strikes[0].owner, 'issue');
  assert.deepEqual([strikes[0].hang.shown, strikes[0].hang.test, strikes[0].hang.head], ['npm test -- test/duration.test.js', 'test/duration.test.js', head]);
  const [note] = notes(w, 17);
  assert.equal(notes(w, 17).length, 1); assert.equal(endComments(w, 17).length, 0); assert.deepEqual(w.labels(17), []);
  assert.match(note.body, new RegExp(`^Autopilot stopped a job here: \`npm test -- test/duration\\.test\\.js\` hung for 15 minutes in test/duration\\.test\\.js on this change \\(head ${head.slice(0, 7)}\\)\\. It tries again after \\d{4}-\\d\\d-\\d\\d \\d\\d:\\d\\d UTC with that detail\\. Nothing to do now\\.`));
  assert.match(note.body, /Stops caused by this change in the last 7 days: 1 of 3/);
  assert.equal(machine(w).streak, 0, 'an issue stop is not a machine fault');
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), [], 'the 24-hour cooldown');
  w.advance(25 * HOUR); await w.tick();
  assert.match(w.job(17, 'build').input, /An earlier Autopilot job on this issue stopped: `npm test -- test\/duration\.test\.js` hung for 15 minutes in test\/duration\.test\.js with no output and almost no CPU/);
});

test('S06 one hang, or two hangs of different commands, then a quiet agent is still a machine stop', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick();
  const head = w.git(w.job(17, 'build').cwd, 'rev-parse', 'HEAD');
  w.hang(17, 'build', { head, command: '/bin/bash -lc npm install' }); w.advance(10 * MIN); await w.tick();
  w.hang(17, 'build', { head, command: '/bin/bash -lc npm test' });
  await quiet(w, 60);
  assert.equal(history(w).find(r => r.issue === 17 && r.outcome).owner, 'machine');
  assert.equal(notes(w, 17).length, 0); assert.equal(history(w).filter(r => r.strike).length, 0);
});

test('S07 a suite that hangs twice at the head is an issue stop: a repair with the hang, one note updated in place, the 3rd stop ENDs', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick(); let built = w.build(17); await w.tick(); w.review(17, 'PASS');
  const hangTwice = async () => {
    for (let i = 0; i < 2; i++) { w.say(17, 'suite', '▶ test/duration.test.js'); await quiet(w, 60); }
  };
  await hangTwice();
  assert.equal(w.started.filter(j => j.role === 'suite').length, 2, 'the first quiet suite runs again');
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'the second hang at the head starts a repair');
  assert.match(repair.input, new RegExp(`The full test suite hung at head ${built.head.slice(0, 7)}: \`npm test\` hung for 45 minutes in test/duration\\.test\\.js with no output and almost no CPU\\. Last output: ▶ test/duration\\.test\\.js\\.`));
  let [note] = notes(w, 17);
  assert.equal(notes(w, 17).length, 1); assert.match(note.body, /A repair starts now with that detail\. Nothing to do now\./); assert.match(note.body, /1 of 3/);
  const id = note.id;
  assert.equal(endComments(w, 17).length, 0); assert.ok(w.labels(17).includes('pdd:working'));
  // The repair pushes a new head; the suite hangs twice again: the same note says 2 of 3.
  built = w.build(17, { role: 'repair' }); await w.tick(); w.review(17, 'PASS');
  await hangTwice();
  [note] = notes(w, 17);
  assert.equal(notes(w, 17).length, 1, 'updated in place'); assert.equal(note.id, id); assert.match(note.body, /2 of 3/);
  assert.ok(w.job(17, 'repair').id !== repair.id, 'a second repair, not the same-finding END');
  // The 3rd stop is the END.
  w.build(17, { role: 'repair' }); await w.tick(); w.review(17, 'PASS');
  await hangTwice();
  const [ended] = endComments(w, 17);
  assert.match(ended, /Cause: job \/ hung/); assert.match(ended, /the 3rd stop that this change caused in 7 days/);
  assert.ok(w.labels(17).includes('pdd:stuck'));
});

test('S08 a suite that hangs once in a test file that the PR changes is an issue stop at once', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick();
  const job = w.job(17, 'build');
  const { writeFileSync, mkdirSync } = await import('node:fs');
  mkdirSync(join(job.cwd, 'test'), { recursive: true }); writeFileSync(join(job.cwd, 'test', 'slow.test.js'), 'test\n');
  w.build(17); await w.tick(); w.review(17, 'PASS');
  w.say(17, 'suite', 'not ok 3 - waits (test/slow.test.js:4:1)'); await quiet(w, 60);
  assert.equal(w.started.filter(j => j.role === 'suite').length, 1, 'no second suite run');
  assert.match(w.job(17, 'repair').input, /hung for 45 minutes in test\/slow\.test\.js/);
  assert.equal(notes(w, 17).length, 1);
});

test('S09 a job that cannot advance: in phase running a pdd report and a release that is not counted; CI that never starts is service', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, quietMinutes: 60 } });
  w.issue(17); await w.tick();
  const broken = { ...w.jobs, read: () => { throw Error('broken job record'); } };
  for (let i = 0; i < 6; i++) { w.advance(20 * MIN); await w.tick({ jobs: broken }); }
  const row = history(w).find(r => r.issue === 17 && r.outcome);
  assert.deepEqual([row.outcome, row.owner, row.noResult], ['released', 'pdd', undefined]);
  const [draft] = listReportDrafts({ root: w.reportRoot });
  assert.equal(draft.fingerprint, 'pdd.autopilot-core.crash.0.1'); assert.equal(draft.stopped, true);
  assert.equal(endComments(w, 17).length, 0); assert.ok(!w.labels(17).includes('pdd:stuck'));
  assert.equal(w.started.filter(job => job.issue === 17).length, 2, 'no cooldown: a new job tries #17 again at the next tick');
  // CI pending with no change for ciStuckMinutes: service, released, not counted.
  const v = await coreWorld(t, { settings: { runs: 1 } });
  v.issue(17); await v.tick(); const built = v.build(17);
  v.github.statuses.set(built.head, [{ context: 'external/ci', state: 'pending' }]);
  await v.tick(); v.review(17, 'PASS'); v.suite(17, 0);
  for (let i = 0; i < 14; i++) { v.advance(30 * MIN); await v.tick(); }
  const ci = history(v).find(r => r.issue === 17 && r.outcome);
  assert.deepEqual([ci.outcome, ci.owner, ci.noResult], ['released', 'service', undefined]);
});

test('S10 the stop note is this engine\'s own: a marker comment by someone else is never patched', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  w.github.comment(17, 'copied text <!-- pdd:autopilot-core:stop-note:17 -->', 'someone');
  await w.tick();
  const head = w.git(w.job(17, 'build').cwd, 'rev-parse', 'HEAD');
  for (let i = 0; i < 2; i++) w.hang(17, 'build', { head, command: '/bin/sh -c make check' });
  await quiet(w, 50);
  const all = notes(w, 17);
  assert.equal(all.length, 2); assert.equal(all[0].body, 'copied text <!-- pdd:autopilot-core:stop-note:17 -->');
  assert.match(all[1].body, /^Autopilot stopped a job here: `make check` hung/);
});

test('S11 the report owner: a stopped cause has its own public sentence and stable codes', async t => {
  const { mkdtempSync } = await import('node:fs'), { tmpdir } = await import('node:os');
  const root = mkdtempSync(join(tmpdir(), 'pdd-stop-report-'));
  t.after(async () => (await import('node:fs')).rmSync(root, { recursive: true, force: true }));
  for (const code of ['base-check', 'step-quiet']) {
    const r = await fileReport({ cause: { kind: 'pdd', component: 'autopilot-core', code, text: 'x', stopped: true }, mode: 'draft', root, machine: 'm', versions: { pdd: '0.1.29' }, step: code }, {});
    assert.equal(r.fingerprint, `pdd.autopilot-core.${code}.0.1`);
  }
  const drafts = listReportDrafts({ root });
  assert.ok(drafts.every(d => d.stopped === true && /stopped one of its own steps/.test(d.body) && !/ended one job/.test(d.body)));
  await fileReport({ cause: { kind: 'pdd', component: 'autopilot-core', code: 'crash', text: 'x' }, mode: 'draft', root, machine: 'm', versions: { pdd: '0.1.29' }, step: 's' }, {});
  assert.match(listReportDrafts({ root }).find(d => d.code === 'crash').body, /ended one job/);
});

test('S12 the loop guard: a 3rd pdd stop of one issue in 24 hours holds it (no END, no strike, one stop-loop report) until a person comments', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  const { pr } = await greenPr(w);
  let ok = false, reads = 0;
  const checkBase = async () => { reads++; return ok ? { exitCode: 0, message: 'Base check ok.' } : { exitCode: 1, message: 'Automatic merge refused: main: could not verify releases; retry the read before merging.' } };
  await w.tick({ checkBase });
  for (let i = 0; i < 30 && !jobFile(w, 17)?.stepStop?.held; i++) await quiet(w, 10, { checkBase });
  const job = jobFile(w, 17);
  assert.equal(job.stepStop.held, true); assert.equal(job.stepStop.count, 3, 'held at the 3rd stop');
  assert.equal(history(w).filter(row => row.issue === 17 && row.stop).length, 3);
  assert.equal(history(w).filter(row => row.issue === 17 && row.hold).length, 1);
  assert.equal(endComments(w, 17).length, 0); assert.ok(!w.labels(17).includes('pdd:stuck')); assert.equal(history(w).filter(row => row.strike).length, 0);
  const fingerprints = listReportDrafts({ root: w.reportRoot }).map(d => d.fingerprint).sort();
  assert.deepEqual(fingerprints, ['pdd.autopilot-core.base-check.0.1', 'pdd.autopilot-core.stop-loop.0.1']);
  assert.match(listReportDrafts({ root: w.reportRoot }).find(d => d.code === 'stop-loop').body, /Autopilot holds one issue/);
  assert.ok(machine(w).streak >= 3, 'the machine pause still counts each stop');
  assert.match(status(w), /#17 held since \S+: 3 stops of Autopilot's own steps or of a service in 24 hours \(last: pdd base-check: .*\); it goes on after a new engine version or a person's comment/);
  // Held: no merge check for hours, also after the backoff; ok = true changes nothing while held.
  ok = true; const before = reads;
  await quiet(w, 180, { checkBase });
  assert.equal(reads, before); assert.equal(w.github.merges.length, 0); assert.ok(jobFile(w, 17).stepStop.held);
  // A trusted person's comment ends the hold (read at most every 30 minutes); then the merge check runs and merges.
  w.github.comment(17, 'The base check is fixed, go on.', 'acme');
  await quiet(w, 40, { checkBase });
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.ok(history(w).some(row => row.issue === 17 && row.unhold && /a person's comment/.test(row.text)));
});

test('S13 the loop guard: three service releases of one issue in 24 hours hold it in the ready rule; a new engine version ends the hold', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  const out = () => w.say(17, 'build', JSON.stringify({ type: 'error', message: 'You are out of credits. Add credits to go on.' }));
  for (let round = 0; round < 3; round++) {
    for (let i = 0; i < 40 && !(w.job(17, 'build') && w.alive.has(w.job(17, 'build').pid)); i++) await quiet(w, 30);
    out(); await quiet(w, 50);
  }
  const holds = history(w).filter(row => row.issue === 17 && row.hold);
  assert.equal(holds.length, 1); assert.equal(holds[0].owner, 'service'); assert.equal(holds[0].version, '0.1.27');
  assert.equal(history(w).filter(row => row.issue === 17 && row.outcome === 'released' && row.owner === 'service').length, 3);
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), [], 'held: not ready');
  assert.equal(w.comments(17).length, 0, 'no note and no END'); assert.ok(!w.labels(17).includes('pdd:stuck'));
  // A comment by an untrusted person or an engine marker comment does not end it; a new engine version does.
  w.github.comment(17, 'please retry', 'stranger');
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports()), []);
  assert.deepEqual(await readyIssues({ state: w.state, settings: w.settings }, w.ports({ version: '0.1.28' })), [17]);
  assert.ok(history(w).some(row => row.issue === 17 && row.unhold && /a new engine version/.test(row.text)));
});
