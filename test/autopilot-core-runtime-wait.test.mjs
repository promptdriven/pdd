// #3241, rule B5: a Runtime check that was never sent because of an interpreter maintenance window is sent once after
// the window, before the merge. The job waits (no "not run", no report, no slot, never quiet), reads the free capacity
// every 10 minutes, and after 12 hours ships "Runtime: not run (maintenance since HH:MM UTC)" with one report. A sent
// check with no verdict and no failed check is sent once more too; a failed check never.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { appendFileSync, readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';
import { coreStatus } from '../src/autopilot-core.mjs';
import { listReportDrafts } from '../src/autopilot-reports.mjs';

const MIN = 60 * 1000, HOUR = 60 * MIN;
const STORY = 'user_stories/place-order.md';
const mergeComment = pr => pr.comments.map(c => c.body).find(body => body.includes('<!-- pdd:autopilot-core:merge:'));
const notRunBody = 'Fixes #17\n\nRuntime: not run (maintenance until 08:52 UTC)\nEvidence: runtime=not-run; tests=pass (3/3)';
const maintenance = { state: 'not-run', kind: 'runtime', component: 'pdd-test', code: 'maintenance', cause: 'the interpreter is in maintenance' };
// A fake interpreter that is in maintenance until `until`; the agent's pdd test stopped before sending one Story.
function window(w, minutes) {
  const until = w.now() + minutes * MIN;
  w.health = () => w.now() < until ? { state: 'unavailable', detail: 'maintenance', until: new Date(until).toISOString(), reason: 'deploy' } : { state: 'healthy', detail: 'HTTP 200' };
  w.resend = () => ({ stories: [STORY], neverSent: [STORY], noVerdict: [], failed: [], maintenance: true });
  return until;
}
const summary = (exitCode, state, stories = ['place-order']) => `${JSON.stringify({ batch: '20261111-090000-abcd', exit_code: exitCode, summary_line: `${stories.length} of ${stories.length} Story ${state}`,
  rows: stories.map(story => ({ story, test: `tests/${story}.json`, state, checks: state === 'not run' ? null : { passed: state === 'passed' ? 3 : 2, total: 3 } })) })}\n`;
const answer = (w, n, exitCode, state, stories) => { const job = w.job(n, 'runtime'); appendFileSync(job.log, summary(exitCode, state, stories)); w.finish(n, 'runtime', { code: exitCode }); return job; };
// The PR changes the Story (a PASS of a Story that the PR does not change never counts, #3227).
const story = (w, n, path = STORY) => { const cwd = w.job(n, 'build').cwd; mkdirSync(join(cwd, 'user_stories'), { recursive: true }); writeFileSync(join(cwd, path), `# ${path}\n`); };
const status = w => coreStatus({ state: w.state, settings: w.settings }, { root: w.root, now: w.now });

test('maintenance for 30 minutes: the job waits, sends the check after the window, gets PASS, and the PR has no "not run"', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); w.issue(18);
  await w.tick();
  const until = window(w, 30);
  story(w, 17); const { pr } = w.build(17, { body: notRunBody, runtime: maintenance });
  await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0);
  await w.tick();
  assert.equal(w.github.merges.length, 0, 'no merge while the check waits');
  assert.equal(w.healthReads.length, 1, 'one free capacity read');
  assert.match(pr.body, /Runtime: not run \(maintenance until 08:52 UTC\)/, 'nothing is rewritten while it waits');
  assert.equal(listReportDrafts({ root: w.reportRoot }).length, 0, 'no report while it waits');
  assert.ok(w.job(18, 'build'), 'the waiting job holds no slot: the next issue starts');
  assert.match(status(w), /#17 PR #\d+ at \w+: .*Runtime: waits for the interpreter maintenance since 12:\d\d UTC \(until 12:\d\d UTC\); no slot/);
  assert.equal(w.resendReads.length, 1, 'the saved checks are read once for the head');
  assert.equal(w.resendReads[0].root, w.job(17, 'build').cwd);

  for (let at = w.now(); at + 10 * MIN < until; at += 10 * MIN) { w.advance(10 * MIN); await w.tick(); }
  assert.equal(w.started.filter(job => job.role === 'runtime').length, 0, 'nothing is sent during the window');
  w.advance(10 * MIN); await w.tick();
  const run = w.job(17, 'runtime');
  assert.ok(run, 'after the window the engine sends the check itself');
  assert.equal(run.command, process.execPath); assert.deepEqual(run.args.slice(1), ['test', '--json', STORY]);
  assert.equal(run.cwd, w.job(17, 'build').cwd, 'in the job worktree, where the agent ran pdd test');
  assert.equal(w.started.filter(job => job.issue === 17 && ['build', 'repair'].includes(job.role)).length, 1, 'no agent for the resend');
  assert.ok(w.healthReads.length >= 4 && w.healthReads.length <= 5, `a read every 10 minutes (${w.healthReads.length})`);
  assert.match(status(w), /Runtime: the check that was not sent runs again/);

  answer(w, 17, 0, 'passed');
  await w.tick();
  assert.match(pr.body, /^Runtime: PASS \(user_stories\/place-order\.md, 3\/3 checks\)$/m); assert.match(pr.body, /Evidence: runtime=pass; tests=pass \(3\/3\)/);
  assert.doesNotMatch(pr.body, /not run/);
  await w.tick();
  assert.deepEqual(w.github.merges, [pr.number], 'the PR merges after the PASS');
  assert.match(mergeComment(pr), /- Runtime: PASS/); assert.doesNotMatch(mergeComment(pr), /not run/);
  assert.equal(listReportDrafts({ root: w.reportRoot }).length, 0, 'no Runtime report');
  assert.equal(w.started.filter(job => job.role === 'runtime').length, 1, 'the check is sent once');
});

test('a long window is no quiet step: 2 hours of waiting never end the job, then the check is sent', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, quietMinutes: 45 } });
  w.issue(17);
  await w.tick();
  window(w, 120);
  story(w, 17); w.build(17, { body: notRunBody, runtime: maintenance }); await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0);
  for (let i = 0; i < 12; i++) { await w.tick(); w.advance(10 * MIN); }
  assert.deepEqual(w.stopped, [], 'no process is stopped');
  assert.ok(w.github.issues.get(17).labels.includes('pdd:working'), 'the claim stays');
  await w.tick();
  assert.ok(w.job(17, 'runtime'), 'the check is sent after 2 hours');
});

test('a real FAIL after the window goes to a repair; no verdict keeps "not run" with one report and merges', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); w.issue(18);
  await w.tick();
  window(w, 10);
  story(w, 17); const first = w.build(17, { body: notRunBody, runtime: maintenance }); await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  w.advance(10 * MIN); await w.tick();
  answer(w, 17, 1, 'failed'); await w.tick();
  assert.match(first.pr.body, /^Runtime: FAIL \(user_stories\/place-order\.md, 1 of 3 checks failed; pdd test sent again by Autopilot\)$/m);
  await w.tick();
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'a real FAIL starts a repair'); assert.match(repair.input, /Runtime: FAIL/);

  // #18: the check sent after the window gives no verdict: "not run" stays true, one report, and the merge goes on.
  w.build(17, { role: 'repair', body: 'Fixes #17\n\nRuntime: PASS\nEvidence: runtime=pass (1/1); tests=pass (3/3)', runtime: { state: 'pass' } });
  w.resend = input => input.root === w.job(18, 'build')?.cwd ? { stories: [STORY], neverSent: [STORY], noVerdict: [], failed: [], maintenance: true } : { stories: [], neverSent: [], noVerdict: [], failed: [], maintenance: false };
  await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  assert.equal(w.github.prs.get(first.pr.number).merged, true, '#17 merges after its repair');
  await w.tick();
  story(w, 18); const second = w.build(18, { body: notRunBody.replace('#17', '#18'), runtime: maintenance }); await w.tick();
  w.review(18, 'PASS'); w.suite(18, 0); await w.tick();
  answer(w, 18, 5, 'not run');
  await w.tick();
  assert.match(second.pr.body, /^Runtime: not run \(user_stories\/place-order\.md: the check that Autopilot sent again gave no verdict\)$/m);
  await w.tick();
  assert.equal(second.pr.merged, true, 'a check with no verdict does not block the merge');
  const drafts = listReportDrafts({ root: w.reportRoot });
  assert.equal(drafts.length, 1); assert.match(drafts[0].fingerprint, /no-verdict/);
  assert.equal(w.started.filter(j => j.issue === 18 && j.role === 'runtime').length, 1, 'a sent check with no verdict is not sent again');
});

test('maintenance for more than 12 hours: "Runtime: not run (maintenance since HH:MM UTC)", one report, then the merge', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick();
  window(w, 24 * 60);
  story(w, 17); const { pr } = w.build(17, { body: notRunBody, runtime: maintenance }); await w.tick();
  w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  const first = w.now();
  for (let i = 0; i < 72 && !pr.merged; i++) { w.advance(10 * MIN); await w.tick(); }
  assert.equal(w.started.filter(job => job.role === 'runtime').length, 0, 'nothing is sent while the maintenance lasts');
  assert.ok(w.now() - first >= 12 * HOUR && w.now() - first <= 12 * HOUR + 20 * MIN, 'the backstop is 12 hours');
  assert.match(pr.body, new RegExp(`^Runtime: not run \\(user_stories/place-order\\.md: maintenance since ${new Date(first).toISOString().slice(11, 16)} UTC\\)$`, 'm'));
  assert.match(pr.body, /Evidence: runtime=not-run/);
  assert.equal(pr.merged, true);
  const drafts = listReportDrafts({ root: w.reportRoot });
  assert.equal(drafts.length, 1, 'one report'); assert.match(drafts[0].fingerprint, /maintenance/);
  assert.ok(w.healthReads.length >= 72 && w.healthReads.length <= 75, `one read every 10 minutes for 12 hours (${w.healthReads.length})`);
});

test('a not-run line with no unsent check keeps today\'s route: no capacity read, one report, the merge', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick();
  story(w, 17); const { pr } = w.build(17, { body: 'Fixes #17\n\nRuntime: not run (pdd lint refused the case)', runtime: { state: 'not-run', kind: 'runtime', component: 'pdd lint', code: 'lint-refusal', cause: 'pdd lint refused the case' } });
  await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  assert.equal(pr.merged, true); assert.equal(w.healthReads, undefined, 'no capacity read');
  assert.match(pr.body, /Runtime: not run \(pdd lint refused the case\)/);
  assert.equal(listReportDrafts({ root: w.reportRoot }).length, 1);
});

test('B5 a sent check with no verdict and no failed check is sent once more, with no wait; the history keeps the agent\'s lines', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick();
  w.resend = () => ({ stories: [STORY], neverSent: [], noVerdict: [STORY], failed: [], maintenance: false });
  const body = 'Fixes #17\n\nRuntime: not run (graph-provider-failure: no verdict)\nEvidence: runtime=not-run (17/19); tests=pass (3/3)';
  story(w, 17); const { pr } = w.build(17, { body, runtime: { state: 'not-run', kind: 'runtime', component: 'pdd test', code: 'no-verdict', cause: 'graph-provider-failure' } });
  await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  assert.ok(w.job(17, 'runtime'), 'sent at once: the interpreter is healthy');
  assert.equal(w.healthReads.length, 1);
  answer(w, 17, 0, 'passed'); await w.tick();
  assert.match(pr.body, /^Runtime: PASS \(user_stories\/place-order\.md, 3\/3 checks\)$/m); assert.match(pr.body, /Evidence: runtime=pass; tests=pass \(3\/3\)/);
  await w.tick();
  assert.equal(pr.merged, true);
  const history = readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line)).find(row => row.outcome === 'merged');
  assert.deepEqual(history.runtimeOriginal.lines, ['Runtime: not run (graph-provider-failure: no verdict)'], 'the agent\'s line stays for an audit');
  assert.equal(history.runtimeOriginal.evidence, 'Evidence: runtime=not-run (17/19); tests=pass (3/3)');
  assert.deepEqual(history.runtimeOriginal.engine, ['Runtime: PASS (user_stories/place-order.md, 3/3 checks)']);
  assert.equal(history.runtimeOriginal.runtime.code, 'no-verdict');
  assert.equal(w.started.filter(job => job.role === 'runtime').length, 1, 'once for the head');
});

test('B5 a check with a failed check is never sent again; one Story line each is fine', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick();
  w.resend = () => ({ stories: ['user_stories/b.md'], neverSent: [], noVerdict: ['user_stories/b.md'], failed: [STORY], maintenance: false });
  story(w, 17); story(w, 17, 'user_stories/b.md'); w.build(17, { body: `Fixes #17\n\nRuntime: not run (${STORY}: no verdict)\nRuntime: not run (user_stories/b.md: no verdict)`, runtime: { state: 'not-run', kind: 'runtime', code: 'no-verdict', cause: 'no verdict' } });
  await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  assert.equal(w.started.filter(job => job.role === 'runtime').length, 0, 'no resend when a check failed');
  assert.equal(w.healthReads, undefined, 'and no capacity read');
});

test('rule B5 maintenance lines, one per Story: the engine waits, sends both Stories once and writes one PASS line each', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick();
  window(w, 20);
  w.resend = () => ({ stories: [STORY, 'user_stories/b.md'], neverSent: [STORY, 'user_stories/b.md'], noVerdict: [], failed: [], maintenance: true });
  story(w, 17); story(w, 17, 'user_stories/b.md'); const { pr } = w.build(17, { body: `Fixes #17\n\nRuntime: not run (${STORY}: maintenance until 08:52 UTC)\nRuntime: not run (user_stories/b.md: maintenance until 08:52 UTC)`, runtime: maintenance });
  await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  assert.equal(w.started.filter(job => job.role === 'runtime').length, 0, 'it waits');
  w.advance(10 * MIN); await w.tick(); w.advance(10 * MIN); await w.tick();
  assert.deepEqual(w.job(17, 'runtime').args.slice(1), ['test', '--json', STORY, 'user_stories/b.md']);
  answer(w, 17, 0, 'passed', ['place-order', 'b']); await w.tick();
  assert.equal(pr.body.match(/^Runtime:.*$/gm).join('|'), 'Runtime: PASS (user_stories/place-order.md, 3/3 checks)|Runtime: PASS (user_stories/b.md, 3/3 checks)');
  await w.tick();
  assert.equal(pr.merged, true);
});

test('a single line with no Story and two resent Stories becomes one line each; a Story with no verdict keeps "not run"', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick();
  w.resend = () => ({ stories: [STORY, 'user_stories/b.md'], neverSent: [STORY, 'user_stories/b.md'], noVerdict: [], failed: [], maintenance: false });
  story(w, 17); story(w, 17, 'user_stories/b.md'); const { pr } = w.build(17, { body: 'Fixes #17\n\nRuntime: not run (maintenance until 08:52 UTC)\nEvidence: runtime=not-run; tests=pass (3/3)', runtime: maintenance });
  await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  const job = w.job(17, 'runtime');
  appendFileSync(job.log, `${JSON.stringify({ exit_code: 3, summary_line: '1 of 2 Stories pass', rows: [{ story: 'place-order', state: 'passed', checks: { passed: 3, total: 3 } }, { story: 'b', state: 'unknown', checks: null }] })}\n`);
  w.finish(17, 'runtime', { code: 3 }); await w.tick();
  assert.equal(pr.body.match(/^Runtime:.*$/gm).join('|'), 'Runtime: PASS (user_stories/place-order.md, 3/3 checks)|Runtime: not run (user_stories/b.md: the check that Autopilot sent again gave no verdict)');
  assert.match(pr.body, /Evidence: runtime=not-run; tests=pass \(3\/3\)/);
  await w.tick();
  assert.equal(pr.merged, true, 'no verdict does not block the merge');
  assert.match(listReportDrafts({ root: w.reportRoot })[0].fingerprint, /no-verdict/);
});

test('per-Story lines limit the resend to the Stories that a "not run" line names', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick();
  w.resend = () => ({ stories: [STORY, 'user_stories/b.md'], neverSent: [STORY, 'user_stories/b.md'], noVerdict: [], failed: [], maintenance: false });
  story(w, 17); story(w, 17, 'user_stories/b.md');
  const { pr } = w.build(17, { body: `Fixes #17\n\nRuntime: PASS (${STORY}, 3/3 checks)\nRuntime: not run (user_stories/b.md: maintenance until 08:52 UTC)`, runtime: maintenance });
  await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  assert.deepEqual(w.job(17, 'runtime').args.slice(1), ['test', '--json', 'user_stories/b.md'], 'only the Story with a not-run line');
  answer(w, 17, 0, 'passed', ['b']); await w.tick();
  assert.equal(pr.body.match(/^Runtime:.*$/gm).join('|'), `Runtime: PASS (${STORY}, 3/3 checks)|Runtime: PASS (user_stories/b.md, 3/3 checks)`);
});

// #3241 case 1: a changed Story with no Runtime test is red, unless every changed prompt is native-only.
for (const [kind, red] of [['port', true], ['native-only', false]]) test(`case 1: a new Story with no Runtime test and a changed ${kind} prompt ${red ? 'is red' : 'is no such red'}`, async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17);
  await w.tick();
  const cwd = w.job(17, 'build').cwd;
  mkdirSync(join(cwd, 'user_stories'), { recursive: true }); mkdirSync(join(cwd, 'prompts'), { recursive: true });
  writeFileSync(join(cwd, 'user_stories/format-bytes.md'), 'As a person, I want bytes formatted, so that I can read them.\n\n## Acceptance criteria\n\n1. `format 1024` prints "1 KiB".\n');
  const block = kind === 'native-only' ? { status: 'draft', prose_sha256: '', kind: 'native-only', reason: 'it writes the real terminal' } : { status: 'draft', prose_sha256: '', entries: [], calls: [], resources: [], limits: { max_steps: 1, max_model_calls: 0 }, conventions: [] };
  writeFileSync(join(cwd, 'prompts/format.prompt.md'), `# Format\n\nFormat bytes.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(block)}\n\`\`\`\n\n</details>\n`);
  w.build(17, { body: 'Fixes #17\n\nRuntime: not run (user_stories/format-bytes.md: no Runtime test)', runtime: { state: 'not-run', kind: 'runtime', code: 'no-test', cause: 'no Runtime test' } });
  await w.tick();
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'a repair starts (the draft prompt also needs its approval)');
  const caseOne = /This PR changes user_stories\/format-bytes\.md, with no Runtime test: user_stories\/format-bytes\.md has no test: expected .*format-bytes\.json.* A missing test is not a reason for "Runtime: not run": write a Runtime test/;
  if (red) assert.match(repair.input, caseOne); else assert.doesNotMatch(repair.input, /with no Runtime test: /);
});
