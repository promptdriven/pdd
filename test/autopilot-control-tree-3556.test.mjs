// Behavioral tests for #3556: Autopilot Core controlTree old-code failure proof
// (Path b bug-fix enforcement, per-head enforcement with no latch bypass,
// per-file newly-added test checks, ordinary *.test.* execution, and import-error handling).
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { appendFileSync, mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { spawn } from 'node:child_process';
import { coreWorld } from './helpers/core-world.mjs';

const writeIn = (cwd, path, text) => {
  mkdirSync(join(cwd, path, '..'), { recursive: true });
  writeFileSync(join(cwd, path), text);
};

function seed(w, files) {
  const dir = join(w.dir, `seed-${Math.random().toString(36).slice(2)}`);
  w.git(w.dir, 'clone', '-q', w.remote, dir);
  for (const [path, text] of Object.entries(files)) writeIn(dir, path, text);
  w.git(dir, 'add', '.');
  w.git(dir, 'commit', '-qm', 'base');
  w.git(dir, 'push', '-q', 'origin', 'HEAD:main');
}

const endComments = (w, n) => w.comments(n).filter(body => body.includes('<!-- pdd:autopilot-core:end:'));
const mergeNote = pr => pr.comments.map(c => c.body).find(body => body.includes('<!-- pdd:autopilot-core:merge:')) ?? '';

function execReplayCommand(job) {
  const command = job.args.at(-3);
  return new Promise(done => {
    const child = spawn('/bin/bash', ['-c', command], {
      cwd: job.cwd,
      detached: true,
      env: { PATH: process.env.PATH, HOME: process.env.HOME, CI: 'true', LANG: 'C' },
    });
    let out = '';
    child.stdout.on('data', chunk => { out += chunk; });
    child.stderr.on('data', chunk => { out += chunk; });
    const timer = setTimeout(() => { try { process.kill(-child.pid, 'SIGKILL'); } catch {} }, 60_000);
    child.on('close', status => { clearTimeout(timer); done({ status, out }); });
  });
}

async function runRealVectors(w, issue = 17) {
  const job = w.job(issue, 'vectors');
  assert.ok(job, 'expected Autopilot to start a vectors/control run');
  const run = await execReplayCommand(job);
  appendFileSync(job.log, run.out);
  w.finish(issue, 'vectors', { code: run.status });
  await w.tick();
  return { job, run };
}

const PROMPT_PATH = 'prompts/duration.prompt.md';
const CODE_PATH = 'src/duration.mjs';
const BASE_PROMPT = '# Duration\n\nOwn `src/duration.mjs`.\n\n`seconds(n)` converts `n` seconds to minutes (`n / 60`).\n';
const BASE_CODE_BUGGY = `// Prompt: ${PROMPT_PATH}\nexport const seconds = n => n / 30;\n`;
const HEAD_CODE_FIXED = `// Prompt: ${PROMPT_PATH}\nexport const seconds = n => n / 60;\n`;
const PATH_B_LINE = `Path: b — ${CODE_PATH} — ${PROMPT_PATH} — no contract change — Test: test/regression.test.mjs`;
const EVIDENCE_LINE = 'Evidence: runtime=not-run; vectors=not-run; formal=not-applicable; tests=pass (2/2)';

async function startPathBWorld(t, { issue = {}, base = {}, change = {}, bodyExtra = '', result = {}, settings = {} } = {}) {
  const w = await coreWorld(t, { settings: { runs: 1, ...settings } });
  seed(w, { [PROMPT_PATH]: BASE_PROMPT, [CODE_PATH]: BASE_CODE_BUGGY, ...base });
  w.issue(17, issue);
  await w.tick();
  const cwd = w.job(17, 'build').cwd;
  for (const [file, text] of Object.entries(change)) writeIn(cwd, file, text);
  const pathD = Object.keys(change).filter(f => f !== CODE_PATH);
  const pathLines = [
    PATH_B_LINE,
    ...(pathD.length ? [`Path: d — ${pathD.join(', ')}, change-17.txt — unowned — no contract change — Test: done check`] : []),
  ].join('\n');
  const body = [
    'Fixes #17.',
    ...(bodyExtra ? [bodyExtra] : []),
    'Runtime: not run (no prompt changed)',
    EVIDENCE_LINE,
    pathLines,
  ].join('\n\n');
  const { pr, head } = w.build(17, { body, result: { promptChanged: false, evidence: EVIDENCE_LINE, ...result } });
  await w.tick();
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  return { w, pr, head, cwd, body };
}

test('3556-1 (Trap 1 & Trap 4): Path b code-only bug fix runs ordinary *.test.mjs on controlTree; vacuous test is RED across skill/label/title signals, genuine failing-on-base test is GREEN', async t => {
  const vacuousTest = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('vacuous', () => { assert.equal(typeof seconds(60), 'number'); });\n`;
  const genuineTest = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('60s is 1 min', () => { assert.equal(seconds(60), 1); });\n`;

  // 1a. Vacuous ordinary *.test.mjs caught on Path b via skill: 'pdd-bug', via bug label, and via bug issue title.
  const signals = [
    { name: 'skill=bug', issue: { title: 'Issue 17', body: 'Adjust duration.' }, result: { skill: 'pdd-bug' } },
    { name: 'label=bug', issue: { title: 'Duration output', body: 'See src/duration.mjs.', labels: ['bug'] }, result: {} },
    { name: 'issue context', issue: { title: 'Fix off-by-two bug in seconds()', body: 'seconds(60) returns wrong result 2 instead of 1.' }, result: {} },
  ];
  for (const sig of signals) {
    const { w } = await startPathBWorld(t, {
      issue: sig.issue,
      change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/regression.test.mjs': vacuousTest },
      result: sig.result,
    });
    const { job } = await runRealVectors(w);
    assert.deepEqual(w.replayFiles(job).map(f => f.kind), ['tests', 'control-tests'], `${sig.name}: runs ordinary test on head and control`);
    const repair = w.job(17, 'repair');
    assert.ok(repair, `${sig.name}: vacuous Path b bug fix triggers repair`);
    assert.match(repair.input, /Autopilot ran the regression tests of this change \(test\/regression\.test\.mjs\) on the merge-base code of the changed code files \(src\/duration\.mjs, merge base [0-9a-f]{7}\): all 1 pass there too, so they do not show the change/);
    assert.deepEqual(w.github.merges, [], `${sig.name}: vacuous PR must not merge`);
  }

  // 1b. Trap 4: Genuine Path b bug fix whose ordinary *.test.mjs fails on merge-base and passes on head -> GREEN.
  const { w, pr } = await startPathBWorld(t, {
    issue: { title: 'Fix off-by-two bug in seconds()', labels: ['bug'] },
    change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/regression.test.mjs': genuineTest },
    result: { skill: 'bug' },
  });
  await runRealVectors(w);
  await w.tick();
  assert.equal(w.job(17, 'repair'), undefined, w.job(17, 'repair')?.input);
  assert.deepEqual(w.github.merges, [pr.number], 'genuine Path b bug fix merges cleanly');
  assert.match(mergeNote(pr), /- Regression tests \(Autopilot's run at [0-9a-f]{7}\): pass \(1\/1\): test\/regression\.test\.mjs pass \(1\/1\)/);
  assert.match(mergeNote(pr), /- Control \(the same tests on the merge-base code of src\/duration\.mjs, merge base [0-9a-f]{7}\): 1 of 1 failed \(the tests show the change\)/);
});

test('3556-2 (Trap 2): per-head enforcement removes one-shot controlAsked latch bypass across repair commit #2 and maxRepairs: 0', async t => {
  const vacuous1 = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('vacuous v1', () => { assert.ok(seconds(60) > 0); });\n`;
  const vacuous2 = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('vacuous v2', () => { assert.ok(seconds(120) > 0); });\n`;

  // Commit #1 -> RED (starts repair #1).
  const { w, head: head1 } = await startPathBWorld(t, {
    issue: { title: 'Fix duration bug', labels: ['bug'] },
    change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/regression.test.mjs': vacuous1 },
    result: { skill: 'bug' },
  });
  await runRealVectors(w);
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'commit #1 vacuous test triggers repair #1');
  assert.equal(JSON.parse(readFileSync(join(w.root, 'jobs', '17.json'), 'utf8')).controlAsked, undefined, 'no one-shot controlAsked latch saved');

  // Commit #2 (repair pushes a DIFFERENT commit whose test STILL passes on merge-base) -> STILL RED, ends checks-red, never merges.
  writeIn(repair.cwd, 'test/regression.test.mjs', vacuous2);
  const { head: head2 } = w.build(17, { role: 'repair', result: { promptChanged: false, skill: 'bug', evidence: EVIDENCE_LINE } });
  assert.notEqual(head2, head1, 'repair pushed a new head commit #2');
  await w.tick();
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  await runRealVectors(w);

  assert.deepEqual(w.github.merges, [], 'repair commit #2 still passing on merge-base must NOT merge');
  assert.equal(endComments(w, 17).length, 1, 'job stops cleanly with END checks-red instead of latching past control');
  assert.match(endComments(w, 17)[0], /all 1 pass there too, so they do not show the change/);

  // Also verify maxRepairs: 0 does NOT silently bypass control and merge.
  const zero = await startPathBWorld(t, {
    issue: { title: 'Fix duration bug', labels: ['bug'] },
    change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/regression.test.mjs': vacuous1 },
    result: { skill: 'bug' },
    settings: { maxRepairs: 0 },
  });
  await runRealVectors(zero.w);
  assert.deepEqual(zero.w.github.merges, [], 'maxRepairs: 0 must not silently merge vacuous bug fix');
  assert.match(endComments(zero.w, 17)[0] ?? '', /safety cap of 0 repair\(s\) is reached/);
});

test('3556-3 (Trap 3): per-file evaluation flags newly added test file that passes on merge-base even when a modified test file fails on merge-base', async t => {
  const baseExisting = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('existing', () => { assert.equal(seconds(60), 2); });\n`;
  const modifiedExisting = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('existing updated', () => { assert.equal(seconds(60), 1); });\n`;
  const vacuousNew = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('vacuous new regression', () => { assert.ok(seconds(60) >= 1); });\n`;

  // 3a. Ordinary *.test.mjs: modified test/existing.test.mjs fails on base + newly added test/vacuous-new.test.mjs passes on base -> RED naming test/vacuous-new.test.mjs.
  const { w, head } = await startPathBWorld(t, {
    issue: { title: 'Fix seconds calculation bug', labels: ['bug'] },
    base: { 'test/existing.test.mjs': baseExisting },
    change: {
      [CODE_PATH]: HEAD_CODE_FIXED,
      'test/existing.test.mjs': modifiedExisting,
      'test/vacuous-new.test.mjs': vacuousNew,
    },
    result: { skill: 'bug' },
  });
  await runRealVectors(w);
  const repair = w.job(17, 'repair');
  assert.ok(repair, 'newly added vacuous test file must trigger repair even when modified test fails on base');
  assert.match(repair.input, /newly added test file\(s\) test\/vacuous-new\.test\.mjs passed on the merge-base code \(even though another test file failed there\)/);
  assert.doesNotMatch(repair.input, /Make test\/existing\.test\.mjs fail/);
  assert.deepEqual(w.github.merges, []);

  const record = JSON.parse(readFileSync(join(w.root, 'logs', `17-evidence-${head}.json`), 'utf8'));
  assert.equal(record.vectors.control.state, 'partial');
  assert.deepEqual(record.vectors.control.added, ['test/vacuous-new.test.mjs']);
  assert.deepEqual(record.vectors.control.addedPassed, ['test/vacuous-new.test.mjs']);

  // 3b. Same per-file rule holds for *.vectors.test.mjs as well.
  const vecClaim = 'Evidence: runtime=not-run; vectors=pass (2/2); formal=not-applicable; tests=pass (2/2)';
  const v = await coreWorld(t, { settings: { runs: 1 } });
  seed(v, {
    [PROMPT_PATH]: BASE_PROMPT,
    [CODE_PATH]: BASE_CODE_BUGGY,
    'test/existing.vectors.test.mjs': baseExisting,
  });
  v.issue(17, { title: 'Fix seconds vector bug', labels: ['bug'] });
  await v.tick();
  const vcwd = v.job(17, 'build').cwd;
  writeIn(vcwd, CODE_PATH, HEAD_CODE_FIXED);
  writeIn(vcwd, 'test/existing.vectors.test.mjs', modifiedExisting);
  writeIn(vcwd, 'test/vacuous-new.vectors.test.mjs', vacuousNew);
  v.build(17, {
    body: `Fixes #17.\n\nRuntime: not run (no prompt changed)\n${vecClaim}\nPath: b — ${CODE_PATH} — ${PROMPT_PATH} — no contract change — Test: test/existing.vectors.test.mjs\nPath: d — test/existing.vectors.test.mjs, test/vacuous-new.vectors.test.mjs, change-17.txt — unowned — no contract change — Test: done check`,
    result: { promptChanged: false, skill: 'bug', evidence: vecClaim },
  });
  await v.tick();
  v.review(17, 'PASS');
  v.suite(17, 0);
  await v.tick();
  await runRealVectors(v);
  assert.match(v.job(17, 'repair')?.input ?? '', /newly added test file\(s\) test\/vacuous-new\.vectors\.test\.mjs passed on the merge-base code/);
  assert.deepEqual(v.github.merges, []);
});

test('3556-4: Path b pure structural refactors stay exempt while negated refactor statements stay enforced', async t => {
  const passOnBoth = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('same behavior', () => { assert.equal(seconds(60), 2); });\n`;
  const refactoredSameBehavior = `// Prompt: ${PROMPT_PATH}\nconst DIVISOR = 30;\nexport const seconds = n => n / DIVISOR;\n`;

  // 4a. Explicitly declared behavior-preserving pure structural refactor on Path b -> exempt, merges cleanly.
  const pure = await startPathBWorld(t, {
    issue: { title: 'Refactor duration module', body: 'Extract divisor constant for readability.' },
    change: { [CODE_PATH]: refactoredSameBehavior, 'test/refactor.test.mjs': passOnBoth },
    bodyExtra: 'Behavior-preserving pure structural refactor; no behavior change.',
  });
  assert.equal(pure.w.job(17, 'vectors'), undefined, 'pure structural refactor does not run bug-fix ordinary test control');
  await pure.w.tick();
  assert.equal(pure.w.job(17, 'repair'), undefined, pure.w.job(17, 'repair')?.input);
  assert.deepEqual(pure.w.github.merges, [pure.pr.number]);

  // 4b. Even with a *.vectors.test.mjs, explicit pure structural refactor on Path b (non-bug-labeled issue) is exempt from control-same red.
  const vecClaim = 'Evidence: runtime=not-run; vectors=pass (1/1); formal=not-applicable; tests=pass (1/1)';
  const pureVec = await coreWorld(t, { settings: { runs: 1 } });
  seed(pureVec, { [PROMPT_PATH]: BASE_PROMPT, [CODE_PATH]: BASE_CODE_BUGGY });
  pureVec.issue(17, { title: 'Clean up duration helper', body: 'Simplify internal layout.' });
  await pureVec.tick();
  writeIn(pureVec.job(17, 'build').cwd, CODE_PATH, refactoredSameBehavior);
  writeIn(pureVec.job(17, 'build').cwd, 'test/duration.vectors.test.mjs', passOnBoth);
  const { pr: pureVecPr } = pureVec.build(17, {
    body: `Fixes #17.\n\nPure structural refactor (no behavior change).\n\nRuntime: not run (no prompt changed)\n${vecClaim}\nPath: b — ${CODE_PATH} — ${PROMPT_PATH} — no contract change — Test: test/duration.vectors.test.mjs\nPath: d — test/duration.vectors.test.mjs, change-17.txt — unowned — no contract change — Test: done check`,
    result: { promptChanged: false, evidence: vecClaim },
  });
  await pureVec.tick();
  pureVec.review(17, 'PASS');
  pureVec.suite(17, 0);
  await pureVec.tick();
  await runRealVectors(pureVec);
  await pureVec.tick();
  assert.equal(pureVec.job(17, 'repair'), undefined, pureVec.job(17, 'repair')?.input);
  assert.deepEqual(pureVec.github.merges, [pureVecPr.number]);

  // 4c. Negated refactor prose ("not a pure structural refactor") on a bug fix stays enforced -> RED.
  const vacuousTest = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('vacuous', () => { assert.ok(seconds(60) > 0); });\n`;
  const negated = await startPathBWorld(t, {
    issue: { title: 'Fix seconds bug', labels: ['bug'] },
    change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/regression.test.mjs': vacuousTest },
    bodyExtra: 'This is not a pure structural refactor; it fixes a real bug.',
    result: { skill: 'bug' },
  });
  await runRealVectors(negated.w);
  assert.ok(negated.w.job(17, 'repair'), 'negated refactor statement must NOT exempt bug fix');
  assert.deepEqual(negated.w.github.merges, []);

  // 4d. Authoritative precedence: bug-labeled issue CANNOT be bypassed by PR prose claiming pure refactor or scoped no-behavior-change.
  for (const bypassProse of [
    'Behavior-preserving pure structural refactor; no behavior change.',
    'Behavior-preserving refactor.',
    'no behavior change for other callers.',
  ]) {
    const labeled = await startPathBWorld(t, {
      issue: { title: 'Adjust duration helper', body: 'See src/duration.mjs.', labels: ['bug'] },
      change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/regression.test.mjs': vacuousTest },
      bodyExtra: bypassProse,
    });
    await runRealVectors(labeled.w);
    assert.ok(labeled.w.job(17, 'repair'), `bug label must override PR prose: ${bypassProse}`);
    assert.deepEqual(labeled.w.github.merges, []);
  }

  // 4e. Authoritative precedence: pdd-bug / bug skill CANNOT be bypassed by PR prose claiming pure refactor.
  for (const skill of ['bug', 'pdd-bug']) {
    const skilled = await startPathBWorld(t, {
      issue: { title: 'Adjust duration helper', body: 'See src/duration.mjs.' },
      change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/regression.test.mjs': vacuousTest },
      bodyExtra: 'Behavior-preserving pure structural refactor; no behavior change.',
      result: { skill },
    });
    await runRealVectors(skilled.w);
    assert.ok(skilled.w.job(17, 'repair'), `skill=${skill} must override PR prose`);
    assert.deepEqual(skilled.w.github.merges, []);
  }

  // 4f. Unlabeled bug issue & mixed bug+refactor PR prose CANNOT self-exempt via refactor/scoped-no-change prose.
  for (const [issue, prose] of [
    [{ title: 'Fix off-by-two in seconds()', body: 'seconds(60) returns wrong result 2.' }, 'Updated seconds(); no behavior change for other callers.'],
    [{ title: 'Fix off-by-two in seconds()', body: 'seconds(60) returns wrong result 2.' }, 'Updated seconds(); no behavior change to existing callers.'],
    [{ title: 'Fix off-by-two in seconds()', body: 'seconds(60) returns wrong result 2.' }, 'Updated seconds(); no behavior change outside error paths.'],
    [{ title: 'Fix off-by-two in seconds()', body: 'seconds(60) returns wrong result 2.' }, 'Fixed seconds(); no behavior change elsewhere.'],
    [{ title: 'Fix off-by-two in seconds()', body: 'seconds(60) returns wrong result 2.' }, 'Fixed seconds(); no behavior change otherwise.'],
    [{ title: 'Fix off-by-two in seconds()', body: 'seconds(60) returns wrong result 2.' }, 'Updated seconds(); no behavior change aside from 60s handling.'],
    [{ title: 'Fix off-by-two in seconds()', body: 'seconds(60) returns wrong result 2.' }, 'Updated seconds(); no behavior change other than 60s handling.'],
    [{ title: 'Fix off-by-two in seconds()', body: 'seconds(60) returns wrong result 2.' }, 'Updated seconds(); no behavior change apart from 60s handling.'],
    [{ title: 'Fix off-by-two in seconds()', body: 'seconds(60) returns wrong result 2.' }, 'Updated seconds(); no behavior change beyond 60s handling.'],
    [{ title: 'Fix off-by-two bug in seconds()', body: 'seconds(60) returns 2 instead of 1.' }, 'Behavior-preserving pure structural refactor; no behavior change.'],
    [{ title: 'Duration helper', body: 'Steps to reproduce: seconds(60) returns wrong result 2; actual behavior is 2, expected behavior is 1.' }, 'Behavior-preserving pure structural refactor; no behavior change.'],
    [{ title: 'Duration helper', body: 'Steps to reproduce: seconds(60) fails when input is 60.' }, 'Internal refactor of helper while adjusting seconds().'],
    [{ title: 'Duration helper', body: 'See src/duration.mjs.' }, 'Bug fix for seconds(). Pure structural refactor.'],
    [{ title: 'Duration helper', body: 'See src/duration.mjs.' }, 'Internal refactor of helper and fixed the seconds() bug.'],
    [{ title: 'Duration helper', body: 'See src/duration.mjs.' }, 'Fix crash in seconds(); pure refactor of helper.'],
    [{ title: 'Duration helper', body: 'See src/duration.mjs.' }, 'Reproduces the crash in seconds(); internal refactor.'],
  ]) {
    const scoped = await startPathBWorld(t, {
      issue,
      change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/regression.test.mjs': vacuousTest },
      bodyExtra: prose,
    });
    await runRealVectors(scoped.w);
    assert.ok(scoped.w.job(17, 'repair'), `must not exempt: ${issue.title} | ${prose}`);
    assert.deepEqual(scoped.w.github.merges, []);
  }
});

test('3556-5: controlTree distinguishes missing-module/export import errors (no noisy false positives) while still catching separate vacuous newly added tests', async t => {
  const newHelper = 'export const normalizeSeconds = n => Math.max(0, n);\n';
  const headCodeWithNewExport = `// Prompt: ${PROMPT_PATH}\nimport { normalizeSeconds } from './duration-helper.mjs';\nexport const seconds = n => normalizeSeconds(n) / 60;\nexport const minutesFromSeconds = seconds;\n`;
  const helperTest = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { normalizeSeconds } from '../src/duration-helper.mjs';\nimport { minutesFromSeconds } from '../src/duration.mjs';\ntest('uses new helper and export', () => { assert.equal(normalizeSeconds(-5), 0); assert.equal(minutesFromSeconds(60), 1); });\n`;
  const vacuousExtra = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('vacuous', () => { assert.equal(typeof seconds(60), 'number'); });\n`;

  // 5a. Test importing a brand-new helper module absent on merge-base -> state 'import-error', NO false-positive red, merges cleanly.
  const ok = await startPathBWorld(t, {
    issue: { title: 'Fix negative duration bug', labels: ['bug'] },
    change: {
      [CODE_PATH]: headCodeWithNewExport,
      'src/duration-helper.mjs': newHelper,
      'test/duration-helper.test.mjs': helperTest,
    },
    result: { skill: 'bug' },
  });
  await runRealVectors(ok.w);
  await ok.w.tick();
  assert.equal(ok.w.job(17, 'repair'), undefined, ok.w.job(17, 'repair')?.input);
  assert.deepEqual(ok.w.github.merges, [ok.pr.number], 'import-error on brand-new helper module does not cause false-positive red');
  const okRecord = JSON.parse(readFileSync(join(ok.w.root, 'logs', `17-evidence-${ok.head}.json`), 'utf8'));
  assert.equal(okRecord.vectors.control.state, 'import-error');
  assert.deepEqual(okRecord.vectors.control.importErrors, ['test/duration-helper.test.mjs']);
  assert.match(mergeNote(ok.pr), /1 of 1 could not load on merge-base \(missing new module or export\)/);

  // 5b. Test importing a brand-new named export from an existing base module -> SyntaxError import-error, NO false-positive red.
  const exportOnlyCode = `// Prompt: ${PROMPT_PATH}\nexport const seconds = n => n / 60;\nexport const minutesFromSeconds = seconds;\n`;
  const exportOnlyTest = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { minutesFromSeconds } from '../src/duration.mjs';\ntest('uses new named export', () => { assert.equal(minutesFromSeconds(60), 1); });\n`;
  const expOk = await startPathBWorld(t, {
    issue: { title: 'Fix seconds export bug', labels: ['bug'] },
    change: {
      [CODE_PATH]: exportOnlyCode,
      'test/new-export.test.mjs': exportOnlyTest,
    },
    result: { skill: 'bug' },
  });
  await runRealVectors(expOk.w);
  await expOk.w.tick();
  assert.equal(expOk.w.job(17, 'repair'), undefined, expOk.w.job(17, 'repair')?.input);
  assert.deepEqual(expOk.w.github.merges, [expOk.pr.number], 'missing named export on merge-base does not cause false-positive red');
  const expRecord = JSON.parse(readFileSync(join(expOk.w.root, 'logs', `17-evidence-${expOk.head}.json`), 'utf8'));
  assert.equal(expRecord.vectors.control.state, 'import-error');
  assert.deepEqual(expRecord.vectors.control.importErrors, ['test/new-export.test.mjs']);

  // 5c. Brand-new helper test (import-error) + separate newly added vacuous test (pass on base) -> STILL RED naming ONLY the vacuous file.
  const mixed = await startPathBWorld(t, {
    issue: { title: 'Fix negative duration bug', labels: ['bug'] },
    change: {
      [CODE_PATH]: headCodeWithNewExport,
      'src/duration-helper.mjs': newHelper,
      'test/duration-helper.test.mjs': helperTest,
      'test/vacuous-extra.test.mjs': vacuousExtra,
    },
    result: { skill: 'bug' },
  });
  await runRealVectors(mixed.w);
  const repair = mixed.w.job(17, 'repair');
  assert.ok(repair, 'import-error in one file must not mask vacuous newly added file');
  assert.match(repair.input, /newly added test file\(s\) test\/vacuous-extra\.test\.mjs passed on the merge-base code/);
  assert.doesNotMatch(repair.input, /Make test\/duration-helper\.test\.mjs fail/);
  assert.deepEqual(mixed.w.github.merges, []);
});

test('3556-6: non-node:test ordinary test files are skipped silently without notRunReds; failing ordinary regression test on head is red', async t => {
  // 6a. Jest-style ordinary test file (no node:test) does not trigger skipped/notRunReds.
  const nonNode = await startPathBWorld(t, {
    issue: { title: 'Fix seconds bug', labels: ['bug'] },
    change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/jest.test.js': 'expect(1).toBe(1);\n' },
    result: { skill: 'bug' },
  });
  assert.equal(nonNode.w.job(17, 'vectors'), undefined, 'non-node:test ordinary test file spawns no replay process');
  await nonNode.w.tick();
  assert.equal(nonNode.w.job(17, 'repair'), undefined, nonNode.w.job(17, 'repair')?.input);
  assert.deepEqual(nonNode.w.github.merges, [nonNode.pr.number]);

  // 6b. Ordinary regression test that fails on head is flagged red directly.
  const brokenHead = await startPathBWorld(t, {
    issue: { title: 'Fix seconds bug', labels: ['bug'] },
    change: {
      [CODE_PATH]: HEAD_CODE_FIXED,
      'test/broken.test.mjs': `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('broken on head', () => { assert.equal(seconds(60), 999); });\n`,
    },
    result: { skill: 'bug' },
  });
  await runRealVectors(brokenHead.w);
  assert.match(brokenHead.w.job(17, 'repair')?.input ?? '', /Autopilot ran the regression tests that this change touches \(test\/broken\.test\.mjs\) at head [0-9a-f]{7}: 1 of 1 failed: broken on head/);
  assert.deepEqual(brokenHead.w.github.merges, []);
});

test('3556-7: legitimate Path b pure refactors with incidental cleanup/preventive/exempt wording stay exempt (no false positives)', async t => {
  const refactoredSameBehavior = `// Prompt: ${PROMPT_PATH}\nconst DIVISOR = 30;\nexport const seconds = n => n / DIVISOR;\n`;
  const passOnBoth = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('same behavior', () => { assert.equal(seconds(60), 2); });\n`;

  const healthyRefactors = [
    { title: 'refactor: clean up fix from #123', body: 'Tidy helper left over from earlier fix.' },
    { title: 'Refactor duration helper to avoid a bug', body: 'Extract helper function to avoid future bugs.' },
    { title: 'Extract constant; expected behavior stays identical with no regression', body: 'Expected behavior stays identical with no regression.' },
    { title: 'chore: simplify exempt list', body: 'Simplify exempt and bypass lists.' },
    { title: 'Split duration module', body: 'Reorganize code after previous bug.', labels: ['refactor'] },
  ];
  for (const issue of healthyRefactors) {
    const { w, pr } = await startPathBWorld(t, {
      issue,
      change: { [CODE_PATH]: refactoredSameBehavior, 'test/refactor.test.mjs': passOnBoth },
    });
    assert.equal(w.job(17, 'vectors'), undefined, `healthy refactor must not trigger bug-fix control run: ${issue.title}`);
    await w.tick();
    assert.equal(w.job(17, 'repair'), undefined, `${issue.title}: ${w.job(17, 'repair')?.input}`);
    assert.deepEqual(w.github.merges, [pr.number], `healthy refactor merges cleanly: ${issue.title}`);
  }
});

test('3556-8: Git rename detection (-M50%) cannot mask a newly added vacuous test file sharing boilerplate with a deleted test', async t => {
  const sharedBoilerplate = [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import { seconds } from '../src/duration.mjs';",
    'const FIXTURE_A = 60;',
    'const FIXTURE_B = 120;',
    'const FIXTURE_C = 180;',
    'const FIXTURE_D = 240;',
    'const FIXTURE_E = 300;',
    'const helperCheck = value => typeof value === "number" && Number.isFinite(value);',
    'const positiveCheck = value => helperCheck(value) && value > 0;',
  ].join('\n');
  const oldDeletedTest = `${sharedBoilerplate}\ntest('old test', () => { assert.ok(positiveCheck(seconds(FIXTURE_A))); });\n`;
  const newVacuousTest = `${sharedBoilerplate}\ntest('new vacuous test', () => { assert.ok(positiveCheck(seconds(FIXTURE_B))); });\n`;
  const baseExisting = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('existing', () => { assert.equal(seconds(60), 2); });\n`;
  const modifiedExisting = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('existing updated', () => { assert.equal(seconds(60), 1); });\n`;

  const w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, {
    [PROMPT_PATH]: BASE_PROMPT,
    [CODE_PATH]: BASE_CODE_BUGGY,
    'test/existing.test.mjs': baseExisting,
    'test/old-removed.test.mjs': oldDeletedTest,
  });
  w.issue(17, { title: 'Fix seconds calculation bug', labels: ['bug'] });
  await w.tick();
  const cwd = w.job(17, 'build').cwd;
  writeIn(cwd, CODE_PATH, HEAD_CODE_FIXED);
  writeIn(cwd, 'test/existing.test.mjs', modifiedExisting);
  w.git(cwd, 'rm', '-q', 'test/old-removed.test.mjs');
  writeIn(cwd, 'test/new-vacuous.test.mjs', newVacuousTest);
  const body = `Fixes #17.\n\nRuntime: not run (no prompt changed)\n${EVIDENCE_LINE}\n${PATH_B_LINE}\nPath: d — test/existing.test.mjs, test/old-removed.test.mjs, test/new-vacuous.test.mjs, change-17.txt — unowned — no contract change — Test: done check`;
  const { head } = w.build(17, { body, result: { promptChanged: false, skill: 'bug', evidence: EVIDENCE_LINE } });

  // Prove Git's default diff actually classifies test/new-vacuous.test.mjs as a rename (R..), NOT status A!
  const diffStatus = w.git(cwd, 'diff', '--name-status', 'origin/main...HEAD');
  assert.match(diffStatus, /^R\d+\ttest\/old-removed\.test\.mjs\ttest\/new-vacuous\.test\.mjs$/m, `expected git rename detection in fixture:\n${diffStatus}`);

  await w.tick();
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  await runRealVectors(w);

  const repair = w.job(17, 'repair');
  assert.ok(repair, 'rename-masked newly added vacuous test file must still trigger repair');
  assert.match(repair.input, /newly added test file\(s\) test\/new-vacuous\.test\.mjs passed on the merge-base code/);
  assert.deepEqual(w.github.merges, []);
  const record = JSON.parse(readFileSync(join(w.root, 'logs', `17-evidence-${head}.json`), 'utf8'));
  assert.equal(record.vectors.control.state, 'partial');
  assert.deepEqual(record.vectors.control.added, ['test/new-vacuous.test.mjs']);
  assert.deepEqual(record.vectors.control.addedPassed, ['test/new-vacuous.test.mjs']);
});

test('3556-9: conditionally empty test (exits 0 with 0 tests on merge-base while passing on head) is flagged RED', async t => {
  const headWithFlag = `// Prompt: ${PROMPT_PATH}\nexport const FIXED_V2 = true;\nexport const seconds = n => n / 60;\n`;
  const condEmptyTest = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport * as duration from '../src/duration.mjs';\nif (duration.FIXED_V2) {\n  test('only runs on head', () => { assert.equal(duration.seconds(60), 1); });\n}\n`;
  const baseExisting = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('existing', () => { assert.equal(seconds(60), 2); });\n`;
  const modifiedExisting = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('existing updated', () => { assert.equal(seconds(60), 1); });\n`;

  // 9a. Single newly added conditionally-empty test file -> RED (never silently passes as unclear).
  const solo = await startPathBWorld(t, {
    issue: { title: 'Fix seconds bug', labels: ['bug'] },
    change: { [CODE_PATH]: headWithFlag, 'test/cond-empty.test.mjs': condEmptyTest },
    result: { skill: 'bug' },
  });
  await runRealVectors(solo.w);
  assert.match(solo.w.job(17, 'repair')?.input ?? '', /newly added test file\(s\) test\/cond-empty\.test\.mjs ran 0 tests \(exited 0 with no test result\) on the merge-base code/);
  assert.deepEqual(solo.w.github.merges, []);
  const soloRecord = JSON.parse(readFileSync(join(solo.w.root, 'logs', `17-evidence-${solo.head}.json`), 'utf8'));
  assert.equal(soloRecord.vectors.control.state, 'partial');
  assert.deepEqual(soloRecord.vectors.control.addedEmpty, ['test/cond-empty.test.mjs']);

  // 9b. Paired with a modified failing test -> STILL RED naming test/cond-empty.test.mjs.
  const paired = await startPathBWorld(t, {
    issue: { title: 'Fix seconds bug', labels: ['bug'] },
    base: { 'test/existing.test.mjs': baseExisting },
    change: { [CODE_PATH]: headWithFlag, 'test/existing.test.mjs': modifiedExisting, 'test/cond-empty.test.mjs': condEmptyTest },
    result: { skill: 'bug' },
  });
  await runRealVectors(paired.w);
  assert.match(paired.w.job(17, 'repair')?.input ?? '', /newly added test file\(s\) test\/cond-empty\.test\.mjs ran 0 tests \(exited 0 with no test result\) on the merge-base code \(even though another test file failed there\)/);
  assert.deepEqual(paired.w.github.merges, []);
});

test('3556-10: test titles or bare stdout mentioning ERR_MODULE_NOT_FOUND are NOT misclassified as import-error', async t => {
  // 10a. Real failing test whose title mentions ERR_MODULE_NOT_FOUND -> control.state is 'shows' (actual test failure, not import-error).
  const titleTest = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('returns ERR_MODULE_NOT_FOUND on bad input', () => { assert.equal(seconds(60), 1); });\n`;
  const a = await startPathBWorld(t, {
    issue: { title: 'Fix seconds bug', labels: ['bug'] },
    change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/title-err.test.mjs': titleTest },
    result: { skill: 'bug' },
  });
  await runRealVectors(a.w);
  await a.w.tick();
  const aRecord = JSON.parse(readFileSync(join(a.w.root, 'logs', `17-evidence-${a.head}.json`), 'utf8'));
  assert.equal(aRecord.vectors.control.state, 'shows');
  assert.equal(aRecord.vectors.control.importErrors, undefined);
  assert.equal(aRecord.vectors.kinds['control-tests'].files[0].state, 'fail');

  // 10b. File that logs bare 'ERR_MODULE_NOT_FOUND' and exits 1 before TAP summary -> NOT misclassified as import-error.
  const bareStdout = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\nif (seconds(60) !== 1) { console.log('ERR_MODULE_NOT_FOUND'); process.exit(1); }\ntest('ok on head', () => { assert.equal(seconds(60), 1); });\n`;
  const b = await startPathBWorld(t, {
    issue: { title: 'Fix seconds bug', labels: ['bug'] },
    change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/bare-stdout.test.mjs': bareStdout },
    result: { skill: 'bug' },
  });
  await runRealVectors(b.w);
  await b.w.tick();
  const bRecord = JSON.parse(readFileSync(join(b.w.root, 'logs', `17-evidence-${b.head}.json`), 'utf8'));
  assert.equal(bRecord.vectors.control.state, 'shows');
  assert.equal(bRecord.vectors.control.importErrors, undefined);
  assert.equal(bRecord.vectors.kinds['control-tests'].files[0].state, 'fail');
});

test('3556-11 (REPAIR-SKILL-DOWNGRADE): monotonic job.skill prevents a repair agent from downgrading bug -> feature/small-change to bypass controlTree', async t => {
  const vacuous1 = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('vacuous v1', () => { assert.ok(seconds(60) > 0); });\n`;
  const vacuous2 = `import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { seconds } from '../src/duration.mjs';\ntest('vacuous v2', () => { assert.ok(seconds(120) > 0); });\n`;

  for (const downgradedSkill of ['feature', 'small-change']) {
    // Neutral unlabeled issue where ONLY job.skill='bug' from build established bug-fix status.
    const { w } = await startPathBWorld(t, {
      issue: { title: 'Duration helper update', body: 'Update src/duration.mjs.' },
      change: { [CODE_PATH]: HEAD_CODE_FIXED, 'test/regression.test.mjs': vacuous1 },
      result: { skill: 'bug' },
    });
    await runRealVectors(w);
    const repair = w.job(17, 'repair');
    assert.ok(repair, `commit #1 triggers repair before ${downgradedSkill} downgrade attempt`);

    // Repair tries to downgrade job.skill to 'feature'/'small-change' AND rewrite PR body to claim pure refactor.
    writeIn(repair.cwd, 'test/regression.test.mjs', vacuous2);
    const bypassBody = [
      'Fixes #17.',
      'Behavior-preserving refactor.',
      'Runtime: not run (no prompt changed)',
      EVIDENCE_LINE,
      PATH_B_LINE,
      'Path: d — test/regression.test.mjs, change-17.txt — unowned — no contract change — Test: done check',
    ].join('\n\n');
    w.build(17, { role: 'repair', body: bypassBody, result: { promptChanged: false, skill: downgradedSkill, evidence: EVIDENCE_LINE } });
    await w.tick();
    assert.equal(JSON.parse(readFileSync(join(w.root, 'jobs', '17.json'), 'utf8')).skill, 'bug', `job.skill remains bug despite repair returning ${downgradedSkill}`);
    w.review(17, 'PASS');
    w.suite(17, 0);
    await w.tick();
    await runRealVectors(w);

    assert.deepEqual(w.github.merges, [], `downgrading skill to ${downgradedSkill} + pure refactor prose must NOT bypass controlTree`);
    assert.equal(endComments(w, 17).length, 1, 'job stops with END checks-red');
    assert.match(endComments(w, 17)[0], /all 1 pass there too, so they do not show the change/);
  }
});
