// Regression tests for the 0.1.29 evidence review (T01, T04, T08, T09): each one failed on 9ee9e51fc.
import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdirSync, readFileSync, writeFileSync, appendFileSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { coreWorld } from './helpers/core-world.mjs';
import { fakeRuntime, portsFor } from './runtime-fake.mjs';
import * as runtime from '../src/runtime-client.mjs';

const writeIn = (cwd, path, text) => { mkdirSync(join(cwd, path, '..'), { recursive: true }); writeFileSync(join(cwd, path), text); };
const endComments = (w, n) => w.comments(n).filter(body => body.includes('<!-- pdd:autopilot-core:end:'));
const mergeNote = pr => pr.comments.map(c => c.body).find(body => body.includes('<!-- pdd:autopilot-core:merge:')) ?? '';
const nodeTest = name => `import test from 'node:test';\ntest(${JSON.stringify(name)}, () => {});\n`;
const finishChecks = async w => { w.review(17, 'PASS'); w.suite(17, 0); await w.tick(); };
// Many base files in one commit.
function seed(w, files) {
  const dir = join(w.dir, `seed-${Math.random().toString(36).slice(2)}`); w.git(w.dir, 'clone', '-q', w.remote, dir);
  for (const [path, text] of Object.entries(files)) writeIn(dir, path, text);
  w.git(dir, 'add', '.'); w.git(dir, 'commit', '-qm', 'base'); w.git(dir, 'push', '-q', 'origin', 'HEAD:main');
}

// ---- T01: the saved checks must cover the change ----------------------------------------------------------
const STORY = 'user_stories/package-repository.md', STORIES = [STORY, 'user_stories/format-percent.md'], PROMPT = 'prompts/package.prompt.md';
const BODY = `Fixes #17.\n\nRuntime: PASS\nPath: a — ${PROMPT} — ${PROMPT} — prompt changed — Test: done check\nPath: d — ${STORY}, change-17.txt — unowned — no contract change — Test: done check`;
async function t01World(t, evidence, { body = BODY, result = {} } = {}) {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, { [PROMPT]: '# Package\n\nRead the package name.\n', [STORY]: '# Package repository\n\nThe package names its repository.\n' });
  w.issue(17); await w.tick();
  const cwd = w.job(17, 'build').cwd;
  writeIn(cwd, PROMPT, '# Package\n\nRead the package name and its repository.\n');
  writeIn(cwd, STORY, '# Package repository\n\nThe package names its repository URL.\n');
  w.runtimeEvidence = evidence;
  const { pr, head } = w.build(17, { body, result });
  await w.tick();
  return { w, pr, head, cwd };
}

test('E01 (MF1, Codex 4) a repair that only runs pdd test again at the same head clears a stale T01 red; the PR merges', async t => {
  let current = false;
  const { w, pr, head } = await t01World(t, async () => ({ stories: [{ story: STORY, pass: true, current }], storyFiles: STORIES, footprints: { [STORY]: [PROMPT] } }));
  assert.match(w.job(17, 'repair').input, /a stale Runtime batch/);
  current = true;                                                    // pdd test saved a check of this source, outside the repository
  assert.equal(w.build(17, { role: 'repair', write: false }).head, head);
  await w.tick(); await finishChecks(w); await w.tick();
  assert.deepEqual({ merges: w.github.merges, ended: endComments(w, 17).length }, { merges: [pr.number], ended: 0 });
});

test('E02 (MF6, Codex 3) the latest check of a Story at this source decides: a newer fail, a newer no-verdict or a tie with a fail is not a pass', async t => {
  for (const rows of [
    [{ story: STORY, pass: true, current: true, at: 1000 }, { story: STORY, pass: false, current: true, at: 2000 }],
    [{ story: STORY, pass: true, current: true, at: 1000 }, { story: STORY, pass: false, result: 'no verdict', current: true, at: 3000 }],
    [{ story: STORY, pass: true, current: true, at: 1000 }, { story: STORY, pass: false, current: true, at: 1000 }],
  ]) {
    const { w } = await t01World(t, async () => ({ stories: rows, storyFiles: STORIES, footprints: { [STORY]: [PROMPT] } }));
    assert.match(w.job(17, 'repair')?.input ?? '', /the latest check of user_stories\/package-repository\.md at this source did not pass/, JSON.stringify(rows));
  }
  // An older failure and a newer pass of the same source: covered.
  const { w, pr } = await t01World(t, async () => ({ stories: [{ story: STORY, pass: false, current: true, at: 1000 }, { story: STORY, pass: true, current: true, at: 2000 }], storyFiles: STORIES, footprints: { [STORY]: [PROMPT] } }));
  assert.equal(w.job(17, 'repair'), undefined); await finishChecks(w); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
});

test('E03 (MF3, Codex 2) every positive Runtime claim is checked: an Evidence runtime=pass alone, a result runtime pass; Git decides that a prompt changed', async t => {
  // 1. No Runtime line, promptChanged false, a changed Story, "Evidence: runtime=pass (3/3)" and no saved check.
  const evidence = 'Evidence: runtime=pass (3/3); vectors=not-run; formal=not-applicable; tests=pass (3/3)';
  let w = await coreWorld(t, { settings: { runs: 1 } });
  w.baseCommit(STORY, '# Package repository\n\nThe package names its repository.\n');
  w.issue(17); await w.tick();
  writeIn(w.job(17, 'build').cwd, STORY, '# Package repository\n\nThe package names its repository URL.\n');
  w.runtimeEvidence = async () => ({ stories: [], storyFiles: STORIES, footprints: {} });
  w.build(17, { body: `Fixes #17.\n\n${evidence}\nPath: d — ${STORY}, change-17.txt — unowned — no contract change — Test: done check`, result: { promptChanged: false, evidence } });
  await w.tick();
  assert.match(w.job(17, 'repair')?.input ?? '', /The Evidence line says runtime=pass, but the saved pdd test checks at head [0-9a-f]{7} do not cover user_stories\/package-repository\.md/);
  assert.deepEqual(w.github.merges, []);
  // 2. A changed prompt, no Runtime line, promptChanged false, a result runtime pass: the missing line is red (Git says
  // a prompt changed), and the coverage reader is asked.
  w = await coreWorld(t, { settings: { runs: 1 } });
  w.baseCommit(PROMPT, '# Package\n\nRead the package name.\n');
  w.issue(17); await w.tick();
  writeIn(w.job(17, 'build').cwd, PROMPT, '# Package\n\nRead the package name and its repository.\n');
  const reads = []; w.runtimeEvidence = async input => { reads.push(input); return { stories: [], storyFiles: [], footprints: {} }; };
  w.build(17, { body: `Fixes #17.\n\nEvidence: runtime=pass (9/9)\nPath: a — ${PROMPT} — ${PROMPT} — prompt changed — Test: done check`, result: { promptChanged: false, runtime: { state: 'pass' } } });
  await w.tick();
  const input = w.job(17, 'repair')?.input ?? '';
  assert.match(input, /The PR body has no Runtime line, but this PR changes prompts\/package\.prompt\.md/);
  assert.deepEqual(w.github.merges, []);
});

test('E04 (MF4) a changed Runtime test file is a change of its Story: it needs a passing check at this source', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, { [STORY]: '# Package repository\n\n## Acceptance criteria\n\n- AC1: The repository is shown.\n',
    'tests/package-repository.json': JSON.stringify({ story_path: STORY, steps: [{ id: 's1', input: { name: 'a' }, checks: [{ criterion_id: 'AC1', op: 'equals', value: 'x' }] }] }, null, 2) + '\n' });
  w.issue(17); await w.tick();
  writeIn(w.job(17, 'build').cwd, 'tests/package-repository.json', JSON.stringify({ story_path: STORY, steps: [{ id: 's1', input: { name: 'b' }, checks: [{ criterion_id: 'AC1', op: 'equals', value: 'y' }] }] }, null, 2) + '\n');
  w.build(17, { body: 'Fixes #17.\n\nRuntime: PASS\nPath: d — tests/package-repository.json, change-17.txt — unowned — no contract change — Test: done check' });
  await w.tick({ runtimeEvidence: undefined });                      // the real reader: findTests, savedStoryEvidence, captureSource
  assert.match(w.job(17, 'repair')?.input ?? '', /do not cover user_stories\/package-repository\.md/);
  assert.deepEqual(w.github.merges, []);
});

test('E05 (M17) two changed Stories: each one needs its own passing check', async t => {
  const other = 'user_stories/format-percent.md';
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, { [STORY]: '# A\n\nOne.\n', [other]: '# B\n\nTwo.\n' });
  w.issue(17); await w.tick();
  const cwd = w.job(17, 'build').cwd;
  writeIn(cwd, STORY, '# A\n\nOne more.\n'); writeIn(cwd, other, '# B\n\nTwo more.\n');
  // The first changed Story (by name) passed; the second did not.
  w.runtimeEvidence = async () => ({ stories: [{ story: other, pass: true, current: true }], storyFiles: STORIES, footprints: {} });
  w.build(17, { body: `Fixes #17.\n\nRuntime: PASS\nPath: d — ${STORY}, ${other}, change-17.txt — unowned — no contract change — Test: done check` });
  await w.tick();
  assert.match(w.job(17, 'repair')?.input ?? '', /do not cover user_stories\/package-repository\.md\b/);
  assert.doesNotMatch(w.job(17, 'repair').input, /do not cover user_stories\/format-percent\.md/);
});

test('E06 (MF5, Codex 1) the reader compares the saved checks with a clean checkout of the agent head, not the job worktree', async t => {
  const reads = [];
  const { w, head, cwd } = await t01World(t, async input => { reads.push(input); return { stories: [{ story: STORY, pass: true, current: true }], storyFiles: STORIES, footprints: { [STORY]: [PROMPT] } }; });
  assert.equal(reads.length, 1);
  const [{ root, tree, head: at }] = reads;
  assert.equal(root, cwd); assert.notEqual(tree, cwd); assert.equal(at, head);
  assert.equal(w.git(tree, 'rev-parse', 'HEAD'), head);
  assert.equal(w.git(tree, 'status', '--porcelain', '--untracked-files=all'), '', 'the clean checkout has only the committed files');
});

// A real pdd test run against a fake Runtime: it saves a real batch and receipts in PDD_STATE_DIR for the worktree.
const HARBOR = fileURLToPath(new URL('./fixtures/harbor/', import.meta.url));
const harbor = (extra = {}) => ({ ...Object.fromEntries(['prompts/place_order.prompt.md', 'user_stories/place-order.md', 'tests/place-order.json', 'user_stories/unknown-item.md', 'tests/unknown-item.json']
  .map(path => [path, readFileSync(join(HARBOR, path), 'utf8')])), ...extra });
async function pddTest(t, w, cwd, words) {
  const state = join(w.dir, 'runtime-state'), home = join(w.dir, 'runtime-home'); mkdirSync(home, { recursive: true });
  const checks = JSON.parse(readFileSync(join(HARBOR, 'tests/place-order.json'), 'utf8')).steps[0].checks.map(check => ({ ...check, expected: check.value, actual: check.value, passed: true }));
  const fake = await fakeRuntime(t, (entry, server) => {
    if (entry.command === 'lint') return { status: 200, json: server.lint(entry.request.requestId) };
    return { status: 200, json: server.check(entry.request?.requestId ?? entry.url.split('/').at(-1), 'passed', checks) };
  });
  const { ports } = portsFor({ HOME: home, PATH: process.env.PATH, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin }, { now: Date.now, sleep: ms => new Promise(done => setTimeout(done, ms)) });
  assert.equal(await runtime.runCheck({ words, options: { '--json': true }, cwd }, ports), 0, ports.stderr.text + ports.stdout.text);
  return { ...process.env, PDD_STATE_DIR: state };
}
const PLACE_STORY = 'user_stories/place-order.md';
const placeStory = more => `${readFileSync(join(HARBOR, PLACE_STORY), 'utf8').replace('so that I know my total\nbefore I pay.', `so that I know my total\nbefore I pay.${more}`)}`;

test('E07 (MF5, Codex 1, real saved checks) a pass of uncommitted Story text is red; the same check of the committed head merges', async t => {
  // The positive case: pdd test of the committed change.
  let w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, harbor()); w.issue(17); await w.tick();
  let cwd = w.job(17, 'build').cwd;
  writeIn(cwd, PLACE_STORY, placeStory(' Pickup is at the counter.'));
  w.git(cwd, 'add', '.'); w.git(cwd, 'commit', '-qm', 'story');
  let env = await pddTest(t, w, cwd, ['place-order']);
  const body = `Fixes #17.\n\nRuntime: PASS\nPath: d — ${PLACE_STORY}, change-17.txt — unowned — no contract change — Test: done check`;
  let { pr } = w.build(17, { body });
  await w.tick({ runtimeEvidence: undefined, env });
  assert.equal(w.job(17, 'repair'), undefined, w.job(17, 'repair')?.input);
  w.review(17, 'PASS'); w.suite(17, 0); await w.tick({ runtimeEvidence: undefined, env }); await w.tick({ runtimeEvidence: undefined, env });
  assert.deepEqual(w.github.merges, [pr.number]);
  // The agent commits one Story text, runs pdd test with more text on disk, and pushes only the commit.
  w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, harbor()); w.issue(17); await w.tick();
  cwd = w.job(17, 'build').cwd;
  writeIn(cwd, PLACE_STORY, placeStory(' Pickup is at the counter.'));
  w.git(cwd, 'add', '.'); w.git(cwd, 'commit', '-qm', 'story');
  writeIn(cwd, PLACE_STORY, placeStory(' Pickup is at the counter, with a receipt.'));   // never committed
  env = await pddTest(t, w, cwd, ['place-order']);
  ({ pr } = w.build(17, { body, write: false, add: false }));
  assert.match(w.git(cwd, 'status', '--porcelain'), /place-order\.md/, 'the worktree still has the uncommitted text');
  await w.tick({ runtimeEvidence: undefined, env });
  assert.match(w.job(17, 'repair')?.input ?? '', /do not cover user_stories\/place-order\.md \(the saved check of user_stories\/place-order\.md is for another source: a stale Runtime batch/);
  assert.deepEqual(w.github.merges, []);
});

test('E08 (MF2, Codex 5, real saved checks) a fixture project and a broken unrelated Story do not hide the footprint of a healthy changed prompt', async t => {
  const notes = 'prompts/notes.prompt.md', place = JSON.parse(readFileSync(join(HARBOR, 'tests/place-order.json'), 'utf8'));
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, harbor({
    [notes]: '# Harbor notes\n\nThe shop opens at 07:00.\n',
    'tests/place-order.json': JSON.stringify({ ...place, context: [{ prompt_path: notes }] }, null, 2) + '\n',
    // An unrelated Story whose test names a prompt that does not exist.
    'user_stories/broken.md': '# Broken\n\n## Acceptance criteria\n\n1. It works.\n',
    'tests/broken.json': JSON.stringify({ ...place, story_path: 'user_stories/broken.md', criteria: [{ id: 'AC1', text: 'It works.' }], steps: [{ ...place.steps[0], entry_path: 'prompts/missing.prompt.md' }] }, null, 2) + '\n',
    // A nested fixture project whose test names another Story (pdd's own test/fixtures/harbor has one).
    'test/fixtures/demo/user_stories/x.md': '# X\n\n## Acceptance criteria\n\n1. X.\n',
    'test/fixtures/demo/tests/x.json': JSON.stringify({ ...place, story_path: 'user_stories/other.md' }, null, 2) + '\n',
  }));
  w.issue(17); await w.tick();
  const cwd = w.job(17, 'build').cwd;
  writeIn(cwd, notes, '# Harbor notes\n\nThe shop opens at 07:30.\n');
  w.git(cwd, 'add', '.'); w.git(cwd, 'commit', '-qm', 'notes');
  const env = await pddTest(t, w, cwd, ['place-order']);
  const { pr } = w.build(17, { body: `Fixes #17.\n\nRuntime: PASS\nPath: d — ${notes}, change-17.txt — unowned — no contract change — Test: done check` });
  await w.tick({ runtimeEvidence: undefined, env });
  assert.equal(w.job(17, 'repair'), undefined, w.job(17, 'repair')?.input);
  w.review(17, 'PASS'); w.suite(17, 0); await w.tick({ runtimeEvidence: undefined, env }); await w.tick({ runtimeEvidence: undefined, env });
  assert.deepEqual(w.github.merges, [pr.number]);
});

test('E09 (SF7) a reader error is a red finding with its cause, never a tick error', async t => {
  const { w } = await t01World(t, async () => { throw Error('pdd-story-mismatch: tests/x.json'); });
  assert.match(w.job(17, 'repair')?.input ?? '', /Autopilot could not read the Stories and the saved pdd test checks at head [0-9a-f]{7}: pdd-story-mismatch: tests\/x\.json/);
});

// ---- T04: the engine's own replay and formal run ------------------------------------------------------
const NOT_RUN = 'Runtime: not run (no prompt changed)';
async function t04World(t, { base = {}, change = {}, remove = [], evidence = 'vectors=not-run; formal=not-applicable', settings = {} } = {}) {
  const w = await coreWorld(t, { settings: { runs: 1, ...settings } });
  seed(w, base);
  w.issue(17); await w.tick();
  const cwd = w.job(17, 'build').cwd;
  for (const [path, text] of Object.entries(change)) writeIn(cwd, path, text);
  for (const path of remove) w.git(cwd, 'rm', '-q', path);
  const line = `Evidence: runtime=not-run; ${evidence}; tests=pass (3/3)`;
  const { pr, head } = w.build(17, { body: `Fixes #17.\n\n${NOT_RUN}\n${line}`, result: { promptChanged: false, evidence: line } });
  await w.tick(); w.review(17, 'PASS'); w.suite(17, 0); await w.tick();
  return { w, pr, head, cwd, command: () => w.job(17, 'vectors')?.args.at(-3) ?? '' };
}

test('E10 (MF1) after a repair at the same head the replay runs again, as the suite does', async t => {
  const { w, pr, head } = await t04World(t, { base: { 'test/flaky.vectors.test.mjs': nodeTest('a') }, change: { 'test/flaky.vectors.test.mjs': nodeTest('a changed') }, evidence: 'vectors=pass (1/1); formal=not-applicable' });
  w.vectorsRun(17, { tests: 1, fail: 1, failed: [{ name: 'a changed', file: 'test/flaky.vectors.test.mjs' }] }); await w.tick();
  assert.match(w.job(17, 'repair')?.input ?? '', /1 of 1 failed: a changed/);
  assert.equal(w.build(17, { role: 'repair', write: false }).head, head);     // the flake passed on the next run: nothing to commit
  await w.tick();
  assert.equal(w.started.filter(job => job.role === 'vectors').length, 2, 'the replay runs again');
  w.review(17, 'PASS'); w.suite(17, 0); w.vectorsRun(17, { tests: 1 }); await w.tick(); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
});

test('E11 (SF1, Codex 6) the replay set is complete: 41 linked files and a 21st changed scenario never push a changed file out', async t => {
  const base = { 'test/runtime/cases.json': '[1]\n' };
  for (let i = 0; i < 41; i++) base[`test/a${String(i).padStart(2, '0')}.vectors.test.mjs`] = `${nodeTest(`a${i}`)}const f = 'cases.json';\n`;
  for (let i = 0; i < 21; i++) base[`test/runtime/s${String(i).padStart(2, '0')}.json`] = '[1]\n';
  base['test/late.vectors.test.mjs'] = `${nodeTest('late')}const f = 's20.json';\n`;
  base['test/zz-changed.vectors.test.mjs'] = nodeTest('zz');
  const change = { 'test/runtime/cases.json': '[1, 2]\n', 'test/zz-changed.vectors.test.mjs': nodeTest('zz changed') };
  for (let i = 0; i < 21; i++) change[`test/runtime/s${String(i).padStart(2, '0')}.json`] = '[2]\n';
  const { command } = await t04World(t, { base, change });
  for (const file of ['test/zz-changed.vectors.test.mjs', 'test/late.vectors.test.mjs', 'test/a00.vectors.test.mjs', 'test/a40.vectors.test.mjs'])
    assert.ok(command().includes(`'./${file}'`), `${file} is not in the run`);
});

test('E12 (Codex 6) more than 400 replay files run nothing: an explicit "not run", and a positive claim is red', async t => {
  const base = {}, change = {};
  for (let i = 0; i < 401; i++) { base[`test/v${i}.vectors.test.mjs`] = nodeTest(`v${i}`); change[`test/v${i}.vectors.test.mjs`] = nodeTest(`v${i} changed`); }
  const { w } = await t04World(t, { base, change, evidence: 'vectors=pass (401/401); formal=not-applicable' });
  assert.equal(w.job(17, 'vectors'), undefined, 'no part of the set runs');
  assert.match(w.job(17, 'repair')?.input ?? '', /The Evidence line says vectors=pass \(401\/401\), but Autopilot could not check it: .*too many replay and formal files: 401; the limit is 400/);
});

test('E13 (SF2, SF3, Codex 7) Git names are exact (NUL mode); every file goes as ./FILE after --; a glob name is not run', async t => {
  const names = ['test/café.vectors.test.mjs', "test/it's here.vectors.test.mjs", '--test-skip-pattern=x.vectors.test.mjs', 'test/[a].vectors.test.mjs'];
  const { w, pr, command } = await t04World(t, { base: Object.fromEntries(names.map(n => [n, nodeTest('x')])), change: Object.fromEntries(names.map(n => [n, nodeTest('y')])), evidence: 'vectors=pass (3/3); formal=not-applicable' });
  const cmd = command();
  assert.ok(cmd.includes("node --test --test-reporter=tap -- "), cmd.slice(0, 200));
  assert.ok(cmd.includes("'./test/café.vectors.test.mjs'"), 'the non-ASCII name runs as written');
  assert.ok(cmd.includes(`'./test/it'\\''s here.vectors.test.mjs'`), 'a quote and a space stay one argument');
  assert.ok(cmd.includes("'./--test-skip-pattern=x.vectors.test.mjs'"), 'a leading dash is never an option');
  assert.ok(!cmd.includes('[a]'), 'a glob name is not run');
  w.vectorsRun(17, { tests: 3 }); await w.tick(); await w.tick();
  assert.match(mergeNote(pr), /- Not run by Autopilot \(a glob character in the name\): test\/\[a\]\.vectors\.test\.mjs/);
});

test('E14 (MF7) only node:test files run; a jest file and a Python file are "not run (runner)", and their claim is not checked', async t => {
  const files = { 'test/a.vectors.test.mjs': nodeTest('a'), 'test/jest.vectors.test.js': "test('j', () => expect(1).toBe(1));\n", 'test/b.vectors.test.py': 'def test_b():\n    pass\n' };
  const { w, pr, command } = await t04World(t, { base: files, change: Object.fromEntries(Object.keys(files).map(f => [f, `${files[f]}\n`])), evidence: 'vectors=pass (1/1); formal=not-applicable' });
  assert.ok(command().includes("'./test/a.vectors.test.mjs'"));
  assert.ok(!command().includes('jest') && !command().includes('.py'), command());
  w.vectorsRun(17, { tests: 1 }); await w.tick(); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.match(mergeNote(pr), /- Not run by Autopilot \(runner: not a node:test file\): test\/jest\.vectors\.test\.js/);
  assert.match(mergeNote(pr), /- Not run by Autopilot \(runner: not a JavaScript file\): test\/b\.vectors\.test\.py/);
  // Only other runners: nothing runs, and the claim is not checked.
  const only = await t04World(t, { base: { 'test/jest.vectors.test.js': files['test/jest.vectors.test.js'] }, change: { 'test/jest.vectors.test.js': `${files['test/jest.vectors.test.js']}\n` }, evidence: 'vectors=pass (1/1); formal=not-applicable' });
  assert.equal(only.w.job(17, 'vectors'), undefined); await only.w.tick();
  assert.deepEqual(only.w.github.merges, [only.pr.number]);
});

test('E15 (M19) a deleted replay file is not run', async t => {
  const { command } = await t04World(t, { base: { 'test/gone.vectors.test.mjs': nodeTest('g'), 'test/kept.vectors.test.mjs': nodeTest('k') }, change: { 'test/kept.vectors.test.mjs': nodeTest('k2') }, remove: ['test/gone.vectors.test.mjs'] });
  assert.ok(command().includes("'./test/kept.vectors.test.mjs'")); assert.ok(!command().includes('gone'), command());
});

test('E16 (Codex 8, M9) a run with no result is retried twice, then "not run": a positive vectors or formal claim is red; a not-run claim merges', async t => {
  const broken = async (evidence, files) => {
    const r = await t04World(t, { base: files, change: Object.fromEntries(Object.entries(files).map(([f, text]) => [f, `${text}\n`])), evidence });
    for (let i = 0; i < 3; i++) {
      const job = r.w.job(17, 'vectors');
      assert.ok(job, `try ${i + 1} runs`);
      appendFileSync(job.log, 'npm ERR! install failed\n'); r.w.finish(17, 'vectors', { code: 1 });   // exit 1, no marker, no summary
      await r.w.tick();
    }
    assert.equal(r.w.started.filter(job => job.role === 'vectors').length, 3);
    return r;
  };
  let { w } = await broken('vectors=pass (99/99); formal=not-applicable', { 'test/a.vectors.test.mjs': nodeTest('a') });
  assert.match(w.job(17, 'repair')?.input ?? '', /The Evidence line says vectors=pass \(99\/99\), but Autopilot could not check it: its run of the replay tests that this change touches \(test\/a\.vectors\.test\.mjs\) at head [0-9a-f]{7} gave no result \(the run gave no result \(no result for the replay tests \(exit 1\), 3 tries\)/);
  ({ w } = await broken('vectors=not-run; formal=proved', { 'test/a.formal.test.mjs': nodeTest('f') }));
  assert.match(w.job(17, 'repair')?.input ?? '', /The Evidence line says formal=proved, but Autopilot could not check it/);
  let pr;
  ({ w, pr } = await broken('vectors=not-run; formal=not-run', { 'test/a.vectors.test.mjs': nodeTest('a') }));
  assert.equal(w.job(17, 'repair'), undefined); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.match(mergeNote(pr), /- Replay tests \(Autopilot's run\): not run \(the run gave no result/);
});

test('E17 (Codex 8, M3, M4) the claims must match the run, kind by kind: counts, formal claims, a non-zero exit with "# fail 0"', async t => {
  const files = { 'test/a.vectors.test.mjs': nodeTest('a'), 'test/a.formal.test.mjs': nodeTest('f') };
  const change = Object.fromEntries(Object.entries(files).map(([f, text]) => [f, `${text}\n`]));
  // A wrong count: the engine ran 3 vectors tests.
  let { w, command } = await t04World(t, { base: files, change, evidence: 'vectors=pass (999/999); formal=proved' });
  assert.match(command(), /vectors exit .*formal exit/);
  w.vectorsRun(17, { tests: 3, formal: { tests: 2 } }); await w.tick();
  assert.match(w.job(17, 'repair')?.input ?? '', /The Evidence line says vectors=pass \(999\/999\), but Autopilot ran the replay tests that this change touches \(test\/a\.vectors\.test\.mjs\) at head [0-9a-f]{7}: 3\/3 passed\. Write vectors=pass \(3\/3\)/);
  // A formal claim that the run contradicts.
  ({ w } = await t04World(t, { base: files, change, evidence: 'vectors=pass (3/3); formal=not-applicable' }));
  w.vectorsRun(17, { tests: 3, formal: { tests: 2 } }); await w.tick();
  assert.match(w.job(17, 'repair')?.input ?? '', /The Evidence line says formal=not-applicable, but Autopilot ran the changed formal tests \(test\/a\.formal\.test\.mjs\)/);
  // A non-zero exit of the formal run with "# fail 0" is a failure.
  ({ w } = await t04World(t, { base: files, change, evidence: 'vectors=pass (3/3); formal=proved' }));
  w.vectorsRun(17, { tests: 3, formal: { tests: 2, code: 1 } }); await w.tick();
  assert.match(w.job(17, 'repair')?.input ?? '', /Autopilot ran the formal tests that this change touches \(test\/a\.formal\.test\.mjs\) at head [0-9a-f]{7}: the run failed \(exit 1\) although its summary says 0 of 2 failed/);
  // True claims merge, and the note has the counts of each kind.
  let pr;
  ({ w, pr } = await t04World(t, { base: files, change, evidence: 'vectors=pass (3/3); formal=proved' }));
  w.vectorsRun(17, { tests: 3, formal: { tests: 2 } }); await w.tick(); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.match(mergeNote(pr), /- Replay tests \(Autopilot's run at [0-9a-f]{7}\): pass \(3\/3\): test\/a\.vectors\.test\.mjs/);
  assert.match(mergeNote(pr), /- Formal tests \(Autopilot's run at [0-9a-f]{7}\): pass \(2\/2\): test\/a\.formal\.test\.mjs/);
});

test('E18 (M10, M8) a running replay holds the merge; a replay at its backstop ends the job', async t => {
  const MIN = 60 * 1000;
  const { w } = await t04World(t, { base: { 'test/a.vectors.test.mjs': nodeTest('a') }, change: { 'test/a.vectors.test.mjs': nodeTest('b') }, evidence: 'vectors=pass (1/1); formal=not-applicable', settings: { maxJobHours: 3 } });
  const run = w.job(17, 'vectors');
  for (let i = 0; i < 3; i++) { w.advance(30 * MIN); w.progress(17, 'vectors'); await w.tick(); }
  assert.deepEqual(w.github.merges, [], 'no merge while the replay runs');
  for (let i = 0; i < 8 && !w.stopped.includes(run.id); i++) { w.advance(30 * MIN); w.progress(17, 'vectors'); await w.tick(); }
  assert.ok(w.stopped.includes(run.id), 'stopped at its backstop');
  const history = readFileSync(join(w.root, 'history.jsonl'), 'utf8');
  assert.match(history, /the replay and formal tests ran 3 h \(its limit/);
  assert.deepEqual(w.github.merges, []);
});

test('E19 (SF4, Codex 9) the replay command bounds its output, and the engine reads a large log in parts', async t => {
  const files = { 'test/a.vectors.test.mjs': nodeTest('a'), 'test/a.formal.test.mjs': nodeTest('f') };
  const { w, pr, command } = await t04World(t, { base: files, change: Object.fromEntries(Object.entries(files).map(([f, text]) => [f, `${text}\n`])), evidence: 'vectors=pass (5/5); formal=proved' });
  assert.match(command(), /set -o pipefail; .*\| LC_ALL=C awk -v cap=4194304 '.*pdd-autopilot: output cut after/);
  const job = w.job(17, 'vectors'), noise = `# ${'n'.repeat(1000)}\n`.repeat(1024);   // 1 MB of noise lines
  appendFileSync(job.log, `TAP version 13\n${noise.repeat(3)}${w.tap({ tests: 5 }, 'vectors', job.cwd)}${noise.repeat(10)}${w.tap({ tests: 2 }, 'formal', job.cwd)}`);
  w.finish(17, 'vectors', { code: 0 }); await w.tick(); await w.tick();
  assert.deepEqual(w.github.merges, [pr.number]);
  assert.match(mergeNote(pr), /Replay tests \(Autopilot's run at [0-9a-f]{7}\): pass \(5\/5\)/);
  assert.match(mergeNote(pr), /Formal tests \(Autopilot's run at [0-9a-f]{7}\): pass \(2\/2\)/);
});

// ---- T08: an AI-service problem is the agent account, not the issue ---------------------------------------
test('E20 (T08) an agent that ends on an AI-service error is released with no strike and no cooldown; it counts for the machine pause', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  const alerts = [];
  for (const n of [17, 18]) w.issue(n);
  const fail = async (n, line) => { appendFileSync(w.job(n, 'build').log, `${line}\n{"type":"turn.failed","error":{"message":${JSON.stringify(JSON.parse(line).message ?? 'x')}}}\n`); w.finish(n, 'build', { code: 1 }); await w.tick({ alert: async a => alerts.push(a) }); };
  await w.tick();
  const first = w.job(17, 'build') ? 17 : 18;
  await fail(first, '{"type":"error","message":"Selected model is at capacity. Please try a different model."}');
  const history = () => readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(line => JSON.parse(line));
  const row = history().find(r => r.issue === first && r.outcome === 'released');
  assert.ok(row, 'released'); assert.equal(row.noResult, undefined, 'not counted: no 24 h cooldown');
  assert.match(row.text, /the AI service said "Selected model is at capacity/);
  assert.deepEqual(w.labels(first).filter(l => ['pdd:stuck', 'pdd:working'].includes(l)), []);
  const machine = () => JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
  assert.equal(machine().streak, 1); assert.equal(machine().pending, null, 'no pending strike');
  // The same issue can start again at once; two more service errors pause the machine, and the alert names the account state.
  for (const message of ['Your workspace is out of credits. Ask your workspace owner to refill in order to continue.', "You've hit your usage limit."]) {
    const n = [17, 18].find(i => w.job(i, 'build') && w.alive.has(w.job(i, 'build').pid));
    assert.ok(n, 'a new build started'); await fail(n, JSON.stringify({ type: 'error', message }));
  }
  assert.equal(machine().streak, 3); assert.ok(machine().pausedUntil > w.now());
  assert.equal(history().filter(r => r.strike).length, 0, 'no strike for any issue');
  const pause = alerts.find(a => a.kind === 'usage-limit');
  assert.match(pause?.text ?? '', /The agent said: "You've hit your usage limit\."/);
});

test('E21 (T08) an ordinary no-result is still counted; a reviewer on an AI-service error is not', async t => {
  let w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick();
  w.finish(17, 'build', { code: 1 }); await w.tick();                  // the fake log says "Error: pdd test returned no verdict"
  let row = readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(l => JSON.parse(l)).find(r => r.outcome === 'released');
  assert.equal(row.noResult, true, 'counted');
  w = await coreWorld(t, { settings: { runs: 1 } });
  w.issue(17); await w.tick();
  w.build(17, { body: `Fixes #17.\n\n${NOT_RUN}` , result: { promptChanged: false } }); await w.tick();
  for (let i = 0; i < 2; i++) {
    appendFileSync(w.job(17, 'review').log, '{"type":"result","subtype":"success","is_error":true,"result":"Credit balance is too low"}\n');
    w.finish(17, 'review', { code: 1 }); w.suite(17, 0); await w.tick();
  }
  row = readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(l => JSON.parse(l)).find(r => r.outcome === 'released');
  assert.ok(row, 'released'); assert.equal(row.noResult, undefined);
  assert.match(row.text, /the fresh reviewer ended twice with no valid verdict: the AI service said "Credit balance is too low"/);
});

// ---- T09: the path check reads the files field only ---------------------------------------------------
test('E22 (T09) R1 reads only the files field of a path d line: the #69 repair body has no false violation; an owned file on path d stays red', async t => {
  const bindings = JSON.stringify({ modules: [{ module: 'docs/errors.md', prompt: 'prompts/errors.prompt.md' }] }, null, 2) + '\n';
  const setup = async body => {
    const w = await coreWorld(t, { settings: { runs: 1 } });
    seed(w, { 'pdd-bindings.json': bindings, 'prompts/errors.prompt.md': '# Errors\n\nThe error table.\n', 'docs/errors.md': '# Errors\n' });
    w.issue(17); await w.tick();
    writeIn(w.job(17, 'build').cwd, 'docs/errors.md', '# Errors\n\nLinks.\n');
    w.build(17, { body, result: { promptChanged: false } }); await w.tick();
    return w;
  };
  // The real Path lines of sandbox PR #80 (issue #69) after its repair.
  const real = [
    'Path: a — docs/errors.md — owner prompts/errors.prompt.md (pdd-bindings.json) — prompt changed — Test: test/errors-doc.test.js',
    'Path: d — prompts/errors.prompt.md — owning prompt for docs/errors.md — prompt changed — Test: test/errors-doc.test.js',
    'Path: d — user_stories/error-helper-links.md, test/errors-doc.test.js — unowned (Story associated through pdd-bindings.json; no owning prompt names either artifact) — no contract change — Test: test/errors-doc.test.js',
  ].join('\n');
  let w = await setup(`Fixes #17.\n\n${NOT_RUN}\n${real}`);
  assert.doesNotMatch(w.job(17, 'repair')?.input ?? '', /docs\/errors\.md is owned by prompts\/errors\.prompt\.md/);
  w = await setup(`Fixes #17.\n\n${NOT_RUN}\nPath: d — docs/errors.md — unowned — no contract change — Test: done check`);
  assert.match(w.job(17, 'repair')?.input ?? '', /docs\/errors\.md is owned by prompts\/errors\.prompt\.md \(binding\), so it cannot take path d/);
});

// ---- T10: the review flags a choice that the issue did not make --------------------------------------
async function t10World(t) {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seed(w, { 'src/duration.js': 'export const formatDuration = s => `${Math.floor(s / 60)}m`;\n', 'prompts/duration.prompt.md': '# Duration\n\nThere are no days: 25 hours is "25h 0m".\n' });
  // Sandbox #82 (vague) and the open decision #4 that it touches through src/duration.js; #9 touches nothing.
  w.issue(17, { title: 'Durations look weird', body: 'durations look weird in our dashboard, can you make them look nicer? some of them are really long and some show 0m' });
  w.github.add(4, { title: 'Durations under one minute show as "0m"', labels: ['pdd:stuck'],
    body: 'A 45-second call shows as `0m` (`formatDuration(45)` in `src/duration.js`).\n\nWe have two ideas and have not decided which one to use:\n\n1. `"45s"`.\n2. `"<1m"`.' });
  w.github.add(9, { title: 'Docs typo', body: 'Fix a typo in docs/intro.md.', labels: ['pdd:stuck'] });
  await w.tick();
  writeIn(w.job(17, 'build').cwd, 'src/duration.js', 'export const formatDuration = s => s < 60 ? `${s}s` : `${Math.floor(s / 60)}m`;\n');
  const { pr, head } = w.build(17, { body: `Fixes #17.\n\n${NOT_RUN}\nPath: e — src/duration.js — unowned — no contract change — Test: done check`, result: { promptChanged: false } });
  await w.tick();
  return { w, pr, head };
}

test('E23 (T10) the review brief has check (6) and the linked open issue; a P2 decision is one question (pdd:needs-decision), not a repair', async t => {
  let { w, pr, head } = await t10World(t);
  const brief = w.job(17, 'review').input;
  assert.match(brief, /\(6\) the change makes no product, contract or naming choice that the issue did not make/);
  assert.match(brief, /Issue #4: Durations under one minute show as "0m"\n<<<\n[\s\S]*We have two ideas and have not decided/);
  assert.doesNotMatch(brief, /Issue #9:/);
  const question = 'Issue #4 is still open: should a duration under one minute show "45s" or "<1m"?';
  w.finish(17, 'review', { result: { verdict: 'FAIL', head, summary: 'Picks option 1 of #4.', mustFix: ['P2 decision: src/duration.js:1 picks "45s", option 1 of the open issue #4'], question } });
  w.suite(17, 0); await w.tick();
  assert.equal(w.job(17, 'repair'), undefined, 'no repair round');
  assert.ok(w.labels(17).includes('pdd:needs-decision'));
  const asked = w.comments(17).filter(body => body.includes('pdd:autopilot-core:question:'));
  assert.equal(asked.length, 1); assert.match(asked[0], /should a duration under one minute show "45s" or "<1m"\?/);
  assert.ok(pr.comments.some(c => c.body.includes('<!-- pdd:autopilot-core:needs-decision-pr:')));
  assert.deepEqual(w.github.merges, []);
  // No question field, and another item too: still one question, built from the decision item.
  ({ w, head } = await t10World(t));
  w.finish(17, 'review', { result: { verdict: 'FAIL', head, summary: 'x', mustFix: ['P1 src/duration.js:1 breaks 0 seconds', 'P2 decision: src/duration.js:1 picks "45s" from issue #4'] } });
  w.suite(17, 0); await w.tick();
  assert.equal(w.job(17, 'repair'), undefined);
  assert.match(w.comments(17).find(body => body.includes('pdd:autopilot-core:question:')) ?? '', /The review found a choice that issue #17 did not make: src\/duration\.js:1 picks "45s" from issue #4\. Which option do you want\?/);
});
