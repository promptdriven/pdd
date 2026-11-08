// Story: user_stories/tests-found-by-name.md. The tests of Story S are S.json and S.<variant>.json in a test or tests
// folder: found by name and folder, never by content, and read in full at any size.
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { chmodSync, cpSync, existsSync, mkdirSync, readFileSync, readdirSync, truncateSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { captureSource, findTests, preflight, selectTests } from '../src/runtime-preflight.mjs';
import { runCheck, saveDoorCase } from '../src/runtime-client.mjs';
import { readAgentScenarios } from '../src/agent-project.mjs';
import { fakeRuntime, harbor, portsFor, root, sink, temp } from './runtime-fake.mjs';

const HARBOR = join(root, 'test/fixtures/harbor');
const PLACE_TEST = JSON.parse(readFileSync(join(HARBOR, 'tests/place-order.json'), 'utf8'));
const PLACE_STORY = readFileSync(join(HARBOR, 'user_stories/place-order.md'), 'utf8');
const git = (cwd, ...args) => { const r = spawnSync('git', args, { cwd, encoding: 'utf8' }); assert.equal(r.status, 0, r.stderr); return r.stdout; };
const put = (repo, path, text) => { mkdirSync(dirname(join(repo, path)), { recursive: true }); writeFileSync(join(repo, path), text); };
const story = (title = 'Place a coffee order') => PLACE_STORY.replace('# Place a coffee order', `# ${title}`);
const scenario = (storyPath, extra = {}) => JSON.stringify({ ...PLACE_TEST, story_path: storyPath, ...extra }, null, 2);

// A Git repo with the Harbor prompt and the given files.
function repoWith(t, files) {
  const sandbox = temp(t), repo = join(sandbox, 'repo'), home = join(sandbox, 'home');
  mkdirSync(home); mkdirSync(repo);
  cpSync(join(HARBOR, 'prompts'), join(repo, 'prompts'), { recursive: true });
  for (const [path, text] of Object.entries(files)) put(repo, path, text);
  git(repo, 'init', '-q'); git(repo, 'add', '-A'); git(repo, '-c', 'user.email=t@example.com', '-c', 'user.name=t', 'commit', '-qm', 'init');
  return { repo, home };
}

// Offline: anything that reaches the network or gh fails the count.
async function check(setup, words, options = {}) {
  const calls = { fetch: 0, gh: 0 };
  const ports = { env: { HOME: setup.home, PDD_INTERPRETER_QUEUE: join(setup.home, 'interpreter-queue'), PDD_RUNTIME_URL: 'http://127.0.0.1:9' }, stdout: sink(), stderr: sink(),
    fetch: async () => { calls.fetch += 1; throw Error('network'); }, gh: () => { calls.gh += 1; return { status: 1, stdout: '' }; } };
  const code = await runCheck({ words, options, cwd: setup.repo }, ports);
  return { code, calls, out: ports.stdout.text, err: ports.stderr.text, json: options['--json'] && ports.stdout.text ? JSON.parse(ports.stdout.text) : null };
}

// Wrong: pdd opened every JSON file to decide what is a test, so a scenario anywhere was a test and an unreadable
// fixture in a test folder broke discovery for every Story.
test('NAME1: the tests of Story S are S.json and S.<variant>.json in a test or tests folder at any depth; no other JSON file is opened', t => {
  const setup = repoWith(t, {
    'user_stories/alpha.md': story('Alpha'), 'tests/alpha.json': scenario('user_stories/alpha.md'), 'tests/alpha.empty-shop.json': scenario('user_stories/alpha.md'),
    'user_stories/sub/beta.md': story('Beta'), 'tests/runtime/beta.json': scenario('user_stories/sub/beta.md'),
    'user_stories/gamma.md': story('Gamma'), 'runtime/tests/gamma.json': scenario('user_stories/gamma.md'),
    'user_stories/delta.md': story('Delta'), 'scenarios/delta.json': scenario('user_stories/delta.md'),
    'tests/blob.json': '{"not": "a test"}\n',
  });
  chmodSync(join(setup.repo, 'tests/blob.json'), 0o000);
  let found;
  assert.doesNotThrow(() => { found = findTests({ root: setup.repo }); });
  assert.deepEqual(found.tests.map(item => [item.path, item.storyPath, item.story, item.title]), [
    ['runtime/tests/gamma.json', 'user_stories/gamma.md', 'gamma', 'Gamma'],
    ['tests/alpha.empty-shop.json', 'user_stories/alpha.md', 'alpha', 'Alpha'],
    ['tests/alpha.json', 'user_stories/alpha.md', 'alpha', 'Alpha'],
    ['tests/runtime/beta.json', 'user_stories/sub/beta.md', 'beta', 'Beta']]);
  assert.ok(found.tests.every(item => item.doc?.schema_version === 'prompt-runtime.program-scenario.v1'));
  assert.deepEqual(found.warnings, [
    'Warning: user_stories/delta.md has no test: expected tests/delta.json (or delta.json in any test or tests folder).',
    'Warning: tests/blob.json matches no Story (user_stories/**/blob.md).']);
  assert.deepEqual(selectTests(found, ['alpha']).selected.map(item => item.path), ['tests/alpha.empty-shop.json', 'tests/alpha.json']);
  assert.deepEqual(selectTests(found, ['alpha.empty-shop']).selected.map(item => item.path), ['tests/alpha.empty-shop.json']);
});

// Wrong (#2580): a 2.4 MB test with schema_version after the first 64 KiB was skipped with no message, and
// `pdd test m1-big` said "Unknown story".
test('NAME2: a 2,408,687-byte runtime/tests/m1-big.json with schema_version after 64 KiB is found, selected by name and read in full', async t => {
  const steps = Array.from({ length: 3 }, (_, index) => ({ ...PLACE_TEST.steps[0], step_id: `order-${index + 1}` }));
  const head = { initial_world: { kv: { notes: '' } } }, tail = { ...PLACE_TEST, story_path: 'user_stories/m1-big.md', steps };
  delete tail.initial_world;
  const build = notes => JSON.stringify({ ...head, initial_world: { kv: { notes } }, ...tail });
  const text = build('x'.repeat(2_408_687 - Buffer.byteLength(build(''))));
  assert.equal(Buffer.byteLength(text), 2_408_687);
  assert.ok(text.indexOf('"schema_version"') > 65_536);
  const setup = repoWith(t, { 'user_stories/m1-big.md': story('M1 big'), 'runtime/tests/m1-big.json': text });
  const found = findTests({ root: setup.repo });
  assert.deepEqual(found.tests.map(item => item.path), ['runtime/tests/m1-big.json']);
  assert.deepEqual(found.warnings, []);
  const { selected, unknown } = selectTests(found, ['m1-big']);
  assert.deepEqual(unknown, []);
  assert.deepEqual(selected.map(item => item.path), ['runtime/tests/m1-big.json']);
  const { rows } = preflight({ root: setup.repo, found, selected });
  assert.deepEqual(rows.map(row => [row.test, row.refusals, row.steps.length, row.criteria_total]), [['runtime/tests/m1-big.json', [], 3, 3]]);
  const captured = captureSource(setup.repo, { tests: ['runtime/tests/m1-big.json'] });
  assert.deepEqual(captured.files.find(file => file.path === 'runtime/tests/m1-big.json'), { path: 'runtime/tests/m1-big.json', size: 2_408_687 });
  const files = await check(setup, ['m1-big'], { '--files': true });
  assert.equal(files.code, 0, files.err);
  assert.match(files.out, /runtime\/tests\/m1-big\.json +2408687 bytes/);
  assert.deepEqual(files.calls, { fetch: 0, gh: 0 });
});

// Wrong: a Story with no test said only "has no test", and `pdd test STORY` for it said "Unknown story".
test('NAME3: a Story with no test prints the expected path; selecting it stops with that line; an unknown word lists every Story', async t => {
  const setup = repoWith(t, { 'user_stories/phone/p17.md': story('P17'), 'user_stories/place-order.md': story(), 'tests/place-order.json': scenario('user_stories/place-order.md') });
  const line = 'user_stories/phone/p17.md has no test: expected tests/p17.json (or p17.json in any test or tests folder).';
  assert.deepEqual(findTests({ root: setup.repo }).warnings, [`Warning: ${line}`]);
  for (const word of ['p17', 'user_stories/phone/p17.md']) {
    const result = await check(setup, [word]);
    assert.equal(result.code, 2, word); assert.equal(result.out, ''); assert.equal(result.err.trimEnd(), line, word);
    assert.deepEqual(result.calls, { fetch: 0, gh: 0 });
  }
  const unknown = await check(setup, ['nope']);
  assert.equal(unknown.code, 2);
  assert.deepEqual(unknown.err.trimEnd().split('\n'), ['Unknown story "nope". Stories:', '  place-order  tests/place-order.json  (Place a coffee order)', '  p17  no test (expected tests/p17.json)']);
  const nested = repoWith(t, { 'app/user_stories/p18.md': story('P18') });
  assert.deepEqual(findTests({ root: nested.repo }).warnings, ['Warning: app/user_stories/p18.md has no test: expected app/tests/p18.json (or p18.json in any test or tests folder).']);
});

// Wrong: a JSON file in a test folder that matched no Story was skipped with no line.
test('NAME4: JSON files in test folders that match no Story print one line; --files and --json list each file', async t => {
  const setup = repoWith(t, { 'user_stories/place-order.md': story(), 'tests/place-order.json': scenario('user_stories/place-order.md'),
    'tests/notes.json': scenario('user_stories/place-order.md'), 'test/fixtures/data.json': '[]\n', 'docs/other.json': '{}\n' });
  const lines = ['Warning: test/fixtures/data.json matches no Story (user_stories/**/data.md).', 'Warning: tests/notes.json matches no Story (user_stories/**/notes.md).'];
  assert.deepEqual(findTests({ root: setup.repo }).warnings, [
    'Warning: 2 JSON files in test folders match no Story (the tests of user_stories/**/S.md are S.json and S.<variant>.json). pdd test --files lists them.']);
  const files = await check(setup, ['place-order'], { '--files': true });
  assert.equal(files.code, 0, files.err);
  for (const text of lines) assert.ok(files.err.split('\n').includes(text), text);
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: join(setup.home, 'state') });
  assert.equal(await runCheck({ words: ['place-order'], options: { '--json': true }, cwd: setup.repo }, ports), 0, ports.stderr.text);
  const json = JSON.parse(ports.stdout.text);
  for (const text of lines) assert.ok(json.warnings.includes(text), text);
  const one = repoWith(t, { 'user_stories/place-order.md': story(), 'tests/place-order.json': scenario('user_stories/place-order.md'), 'tests/notes.json': '{}' });
  assert.deepEqual(findTests({ root: one.repo }).warnings, [lines[1]]);
});

// Wrong: two tests for one Story were both checked, and two Stories with one name shared a test.
test('NAME5: two files with one name for one Story, or one test for two Stories, are an error that names every file; pdd checks none', async t => {
  const setup = repoWith(t, { 'user_stories/phone/p17.md': story('P17'), 'tests/p17.json': scenario('user_stories/phone/p17.md'),
    'test/runtime/p17.json': scenario('user_stories/phone/p17.md') });
  const sentence = 'user_stories/phone/p17.md has 2 files named p17.json: test/runtime/p17.json and tests/p17.json. Keep one.';
  assert.deepEqual(findTests({ root: setup.repo }).warnings, [`Warning: ${sentence}`]);
  for (const word of ['p17', 'tests/p17.json']) {
    const result = await check(setup, [word], { '--json': true });
    assert.equal(result.code, 4, word);
    assert.deepEqual(result.json.rows.map(row => [row.test, row.state, row.refusals.map(item => item.message)]), [['test/runtime/p17.json', 'not run', [sentence]]], word);
    assert.deepEqual(result.calls, { fetch: 0, gh: 0 });
  }
  // pdd test --lint refuses the conflict locally, sends the other Story's test and names only that one.
  put(setup.repo, 'user_stories/place-order.md', story()); put(setup.repo, 'tests/place-order.json', scenario('user_stories/place-order.md'));
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  fake.capacity = () => ({ status: 200, json: { maintenance: null, features: ['lint-tests'] } });
  const lintRun = async words => {
    const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: join(setup.home, 'state') });
    const code = await runCheck({ words, options: { '--lint': true, '--json': true }, cwd: setup.repo }, ports);
    return { code, json: JSON.parse(ports.stdout.text), err: ports.stderr.text };
  };
  const alone = await lintRun(['p17']);
  assert.equal(alone.code, 4, alone.err);
  assert.deepEqual(alone.json.rows.map(row => [row.test, row.state, row.refusals.map(item => item.message)]), [['test/runtime/p17.json', 'not run', [sentence]]]);
  assert.equal(fake.posts.length, 0, 'nothing is sent');
  const both = await lintRun(['p17', 'place-order']);
  assert.equal(both.code, 4, both.err);
  assert.deepEqual(both.json.rows.map(row => [row.test, row.state]), [['test/runtime/p17.json', 'not run'], ['tests/place-order.json', 'passed']]);
  assert.deepEqual(fake.posts.map(post => [post.command, post.request.tests]), [['lint', ['tests/place-order.json']]]);
  const twin = repoWith(t, { 'user_stories/a/x.md': story('X a'), 'user_stories/b/x.md': story('X b'), 'tests/x.json': scenario('user_stories/a/x.md') });
  assert.deepEqual(findTests({ root: twin.repo }).warnings, ['Warning: tests/x.json matches 2 Stories: user_stories/a/x.md and user_stories/b/x.md. Rename one.']);
  const result = await check(twin, ['x'], { '--json': true });
  assert.equal(result.code, 4);
  assert.deepEqual(result.json.rows.map(row => row.refusals.map(item => item.message)), [['tests/x.json matches 2 Stories: user_stories/a/x.md and user_stories/b/x.md. Rename one.']]);
});

// Wrong: a test whose story_path named another Story was checked against that other Story.
test('NAME6: a matched test that is not valid JSON, or whose story_path names another Story, is refused with the file', async t => {
  const setup = repoWith(t, { 'user_stories/p17.md': story('P17'), 'user_stories/other.md': story('Other'),
    'tests/p17.json': scenario('user_stories/other.md'), 'tests/other.json': '{"schema_version": "prompt-runtime.program-scenario.v1",' });
  let result = await check(setup, ['p17'], { '--json': true });
  assert.equal(result.code, 4);
  assert.deepEqual(result.json.rows[0].refusals.map(item => [item.code, item.section, item.message]), [['pdd-story-mismatch', 'story_path',
    'tests/p17.json is the test of user_stories/p17.md by its name, but its story_path names user_stories/other.md. Make them agree.']]);
  result = await check(setup, ['other'], { '--json': true });
  assert.equal(result.code, 4);
  assert.equal(result.json.rows[0].refusals[0].code, 'invalid-document');
  assert.match(result.json.rows[0].refusals[0].message, /^tests\/other\.json is not valid JSON: /);
});

// Wrong: the server found the tests in the upload by itself, skipping files over 1 MiB with no message.
test('NAME7: when the interpreter lists lint-tests, the lint request names the selected tests; otherwise it is unchanged', async t => {
  for (const features of [['lint-tests'], undefined]) {
    const setup = harbor(t), fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
    fake.capacity = () => ({ status: 200, json: { maintenance: null, ...(features ? { features } : {}) } });
    const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: setup.state });
    const code = await runCheck({ words: ['place-order'], options: {}, cwd: setup.repo }, ports);
    assert.equal(code, 0, ports.stdout.text + ports.stderr.text);
    const lint = fake.posts.find(entry => entry.command === 'lint').request;
    if (features) { assert.deepEqual(lint.tests, ['tests/place-order.json']); assert.deepEqual(lint.app_maps, []); }
    else { assert.equal(Object.hasOwn(lint, 'tests'), false); assert.equal(Object.hasOwn(lint, 'app_maps'), false); }
  }
});

// Wrong: the Try guide read every JSON file up to 1 MiB, so a big test was missing and a scenario anywhere was a test.
test('NAME8: the Try guide reads tests by the same rule, in full, and marks a conflict as incomplete', t => {
  const big = scenario('user_stories/big.md', { initial_world: { kv: { notes: 'y'.repeat(1_500_000) } } });
  const setup = repoWith(t, { 'user_stories/big.md': story('Big'), 'tests/big.json': big,
    'user_stories/delta.md': story('Delta'), 'scenarios/delta.json': scenario('user_stories/delta.md') });
  const records = readAgentScenarios({ root: setup.repo });
  assert.deepEqual(records.map(record => [record.path, record.doc.story_path]), [['tests/big.json', 'user_stories/big.md']]);
  assert.equal(records.incomplete, false);
  const twice = repoWith(t, { 'user_stories/big.md': story('Big'), 'tests/big.json': big, 'test/big.json': big });
  const none = readAgentScenarios({ root: twice.repo });
  assert.deepEqual(none.map(record => record.path), []);
  assert.equal(none.incomplete, true);
});

// Wrong: with Stories a and a.b, tests/a.b.json was given to one of them with no message.
test('NAME9: a file name that fits two Story names is an error that names both Stories', t => {
  const setup = repoWith(t, { 'user_stories/a.md': story('A'), 'user_stories/a.b.md': story('A B'), 'user_stories/x.y.md': story('X Y'),
    'tests/a.b.json': scenario('user_stories/a.b.md'), 'tests/a.b.c.json': scenario('user_stories/a.b.md'), 'tests/a.c.json': scenario('user_stories/a.md'),
    'tests/x.y.json': scenario('user_stories/x.y.md'), 'tests/x.y.z.json': scenario('user_stories/x.y.md') });
  const found = findTests({ root: setup.repo });
  assert.deepEqual(found.tests.map(item => [item.path, item.storyPath, item.error ?? null]), [
    ['tests/a.b.c.json', null, 'tests/a.b.c.json matches 2 Stories: user_stories/a.b.md and user_stories/a.md. Rename one.'],
    ['tests/a.b.json', null, 'tests/a.b.json matches 2 Stories: user_stories/a.b.md and user_stories/a.md. Rename one.'],
    ['tests/a.c.json', 'user_stories/a.md', null],
    ['tests/x.y.json', 'user_stories/x.y.md', null],
    ['tests/x.y.z.json', 'user_stories/x.y.md', null]]);
  assert.deepEqual(found.warnings, [
    'Warning: tests/a.b.c.json matches 2 Stories: user_stories/a.b.md and user_stories/a.md. Rename one.',
    'Warning: tests/a.b.json matches 2 Stories: user_stories/a.b.md and user_stories/a.md. Rename one.']);
  assert.deepEqual(selectTests(found, ['a.b']).selected.map(item => item.path), ['tests/a.b.c.json', 'tests/a.b.json']);
});

// Wrong: one unreadable test stopped pdd test for every Story; a test over the upload limit was read anyway.
test('NAME10: an unreadable test or a test over the upload limit is refused by name, never uploaded, and other Stories still run', async t => {
  const setup = repoWith(t, { 'user_stories/place-order.md': story(), 'tests/place-order.json': scenario('user_stories/place-order.md'),
    'user_stories/locked.md': story('Locked'), 'tests/locked.json': scenario('user_stories/locked.md'),
    'user_stories/huge.md': story('Huge'), 'tests/huge.json': '{}' });
  truncateSync(join(setup.repo, 'tests/huge.json'), 11 * 1024 * 1024);
  chmodSync(join(setup.repo, 'tests/locked.json'), 0o000);
  let found;
  assert.doesNotThrow(() => { found = findTests({ root: setup.repo }); });
  assert.deepEqual(found.tests.map(item => [item.path, item.error ?? null]), [
    ['tests/huge.json', 'tests/huge.json is 11.0 MB. The upload limit is 10 MB, so pdd cannot send it.'],
    ['tests/locked.json', 'tests/locked.json cannot be read: EACCES.'],
    ['tests/place-order.json', null]]);
  const files = await check(setup, [], { '--files': true });
  assert.equal(files.code, 4, files.err);
  assert.ok(files.out.includes('tests/locked.json') && files.out.includes('EACCES'));
  assert.doesNotMatch(files.out, /tests\/(?:huge|locked)\.json +\d+ bytes/);
  // pdd test runs the other Stories: the two refused tests are neither uploaded nor named for lint.
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  fake.capacity = () => ({ status: 200, json: { maintenance: null, features: ['lint-tests'] } });
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: join(setup.home, 'state') };
  let made = portsFor(env);
  assert.equal(await runCheck({ words: [], options: { '--json': true }, cwd: setup.repo }, made.ports), 4, made.ports.stderr.text);
  const json = JSON.parse(made.ports.stdout.text);
  assert.deepEqual(json.rows.map(row => [row.test, row.state]), [['tests/huge.json', 'not run'], ['tests/locked.json', 'not run'], ['tests/place-order.json', 'passed']]);
  assert.deepEqual(fake.posts.find(post => post.command === 'lint').request.tests, ['tests/place-order.json']);
  assert.ok(fake.posts.every(post => !post.tar.includes(Buffer.from('tests/huge.json')) && !post.tar.includes(Buffer.from('tests/locked.json'))));
  made = portsFor(env);
  assert.equal(await runCheck({ words: [json.batch], options: { '--read': true, '--json': true }, cwd: setup.repo }, made.ports), 4, made.ports.stderr.text);
});

// Wrong: a saved Try case made a second test file for a Story whose test pdd could not use.
test('NAME11: a saved case never makes a second test for a Story; a test path that is taken is refused', t => {
  const setup = repoWith(t, { 'user_stories/s.md': story('S'), 'runtime/tests/s.json': '{"schema_version":', 'user_stories/q.md': story('Q'), 'tests/q.json/notes.txt': 'x' });
  const env = { HOME: setup.home, PDD_STATE_DIR: join(setup.home, 'state') };
  const saved = (storyPath, originalPath) => ({ id: 'c1', name: 'saved', original_path: originalPath, story_path: storyPath, test: JSON.parse(scenario(storyPath)) });
  // The approved received-case contract retains invalid exact originals durably,
  // rather than choosing or creating another Story test. No writer handoff is needed for refusal.
  for (const [storyPath, originalPath] of [['user_stories/s.md', 'runtime/tests/s.json'], ['user_stories/q.md', 'tests/q.json']]) {
    const received = saved(storyPath, originalPath), result = saveDoorCase(setup.repo, received, { env });
    assert.ok(result.startsWith(`not added: the original test ${originalPath} is missing or no longer belongs to ${storyPath}. Restore it before importing the case`), result);
    assert.match(result, /Case retained at .* \(pending [a-f0-9]+\.[a-f0-9]+\)\.$/);
    const retained = JSON.parse(readFileSync(result.match(/Case retained at (.*) \(pending /)[1], 'utf8'));
    assert.deepEqual(retained.saved, received, 'complete received case remains recoverable');
    assert.equal(retained.raw, JSON.stringify(received));
  }
  assert.equal(readFileSync(join(setup.repo, 'runtime/tests/s.json'), 'utf8'), '{"schema_version":');
  assert.equal(readFileSync(join(setup.repo, 'tests/q.json/notes.txt'), 'utf8'), 'x');
  assert.equal(existsSync(join(setup.repo, 'tests/s.json')), false);
  assert.deepEqual(readdirSync(join(setup.repo, 'tests')), ['q.json']);
});

// The selected tests declare the maps that lint must judge, even when the CLI names none.
test('NAME12: named lint refuses unknown scenario map keys before upload', async t => {
  const setup = repoWith(t, {
    'user_stories/place-order.md': story(),
    'tests/place-order.json': scenario('user_stories/place-order.md', { app_maps: ['maps/b.json', 'maps/a.json', 'maps/a.json'] }),
    'user_stories/other.md': story('Other'),
    'tests/other.json': scenario('user_stories/other.md', { app_maps: ['maps/other.json'] }),
    'maps/a.json': '{}', 'maps/b.json': '{}', 'maps/other.json': '{}',
    'pdd-source.json': JSON.stringify({ include: ['maps/a.json', 'maps/b.json', 'maps/other.json'] }),
  });
  const fake = await fakeRuntime(t, (entry, f) => f.normal(entry));
  fake.capacity = () => ({ status: 200, json: { maintenance: null, features: ['lint-tests'] } });
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: join(setup.home, 'state') });
  const code = await runCheck({ words: ['place-order'], options: { '--lint': true }, cwd: setup.repo }, ports);
  // P1 owns the closed scenario keys. The capture check now applies it to
  // lint too; app_maps is not an admitted scenario key.
  assert.equal(code, 4, ports.stdout.text + ports.stderr.text);
  assert.match(ports.stdout.text, /invalid-document/);
  assert.match(ports.stdout.text, /app_maps/);
  assert.equal(fake.posts.length, 0);
});

// A local refusal remains a fact while the remote lint waits or cannot run.
for (const state of ['running', 'not_run']) test(`NAME13: ${state} lint preserves local discovery refusals`, async t => {
  const setup = repoWith(t, {
    'user_stories/place-order.md': story(), 'tests/place-order.json': scenario('user_stories/place-order.md'),
    'user_stories/broken.md': story('Broken'), 'tests/broken.json': '{"schema_version":"prompt-runtime.program-scenario.v1",',
  });
  const fake = await fakeRuntime(t, (entry, f) => state === 'not_run'
    ? { status: 503, json: { error: { code: 'pool-low-room', message: 'No login room.' } } }
    : { status: 202, json: f.job(entry.request?.requestId ?? entry.url.split('/').at(-1), 'lint', 'running') });
  const stateDir = join(setup.home, 'state');
  const { ports } = portsFor({ HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: stateDir });
  assert.equal(await runCheck({ words: [], options: { '--lint': true, '--json': true }, cwd: setup.repo }, ports), state === 'running' ? 3 : 5);
  const batch = readdirSync(join(stateDir, 'batches'))[0];
  const saved = JSON.parse(readFileSync(join(stateDir, 'batches', batch, 'batch.json')));
  assert.deepEqual(saved.rows.map(row => [row.test, row.state, row.phase]), [
    ['tests/broken.json', 'not run', 'local'], ['tests/place-order.json', 'not run', 'lint']]);
  assert.equal(saved.rows[0].refusals[0].code, 'invalid-document');
  if (state === 'not_run') assert.equal(JSON.parse(ports.stdout.text).rows[0].state, 'not run');
});

// Receipt refresh must reuse the same source as dispatch, including the excluded-test decision.
test('NAME14: a UUID receipt refresh keeps unsent tests out of capture and caches the completed Story', async t => {
  const setup = repoWith(t, {
    'user_stories/place-order.md': story(), 'tests/place-order.json': scenario('user_stories/place-order.md'),
    'user_stories/huge.md': story('Huge'), 'tests/huge.json': '{}',
  });
  truncateSync(join(setup.repo, 'tests/huge.json'), 11 * 1024 * 1024);
  let running = true;
  const fake = await fakeRuntime(t, (entry, f) => entry.command === 'lint'
    ? { status: 200, json: f.lint(entry.request.requestId) }
    : { status: 200, json: f.check(entry.request?.requestId ?? entry.url.split('/').at(-1), running ? 'running' : 'passed') });
  const env = { HOME: setup.home, PDD_RUNTIME_URL: fake.origin, PDD_STATE_DIR: join(setup.home, 'state') };
  const invoke = async (words = [], options = {}) => {
    const { ports } = portsFor(env);
    const code = await runCheck({ words, options: { '--json': true, ...options }, cwd: setup.repo, cache: true }, ports);
    return { code, json: JSON.parse(ports.stdout.text) };
  };
  const first = await invoke([], { '--timeout': 1 });
  assert.deepEqual(first.json.rows.map(row => [row.test, row.state]), [['tests/huge.json', 'not run'], ['tests/place-order.json', 'sent']]);
  const id = first.json.rows[1].request_id;
  running = false;
  assert.equal((await invoke([id], { '--read': true })).code, 0);
  const cache = JSON.parse(readFileSync(join(setup.repo, '.pdd/cache/test/stories.json')));
  assert.equal(cache.stories['user_stories/place-order.md'].outcome, 'passed');
  assert.deepEqual(cache.stories['user_stories/place-order.md'].pass.tests, ['tests/place-order.json']);
  assert.equal(fake.posts.filter(post => post.command === 'check').length, 1);
});
