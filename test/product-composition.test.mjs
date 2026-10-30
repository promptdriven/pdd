import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { parseProductDocuments, parseProductWorldWriters, productStatus, readProduct } from '../src/product.mjs';
import { selectJourneys } from '../src/product-composition.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { captureSource } from '../src/runtime-preflight.mjs';

const coffee = relative => readFileSync(new URL(`../examples/coffee-pickup/${relative}`, import.meta.url), 'utf8');

test('snapshot product parser preserves the async reader result and boundaries', async () => {
  const mapText = coffee('product/map.md'), planText = coffee('product/plan.md');
  const parsed = parseProductDocuments({ mapText, planText });
  const actual = await readProduct({ cwd: '/repo' }, { readFile: async path => path.endsWith('/map.md') ? mapText : planText });
  assert.deepEqual(parsed.product, actual);
  assert.deepEqual(parsed.boundaries.map(row => row.Contract), ['contracts/phone-server.md', 'contracts/server-barista.md']);
  assert.equal(parsed.product.stories.filter(story => story.tag === 'CORE').length, 12);
  assert.equal(parsed.product.runs.length, 4);
});

test('pure and async readers retain invalid-plan validation', async () => {
  const mapText = coffee('product/map.md');
  assert.throws(() => parseProductDocuments({ mapText, planText: '' }), error => error.code === 'invalid-product' && error.message.includes('no planned runs'));
  await assert.rejects(readProduct({ cwd: '/repo' }, { readFile: async path => path.endsWith('/map.md') ? mapText : '' }), error => error.code === 'invalid-product' && error.message.includes('no planned runs'));
});

test('world writer declarations preserve duplicates and meaningful escaped cells', () => {
  const worldText = '# World\n| Key | Writer | Readers |\n|---|---|---|\n| `orders` | phone | server |\n| orders | phone | server |\n| orders | barista | phone |\n| display\\|state | phone | server |\n';
  assert.deepEqual(parseProductWorldWriters({ worldText }), [
    { key: 'orders', writer: 'phone' }, { key: 'orders', writer: 'phone' },
    { key: 'orders', writer: 'barista' }, { key: 'display|state', writer: 'phone' },
  ]);
  for (const text of ['', '| Key |\n|---|\n| orders |', '| Key | Writer |\n|---|---|\n| orders | |']) {
    assert.throws(() => parseProductWorldWriters({ worldText: text }), error => error.code === 'invalid-product' && error.message.includes('world.md'));
  }
});

const rows = [
  { testPath: 'test/J1-a.json', storyPath: 'user_stories/journeys/J1-order.md' },
  { testPath: 'test/J10.json', storyPath: 'user_stories/journeys/J10-return.md' },
  { testPath: 'test/J1-b.json', storyPath: 'user_stories/journeys/J1-order.md' },
  { testPath: 'test/nested.json', storyPath: 'user_stories/journeys/nested/J1-order.md' },
  { testPath: 'test/example.json', storyPath: 'examples/shop/user_stories/journeys/J1-order.md' },
];

test('journeys keep discovery order, complete IDs, and multiple tests for one Story', () => {
  assert.deepEqual(selectJourneys(rows), ['test/J1-a.json', 'test/J10.json', 'test/J1-b.json']);
  assert.deepEqual(selectJourneys(rows, 'J1'), ['test/J1-a.json', 'test/J1-b.json']);
  assert.deepEqual(selectJourneys(rows, 'user_stories/journeys/J1-order.md'), ['test/J1-a.json', 'test/J1-b.json']);
  assert.deepEqual(selectJourneys(rows, 'test/J1-b.json'), ['test/J1-b.json']);
  assert.throws(() => selectJourneys(rows, 'j1'), error => error.code === 'invalid-journey' && error.message.includes('J10-return'));
  assert.throws(() => selectJourneys([...rows, { testPath: 'test/other.json', storyPath: 'user_stories/journeys/J1-other.md' }], 'J1'), error => error.code === 'invalid-journey' && error.message.includes('Ambiguous'));
});

test('product choose journeys: unchanged prompt-space cases execute the real public boundary', () => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/product-choose-journeys.json', import.meta.url)));
  for (const step of scenario.steps) {
    let result, error;
    try { result = selectJourneys(step.input.tests, step.input.selector); } catch (caught) { error = caught; }
    if (!step.expected_error) assert.equal(error, undefined, step.step_id);
    for (const check of step.checks) {
      assert.equal(check.op, 'equals');
      assert.deepEqual(check.target === 'result' ? result : error?.code, check.value, `${step.step_id}/${check.criterion_id}`);
    }
  }
});

test('check --journeys uses ordinary source capture and excludes parts, examples and J10', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-product-journeys-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  cpSync(new URL('./fixtures/harbor', import.meta.url), root, { recursive: true });
  const source = JSON.parse(readFileSync(join(root, 'tests/place-order.json'), 'utf8'));
  const story = readFileSync(join(root, source.story_path), 'utf8');
  for (const [name, storyPath] of [['J1', 'user_stories/journeys/J1-order.md'], ['J10', 'user_stories/journeys/J10-order.md'], ['nested', 'examples/x/user_stories/journeys/J1-order.md']]) {
    mkdirSync(join(root, storyPath, '..'), { recursive: true });
    writeFileSync(join(root, storyPath), story);
    writeFileSync(join(root, `tests/${name}.json`), JSON.stringify({ ...source, story_path: storyPath }));
  }
  for (const args of [['init', '-q'], ['add', '-A']]) {
    const result = spawnSync('git', args, { cwd: root, encoding: 'utf8' });
    assert.equal(result.status, 0, result.stderr);
  }
  const stdout = { text: '', write(value) { this.text += value; } }, stderr = { text: '', write(value) { this.text += value; } };
  let outside = 0;
  const ports = { env: {}, stdout, stderr, gh: () => { outside++; throw Error('Unexpected gh'); }, fetch: async () => { outside++; throw Error('Unexpected network'); } };
  assert.equal(await runCheck({ cwd: root, words: ['J1'], options: { '--journeys': true, '--files': true } }, ports), 0, stderr.text);
  assert.match(stdout.text, /tests\/J1\.json/);
  assert.doesNotMatch(stdout.text, /tests\/(?:J10|nested|place-order)\.json/);
  assert.equal(outside, 0);
  stdout.text = ''; stderr.text = '';
  assert.equal(await runCheck({ cwd: root, words: ['J99'], options: { '--journeys': true, '--files': true } }, ports), 2);
  assert.match(stderr.text, /Unknown journey J99/);
  assert.equal(outside, 0);
});

test('journey progress uses actual selected source identity across its parts', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-product-journey-progress-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const copy = (source, target) => { mkdirSync(join(root, target, '..'), { recursive: true }); cpSync(new URL(source, import.meta.url), join(root, target), { recursive: true }); };
  copy('../examples/coffee-pickup/', 'examples/coffee-pickup');
  copy('../examples/coffee-pickup/product/', 'product');
  copy('../user_stories/journeys/J1-coffee-pickup.md', 'user_stories/journeys/J1-coffee-pickup.md');
  copy('./runtime/J1-coffee-pickup.json', 'test/J1.json');
  writeFileSync(join(root, 'unrelated.txt'), 'unrelated');
  for (const args of [['init', '-q'], ['add', '-A']]) assert.equal(spawnSync('git', args, { cwd: root }).status, 0);
  const source = { kind: 'runtime-capture-v1', tests: ['test/J1.json'], sha256: captureSource(root, { tests: ['test/J1.json'], appMap: null }).sha256 };
  const run = { number: 81, root, state: 'running', pr: [], runtimeHistory: [{ at: 1, source,
    summary: 'Runtime check (J1-coffee-pickup): ✓ 2 of 2 criteria\nRuntime check (J10-unrelated): ✓ 1 of 1 criteria' }] };
  const issue = { number: 81, body: '<!-- pdd-product: run=journeys -->', user: { login: 'project-member' }, author_association: 'MEMBER', created_at: '2026-10-01T00:00:00Z', repository_url: 'https://api.github.com/repos/example/coffee' };
  let savedState = null;
  const ports = { listRuns: async () => [run], resolveRepository: async () => ({ repository: 'example/coffee', defaultBranch: 'alpha' }), planOnBase: async () => true,
    readProductState: async () => ({ json: savedState }), writeProductState: async ({ json }) => { savedState = json; return {}; },
    lockProductState: async () => ({ handle: 'owned-test-lock' }), unlockProductState: async () => ({}), now: async () => ({ milliseconds: 100000 }),
    issueByNumber: async () => issue,
    issuePage: async ({ page }) => ({ items: page === 1 ? [issue] : [], total_count: 1, incomplete_results: false }),
    timelinePage: async () => [] };
  const journey = async () => (await productStatus({ cwd: root }, ports)).parts.find(row => row.part === 'journeys');
  assert.deepEqual(await journey(), { part: 'journeys', total: 1, pass: 1, stale: 0, notRun: 0 });
  writeFileSync(join(root, 'unrelated.txt'), 'changed unrelated');
  assert.equal((await journey()).pass, 1);
  const part = join(root, 'examples/coffee-pickup/prompts/barista/board.prompt.md');
  writeFileSync(part, `${readFileSync(part, 'utf8')}\nA changed barista rule.\n`);
  assert.deepEqual(await journey(), { part: 'journeys', total: 1, pass: 0, stale: 1, notRun: 0 });
});
