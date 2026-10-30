import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { parseProductDocuments, readProduct } from '../src/product.mjs';
import { selectJourneys } from '../src/product-composition.mjs';
import { runCheck } from '../src/runtime-client.mjs';

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
