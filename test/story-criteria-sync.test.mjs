import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { harbor, storyTest, fakeRuntime, portsFor } from './runtime-fake.mjs';
import { runCheck } from '../src/runtime-client.mjs';
import { captureSource, fillHashes, findTests, preflight, scenarioShapeRefusal } from '../src/runtime-preflight.mjs';

const cli = fileURLToPath(new URL('../bin/pdd.mjs', import.meta.url));
const git = (cwd, ...args) => {
  const result = spawnSync('git', args, { cwd, encoding: 'utf8' });
  assert.equal(result.status, 0, result.stderr);
};
const readJson = (repo, path) => JSON.parse(readFileSync(join(repo, path), 'utf8'));
const tarScenario = (tar, path) => {
  const out = spawnSync('tar', ['-xOf', '-', path], { input: tar, encoding: 'utf8' });
  assert.equal(out.status, 0, out.stderr);
  return JSON.parse(out.stdout);
};
const ALL_PASSED_CHECKS = [
  { criterion_id: 'AC1', target: 'result', path: '/totalCents', op: 'equals', expected: 900, actual: 900, passed: true },
  { criterion_id: 'AC2', target: 'result', path: '/customer', op: 'equals', expected: 'Sam', actual: 'Sam', passed: true },
  { criterion_id: 'AC3', target: 'world', path: '/orders/0/customer', op: 'equals', expected: 'Sam', actual: 'Sam', passed: true },
];

test('3298 AC1: scenario with story_path and omitted criteria resolves AC1..ACN in preflight, capture and check', async t => {
  const { repo, home, state } = harbor(t, r => {
    const doc = readJson(r, 'tests/place-order.json');
    delete doc.criteria;
    writeFileSync(join(r, 'tests/place-order.json'), JSON.stringify(doc, null, 2) + '\n');
  });
  const beforeBytes = readFileSync(join(repo, 'tests/place-order.json'), 'utf8');
  assert.equal(Object.hasOwn(JSON.parse(beforeBytes), 'criteria'), false);

  const found = findTests({ root: repo });
  const selected = found.tests.filter(item => item.path === 'tests/place-order.json');
  const checked = preflight({ root: repo, found, selected });
  assert.deepEqual(checked.rows[0].refusals, []);
  assert.equal(checked.rows[0].criteria_total, 3);
  assert.equal(checked.rows[0].not_checked, undefined);

  const captured = captureSource(repo, { tests: ['tests/place-order.json'] });
  const uploaded = tarScenario(captured.tar, 'tests/place-order.json');
  assert.equal(scenarioShapeRefusal(uploaded, 'tests/place-order.json'), null);
  assert.equal(uploaded.criteria.length, 3);
  assert.deepEqual(uploaded.criteria.map(item => item.id), ['AC1', 'AC2', 'AC3']);
  assert.match(uploaded.criteria[0].text, /900/);

  const fake = await fakeRuntime(t, entry => {
    if (entry.method === 'POST' && entry.command === 'lint') return { status: 200, json: fake.lint(entry.request.requestId) };
    if (entry.method === 'POST') return { status: 202, json: fake.check(entry.request.requestId, 'queued', ALL_PASSED_CHECKS) };
    return { status: 200, json: fake.check(entry.url.split('/').at(-1), 'passed', ALL_PASSED_CHECKS) };
  });
  const { ports } = portsFor({ HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin });
  assert.equal(await runCheck({ cwd: repo, words: ['place-order'], options: { '--files': true } }, ports), 0);
  ports.stdout.text = '';
  assert.equal(await runCheck({ cwd: repo, words: ['place-order'], options: { '--json': true } }, ports), 0);
  const report = JSON.parse(ports.stdout.text);
  assert.equal(report.rows[0].state, 'passed');
  assert.deepEqual(report.rows[0].criteria, { passed: 3, total: 3 });
  assert.equal(readFileSync(join(repo, 'tests/place-order.json'), 'utf8'), beforeBytes, 'authored scenario stays criteria-less');
});

test('3298 AC1: scenario with story_path and ID-only criteria resolves text and refuses out-of-range or duplicate IDs', t => {
  for (const criteria of [
    ['AC1', 'AC2', 'AC3'],
    [{ id: 'AC1' }, { id: 'AC2' }, { id: 'AC3' }],
    ['AC1'],
  ]) {
    const { repo } = harbor(t, r => {
      const doc = readJson(r, 'tests/place-order.json');
      doc.criteria = criteria;
      if (criteria.length === 1) doc.steps[0].checks = doc.steps[0].checks.filter(check => check.criterion_id === 'AC1');
      writeFileSync(join(r, 'tests/place-order.json'), JSON.stringify(doc, null, 2) + '\n');
    });
    const found = findTests({ root: repo });
    const selected = found.tests.filter(item => item.path === 'tests/place-order.json');
    const checked = preflight({ root: repo, found, selected });
    assert.deepEqual(checked.rows[0].refusals, [], JSON.stringify(criteria));
    assert.equal(checked.rows[0].criteria_total, 3);
    assert.equal((checked.rows[0].not_checked ?? []).length, criteria.length === 1 ? 2 : 0);

    const captured = captureSource(repo, { tests: ['tests/place-order.json'] });
    const uploaded = tarScenario(captured.tar, 'tests/place-order.json');
    assert.equal(scenarioShapeRefusal(uploaded, 'tests/place-order.json'), null);
    assert.equal(uploaded.criteria.length, 3);
    assert.equal(Array.isArray(uploaded.check_exemptions) ? uploaded.check_exemptions.length : 0, criteria.length === 1 ? 2 : 0);
  }

  for (const [badCriteria, expectedCode] of [
    [['AC99'], 'invalid-criterion'],
    [[{ id: 'AC0' }], 'invalid-criterion'],
    [['CUSTOM'], 'invalid-criterion'],
    [['AC1', 'AC1'], 'duplicate-criterion'],
  ]) {
    const { repo } = harbor(t, r => {
      const doc = readJson(r, 'tests/place-order.json');
      doc.criteria = badCriteria;
      writeFileSync(join(r, 'tests/place-order.json'), JSON.stringify(doc, null, 2));
    });
    const found = findTests({ root: repo });
    const selected = found.tests.filter(item => item.path === 'tests/place-order.json');
    const checked = preflight({ root: repo, found, selected });
    assert.equal(checked.rows[0].refusals[0]?.code, expectedCode, JSON.stringify(badCriteria));
    assert.throws(() => captureSource(repo, { tests: ['tests/place-order.json'] }), error => error.code === expectedCode);
  }
});

test('3298 AC1: pdd test --fill-hash syncs stale criteria[].text in place while preserving exact tokens and scoping', async t => {
  const { repo, home, state } = harbor(t, r => {
    storyTest(r, 'other');
    mkdirSync(join(r, 'contracts'), { recursive: true });
    writeFileSync(join(r, 'contracts/world.json'), '{"orders":[]}\n');
    // Author a scenario with an unexpanded $seed reference and an exact >53-bit integer token.
    const raw = `{
  "schema_version": "prompt-runtime.program-scenario.v1",
  "story_path": "user_stories/place-order.md",
  "criteria": [
    { "id": "AC2", "text": ${JSON.stringify(readJson(r, 'tests/place-order.json').criteria[1].text)} },
    { "id": "AC1", "text": ${JSON.stringify(readJson(r, 'tests/place-order.json').criteria[0].text)} },
    { "id": "AC3", "text": ${JSON.stringify(readJson(r, 'tests/place-order.json').criteria[2].text)} }
  ],
  "initial_world": {
    "orders": { "$seed": "contracts/world.json#/orders" },
    "audit_seq": 9007199254740993
  },
  "steps": ${JSON.stringify(readJson(r, 'tests/place-order.json').steps, null, 2)}
}\n`;
    writeFileSync(join(r, 'tests/place-order.json'), raw);
  });

  // Edit both Stories so both scenarios become stale with story-criterion-mismatch.
  const editStory = (path, from, to) => {
    const full = join(repo, path), updated = readFileSync(full, 'utf8').replace(from, to);
    assert.notEqual(updated, readFileSync(full, 'utf8'));
    writeFileSync(full, updated);
  };
  editStory('user_stories/place-order.md', 'keeps the name "Sam"', 'retains the name "Sam"');
  editStory('user_stories/other.md', 'keeps the name "Sam"', 'records the name "Sam"');
  git(repo, 'add', '-A');

  const staleFound = findTests({ root: repo });
  assert.equal(preflight({ root: repo, found: staleFound, selected: staleFound.tests.filter(i => i.path === 'tests/place-order.json') }).rows[0].refusals[0]?.code, 'story-criterion-mismatch');
  assert.equal(preflight({ root: repo, found: staleFound, selected: staleFound.tests.filter(i => i.path === 'tests/other.json') }).rows[0].refusals[0]?.code, 'story-criterion-mismatch');

  // Scoped --fill-hash updates ONLY place-order, leaving other.json stale.
  const { ports } = portsFor({ HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' });
  ports.fetch = async () => { throw Error('unexpected network'); };
  ports.gh = () => { throw Error('unexpected gh'); };
  assert.equal(await runCheck({ cwd: repo, words: ['place-order'], options: { '--fill-hash': true } }, ports), 0);
  assert.match(ports.stdout.text, /Synced criteria: tests\/place-order\.json/);
  assert.doesNotMatch(ports.stdout.text, /tests\/other\.json/);

  const syncedRaw = readFileSync(join(repo, 'tests/place-order.json'), 'utf8');
  assert.match(syncedRaw, /"\$seed": "contracts\/world\.json#\/orders"/, 'unexpanded $seed preserved');
  assert.match(syncedRaw, /"audit_seq": 9007199254740993/, 'exact >53-bit integer token preserved');
  assert.match(syncedRaw, /retains the name \\"Sam\\"/, 'AC2 updated in place despite AC2/AC1/AC3 order');

  const afterScoped = findTests({ root: repo });
  assert.deepEqual(preflight({ root: repo, found: afterScoped, selected: afterScoped.tests.filter(i => i.path === 'tests/place-order.json') }).rows[0].refusals, []);
  assert.equal(preflight({ root: repo, found: afterScoped, selected: afterScoped.tests.filter(i => i.path === 'tests/other.json') }).rows[0].refusals[0]?.code, 'story-criterion-mismatch');

  // Unscoped CLI `pdd test --fill-hash` syncs the remaining stale scenario and preserves default enumerable keys.
  const direct = fillHashes({ root: repo });
  assert.deepEqual(Object.keys(direct), ['filled', 'current', 'refused', 'stale', 'warnings']);
  assert.deepEqual(direct.synced, [{ path: 'tests/other.json' }]);

  const afterAll = findTests({ root: repo });
  assert.deepEqual(preflight({ root: repo, found: afterAll, selected: afterAll.tests }).rows.flatMap(row => row.refusals), []);

  // Verify real CLI `pdd lint --local` passes cleanly afterwards with 0 errors.
  const localLint = spawnSync(process.execPath, [cli, 'lint', '--local'], {
    cwd: repo, encoding: 'utf8', env: { ...process.env, HOME: home, PDD_STATE_DIR: state },
  });
  assert.equal(localLint.status, 0, `${localLint.stdout}\n${localLint.stderr}`);
});
