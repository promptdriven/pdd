import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { harbor, storyTest, fakeRuntime, portsFor } from './runtime-fake.mjs';
import { runCheck, saveDoorCase, acquireCaseWriteOwnership } from '../src/runtime-client.mjs';
import { createTryTools } from '../src/try-mcp.mjs';
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
    [['AC1', 'ac-1'], 'duplicate-criterion'],
    [['AC1', 'ac1'], 'duplicate-criterion'],
    [[{ id: 'AC1', text: 'An order of 2 Espresso S and 1 Blueberry Muffin L has a total of 900 cents ($9.00).' }, 'ac-1'], 'duplicate-criterion'],
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

test('3298 AC1: fillHashes skips non-AC<N> or mixed criterion IDs without overwriting or inverting texts', t => {
  const { repo } = harbor(t, r => {
    const doc = readJson(r, 'tests/place-order.json');
    doc.criteria = [
      { id: 'AC2', text: doc.criteria[1].text },
      { id: 'CUSTOM', text: doc.criteria[0].text },
      { id: 'AC3', text: doc.criteria[2].text },
    ];
    for (const check of doc.steps[0].checks) {
      if (check.criterion_id === 'AC1') check.criterion_id = 'CUSTOM';
    }
    writeFileSync(join(r, 'tests/place-order.json'), JSON.stringify(doc, null, 2) + '\n');
  });
  const before = readFileSync(join(repo, 'tests/place-order.json'), 'utf8');
  const storyFull = join(repo, 'user_stories/place-order.md');
  writeFileSync(storyFull, readFileSync(storyFull, 'utf8').replace('keeps the name "Sam"', 'retains the name "Sam"'));
  git(repo, 'add', '-A');

  const res = fillHashes({ root: repo });
  assert.deepEqual(res.synced, []);
  assert.equal(readFileSync(join(repo, 'tests/place-order.json'), 'utf8'), before, 'mixed/custom IDs must not be overwritten');
});

test('3298 AC1: saveDoorCase and MCP try_save_case work when original scenario omits criteria or uses ID-only criteria', async t => {
  for (const mode of ['omitted', 'id-only']) {
    const { repo, home, state } = harbor(t, r => {
      const doc = readJson(r, 'tests/place-order.json');
      if (mode === 'omitted') delete doc.criteria;
      else doc.criteria = ['AC1', 'AC2', 'AC3'];
      doc.steps[0].checks.push({ criterion_id: 'AC1', target: 'world', path: '', op: 'equals', value: {} });
      writeFileSync(join(r, 'tests/place-order.json'), JSON.stringify(doc, null, 2) + '\n');
    });
    const env = { ...process.env, HOME: home, PDD_STATE_DIR: state };
    const found = findTests({ root: repo });
    const original = found.tests.find(item => item.path === 'tests/place-order.json');
    assert.equal(Object.keys(original).includes('rawDoc'), false, 'rawDoc stays non-enumerable');
    assert.equal(original.doc.criteria.length, 3);

    // 1. Continuation append via saveDoorCase maps criterion text to AC1..AC3 while preserving authored criteria shape on disk.
    const lease = await acquireCaseWriteOwnership({
      root: repo, testPath: 'tests/place-order.json',
      handoff: { kind: 'closed-editor', testPath: 'tests/place-order.json' },
    }, { env });
    let msg;
    try {
      msg = saveDoorCase(repo, {
        id: 'cont-1',
        name: 'Continuation case',
        story_path: 'user_stories/place-order.md',
        original_path: 'tests/place-order.json',
        world_before: {},
        test: {
          schema_version: 'prompt-runtime.program-scenario.v1',
          story_path: 'user_stories/place-order.md',
          criteria: [{ id: 'SERVER_C2', text: original.doc.criteria[1].text }],
          initial_world: {},
          steps: [{
            step_id: 'second-order',
            entry_path: 'prompts/place_order.prompt.md',
            operation: 'place_order',
            input: original.doc.steps[0].input,
            checks: [{ criterion_id: 'SERVER_C2', target: 'result', path: '/customerName', op: 'equals', value: 'Sam' }],
          }],
        },
      }, { env, writeOwnership: lease });
    } finally {
      lease.release();
    }
    assert.match(msg, /^added /, `${mode}: ${msg}`);
    const afterAppend = readJson(repo, 'tests/place-order.json');
    assert.equal(afterAppend.steps.length, 2);
    assert.equal(afterAppend.steps[1].checks[0].criterion_id, 'AC2');
    if (mode === 'omitted') assert.equal(Object.hasOwn(afterAppend, 'criteria'), false);
    else assert.deepEqual(afterAppend.criteria, ['AC1', 'AC2', 'AC3']);
    git(repo, 'add', '-A');
    const afterFound = findTests({ root: repo });
    assert.deepEqual(preflight({ root: repo, found: afterFound, selected: afterFound.tests }).rows[0].refusals, []);

    // 2. Isolated MCP try_save_case writes valid variant without failing original.doc comparison.
    const currentTest = afterFound.tests.find(item => item.path === 'tests/place-order.json');
    const owner = {
      root: repo,
      test: currentTest,
      record: { id: 'try-1', origin: 'http://127.0.0.1:9', login: 'tester' },
      model: { entries: [{ entry_path: 'prompts/place_order.prompt.md', operation: 'place_order', input_schema: { type: 'object' } }], calls: { cap: 20, remaining: 19 } },
      data: {},
    };
    const ownedIso = await acquireCaseWriteOwnership({
      root: repo, testPath: 'tests/place-order.json',
      handoff: { kind: 'closed-editor', testPath: 'tests/place-order.json' },
    }, { env });
    try {
      const mcpTools = createTryTools({ cwd: repo, env }, {
        env,
        readTryOwner: async () => owner,
        runDoorCall: async () => ({ id: 'mcp1', result: { customerName: 'Sam', pickupAt: '08:30', items: [], totalCents: 900 }, inputWorld: {}, world: {} }),
        saveDoorCase: (root, saved, opts) => saveDoorCase(root, saved, { ...opts, env, writeOwnership: ownedIso }),
      });
      await mcpTools.call('try_run', { entry: 'prompts/place_order.prompt.md#place_order', input: currentTest.doc.steps[0].input });
      const savedOut = await mcpTools.call('try_save_case', { criterion_id: 'AC1' });
      assert.match(savedOut.result, /^added /, `${mode} isolated: ${savedOut.result}`);
    } finally {
      ownedIso.release();
    }
    const variantDoc = readJson(repo, 'tests/place-order.try-mcp1.json');
    assert.equal(scenarioShapeRefusal(variantDoc, 'tests/place-order.try-mcp1.json'), null);
    assert.equal(variantDoc.criteria.length, 3);
  }
});

test('3298 AC1: pdd test --explain-bindings surfaces real criterion resolution refusals instead of invalid-document', async t => {
  // Valid omitted-criteria scenario succeeds in --explain-bindings.
  {
    const { repo, home, state } = harbor(t, r => {
      const doc = readJson(r, 'tests/place-order.json');
      delete doc.criteria;
      writeFileSync(join(r, 'tests/place-order.json'), JSON.stringify(doc, null, 2) + '\n');
    });
    const { ports } = portsFor({ HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' });
    assert.equal(await runCheck({ cwd: repo, words: ['place-order'], options: { '--explain-bindings': true, '--json': true } }, ports), 0);
    assert.equal(JSON.parse(ports.stdout.text).schema_version, 'pdd.binding-plans.v1');
  }

  // Bullet-only Story + omitted criteria surfaces story-criteria-missing, not invalid-document.
  {
    const { repo, home, state } = harbor(t, r => {
      writeFileSync(join(r, 'user_stories/place-order.md'), '# Place an order\n\n## Acceptance criteria\n- First bullet.\n- Second bullet.\n');
      const doc = readJson(r, 'tests/place-order.json');
      delete doc.criteria;
      writeFileSync(join(r, 'tests/place-order.json'), JSON.stringify(doc, null, 2) + '\n');
    });
    const { ports } = portsFor({ HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' });
    assert.equal(await runCheck({ cwd: repo, words: ['place-order'], options: { '--explain-bindings': true } }, ports), 4);
    assert.match(ports.stderr.text, /has no numbered "## Acceptance criteria" list/);
    assert.doesNotMatch(ports.stderr.text, /The test has no "criteria"/);
  }

  // Out-of-range ID-only criterion surfaces numbered bounds refusal, not generic shape refusal.
  {
    const { repo, home, state } = harbor(t, r => {
      const doc = readJson(r, 'tests/place-order.json');
      doc.criteria = ['AC99'];
      writeFileSync(join(r, 'tests/place-order.json'), JSON.stringify(doc, null, 2) + '\n');
    });
    const { ports } = portsFor({ HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'http://127.0.0.1:9' });
    assert.equal(await runCheck({ cwd: repo, words: ['place-order'], options: { '--explain-bindings': true } }, ports), 4);
    assert.match(ports.stderr.text, /Criterion ID "AC99" does not match numbered item 1\.\.3/);
  }
});
