import test from 'node:test';
import assert from 'node:assert/strict';
import childProcess, { spawnSync } from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import { mkdirSync, readFileSync, readdirSync, statSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import * as runtime from '../src/runtime-client.mjs';
import { captureSource } from '../src/runtime-preflight.mjs';
import { productStatus, productNext } from '../src/product.mjs';
import { harbor, portsFor, fakeRuntime, sha } from './runtime-fake.mjs';

const vectors = JSON.parse(readFileSync(new URL('./fixtures/product-unsent-checks.json', import.meta.url)));
const productScenario = JSON.parse(readFileSync(new URL('./runtime/product-saved-checks.json', import.meta.url)));
const copy = value => structuredClone(value);
const own = (value, key) => Object.hasOwn(value, key);
const forbidden = name => () => assert.fail(`Forbidden evidence-read effect: ${name}`);
const uuid = number => `11111111-1111-4111-8111-${String(number).padStart(12, '0')}`;
const sorted = rows => rows.map(row => copy(row)).sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
const sets = values => [...new Set(values.map(value => JSON.stringify(value)))].sort().map(value => JSON.parse(value));

function ownerWorld(fixture, variant) {
  const records = [], receipts = {}, captures = [];
  let sequence = 1;
  const passing = id => ({ ...copy(Object.values(vectors.receipts)[0]), requestId: id, id });
  for (const [index, spec] of fixture.batches.entries()) {
    const batch = copy(vectors.canonical_full_record);
    batch.batch = `20261030-120000-${String(index).padStart(4, '0')}`;
    batch.created_at = spec.created_at;
    batch.source_sha256 = spec.source_sha256 ?? batch.source_sha256;
    if (variant.intent === 'absent') delete batch.intent;
    batch.rows = spec.rows.map(input => {
      const row = copy(vectors.canonical_full_record.rows[0]);
      row.story = input.story; row.test = input.test;
      delete row.ended_at;
      if (input.attempt === 'unsent') {
        row.request_ids = []; row.state = variant.unsentState ?? input.state;
        if (own(input, 'ended_at')) row.ended_at = input.ended_at;
        return row;
      }
      const id = uuid(sequence++), receipt = passing(id);
      row.request_ids = [id]; row.state = input.attempt; row.ended_at = input.sent_at;
      receipt.state = input.attempt;
      if (input.attempt === 'failed') {
        for (const criterion of receipt.result.report.criterion_results) criterion.status = 'failed';
        for (const sample of receipt.result.report.samples) for (const step of sample.steps) for (const check of step.checks) check.passed = false;
      }
      if (input.prior_passing_attempt) {
        const prior = uuid(sequence++); row.request_ids.unshift(prior); receipts[`${batch.batch}/${prior}.json`] = passing(prior);
      }
      const defect = input.receipt_defect;
      if (defect === 'wrong-requestId') receipt.requestId = uuid(sequence++);
      else if (defect === 'wrong-id') receipt.id = uuid(sequence++);
      else if (defect === 'wrong-command') receipt.command = 'try';
      else if (defect === 'refused-receipt') receipt.state = 'refused';
      else if (defect === 'incomplete-criteria') receipt.result.report.criterion_results = [];
      else if (defect === 'failed-selected-check') receipt.result.report.samples[0].steps[0].checks[0].passed = false;
      else assert.ok(!defect || defect === 'missing-receipt', `Unmapped receipt defect ${defect}`);
      if (defect !== 'missing-receipt') receipts[`${batch.batch}/${id}.json`] = receipt;
      return row;
    });
    if (variant.order === 'unsent-first') batch.rows.reverse();
    const lintId = uuid(sequence++);
    batch.lint = { request_ids: [lintId], state: variant.lintState ?? spec.lint?.state ?? 'passed' };
    receipts[`${batch.batch}/${lintId}.json`] = { requestId: lintId, id: lintId, command: 'lint', state: batch.lint.state, ended_at: spec.lint?.ended_at };
    if (fixture.unreferenced_receipt) {
      const id = Object.keys(vectors.receipts)[0];
      receipts[`${batch.batch}/${id}.json`] = copy(vectors.receipts[id]); batch.lint.request_ids = [id];
    }
    records.push(batch);
  }
  const before = JSON.stringify({ records, receipts });
  const ports = {
    env: { PDD_STATE_DIR: '/state' }, realpath: path => path,
    readDir: path => { assert.equal(path, '/state/batches'); return records.map(row => row.batch); },
    readFile: path => {
      assert.ok(path.startsWith('/state/batches/'));
      const key = path.slice('/state/batches/'.length), name = key.split('/')[0];
      const value = key.endsWith('/batch.json') ? records.find(row => row.batch === name) : receipts[key];
      if (!value) throw Object.assign(Error('missing'), { code: 'ENOENT' });
      return JSON.stringify(value);
    },
    captureSource: (root, selection) => {
      assert.equal(root, '/project'); assert.equal(selection.appMap, null); captures.push(copy(selection.tests));
      const full = records.some(batch => JSON.stringify([...new Set(batch.rows.map(row => row.test))].sort()) === JSON.stringify(selection.tests));
      return { sha256: full ? vectors.default_capture_sha256 : 'c'.repeat(64) };
    },
    fetch: forbidden('fetch'), gh: forbidden('gh'), writeFile: forbidden('writeFile'), mkdir: forbidden('mkdir'), startRun: forbidden('workflow.start'),
  };
  return { records, receipts, captures, ports, unchanged: () => assert.equal(JSON.stringify({ records, receipts }), before) };
}

for (const fixture of vectors.cases) test(`unsent vector: ${fixture.case}`, async () => {
  for (const intent of fixture.intent_variants) for (const unsentState of fixture.unsent_state_variants ?? [undefined])
    for (const lintState of fixture.lint_state_variants ?? [undefined]) for (const order of fixture.row_order_variants ?? [undefined])
      for (const boundary of ['savedStoryEvidence', 'createSavedStoryEvidenceReader']) {
        const world = ownerWorld(fixture, { intent, unsentState, lintState, order });
        const result = boundary === 'savedStoryEvidence' ? await runtime.savedStoryEvidence(vectors.default_input, world.ports)
          : await runtime.createSavedStoryEvidenceReader(world.ports)(vectors.default_input);
        for (const [key, expected] of Object.entries(fixture.expected)) {
          if (key === 'summaries') assert.deepEqual(sorted(result.stories), sorted(expected), `${intent}/${unsentState}/${lintState}/${order}/${boundary}`);
          else if (key === 'capture_test_sets') assert.deepEqual(sets(world.captures), sets(expected), key);
          else assert.fail(`Not replayed: ${fixture.case} expectation ${key}`);
        }
        world.unchanged();
      }
});

const git = (cwd, ...args) => { const value = spawnSync('git', args, { cwd, encoding: 'utf8' }); assert.equal(value.status, 0, value.stderr); return value.stdout; };
const snapshot = root => readdirSync(root, { recursive: true }).map(path => {
  const full = join(root, path); return [path, statSync(full).isDirectory() ? 'directory' : sha(readFileSync(full))];
}).sort(([a], [b]) => a.localeCompare(b));
const issue = { number: 81, body: '<!-- pdd-product: run=server-1 -->', state: 'OPEN', author_association: 'MEMBER', user: { login: 'member' }, created_at: '2026-10-01T00:00:00Z' };
function productPorts(f) {
  let cache = null;
  return {
    listRuns: async () => [{ workflow: 'feature', number: 81, issue: { number: 81 }, root: f.repo, productMarker: issue.body, state: 'running', done: {}, runtimeHistory: [], stage: { id: 'prompt-story' } }],
    resolveRepository: async () => ({ repository: 'example/coffee', defaultBranch: 'alpha' }),
    issuePage: async () => ({ items: [issue], total_count: 1, incomplete_results: false }), issueByNumber: async () => issue,
    timelinePage: async () => [], planOnBase: async () => true, storyEvidence: async () => [],
    readProductState: async () => ({ json: cache }), writeProductState: async input => { cache = input.json; return {}; },
    lockProductState: async () => ({ handle: 'synthetic-lock' }), unlockProductState: async () => ({}), now: async () => ({ milliseconds: 100000 }),
    startRun: forbidden('workflow.start'), execFile: forbidden('Runtime authentication or external metadata command'),
  };
}
function productFiles(t) {
  const f = harbor(t);
  for (const [path, file] of Object.entries(productScenario.initial_world.files)) {
    const target = join(f.repo, path.slice('/project/'.length)); mkdirSync(dirname(target), { recursive: true }); writeFileSync(target, file.content);
  }
  const seed = JSON.parse(readFileSync(join(f.repo, 'tests/place-order.json'))), story = readFileSync(join(f.repo, seed.story_path), 'utf8'), selected = [];
  for (const id of ['S01', 'S02', 'S03', 'S04']) {
    const scenario = copy(seed); scenario.story_path = `user_stories/${id}-saved.md`;
    writeFileSync(join(f.repo, scenario.story_path), story);
    const path = `tests/${id}-saved.json`; writeFileSync(join(f.repo, path), JSON.stringify(scenario)); selected.push(path);
  }
  git(f.repo, 'add', '-A');
  const previous = process.env.PDD_STATE_DIR; process.env.PDD_STATE_DIR = f.state;
  t.after(() => { if (previous === undefined) delete process.env.PDD_STATE_DIR; else process.env.PDD_STATE_DIR = previous; });
  return { ...f, seed, selected };
}
function readGuard(t, f) {
  const before = snapshot(f.state), requests = f.fake && JSON.stringify([f.fake.posts, f.fake.gets, f.fake.deletes, f.fake.jsonPosts]);
  t.mock.method(globalThis, 'fetch', forbidden('Runtime network'));
  const native = childProcess.spawnSync;
  t.mock.method(childProcess, 'spawnSync', (file, args, options) => {
    assert.equal(file, 'git', 'Product reads may capture local Git source, but must not authenticate'); return native(file, args, options);
  });
  syncBuiltinESMExports();
  const check = () => {
    assert.deepEqual(snapshot(f.state), before, 'saved-check files and directories unchanged');
    if (f.fake) assert.equal(JSON.stringify([f.fake.posts, f.fake.gets, f.fake.deletes, f.fake.jsonPosts]), requests, 'no Runtime request while reading');
  };
  return { check, restore() { t.mock.restoreAll(); syncBuiltinESMExports(); } };
}
function productExpected(expected, status, next, facts = {}) {
  const values = {
    server: () => { const { part, ...counts } = status.parts.find(row => row.part === 'server'); return counts; },
    slice: () => { const { slice, ...counts } = status.slices[0]; return counts; },
    runState: () => status.runs[0].state, journeyReady: () => next.ready.includes('journeys'),
    legacy_hints: () => (status.warnings ?? []).filter(warning => warning.includes('Older checks are not counted')).length,
    serverPass: () => status.parts.find(row => row.part === 'server').pass,
    serverStale: () => status.parts.find(row => row.part === 'server').stale,
    serverNotRun: () => status.parts.find(row => row.part === 'server').notRun,
    ...Object.fromEntries(Object.entries(facts).map(([key, value]) => [key, () => value])),
  };
  for (const [key, value] of Object.entries(expected)) { assert.ok(values[key], `Not replayed: integration expectation ${key}`); assert.deepEqual(values[key](), value, key); }
}

const authentic = vectors.integration_cases.find(row => row.case === 'authentic-four-passes-then-four-unsent-default-product-read');
for (const stop of authentic.stop_variants) for (const intent of ['check', 'absent']) test(`unsent integration: ${authentic.case}/${stop}/${intent}`, async t => {
  const f = productFiles(t);
  let mode = 'pass', interrupt;
  const fake = await fakeRuntime(t, (entry, server) => {
    if (entry.command === 'lint' || entry.method === 'GET' && mode === 'hold') {
      const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
      if (mode === 'hold') return { status: 200, json: server.job(id, 'lint', 'running') };
      return { status: 200, json: server.lint(id) };
    }
    assert.equal(mode, 'pass', 'stopped batch must not POST a Check');
    const checks = f.seed.steps.flatMap(step => step.checks).map(check => ({ ...check, expected: check.value, actual: check.value, passed: true }));
    return { status: 200, json: server.check(entry.request.requestId, 'passed', checks) };
  });
  f.fake = fake;
  const env = { ...process.env, HOME: f.home, PDD_STATE_DIR: f.state, PDD_RUNTIME_URL: fake.origin };
  const first = portsFor(env);
  assert.equal(await runtime.runCheck({ words: f.selected, options: { '--json': true }, cwd: f.repo }, first.ports), 0, first.ports.stderr.text);
  assert.equal(fake.posts.filter(row => row.command === 'check').length, 4);
  const earlier = readdirSync(join(f.state, 'batches'))[0];
  mode = stop.startsWith('lint hold') ? 'hold' : 'interrupt';
  const later = portsFor(env, { onInterrupt: handler => { interrupt = handler; return () => { interrupt = null; }; } });
  later.clock.now = first.clock.now + 10000;
  if (mode === 'interrupt') {
    const output = later.ports.stderr;
    later.ports.stderr = { write(text) { output.write(text); if (text.includes('If pdd stops, read the results with:')) interrupt(); return true; } };
  }
  await runtime.runCheck({ words: f.selected, options: { '--json': true }, cwd: f.repo }, later.ports);
  assert.equal(fake.posts.filter(row => row.command === 'check').length, 4, 'later batch never POSTed any Check');
  const latest = readdirSync(join(f.state, 'batches')).find(name => name !== earlier);
  assert.ok(latest); assert.ok(latest > earlier);
  const batchPath = name => join(f.state, 'batches', name, 'batch.json');
  const older = JSON.parse(readFileSync(batchPath(earlier))), newer = JSON.parse(readFileSync(batchPath(latest)));
  assert.equal(newer.rows.length, 4); assert.ok(newer.rows.every(row => row.request_ids.length === 0));
  assert.equal(newer.source_sha256, older.source_sha256); assert.ok(newer.lint.request_ids.length > 0);
  if (intent === 'absent') for (const name of [earlier, latest]) { const batch = JSON.parse(readFileSync(batchPath(name))); delete batch.intent; writeFileSync(batchPath(name), JSON.stringify(batch)); }
  const guard = readGuard(t, f);
  try {
    const status = await productStatus({ cwd: f.repo }, productPorts(f)), next = await productNext({ cwd: f.repo }, productPorts(f));
    guard.check();
    productExpected(authentic.expected, status, next, { saved_check_state_changed: false, runtime_requests_during_read: 0, runtime_auth_during_read: 0, workflow_dispatches_during_read: 0 });
  } finally { guard.restore(); }
});

for (const fixture of vectors.integration_cases.filter(row => row !== authentic)) {
  const variants = fixture.independent_variants ?? fixture.sent_state_variants.map(state => ({ state, expected: fixture.expected }));
  for (const variant of variants) test(`unsent integration: ${fixture.case}/${variant.prior_batch ?? variant.state}`, async t => {
    const f = productFiles(t), story = 'user_stories/S01-saved.md', one = 'tests/S01-saved.json', two = 'tests/S01-second.json';
    writeFileSync(join(f.repo, two), readFileSync(join(f.repo, one))); git(f.repo, 'add', '-A');
    const source = captureSource(f.repo, { tests: [one, two].sort(), appMap: null });
    const fixtureRow = (attempt, test, at) => ({ story, test, attempt, ...(attempt === 'unsent' ? { state: 'not_run', ended_at: 9000 } : { sent_at: at }) });
    const batches = [];
    if (variant.prior_batch && variant.prior_batch !== 'none' || variant.state) batches.push({ created_at: '1970-01-01T00:00:01.000Z', rows: [fixtureRow('passed', one, 2000), fixtureRow('passed', two, 2000)] });
    batches.push({ created_at: '1970-01-01T00:00:03.000Z', rows: [fixtureRow(variant.state ?? 'passed', one, 4000), fixtureRow('unsent', two)] });
    const world = ownerWorld({ batches }, { intent: 'check' });
    for (const batch of world.records) {
      batch.root = f.repo; batch.source_sha256 = source.sha256;
      for (const row of batch.rows) {
        row.steps = copy(f.seed.steps); row.criteria_total = f.seed.criteria.length;
        row.criterion_texts = Object.fromEntries(f.seed.criteria.map(criterion => [criterion.id, criterion.text]));
        for (const id of row.request_ids) {
          const receipt = world.receipts[`${batch.batch}/${id}.json`], passed = row.state !== 'failed';
          receipt.result.report.criterion_results = f.seed.criteria.map(criterion => ({ criterion_id: criterion.id, status: passed ? 'passed' : 'failed' }));
          receipt.result.report.samples = [{ sample: 1, steps: f.seed.steps.map(step => ({ step_id: step.step_id,
            checks: step.checks.map(check => ({ ...copy(check), expected: check.value, actual: check.value, passed })) })) }];
        }
      }
      const folder = join(f.state, 'batches', batch.batch); mkdirSync(folder, { recursive: true }); writeFileSync(join(folder, 'batch.json'), JSON.stringify(batch));
      for (const [path, receipt] of Object.entries(world.receipts)) if (path.startsWith(`${batch.batch}/`)) writeFileSync(join(folder, path.split('/')[1]), JSON.stringify(receipt));
    }
    const guard = readGuard(t, f);
    try { const status = await productStatus({ cwd: f.repo }, productPorts(f)); guard.check(); productExpected(variant.expected, status); }
    finally { guard.restore(); }
  });
}
