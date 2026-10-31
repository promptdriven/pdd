import test from 'node:test';
import assert from 'node:assert/strict';
import childProcess, { spawnSync } from 'node:child_process';
import { syncBuiltinESMExports } from 'node:module';
import { chmodSync, cpSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import * as runtime from '../src/runtime-client.mjs';
import { productStatus, productNext, productStart } from '../src/product.mjs';
import { harbor, portsFor, fakeRuntime, filesUnder, sha } from './runtime-fake.mjs';

const vectors = JSON.parse(readFileSync(new URL('./fixtures/product-saved-checks-followup.json', import.meta.url)));
const productScenario = JSON.parse(readFileSync(new URL('./runtime/product-saved-checks.json', import.meta.url)));
const copy = value => structuredClone(value);
const own = (value, key) => Object.prototype.hasOwnProperty.call(value, key);
const forbidden = name => () => assert.fail(`Forbidden during evidence read: ${name}`);
const legacyHints = warnings => warnings.filter(warning => vectors.legacy_hint_fragments.contains.every(fragment => warning.toLowerCase().includes(fragment.toLowerCase()))).length;

function mutate(row, mutation = {}) {
  for (const key of mutation.remove ?? mutation.remove_row_keys ?? []) delete row[key];
  Object.assign(row, mutation.set ?? {});
  for (const step of row.steps ?? []) {
    for (const key of mutation.remove_step_keys ?? []) delete step[key];
    Object.assign(step, mutation.set_step ?? {});
    if (mutation.set_first_check) Object.assign(step.checks[0], mutation.set_first_check);
  }
  if (mutation.duplicate_step) row.steps.push(copy(row.steps[0]));
}

function ownerWorld(fixture, variant = {}, mutation = {}) {
  const setup = fixture.setup ?? {}, records = [], receipts = {}, captures = [];
  const batchSpecs = setup.batches ?? Array.from({ length: setup.batch_count ?? 1 }, () => ({}));
  for (const [batchIndex, spec] of batchSpecs.entries()) {
    const batch = copy(vectors.canonical_full_record);
    batch.batch = `20261030-120000-${batchIndex.toString(36).padStart(4, '0')}`;
    batch.root = spec.root ?? batch.root;
    batch.source_sha256 = spec.saved_sha256 ?? setup.saved_sha256 ?? batch.source_sha256;
    if (own(spec, 'intent')) batch.intent = spec.intent;
    if (spec.remove_intent) delete batch.intent;
    for (const key of fixture.remove_batch_keys ?? []) delete batch[key];
    const tests = spec.tests ?? setup.test_paths ?? Array.from({ length: setup.rows_per_batch ?? 1 }, (_, i) => `test/runtime/${i === 0 ? 'one' : 'two'}.json`);
    batch.rows = tests.map((path, rowIndex) => {
      const row = copy(vectors.canonical_full_record.rows[0]);
      row.test = path;
      row.story = `user_stories/server/S${batchIndex}-${rowIndex}-synthetic.md`;
      const id = `11111111-1111-4111-8111-${(batchIndex * 10 + rowIndex).toString().padStart(12, '0')}`;
      row.request_ids = [id];
      const receipt = copy(Object.values(vectors.receipts)[0]);
      receipt.requestId = receipt.id = id;
      const patch = variant.receipt_patch ?? fixture.receipt_patch ?? {};
      for (const key of ['state', 'command', 'id']) if (own(patch, key)) receipt[key] = patch[key];
      if (own(patch, 'criterion_results')) receipt.result.report.criterion_results = copy(patch.criterion_results);
      if (patch.all_criterion_status) for (const criterion of receipt.result.report.criterion_results) criterion.status = patch.all_criterion_status;
      if (own(patch, 'all_checks_passed')) for (const sample of receipt.result.report.samples) for (const step of sample.steps) for (const check of step.checks) check.passed = patch.all_checks_passed;
      receipts[`${batch.batch}/${id}.json`] = receipt;
      mutate(row, { remove: fixture.remove_row_keys ?? [] });
      mutate(row, spec);
      mutate(row, mutation);
      if (rowIndex === 1) mutate(row, { remove: setup.remove_second_row_keys ?? [] });
      return row;
    });
    if (setup.alternate_reverse_rows && batchIndex % 2) batch.rows.reverse();
    if (setup.duplicate_test_row_on_last_batch && batchIndex === batchSpecs.length - 1) {
      const row = copy(batch.rows[0]); row.story += '.duplicate.md'; batch.rows.push(row);
    }
    records.push(batch);
  }
  const before = JSON.stringify({ records, receipts });
  let captureSha = variant.capture_sha256 ?? setup.capture_sha256 ?? vectors.default_capture_sha256;
  let captureError = setup.capture_error, releaseCapture;
  const pending = setup.capture_pending_until_both_reads_started ? new Promise(resolve => { releaseCapture = resolve; }) : null;
  const ports = {
    env: { PDD_STATE_DIR: '/state' }, realpath: path => setup.realpath_aliases?.[path] ?? path,
    readDir: path => { assert.equal(path, '/state/batches'); return records.map(record => record.batch); },
    readFile: path => {
      const relative = path.slice('/state/batches/'.length), [batch] = relative.split('/');
      assert.ok(path.startsWith('/state/batches/'));
      const value = relative.endsWith('/batch.json') ? records.find(record => record.batch === batch) : receipts[relative];
      if (!value) throw Object.assign(Error('missing'), { code: 'ENOENT' });
      return JSON.stringify(value);
    },
    captureSource: async (root, selection) => {
      captures.push({ root, ...copy(selection) });
      if (pending) await pending;
      if (captureError) throw Object.assign(Error(captureError), { code: captureError });
      return { sha256: captureSha };
    },
    fetch: forbidden('fetch'), gh: forbidden('gh'), writeFile: forbidden('writeFile'), mkdir: forbidden('mkdir'), startRun: forbidden('workflow.start'),
  };
  return { records, captures, ports, releaseCapture,
    setCapture(value, error) { captureSha = value; captureError = error; },
    unchanged() { assert.equal(JSON.stringify({ records, receipts }), before); },
  };
}

function checkExpected(expected, replies, world, beforeReplies = replies) {
  const rows = replies.flatMap(reply => reply.stories), warnings = [...new Set(replies.flatMap(reply => reply.warnings))];
  const values = {
    stories: () => rows.length, pass: () => rows.filter(row => row.pass).length, current: () => rows.filter(row => row.current).length,
    warnings: () => warnings.length, legacy_hints: () => legacyHints(warnings), capture_calls: () => world.captures.length,
    capture_calls_total: () => world.captures.length,
    all_rows_current: () => rows.length > 0 && rows.every(row => row.current),
    current_by_batch: () => replies[0].stories.map(row => row.current), pass_by_batch: () => replies[0].stories.map(row => row.pass),
    current_by_read: () => replies.map(reply => reply.stories.length > 0 && reply.stories.every(row => row.current)),
    all_rows_current_before_new_reader: () => beforeReplies.flatMap(reply => reply.stories).every(row => row.current),
    all_rows_current_after_new_reader: () => replies.at(-1).stories.length > 0 && replies.at(-1).stories.every(row => row.current),
    finite_warnings: () => replies.every(reply => Array.isArray(reply.warnings) && reply.warnings.every(warning => typeof warning === 'string' && warning.length > 0 && warning.length < 2000) && new Set(reply.warnings).size === reply.warnings.length),
  };
  for (const [key, value] of Object.entries(expected)) {
    if (key === 'capture_tests') {
      for (const capture of world.captures) assert.deepEqual({ tests: capture.tests, appMap: capture.appMap }, { tests: value, appMap: null }, key);
    } else if (key === 'capture_calls_before_new_reader') {
      // Captured at the point just before the fresh reader is created.
      assert.equal(world.capturesBeforeNewReader, value, key);
    } else {
      assert.ok(values[key], `Unmapped approved expectation: ${key}`);
      assert.deepEqual(values[key](), value, key);
    }
  }
  world.unchanged();
}

for (const fixture of vectors.cases) test(`followup vector: ${fixture.case}`, async () => {
  const variants = fixture.independent_variants ?? [{}], mutations = fixture.independent_row_mutations ?? [{}];
  for (const variant of variants) for (const mutation of mutations) {
    const world = ownerWorld(fixture, variant, mutation);
    // Let the old public boundary run for semantic mutation controls, rather than crash on an absent new export.
    const factory = () => runtime.createSavedStoryEvidenceReader?.(world.ports) ?? (input => runtime.savedStoryEvidence(input, world.ports));
    let reader = factory();
    const read = async input => {
      if (own(input, 'capture_sha256')) world.setCapture(input.capture_sha256);
      const { capture_sha256, ...args } = input;
      return fixture.boundary === 'savedStoryEvidence' ? runtime.savedStoryEvidence(args, world.ports) : reader(args);
    };
    let replies;
    if (fixture.concurrent_reads) {
      const first = read(fixture.concurrent_reads[0]), second = read(fixture.concurrent_reads[1]);
      // Release after both reads have entered, even if a broken implementation captured twice.
      await new Promise(resolve => setImmediate(resolve)); world.releaseCapture();
      replies = await Promise.all([first, second]);
    } else {
      replies = [];
      const reads = fixture.reads ?? [{ ...vectors.default_input, ...(own(variant, 'comparisonRoot') ? { comparisonRoot: variant.comparisonRoot } : {}) }];
      for (const input of reads) { if (fixture.setup?.new_reader_per_read) reader = factory(); replies.push(await read(input)); }
    }
    const beforeReplies = [...replies];
    if (fixture.next_reader) {
      world.capturesBeforeNewReader = world.captures.length;
      world.setCapture(fixture.next_reader.capture_sha256); reader = factory();
      replies.push(await read(fixture.next_reader.read));
    }
    checkExpected(variant.expected ?? fixture.expected_each ?? fixture.expected, replies, world, beforeReplies);
  }
});

const git = (cwd, ...args) => { const result = spawnSync('git', args, { cwd, encoding: 'utf8' }); assert.equal(result.status, 0, result.stderr); return result.stdout; };
const snapshot = directory => filesUnder(directory).filter(path => !path.endsWith('.lock')).flatMap(path => { try { return [[path, sha(readFileSync(path))]]; } catch { return []; } }).sort(([a], [b]) => a.localeCompare(b));
const issue = { number: 81, body: '<!-- pdd-product: run=server-1 -->', state: 'OPEN', author_association: 'MEMBER', user: { login: 'member' }, created_at: '2026-10-01T00:00:00Z' };
function productPorts(f, extra = {}) {
  let cache = null;
  return {
    listRuns: async () => [{ workflow: 'feature', number: 81, issue: { number: 81 }, productMarker: issue.body, root: f.repo, state: 'running', done: {}, runtimeHistory: [], stage: { id: 'prompt-story' } }],
    resolveRepository: async () => ({ repository: 'example/coffee', defaultBranch: 'alpha' }),
    issuePage: async () => ({ items: [issue], total_count: 1, incomplete_results: false }), issueByNumber: async () => issue,
    timelinePage: async () => [], planOnBase: async () => true, storyEvidence: async () => [],
    readProductState: async () => ({ json: cache }), writeProductState: async input => { cache = input.json; return {}; },
    lockProductState: async () => ({ handle: 'synthetic-lock' }), unlockProductState: async () => ({}),
    now: async () => ({ milliseconds: 100000 }), startRun: forbidden('workflow.start'), execFile: forbidden('external metadata command'), ...extra,
  };
}

async function produced(t) {
  const f = harbor(t);
  for (const [path, file] of Object.entries(productScenario.initial_world.files)) {
    const target = join(f.repo, path.slice('/project/'.length)); mkdirSync(dirname(target), { recursive: true }); writeFileSync(target, file.content);
  }
  const seed = JSON.parse(readFileSync(join(f.repo, 'tests/place-order.json'))), story = readFileSync(join(f.repo, seed.story_path), 'utf8'), selected = [];
  for (const id of ['S01', 'S02', 'S03', 'S04', 'S010']) {
    const scenario = copy(seed); scenario.story_path = `user_stories/${id}-saved.md`;
    writeFileSync(join(f.repo, scenario.story_path), story);
    const path = `tests/${id}-saved.json`; writeFileSync(join(f.repo, path), JSON.stringify(scenario)); selected.push(path);
  }
  git(f.repo, 'add', '-A');
  const fake = await fakeRuntime(t, (entry, server) => {
    if (entry.command === 'lint') return { status: 200, json: server.lint(entry.request.requestId) };
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    const checks = seed.steps.flatMap(step => step.checks).map(check => ({ ...check, expected: check.value, actual: check.value, passed: true }));
    return { status: 200, json: server.check(id, 'passed', checks) };
  });
  const env = { ...process.env, HOME: f.home, PDD_STATE_DIR: f.state, PDD_RUNTIME_URL: fake.origin }, { ports } = portsFor(env);
  assert.equal(await runtime.runCheck({ words: selected, options: { '--json': true }, cwd: f.repo }, ports), 0, ports.stderr.text + ports.stdout.text);
  const folder = join(f.state, 'batches', readdirSync(join(f.state, 'batches'))[0]);
  const batch = JSON.parse(readFileSync(join(folder, 'batch.json')));
  assert.equal(batch.intent, 'check'); assert.equal(batch.rows.length, selected.length);
  delete batch.intent; writeFileSync(join(folder, 'batch.json'), JSON.stringify(batch));
  const previous = process.env.PDD_STATE_DIR; process.env.PDD_STATE_DIR = f.state;
  t.after(() => { if (previous === undefined) delete process.env.PDD_STATE_DIR; else process.env.PDD_STATE_DIR = previous; });
  return { ...f, env, fake, batch, folder, selected };
}

function readGuard(f) {
  const state = snapshot(f.state), requests = JSON.stringify([f.fake.posts, f.fake.gets, f.fake.deletes]);
  return () => { assert.deepEqual(snapshot(f.state), state); assert.equal(JSON.stringify([f.fake.posts, f.fake.gets, f.fake.deletes]), requests); };
}

function checkProductExpected(expected, status, next) {
  const values = {
    server: () => { const { part, ...counts } = status.parts.find(row => row.part === 'server'); return counts; },
    slice: () => { const { slice, ...counts } = status.slices[0]; return counts; },
    runState: () => status.runs[0].state, journeyReady: () => next.ready.includes('journeys'),
    serverPass: () => status.parts.find(row => row.part === 'server').pass, slicePass: () => status.slices[0].pass,
    legacy_hints: () => legacyHints(status.warnings ?? []),
  };
  for (const [key, value] of Object.entries(expected)) { assert.ok(values[key], `Unmapped integration expectation ${key}`); assert.deepEqual(values[key](), value, key); }
}

for (const fixture of vectors.integration_cases.slice(0, 2)) test(`followup integration: ${fixture.case}`, async t => {
  const f = await produced(t);
  for (const row of f.batch.rows) for (const key of fixture.also_remove_every_row_keys ?? []) delete row[key];
  writeFileSync(join(f.folder, 'batch.json'), JSON.stringify(f.batch));
  const unchanged = readGuard(f), ports = productPorts(f);
  const status = await productStatus({ cwd: f.repo }, ports);
  const next = fixture.operations.includes('productNext') ? await productNext({ cwd: f.repo }, ports) : null;
  checkProductExpected(fixture.expected, status, next); unchanged();
  if (fixture.also_remove_every_row_keys) await cliStatus(t, f, fixture.expected);
});

test('followup integration: default-product-reader-command-scope', async t => {
  const fixture = vectors.integration_cases.find(row => row.case === 'default-product-reader-command-scope');
  const f = await produced(t), base = join(f.sandbox, 'base'), runRoot = join(f.sandbox, 'run');
  cpSync(f.repo, base, { recursive: true }); cpSync(f.repo, runRoot, { recursive: true });
  const second = copy(f.batch); second.batch = '20261030-120000-zzzz'; second.root = runRoot;
  const secondFolder = join(f.state, 'batches', second.batch); mkdirSync(secondFolder);
  for (const row of second.rows) for (const id of row.request_ids) cpSync(join(f.folder, `${id}.json`), join(secondFolder, `${id}.json`));
  writeFileSync(join(secondFolder, 'batch.json'), JSON.stringify(second));
  const local = { workflow: 'feature', number: 81, issue: { number: 81 }, root: runRoot, baseBranch: 'alpha', productMarker: issue.body, pr: [{ number: 91, stage: 'code', branch: 'server-code' }] };
  const ports = productPorts(f, {
    listRuns: async () => [local],
    pullRequest: async () => ({ number: 91, url: 'https://github.com/example/coffee/pull/91', body: issue.body, state: 'MERGED', headRefName: 'server-code', isCrossRepository: false }),
    openBaseSource: async () => ({ root: base, handle: null }),
  });
  const unchanged = readGuard(f), nativeSpawn = childProcess.spawnSync;
  let listings = 0;
  // A stable native capture observes the Git file list before and after reading its files.
  t.mock.method(childProcess, 'spawnSync', (file, args, options) => {
    if (file === 'git' && args[0] === 'ls-files' && options.cwd === base) listings++;
    return nativeSpawn(file, args, options);
  });
  syncBuiltinESMExports(); t.after(() => { t.mock.restoreAll(); syncBuiltinESMExports(); });
  for (const operation of fixture.independent_operations) {
    listings = 0;
    const invoke = () => ({ productStatus, productNext, productStart })[operation]({ cwd: f.repo, run: 'server-1', noRun: true }, ports);
    const first = await invoke(), firstListings = listings;
    if (operation === 'productStatus') assert.equal(first.parts.find(row => row.part === 'server').pass, 4);
    if (operation === 'productStart') assert.equal(first.exitCode, 0, first.message);
    await invoke();
    const actual = {
      captures_first_command: firstListings / 2, captures_second_command: (listings - firstListings) / 2,
      second_command_reuses_first_capture: listings === firstListings, captures_total: listings / 2,
      saved_check_state_changed: false, runtime_requests: 0, workflow_dispatches: 0,
    };
    unchanged(); assert.deepEqual(actual, fixture.expected, operation);
  }
});

test('followup integration: default-product-status-observes-next-file-edit', async t => {
  const fixture = vectors.integration_cases.find(row => row.case === 'default-product-status-observes-next-file-edit'), f = await produced(t), unchanged = readGuard(f), ports = productPorts(f);
  const first = await productStatus({ cwd: f.repo }, ports);
  const story = join(f.repo, JSON.parse(readFileSync(join(f.repo, f.batch.rows[0].test))).story_path); writeFileSync(story, readFileSync(story, 'utf8') + '\nChanged synthetic source.\n');
  const second = await productStatus({ cwd: f.repo }, ports);
  const counts = status => { const { pass, stale, notRun } = status.parts.find(row => row.part === 'server'); return { pass, stale, notRun }; };
  unchanged();
  assert.deepEqual({ first_server: counts(first), second_server: counts(second), saved_check_state_changed: false, runtime_requests: 0, workflow_dispatches: 0 }, fixture.expected);
});

async function cliStatus(t, f, expected) {
  git(f.repo, '-c', 'user.email=t@example.com', '-c', 'user.name=t', 'commit', '-qm', 'synthetic product');
  git(f.repo, 'remote', 'add', 'origin', 'https://github.com/example/coffee.git'); git(f.repo, 'update-ref', 'refs/remotes/origin/alpha', 'HEAD');
  const runDir = join(f.repo, '.git/pdd/runs/81'); mkdirSync(runDir, { recursive: true });
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({ v: 1, number: 81, workflow: 'feature', root: f.repo, productMarker: issue.body, state: 'running', done: {}, runtimeHistory: [], stage: { id: 'prompt-story' } }));
  const bin = join(f.sandbox, 'bin'); mkdirSync(bin);
  const log = join(f.sandbox, 'gh.jsonl'), executable = join(bin, 'gh');
  writeFileSync(executable, `#!${process.execPath}
import {appendFileSync} from 'node:fs';
const args=process.argv.slice(2); appendFileSync(${JSON.stringify(log)}, JSON.stringify(args)+'\\n');
const issue=${JSON.stringify(issue)};
if(args[0]==='repo') console.log(JSON.stringify({nameWithOwner:'example/coffee',defaultBranchRef:{name:'alpha'},url:'https://github.com/example/coffee'}));
else if(args[0]==='api' && args[1].startsWith('search/issues?')) console.log(JSON.stringify({items:[issue],total_count:1,incomplete_results:false}));
else if(args[0]==='api' && args[1].includes('/timeline?')) console.log('[]');
else if(args[0]==='api' && args[1]==='repos/example/coffee/issues/81') console.log('HTTP/2 200 OK\\n\\n'+JSON.stringify(issue));
else {console.error('Forbidden gh '+JSON.stringify(args));process.exit(91);}
`); chmodSync(executable, 0o755);
  const unchanged = readGuard(f);
  const result = spawnSync(process.execPath, [new URL('../bin/pdd.mjs', import.meta.url).pathname, 'product', 'status', '--json'], { cwd: f.repo, encoding: 'utf8', env: { ...f.env, PATH: `${bin}:${process.env.PATH}`, PDD_RUNTIME_URL: 'invalid-reader-must-not-resolve-runtime' }, timeout: 30000 });
  assert.equal(result.status, 0, result.stderr + result.stdout); checkProductExpected(expected, JSON.parse(result.stdout)); unchanged();
  const calls = readFileSync(log, 'utf8').trim().split('\n').map(line => JSON.parse(line));
  assert.ok(calls.every(args => args[0] !== 'auth' && !(args[0] === 'api' && args[1] === 'user')));
}
