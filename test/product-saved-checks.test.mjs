import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { chmodSync, existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join, dirname } from 'node:path';
import * as runtime from '../src/runtime-client.mjs';
import { productStatus, productNext } from '../src/product.mjs';
import { harbor, portsFor, fakeRuntime, filesUnder, sha } from './runtime-fake.mjs';

const scenario = JSON.parse(readFileSync(new URL('./runtime/product-saved-checks.json', import.meta.url)));
const owner = JSON.parse(readFileSync(new URL('./fixtures/product-saved-checks-owner.json', import.meta.url)));
const git = (cwd, ...args) => { const reply = spawnSync('git', args, { cwd, encoding: 'utf8' }); assert.equal(reply.status, 0, reply.stderr); return reply.stdout; };
const snapshot = dir => filesUnder(dir).filter(path => !path.endsWith('.lock')).map(path => { try { return [path, sha(readFileSync(path))]; } catch { return null; } }).filter(Boolean);
const issue = { number: 81, body: '<!-- pdd-product: run=server-1 -->', state: 'OPEN', author_association: 'MEMBER', user: { login: 'member' }, created_at: '2026-10-01T00:00:00Z' };
function productPorts(f, extra = {}) {
  let state = null;
  return {
    listRuns: async () => [{ workflow: 'feature', number: 81, issue: { number: 81 }, productMarker: '<!-- pdd-product: run=server-1 -->', root: f.repo, state: 'running', done: {}, runtimeHistory: [], stage: { id: 'prompt-story' } }],
    resolveRepository: async () => ({ repository: 'example/coffee', defaultBranch: 'alpha' }),
    issuePage: async () => ({ items: [issue], total_count: 1, incomplete_results: false }),
    issueByNumber: async () => issue,
    timelinePage: async () => [], planOnBase: async () => true,
    readProductState: async () => ({ json: state }), writeProductState: async input => { state = input.json; return {}; },
    lockProductState: async () => ({ handle: 'fixture-lock' }), unlockProductState: async () => ({}),
    now: async () => ({ milliseconds: 100000 }),
    startRun: async () => assert.fail('status must not start a workflow'),
    execFile: async () => assert.fail('unexpected external command'), ...extra,
  };
}
async function produced(t) {
  const f = harbor(t);
  for (const [path, file] of Object.entries(scenario.initial_world.files)) {
    const target = join(f.repo, path.slice('/project/'.length)); mkdirSync(dirname(target), { recursive: true }); writeFileSync(target, file.content);
  }
  const seed = JSON.parse(readFileSync(join(f.repo, 'tests/place-order.json')));
  const story = readFileSync(join(f.repo, seed.story_path), 'utf8');
  const selected = [];
  for (const id of ['S01', 'S02', 'S03', 'S04', 'S010']) {
    const value = structuredClone(seed); value.story_path = `user_stories/${id}-saved.md`;
    writeFileSync(join(f.repo, value.story_path), story);
    const path = `tests/${id}-saved.json`; writeFileSync(join(f.repo, path), JSON.stringify(value)); selected.push(path);
  }
  git(f.repo, 'add', '-A');
  const fake = await fakeRuntime(t, (entry, server) => {
    if (entry.command === 'lint') return { status: 200, json: server.lint(entry.request.requestId) };
    const id = entry.request?.requestId ?? entry.url.split('/').at(-1);
    const checks = seed.steps[0].checks.map(check => ({ ...check, expected: check.value, actual: check.value, passed: true }));
    return { status: 200, json: server.check(id, 'passed', checks) };
  });
  const env = { ...process.env, HOME: f.home, PDD_STATE_DIR: f.state, PDD_RUNTIME_URL: fake.origin };
  const { ports } = portsFor(env);
  assert.equal(await runtime.runCheck({ words: selected, options: { '--json': true }, cwd: f.repo }, ports), 0, ports.stderr.text + ports.stdout.text);
  assert.equal(fake.posts.filter(entry => entry.command === 'check').length, 5);
  const batchName = readdirSync(join(f.state, 'batches'))[0], folder = join(f.state, 'batches', batchName);
  const batch = JSON.parse(readFileSync(join(folder, 'batch.json')));
  assert.equal(batch.intent, 'check'); assert.equal(batch.rows.length, 5);
  return { ...f, env, fake, batch, folder, selected };
}

test('producer-default-reader-product: authentic saved checks count before workflow completion', async t => {
  const f = await produced(t), oldEnv = process.env.PDD_STATE_DIR;
  process.env.PDD_STATE_DIR = f.state; t.after(() => { if (oldEnv === undefined) delete process.env.PDD_STATE_DIR; else process.env.PDD_STATE_DIR = oldEnv; });
  const before = snapshot(f.state), sent = f.fake.posts.length, reads = f.fake.gets.length;
  const status = await productStatus({ cwd: f.repo }, productPorts(f));
  const expected = owner.integration_cases.find(value => value.case === 'producer-default-reader-product').expected;
  assert.deepEqual(status.parts.find(row => row.part === 'server'), { part: 'server', ...expected.server });
  assert.deepEqual(status.slices[0], { slice: '1', ...expected.slice });
  assert.equal(status.runs[0].state, expected.runState);
  assert.equal((await productNext({ cwd: f.repo }, productPorts(f))).ready.includes('journeys'), expected.journeyReady);
  assert.deepEqual(snapshot(f.state), before); assert.equal(f.fake.posts.length, sent); assert.equal(f.fake.gets.length, reads);
});

test('planned and unverified links retain cwd saved progress without foreign reads', async t => {
  const f = await produced(t);
  for (const unverified of [false, true]) {
    const roots = [];
    const ports = productPorts(f, {
      listRuns: async () => unverified ? [{ workflow: 'feature', number: 81, root: '/foreign', productMarker: '<!-- pdd-product: run=server-1 -->' }] : [],
      issuePage: async () => ({ items: [], total_count: 0, incomplete_results: false }),
      issueByNumber: async () => ({ status: 404 }),
      savedStoryEvidence: async input => { roots.push(input.root); return runtime.savedStoryEvidence(input, { env: f.env }); },
    });
    const status = await productStatus({ cwd: f.repo }, ports);
    const expected = owner.integration_cases.find(value => value.case === (unverified ? 'unverified-link-root' : 'planned-without-workflow')).expected;
    assert.equal(status.parts[1].pass, expected.serverPass);
    assert.equal(status.runs[0].state, expected.runState ?? expected.serverState);
    assert.ok(roots.every(root => root === f.repo));
    assert.equal((await productNext({ cwd: f.repo }, ports)).ready.includes('journeys'), expected.journeyReady);
  }
});

for (const fixture of owner.cases) test(`saved owner: ${fixture.case}`, async () => {
  const batch = structuredClone(owner.batch), receipts = structuredClone(owner.receipts), captures = [];
  if (fixture.intent) batch.intent = fixture.intent;
  if (fixture.replace_receipt) receipts[fixture.replace_receipt.id] = fixture.replace_receipt.value;
  const ports = {
    env: { PDD_STATE_DIR: '/state' }, realpath: path => path,
    readDir: path => { assert.equal(path, '/state/batches'); if (fixture.state_missing) throw Object.assign(Error('missing'), { code: 'ENOENT' }); if (fixture.read_error) throw Object.assign(Error('denied'), { code: fixture.read_error }); return [batch.batch]; },
    readFile: path => {
      if (path.endsWith('/batch.json')) return JSON.stringify(batch);
      const id = path.split('/').at(-1).replace(/\.json$/, '');
      if (receipts[id]) return JSON.stringify(receipts[id]);
      throw Object.assign(Error('missing'), { code: 'ENOENT' });
    },
    captureSource: (root, selection) => { captures.push({ root, ...selection }); return { sha256: fixture.captured_sha256 ?? owner.captured_sha256 }; },
    fetch: () => assert.fail('reader network'), gh: () => assert.fail('reader auth'), mkdir: () => assert.fail('reader mkdir'), writeFile: () => assert.fail('reader write'),
  };
  assert.equal(typeof runtime.savedStoryEvidence, 'function', 'approved local reader must be exported');
  const result = await runtime.savedStoryEvidence(fixture.input ?? owner.input, ports), expected = fixture.expected;
  if (expected.stories !== undefined) assert.equal(result.stories.length, expected.stories);
  if (expected.pass !== undefined) assert.equal(result.stories.filter(row => row.pass).length, expected.pass);
  if (expected.current !== undefined) assert.equal(result.stories.filter(row => row.current).length, expected.current);
  if (expected.warnings !== undefined) assert.equal(result.warnings.length, expected.warnings);
  if (expected.minimum_warnings !== undefined) assert.ok(result.warnings.length >= expected.minimum_warnings);
  if (fixture.case === 'whole-batch-current') assert.deepEqual(captures, [owner.expected_capture]);
});

for (const name of ['current-failure-across-sources', 'current-unknown-across-sources', 'current-before-stale']) test(name, async () => {
  const fixture = owner.integration_cases.find(value => value.case === name);
  const ports = productPorts({ repo: '/project' }, {
    readFile: async path => scenario.initial_world.files[path].content,
    storyEvidence: async () => fixture.workflowEvidence,
    savedStoryEvidence: async () => ({ stories: fixture.savedEvidence, warnings: [] }),
  });
  const status = await productStatus({ cwd: '/project' }, ports);
  assert.equal(status.parts[1].pass, fixture.expected.pass); assert.equal(status.parts[1].stale, fixture.expected.stale);
});

test('saved owner: latest attempts, whole Story cases and authored criteria completeness', async t => {
  const f = await produced(t), row = f.batch.rows[0], id = row.request_ids.at(-1);
  const original = JSON.parse(readFileSync(join(f.folder, `${id}.json`)));
  const read = () => runtime.savedStoryEvidence({ root: f.repo }, { env: f.env });
  const storyPath = JSON.parse(readFileSync(join(f.repo, row.test))).story_path;
  const failedId = '77777777-7777-4777-8777-777777777777';
  row.request_ids.push(failedId);
  writeFileSync(join(f.folder, `${failedId}.json`), JSON.stringify({ ...original, id: failedId, requestId: failedId, state: 'unknown' }));
  writeFileSync(join(f.folder, 'batch.json'), JSON.stringify(f.batch));
  assert.equal((await read()).stories.find(value => value.story === storyPath).pass, false);
  row.request_ids.pop();
  const duplicate = { ...row, test: f.batch.rows[1].test, request_ids: [failedId] };
  f.batch.rows.push(duplicate); writeFileSync(join(f.folder, 'batch.json'), JSON.stringify(f.batch));
  assert.equal((await read()).stories.find(value => value.story === storyPath).pass, false);
  f.batch.rows.pop();
  original.result.report.criterion_results.pop();
  writeFileSync(join(f.folder, `${id}.json`), JSON.stringify(original)); writeFileSync(join(f.folder, 'batch.json'), JSON.stringify(f.batch));
  assert.equal((await read()).stories.find(value => value.story === storyPath).pass, false);
});

test('merged base compares cwd and own root; another run cannot restore merged Story', async () => {
  const fixture = owner.integration_cases.find(value => value.case === 'mixed-merged-and-unmerged-roots'), reads = [], comparisons = [];
  const runs = [
    { workflow: 'feature', number: 81, root: '/server', baseBranch: 'alpha', productMarker: '<!-- pdd-product: run=server-1 -->', pr: [{ number: 91, stage: 'code', branch: 'server-code' }] },
    { workflow: 'feature', number: 82, root: '/phone', productMarker: '<!-- pdd-product: run=phone-1 -->' },
  ];
  const issues = [issue, { ...issue, number: 82, body: '<!-- pdd-product: run=phone-1 -->' }];
  const ports = productPorts({ repo: '/project' }, {
    readFile: async path => scenario.initial_world.files[path].content, listRuns: async () => runs,
    issuePage: async () => ({ items: issues, total_count: 2, incomplete_results: false }), issueByNumber: async ({ number }) => issues.find(row => row.number === number),
    timelinePage: async ({ issue }) => issue === 81 ? [{ event: 'cross-referenced', source: { issue: { pull_request: { html_url: 'https://github.com/example/coffee/pull/91' } } } }] : [],
    pullRequest: async () => ({ number: 91, url: 'https://github.com/example/coffee/pull/91', body: '<!-- pdd-product: run=server-1 -->', state: 'MERGED', headRefName: 'server-code', isCrossRepository: false }),
    openBaseSource: async () => ({ root: '/base', handle: null }),
    storyEvidence: async (run, options) => { comparisons.push([run.root, options]); return []; },
    savedStoryEvidence: async input => { reads.push(input); return { stories: fixture.cwdEvidence.map(row => ({ ...row, current: input.comparisonRoot !== '/base', at: 1 })), warnings: [] }; },
  });
  const status = await productStatus({ cwd: '/project' }, ports);
  assert.equal(status.parts[1].pass, fixture.expected.serverPass); assert.equal(status.parts[1].stale, fixture.expected.serverStale);
  assert.ok(reads.some(input => input.root === '/server' && input.comparisonRoot === '/base'));
  assert.ok(reads.some(input => input.root === '/project' && input.comparisonRoot === '/base'));
  assert.ok(comparisons.some(([root, options]) => root === '/server' && options.comparisonRoot === '/base'));
});


test('actual CLI consumes producer state with a deterministic metadata-only gh', async t => {
  const f = await produced(t);
  git(f.repo, '-c', 'user.email=t@example.com', '-c', 'user.name=t', 'commit', '-qm', 'synthetic product');
  git(f.repo, 'remote', 'add', 'origin', 'https://github.com/example/coffee.git');
  git(f.repo, 'update-ref', 'refs/remotes/origin/alpha', 'HEAD');
  const runDir = join(f.repo, '.git/pdd/runs/81'); mkdirSync(runDir, { recursive: true });
  writeFileSync(join(runDir, 'status.json'), JSON.stringify({ v: 1, number: 81, workflow: 'feature', root: f.repo, productMarker: issue.body, state: 'running', done: {}, runtimeHistory: [], stage: { id: 'prompt-story' } }));
  const bin = join(f.sandbox, 'bin'); mkdirSync(bin);
  const log = join(f.sandbox, 'gh-calls.jsonl'), executable = join(bin, 'gh');
  writeFileSync(executable, `#!${process.execPath}
import {appendFileSync} from 'node:fs';
const args=process.argv.slice(2); appendFileSync(${JSON.stringify(log)}, JSON.stringify(args)+'\\n');
const issue=${JSON.stringify(issue)};
if(args[0]==='repo') console.log(JSON.stringify({nameWithOwner:'example/coffee',defaultBranchRef:{name:'alpha'},url:'https://github.com/example/coffee'}));
else if(args[0]==='api' && args[1].startsWith('search/issues?')) console.log(JSON.stringify({items:[issue],total_count:1,incomplete_results:false}));
else if(args[0]==='api' && args[1].includes('/timeline?')) console.log('[]');
else if(args[0]==='api' && args[1]==='repos/example/coffee/issues/81') console.log('HTTP/2 200 OK\\n\\n'+JSON.stringify(issue));
else {console.error('Forbidden fixture gh '+JSON.stringify(args));process.exit(91);}
`); chmodSync(executable, 0o755);
  const before = snapshot(f.state);
  const result = spawnSync(process.execPath, [new URL('../bin/pdd.mjs', import.meta.url).pathname, 'product', 'status', '--json'], {
    cwd: f.repo, encoding: 'utf8', env: { ...f.env, PATH: `${bin}:${process.env.PATH}`, PDD_RUNTIME_URL: 'invalid-reader-must-not-resolve-runtime' }, timeout: 30000,
  });
  assert.equal(result.status, 0, result.stderr + result.stdout);
  const status = JSON.parse(result.stdout), expected = owner.integration_cases.find(value => value.case === 'producer-default-reader-product').expected;
  assert.deepEqual(status.parts[1], { part: 'server', ...expected.server });
  assert.deepEqual(status.slices[0], { slice: '1', ...expected.slice });
  assert.equal(status.runs[0].state, expected.runState); assert.deepEqual(snapshot(f.state), before);
  const calls = readFileSync(log, 'utf8').trim().split('\n').map(value => JSON.parse(value));
  assert.ok(calls.every(args => args[0] !== 'auth' && !(args[0] === 'api' && args[1] === 'user')));
});

for (const name of ['whole-story-cases', 'partial-criteria', 'merged-base']) test(`canonical owner integration: ${name}`, async () => {
  const fixture = owner.integration_cases.find(value => value.case === name);
  const batch = structuredClone(owner.batch), receipts = structuredClone(owner.receipts), captures = [];
  const first = batch.rows[0];
  if (name === 'whole-story-cases') {
    batch.rows[1].story = first.story;
    receipts[batch.rows[1].request_ids[0]].state = fixture.receiptStates[1];
  }
  if (name === 'partial-criteria') {
    Object.assign(first, fixture.row);
    receipts[first.request_ids[0]].result = fixture.receiptResult;
  }
  const result = await runtime.savedStoryEvidence({ root: '/project', ...(name === 'merged-base' ? { comparisonRoot: '/base' } : {}) }, {
    env: { PDD_STATE_DIR: '/state' }, realpath: value => value, readDir: () => [batch.batch],
    readFile: path => {
      assert.ok(path.startsWith(`/state/batches/${batch.batch}/`));
      if (path.endsWith('/batch.json')) return JSON.stringify(batch);
      return JSON.stringify(receipts[path.split('/').at(-1).replace(/\.json$/, '')]);
    },
    captureSource: (root, options) => { captures.push({ root, ...options }); return { sha256: owner.captured_sha256 }; },
  });
  if (name === 'merged-base') {
    assert.deepEqual(captures, [{ ...owner.expected_capture, root: '/base' }]); assert.equal(result.stories.length, 2);
  } else assert.equal(result.stories.find(row => row.story === first.story).pass ? 1 : 0, fixture.expected.pass);
});


test('native default reader leaves a nonexistent state directory absent', async t => {
  const f = harbor(t), before = snapshot(f.sandbox);
  assert.equal(existsSync(f.state), false);
  const result = await runtime.savedStoryEvidence({ root: f.repo }, { env: { HOME: f.home, PDD_STATE_DIR: f.state, PDD_RUNTIME_URL: 'invalid-reader-must-not-resolve-runtime' } });
  assert.deepEqual(result, { stories: [], warnings: [] }); assert.equal(existsSync(f.state), false);
  assert.deepEqual(snapshot(f.sandbox), before);
});

test('native source recapture includes every selected test when one Story changes', async t => {
  const f = await produced(t);
  const read = () => runtime.savedStoryEvidence({ root: f.repo }, { env: f.env });
  const original = await read();
  assert.deepEqual(original.stories.map(row => row.story).sort(), f.selected.map(path => JSON.parse(readFileSync(join(f.repo, path))).story_path).sort());
  assert.ok(original.stories.every(row => row.pass && row.current));
  const path = join(f.repo, JSON.parse(readFileSync(join(f.repo, f.batch.rows[0].test))).story_path); writeFileSync(path, readFileSync(path, 'utf8') + '\nChanged synthetic criterion input.\n');
  const result = await read(); assert.ok(result.stories.every(row => row.pass && !row.current));
});

for (const ambiguity of [false, true]) test(`legacy Story identity refuses ${ambiguity ? 'ambiguous' : 'missing'} captured paths`, async () => {
  const batch = structuredClone(owner.batch);
  batch.rows[0].story = 'S01-one';
  batch.files = ambiguity ? ['user_stories/server/S01-one.md', 'other/S01-one.md'] : [];
  const result = await runtime.savedStoryEvidence(owner.input, {
    env: { PDD_STATE_DIR: '/state' }, realpath: path => path, readDir: () => [batch.batch],
    readFile: path => path.endsWith('/batch.json') ? JSON.stringify(batch) : JSON.stringify(owner.receipts[path.split('/').at(-1).replace(/\.json$/, '')]),
    captureSource: () => ({ sha256: owner.captured_sha256 }),
  });
  assert.equal(result.stories.filter(row => row.pass).length, 0);
  assert.ok(result.warnings.length > 0);
});
