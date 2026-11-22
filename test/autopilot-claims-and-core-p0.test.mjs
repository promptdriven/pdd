import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdirSync, readFileSync, writeFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import {
  createDependencyReadPorts,
  refreshClaimHeartbeat,
  takeoverLimited,
  winningClaim,
  withoutClaimHeartbeat,
} from '../src/autopilot/claims.mjs';
import { pathRules } from '../src/autopilot-core.mjs';
import { coreWorld } from './helpers/core-world.mjs';

const REPO_ROOT = join(dirname(fileURLToPath(import.meta.url)), '..');

function writeIn(cwd, rel, text) {
  const abs = join(cwd, rel);
  mkdirSync(dirname(abs), { recursive: true });
  writeFileSync(abs, text);
}

function traceResolvedImports(entryRelPath) {
  const entryUrl = pathToFileURL(join(REPO_ROOT, entryRelPath)).href;
  const script = `
    import { registerHooks } from 'node:module';
    const seen = [];
    registerHooks({
      resolve(specifier, context, nextResolve) {
        const res = nextResolve(specifier, context);
        seen.push(res.url);
        return res;
      },
    });
    await import(${JSON.stringify(entryUrl)});
    process.stdout.write(JSON.stringify(seen));
  `;
  const run = spawnSync(process.execPath, ['--input-type=module', '-e', script], { cwd: REPO_ROOT, encoding: 'utf8', timeout: 15000 });
  assert.equal(run.status, 0, `import trace for ${entryRelPath} failed: ${run.stderr}`);
  return JSON.parse(run.stdout);
}

test('P0-10: claims.mjs module graph has zero workflow/Herdr imports and autopilot-core resolves ./autopilot/claims.mjs', () => {
  const claimsGraph = traceResolvedImports('src/autopilot/claims.mjs');
  const forbidden = /\/(?:workflow-|issue-dependencies-|issue-sort-|issue-mixed|autopilot-parking|herdr)/i;
  const badInClaims = claimsGraph.filter(url => forbidden.test(url));
  assert.deepEqual(badInClaims, [], 'claims.mjs module graph must not resolve workflow, Herdr, or dependency-graph modules');

  const coreGraph = traceResolvedImports('src/autopilot-core.mjs');
  assert.ok(coreGraph.some(url => url.endsWith('/src/autopilot/claims.mjs')), 'autopilot-core resolves src/autopilot/claims.mjs');
  assert.equal(coreGraph.some(url => url.endsWith('/src/issue-dependencies-github.mjs')), false, 'autopilot-core must not resolve src/issue-dependencies-github.mjs');
});

test('P0-10: takeoverLimited, withoutClaimHeartbeat, refreshClaimHeartbeat, and createDependencyReadPorts work cleanly', async () => {
  const self = { coordinatorId: 'coord-a', machine: 'mac-1' };
  assert.equal(takeoverLimited({ expired: true, takeovers: 2, coordinatorId: 'coord-b', machine: 'mac-2' }, self), false);
  assert.equal(takeoverLimited({ expired: true, takeovers: 3, coordinatorId: 'coord-b', machine: 'mac-2' }, self), true);
  assert.equal(takeoverLimited({ expired: true, takeovers: 3, coordinatorId: 'coord-a', machine: 'mac-1' }, self), false, 'self-retake is not takeover-limited');

  const rawBody = 'Autopilot core claim.\n\n```json\n{"repository":"acme/app","coordinatorId":"coord-a","machine":"mac-1","labelEventId":"901","lastSeen":"2026-11-20T00:00:00.000Z","longRunningAlertedAt":"2026-11-20T01:00:00.000Z"}\n```';
  const stripped = withoutClaimHeartbeat(rawBody);
  assert.doesNotMatch(stripped, /lastSeen/);
  assert.doesNotMatch(stripped, /longRunningAlertedAt/);
  assert.match(stripped, /"coordinatorId":"coord-a"/);

  let savedBody = rawBody;
  const mockExec = async (_file, args, options = {}) => {
    const endpoint = args[args.indexOf('--method') + 2];
    const method = args[args.indexOf('--method') + 1];
    if (method === 'GET' && endpoint === 'repos/acme/app/issues/comments/777') {
      return { code: 0, stdout: `HTTP/2 200\r\n\r\n${JSON.stringify({ id: 777, body: savedBody })}`, stderr: '' };
    }
    if (method === 'PATCH' && endpoint === 'repos/acme/app/issues/comments/777') {
      savedBody = JSON.parse(options.input).body;
      return { code: 0, stdout: `HTTP/2 200\r\n\r\n${JSON.stringify({ id: 777, body: savedBody })}`, stderr: '' };
    }
    if (method === 'POST' && endpoint === 'graphql') {
      return {
        code: 0,
        stdout: `HTTP/2 200\r\n\r\n${JSON.stringify({
          data: {
            repository: {
              i0: { url: 'https://github.com/acme/app/issues/1', labels: { nodes: [{ name: 'pdd:working' }], pageInfo: { hasNextPage: false } } },
              i1: { url: 'https://github.com/acme/app/issues/2', labels: { nodes: [], pageInfo: { hasNextPage: false } } },
            },
          },
        })}`,
        stderr: '',
      };
    }
    if (endpoint === 'repos/acme/app') {
      return { code: 0, stdout: `HTTP/2 200\r\n\r\n${JSON.stringify({ owner: { login: 'alice' } })}`, stderr: '' };
    }
    if (endpoint.startsWith('repos/acme/app/collaborators')) {
      return { code: 0, stdout: `HTTP/2 200\r\n\r\n${JSON.stringify([{ login: 'alice', permissions: { admin: true } }])}`, stderr: '' };
    }
    if (endpoint === 'repos/acme/app/issues/1') {
      return { code: 0, stdout: `HTTP/2 200\r\n\r\n${JSON.stringify({ number: 1, labels: [{ name: 'pdd:working' }], updated_at: '2026-11-20T00:00:00.000Z' })}`, stderr: '' };
    }
    if (endpoint.startsWith('repos/acme/app/issues/1/timeline')) {
      return { code: 0, stdout: `HTTP/2 200\r\n\r\n${JSON.stringify([{ id: 901, event: 'labeled', label: { name: 'pdd:working' }, actor: { login: 'alice' }, created_at: '2026-11-20T00:00:00.000Z' }])}`, stderr: '' };
    }
    if (endpoint.startsWith('repos/acme/app/issues/1/comments')) {
      return { code: 0, stdout: `HTTP/2 200\r\n\r\n${JSON.stringify([{ id: 777, body: savedBody, user: { login: 'alice' }, created_at: '2026-11-20T00:00:00.000Z', updated_at: '2026-11-20T05:00:00.000Z' }])}`, stderr: '' };
    }
    throw Error(`Unexpected gh endpoint: ${method} ${endpoint}`);
  };

  const refreshed = await refreshClaimHeartbeat({
    repository: 'acme/app',
    coordinatorId: 'coord-a',
    machine: 'mac-1',
    at: '2026-11-20T05:00:00.000Z',
    claim: {
      issue: 'https://github.com/acme/app/issues/1',
      active: true,
      coordinatorId: 'coord-a',
      machine: 'mac-1',
      commentId: '777',
      labelEventId: '901',
    },
  }, { execFile: mockExec });
  assert.deepEqual(refreshed, { state: 'refreshed', lastSeen: '2026-11-20T05:00:00.000Z' });
  assert.match(savedBody, /"lastSeen":"2026-11-20T05:00:00\.000Z"/);

  const reader = createDependencyReadPorts({}, { execFile: mockExec, now: () => Date.parse('2026-11-20T06:00:00.000Z') });
  const out = JSON.parse((await reader.owners.read({
    repository: 'acme/app',
    issues: ['https://github.com/acme/app/issues/1', 'https://github.com/acme/app/issues/2'],
  })).json);
  assert.equal(out.claims.length, 1);
  assert.equal(out.claims[0].coordinatorId, 'coord-a');
  assert.equal(out.claims[0].active, true);

  const expiredClaim = await winningClaim('acme/app', 'https://github.com/acme/app/issues/1', reader.github, reader.authority, Date.parse('2026-11-20T10:00:00.000Z'), true);
  assert.equal(expiredClaim.expired, true);
  assert.equal(expiredClaim.active, false);
});

test('P0-1: unlabeled PR with builder skill "pdd-bug" (stripped to "bug") enforces bug-fix base control', async t => {
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.baseCommit('api/tax.mjs', 'export function computeTax(amount) { return amount; }\n');
  // Intentionally NO bug label on the issue!
  w.issue(81, { title: 'Fix tax multiplier rounding' });
  await w.tick();
  const buildCwd = w.job(81, 'build').cwd;
  writeIn(buildCwd, 'api/tax.mjs', 'export function computeTax(amount) { return Math.round(amount * 1.1); }\n');
  // Test that ALREADY passes on base (does not reproduce the bug on base!)
  writeIn(buildCwd, 'test/tax-e2e.test.mjs', [
    "import test from 'node:test';",
    "import assert from 'node:assert/strict';",
    "import http from 'node:http';",
    "import { computeTax } from '../api/tax.mjs';",
    "test('tax endpoint returns zero for zero', async () => {",
    "  const s = http.createServer((_req, res) => res.end(String(computeTax(0))));",
    "  await new Promise(resolve => s.listen(0, '127.0.0.1', resolve));",
    "  try {",
    "    const r = await fetch(`http://127.0.0.1:${s.address().port}`);",
    "    assert.equal(await r.text(), '0');",
    "  } finally { s.close(); }",
    "});",
    '',
  ].join('\n'));
  const { pr } = w.build(81, {
    write: false,
    result: { skill: 'pdd-bug' },
    body: 'Fixes #81\n\nRuntime: PASS\nPath: d — api/tax.mjs, test/tax-e2e.test.mjs — unowned — no contract change — Test: done check',
  });
  await w.tick();
  w.review(81, 'PASS');
  w.suite(81, 0);
  await w.tick();
  assert.equal(pr.merged, false, 'unlabeled pdd-bug PR whose test passes on base must NOT merge');
  const repair = w.job(81, 'repair');
  assert.ok(repair, 'unlabeled pdd-bug PR enters repair on bug-fix-passed-on-base');
  assert.match(repair.input, /passed[- ]on[- ]base|bug-fix-passed-on-base/i);
});

test('P0-2: backside validation lint loads pdd.json config from trusted baseTree, not untrusted PR head', async t => {
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.baseCommit('pdd.json', `${JSON.stringify({ lint: { rules: { 'silent-validation-skip': 'error' } } }, null, 2)}\n`);
  w.baseCommit('api/orders.mjs', 'export function orderTotal(n) { return n; }\n');
  w.issue(82, { title: 'Update orders handler' });
  await w.tick();
  const buildCwd = w.job(82, 'build').cwd;
  // PR head tries to disable silent-validation-skip in its own pdd.json while introducing a skipped E2E test!
  writeIn(buildCwd, 'pdd.json', `${JSON.stringify({
    lint: { disable: ['silent-validation-skip', 'boundary-mock-only-test'] },
  }, null, 2)}\n`);
  writeIn(buildCwd, 'test/orders-e2e.test.mjs', [
    "import test from 'node:test';",
    "test.skip('orders e2e skipped silently', () => {});",
    '',
  ].join('\n'));
  const { pr } = w.build(82, {
    write: false,
    body: 'Fixes #82\n\nRuntime: PASS\nPath: d — pdd.json, test/orders-e2e.test.mjs — unowned — no contract change — Test: done check',
  });
  await w.tick();
  w.review(82, 'PASS');
  await w.tick();
  w.suite(82, 0);
  await w.tick();
  assert.equal(pr.merged, false, 'PR head pdd.json must NOT disable backside validation lint');
  const repair = w.job(82, 'repair');
  assert.ok(repair, 'backside lint must still fire and trigger repair');
  assert.match(repair.input, /silent-validation-skip/);
});

test('P0-3: preReviewTestInventoryCheck cache is keyed by BOTH baseSha and headSha so base retargets invalidate stale cache', async t => {
  const w = await coreWorld(t, { settings: { runs: 1, hygieneGate: 'observe' } });
  w.baseCommit('test/keep.test.mjs', "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('k', () => assert.equal(1, 1));\n");
  w.issue(83, { title: 'Update test' });
  await w.tick();
  const buildCwd = w.job(83, 'build').cwd;
  writeIn(buildCwd, 'test/keep.test.mjs', "import test from 'node:test';\nimport assert from 'node:assert/strict';\ntest('k', () => assert.equal(2, 2));\n");
  w.build(83, {
    write: false,
    body: 'Fixes #83\n\nRuntime: PASS\nPath: d — test/keep.test.mjs — unowned — no contract change — Test: done check',
  });
  const calls = [];
  await w.tick({
    collectTestInventory: async ({ baseSha, headSha }) => {
      calls.push({ baseSha, headSha });
      return { available: true, reason: '', text: `base=${baseSha}\nNew skips: none.\n` };
    },
  });
  assert.equal(calls.length, 1, 'initial inventory check ran once');
  const jobFile = join(w.root, 'jobs', '83.json');
  const saved1 = JSON.parse(readFileSync(jobFile, 'utf8'));
  const originalBaseSha = saved1.testInventory.baseSha;
  assert.match(originalBaseSha, /^[0-9a-f]{40}$/i);

  // Simulate a retargeted base (cached entry carries a different baseSha at the SAME headSha) and clear review to trigger fresh preReviewTestInventoryCheck.
  saved1.testInventory.baseSha = '0'.repeat(40);
  saved1.review = null;
  writeFileSync(jobFile, JSON.stringify(saved1, null, 2));

  await w.tick({
    collectTestInventory: async ({ baseSha, headSha }) => {
      calls.push({ baseSha, headSha });
      return { available: true, reason: '', text: `base=${baseSha}\nNew skips: none.\n` };
    },
  });
  assert.equal(calls.length, 2, 'mismatched baseSha at the same headSha MUST invalidate cache and recompute inventory');
  assert.equal(calls[1].baseSha, originalBaseSha);
  const saved2 = JSON.parse(readFileSync(jobFile, 'utf8'));
  assert.equal(saved2.testInventory.baseSha, originalBaseSha);

  // Transient refresh failure for the SAME baseSha+headSha (e.g. after PR body edit) preserves valid cached job.testInventory for reviewPrompt without overwriting it!
  saved2.review = null;
  saved2.testInventory.bodyKey = 'stale-body-key';
  saved2.testInventory.text = 'CACHED-INVENTORY-MARKER\nNew skips: none.\n';
  writeFileSync(jobFile, JSON.stringify(saved2, null, 2));

  await w.tick({
    collectTestInventory: async () => { throw new Error('transient git error'); },
  });
  const saved3 = JSON.parse(readFileSync(jobFile, 'utf8'));
  assert.equal(saved3.testInventory.failed, false, 'transient refresh error must not overwrite valid cached job.testInventory');
  assert.equal(saved3.testInventory.baseSha, originalBaseSha);
  assert.match(saved3.testInventory.text, /CACHED-INVENTORY-MARKER/);
  const reviewJob = w.job(83, 'review');
  assert.ok(reviewJob, 'review starts in observe mode on transient refresh failure');
  assert.match(reviewJob.input, /CACHED-INVENTORY-MARKER/, 'reviewPrompt retains valid cached inventory for same baseSha+headSha');
});

test('P0-4: pathRules & pathChecks populate job.paths.letters and record accurate pathsOnlyD', async t => {
  const onlyD = pathRules({
    changed: [{ status: 'M', path: 'docs/guide.md' }],
    baseFiles: ['docs/guide.md'],
    body: 'Path: d — docs/guide.md — unowned — no contract change — Test: done check',
  });
  assert.deepEqual(onlyD.letters, ['d']);

  const mixed = pathRules({
    changed: [{ status: 'M', path: 'docs/guide.md' }, { status: 'M', path: 'src/a.mjs' }],
    baseFiles: ['docs/guide.md', 'src/a.mjs'],
    body: 'Path: d — docs/guide.md — unowned — no contract change — Test: done check\nPath: e — src/a.mjs — unowned — no contract change — Test: done check',
  });
  assert.deepEqual(mixed.letters, ['d', 'e']);

  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  const metricsStateDir = join(w.root, 'metrics-state');
  w.baseCommit('docs/guide.md', '# Guide\n');
  w.issue(84, { title: 'Clarify guide' });
  await w.tick({ metricsStateDir });
  writeIn(w.job(84, 'build').cwd, 'docs/guide.md', '# Guide\n\nClear steps.\n');
  const { pr } = w.build(84, {
    write: false,
    body: 'Fixes #84\n\nRuntime: PASS\nPath: d — docs/guide.md — unowned — no contract change — Test: done check',
  });
  await w.tick({ metricsStateDir });
  const saved = JSON.parse(readFileSync(join(w.root, 'jobs', '84.json'), 'utf8'));
  assert.deepEqual(saved.paths?.letters, ['d'], 'job.paths.letters populated during pathChecks');
  w.review(84, 'PASS');
  w.suite(84, 0);
  await w.tick({ metricsStateDir });
  assert.equal(pr.merged, true);

  const historyLines = readFileSync(join(w.root, 'history.jsonl'), 'utf8').trim().split('\n').map(l => JSON.parse(l));
  const mergedHistory = historyLines.find(h => h.issue === 84 && h.outcome === 'merged');
  assert.deepEqual(mergedHistory?.paths?.letters, ['d'], 'history.jsonl preserves paths.letters');

  const runsPath = join(metricsStateDir, 'autopilot', 'metrics', 'runs.jsonl');
  const runLines = readFileSync(runsPath, 'utf8').trim().split('\n').map(l => JSON.parse(l));
  const mergedRun = runLines.find(r => r.issue === 84);
  assert.equal(mergedRun?.pathsOnlyD, true, 'runs.jsonl records pathsOnlyD: true for Path-d-only PR');
});
