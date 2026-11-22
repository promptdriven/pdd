import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, mkdtempSync, readdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
import { productNext, productStart, productStatus, readProduct, runProduct } from '../src/product.mjs';

const ROOT = new URL('../', import.meta.url).pathname;

function makeFixture(t) {
  const cwd = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-product-s6-')));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  cpSync(new URL('../examples/coffee-pickup/', import.meta.url), cwd, { recursive: true });
  const state = { issues: [], prs: [], events: {}, creates: [] };
  const ports = {
    lockProductState: async () => ({ handle: 's6-lock' }),
    unlockProductState: async () => ({}),
    readProductState: async () => ({ json: state.productState ?? null }),
    writeProductState: async ({ json }) => { state.productState = json; return {}; },
    now: async () => ({ milliseconds: (state.clock = (state.clock ?? 0) + 60000) }),
    listRuns: async () => [],
    resolveRepository: async () => ({ repository: 'example/coffee', defaultBranch: 'main' }),
    planOnBase: async args => { state.baseArgs = args; return true; },
    openBaseSource: async () => ({ root: cwd, handle: null }),
    savedStoryEvidence: async () => ({ stories: [], warnings: [] }),
    issueByNumber: async ({ number }) => {
      const row = state.issues.find(i => i.number === number);
      return row ? { author_association: 'OWNER', user: { login: 'owner' }, created_at: '2026-11-01T00:00:00Z', state: 'OPEN', ...row } : { status: 404, message: 'Not Found' };
    },
    issuePage: async ({ page, perPage }) => {
      const all = state.issues.map(i => ({ author_association: 'OWNER', user: { login: 'owner' }, created_at: '2026-11-01T00:00:00Z', state: 'OPEN', ...i }));
      return { items: all.slice((page - 1) * perPage, page * perPage), total_count: all.length, incomplete_results: false };
    },
    timelinePage: async ({ issue }) => state.events[issue] ?? [],
    pullRequest: async ({ number }) => state.prs.find(p => p.number === number),
    createIssue: async payload => {
      state.creates.push(payload);
      const number = 300 + state.creates.length;
      state.issues.push({ number, body: payload.body, state: 'OPEN' });
      return { url: `https://github.com/example/coffee/issues/${number}` };
    },
  };
  return { cwd, state, ports };
}

const xref = number => ({ event: 'cross-referenced', source: { issue: { pull_request: { html_url: `https://github.com/example/coffee/pull/${number}` } } } });
const mkPr = (number, body, state = 'MERGED') => ({
  number,
  url: `https://github.com/example/coffee/pull/${number}`,
  body,
  state,
  isDraft: false,
  updatedAt: '2026-11-02T00:00:00Z',
  headRefName: `feat-${number}`,
  isCrossRepository: false,
  headRepository: { name: 'coffee' },
  headRepositoryOwner: { login: 'example' },
});

test('S6 architecture: src/core/product/* modules are <=450 LOC with zero legacy workflow imports', () => {
  const dir = join(ROOT, 'src/core/product');
  const files = readdirSync(dir).filter(f => f.endsWith('.mjs')).sort();
  assert.ok(files.length >= 6, 'expected modular core product files');
  for (const rel of ['src/product.mjs', 'src/product-documents.mjs', ...files.map(f => `src/core/product/${f}`)]) {
    const text = readFileSync(join(ROOT, rel), 'utf8');
    const lines = text.split('\n').length;
    assert.ok(lines <= 450, `${rel} is ${lines} lines (>450)`);
    assert.equal(/\bworkflow-[a-z-]+\.mjs\b/.test(text), false, `${rel} must not import legacy workflow-* modules`);
  }
});

test('S6 workflow-free productStart prints crisp /pdd handoff with wave and SHA-pinned base when startRun is not injected', async t => {
  const f = makeFixture(t);
  execFileSync('git', ['init', '-q', '-b', 'release/v2'], { cwd: f.cwd });
  execFileSync('git', ['config', 'user.name', 'Test'], { cwd: f.cwd });
  execFileSync('git', ['config', 'user.email', 'test@example.invalid'], { cwd: f.cwd });
  const planPath = join(f.cwd, 'product/plan.md');
  writeFileSync(planPath, readFileSync(planPath, 'utf8').replace('# Coffee pickup: plan', '# Coffee pickup: plan\nBase: release/v2\nIssue: #42'));
  execFileSync('git', ['add', '.'], { cwd: f.cwd });
  execFileSync('git', ['commit', '-qm', 'plan'], { cwd: f.cwd });
  const headSha = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: f.cwd, encoding: 'utf8' }).trim();

  const product = await readProduct({ cwd: f.cwd }, f.ports);
  assert.equal(product.base, 'release/v2');
  assert.equal(product.issue, 42);

  const started = await productStart({ cwd: f.cwd, run: 'phone-1' }, f.ports);
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(started.created, true);
  assert.equal(started.started, false);
  assert.equal(started.handoff, '/pdd');
  assert.equal(f.state.baseArgs.baseBranch, 'release/v2');
  assert.match(started.message, /Wave 1/);
  assert.match(started.message, new RegExp(`release/v2 @ ${headSha.slice(0, 7)}`));
  assert.match(started.message, /\/pdd for issue #301/);
  assert.match(f.state.creates[0].body, /^Part of #42 \(product\)\./m);

  const status = await productStatus({ cwd: f.cwd }, f.ports);
  assert.equal(status.base, 'release/v2');
  assert.equal(status.baseSha, headSha);
  assert.deepEqual(status.waves, [
    { wave: 1, runs: ['server-1', 'phone-1', 'barista-1'] },
    { wave: 2, runs: ['journeys'] },
  ]);
  const textNext = await runProduct({ cwd: f.cwd, command: 'next' }, f.ports);
  assert.equal(textNext.exitCode, 0);
  assert.match(textNext.message, /Wave 1: server-1, phone-1, barista-1\./);
  assert.match(textNext.message, /Wave 2: journeys\./);
});

test('#3328 mechanical fix: single-part runs mock other parts while all/journey runs require real unmocked cross-part integration + pdd sim --product', async t => {
  const f = makeFixture(t);
  const single = await productStart({ cwd: f.cwd, run: 'phone-1', noRun: true }, f.ports);
  assert.equal(single.exitCode, 0);
  const singleBody = f.state.creates[0].body;
  assert.match(singleBody, /Other parts are fakes from their contracts\. Do not change contracts\/ in this run\./);

  const journey = await productStart({ cwd: f.cwd, run: 'journeys', noRun: true }, f.ports);
  assert.equal(journey.exitCode, 0);
  const journeyBody = f.state.creates[1].body;
  assert.doesNotMatch(journeyBody, /Other parts are fakes from their contracts/);
  assert.match(journeyBody, /real unmocked cross-part journeys/i);
  assert.match(journeyBody, /pdd sim --product/);
});

test('S6 completion accepts canonical pdd-product stage markers and normal merged same-repo PRs closing the issue without weakening prompt-only guards', async t => {
  const f = makeFixture(t);
  f.state.issues = [
    { number: 81, body: '<!-- pdd-product: run=server-1 -->' },
    { number: 82, body: '<!-- pdd-product: run=phone-1 -->' },
    { number: 83, body: '<!-- pdd-product: run=barista-1 -->' },
  ];
  f.state.events = { 81: [xref(11)], 82: [xref(12)], 83: [xref(13)] };
  // 1) server-1: canonical stage=prompt-pr, phone-1: normal closing PR (Closes #82), barista-1: canonical stage=code.
  f.state.prs = [
    mkPr(11, '<!-- pdd-product: run=server-1 stage=prompt-pr -->\nCloses #81'),
    mkPr(12, 'Implement phone slice.\n\nCloses #82'),
    mkPr(13, '<!-- pdd-product: run=barista-1 stage=code -->'),
  ];

  // Under default code target, server-1 is still prompt-pr-only (even with Closes #81!), so journeys waits on server-1 only.
  const nextCode = await productNext({ cwd: f.cwd }, f.ports);
  assert.deepEqual(nextCode.ready, []);
  assert.deepEqual(nextCode.waiting, [{ run: 'journeys', needs: ['server-1'] }]);

  // Under --through prompt-pr, all three satisfy prompt-pr and journeys becomes ready!
  const nextPrompt = await productNext({ cwd: f.cwd, through: 'prompt-pr' }, f.ports);
  assert.deepEqual(nextPrompt.ready, ['journeys']);

  // Upgrading server-1 to a normal same-repo merged PR closing #81 unlocks journeys under default code target!
  f.state.prs[0] = mkPr(11, 'Implement server slice.\nFixes #81');
  const nextDone = await productNext({ cwd: f.cwd }, f.ports);
  assert.deepEqual(nextDone.ready, ['journeys']);
});
