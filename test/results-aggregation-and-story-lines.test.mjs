import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { readRunResults, resultLines, usableResult } from '../src/workflow-results.mjs';
import * as seam from '../src/runtime-seam.mjs';
import { SHORT_SCENARIO_SCHEMA, V1_SCENARIO_SCHEMA } from '../src/scenario-compile.mjs';
import { fakeRuntime, portsFor } from './helpers/runtime-fake.mjs';

const SINCE = Date.parse('2026-11-10T10:00:00Z');
const SHA_A = 'a'.repeat(64);
const SHA_B = 'b'.repeat(64);
const SHA_C = 'c'.repeat(64);
const SHA_AB = 'd'.repeat(64);
const SHA_ABC = 'e'.repeat(64);

function makeResultsFixture(t) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-agg-3611-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const root = join(base, 'worktree');
  const state = join(base, 'state');
  mkdirSync(root, { recursive: true });
  mkdirSync(state, { recursive: true });
  const writeBatch = (name, batchFields, summary) => {
    const dir = join(state, 'batches', name);
    mkdirSync(dir, { recursive: true });
    writeFileSync(
      join(dir, 'batch.json'),
      JSON.stringify({ version: 1, batch: name, root, intent: 'check', ...batchFields }),
    );
    if (summary) writeFileSync(join(dir, 'summary.json'), JSON.stringify(summary));
  };
  return { root, state, env: { PDD_STATE_DIR: state, HOME: base }, writeBatch };
}

function makeShortScenarioRepo(t, files) {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-story-lines-101-')));
  t.after(() => rmSync(base, { recursive: true, force: true }));
  const repo = join(base, 'repo');
  const home = join(base, 'home');
  const state = join(base, 'state');
  mkdirSync(repo, { recursive: true });
  mkdirSync(home, { recursive: true });
  mkdirSync(state, { recursive: true });
  for (const [rel, content] of Object.entries(files)) {
    const full = join(repo, rel);
    mkdirSync(join(full, '..'), { recursive: true });
    writeFileSync(full, content);
  }
  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });
  return { repo, home, state };
}

function makeSimplePrompt(title = 'Echo') {
  const itemSchema = {
    type: 'object',
    properties: {
      enabled: { type: 'boolean' },
      label: { type: 'string' },
      value: { type: 'integer' },
    },
    required: ['enabled', 'label', 'value'],
    additionalProperties: false,
  };
  const iface = {
    status: 'approved',
    prose_sha256: '',
    entries: [
      {
        operation: 'run',
        input_schema: {
          type: 'object',
          properties: {
            items: { type: 'array', items: itemSchema },
            step: { type: 'integer' },
          },
          required: ['items', 'step'],
          additionalProperties: false,
        },
        result_schema: { type: 'object', properties: { ok: { type: 'boolean' } }, required: ['ok'], additionalProperties: false },
        errors: [],
      },
    ],
    calls: [],
    resources: [],
    limits: { max_steps: 20, max_model_calls: 20 },
  };
  const render = () =>
    `# ${title}\n\nAccept a list of items and return \`{"ok": true}\`.\n\n## Dependencies\n\nNone.\n\n<details><summary>Runtime interface</summary>\n\n\`\`\`json\n${JSON.stringify(iface)}\n\`\`\`\n</details>\n`;
  iface.prose_sha256 = seam.proseSha256(render());
  return render();
}

function makeWideSeed(count = 60) {
  return {
    items: Array.from({ length: count }, (_, i) => ({ enabled: true, label: `item-${i}`, value: i })),
    step: 0,
  };
}

// ============================================================================
// Part A: pdd#3611 — Aggregate latest per-test verdicts across pdd test batches
// ============================================================================

test('3611: aggregates disjoint current pdd test batches into one result preserving all tests, stories, requests, reports, and combined sourceSha256', t => {
  const f = makeResultsFixture(t);
  const reqA = '11111111-1111-4111-8111-111111111111';
  const reqB = '22222222-2222-4222-8222-222222222222';
  const repA = 'https://rt.example.test/r/report-a';
  const repB = 'https://rt.example.test/r/report-b';

  f.writeBatch(
    '20261110-110000-aaaa',
    {
      created_at: '2026-11-10T11:00:00Z',
      source_sha256: SHA_A,
      rows: [{
        test: 'tests/a.json',
        story: 'user_stories/a.md',
        state: 'passed',
        engine_sha: 'aaaa111122223333',
        requested_model: 'older-model',
        request_ids: [reqA],
        report_url: repA,
      }],
    },
    {
      summary_line: 'Prompt tests: ✓ 2 of 2 criteria',
      rows: [{ test: 'tests/a.json', story: 'user_stories/a.md', summary_line: 'Prompt tests (a): ✓ 2 of 2 criteria' }],
    },
  );
  f.writeBatch(
    '20261110-120000-bbbb',
    {
      created_at: '2026-11-10T12:00:00Z',
      source_sha256: SHA_B,
      rows: [{
        test: 'tests/b.json',
        story: 'user_stories/b.md',
        state: 'passed',
        engine_sha: 'bbbb111122223333',
        requested_model: 'newest-model',
        request_ids: [reqB],
        report_url: repB,
      }],
    },
    {
      summary_line: 'Prompt tests: ✓ 3 of 3 criteria',
      rows: [{ test: 'tests/b.json', story: 'user_stories/b.md', summary_line: 'Prompt tests (b): ✓ 3 of 3 criteria' }],
    },
  );

  const capture = (_root, { tests }) => {
    const key = [...tests].sort().join(',');
    if (key === 'tests/a.json') return { sha256: SHA_A };
    if (key === 'tests/b.json') return { sha256: SHA_B };
    if (key === 'tests/a.json,tests/b.json') return { sha256: SHA_AB };
    throw new Error(`unexpected capture selection: ${key}`);
  };

  const results = readRunResults({ root: f.root, since: SINCE }, { env: f.env, capture });
  assert.equal(results.length, 1);
  const [res] = results;
  assert.equal(res.kind, 'pdd test');
  assert.equal(res.batch, '20261110-120000-bbbb');
  assert.equal(res.at, Date.parse('2026-11-10T12:00:00Z'));
  assert.equal(res.source, 'current');
  assert.equal(res.sourceSha256, SHA_AB);
  assert.deepEqual(res.tests, ['tests/a.json', 'tests/b.json']);
  assert.deepEqual(res.states.map(s => [s.test, s.state]), [
    ['tests/a.json', 'passed'],
    ['tests/b.json', 'passed'],
  ]);
  assert.deepEqual(res.requests, [reqA, reqB]);
  assert.deepEqual(res.reports, [repA, repB]);
  assert.deepEqual(res.stories, [
    'Prompt tests (a): ✓ 2 of 2 criteria',
    'Prompt tests (b): ✓ 3 of 3 criteria',
  ]);
  assert.equal(res.summary, 'Prompt tests: 2/2 passed; tests/a.json: passed; tests/b.json: passed');
  assert.equal(res.engine, 'bbbb11112222');
  assert.equal(res.model, 'newest-model');
  assert.equal(usableResult(res), true);

  const [line] = resultLines(results);
  assert.ok(line.includes('Prompt tests: 2/2 passed'));
  assert.ok(line.includes('Prompt tests (a): ✓ 2 of 2 criteria'));
  assert.ok(line.includes('Prompt tests (b): ✓ 3 of 3 criteria'));
  assert.ok(line.includes(reqA) && line.includes(reqB));
  assert.ok(line.includes(repA) && line.includes(repB));
});

test('3611: latest current verdict always wins per test so regressions are never hidden by earlier passes', t => {
  const f = makeResultsFixture(t);
  f.writeBatch(
    '20261110-110000-aaaa',
    {
      created_at: '2026-11-10T11:00:00Z',
      source_sha256: SHA_A,
      rows: [{ test: 'tests/a.json', story: 'user_stories/a.md', state: 'passed' }],
    },
    {
      summary_line: 'Prompt tests: ✓ 1 of 1 criterion',
      rows: [{ test: 'tests/a.json', story: 'user_stories/a.md', summary_line: 'Prompt tests (a): ✓ 1 of 1 criterion' }],
    },
  );
  f.writeBatch(
    '20261110-120000-bbbb',
    {
      created_at: '2026-11-10T12:00:00Z',
      source_sha256: SHA_A,
      rows: [{ test: 'tests/a.json', story: 'user_stories/a.md', state: 'failed' }],
    },
    {
      summary_line: 'Prompt tests: ✗ 0 of 1 criterion',
      rows: [{ test: 'tests/a.json', story: 'user_stories/a.md', summary_line: 'Prompt tests (a): ✗ 0 of 1 criterion' }],
    },
  );
  f.writeBatch(
    '20261110-130000-cccc',
    {
      created_at: '2026-11-10T13:00:00Z',
      source_sha256: SHA_B,
      rows: [{ test: 'tests/b.json', story: 'user_stories/b.md', state: 'passed' }],
    },
    {
      summary_line: 'Prompt tests: ✓ 2 of 2 criteria',
      rows: [{ test: 'tests/b.json', story: 'user_stories/b.md', summary_line: 'Prompt tests (b): ✓ 2 of 2 criteria' }],
    },
  );

  const capture = (_root, { tests }) => {
    const key = [...tests].sort().join(',');
    if (key === 'tests/a.json') return { sha256: SHA_A };
    if (key === 'tests/b.json') return { sha256: SHA_B };
    if (key === 'tests/a.json,tests/b.json') return { sha256: SHA_AB };
    return { sha256: SHA_ABC };
  };

  const [res] = readRunResults({ root: f.root, since: SINCE }, { env: f.env, capture });
  assert.equal(res.batch, '20261110-130000-cccc');
  assert.equal(res.source, 'current');
  assert.deepEqual(res.states.map(s => [s.test, s.state]), [
    ['tests/a.json', 'failed'],
    ['tests/b.json', 'passed'],
  ]);
  assert.ok(res.summary.startsWith('Prompt tests: no full pass;'));
  assert.ok(!res.summary.includes('2/2 passed'));
  assert.ok(res.stories.includes('Prompt tests (b): ✓ 2 of 2 criteria'));
  assert.ok(res.stories.includes('Prompt tests (a): ✗ 0 of 1 criterion'));
  assert.ok(!res.stories.includes('Prompt tests (a): ✓ 1 of 1 criterion'));
});

test('3611: fail-closed staleness, partial newest batch, stage isolation, and affected-mode isolation', t => {
  // 1. Newest batch changed: must NOT paper over with older current batch
  {
    const f = makeResultsFixture(t);
    f.writeBatch('20261110-110000-aaaa', {
      created_at: '2026-11-10T11:00:00Z',
      source_sha256: SHA_A,
      rows: [{ test: 'tests/a.json', state: 'passed' }],
    }, { summary_line: 'Prompt tests: ✓ a' });
    f.writeBatch('20261110-120000-bbbb', {
      created_at: '2026-11-10T12:00:00Z',
      source_sha256: SHA_B,
      rows: [{ test: 'tests/b.json', state: 'passed' }],
    }, { summary_line: 'Prompt tests: ✓ b' });
    const capture = (_root, { tests }) => ({ sha256: tests[0] === 'tests/a.json' ? SHA_A : SHA_C });
    const [res] = readRunResults({ root: f.root, since: SINCE }, { env: f.env, capture });
    assert.equal(res.batch, '20261110-120000-bbbb');
    assert.equal(res.source, 'changed');
    assert.deepEqual(res.tests, ['tests/b.json']);
  }

  // 2. Older batch changed while newest is current: skip stale older batch
  {
    const f = makeResultsFixture(t);
    f.writeBatch('20261110-110000-aaaa', {
      created_at: '2026-11-10T11:00:00Z',
      source_sha256: SHA_A,
      rows: [{ test: 'tests/a.json', state: 'passed' }],
    }, { summary_line: 'Prompt tests: ✓ a' });
    f.writeBatch('20261110-120000-bbbb', {
      created_at: '2026-11-10T12:00:00Z',
      source_sha256: SHA_B,
      rows: [{ test: 'tests/b.json', state: 'passed' }],
    }, { summary_line: 'Prompt tests: ✓ b' });
    const capture = (_root, { tests }) => ({ sha256: tests[0] === 'tests/b.json' ? SHA_B : SHA_C });
    const [res] = readRunResults({ root: f.root, since: SINCE }, { env: f.env, capture });
    assert.equal(res.batch, '20261110-120000-bbbb');
    assert.equal(res.source, 'current');
    assert.deepEqual(res.tests, ['tests/b.json']);
  }

  // 3. Newest batch in-progress (running) or partial (unknown) while earlier batch passed: merged result stays non-passing
  {
    const f = makeResultsFixture(t);
    f.writeBatch('20261110-110000-aaaa', {
      created_at: '2026-11-10T11:00:00Z',
      source_sha256: SHA_A,
      rows: [{ test: 'tests/a.json', story: 'user_stories/a.md', state: 'passed' }],
    }, {
      summary_line: 'Prompt tests: ✓ 1 of 1 criterion',
      rows: [{ test: 'tests/a.json', story: 'user_stories/a.md', summary_line: 'Prompt tests (a): ✓ 1 of 1 criterion' }],
    });
    f.writeBatch('20261110-120000-bbbb', {
      created_at: '2026-11-10T12:00:00Z',
      source_sha256: SHA_B,
      rows: [{ test: 'tests/b.json', story: 'user_stories/b.md', state: 'running' }],
    });
    const capture = (_root, { tests }) => {
      const key = [...tests].sort().join(',');
      if (key === 'tests/a.json') return { sha256: SHA_A };
      if (key === 'tests/b.json') return { sha256: SHA_B };
      return { sha256: SHA_AB };
    };
    const [runningRes] = readRunResults({ root: f.root, since: SINCE }, { env: f.env, capture });
    assert.equal(runningRes.source, 'current');
    assert.deepEqual(runningRes.tests, ['tests/a.json', 'tests/b.json']);
    assert.deepEqual(runningRes.states.map(s => [s.test, s.state]), [
      ['tests/a.json', 'passed'],
      ['tests/b.json', 'sent'],
    ]);
    assert.ok(runningRes.summary.startsWith('Prompt tests: no full pass;'));
    assert.deepEqual(runningRes.stories, ['Prompt tests (a): ✓ 1 of 1 criterion']);

    // Partial/unknown newest batch also keeps usableResult === false
    f.writeBatch('20261110-120000-bbbb', {
      created_at: '2026-11-10T12:00:00Z',
      source_sha256: SHA_B,
      rows: [{ test: 'tests/b.json', story: 'user_stories/b.md', state: 'unknown' }],
    });
    const [partialRes] = readRunResults({ root: f.root, since: SINCE }, { env: f.env, capture });
    assert.deepEqual(partialRes.states.map(s => [s.test, s.state]), [
      ['tests/a.json', 'passed'],
      ['tests/b.json', 'partial'],
    ]);
    assert.ok(partialRes.summary.startsWith('Prompt tests: no full pass;'));
    assert.equal(usableResult(partialRes), false);
    assert.deepEqual(partialRes.stories, ['Prompt tests (a): ✓ 1 of 1 criterion']);
  }

  // 4. Historical PR 1 batch must NOT merge into current-stage batch
  {
    const f = makeResultsFixture(t);
    const pr1Anchor = join(f.root, 'pr1-anchor');
    mkdirSync(pr1Anchor, { recursive: true });
    f.writeBatch('20261110-110000-aaaa', {
      created_at: '2026-11-10T11:00:00Z',
      source_sha256: SHA_A,
      association: { runId: 'run-1', stage: 'pr1' },
      rows: [{ test: 'tests/a.json', state: 'passed' }],
    }, { summary_line: 'Prompt tests: ✓ pr1 a' });
    f.writeBatch('20261110-120000-bbbb', {
      created_at: '2026-11-10T12:00:00Z',
      source_sha256: SHA_B,
      rows: [{ test: 'tests/b.json', state: 'passed' }],
    }, { summary_line: 'Prompt tests: ✓ current b' });
    const workspace = req => req.stage === 'pr1'
      ? { state: 'eligible', runId: 'run-1', repo: 'example/repo', producerRoot: f.root, tests: req.tests, source_sha256: SHA_A, stage: 'pr1', sourceAnchor: { root: pr1Anchor, head: '1'.repeat(40) } }
      : { state: 'eligible', runId: 'run-1', repo: 'example/repo', producerRoot: f.root, tests: req.tests, source_sha256: SHA_B, stage: 'current', sourceAnchor: { root: f.root, head: '2'.repeat(40) } };
    const capture = (_root, { tests }) => ({ sha256: tests[0] === 'tests/a.json' ? SHA_A : SHA_B });
    const [res] = readRunResults({ root: f.root, since: SINCE }, { env: f.env, workspace, capture });
    assert.equal(res.batch, '20261110-120000-bbbb');
    assert.equal(res.stage, 'current');
    assert.deepEqual(res.tests, ['tests/b.json']);
  }

  // 5. Affected-mode newest batch must NOT pull in omitted baseline tests from earlier full batch
  {
    const f = makeResultsFixture(t);
    f.writeBatch('20261110-110000-aaaa', {
      created_at: '2026-11-10T11:00:00Z',
      source_sha256: SHA_AB,
      rows: [{ test: 'tests/a.json', state: 'passed' }, { test: 'tests/b.json', state: 'passed' }],
    }, { summary_line: 'Prompt tests: ✓ 2' });
    f.writeBatch('20261110-120000-bbbb', {
      created_at: '2026-11-10T12:00:00Z',
      source_sha256: SHA_B,
      check_selection: { mode: 'affected', tests: ['tests/b.json'] },
      rows: [{ test: 'tests/b.json', state: 'passed' }],
    }, { summary_line: 'Prompt tests: ✓ 1' });
    const capture = (_root, { tests }) => ({ sha256: tests.length === 2 ? SHA_AB : SHA_B });
    const [res] = readRunResults({ root: f.root, since: SINCE }, { env: f.env, capture });
    assert.equal(res.batch, '20261110-120000-bbbb');
    assert.deepEqual(res.tests, ['tests/b.json']);
    assert.ok(res.summary.includes('Affected checks only'));
  }
});

// ============================================================================
// Part B: runtime-client#101 Part 1 — Raw authored Short JSON line counts
// ============================================================================

test('runtime-client#101 Part 1: compact Short JSON expanding > 1000 v1 lines emits zero oversized Story warnings across preflight, lint --local, and pdd test', async t => {
  const storyText = '# Compact short story\n\nAccept payloads cleanly.\n\n## Acceptance criteria\n\n1. Every step returns ok true.\n';
  const wideSeed = makeWideSeed(65);
  const steps = Array.from({ length: 6 }, (_, i) => ({
    id: `step-${i + 1}`,
    op: 'run',
    input: { $use: 'base_payload', patch: { step: i + 1 } },
    checks: { 1: [['result', '/ok', '=', true]] },
  }));
  const implicitShortText = `${JSON.stringify({
    entry_path: 'prompts/echo.prompt.md',
    seeds: { base_payload: wideSeed },
    steps,
  }, null, 2)}\n`;
  const explicitShortText = `${JSON.stringify({
    schema_version: SHORT_SCENARIO_SCHEMA,
    entry_path: 'prompts/echo.prompt.md',
    seeds: { base_payload: wideSeed },
    steps,
  }, null, 2)}\n`;

  const implicitRawLines = implicitShortText.trimEnd().split('\n').length;
  const explicitRawLines = explicitShortText.trimEnd().split('\n').length;
  assert.ok(implicitRawLines < 500, `expected compact implicit Short JSON (< 500 raw lines), got ${implicitRawLines}`);
  assert.ok(explicitRawLines < 500, `expected compact explicit Short JSON (< 500 raw lines), got ${explicitRawLines}`);

  const { repo, home, state } = makeShortScenarioRepo(t, {
    'prompts/echo.prompt.md': makeSimplePrompt(),
    'user_stories/compact-implicit.md': storyText,
    'tests/compact-implicit.json': implicitShortText,
    'user_stories/compact-explicit.md': storyText,
    'tests/compact-explicit.json': explicitShortText,
  });

  const found = seam.findTests({ root: repo });
  assert.equal(found.tests.length, 2);
  for (const item of found.tests) {
    assert.ok(typeof item.compiledText === 'string', `${item.path} should compile from Short JSON`);
    const expandedLines = item.compiledText.trimEnd().split('\n').length;
    assert.ok(expandedLines > 1000, `expected expanded compiledText > 1000 lines for ${item.path}, got ${expandedLines}`);
  }

  // 1. Direct preflight()
  const pf = seam.preflight({ root: repo, found, selected: found.tests });
  const pfOversized = pf.warnings.filter(w => w.includes('oversized Story'));
  assert.deepEqual(pfOversized, [], `expected no oversized Story warnings from preflight, got:\n${pfOversized.join('\n')}`);

  // 2. Repo-wide & Story-scoped pdd lint --local --json
  for (const words of [[], ['compact-implicit'], ['compact-explicit']]) {
    let stdout = '';
    let stderr = '';
    const code = await seam.runCheck(
      { cwd: repo, words, options: { '--lint': true, '--local': true, '--json': true } },
      {
        env: { HOME: home, PDD_STATE_DIR: state },
        stdout: { write: s => { stdout += s; } },
        stderr: { write: s => { stderr += s; } },
      },
    );
    assert.equal(code, 0, stderr);
    const report = JSON.parse(stdout);
    const oversized = (report.warnings ?? []).filter(w => w.includes('oversized Story'));
    assert.deepEqual(oversized, [], `expected no oversized Story warnings for lint --local ${words.join(' ')}, got:\n${oversized.join('\n')}`);
  }

  // 3. Full pdd test (seam.check) against fakeRuntime
  const fake = await fakeRuntime(t, (entry, f) =>
    entry.method === 'POST' && entry.command === 'lint'
      ? { status: 200, json: f.lint(entry.request.requestId, [{ path: 'prompts/echo.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } }]) }
      : f.normal(entry),
  );
  const { ports } = portsFor({ HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin });
  const checkCode = await seam.check({ cwd: repo, words: [], options: { '--json': true } }, ports);
  assert.equal(checkCode, 0, `${ports.stderr.text}\n${ports.stdout.text}`);
  const checkJson = JSON.parse(ports.stdout.text);
  const checkOversized = (checkJson.warnings ?? []).filter(w => w.includes('oversized Story'));
  assert.deepEqual(checkOversized, [], `expected no oversized Story warnings from pdd test, got:\n${checkOversized.join('\n')}`);
  assert.ok(!ports.stderr.text.includes('oversized Story'), `unexpected stderr oversized Story:\n${ports.stderr.text}`);
});

test('runtime-client#101 Part 1: genuinely > 1000-line Short JSON warns with real raw authored line count, > 15 steps keeps step-only warning, and regular v1 JSON stays unchanged', async t => {
  const storyText = '# Oversized checks\n\nAccept payloads cleanly.\n\n## Acceptance criteria\n\n1. Every step returns ok true.\n';

  // 1. Genuinely oversized explicit Short JSON (> 1000 raw lines, expands to even more)
  const bigSeed = makeWideSeed(210); // ~1060 raw lines when pretty-printed
  const bigExplicitShortText = `${JSON.stringify({
    schema_version: SHORT_SCENARIO_SCHEMA,
    entry_path: 'prompts/echo.prompt.md',
    seeds: { big: bigSeed },
    steps: [
      { id: 's1', op: 'run', input: { $use: 'big', patch: { step: 1 } }, checks: { 1: [['result', '/ok', '=', true]] } },
      { id: 's2', op: 'run', input: { $use: 'big', patch: { step: 2 } }, checks: { 1: [['result', '/ok', '=', true]] } },
    ],
  }, null, 2)}\n`;
  const bigRawLines = bigExplicitShortText.trimEnd().split('\n').length;
  assert.ok(bigRawLines > 1000, `expected > 1000 raw authored lines, got ${bigRawLines}`);

  // 2. Compact Short JSON with 16 steps (<= 1000 raw lines, expands to > 1000 v1 lines) -> step warning ONLY, no line warning
  const manyStepsSeed = makeWideSeed(30);
  const manyStepsShortText = `${JSON.stringify({
    entry_path: 'prompts/echo.prompt.md',
    seeds: { base: manyStepsSeed },
    steps: Array.from({ length: 16 }, (_, i) => ({
      id: `s${i + 1}`,
      op: 'run',
      input: { $use: 'base', patch: { step: i + 1 } },
      checks: { 1: [['result', '/ok', '=', true]] },
    })),
  }, null, 2)}\n`;
  const manyStepsRawLines = manyStepsShortText.trimEnd().split('\n').length;
  assert.ok(manyStepsRawLines < 1000, `expected < 1000 raw authored lines for 16-step Short JSON, got ${manyStepsRawLines}`);

  // 3. Regular v1 JSON (> 1000 raw lines) -> behaves identically to today
  const bigV1Text = `${JSON.stringify({
    schema_version: V1_SCENARIO_SCHEMA,
    story_path: 'user_stories/regular-v1.md',
    criteria: [{ id: 'AC1', text: 'Every step returns ok true.' }],
    initial_world: {},
    steps: [{
      step_id: 's1',
      entry_path: 'prompts/echo.prompt.md',
      operation: 'run',
      input: bigSeed,
      checks: [{ criterion_id: 'AC1', target: 'result', path: '/ok', op: 'equals', value: true }],
    }],
  }, null, 2)}\n`;
  const bigV1Lines = bigV1Text.trimEnd().split('\n').length;
  assert.ok(bigV1Lines > 1000, `expected > 1000 lines for regular v1 JSON, got ${bigV1Lines}`);

  const { repo, home, state } = makeShortScenarioRepo(t, {
    'prompts/echo.prompt.md': makeSimplePrompt(),
    'user_stories/big-short.md': storyText,
    'tests/big-short.json': bigExplicitShortText,
    'user_stories/many-steps.md': storyText,
    'tests/many-steps.json': manyStepsShortText,
    'user_stories/regular-v1.md': storyText,
    'tests/regular-v1.json': bigV1Text,
  });

  const found = seam.findTests({ root: repo });
  const bigShortItem = found.tests.find(item => item.path === 'tests/big-short.json');
  const manyStepsItem = found.tests.find(item => item.path === 'tests/many-steps.json');
  const v1Item = found.tests.find(item => item.path === 'tests/regular-v1.json');
  assert.ok(bigShortItem.compiledText.trimEnd().split('\n').length > bigRawLines + 500);
  assert.ok(manyStepsItem.compiledText.trimEnd().split('\n').length > 1000);
  assert.equal(v1Item.compiledText, undefined);

  // 1. preflight()
  const pf = seam.preflight({ root: repo, found, selected: found.tests });
  const bigShortWarn = pf.warnings.find(w => w.includes('(tests/big-short.json)'));
  assert.ok(bigShortWarn, `expected oversized Story warning for big-short, got:\n${pf.warnings.join('\n')}`);
  assert.ok(bigShortWarn.includes(`${bigRawLines} lines (limit: 1000)`), `expected real raw line count ${bigRawLines}, got: ${bigShortWarn}`);

  const manyStepsWarn = pf.warnings.find(w => w.includes('(tests/many-steps.json)'));
  assert.ok(manyStepsWarn, `expected step-count warning for many-steps, got:\n${pf.warnings.join('\n')}`);
  assert.ok(manyStepsWarn.includes('16 scenario steps (limit: 15)'), manyStepsWarn);
  assert.ok(!manyStepsWarn.includes('lines (limit: 1000)'), `must not emit bogus line-count warning on <=1000-line Short JSON: ${manyStepsWarn}`);

  const v1Warn = pf.warnings.find(w => w.includes('(tests/regular-v1.json)'));
  assert.ok(v1Warn && v1Warn.includes(`${bigV1Lines} lines (limit: 1000)`), `expected regular v1 warning with ${bigV1Lines} lines, got: ${v1Warn}`);

  // 2. lint --local --json (both repo-wide and explicit Story selection)
  for (const words of [[], ['big-short']]) {
    let stdout = '';
    let stderr = '';
    const code = await seam.runCheck(
      { cwd: repo, words, options: { '--lint': true, '--local': true, '--json': true } },
      {
        env: { HOME: home, PDD_STATE_DIR: state },
        stdout: { write: s => { stdout += s; } },
        stderr: { write: s => { stderr += s; } },
      },
    );
    assert.equal(code, 0, stderr);
    const report = JSON.parse(stdout);
    const matches = (report.warnings ?? []).filter(w => w.includes('(tests/big-short.json)'));
    assert.equal(matches.length, 1, `expected exactly 1 raw-line warning for big-short (${words.join(' ') || 'repo'}), got:\n${matches.join('\n')}`);
    assert.ok(matches[0].includes(`${bigRawLines} lines (limit: 1000)`), matches[0]);
  }

  // 3. pdd test (seam.check) against fakeRuntime also reports real raw authored line count for big-short
  const fake = await fakeRuntime(t, (entry, f) =>
    entry.method === 'POST' && entry.command === 'lint'
      ? { status: 200, json: f.lint(entry.request.requestId, [{ path: 'prompts/echo.prompt.md', state: 'approved', admission_state: 'approved', interface: { calls: [] } }]) }
      : f.normal(entry),
  );
  const { ports } = portsFor({ HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: fake.origin });
  const checkCode = await seam.check({ cwd: repo, words: ['big-short'], options: { '--json': true } }, ports);
  assert.equal(checkCode, 0, `${ports.stderr.text}\n${ports.stdout.text}`);
  const checkJson = JSON.parse(ports.stdout.text);
  const checkBigWarn = (checkJson.warnings ?? []).filter(w => w.includes('(tests/big-short.json)'));
  assert.equal(checkBigWarn.length, 1, `expected exactly 1 raw-line warning from pdd test, got:\n${checkBigWarn.join('\n')}`);
  assert.ok(checkBigWarn[0].includes(`${bigRawLines} lines (limit: 1000)`), checkBigWarn[0]);
});
