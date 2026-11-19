import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import {
  PREFLIGHT_REASON_CODES,
  sanitizeIssueText,
  classifyPreflightIssue,
  summarizeIntakeFilterPrecision,
} from '../src/autopilot-intake-preflight.mjs';
import {
  PREFLIGHT_REASON_CODES as REEXPORTED_CODES,
  PREFLIGHT_MARKER_PREFIX,
  OTHER_REPO_MARKER_PREFIX,
  NEEDS_OTHER_REPO_LABEL,
  sanitizeIssueText as reexportedSanitize,
  classifyPreflightIssue as reexportedClassify,
  summarizeIntakeFilterPrecision as reexportedSummarize,
  detectWrongRepositoryIssue,
  applyPreflightDecision,
  shadowIntake,
  activeIntake,
  readIntake,
  intakeText,
  cardPrompt,
  improvePrompt,
  readCard,
  readImprovement,
} from '../src/autopilot-intake.mjs';

function pointer(root, path) {
  if (!path || path === '/') return root;
  let cur = root;
  for (const part of path.replace(/^\//, '').split('/')) {
    const key = part.replace(/~1/g, '/').replace(/~0/g, '~');
    cur = cur == null ? undefined : cur[key];
  }
  return cur;
}

function makeIntakeHarness(t, { mode = 'active', repo = 'promptdriven/pdd', failNextLabel = false } = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-preflight-wiring-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const root = join(dir, 'state');
  const cwd = join(dir, 'repo');
  mkdirSync(join(cwd, 'src'), { recursive: true });
  mkdirSync(join(cwd, 'test'), { recursive: true });
  writeFileSync(join(cwd, 'src', 'accounts-cli.mjs'), 'export const accounts = true;\n');
  writeFileSync(join(cwd, 'src', 'metrics-model.mjs'), 'export const metrics = true;\n');
  writeFileSync(join(cwd, 'src', 'runtime-seam.mjs'), 'export const seam = true;\n');

  let now = Date.parse('2026-11-18T12:00:00Z');
  let pid = 100;
  let shouldFailLabel = failNextLabel;
  const writes = [];
  const commentsByIssue = new Map();
  const labelsByIssue = new Map();
  const alerts = [];
  const warnings = [];
  const startedJobs = [];

  const gh = {
    all: async endpoint => {
      const m = endpoint.match(/issues\/(\d+)\/comments/);
      if (m) return [...(commentsByIssue.get(Number(m[1])) ?? [])];
      return [];
    },
    call: async (method, endpoint, payload) => {
      writes.push({ method, endpoint, payload });
      const labelMatch = endpoint.match(/issues\/(\d+)\/labels/);
      if (method === 'POST' && labelMatch) {
        if (shouldFailLabel) {
          shouldFailLabel = false;
          return { status: 503 };
        }
        const n = Number(labelMatch[1]);
        const set = labelsByIssue.get(n) ?? new Set();
        for (const name of payload?.labels ?? []) set.add(name);
        labelsByIssue.set(n, set);
        return { status: 200 };
      }
      return { status: 200 };
    },
    ok: async (method, endpoint, payload) => {
      writes.push({ method, endpoint, payload });
      const commentMatch = endpoint.match(/issues\/(\d+)\/comments/);
      if (method === 'POST' && commentMatch) {
        const n = Number(commentMatch[1]);
        const list = commentsByIssue.get(n) ?? [];
        list.push({ id: list.length + 1, body: payload.body, user: { login: 'autopilot-bot' }, created_at: new Date(now).toISOString() });
        commentsByIssue.set(n, list);
        return {};
      }
      return {};
    },
  };

  const jobs = {
    start: spec => {
      const job = { ...spec, pid: ++pid, log: join(spec.dir, `${spec.id}.log`), exit: join(spec.dir, `${spec.id}.exit.json`) };
      writeFileSync(job.log, '');
      startedJobs.push(job);
      return job;
    },
    read: () => ({ state: 'running', exit: null, result: null }),
    stop: () => {},
  };

  const ctx = {
    fs,
    now: () => now,
    root,
    repo,
    state: { agent: { kind: 'codex', command: 'codex', model: 'gpt-test' }, cwd },
    settings: { intake: mode },
    budget: { state: 'normal' },
    gh,
    jobs,
    ports: {
      trusted: async ({ user }) => user?.login === 'maintainer' || user?.login === 'serhan',
      agentReady: async () => true,
      alert: async payload => { alerts.push(payload); },
      env: {},
    },
    warn: msg => warnings.push(msg),
  };

  return {
    ctx,
    root,
    cwd,
    writes,
    commentsByIssue,
    labelsByIssue,
    alerts,
    warnings,
    startedJobs,
    advance: ms => { now += ms; },
  };
}

test('3534 runtime scenario parity: all 8 steps and 42 checks in test/runtime/autopilot-intake-preflight.json pass natively', () => {
  const scenario = JSON.parse(readFileSync(new URL('./runtime/autopilot-intake-preflight.json', import.meta.url), 'utf8'));
  const ops = { classifyPreflightIssue, summarizeIntakeFilterPrecision };
  let totalChecks = 0;

  for (const step of scenario.steps) {
    const fn = ops[step.operation];
    assert.equal(typeof fn, 'function', `operation ${step.operation} exists`);
    const snapshot = JSON.stringify(step.input);
    const result = fn(step.input);
    assert.equal(JSON.stringify(step.input), snapshot, `${step.step_id} never mutates caller input`);

    for (const check of step.checks) {
      totalChecks += 1;
      const actual = pointer(result, check.path);
      if (check.op === 'equals') {
        assert.deepEqual(actual, check.value, `${step.step_id} ${check.path}`);
      } else if (check.op === 'at_least' && check.measure === 'length') {
        assert.equal(typeof actual, 'string', `${step.step_id} ${check.path} is string`);
        assert.ok(actual.length >= check.value, `${step.step_id} ${check.path} length ${actual.length} >= ${check.value}`);
      } else if (check.op === 'count') {
        assert.ok(Array.isArray(actual), `${step.step_id} ${check.path} is array`);
        assert.equal(actual.length, check.value, `${step.step_id} ${check.path} count`);
      } else {
        assert.fail(`unsupported check op ${check.op}`);
      }
    }
  }
  assert.equal(scenario.steps.length, 8);
  assert.equal(totalChecks, 42);
});

test('3534 sanitizeIssueText strips HTML comments, backtick/tilde fences, and blockquotes while preserving real prose', () => {
  const raw = [
    'Real title context',
    '<!-- Repo: promptdriven/pdd_cloud -->',
    '```txt',
    'Error in pdd_cloud/api/billing.py: Open question: pricing?',
    '```',
    '~~~sh',
    'Repository: promptdriven/pdd-workflow',
    '~~~',
    '  > Quoted: Open question: should we charge $99?',
    'Keep this local fix in `src/runtime-seam.mjs`.',
  ].join('\n');
  const cleaned = sanitizeIssueText(raw);
  assert.match(cleaned, /Real title context/);
  assert.match(cleaned, /src\/runtime-seam\.mjs/);
  assert.doesNotMatch(cleaned, /pdd_cloud|pdd-workflow|Open question|\$99/);
  assert.equal(sanitizeIssueText(null), '');
});

test('3534 classifyPreflightIssue enforces strict precedence and handles replay edge cases', () => {
  // Precedence: cross_repo beats human_decision and unverifiable_boundary.
  const multi = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 1,
      title: '[pdd_cloud] Sync billing and verify in live production',
      body: 'Open question: should Pro tier be $19 or $29? Update `pdd_cloud/api/billing.py` and verify with live Stripe checkout and maintainer 2FA.',
      comments: [],
    },
    repoFiles: ['src/accounts-cli.mjs'],
  });
  assert.equal(multi.decision, 'reject');
  assert.equal(multi.reasonCode, 'cross_repo');
  assert.equal(multi.label, 'needs-other-repo');
  assert.equal(multi.targetRepo, 'pdd_cloud');
  assert.equal(multi.question, null);

  // Unnamed external service coordinated edit -> canonical "external-service".
  const extService = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 2,
      title: 'Ship paired webhook change',
      body: 'Update `src/accounts-cli.mjs` and requires a paired deployment in an external service.',
      comments: [],
    },
    repoFiles: ['src/accounts-cli.mjs'],
  });
  assert.equal(extService.decision, 'reject');
  assert.equal(extService.reasonCode, 'cross_repo');
  assert.equal(extService.targetRepo, 'external-service');
  assert.ok(extService.signals.includes('coordinated_multi_repo'));

  // Untrusted comment can neither resolve nor trigger a human decision.
  const untrustedResolve = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 3,
      title: 'Choose default output view',
      body: 'Open question: should `pdd metrics` default to overview or full?',
      comments: [
        { author: 'outsider', trusted: false, at: '2026-11-18T10:00:00Z', body: 'Decision: go with full.' },
      ],
    },
    repoFiles: ['src/metrics-model.mjs'],
  });
  assert.equal(untrustedResolve.decision, 'park');
  assert.equal(untrustedResolve.reasonCode, 'human_decision');

  const untrustedTrigger = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 4,
      title: 'Fix crash on empty metrics file',
      body: 'Fix `src/metrics-model.mjs` so empty JSONL files do not throw.',
      comments: [
        { author: 'outsider', trusted: false, body: 'Pricing decision: should we charge $50/month?' },
      ],
    },
    repoFiles: ['src/metrics-model.mjs'],
  });
  assert.equal(untrustedTrigger.decision, 'allow');

  // decisionNote resolves human_decision.
  const resolvedByNote = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 5,
      title: 'Choose default output view',
      body: 'Open question: should `pdd metrics` default to overview or full?',
      comments: [],
    },
    repoFiles: ['src/metrics-model.mjs'],
    decisionNote: 'Trusted person removed pdd:needs-decision; treat option A as approved.',
  });
  assert.equal(resolvedByNote.decision, 'allow');

  // Named external E2E recipe unavailable vs available (case-insensitive).
  const recipeIssue = {
    number: 6,
    title: 'Validate staging checkout sync',
    body: 'Acceptance criteria: run external E2E recipe: Stripe-Staging-E2E before merge.',
    comments: [],
  };
  const missingRecipe = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: recipeIssue,
    repoFiles: ['src/accounts-cli.mjs'],
    workerCapabilities: { localTests: true, liveExternalServices: false, availableRecipes: ['npm test'] },
  });
  assert.equal(missingRecipe.decision, 'park');
  assert.equal(missingRecipe.reasonCode, 'unverifiable_boundary');
  assert.ok(missingRecipe.signals.includes('unavailable_external_e2e'));

  const presentRecipe = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: recipeIssue,
    repoFiles: ['src/accounts-cli.mjs'],
    workerCapabilities: { localTests: true, liveExternalServices: false, availableRecipes: ['stripe-staging-e2e'] },
  });
  assert.equal(presentRecipe.decision, 'allow');

  // Manual human QA / physical device parked; trusted comment authorizing local tests allows it.
  const manualQa = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 7,
      title: 'Verify layout on real mobile device',
      body: 'Acceptance criteria: requires manual human QA sign-off on a physical iPhone device.',
      comments: [],
    },
    repoFiles: ['src/runtime-seam.mjs'],
  });
  assert.equal(manualQa.decision, 'park');
  assert.equal(manualQa.reasonCode, 'unverifiable_boundary');
  assert.ok(manualQa.signals.includes('manual_human_qa_only'));

  const localAuthorized = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 7,
      title: 'Verify layout on real mobile device',
      body: 'Acceptance criteria: requires manual human QA sign-off on a physical iPhone device.',
      comments: [
        { author: 'maintainer', trusted: true, body: 'Decision: verify with local unit tests and dry-run fixtures instead.' },
      ],
    },
    repoFiles: ['src/runtime-seam.mjs'],
  });
  assert.equal(localAuthorized.decision, 'allow');

  // Reference-only foreign GitHub URL alongside greenfield local files stays allow.
  const referenceOnly = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 8,
      title: 'Add src/runtime-retry.mjs for prompt-runtime transient 503s',
      body: 'Create `src/runtime-retry.mjs` and `test/runtime-retry.test.mjs` so PDD retries transient 503s from `prompt-runtime` (see https://github.com/promptdriven/pdd-cloud/blob/main/pdd_cloud/gateway/retry.py for reference).',
      comments: [],
    },
    repoFiles: ['src/runtime-seam.mjs', 'test/runtime-seam.test.mjs'],
  });
  assert.equal(referenceOnly.decision, 'allow');
  assert.deepEqual(referenceOnly.signals, []);
});

test('3534 summarizeIntakeFilterPrecision deduplicates skips by latest timestamp and ranks merged/would-merge runs', () => {
  const skips = [
    { repo: 'PromptDriven/PDD', issue: 10, reasonCode: 'human_decision', at: '2026-11-18T08:00:00Z' },
    { repo: 'promptdriven/pdd', issue: 10, reasonCode: 'cross_repo', at: '2026-11-18T09:00:00Z' },
    { repo: 'promptdriven/pdd', issue: 11, reasonCode: 'unverifiable_boundary', at: '2026-11-18T09:30:00Z' },
    { repo: 'promptdriven/pdd', issue: -1, reasonCode: 'cross_repo' },
    { repo: 'promptdriven/pdd', issue: 12, reasonCode: 'not_a_code' },
  ];
  const runs = [
    { repo: 'promptdriven/pdd', issue: 20, status: 'failed' },
    { repo: 'PromptDriven/PDD', issue: 20, status: 'merged' },
    { repo: 'promptdriven/pdd', issues: [21, 22], status: 'would-merge' },
    { repo: 'promptdriven/pdd', issue: 23, status: 'running' },
    { repo: 'promptdriven/pdd', issue: 24, status: 'needs-person' },
    { repo: 'promptdriven/pdd', issue: 25, status: 'ended' },
  ];
  const snapshot = JSON.stringify({ skips, runs });
  const summary = summarizeIntakeFilterPrecision({ skips, runs });
  assert.equal(JSON.stringify({ skips, runs }), snapshot, 'inputs are not mutated');

  assert.equal(summary.skipped, 2);
  assert.deepEqual(summary.byReasonCode, { cross_repo: 1, human_decision: 0, unverifiable_boundary: 1 });
  assert.equal(summary.taken, 6);
  assert.equal(summary.merged, 3);
  assert.equal(summary.unmerged, 3);
  assert.equal(summary.classifierConversionPct, 50);
  assert.equal(summary.classifierConversionDisplay, '3/6 (50.0%)');
  assert.equal(summary.skipSummary, 'Pre-flight skipped (2): 1 cross_repo · 1 unverifiable_boundary');
});

test('3534 autopilot-intake wiring: re-exports, sanitization, shadowIntake read-only skip ledger, and intakeText summary', async t => {
  assert.equal(REEXPORTED_CODES, PREFLIGHT_REASON_CODES);
  assert.equal(reexportedSanitize, sanitizeIssueText);
  assert.equal(reexportedClassify, classifyPreflightIssue);
  assert.equal(reexportedSummarize, summarizeIntakeFilterPrecision);

  // detectWrongRepositoryIssue ignores fenced/quoted mentions and detects pdd-workflow paths.
  const h = makeIntakeHarness(t, { mode: 'shadow' });
  assert.equal(
    detectWrongRepositoryIssue(
      { title: 'Fix error message', body: 'Fix `src/runtime-seam.mjs`.\n```text\nRepository: promptdriven/pdd_cloud\n```\n> Repo: promptdriven/pdd-workflow' },
      { repo: 'promptdriven/pdd', cwd: h.cwd },
    ),
    null,
  );
  assert.equal(
    detectWrongRepositoryIssue(
      { title: 'Update workflow scorecard', body: 'Edit `pdd-workflow/scripts/scorecard.py`.' },
      { repo: 'promptdriven/pdd', cwd: h.cwd },
    )?.targetRepo,
    'pdd-workflow',
  );

  // Shadow mode records pre-flight skips locally with ZERO GitHub writes and ZERO AI card jobs for skipped issues.
  const rows = [
    {
      number: 401,
      title: 'Sync billing between pdd and pdd_cloud',
      body: 'Requires coordinated changes in both `src/accounts-cli.mjs` and `pdd_cloud/api/billing.py`.',
      labels: [],
      assignees: [],
      comments: 0,
      user: { login: 'maintainer' },
      created_at: '2026-11-18T01:00:00Z',
    },
    {
      number: 402,
      title: 'Set Pro tier pricing',
      body: 'Open question: should Pro tier be $19 or $29? Needs a pricing decision.',
      labels: [],
      assignees: [],
      comments: 0,
      user: { login: 'maintainer' },
      created_at: '2026-11-18T02:00:00Z',
    },
    {
      number: 403,
      title: 'Fix local CLI retry output',
      body: 'Fix `src/runtime-seam.mjs` to print a retry hint when `prompt-runtime` returns 502 and verify with local unit tests.',
      labels: [],
      assignees: [],
      comments: 0,
      user: { login: 'maintainer' },
      created_at: '2026-11-18T03:00:00Z',
    },
  ];
  await shadowIntake(h.ctx, rows);
  assert.equal(h.writes.length, 0, 'shadowIntake makes zero GitHub writes');
  assert.deepEqual(h.startedJobs.map(j => j.issue), [403], 'only the valid local issue starts an AI card job');

  const report = readIntake({ root: h.root, now: h.ctx.now() });
  assert.equal(report.preflightSkips.length, 2);
  assert.deepEqual(report.preflightSkips.map(s => [s.issue, s.reasonCode]), [[401, 'cross_repo'], [402, 'human_decision']]);
  assert.ok(report.diff.some(d => d.kind === 'preflight-skip' && d.issue === 401 && d.reasonCode === 'cross_repo'));
  assert.ok(report.diff.some(d => d.kind === 'preflight-skip' && d.issue === 402 && d.reasonCode === 'human_decision'));

  const printed = intakeText(report, { mode: 'shadow' });
  assert.match(printed, /Pre-flight skipped \(2\): 1 cross_repo · 1 human_decision/);
  assert.match(printed, /#401 preflight-skip \(cross_repo -> reject\)/);
});

test('3534 activeIntake + applyPreflightDecision: routes cross-repo, parks human/unverifiable, resumes after trusted answer, and retries failed GitHub writes cleanly', async t => {
  const h = makeIntakeHarness(t, { mode: 'active' });
  const crossRepoRow = {
    number: 501,
    title: 'Coordinate scorecard in pdd-workflow and pdd',
    body: 'Coordinate changes across promptdriven/pdd and pdd-workflow: update `pdd-workflow/scripts/scorecard.py` alongside `src/metrics-model.mjs`.',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T01:00:00Z',
  };
  const decisionRow = {
    number: 502,
    title: 'Choose default pdd metrics view',
    body: 'Open question: should `pdd metrics` default to overview or full?',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T02:00:00Z',
  };
  const unverifiableRow = {
    number: 503,
    title: 'Verify live Stripe checkout in production',
    body: 'Acceptance criteria: trigger a real $1 live Stripe checkout charge in production with maintainer 2FA credentials. No local mock or fake test is accepted.',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T03:00:00Z',
  };

  await activeIntake(h.ctx, [crossRepoRow, decisionRow, unverifiableRow]);
  assert.equal(h.startedJobs.length, 0, 'zero AI card jobs spawned for pre-flight skipped issues');
  assert.ok(h.labelsByIssue.get(501)?.has(NEEDS_OTHER_REPO_LABEL));
  assert.ok(h.labelsByIssue.get(502)?.has('pdd:needs-decision'));
  assert.ok(h.labelsByIssue.get(503)?.has('pdd:needs-decision'));
  assert.equal((h.commentsByIssue.get(501) ?? []).filter(c => c.body.includes(`${OTHER_REPO_MARKER_PREFIX}501 -->`)).length, 1);
  assert.equal((h.commentsByIssue.get(502) ?? []).filter(c => c.body.includes(`${PREFLIGHT_MARKER_PREFIX}502:`)).length, 1);
  assert.equal((h.commentsByIssue.get(503) ?? []).filter(c => c.body.includes(`${PREFLIGHT_MARKER_PREFIX}503:`)).length, 1);
  assert.equal(h.alerts.filter(a => a.kind === 'decision').length, 2, 'alerts emitted for both parked issues');

  // Once a trusted maintainer answers #502 in a comment and removes pdd:needs-decision, activeIntake allows it and starts a card job.
  decisionRow.labels = [];
  h.labelsByIssue.get(502)?.delete('pdd:needs-decision');
  h.commentsByIssue.get(502).push({
    id: 99,
    body: 'Decision: default to overview and keep full under `pdd metrics full`.',
    user: { login: 'maintainer' },
    created_at: '2026-11-18T12:05:00Z',
  });
  decisionRow.comments = h.commentsByIssue.get(502).length;
  h.advance(60_000);

  await activeIntake(h.ctx, [crossRepoRow, decisionRow, unverifiableRow]);
  assert.deepEqual(h.startedJobs.map(j => j.issue), [502], 'answered decision issue passes pre-flight and enters intake');

  // Failure edge: GitHub label write fails -> warns, does NOT mark preflight-routed.json, retries cleanly next tick with 1 comment total.
  const hFail = makeIntakeHarness(t, { mode: 'active', failNextLabel: true });
  const retryRow = {
    number: 504,
    title: 'Set seat price for Pro tier',
    body: 'Pricing decision: should Pro tier cost $19/seat or $29/seat?',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T04:00:00Z',
  };
  await activeIntake(hFail.ctx, [retryRow]);
  assert.equal(hFail.startedJobs.length, 0, 'failed pre-flight GitHub write never claims or starts an AI card');
  assert.ok(hFail.warnings.some(w => w.includes('#504')), 'warns via ctx.warn on GitHub write failure');
  assert.equal(hFail.labelsByIssue.get(504)?.has('pdd:needs-decision') ?? false, false);

  await activeIntake(hFail.ctx, [retryRow]);
  assert.equal(hFail.startedJobs.length, 0, 'still parked after retry succeeds');
  assert.equal(hFail.labelsByIssue.get(504)?.has('pdd:needs-decision'), true, 'label applied on retry');
  assert.equal((hFail.commentsByIssue.get(504) ?? []).filter(c => c.body.includes(`${PREFLIGHT_MARKER_PREFIX}504:`)).length, 1, 'exactly one comment posted after retry');

  // cardPrompt / improvePrompt / readCard / readImprovement contracts.
  assert.match(cardPrompt({ repo: 'promptdriven/pdd', row: decisionRow, comments: [], pool: [] }), /reason_code/);
  assert.match(improvePrompt({ repo: 'promptdriven/pdd', row: decisionRow, comments: [], card: { reason: 'x' }, pool: [] }), /"outcome":"ready\|person\|elsewhere"/);
  assert.equal(readCard({ class: 'elsewhere', reason: 'Needs pdd_cloud edit.', reason_code: 'cross_repo' })?.reasonCode, 'cross_repo');
  assert.equal(readCard({ class: 'person', reason: 'Invalid code ignored.', reason_code: 'bogus' })?.reasonCode, null);
  const impElsewhere = readImprovement({ outcome: 'elsewhere', reason: 'Belongs in pdd-workflow.' });
  assert.equal(impElsewhere?.outcome, 'elsewhere');
  assert.equal(impElsewhere?.reasonCode, 'cross_repo');
  const impUnverifiable = readImprovement({ outcome: 'person', reason: 'Needs live prod creds.', reason_code: 'unverifiable_boundary', question: 'Allow local fake test?' });
  assert.equal(impUnverifiable?.reasonCode, 'unverifiable_boundary');

  // Direct applyPreflightDecision on an allow verdict is a clean no-op.
  const noop = await applyPreflightDecision(hFail.ctx, retryRow, { decision: 'allow', reasonCode: null });
  assert.deepEqual(noop, { applied: false, commented: false, label: null, reasonCode: null });
});
