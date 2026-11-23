import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as fs from 'node:fs';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { coreWorld } from './helpers/core-world.mjs';
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
  DECLINED_MARKER_PREFIX,
  DEFAULT_MIN_INTAKE_CONFIDENCE,
  NEEDS_OTHER_REPO_LABEL,
  normalizeSiblingRepos,
  sanitizeIssueText as reexportedSanitize,
  classifyPreflightIssue as reexportedClassify,
  summarizeIntakeFilterPrecision as reexportedSummarize,
  detectWrongRepositoryIssue,
  applyPreflightDecision,
  commentWhyDeclined,
  collectActiveIntake,
  activeReadyCards,
  wouldPick,
  issueVersion,
  intakeFolders,
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

function makeIntakeHarness(t, { mode = 'active', repo = 'promptdriven/pdd', failNextLabel = false, failNextCommentFetch = false, agentReady = true } = {}) {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-preflight-wiring-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const root = join(dir, 'state');
  const cwd = join(dir, 'repo');
  mkdirSync(join(cwd, 'src'), { recursive: true });
  mkdirSync(join(cwd, 'prompts', 'cli'), { recursive: true });
  mkdirSync(join(cwd, 'test'), { recursive: true });
  writeFileSync(join(cwd, 'src', 'accounts-cli.mjs'), 'export const accounts = true;\n');
  writeFileSync(join(cwd, 'src', 'metrics-model.mjs'), 'export const metrics = true;\n');
  writeFileSync(join(cwd, 'src', 'runtime-seam.mjs'), 'export const seam = true;\n');
  writeFileSync(join(cwd, 'src', 'login-pool.mjs'), 'export const pool = true;\n');
  writeFileSync(join(cwd, 'prompts', 'cli', 'login-pool.prompt.md'), '# login-pool\n');

  let now = Date.parse('2026-11-18T12:00:00Z');
  let pid = 100;
  let shouldFailLabel = failNextLabel;
  let shouldFailCommentFetch = failNextCommentFetch;
  const writes = [];
  const commentsByIssue = new Map();
  const labelsByIssue = new Map();
  const timelineByIssue = new Map();
  const alerts = [];
  const warnings = [];
  const startedJobs = [];

  const gh = {
    all: async endpoint => {
      const cm = endpoint.match(/issues\/(\d+)\/comments/);
      if (cm) {
        if (shouldFailCommentFetch) {
          shouldFailCommentFetch = false;
          throw new Error('HTTP 502 Bad Gateway reading comments');
        }
        return [...(commentsByIssue.get(Number(cm[1])) ?? [])];
      }
      const tm = endpoint.match(/issues\/(\d+)\/timeline/);
      if (tm) return [...(timelineByIssue.get(Number(tm[1])) ?? [])];
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
    login: async () => 'autopilot-bot',
    state: { agent: { kind: 'codex', command: 'codex', model: 'gpt-test' }, cwd },
    settings: { intake: mode },
    budget: { state: 'normal' },
    gh,
    jobs,
    ports: {
      trusted: async ({ user }) => user?.login === 'maintainer' || user?.login === 'serhan',
      agentReady: async () => agentReady,
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
    timelineByIssue,
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
    siblingRepos: ['pdd_cloud'],
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
  assert.deepEqual(summary.byReasonCode, { cross_repo: 1, human_decision: 0, unverifiable_boundary: 1, unclear_or_unsound: 0 });
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
      { repo: 'promptdriven/pdd', cwd: h.cwd, siblingRepos: ['pdd-workflow'] },
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

test('3534 adversarial regressions (MF1-MF2): eliminates cross_repo false positives, handles CommonMark fences, and keeps true multi-repo catches', () => {
  const repoFiles = ['src/metrics-model.mjs', 'src/command-catalog.mjs', 'src/runtime-seam.mjs', 'src/accounts-cli.mjs', 'src/login-pool.mjs', 'package.json'];

  // MF1: everyday prose ("alongside", slash tokens, dependency bumps, meta-issues, companion tracking briefs) must stay allow.
  const singleRepoSamples = [
    {
      name: 'slash tokens in prose + alongside English',
      title: 'Fix local/state cleanup alongside existing npm cache',
      body: 'Update `src/metrics-model.mjs` to remove/use sqlite/postgres or headless/process config in `.codex/skills` (3/4 installs/launches confirm y/N).',
    },
    {
      name: 'dependency bump of @promptdriven/runtime-client',
      title: 'Bump @promptdriven/runtime-client pin and enforce src/command-catalog.mjs flag parity',
      body: 'Since PR #3418, 12 commits have merged to `@promptdriven/runtime-client` `main` closing issues across both repos. Changes in `runtime-client` that add CLI flags to `test/host-shims/command-catalog.mjs` do not update `src/command-catalog.mjs`. Bump `@promptdriven/runtime-client` in `package.json`.',
    },
    {
      name: 'meta-issue describing cross-repo classifier',
      title: 'Tighten Autopilot intake classifier',
      body: 'Filter issues before spending tokens when they:\n- Require coordinated changes in another repository (`pdd_cloud`, `pdd-workflow`, external services).',
    },
    {
      name: 'locked-in brief referencing companion tracking issue',
      title: 'pdd metrics overhaul',
      body: '# Locked-In Brief: `pdd metrics` Overhaul (`pdd#3530` & `pdd-workflow#3787`)\nUpdate `src/metrics-model.mjs` to add Regressions column.',
    },
    {
      name: 'MF2 title prefixes and non-repo Service headers',
      title: 'src/metrics-model.mjs: fix NaN under systemd',
      body: 'Service: launchd\nFix NaN division in `src/metrics-model.mjs`.',
    },
    {
      name: 'MF2 bracketed UI/CLI and feat/branch title prefixes',
      title: '[CLI/UX] improve help output',
      body: 'Service: systemd\nUpdate `src/command-catalog.mjs`.',
    },
    {
      name: 'MF2 feat/metrics prefix',
      title: 'feat/metrics: add regressions column',
      body: 'Update `src/metrics-model.mjs`.',
    },
    {
      name: 'MF2 reference-only foreign URL without local files named yet',
      title: 'Improve retry backoff messaging',
      body: 'See https://github.com/other-org/example/blob/main/retry.ts for reference on clearer retry messages.',
    },
  ];
  for (const sample of singleRepoSamples) {
    const res = classifyPreflightIssue({
      repository: 'promptdriven/pdd',
      issue: { number: 100, title: sample.title, body: sample.body, comments: [] },
      repoFiles,
    });
    assert.equal(res.decision, 'allow', `${sample.name} must stay allow (got ${res.decision}/${res.reasonCode}: ${res.reason})`);
  }

  // MF2: other-org/pdd is NOT the same repository as promptdriven/pdd.
  const otherOrgSameShort = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: { number: 101, title: 'Fix fork build', body: 'Repo: other-org/pdd\nFix `custom/fork.py`.' },
    repoFiles,
  });
  assert.equal(otherOrgSameShort.decision, 'reject');
  assert.equal(otherOrgSameShort.reasonCode, 'cross_repo');
  assert.equal(otherOrgSameShort.targetRepo, 'other-org/pdd');

  // MF2: CommonMark sanitization strips 4-space indented fences in lists and ignores inline triple backticks.
  const indentedFence = sanitizeIssueText([
    '- Observed log:',
    '    ```',
    '    Repo: promptdriven/pdd_cloud',
    '    Update pdd_cloud/billing/stripe.py',
    '    ```',
    '```inline``` keep this real line about `src/metrics-model.mjs`.',
  ].join('\n'));
  assert.doesNotMatch(indentedFence, /pdd_cloud\/billing\/stripe\.py/, '4-space indented fence stripped');
  assert.match(indentedFence, /keep this real line about `src\/metrics-model\.mjs`/, 'inline triple backticks do not swallow prose');

  // True multi-repo heading (#3426 shape) still rejects as cross_repo.
  const trueMultiRepo = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 3426,
      title: 'pdd accounts: use tokenless gateway_grant for shared Codex logins',
      body: '### 1. Server (`promptdriven/pdd_cloud`)\nAdd endpoint.\n### 2. Client (`promptdriven/pdd`)\nUpdate `src/accounts-cli.mjs`.',
    },
    repoFiles,
  });
  assert.equal(trueMultiRepo.decision, 'reject');
  assert.equal(trueMultiRepo.reasonCode, 'cross_repo');
  assert.equal(trueMultiRepo.targetRepo, 'promptdriven/pdd_cloud');
});

test('3534 adversarial regressions (MF3-MF4): engineering prose stays allow, natural answers resolve, npm test never bypasses mandatory live gates, and all recipes are checked', () => {
  const repoFiles = ['src/metrics-model.mjs', 'src/login-pool.mjs', 'src/accounts-cli.mjs'];

  // MF3: engineering questions mentioning plan/cost/quota/limit/default/copy/policy/publish/deprecate stay allow.
  const engineeringBug = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 201,
      title: 'Fix quota limit default copy on publish retry',
      body: 'Should we retry when quota limit returns 429 or fall back to cached plan cost policy before we deprecate the old endpoint?',
    },
    repoFiles,
  });
  assert.equal(engineeringBug.decision, 'allow', 'pure engineering bug with policy-adjacent words stays allow');

  // MF3: natural maintainer answers resolve human_decision without rigid Decision: prefix.
  for (const reply of ["Let's default to overview.", '$19/seat and 1 free account.', 'A']) {
    const resolved = classifyPreflightIssue({
      repository: 'promptdriven/pdd',
      issue: {
        number: 202,
        title: 'Choose Pro tier seat pricing',
        body: 'Pricing decision: should Pro tier charge $19/seat or $29/seat?',
        comments: [{ author: 'serhan', trusted: true, body: reply }],
      },
      repoFiles,
    });
    assert.equal(resolved.decision, 'allow', `natural reply ${JSON.stringify(reply)} resolves human_decision`);
  }

  // MF4: npm test / pdd test / node --test in the issue MUST NOT bypass mandatory prod/manual/recipe gates.
  const liveWithNpmTest = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 203,
      title: 'Verify live Stripe checkout in production',
      body: 'Run `npm test` and `node --test`, and acceptance criteria also require triggering a real $1 live Stripe checkout charge in production with maintainer 2FA credentials.',
    },
    repoFiles,
  });
  assert.equal(liveWithNpmTest.decision, 'park', 'npm test must not bypass mandatory live production gate');
  assert.equal(liveWithNpmTest.reasonCode, 'unverifiable_boundary');

  // MF4: later trusted comment rejecting mocks overrides an earlier positive local-verify comment.
  const laterRejectsMocks = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 204,
      title: 'Verify live webhook',
      body: 'Acceptance criteria: verify against live Stripe webhook with production credentials.',
      comments: [
        { author: 'serhan', trusted: true, at: '2026-11-18T10:00:00Z', body: 'Use local unit tests and fake HTTP server instead.' },
        { author: 'serhan', trusted: true, at: '2026-11-18T11:00:00Z', body: 'Actually no mocks are accepted — must verify against live Stripe.' },
      ],
    },
    repoFiles,
  });
  assert.equal(laterRejectsMocks.decision, 'park', 'later trusted rejection overrides earlier local authorization');
  assert.equal(laterRejectsMocks.reasonCode, 'unverifiable_boundary');

  // MF4: redaction/security bugs mentioning production credentials or live API keys stay allow.
  const redactionBug = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 205,
      title: 'Never log production credentials or live API keys',
      body: 'Fix `src/login-pool.mjs` to redact production credentials, production API keys, and live Stripe keys from error logs so zero plaintext leaks.',
    },
    repoFiles,
  });
  assert.equal(redactionBug.decision, 'allow', 'defensive redaction bug mentioning production credentials stays allow');

  // MF4: multiple named recipes are all checked via matchAll.
  const multiRecipes = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 206,
      title: 'Run both verification recipes',
      body: 'Verification recipe: recipe-a\nVerification recipe: recipe-b',
    },
    repoFiles,
    workerCapabilities: { localTests: true, availableRecipes: ['recipe-a'] },
  });
  assert.equal(multiRecipes.decision, 'park', 'missing second named recipe still parks');
  assert.equal(multiRecipes.reasonCode, 'unverifiable_boundary');
  assert.match(multiRecipes.reason, /recipe-b/);
});

test('3534 adversarial regressions (MF3/MF5/MF6 + minor): comment-before-label, no re-park loop on PREFLIGHT_MARKER_PREFIX, cwd module lookup, shadow ordering, stale improve card, and readIntake date scope', async t => {
  // MF5: comment MUST be posted BEFORE label; comment-fetch error warns and posts nothing; stale comments:0 still deduplicates.
  const hOrder = makeIntakeHarness(t, { mode: 'active' });
  const parkRow = {
    number: 601,
    title: 'Choose Pro pricing',
    body: 'Pricing decision: should Pro tier charge $19/seat or $29/seat?',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T01:00:00Z',
  };
  await activeIntake(hOrder.ctx, [parkRow]);
  const issue601Writes = hOrder.writes.filter(w => w.endpoint.includes('/issues/601/'));
  assert.ok(issue601Writes.length >= 2);
  assert.match(issue601Writes[0].endpoint, /\/comments$/, 'comment posted BEFORE label');
  assert.match(issue601Writes[1].endpoint, /\/labels$/, 'label applied AFTER comment');

  // MF3: removing pdd:needs-decision after a PREFLIGHT_MARKER_PREFIX comment breaks the infinite re-park loop even with NO comment!
  parkRow.labels = [];
  hOrder.labelsByIssue.get(601)?.delete('pdd:needs-decision');
  parkRow.comments = 0; // Even if row.comments is stale!
  hOrder.timelineByIssue.set(601, [
    { event: 'unlabeled', label: { name: 'pdd:needs-decision' }, actor: { login: 'serhan' }, created_at: '2026-11-18T12:05:00Z' },
  ]);
  hOrder.advance(60_000);
  await activeIntake(hOrder.ctx, [parkRow]);
  assert.deepEqual(hOrder.startedJobs.map(j => j.issue), [601], 'trusted label removal after PREFLIGHT_MARKER_PREFIX resumes without re-parking');
  assert.equal(hOrder.labelsByIssue.get(601)?.has('pdd:needs-decision') ?? false, false, 'does not re-apply pdd:needs-decision');

  // MF5: comment-fetch error logs warning and does NOT post duplicate comment or label.
  const hFetchErr = makeIntakeHarness(t, { mode: 'active', failNextCommentFetch: true });
  const errRow = {
    number: 602,
    title: 'Choose Pro pricing',
    body: 'Pricing decision: should Pro tier charge $19/seat or $29/seat?',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T02:00:00Z',
  };
  const errRes = await applyPreflightDecision(hFetchErr.ctx, errRow, {
    decision: 'park',
    reasonCode: 'human_decision',
    label: 'pdd:needs-decision',
    reason: 'Needs pricing choice.',
    question: 'Should Pro tier charge $19/seat or $29/seat?',
  });
  assert.equal(errRes.applied, false);
  assert.equal(hFetchErr.writes.length, 0, 'zero GitHub writes when comment fetch fails');
  assert.ok(hFetchErr.warnings.some(w => w.includes('#602')));

  // MF6: bare local module name ("login-pool") in production cwd mode keeps issue local.
  assert.equal(
    detectWrongRepositoryIssue(
      { title: 'Refresh login-pool backoff when prompt-runtime returns 503', body: 'In `login-pool`, add retry jitter when calling `prompt-runtime`.' },
      { repo: 'promptdriven/pdd', cwd: hOrder.cwd },
    ),
    null,
    'cwd inventory includes src/login-pool.mjs so bare module reference stays local',
  );

  // Minor: shadowIntake records pre-flight skips BEFORE canStart() even when agentReady is false (zero GitHub writes).
  const hShadow = makeIntakeHarness(t, { mode: 'shadow', agentReady: false });
  const shadowSkipRow = {
    number: 603,
    title: 'Choose pricing model',
    body: 'Pricing decision: should we charge $19/seat or $29/seat?',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T03:00:00Z',
  };
  await shadowIntake(hShadow.ctx, [shadowSkipRow]);
  assert.equal(hShadow.writes.length, 0, 'shadow mode makes zero GitHub writes');
  const shadowToday = readIntake({ root: hShadow.root, date: '2026-11-18' });
  const shadowOtherDay = readIntake({ root: hShadow.root, date: '2026-11-19' });
  assert.equal(shadowToday.preflightSkips.length, 1, 'shadowIntake recorded pre-flight skip even when canStart() was false');
  assert.equal(shadowOtherDay.preflightSkips.length, 0, 'readIntake scopes preflightSkips to requested UTC date');

  // Minor: activeIntake checks pre-flight on pre-existing improve cards before spawning auto-improve.
  const hImprove = makeIntakeHarness(t, { mode: 'active' });
  const fImp = intakeFolders(hImprove.root);
  mkdirSync(fImp.cards, { recursive: true });
  const staleImproveRow = {
    number: 604,
    title: 'Verify live Stripe checkout in production',
    body: 'Acceptance criteria: trigger a real $1 live Stripe checkout charge in production with maintainer 2FA credentials.',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T04:00:00Z',
  };
  // Seed a matching improve card from before the pre-flight classifier existed.
  const { issueVersion } = await import('../src/autopilot-intake.mjs');
  writeFileSync(join(fImp.cards, '604.json'), JSON.stringify({
    issue: 604,
    version: issueVersion(staleImproveRow),
    at: hImprove.ctx.now(),
    agent: { kind: 'codex', model: 'gpt-test' },
    native: null,
    card: { class: 'improve', confidence: 0.7, reason: 'Needs detail', areas: [] },
  }));
  await activeIntake(hImprove.ctx, [staleImproveRow]);
  assert.equal(hImprove.startedJobs.length, 0, 'stale improve card is parked at pre-flight instead of spawning auto-improve');
  assert.equal(hImprove.labelsByIssue.get(604)?.has('pdd:needs-decision'), true);

  // Minor: cross-repo routing comment excludes local-root greenfield paths from missingPaths.
  const hGreenfield = makeIntakeHarness(t, { mode: 'active' });
  hGreenfield.ctx.settings.siblingRepos = ['pdd_cloud'];
  const mixedGreenfieldRow = {
    number: 605,
    title: 'Coordinate pdd_cloud handler with new local helper',
    body: 'Update `pdd_cloud/webhooks/github.py` alongside creating `src/new-local-helper.mjs`.',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T05:00:00Z',
  };
  await activeIntake(hGreenfield.ctx, [mixedGreenfieldRow]);
  const routeComment605 = (hGreenfield.commentsByIssue.get(605) ?? [])[0]?.body ?? '';
  assert.match(routeComment605, /pdd_cloud\/webhooks\/github\.py/, 'foreign path reported in missingPaths');
  assert.doesNotMatch(routeComment605, /src\/new-local-helper\.mjs/, 'local-root greenfield path excluded from missingPaths');
});

test('3534 adversarial regression (MF7): autopilot-core pre-claim enforces cross_repo, human_decision, and unverifiable_boundary with intake off and resumes after trusted resolution', async t => {
  const w = await coreWorld(t, { repository: 'promptdriven/pdd', settings: { runs: 3, intake: 'off', label: 'pdd:autopilot' } });
  mkdirSync(join(w.cwd, 'src'), { recursive: true });
  writeFileSync(join(w.cwd, 'src', 'accounts-cli.mjs'), 'export const accounts = true;\n');
  writeFileSync(join(w.cwd, 'src', 'metrics-model.mjs'), 'export const metrics = true;\n');

  w.issue(701, {
    user: 'promptdriven',
    labels: ['pdd:autopilot'],
    title: 'Coordinate pdd_cloud and pdd gateway change',
    body: '### 1. Server (`promptdriven/pdd_cloud`)\nUpdate `pdd_cloud/gateway/codex.py`.\n### 2. Client (`promptdriven/pdd`)\nUpdate `src/accounts-cli.mjs`.',
  });
  w.issue(702, {
    user: 'promptdriven',
    labels: ['pdd:autopilot'],
    title: 'Choose seat price for Pro tier',
    body: 'Pricing decision: should Pro tier charge $19/seat or $29/seat?',
  });
  w.issue(703, {
    user: 'promptdriven',
    labels: ['pdd:autopilot'],
    title: 'Verify live Stripe checkout in production',
    body: 'Acceptance criteria: trigger a real $1 live Stripe checkout charge in production with maintainer 2FA credentials.',
  });
  w.issue(704, {
    user: 'promptdriven',
    labels: ['pdd:autopilot'],
    title: 'Fix metrics NaN guard',
    body: 'Update `src/metrics-model.mjs` so empty arrays return 0 instead of NaN.',
  });

  await w.tick();
  assert.equal(w.job(701, 'build'), undefined, 'coordinated multi-repo #701 not claimed');
  assert.equal(w.job(702, 'build'), undefined, 'unanswered pricing #702 not claimed');
  assert.equal(w.job(703, 'build'), undefined, 'unverifiable live prod #703 not claimed');
  assert.ok(w.job(704, 'build'), 'normal single-repo #704 claimed and started');

  assert.equal(w.labels(701).includes(NEEDS_OTHER_REPO_LABEL), true, '#701 labeled needs-other-repo');
  assert.equal(w.labels(702).includes('pdd:needs-decision'), true, '#702 labeled pdd:needs-decision');
  assert.equal(w.labels(703).includes('pdd:needs-decision'), true, '#703 labeled pdd:needs-decision');
  assert.equal(w.comments(702).filter(c => c.includes(`${PREFLIGHT_MARKER_PREFIX}702:`)).length, 1);
  assert.equal(w.comments(703).filter(c => c.includes(`${PREFLIGHT_MARKER_PREFIX}703:`)).length, 1);

  const skips = readIntake({ root: w.root, now: w.now() }).preflightSkips;
  assert.deepEqual(
    skips.map(s => [s.issue, s.reasonCode, s.mode]).sort((a, b) => a[0] - b[0]),
    [
      [701, 'cross_repo', 'core'],
      [702, 'human_decision', 'core'],
      [703, 'unverifiable_boundary', 'core'],
    ],
    'core pre-claim records all three pre-flight skip reasons in preflight-skips.jsonl',
  );

  // Trusted maintainer answers #702 and removes pdd:needs-decision -> next tick claims #702 without re-parking!
  w.advance(5000);
  w.github.comment(702, '$19/seat and 1 free account.', 'promptdriven');
  w.github.unlabel(702, 'pdd:needs-decision', 'promptdriven');
  // Trusted maintainer removes pdd:needs-decision on #703 without a comment -> next tick claims #703 too!
  w.github.unlabel(703, 'pdd:needs-decision', 'promptdriven');
  await w.tick();
  assert.equal(w.labels(702).includes('pdd:needs-decision'), false, '#702 is not re-parked after trusted answer');
  assert.ok(w.job(702, 'build'), '#702 is claimed and started by core after trusted answer');
  assert.equal(w.labels(703).includes('pdd:needs-decision'), false, '#703 is not re-parked after trusted label removal');
  assert.ok(w.job(703, 'build'), '#703 is claimed and started by core after trusted label removal');
});

test('3534 R2 regressions (items 1-7 + minor): headings, reference URLs, title/Service slugs, clause-bound coord, unverifiable/recipe/comment guards, deferrals, nested dirs, and timeline errors', async t => {
  const repoFiles = ['src/metrics-model.mjs', 'src/accounts-cli.mjs', 'src/login-pool.mjs', 'src/runtime-seam.mjs', 'package.json'];

  // Item 1: passive/contrast/error/mock headings stay allow; deliverable repo headings still reject.
  const headingAllows = [
    {
      name: '#3274-style comment contrast heading',
      title: 'Add scope triage to pdd-feature',
      body: 'Update `src/runtime-seam.mjs` for native-only guidance.',
      comments: [{ author: 'maintainer', trusted: true, body: '### Concrete contrast in `promptdriven/agent-link`\nObservational data point only.' }],
    },
    {
      name: 'error handling heading for sibling',
      title: 'Retry transient runtime 502s',
      body: '## Handling 502 errors from prompt-runtime\nAdd backoff in `src/runtime-seam.mjs`.',
      comments: [],
    },
    {
      name: 'mocking heading for sibling',
      title: 'Improve local account tests',
      body: '### Mock pdd_cloud in local tests\nUse fake HTTP responses in `src/accounts-cli.mjs`.',
      comments: [],
    },
  ];
  for (const sample of headingAllows) {
    const res = classifyPreflightIssue({
      repository: 'promptdriven/pdd',
      issue: { number: 801, title: sample.title, body: sample.body, comments: sample.comments },
      repoFiles,
    });
    assert.equal(res.decision, 'allow', `Item 1 (${sample.name}) must stay allow (got ${res.decision}/${res.reasonCode}: ${res.reason})`);
  }
  const deliverableListReject = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 3428,
      title: 'pdd accounts: enrolled Codex logins stay at 0% usage',
      body: '1. **`promptdriven/pdd` CLI (`src/accounts-cli.mjs`):**\nRefresh usage.\n2. **`promptdriven/pdd_cloud` (`cloud_accounts_usage.py`):**\nFix parser.',
    },
    repoFiles,
  });
  assert.equal(deliverableListReject.decision, 'reject');
  assert.equal(deliverableListReject.reasonCode, 'cross_repo');

  // Item 2: #3012-style URL with "create" in path under References heading, plus comparison phrasing.
  const urlAllows = [
    {
      name: '#3012-style URL under References and related work',
      title: 'Give each PDD repository a reusable way to verify its app',
      body: 'Update `src/runtime-seam.mjs`.\n\n## References and related work\n- https://github.com/cursor/plugins/blob/main/pstack/skills/create-verification-skill/SKILL.md',
    },
    {
      name: 'comparison phrasing (match / align with / mirror)',
      title: 'Align retry jitter with upstream pattern',
      body: 'Update `src/runtime-seam.mjs` to match https://github.com/other/repo/blob/main/create-retry.ts and align with https://github.com/other/repo/blob/main/update-backoff.ts (mirror https://github.com/other/repo/blob/main/edit.ts).',
    },
    {
      name: 'URL path contains edit verb but surrounding prose has none',
      title: 'Improve verification skill docs',
      body: 'Update `src/metrics-model.mjs`.\nBackground link: https://github.com/cursor/plugins/blob/main/skills/create-verification-skill/SKILL.md',
    },
  ];
  for (const sample of urlAllows) {
    const res = classifyPreflightIssue({
      repository: 'promptdriven/pdd',
      issue: { number: 802, title: sample.title, body: sample.body, comments: [] },
      repoFiles,
    });
    assert.equal(res.decision, 'allow', `Item 2 (${sample.name}) must stay allow (got ${res.decision}/${res.reasonCode}: ${res.reason})`);
  }

  // Item 3: non-repo title prefixes and Service: a/b stay allow; sibling / same-org prefixes and Repo: other-org/pdd still reject.
  for (const sample of [
    { title: '[autopilot/intake] improve status line', body: 'Update `src/metrics-model.mjs`.' },
    { title: 'codex/claude: rotate logins cleanly', body: 'Update `src/login-pool.mjs`.' },
    { title: '[macOS/Linux] normalize cache paths', body: 'Update `src/runtime-seam.mjs`.' },
    { title: 'Fix daemon restart behavior', body: 'Service: systemd/launchd\nUpdate `src/runtime-seam.mjs`.' },
  ]) {
    const res = classifyPreflightIssue({
      repository: 'promptdriven/pdd',
      issue: { number: 803, title: sample.title, body: sample.body, comments: [] },
      repoFiles,
    });
    assert.equal(res.decision, 'allow', `Item 3 (${sample.title}) must stay allow (got ${res.decision}/${res.reasonCode})`);
  }
  const sameOrgTitleReject = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: { number: 804, title: '[promptdriven/pdd_cloud] fix billing retry', body: 'Retry webhook handler.' },
    repoFiles,
  });
  assert.equal(sameOrgTitleReject.decision, 'reject');
  assert.equal(sameOrgTitleReject.reasonCode, 'cross_repo');
  const serviceSameOrgReject = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: { number: 805, title: 'Fix gateway timeout', body: 'Service: promptdriven/pdd_cloud\nFix gateway.' },
    repoFiles,
  });
  assert.equal(serviceSameOrgReject.decision, 'reject');
  assert.equal(serviceSameOrgReject.reasonCode, 'cross_repo');

  // Item 4: local pairs mentioning a sibling passively stay allow; foreign-bound pairs still reject.
  for (const body of [
    'Rotate accounts across codex and claude when prompt-runtime returns 502.',
    'Update accounts-cli alongside login-pool to handle pdd_cloud 503 responses.',
  ]) {
    const res = classifyPreflightIssue({
      repository: 'promptdriven/pdd',
      issue: { number: 806, title: 'Improve retry rotation', body, comments: [] },
      repoFiles,
    });
    assert.equal(res.decision, 'allow', `Item 4 passive pair must stay allow: ${body}`);
  }
  const boundAlongsideReject = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: { number: 807, title: 'Ship paired gateway update', body: 'Update `src/accounts-cli.mjs` alongside `pdd_cloud`.', comments: [] },
    repoFiles,
    siblingRepos: ['pdd_cloud'],
  });
  assert.equal(boundAlongsideReject.decision, 'reject');
  assert.equal(boundAlongsideReject.reasonCode, 'cross_repo');
  assert.equal(boundAlongsideReject.targetRepo, 'pdd_cloud');

  // Item 5: unit-test/validation/rejection guards, NAMED_RECIPE_RE punctuation/backticks, COMMENT_LOCAL_AUTH_RE, and Acceptance Criteria heading.
  for (const body of [
    'Add a unit test verifying production credentials parsing.',
    'Test that auth rejects expired production tokens with exit code 4.',
    'Validate config returns an error when production API keys are missing.',
    'Verify package.json metadata before live npm publish.',
  ]) {
    const res = classifyPreflightIssue({
      repository: 'promptdriven/pdd',
      issue: { number: 808, title: 'Harden token validation', body, comments: [] },
      repoFiles,
    });
    assert.equal(res.decision, 'allow', `Item 5 guard must stay allow: ${body}`);
  }
  const recipePeriodAllow = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: { number: 809, title: 'Run recipe with trailing period', body: 'Verification recipe: stripe-staging-e2e.', comments: [] },
    repoFiles,
    workerCapabilities: { localTests: true, availableRecipes: ['stripe-staging-e2e'] },
  });
  assert.equal(recipePeriodAllow.decision, 'allow', 'trailing period stripped so available recipe matches');
  const recipeBacktickPark = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: { number: 810, title: 'Run backticked recipe', body: 'Verification recipe: `stripe-staging-e2e`', comments: [] },
    repoFiles,
    workerCapabilities: { localTests: true, availableRecipes: [] },
  });
  assert.equal(recipeBacktickPark.decision, 'park', 'backticked missing recipe after colon+space still parks');
  assert.equal(recipeBacktickPark.reasonCode, 'unverifiable_boundary');
  assert.match(recipeBacktickPark.reason, /stripe-staging-e2e/);

  const androidInsteadPark = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 811,
      title: 'Verify mobile UI',
      body: 'Acceptance criteria: manual human QA sign-off on a physical iPhone device.',
      comments: [{ author: 'serhan', trusted: true, body: 'Test on Android instead of iPhone.' }],
    },
    repoFiles,
  });
  assert.equal(androidInsteadPark.decision, 'park', '"instead of iPhone" must not authorize local verification');
  const notAcceptablePark = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 812,
      title: 'Verify live checkout',
      body: 'Acceptance criteria: trigger a real $1 live Stripe checkout charge in production with maintainer 2FA credentials.',
      comments: [{ author: 'serhan', trusted: true, body: 'Skipping real charge is not acceptable.' }],
    },
    repoFiles,
  });
  assert.equal(notAcceptablePark.decision, 'park', '"not acceptable" must not authorize local verification');
  const sectionHeadingPark = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 813,
      title: 'Live Stripe verification',
      body: '## Acceptance Criteria\n- Real $1 live Stripe checkout charge in production with maintainer 2FA credentials.',
      comments: [],
    },
    repoFiles,
  });
  assert.equal(sectionHeadingPark.decision, 'park', 'bullets under ## Acceptance Criteria inherit verification framing');
  assert.equal(sectionHeadingPark.reasonCode, 'unverifiable_boundary');

  // Item 6: deferrals and bare full/overview/use comments stay parked; explicit choice answers resolve.
  for (const reply of [
    'Not decided yet — sharing the full overview so we can use it in the meeting.',
    'Still undecided on pricing tiers.',
    'Here is the full overview for context.',
  ]) {
    const res = classifyPreflightIssue({
      repository: 'promptdriven/pdd',
      issue: {
        number: 814,
        title: 'Choose Pro pricing',
        body: 'Pricing decision: should Pro tier charge $19/seat or $29/seat?',
        comments: [{ author: 'serhan', trusted: true, body: reply }],
      },
      repoFiles,
    });
    assert.equal(res.decision, 'park', `Item 6 non-decision comment must keep park: ${reply}`);
  }
  const explicitByDefault = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 815,
      title: 'Choose default metrics view',
      body: 'Open question: should `pdd metrics` default to overview or full?',
      comments: [{ author: 'serhan', trusted: true, body: 'Overview by default.' }],
    },
    repoFiles,
  });
  assert.equal(explicitByDefault.decision, 'allow', '"Overview by default." resolves human_decision');

  // Item 7: nested directory sentinels ("extensions/github_pdd_app/.") are recognized as owned locally.
  const nestedSentinel = classifyPreflightIssue({
    repository: 'promptdriven/pdd_cloud',
    issue: {
      number: 816,
      title: 'Fix webhook signature check',
      body: 'Update `extensions/github_pdd_app/webhook.ts` to validate signatures.',
      comments: [],
    },
    repoFiles: ['extensions/github_pdd_app/.', 'packages/runtime-client/.'],
  });
  assert.equal(nestedSentinel.decision, 'allow', 'nested sentinel dir marks extensions/github_pdd_app as local');

  // Item 8 minor: activeIntake recognizes CORE_QUESTION_MARKER_PREFIX and does not re-park on timeline fetch error.
  const hCoreMarker = makeIntakeHarness(t, { mode: 'active' });
  const rowCoreQ = {
    number: 817,
    title: 'Choose Pro pricing',
    body: 'Pricing decision: should Pro tier charge $19/seat or $29/seat?',
    labels: [],
    assignees: [],
    comments: 1,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T01:00:00Z',
  };
  hCoreMarker.commentsByIssue.set(817, [{
    id: 1,
    body: 'Autopilot needs a decision:\n\n> Should Pro tier charge $19/seat or $29/seat?\n\n<!-- pdd:autopilot-core:question:817:job-1 -->',
    user: { login: 'autopilot-bot' },
    created_at: '2026-11-18T11:00:00Z',
  }]);
  hCoreMarker.timelineByIssue.set(817, [
    { event: 'unlabeled', label: { name: 'pdd:needs-decision' }, actor: { login: 'serhan' }, created_at: '2026-11-18T11:30:00Z' },
  ]);
  await activeIntake(hCoreMarker.ctx, [rowCoreQ]);
  assert.deepEqual(hCoreMarker.startedJobs.map(j => j.issue), [817], 'activeIntake honors trusted label removal after CORE_QUESTION_MARKER_PREFIX');

  const hTimelineErr = makeIntakeHarness(t, { mode: 'active' });
  const origAll = hTimelineErr.ctx.gh.all;
  hTimelineErr.ctx.gh.all = async endpoint => {
    if (endpoint.includes('/timeline')) throw new Error('HTTP 502 reading timeline');
    return origAll(endpoint);
  };
  const rowTimelineErr = {
    number: 818,
    title: 'Choose Pro pricing',
    body: 'Pricing decision: should Pro tier charge $19/seat or $29/seat?',
    labels: [],
    assignees: [],
    comments: 1,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T01:00:00Z',
  };
  hTimelineErr.commentsByIssue.set(818, [{
    id: 1,
    body: `Autopilot parked:\n- Question: Should Pro tier charge $19/seat or $29/seat?\n${PREFLIGHT_MARKER_PREFIX}818:abc -->`,
    user: { login: 'autopilot-bot' },
    created_at: '2026-11-18T11:00:00Z',
  }]);
  await activeIntake(hTimelineErr.ctx, [rowTimelineErr]);
  assert.equal(hTimelineErr.writes.length, 0, 'timeline read error propagates and warns instead of re-parking');
  assert.ok(hTimelineErr.warnings.some(w => w.includes('#818') && w.includes('timeline')));
});

test('3534 R3 regressions (section resets, heading self-match, polish)', () => {
  const repoFiles = ['src/metrics-model.mjs', 'src/accounts-cli.mjs', 'src/login-pool.mjs', 'src/runtime-seam.mjs', 'package.json'];

  // Item 1a: trailing ## Acceptance Criteria in body must not leak into later trusted comments.
  const noVerifyLeak = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 901,
      title: 'Fix status formatting',
      body: 'Update `src/metrics-model.mjs`.\n\n## Acceptance Criteria\n- Local unit tests pass.',
      comments: [
        { author: 'maintainer', trusted: true, body: 'FYI I rotated our production API keys today unrelated to this.' },
      ],
    },
    repoFiles,
  });
  assert.equal(noVerifyLeak.decision, 'allow', 'body ## Acceptance Criteria must not leak into unrelated comment');

  const commentOwnVerifySection = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 902,
      title: 'Fix status formatting',
      body: 'Update `src/metrics-model.mjs`.\n\n## Acceptance Criteria\n- Local unit tests pass.',
      comments: [
        { author: 'maintainer', trusted: true, body: '## Verification\n- Must test with production API keys before merge.' },
      ],
    },
    repoFiles,
  });
  assert.equal(commentOwnVerifySection.decision, 'park', 'explicit ## Verification section inside comment still parks');
  assert.equal(commentOwnVerifySection.reasonCode, 'unverifiable_boundary');

  // Item 1b: trailing ## References in body must not leak into later trusted comments,
  // and nested ### subheadings under ## References stay inside reference mode until an equal-or-higher heading.
  const commentAfterRefSection = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 903,
      title: 'Sync local skill parser',
      body: 'Update `src/runtime-seam.mjs`.\n\n## References\n- https://github.com/cursor/plugins/blob/main/skills/create-verification-skill/SKILL.md',
      comments: [
        { author: 'maintainer', trusted: true, body: 'Also edit https://github.com/promptdriven/pdd_cloud/blob/main/src/worker.ts to match.' },
      ],
    },
    repoFiles,
  });
  assert.equal(commentAfterRefSection.decision, 'reject', 'body ## References must not suppress edit URL in later comment');
  assert.equal(commentAfterRefSection.reasonCode, 'cross_repo');
  assert.equal(commentAfterRefSection.targetRepo, 'promptdriven/pdd_cloud');

  const nestedRefSubheading = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 904,
      title: 'Add local verification skill helper',
      body: [
        'Update `src/runtime-seam.mjs`.',
        '',
        '## References',
        '### Cursor plugin',
        '- https://github.com/cursor/plugins/blob/main/pstack/skills/create-verification-skill/SKILL.md',
      ].join('\n'),
      comments: [],
    },
    repoFiles,
  });
  assert.equal(nestedRefSubheading.decision, 'allow', 'nested ### subheading under ## References stays in reference section');

  const exitRefOnEqualHeading = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 905,
      title: 'Add local verification skill helper',
      body: [
        'Update `src/runtime-seam.mjs`.',
        '',
        '## References',
        '### Cursor plugin',
        '- https://github.com/cursor/plugins/blob/main/pstack/skills/create-verification-skill/SKILL.md',
        '',
        '## Implementation',
        '- Update https://github.com/promptdriven/pdd_cloud/blob/main/src/worker.ts',
      ].join('\n'),
      comments: [],
    },
    repoFiles,
  });
  assert.equal(exitRefOnEqualHeading.decision, 'reject', 'equal-level ## Implementation exits ## References');
  assert.equal(exitRefOnEqualHeading.reasonCode, 'cross_repo');
  assert.equal(exitRefOnEqualHeading.targetRepo, 'promptdriven/pdd_cloud');

  // Item 2: IMPL_HEADING_RE must not self-match matched sibling/slug tokens (e.g. runtime-client -> client).
  const runtimeClientHeading = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 906,
      title: 'Tune retry backoff',
      body: '## How pdd uses runtime-client\nAdjust retry delay in `src/runtime-seam.mjs`.',
      comments: [],
    },
    repoFiles,
  });
  assert.equal(runtimeClientHeading.decision, 'allow', 'runtime-client in heading must not self-match IMPL_HEADING_RE "client"');

  const slugSelfMatchHeading = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 907,
      title: 'Tune request timeout',
      body: '## How pdd calls promptdriven/api-gateway\nAdjust timeout in `src/runtime-seam.mjs`.',
      comments: [],
    },
    repoFiles,
  });
  assert.equal(slugSelfMatchHeading.decision, 'allow', 'same-org slug token must not self-match IMPL_HEADING_RE "api"/"gateway"');

  const runtimeClientUpdateHeading = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 908,
      title: 'Add new retry header',
      body: '## Update runtime-client\nExpose the new header alongside `src/runtime-seam.mjs`.',
      comments: [],
    },
    repoFiles,
    siblingRepos: ['runtime-client', 'pdd_cloud'],
  });
  assert.equal(runtimeClientUpdateHeading.decision, 'reject', 'explicit Update heading for runtime-client still rejects');
  assert.equal(runtimeClientUpdateHeading.reasonCode, 'cross_repo');
  assert.equal(runtimeClientUpdateHeading.targetRepo, 'runtime-client');

  // Item 3a: ALONGSIDE_PAIR_RE allows optional article (the/a/an) before either capture group.
  const alongsideArticleRight = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 909,
      title: 'Sync account quota response',
      body: 'Update `src/accounts-cli.mjs` alongside the `pdd_cloud` server.',
      comments: [],
    },
    repoFiles,
    siblingRepos: ['runtime-client', 'pdd_cloud'],
  });
  assert.equal(alongsideArticleRight.decision, 'reject', 'ALONGSIDE_PAIR_RE binds sibling after "the"');
  assert.equal(alongsideArticleRight.reasonCode, 'cross_repo');
  assert.equal(alongsideArticleRight.targetRepo, 'pdd_cloud');

  const alongsideArticleLeft = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 910,
      title: 'Sync account quota response',
      body: 'Update the `pdd_cloud` server alongside `src/accounts-cli.mjs`.',
      comments: [],
    },
    repoFiles,
    siblingRepos: ['runtime-client', 'pdd_cloud'],
  });
  assert.equal(alongsideArticleLeft.decision, 'reject', 'ALONGSIDE_PAIR_RE binds sibling after leading "the"');
  assert.equal(alongsideArticleLeft.reasonCode, 'cross_repo');
  assert.equal(alongsideArticleLeft.targetRepo, 'pdd_cloud');

  // Item 3b: resolveLocalBoundaryOverride ignores question comments ending in "?".
  const questionDoesNotOverride = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 911,
      title: 'Add Stripe webhook validation',
      body: 'Update `src/accounts-cli.mjs`. Verification requires testing against live Stripe checkout.',
      comments: [
        { author: 'maintainer', trusted: true, body: 'Are local mocks sufficient here?' },
      ],
    },
    repoFiles,
  });
  assert.equal(questionDoesNotOverride.decision, 'park', 'question comment ending in ? must not authorize local override');
  assert.equal(questionDoesNotOverride.reasonCode, 'unverifiable_boundary');

  const affirmativeOverrides = classifyPreflightIssue({
    repository: 'promptdriven/pdd',
    issue: {
      number: 912,
      title: 'Add Stripe webhook validation',
      body: 'Update `src/accounts-cli.mjs`. Verification requires testing against live Stripe checkout.',
      comments: [
        { author: 'maintainer', trusted: true, body: 'Are local mocks sufficient here?' },
        { author: 'maintainer', trusted: true, body: 'Yes, local mocks are sufficient here.' },
      ],
    },
    repoFiles,
  });
  assert.equal(affirmativeOverrides.decision, 'allow', 'affirmative local mock authorization still unlocks boundary');
});

test('P0-11: repo-agnostic siblingRepos, unclear_or_unsound preflight class, minIntakeConfidence floor, and mandatory commentWhyDeclined (active vs shadow)', async t => {
  // 1. Zero hardcoded org/repo assumptions: bare names without siblingRepos do not trigger cross_repo routing.
  for (const bareRepoName of ['pdd_cloud', 'prompt-runtime', 'runtime-client', 'pdd-workflow']) {
    const noHardcodedSibling = classifyPreflightIssue({
      repository: 'acme/web-app',
      issue: { number: 1000, title: `Mention ${bareRepoName} in docs`, body: `Update \`src/app.tsx\` to document ${bareRepoName} integration.` },
      repoFiles: ['src/app.tsx'],
      siblingRepos: [],
    });
    assert.equal(noHardcodedSibling.decision, 'allow', `bare mention of ${bareRepoName} must not trigger hardcoded cross_repo`);
  }

  // Configurable siblingRepos works across arbitrary Web/API/Mobile/Go/Python repos.
  const siblings = normalizeSiblingRepos(['acme/mobile-ios', { canonical: 'billing-api', aliases: ['billing_api'] }]);
  assert.equal(siblings.length, 2);
  const mobileCross = classifyPreflightIssue({
    repository: 'acme/web-app',
    issue: { number: 1001, title: '[billing_api] Add retry header', body: 'Update `billing-api/cmd/server/main.go`.' },
    repoFiles: ['src/app.tsx', 'pkg/http/client.go'],
    siblingRepos: siblings,
  });
  assert.equal(mobileCross.decision, 'reject');
  assert.equal(mobileCross.reasonCode, 'cross_repo');
  assert.equal(mobileCross.targetRepo, 'billing-api');

  // 2. unclear_or_unsound mechanical preflight class.
  assert.ok(PREFLIGHT_REASON_CODES.includes('unclear_or_unsound'));
  const emptyStub = classifyPreflightIssue({
    repository: 'acme/api',
    issue: { number: 1002, title: 'Fix bug', body: 'TBD' },
    repoFiles: ['pkg/server/handler.go'],
  });
  assert.equal(emptyStub.decision, 'park');
  assert.equal(emptyStub.reasonCode, 'unclear_or_unsound');
  assert.equal(emptyStub.label, 'pdd:needs-decision');
  assert.ok(emptyStub.signals.includes('empty_or_stub_issue'));

  const draftIssue = classifyPreflightIssue({
    repository: 'acme/api',
    issue: { number: 1003, title: '[WIP] Refactor auth middleware', body: 'Drafting notes for auth middleware.' },
    repoFiles: ['pkg/auth/middleware.go'],
  });
  assert.equal(draftIssue.decision, 'park');
  assert.equal(draftIssue.reasonCode, 'unclear_or_unsound');
  assert.ok(draftIssue.signals.includes('explicit_draft_or_needs_repro'));

  const missingEditTarget = classifyPreflightIssue({
    repository: 'acme/api',
    issue: { number: 1004, title: 'Fix handler timeout', body: 'Modify `pkg/server/ghost_handler.go` to return 504.' },
    repoFiles: ['pkg/server/handler.go'],
  });
  assert.equal(missingEditTarget.decision, 'park');
  assert.equal(missingEditTarget.reasonCode, 'unclear_or_unsound');
  assert.ok(missingEditTarget.signals.includes('missing_target_paths'));

  // Greenfield creation stays allow.
  const greenfieldCreate = classifyPreflightIssue({
    repository: 'acme/api',
    issue: { number: 1005, title: 'Add timeout handler', body: 'Create `pkg/server/timeout_handler.go` returning 504.' },
    repoFiles: ['pkg/server/handler.go'],
  });
  assert.equal(greenfieldCreate.decision, 'allow');

  // Precision rollup includes unclear_or_unsound.
  const rollup = summarizeIntakeFilterPrecision({
    skips: [{ repo: 'acme/api', issue: 1002, reasonCode: 'unclear_or_unsound' }],
    runs: [],
  });
  assert.equal(rollup.byReasonCode.unclear_or_unsound, 1);
  assert.match(rollup.skipSummary, /1 unclear_or_unsound/);

  // 3. Skeptical prompts: improvePrompt removes "Vagueness alone" rule and exposes unclear_or_unsound.
  const sampleRow = { number: 1006, title: 'Fix parser', body: 'Parser fails on edge case.' };
  const impText = improvePrompt({ repo: 'acme/api', row: sampleRow, comments: [], card: { reason: 'unclear' }, pool: [] });
  assert.doesNotMatch(impText, /Vagueness alone is never a reason/i);
  assert.match(impText, /unclear_or_unsound/);
  const cardText = cardPrompt({ repo: 'acme/api', row: sampleRow, comments: [], pool: [] });
  assert.match(cardText, /unclear_or_unsound/);
  assert.doesNotMatch(cardText, /pdd_cloud|pdd-workflow/i);

  // 4. minIntakeConfidence floor (default 0.75) + mandatory marker-deduped commentWhyDeclined across ALL declined classes.
  assert.equal(DEFAULT_MIN_INTAKE_CONFIDENCE, 0.75);
  const h = makeIntakeHarness(t, { mode: 'active', repo: 'acme/api' });
  const f = intakeFolders(h.root);
  for (const d of [f.base, f.cards, f.jobs, f.logs, f.empty]) mkdirSync(d, { recursive: true });

  const makeRow = (n, title = `Issue ${n}`) => ({
    number: n,
    title,
    body: `Detailed report for issue ${n} in src/accounts-cli.mjs.`,
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: `2026-11-18T0${n % 9}:00:00Z`,
  });

  const rows = [
    makeRow(1101, 'Low confidence ready card'),
    makeRow(1102, 'Duplicate issue'),
    makeRow(1103, 'Blocked issue'),
    makeRow(1104, 'Already fixed issue'),
    makeRow(1105, 'Held issue'),
    makeRow(1106, 'High confidence ready card'),
  ];

  // Seed finished intake card jobs for collectActiveIntake.
  const seedJob = (row, payload) => {
    const answerPath = join(f.logs, `intake-${row.number}.answer.txt`);
    const exitPath = join(f.logs, `intake-${row.number}.exit.json`);
    writeFileSync(answerPath, JSON.stringify(payload));
    writeFileSync(exitPath, JSON.stringify({ code: 0 }));
    writeFileSync(join(f.jobs, `${row.number}.json`), JSON.stringify({
      issue: row.number,
      stage: 'card',
      version: issueVersion(row),
      startedAt: h.ctx.now() - 1000,
      agent: { kind: 'codex', model: 'gpt-test' },
      job: { id: `intake-${row.number}`, exit: exitPath, log: answerPath },
      answer: answerPath,
    }));
  };
  h.ctx.jobs.read = job => ({ state: 'exited', exit: JSON.parse(readFileSync(job.exit, 'utf8')), result: null });

  seedJob(rows[0], { class: 'ready', reason: 'Might be this file.', confidence: 0.55, areas: ['src/accounts-cli.mjs'] });
  seedJob(rows[1], { class: 'duplicate', canonical: 1106, reason: 'Duplicate of #1106.', confidence: 0.95 });
  seedJob(rows[2], { class: 'blocked', suggested_links: [{ to: 1106, type: 'blocked-by', reason: 'depends on #1106' }], reason: 'Blocked by #1106.', confidence: 0.9 });
  seedJob(rows[3], { class: 'fixed', reason: 'Comments confirm fix already shipped.', confidence: 0.92 });
  seedJob(rows[4], { class: 'held', reason: 'Maintainer is already working on it.', confidence: 0.9 });
  seedJob(rows[5], { class: 'ready', reason: 'Clear scoped fix in src/accounts-cli.mjs.', confidence: 0.88, areas: ['src/accounts-cli.mjs'] });

  await collectActiveIntake(h.ctx, rows);

  // Only #1106 passes the 0.75 confidence floor!
  const readyMap = activeReadyCards(h.root, rows, fs);
  assert.deepEqual([...readyMap.keys()], [1106], 'only >= 0.75 ready card survives confidence floor');

  // Every declined class (#1101 low-confidence -> person/unclear_or_unsound, #1102 duplicate, #1103 blocked, #1104 fixed, #1105 held) received a marker-deduped explanation comment!
  for (const [issueNum, expectedClass] of [[1101, 'person'], [1102, 'duplicate'], [1103, 'blocked'], [1104, 'fixed'], [1105, 'held']]) {
    const comments = h.commentsByIssue.get(issueNum) ?? [];
    assert.equal(comments.length, 1, `issue #${issueNum} (${expectedClass}) received exactly one declined comment`);
    assert.ok(comments[0].body.includes(`${DECLINED_MARKER_PREFIX}${issueNum}:${expectedClass}:`), `issue #${issueNum} comment carries dedup marker`);
  }
  assert.equal((h.commentsByIssue.get(1106) ?? []).length, 0, 'accepted ready issue #1106 gets no declined comment');
  assert.equal(h.labelsByIssue.get(1101)?.has('pdd:needs-decision'), true, 'low-confidence demoted issue receives pdd:needs-decision');

  // Calling commentWhyDeclined again for the same body produces ZERO duplicate comments.
  const deduped = await commentWhyDeclined(h.ctx, rows[1], { class: 'duplicate', canonical: 1106, reason: 'Duplicate of #1106.' }, { mode: 'active' });
  assert.equal(deduped.commented, false, 'marker deduplication prevents duplicate declined comments');
  assert.equal((h.commentsByIssue.get(1102) ?? []).length, 1);

  // Shadow mode makes ZERO GitHub writes on commentWhyDeclined!
  const hShadow = makeIntakeHarness(t, { mode: 'shadow', repo: 'acme/api' });
  const shadowRes = await commentWhyDeclined(hShadow.ctx, rows[1], { class: 'duplicate', canonical: 1106, reason: 'Duplicate of #1106.' }, { mode: 'shadow' });
  assert.equal(shadowRes.commented, false);
  assert.equal(hShadow.writes.length, 0, 'zero GitHub writes in shadow mode');

  // wouldPick enforces minConfidence floor too, and cardPrompt interpolates the effective minConfidence.
  const cards = new Map([
    [1101, { issue: 1101, version: issueVersion(rows[0]), card: { class: 'ready', confidence: 0.6, reason: 'low' } }],
    [1106, { issue: 1106, version: issueVersion(rows[5]), card: { class: 'ready', confidence: 0.85, reason: 'high' } }],
  ]);
  assert.deepEqual(wouldPick([rows[0], rows[5]], cards), [1106]);
  assert.deepEqual(wouldPick([rows[0], rows[5]], cards, { minConfidence: 0.5 }), [1106, 1101]);

  const defaultPrompt = cardPrompt({ repo: 'acme/api', row: rows[5], comments: [], pool: [], mode: 'active' });
  assert.match(defaultPrompt, /confidence >= 0\.75/);
  const customPrompt = cardPrompt({ repo: 'acme/api', row: rows[5], comments: [], pool: [], mode: 'active', minConfidence: 0.85 });
  assert.match(customPrompt, /confidence >= 0\.85/);
  assert.doesNotMatch(customPrompt, /confidence >= 0\.75/);
});

test('P0-11 review fix: transient GitHub write failure during collectActiveIntake persists declineCommentPending and retries on next activeIntake tick without re-running LLM', async t => {
  const h = makeIntakeHarness(t, { mode: 'active', repo: 'acme/api', repoFiles: ['src/accounts-cli.mjs'] });
  const f = intakeFolders(h.root);
  for (const dir of [f.base, f.cards, f.jobs, f.logs, f.empty]) mkdirSync(dir, { recursive: true });

  const row = {
    number: 1201,
    state: 'open',
    title: 'Unclear low-confidence issue',
    body: 'Update `src/accounts-cli.mjs` behavior.',
    labels: [],
    assignees: [],
    comments: 0,
    user: { login: 'maintainer' },
    created_at: '2026-11-18T01:00:00Z',
  };

  // Seed a finished low-confidence card job.
  const answerPath = join(f.logs, 'intake-1201.answer.txt');
  const exitPath = join(f.logs, 'intake-1201.exit.json');
  writeFileSync(answerPath, JSON.stringify({ class: 'ready', reason: 'Uncertain scope.', confidence: 0.5, areas: ['src/accounts-cli.mjs'] }));
  writeFileSync(exitPath, JSON.stringify({ code: 0 }));
  writeFileSync(join(f.jobs, '1201.json'), JSON.stringify({
    issue: 1201,
    stage: 'card',
    version: issueVersion(row),
    startedAt: h.ctx.now() - 1000,
    agent: { kind: 'codex', model: 'gpt-test' },
    job: { id: 'intake-1201', exit: exitPath, log: answerPath },
    answer: answerPath,
  }));
  h.ctx.jobs.read = job => ({ state: 'exited', exit: JSON.parse(readFileSync(job.exit, 'utf8')), result: null });

  let llmStarts = 0;
  h.ctx.jobs.start = (...args) => { llmStarts++; return { id: `unexpected-${llmStarts}`, exit: exitPath, log: answerPath }; };

  // Tick 1: fail the comment POST transiently.
  const origOk = h.ctx.gh.ok;
  const origCall = h.ctx.gh.call;
  let failComments = true;
  let failLabels = false;
  h.ctx.gh.call = async (method, path, body) => {
    if (failLabels && method === 'POST' && path.endsWith('/labels')) return { status: 503, body: 'Service Unavailable' };
    return origCall(method, path, body);
  };
  h.ctx.gh.ok = async (method, path, body) => {
    if (failComments && method === 'POST' && path.endsWith('/comments')) throw new Error('502 Bad Gateway');
    if (failLabels && method === 'POST' && path.endsWith('/labels')) throw new Error('503 Service Unavailable');
    return origOk(method, path, body);
  };

  const readSavedCard = () => JSON.parse(readFileSync(join(f.cards, '1201.json'), 'utf8'));

  await collectActiveIntake(h.ctx, [row]);
  const savedAfterFail = readSavedCard();
  assert.equal(savedAfterFail?.declineCommentPending, true, 'declineCommentPending persisted when GH write fails');
  assert.equal((h.commentsByIssue.get(1201) ?? []).length, 0, 'no comment posted on failed attempt');
  assert.equal(activeReadyCards(h.root, [row], fs).size, 0, 'declined issue is never claimable');

  // Tick 2: comment succeeds, label fails transiently -> stays pending without duplicating comment later.
  failComments = false;
  failLabels = true;
  await activeIntake(h.ctx, [row]);
  assert.equal(llmStarts, 0, 'retry must not spawn a new LLM card job');
  assert.equal((h.commentsByIssue.get(1201) ?? []).length, 1, 'decline comment posted on retry');
  const savedAfterPartial = readSavedCard();
  assert.equal(savedAfterPartial?.declineCommentPending, true, 'stays pending while label write is still incomplete');

  // Tick 3: label write recovers -> label applied, ZERO duplicate comment, declineCommentPending cleared!
  failLabels = false;
  await activeIntake(h.ctx, [row]);
  assert.equal(llmStarts, 0, 'completion tick must not spawn a new LLM card job');
  assert.equal((h.commentsByIssue.get(1201) ?? []).length, 1, 'marker deduplication prevents duplicate comment on label retry');
  assert.equal(h.labelsByIssue.get(1201)?.has('pdd:needs-decision'), true, 'pdd:needs-decision label applied on retry');
  const savedAfterSuccess = readSavedCard();
  assert.equal(savedAfterSuccess?.declineCommentPending, undefined, 'declineCommentPending cleared once applied');
});
