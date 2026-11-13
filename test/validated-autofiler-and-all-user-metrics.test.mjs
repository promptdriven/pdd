import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { checkInput, interfaceBlocks } from '../src/runtime-seam.mjs';
import {
  DEFAULT_DAILY_REPORT_LIMIT,
  DEFAULT_RUNTIME_REPORT_REPOSITORY,
  REPORT_REPOSITORY,
  autoFileValidatedReports,
  classifyNonDefect,
  fileReport,
  listReportDrafts,
  reportMarker,
  summarizeConversionDrops,
  validateReportDraft,
} from '../src/autopilot-reports.mjs';

const DAY = 24 * 60 * 60 * 1000;
const VERSIONS = { pdd: '0.1.28', node: 'v22.23.2', platform: 'darwin', agent: 'codex' };

function tempDir(t, prefix = 'pdd-pr4b-') {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function createFakeReportGithub({ readableRepos = new Set([REPORT_REPOSITORY, DEFAULT_RUNTIME_REPORT_REPOSITORY]), seededIssues = [] } = {}) {
  const issues = seededIssues.map((row, idx) => ({
    id: row.id ?? 9000 + idx,
    number: row.number ?? 400 + idx,
    repo: row.repo ?? REPORT_REPOSITORY,
    state: row.state ?? 'open',
    state_reason: row.state_reason ?? null,
    closed_at: row.closed_at ?? null,
    title: row.title ?? '',
    body: row.body ?? '',
    labels: row.labels ?? [],
    assignees: row.assignees ?? [],
  }));
  const comments = [];
  const writes = [];
  let nextNumber = 600;

  const reply = (status, value) => ({
    code: 0,
    stdout: `HTTP/1.1 ${status} OK\r\n\r\n${value === undefined ? '' : JSON.stringify(value)}`,
    stderr: '',
  });

  const gh = async (args, options = {}) => {
    const method = args[args.indexOf('--method') + 1];
    const endpoint = args.find(arg => arg.startsWith('repos/'));
    if (method === 'GET' && /^repos\/[^/]+\/[^/]+$/.test(endpoint)) {
      const repo = endpoint.slice(6);
      return readableRepos.has(repo) ? reply(200, { full_name: repo }) : reply(404, { message: 'Not Found' });
    }
    if (method === 'GET' && endpoint.includes('/issues?')) {
      const repo = /^repos\/([^/]+\/[^/]+)\/issues\?/.exec(endpoint)[1];
      const labelMatch = /labels=([^&]+)/.exec(endpoint);
      const wantedLabel = labelMatch ? decodeURIComponent(labelMatch[1]) : null;
      const matching = issues.filter(item => {
        if (item.repo !== repo) return false;
        if (!wantedLabel) return true;
        return item.labels.some(l => (typeof l === 'string' ? l : l?.name) === wantedLabel);
      });
      return reply(200, matching);
    }
    if (method === 'POST' && /\/issues\/\d+\/comments$/.test(endpoint)) {
      const [, repo, num] = /^repos\/([^/]+\/[^/]+)\/issues\/(\d+)\/comments$/.exec(endpoint);
      const payload = JSON.parse(options.input ?? '{}');
      writes.push({ method, endpoint, payload });
      comments.push({ repo, number: Number(num), body: payload.body });
      return reply(201, { id: 7000 + comments.length, body: payload.body });
    }
    if (method === 'POST' && endpoint.endsWith('/issues')) {
      const repo = /^repos\/([^/]+\/[^/]+)\/issues$/.exec(endpoint)[1];
      const payload = JSON.parse(options.input ?? '{}');
      const created = {
        id: 8000 + issues.length + 1,
        number: ++nextNumber,
        repo,
        state: 'open',
        state_reason: null,
        closed_at: null,
        title: payload.title,
        body: payload.body,
        labels: payload.labels ?? [],
        assignees: payload.assignees ?? [],
      };
      writes.push({ method, endpoint, payload });
      issues.push(created);
      return reply(201, { number: created.number, id: created.id });
    }
    return reply(404, {});
  };

  return { gh, issues, comments, writes };
}

test('Rule 1: quota, auth expiry, operator stop, maintenance, transient network blips, and content/not-run causes are filtered and never auto-filed', async t => {
  const root = tempDir(t);
  const fake = createFakeReportGithub();

  const nonDefectCases = [
    { kind: 'pdd', component: 'agent', code: 'quota', text: 'Account out of quota', expectedCategory: 'quota_or_service' },
    { kind: 'pdd', component: 'agent', code: 'rate-limit', text: '429 rate limit exceeded', expectedCategory: 'quota_or_service' },
    { kind: 'pdd', component: 'agent', code: 'billing', text: 'credit balance exhausted', expectedCategory: 'quota_or_service' },
    { kind: 'pdd', component: 'pdd', code: 'token-expired', text: '401 Unauthorized', expectedCategory: 'auth' },
    { kind: 'pdd', component: 'pdd', code: 'login', text: 'please log in again', expectedCategory: 'auth' },
    { kind: 'pdd', component: 'autopilot-core', code: 'operator-stop', text: 'stopped by operator', expectedCategory: 'operator' },
    { kind: 'pdd', component: 'autopilot-core', code: 'cancelled', text: 'user cancelled job', expectedCategory: 'operator' },
    { kind: 'runtime', component: 'pdd test', code: 'maintenance', text: 'Runtime is in maintenance', expectedCategory: 'maintenance' },
    { kind: 'runtime', component: 'pdd test', code: 'capacity', text: 'provider overloaded', expectedCategory: 'maintenance' },
    { kind: 'runtime', component: 'pdd test', code: 'econnreset', text: 'read ECONNRESET', expectedCategory: 'network_blip' },
    { kind: 'pdd', component: 'pdd', code: 'etimedout', text: 'connect ETIMEDOUT', expectedCategory: 'network_blip' },
    { kind: 'runtime', component: 'pdd test', code: 'no-story', text: 'No Story covers this module', expectedCategory: 'content' },
    { kind: 'pdd', component: 'pdd test', code: 'not-run', text: 'Allowed not-run path', expectedCategory: 'content' },
    { kind: 'pdd', component: 'pdd lint', code: 'unchecked-criteria', text: 'Story criterion unchecked', expectedCategory: 'content' },
    { kind: 'pdd', component: 'pdd lint', code: 'story-criterion-mismatch', text: 'Mismatch in Story', expectedCategory: 'content' },
  ];

  for (const entry of nonDefectCases) {
    assert.ok(classifyNonDefect(entry), `classifyNonDefect detects ${entry.code}`);
    const res = await fileReport(
      {
        cause: { ...entry, reproduced: true, count: 5, command: 'pdd test' },
        mode: 'validated',
        root,
        machine: 'm1',
        versions: VERSIONS,
        step: 'build',
      },
      { gh: fake.gh, now: () => 1000 },
    );
    assert.equal(res.state, 'filtered', `expected ${entry.code} to be filtered`);
    assert.equal(res.category, entry.expectedCategory);
    assert.match(res.fingerprint, /^(?:pdd|runtime)\./, 'fingerprint is always returned even when filtered');
  }

  assert.equal(fake.writes.length, 0, 'zero GitHub writes for non-defect / noise causes');
  assert.equal(listReportDrafts({ root }).length, 0, 'filtered noise does not queue validated auto-file issues');
});

test('Rule 2: verified owner routing, scrubbed command/proof fields, single-occurrence draft hold, daily cap, and not_planned/invalid needs-person guard', async t => {
  const root = tempDir(t);
  const fake = createFakeReportGithub({
    seededIssues: [
      {
        number: 410,
        id: 9410,
        repo: REPORT_REPOSITORY,
        state: 'closed',
        state_reason: 'not_planned',
        closed_at: new Date(0).toISOString(),
        title: 'Autopilot report: PDD pdd timeout (PDD 0.1)',
        body: `- Kind: pdd\n- Component: pdd\n- Error code: timeout\n\n${reportMarker('pdd.pdd.timeout.0.1')}`,
        labels: ['pdd:autopilot-report'],
      },
      {
        number: 411,
        id: 9411,
        repo: REPORT_REPOSITORY,
        state: 'closed',
        state_reason: 'completed',
        closed_at: new Date(0).toISOString(),
        title: 'Autopilot report: PDD pdd-lint lint-refusal (PDD 0.1)',
        body: `- Kind: pdd\n- Component: pdd-lint\n- Error code: lint-refusal\n\n${reportMarker('pdd.pdd-lint.lint-refusal.0.1')}`,
        labels: ['pdd:autopilot-report', 'invalid'],
      },
    ],
  });

  const secretCommand = 'API_KEY=super-secret-xyz pdd test /Users/alice/acme/secret-repo/prompts/billing.prompt.md --token ghp_1234567890abcdefghijklmnopqrstuvwx --url https://internal.acme.example/v1';
  const words = ['acme/secret-repo', 'acme', 'secret-repo'];

  // 1) Unverified single-occurrence Runtime defect stays local draft (0 GitHub writes).
  const firstRuntime = await fileReport(
    {
      cause: {
        kind: 'runtime',
        component: 'pdd test',
        code: 'interpreter-error',
        issue: 21,
        head: 'a'.repeat(40),
        command: secretCommand,
        batchId: 'batch_20261113_01',
        reportId: 'https://secret.acme.example/unsafe-id',
        detail: ` Secret token ghp_1234567890abcdefghijklmnopqrstuvwx at /Users/alice/acme/secret-repo/src/private.js `,
      },
      mode: 'validated',
      root,
      machine: 'm1',
      versions: VERSIONS,
      step: 'check',
      words,
    },
    { gh: fake.gh, now: () => 10_000 },
  );
  assert.equal(firstRuntime.state, 'draft');
  assert.equal(firstRuntime.reason, 'unverified-single-occurrence');
  assert.equal(fake.writes.length, 0);

  // Vague unknown code without step or command never passes proof validation even if count >= 2.
  const vagueVerdict = validateReportDraft({
    fingerprint: 'pdd.other.other-deadbeef.0.1',
    kind: 'pdd',
    component: 'other',
    code: 'other-deadbeef',
    step: 'unknown',
    count: 3,
    versions: VERSIONS,
  });
  assert.equal(vagueVerdict.ok, false);
  assert.equal(vagueVerdict.reason, 'missing-concrete-proof');

  // 2) Second occurrence across another issue/head satisfies proof and routes Runtime defect to promptdriven/prompt-runtime!
  const secondRuntime = await fileReport(
    {
      cause: {
        kind: 'runtime',
        component: 'pdd test',
        code: 'interpreter-error',
        issue: 22,
        head: 'b'.repeat(40),
        command: secretCommand,
        batchId: 'batch_20261113_01',
      },
      mode: 'validated',
      root,
      machine: 'm1',
      versions: VERSIONS,
      step: 'check',
      words,
    },
    { gh: fake.gh, now: () => 20_000 },
  );
  assert.equal(secondRuntime.state, 'filed');
  assert.equal(secondRuntime.ref, `${DEFAULT_RUNTIME_REPORT_REPOSITORY}#601`);
  const runtimeIssue = fake.issues.find(i => i.number === 601);
  assert.equal(runtimeIssue.repo, DEFAULT_RUNTIME_REPORT_REPOSITORY);
  assert.deepEqual(runtimeIssue.labels, ['pdd:runtime']);
  assert.match(runtimeIssue.body, /- Command: \[REDACTED\] pdd test \[path\] --token \[REDACTED\] --url \[url\]/);
  assert.match(runtimeIssue.body, /- Runtime batch: batch_20261113_01/);
  assert.doesNotMatch(runtimeIssue.body, /Runtime report:/, 'unsafe URL reportId is omitted');
  assert.match(runtimeIssue.body, /- Proof: 2 issues, 2 heads/);
  assert.doesNotMatch(runtimeIssue.body, /super-secret-xyz|ghp_|\/Users\/alice|acme|secret-repo|private\.js/);

  // 3) Fallback when configured/default Runtime repo is unreachable -> files safely to promptdriven/pdd.
  const fallbackRoot = tempDir(t);
  const pddOnlyFake = createFakeReportGithub({ readableRepos: new Set([REPORT_REPOSITORY]) });
  const fallbackFiled = await fileReport(
    {
      cause: { kind: 'runtime', component: 'pdd test', code: 'server-internal', reproduced: true, command: 'pdd test' },
      mode: 'validated',
      root: fallbackRoot,
      machine: 'm1',
      versions: VERSIONS,
      step: 'check',
    },
    { gh: pddOnlyFake.gh, now: () => 25_000 },
  );
  assert.equal(fallbackFiled.state, 'filed');
  assert.equal(fallbackFiled.ref, `${REPORT_REPOSITORY}#601`);

  // 4) Closed as not_planned or labeled invalid -> returns needs-person instead of filing/re-opening!
  for (const [code, expectedNumber] of [['timeout', 410], ['lint-refusal', 411]]) {
    const rejected = await fileReport(
      {
        cause: { kind: 'pdd', component: code === 'timeout' ? 'pdd' : 'pdd lint', code, reproduced: true, command: 'pdd workflow run' },
        mode: 'validated',
        root,
        machine: 'm1',
        versions: VERSIONS,
        step: 'build',
      },
      { gh: fake.gh, now: () => 30_000 },
    );
    assert.equal(rejected.state, 'needs-person');
    assert.equal(rejected.number, expectedNumber);
  }

  // 5) PDD defects route to promptdriven/pdd and respect DEFAULT_DAILY_REPORT_LIMIT = 3 per 24h.
  assert.equal(DEFAULT_DAILY_REPORT_LIMIT, 3);
  const pddCodes = ['crash', 'suite-broken', 'merge-check-tool'];
  const states = [];
  for (const code of pddCodes) {
    const res = await fileReport(
      {
        cause: { kind: 'pdd', component: 'autopilot-core', code, reproduced: true, command: 'pdd autopilot' },
        mode: 'validated',
        root,
        machine: 'm1',
        versions: VERSIONS,
        step: 'merge',
      },
      { gh: fake.gh, now: () => 40_000 },
    );
    states.push(res);
  }
  // 1 runtime issue (#601) + 2 pdd issues (#602, #603) = 3 new issues today; the 4th ('merge-check-tool') stays draft!
  assert.equal(states[0].state, 'filed');
  assert.equal(states[0].ref, `${REPORT_REPOSITORY}#602`);
  assert.equal(states[1].state, 'filed');
  assert.equal(states[1].ref, `${REPORT_REPOSITORY}#603`);
  assert.equal(states[2].state, 'draft');
  assert.equal(states[2].reason, 'daily-cap');

  // Next day (> 24h later), autoFileValidatedReports sends the queued merge-check-tool draft while keeping needs-person drafts untouched.
  const batch = await autoFileValidatedReports({ root, machine: 'm1' }, { gh: fake.gh, now: () => 40_000 + DAY + 1000 });
  assert.equal(batch.filed.length, 1);
  assert.equal(batch.filed[0].ref, `${REPORT_REPOSITORY}#604`);
  assert.equal(batch.needsPerson.length, 2);
});

test('Rule 3: live duplicate check matches existing open issue by marker or (kind, component, code) across versions and comments once per version/day', async t => {
  const root = tempDir(t);
  const fake = createFakeReportGithub({
    seededIssues: [
      {
        number: 512,
        id: 9512,
        repo: DEFAULT_RUNTIME_REPORT_REPOSITORY,
        state: 'open',
        title: 'Autopilot report: Runtime pdd-test no-verdict (PDD 0.1)',
        body: [
          'Autopilot ended one job because of a Runtime problem. The job did not wait for a fix.',
          '',
          '- Kind: runtime',
          '- Component: pdd-test',
          '- Error code: no-verdict',
          '- Step: check',
          '- Versions: PDD 0.1.20, Node v22.0.0, linux, agent codex',
          '- Seen on this machine: 2',
          '',
          reportMarker('runtime.pdd-test.no-verdict.0.1'),
        ].join('\n'),
        labels: ['pdd:runtime'],
      },
    ],
  });

  const sendForVersion = (pddVersion, now) => fileReport(
    {
      cause: { kind: 'runtime', component: 'pdd test', code: 'no-verdict', reproduced: true, command: 'pdd test' },
      mode: 'validated',
      root,
      machine: 'm1',
      versions: { ...VERSIONS, pdd: pddVersion },
      step: 'check',
    },
    { gh: fake.gh, now: () => now },
  );

  // Version 0.1.28 matches open 0.1.20 issue -> comments once ('seen'), second call same day is 'counted'.
  const v01First = await sendForVersion('0.1.28', 1_000);
  assert.equal(v01First.state, 'seen');
  assert.equal(v01First.ref, `${DEFAULT_RUNTIME_REPORT_REPOSITORY}#512`);

  const v01Repeat = await sendForVersion('0.1.28', 2_000);
  assert.equal(v01Repeat.state, 'counted');
  assert.equal(v01Repeat.ref, `${DEFAULT_RUNTIME_REPORT_REPOSITORY}#512`);

  // Version 0.2.0 (different minor fingerprint runtime.pdd-test.no-verdict.0.2!) STILL matches open #512 across versions -> no duplicate issue!
  const v02First = await sendForVersion('0.2.0', 3_000);
  assert.equal(v02First.state, 'seen');
  assert.equal(v02First.ref, `${DEFAULT_RUNTIME_REPORT_REPOSITORY}#512`);

  const v02Repeat = await sendForVersion('0.2.0', 4_000);
  assert.equal(v02Repeat.state, 'counted');

  assert.equal(fake.issues.length, 1, 'never opened a duplicate issue across versions');
  assert.equal(fake.comments.length, 2, 'at most one Seen again comment per version per day');
  assert.match(fake.comments[0].body, /PDD 0\.1\.28/);
  assert.match(fake.comments[1].body, /PDD 0\.2\.0/);
});

test('summarizeConversionDrops computes exact 4-stage conversion funnel rates, grouped root-cause drops, and verified vs filtered report lists (#3361)', () => {
  const summary = summarizeConversionDrops({
    date: '2026-11-13',
    backlogCount: 10,
    claimableCount: 8,
    runs: [
      { issue: 1, pr: 101, merged: true },
      { issue: 2, pr: 102, wouldMerge: true },
      { issue: 3, clearSpec: false, outcome: 'question', reason: 'unclear-spec' },
      { issue: 4, clearSpec: false, cause: { kind: 'runtime', component: 'pdd test', code: 'no-story' } },
      { issue: 5, clearSpec: true, prOpened: false, cause: { kind: 'pdd', component: 'agent', code: 'quota' } },
      { issue: 6, clearSpec: true, prOpened: false, operatorStop: true, reason: 'operator-stop' },
      { issue: 7, clearSpec: true, pr: 107, cause: { kind: 'runtime', component: 'pdd test', code: 'interpreter-error' } },
      { issue: 8, clearSpec: true, pr: 108, cause: { kind: 'pdd', component: 'autopilot-core', code: 'crash' } },
    ],
    filed: [
      { fingerprint: 'runtime.pdd-test.interpreter-error.0.1', state: 'filed', ref: 'promptdriven/prompt-runtime#601', number: 601, kind: 'runtime', component: 'pdd-test', code: 'interpreter-error' },
      { fingerprint: 'pdd.autopilot-core.crash.0.1', state: 'seen', ref: 'promptdriven/pdd#502', number: 502, kind: 'pdd', component: 'autopilot-core', code: 'crash' },
    ],
    drafts: [
      { fingerprint: 'pdd.pdd.timeout.0.1', status: 'needs-person', statusReason: 'closed-not-planned', kind: 'pdd', component: 'pdd', code: 'timeout', count: 2 },
      { fingerprint: 'pdd.agent.quota.0.1', kind: 'pdd', component: 'agent', code: 'quota', rawCode: 'quota', count: 1 },
    ],
    filtered: [
      { fingerprint: 'pdd.pdd-test.other-12345678.0.1', state: 'filtered', reason: 'no-story', category: 'content', owner: 'content', rawCode: 'no-story' },
    ],
  });

  assert.equal(summary.date, '2026-11-13');
  assert.deepEqual(summary.stages, {
    backlogToClaimable: { numerator: 8, denominator: 10, rate: 0.8 },
    claimedToClearSpec: { numerator: 6, denominator: 8, rate: 0.75 },
    clearSpecToPrOpened: { numerator: 4, denominator: 6, rate: 0.6667 },
    prOpenedToMergedOrWouldMerge: { numerator: 2, denominator: 4, rate: 0.5 },
  });
  assert.equal(summary.totals.dropped, 6);
  assert.deepEqual(summary.dropsByOwner.pdd, { count: 1, causes: { crash: 1 }, issues: [8] });
  assert.deepEqual(summary.dropsByOwner.runtime, { count: 1, causes: { 'interpreter-error': 1 }, issues: [7] });
  assert.deepEqual(summary.dropsByOwner.content, { count: 1, causes: { 'no-story': 1 }, issues: [4] });
  assert.deepEqual(summary.dropsByOwner.quota_or_service, { count: 1, causes: { quota: 1 }, issues: [5] });
  assert.deepEqual(summary.dropsByOwner.operator, { count: 1, causes: { 'operator-stop': 1 }, issues: [6] });
  assert.deepEqual(summary.dropsByOwner.person_decision, { count: 1, causes: { 'unclear-spec': 1 }, issues: [3] });

  assert.equal(summary.reports.verifiedIssues.length, 2);
  assert.equal(summary.reports.pendingDrafts.length, 1);
  assert.equal(summary.reports.pendingDrafts[0].state, 'needs-person');
  assert.equal(summary.reports.filteredNoise.length, 2);
});

test('All-user GitHub receipt discovery in pdd metrics reconstructs issues, PRs, skills, done/applies checks, merges, and would-merge with an empty .git/pdd directory (#3250)', t => {
  const root = tempDir(t, 'pdd-metrics-all-users-');
  const repoDir = join(root, 'repo');
  const binDir = join(root, 'bin');
  mkdirSync(repoDir, { recursive: true });
  mkdirSync(binDir, { recursive: true });

  execFileSync('git', ['init', '-q', repoDir]);
  execFileSync('git', ['-C', repoDir, 'remote', 'add', 'origin', 'https://github.com/acme/shared-product.git']);
  writeFileSync(join(repoDir, 'pdd.json'), JSON.stringify({ autopilot: { trust: ['pdd-vm'] } }, null, 2));

  // Confirm .git/pdd does not exist at all before running pdd metrics.
  assert.equal(existsSync(join(repoDir, '.git', 'pdd')), false);

  const sha = ch => ch.repeat(40);
  const ghFixture = {
    openIssues: [
      { number: 11 },
      { number: 12 },
    ],
    allIssues: [
      {
        number: 10,
        state: 'closed',
        html_url: 'https://github.com/acme/shared-product/issues/10',
        labels: [{ name: 'small-change' }],
        comments: 0,
        created_at: '2026-11-12T09:00:00Z',
        updated_at: '2026-11-12T10:30:00Z',
      },
      {
        number: 11,
        state: 'open',
        html_url: 'https://github.com/acme/shared-product/issues/11',
        labels: [{ name: 'pdd:would-merge' }, { name: 'bug' }],
        comments: 0,
        created_at: '2026-11-12T11:00:00Z',
        updated_at: '2026-11-12T12:00:00Z',
      },
      {
        number: 12,
        state: 'open',
        html_url: 'https://github.com/acme/shared-product/issues/12',
        labels: [{ name: 'pdd:needs-decision' }, { name: 'pdd:bug' }],
        comments: 1,
        created_at: '2026-11-12T13:00:00Z',
        updated_at: '2026-11-12T13:15:00Z',
      },
      {
        number: 13,
        state: 'closed',
        html_url: 'https://github.com/acme/shared-product/issues/13',
        labels: [{ name: 'feature' }],
        comments: 0,
        created_at: '2026-11-12T14:00:00Z',
        updated_at: '2026-11-12T16:00:00Z',
      },
      {
        number: 14,
        state: 'closed',
        html_url: 'https://github.com/acme/shared-product/issues/14',
        labels: [{ name: 'pdd:no-behavior-change' }],
        comments: 0,
        created_at: '2026-11-12T17:00:00Z',
        updated_at: '2026-11-12T17:30:00Z',
      },
    ],
    pulls: [
      {
        number: 101,
        state: 'closed',
        merged_at: '2026-11-12T10:30:00Z',
        created_at: '2026-11-12T09:30:00Z',
        updated_at: '2026-11-12T10:30:00Z',
        html_url: 'https://github.com/acme/shared-product/pull/101',
        author_association: 'COLLABORATOR',
        user: { login: 'greg' },
        head: { sha: sha('1'), ref: 'pdd/small-change-10' },
        title: 'Fix config default for #10',
        body: [
          'Prompt tests: 1 of 1 Stories pass.',
          'Code replay: PASS — 4 checks.',
          'Formal check: not needed (no Rules to check in the Story).',
          '',
          'Closes #10',
          '',
          'Made with `pdd workflow run small-change`.',
        ].join('\n'),
        labels: [],
      },
      {
        number: 102,
        state: 'open',
        merged_at: null,
        created_at: '2026-11-12T11:20:00Z',
        updated_at: '2026-11-12T12:00:00Z',
        html_url: 'https://github.com/acme/shared-product/pull/102',
        author_association: 'NONE',
        user: { login: 'pdd-vm' },
        head: { sha: sha('2'), ref: 'pdd/core-11-fix' },
        title: 'Repair null crash on #11',
        body: 'Closes #11\n\nSkill: bug',
        labels: [{ name: 'pdd:would-merge' }],
      },
      {
        number: 103,
        state: 'closed',
        merged_at: '2026-11-12T14:45:00Z',
        created_at: '2026-11-12T14:15:00Z',
        updated_at: '2026-11-12T14:45:00Z',
        html_url: 'https://github.com/acme/shared-product/pull/103',
        author_association: 'MEMBER',
        user: { login: 'sam' },
        head: { sha: sha('3'), ref: 'pdd/13-prompt' },
        title: 'Story and prompt for #13',
        body: 'Part of #13\n\nMade with `pdd workflow run feature`.',
        labels: [],
      },
      {
        number: 104,
        state: 'closed',
        merged_at: '2026-11-12T16:00:00Z',
        created_at: '2026-11-12T15:10:00Z',
        updated_at: '2026-11-12T16:00:00Z',
        html_url: 'https://github.com/acme/shared-product/pull/104',
        author_association: 'MEMBER',
        user: { login: 'sam' },
        head: { sha: sha('4'), ref: 'pdd/13-code' },
        title: 'Implement #13',
        body: [
          'PR 2 of this run: the code. It builds on PR 1: https://github.com/acme/shared-product/pull/103.',
          'Closes #13',
          'Made with `pdd workflow run feature`.',
          '```json',
          JSON.stringify({
            skill: 'feature',
            checks: {
              runtime: { done: true, applies: true },
              vectors: { done: true, applies: true },
              formal: { done: false, applies: true },
            },
          }),
          '```',
        ].join('\n'),
        labels: [],
      },
      {
        number: 105,
        state: 'closed',
        merged_at: '2026-11-12T17:30:00Z',
        created_at: '2026-11-12T17:05:00Z',
        updated_at: '2026-11-12T17:30:00Z',
        html_url: 'https://github.com/acme/shared-product/pull/105',
        author_association: 'OWNER',
        user: { login: 'dana' },
        head: { sha: sha('5'), ref: 'pdd/core-14-docs' },
        title: 'Clarify README wording (#14)',
        body: [
          'Closes #14',
          'Path: b',
          'Runtime: no line (no prompt changed)',
          "Replay and formal tests (Autopilot's run): none changed",
        ].join('\n'),
        labels: [{ name: 'pdd:no-behavior-change' }],
      },
      {
        // Untrusted unmerged stranger PR must be ignored!
        number: 999,
        state: 'open',
        merged_at: null,
        created_at: '2026-11-12T18:00:00Z',
        updated_at: '2026-11-12T18:00:00Z',
        html_url: 'https://github.com/acme/shared-product/pull/999',
        author_association: 'NONE',
        user: { login: 'stranger' },
        head: { sha: sha('9'), ref: 'forged-branch' },
        title: 'Forged PR',
        body: 'Closes #99\nMade with `pdd workflow run feature`.',
        labels: [{ name: 'pdd:would-merge' }],
      },
    ],
    commentsByThread: {
      12: [
        {
          id: 5012,
          author_association: 'OWNER',
          user: { login: 'dana' },
          created_at: '2026-11-12T13:15:00Z',
          html_url: 'https://github.com/acme/shared-product/issues/12#issuecomment-5012',
          body: 'Need product decision on edge case.\n\nSkill: bug\n<!-- pdd:autopilot-core:question:12:abc -->',
        },
      ],
      102: [
        {
          id: 5102,
          author_association: 'NONE',
          user: { login: 'pdd-vm' },
          created_at: '2026-11-12T12:00:00Z',
          html_url: 'https://github.com/acme/shared-product/pull/102#issuecomment-5102',
          body: [
            'Observe mode passed merge check.',
            'Runtime: PASS',
            'Evidence: vectors=pass formal=proved',
            `<!-- pdd:autopilot-core:would-merge:${sha('2')} -->`,
          ].join('\n'),
        },
      ],
    },
    permissions: {
      greg: 'write',
      sam: 'write',
      stranger: 'read',
    },
  };

  const fixturePath = join(root, 'gh-fixture.json');
  writeFileSync(fixturePath, JSON.stringify(ghFixture));

  const mockGhScript = `#!/usr/bin/env node
const fs = require('node:fs');
const data = JSON.parse(fs.readFileSync(process.env.GH_FIXTURE_FILE, 'utf8'));
const args = process.argv.slice(2);
const endpoint = args.find(a => a.startsWith('repos/')) || '';

if (endpoint.includes('/issues?state=open')) {
  process.stdout.write(data.openIssues.map(x => JSON.stringify(x)).join('\\n') + '\\n');
} else if (endpoint.includes('/pulls?state=all')) {
  process.stdout.write(JSON.stringify(data.pulls));
} else if (endpoint.includes('/issues?state=all')) {
  process.stdout.write(JSON.stringify(data.allIssues));
} else if (/\\/collaborators\\/([^/]+)\\/permission$/.test(endpoint)) {
  const login = /\\/collaborators\\/([^/]+)\\/permission$/.exec(endpoint)[1];
  process.stdout.write(JSON.stringify({ permission: data.permissions[login] || 'read' }));
} else if (/\\/pulls\\/(\\d+)\\/files/.test(endpoint)) {
  process.stdout.write('src/app.mjs\\n');
} else if (/\\/pulls\\/(\\d+)$/.test(endpoint)) {
  const num = Number(/\\/pulls\\/(\\d+)$/.exec(endpoint)[1]);
  const pr = data.pulls.find(p => p.number === num);
  if (!pr) process.exit(1);
  process.stdout.write(JSON.stringify(pr));
} else if (/\\/issues\\/(\\d+)\\/comments/.test(endpoint)) {
  const num = Number(/\\/issues\\/(\\d+)\\/comments/.exec(endpoint)[1]);
  const list = data.commentsByThread[num] || [];
  process.stdout.write(list.map(c => JSON.stringify(c)).join('\\n') + (list.length ? '\\n' : ''));
} else if (endpoint.includes('/check-runs')) {
  process.stdout.write(JSON.stringify({ check_runs: [] }));
} else {
  process.exit(1);
}
`;
  writeFileSync(join(binDir, 'gh'), mockGhScript, { mode: 0o755 });

  const cli = resolve('bin/pdd.mjs');
  const env = { ...process.env, PATH: `${binDir}:${process.env.PATH}`, GH_FIXTURE_FILE: fixturePath };

  const jsonOut = execFileSync(process.execPath, [cli, 'metrics', '--json'], { cwd: repoDir, env, encoding: 'utf8' });
  const report = JSON.parse(jsonOut);

  // Untrusted stranger #99 was ignored; issues 10, 11, 12, 13, 14 across greg, pdd-vm, dana, sam were reconstructed!
  assert.deepEqual(report.issues.map(i => i.issue), [10, 11, 12, 13, 14]);
  assert.equal(report.queue.unknown.count, 2, 'open queue still counts only open issues #11 and #12');

  // Verify small-change (#10): 1 issue, 1 merged, 0 WM, 100% conv, runtime 1/1, vectors 1/1, formal 0/0 (not needed), complete 1/1
  assert.deepEqual(report.bySkill['small-change'], {
    issues: 1,
    runs: 1,
    pr: 1,
    merged: 1,
    wouldMerge: 0,
    mergedOrWouldMerge: 1,
    conversionPct: 100,
    checks: {
      runtime: { done: 1, applies: 1, unknown: 0 },
      vectors: { done: 1, applies: 1, unknown: 0 },
      formal: { done: 0, applies: 0, unknown: 0 },
      complete: { done: 1, applies: 1, unknown: 0 },
    },
  });

  // Verify bug (#11 would-merge with all checks done + #12 needs-decision with no PR and unknown checks, not false misses!)
  assert.deepEqual(report.bySkill.bug, {
    issues: 2,
    runs: 2,
    pr: 1,
    merged: 0,
    wouldMerge: 1,
    mergedOrWouldMerge: 1,
    conversionPct: 50,
    checks: {
      runtime: { done: 1, applies: 1, unknown: 1 },
      vectors: { done: 1, applies: 1, unknown: 1 },
      formal: { done: 1, applies: 1, unknown: 1 },
      complete: { done: 1, applies: 1, unknown: 1 },
    },
  });

  // Verify feature (#13 stacked PR 1 + PR 2 counted as 1 issue & 1 run, merged, formal missed -> complete 0/1)
  assert.deepEqual(report.bySkill.feature, {
    issues: 1,
    runs: 1,
    pr: 1,
    merged: 1,
    wouldMerge: 0,
    mergedOrWouldMerge: 1,
    conversionPct: 100,
    checks: {
      runtime: { done: 1, applies: 1, unknown: 0 },
      vectors: { done: 1, applies: 1, unknown: 0 },
      formal: { done: 0, applies: 1, unknown: 0 },
      complete: { done: 0, applies: 1, unknown: 0 },
    },
  });

  // Verify no-behavior-change (#14 docs Path: b): merged, applies is 0 across all checks (never inflates denominators!)
  assert.deepEqual(report.bySkill['no-behavior-change'], {
    issues: 1,
    runs: 1,
    pr: 1,
    merged: 1,
    wouldMerge: 0,
    mergedOrWouldMerge: 1,
    conversionPct: 100,
    checks: {
      runtime: { done: 0, applies: 0, unknown: 0 },
      vectors: { done: 0, applies: 0, unknown: 0 },
      formal: { done: 0, applies: 0, unknown: 0 },
      complete: { done: 0, applies: 0, unknown: 0 },
    },
  });

  // Verify 'all' aggregates cleanly across all 5 distinct issues without double counting or denominator inflation!
  assert.deepEqual(report.bySkill.all, {
    issues: 5,
    runs: 5,
    pr: 4,
    merged: 3,
    wouldMerge: 1,
    mergedOrWouldMerge: 4,
    conversionPct: 80,
    checks: {
      runtime: { done: 3, applies: 3, unknown: 1 },
      vectors: { done: 3, applies: 3, unknown: 1 },
      formal: { done: 1, applies: 2, unknown: 1 },
      complete: { done: 2, applies: 3, unknown: 1 },
    },
  });

  // Verify terminal output renders the per-skill table and keeps existing Stage / Transition / Queue / #N lines intact!
  const textOut = execFileSync(process.execPath, [cli, 'metrics'], { cwd: repoDir, env, encoding: 'utf8' });
  assert.match(textOut, /Skill \| Issues \| M\/WM \(Conv%\) \| PR \| Runs \| Runtime \| Vectors \| Formal \| Complete/);
  assert.match(textOut, /small-change \| 1 \| 1\/0 \(100%\) \| 1 \| 1 \| 1\/1 \| 1\/1 \| 0\/0 \| 1\/1/);
  assert.match(textOut, /bug \| 2 \| 0\/1 \(50%\) \| 1 \| 2 \| 1\/1 \(\?1\) \| 1\/1 \(\?1\) \| 1\/1 \(\?1\) \| 1\/1 \(\?1\)/);
  assert.match(textOut, /feature \| 1 \| 1\/0 \(100%\) \| 1 \| 1 \| 1\/1 \| 1\/1 \| 0\/1 \| 0\/1/);
  assert.match(textOut, /no-behavior-change \| 1 \| 1\/0 \(100%\) \| 1 \| 1 \| 0\/0 \| 0\/0 \| 0\/0 \| 0\/0/);
  assert.match(textOut, /all \| 5 \| 3\/1 \(80%\) \| 4 \| 5 \| 3\/3 \(\?1\) \| 3\/3 \(\?1\) \| 1\/2 \(\?1\) \| 2\/3 \(\?1\)/);
  assert.match(textOut, /Stage delivered:/);
  assert.match(textOut, /Transition delivery:/);
  assert.match(textOut, /Queue unknown: 2/);
  assert.match(textOut, /#10:.*delivered yes/);

  // Verify --date 2026-11-12 activity mode also reconstructs all 5 issues and matches metrics-model result_schema!
  const dailyReport = JSON.parse(
    execFileSync(process.execPath, [cli, 'metrics', '--date', '2026-11-12', '--json'], { cwd: repoDir, env, encoding: 'utf8' }),
  );
  assert.deepEqual(dailyReport.issues.map(i => i.issue), [10, 11, 12, 13, 14]);
  assert.deepEqual(dailyReport.bySkill.all, report.bySkill.all);
  assert.equal(dailyReport.activity.deliveries.count, 3);

  const modelPrompt = readFileSync(new URL('../prompts/cli/metrics-model.prompt.md', import.meta.url), 'utf8');
  const modelContract = JSON.parse(interfaceBlocks(modelPrompt)[0][1]);
  const resultSchema = modelContract.entries.find(e => e.operation === 'calculateMetrics').result_schema;
  assert.deepEqual(checkInput(dailyReport, resultSchema, 0).refusals, []);
});
