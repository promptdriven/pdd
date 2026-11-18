import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { checkInput, interfaceBlocks } from '../src/runtime-seam.mjs';
import {
  AUTOPILOT_ZERO_EDIT_TARGET,
  DEFAULT_DAILY_REPORT_LIMIT,
  DEFAULT_RUNTIME_REPORT_REPOSITORY,
  REPORT_REPOSITORY,
  autoFileValidatedReports,
  classifyNonDefect,
  fileReport,
  listReportDrafts,
  reportMarker,
  sendReportDraft,
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
    if (method === 'PATCH' && /\/issues\/\d+$/.test(endpoint)) {
      const [, repo, num] = /^repos\/([^/]+\/[^/]+)\/issues\/(\d+)$/.exec(endpoint);
      const payload = JSON.parse(options.input ?? '{}');
      writes.push({ method, endpoint, payload });
      const found = issues.find(item => item.repo === repo && item.number === Number(num));
      if (!found) return reply(404, { message: 'Not Found' });
      if (payload.state) {
        found.state = payload.state;
        if (payload.state === 'open') {
          found.state_reason = 'reopened';
          found.closed_at = null;
        }
      }
      return reply(200, { number: found.number, id: found.id, state: found.state });
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

test('Drafted noise reports preserve detail text and operatorStop so autoFileValidatedReports filters them under Rule 1', async t => {
  const root = tempDir(t, 'pdd-draft-rule1-');
  const gh = createFakeReportGithub();

  const draftedNoise = [
    {
      kind: 'pdd',
      component: 'agent',
      code: 'cli-error',
      text: 'Model request failed: quota exceeded for current billing period',
      command: 'pdd workflow run bug',
      reproduced: true,
    },
    {
      kind: 'pdd',
      component: 'pdd-workflow',
      code: 'cli-error',
      text: 'API returned 401 unauthorized: token expired',
      command: 'pdd workflow run feature',
      reproduced: true,
    },
    {
      kind: 'runtime',
      component: 'pdd-test',
      code: 'no-verdict',
      detail: 'Transport read ECONNRESET while awaiting stream',
      command: 'pdd test prompts/cli/example.prompt.md',
      reproduced: true,
    },
    {
      kind: 'pdd',
      component: 'autopilot-core',
      code: 'crash',
      text: 'Worker exited unexpectedly',
      operatorStop: true,
      command: 'pdd autopilot',
      reproduced: true,
    },
  ];

  for (const cause of draftedNoise) {
    const res = await fileReport(
      { cause, mode: 'draft', root, machine: 'vm-draft', versions: VERSIONS, step: 'verify' },
      gh.ports,
    );
    assert.equal(res.state, 'draft');
  }

  assert.equal(listReportDrafts({ root }).length, 4);

  const batch = await autoFileValidatedReports(
    { root, machine: 'vm-draft', runtimeRepo: DEFAULT_RUNTIME_REPORT_REPOSITORY },
    gh.ports,
  );
  assert.equal(batch.filed.length, 0);
  assert.equal(gh.writes.length, 0);
  assert.equal(gh.issues.length, 0);
  assert.equal(batch.filtered.length, 4);
  assert.deepEqual(
    batch.filtered.map(r => r.reason).sort(),
    ['auth-expiry', 'operator-stop', 'quota-or-credit', 'transient-network-blip'],
  );
});

test('Closed matching issue (even >14d old) is reopened with scrubbed forensic summary instead of filing a duplicate (#3182)', async t => {
  const root = tempDir(t);
  const now = Date.parse('2026-11-16T18:00:00Z');
  const fake = createFakeReportGithub({
    seededIssues: [
      {
        number: 520,
        id: 9520,
        repo: REPORT_REPOSITORY,
        state: 'closed',
        state_reason: 'completed',
        closed_at: '2026-07-01T00:00:00Z', // closed > 130 days ago
        title: 'Autopilot report: PDD autopilot-core post-merge-reopen (PDD 0.1)',
        body: [
          'Autopilot detected a post-merge regression on a previously merged change (reopened issue, reverted merge, or post-merge CI failure).',
          '',
          '- Kind: pdd',
          '- Component: autopilot-core',
          '- Error code: post-merge-reopen',
          '- Step: post-merge',
          '- Versions: PDD 0.1.15, Node v22.0.0, linux, agent codex',
          '- Seen on this machine: 1',
          '',
          reportMarker('pdd.autopilot-core.post-merge-reopen.0.1'),
        ].join('\n'),
        labels: ['pdd:autopilot-report'],
      },
    ],
  });

  const reopenedRes = await fileReport(
    {
      cause: {
        kind: 'pdd',
        component: 'autopilot-core',
        code: 'post-merge-reopen',
        reproduced: true,
        issues: [42, 43],
        heads: ['a'.repeat(40)],
        command: 'TOKEN=secret_abc123 pdd autopilot --repo acme/private-app https://internal.acme.test/hook',
        text: 'Private customer text for acme/private-app issue #42',
        detail: 'SECRET_KEY=topsecret /Users/bob/acme/private-app/src/secret.js',
      },
      mode: 'validated',
      root,
      machine: 'vm-1',
      versions: { ...VERSIONS, pdd: '0.2.0' },
      step: 'post-merge',
      words: ['acme/private-app', 'acme', 'private-app'],
    },
    { gh: fake.gh, now: () => now },
  );

  assert.equal(reopenedRes.state, 'reopened');
  assert.equal(reopenedRes.number, 520);
  assert.equal(reopenedRes.ref, `${REPORT_REPOSITORY}#520`);
  assert.equal(fake.issues.length, 1, 'never opened a duplicate GitHub issue');
  assert.equal(fake.issues[0].state, 'open', 'reopened the existing closed issue');
  assert.equal(fake.writes.filter(w => w.method === 'PATCH').length, 1);
  assert.equal(fake.comments.length, 1, 'appended the scrubbed forensic summary comment');
  assert.match(fake.comments[0].body, /Reopened automatically because this cause occurred again/);
  assert.match(fake.comments[0].body, /- Error code: post-merge-reopen/);
  assert.match(fake.comments[0].body, /- Proof: reproduced, 2 issues/);
  assert.match(fake.comments[0].body, /- Command: TOKEN=\[redacted\] pdd autopilot --repo \[repository\] \[url\]/i);
  assert.doesNotMatch(fake.comments[0].body, /secret_abc123|topsecret|private-app|acme|\/Users\/bob|Private customer/);

  // Immediate repeat on the now-open issue within 24h is counted without extra comments or PATCH calls.
  const repeatRes = await fileReport(
    {
      cause: { kind: 'pdd', component: 'autopilot-core', code: 'post-merge-reopen', reproduced: true, step: 'post-merge' },
      mode: 'validated',
      root,
      machine: 'vm-1',
      versions: { ...VERSIONS, pdd: '0.2.0' },
      step: 'post-merge',
    },
    { gh: fake.gh, now: () => now + 60_000 },
  );
  assert.equal(repeatRes.state, 'counted');
  assert.equal(fake.comments.length, 1);

  assert.deepEqual(AUTOPILOT_ZERO_EDIT_TARGET, { min: 0.9, max: 0.95, label: '90-95%' });
  const summary = summarizeConversionDrops({
    date: '2026-11-16',
    openIssuesCount: 50,
    backlogCount: 20,
    claimableCount: 15,
    claimedCount: 10,
    clearSpecCount: 8,
    prOpenedCount: 6,
    zeroEditCount: 4,
    mergedOrWouldMergeCount: 5,
    reopenedCount: 0,
    filed: [reopenedRes],
  });
  assert.deepEqual(summary.funnel, {
    openIssues: 50,
    taken: 10,
    openToTaken: { numerator: 10, denominator: 50, rate: 0.2 },
    zeroEditMergedOrWouldMerge: 4,
    zeroEditRate: { numerator: 4, denominator: 10, rate: 0.4 },
    zeroEditTarget: { min: 0.9, max: 0.95, label: '90-95%' },
    mergedOrWouldMerge: 5,
    takenToMergedOrWouldMerge: { numerator: 5, denominator: 10, rate: 0.5 },
    reopened: 0,
    reopenRate: { numerator: 0, denominator: 5, rate: 0 },
    reopenTarget: 0,
  });
  assert.equal(summary.reports.verifiedIssues.length, 1);
  assert.equal(summary.reports.verifiedIssues[0].state, 'reopened');
});


test('If reopening a closed report succeeds (PATCH 200) and comment POST fails (HTTP 500), retry still posts the full reopened forensic summary instead of Seen again (#3182)', async t => {
  const root = tempDir(t);
  const now = Date.parse('2026-11-16T19:00:00Z');
  const fake = createFakeReportGithub({
    seededIssues: [
      {
        number: 530,
        id: 9530,
        repo: REPORT_REPOSITORY,
        state: 'closed',
        state_reason: 'completed',
        closed_at: '2026-10-01T00:00:00Z',
        title: 'Autopilot report: PDD autopilot-core post-merge-revert (PDD 0.1)',
        body: [
          'Autopilot detected a post-merge regression on a previously merged change (reopened issue, reverted merge, or post-merge CI failure).',
          '',
          '- Kind: pdd',
          '- Component: autopilot-core',
          '- Error code: post-merge-revert',
          '- Step: post-merge',
          '- Versions: PDD 0.1.20, Node v22.0.0, linux, agent codex',
          '- Seen on this machine: 1',
          '',
          reportMarker('pdd.autopilot-core.post-merge-revert.0.1'),
        ].join('\n'),
        labels: ['pdd:autopilot-report'],
      },
    ],
  });

  let failCommentOnce = true;
  const wrappedGh = async (args, opts) => {
    const methodIdx = args.indexOf('--method');
    const method = methodIdx >= 0 ? args[methodIdx + 1] : 'GET';
    const endpoint = args[args.length - (args.includes('--input') ? 3 : 1)];
    if (failCommentOnce && method === 'POST' && endpoint.endsWith('/issues/530/comments')) {
      failCommentOnce = false;
      return { code: 1, stdout: 'HTTP/2 500 Internal Server Error\r\n\r\n{"message":"transient"}', stderr: 'gh: HTTP 500' };
    }
    return fake.gh(args, opts);
  };

  // Attempt 1: PATCH reopens #530, POST /comments fails with 500 -> kept as local draft!
  const first = await fileReport(
    {
      cause: {
        kind: 'pdd',
        component: 'autopilot-core',
        code: 'post-merge-revert',
        reproduced: true,
        issues: [77],
        command: 'API_SECRET=xyz pdd autopilot',
      },
      mode: 'validated',
      root,
      machine: 'vm-1',
      versions: { ...VERSIONS, pdd: '0.2.0' },
      step: 'post-merge',
    },
    { gh: wrappedGh, now: () => now },
  );
  assert.equal(first.state, 'draft', 'failed comment POST keeps draft locally');
  assert.equal(fake.issues[0].state, 'open', 'issue #530 is already open on GitHub');
  assert.equal(fake.comments.length, 0);
  assert.equal(listReportDrafts({ root }).length, 1);

  // Attempt 2 (retry via sendReportDraft): sees #530 open + pendingReopen in ledger -> posts full forensic summary, NOT Seen again!
  const retry = await sendReportDraft({ root, fingerprint: first.fingerprint, machine: 'vm-1' }, { gh: wrappedGh, now: () => now + 5000 });
  assert.equal(retry.exitCode, 0);
  assert.equal(retry.state, 'reopened');
  assert.equal(listReportDrafts({ root }).length, 0, 'retained draft deleted only after forensic summary succeeded');
  assert.equal(fake.comments.length, 1);
  assert.match(fake.comments[0].body, /Reopened automatically because this cause occurred again/);
  assert.match(fake.comments[0].body, /- Error code: post-merge-revert/);
  assert.match(fake.comments[0].body, /- Proof: reproduced/);
  assert.doesNotMatch(fake.comments[0].body, /Seen again|xyz/);
});
