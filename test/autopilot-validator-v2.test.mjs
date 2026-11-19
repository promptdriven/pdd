import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import {
  MAX_VALIDATION_REPAIRS,
  evaluateValidationOutcome,
  lintValidationCode,
  planValidationResume,
  shouldClaimWithCooldowns,
} from '../src/autopilot-validator.mjs';
import { coreStatus } from '../src/autopilot-core.mjs';
import {
  lintBoundaryMockOnlyTests,
  lintRepoProject,
  lintValidationSkips,
  loadProjectLintConfig,
} from '../src/repo-hygiene-lint.mjs';
import { coreWorld } from './helpers/core-world.mjs';

function makeTempGitRepo(t, prefix = 'pdd-validator-v2-') {
  const dir = mkdtempSync(join(tmpdir(), prefix));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  execFileSync('git', ['init', '-q', dir]);
  execFileSync('git', ['-C', dir, 'config', 'user.name', 'Test']);
  execFileSync('git', ['-C', dir, 'config', 'user.email', 'test@example.com']);
  return dir;
}

function writeFile(root, rel, content) {
  const abs = join(root, rel);
  mkdirSync(dirname(abs), { recursive: true });
  writeFileSync(abs, content);
}

function commitAll(root, msg = 'init') {
  execFileSync('git', ['-C', root, 'add', '.']);
  execFileSync('git', ['-C', root, 'commit', '-qm', msg]);
}

function writeIn(cwd, rel, text) {
  const abs = join(cwd, rel);
  mkdirSync(dirname(abs), { recursive: true });
  writeFileSync(abs, text);
}

test('Planted Trap 1: real-binding-unavailable fails closed to Bucket 2 in BOTH auto and observe modes (0 repairs, never merged or would-merge)', async (t) => {
  for (const mode of ['auto', 'observe']) {
    const story = 'user_stories/billing-sync.md';
    const w = await coreWorld(t, { settings: { mode, runs: 1 } });
    w.baseCommit(story, '# Billing\n\nSync billing.\n');
    w.issue(11, { title: 'Sync billing webhook' });
    await w.tick();
    writeIn(w.job(11, 'build').cwd, story, '# Billing\n\nSync signed billing.\n');
    writeIn(w.job(11, 'build').cwd, 'api/billing.mjs', 'export function sync() { return true; }\n');

    w.runtimeEvidence = async () => ({
      stories: [{
        story,
        pass: false,
        current: true,
        sent: false,
        at: 1000,
        reason: { code: 'real-binding-unavailable' },
        codes: ['real-binding-unavailable'],
        refusals: ['real-binding-unavailable'],
        states: ['refused'],
      }],
      storyFiles: [story],
      tests: [],
    });

    const { pr } = w.build(11, {
      body: `Fixes #11\n\nPath: d — ${story}, api/billing.mjs — unowned — no contract change — Test: done check`,
      runtime: { state: 'not-run' },
    });
    await w.tick();

    assert.equal(w.job(11, 'repair'), undefined, `${mode}: 0 repair rounds spent`);
    assert.equal(pr.state, 'open', `${mode}: PR stays open`);
    assert.equal(pr.merged, false, `${mode}: never merged`);
    assert.ok(!w.labels(11).includes('pdd:would-merge'), `${mode}: never marked would-merge`);
    assert.ok(w.labels(11).includes('pdd:needs-decision'), `${mode}: parked as needs-person`);
    assert.ok(!w.labels(11).includes('pdd:working'), `${mode}: worker slot freed immediately`);
    assert.ok(pr.comments.some((c) => /<!-- pdd:autopilot-core:auth-wait:/.test(c.body)), `${mode}: PR carries auth-wait marker`);
    const machine = JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
    assert.equal(machine.toolCooldowns?.['runtime-binding']?.active, true, `${mode}: runtime-binding on cooldown`);
  }
});

test('Planted Trap 2: mock-only unit tests without real E2E fail closed to Bucket 3 in BOTH auto and observe modes with 3-line Human Verification Card', async (t) => {
  for (const mode of ['auto', 'observe']) {
    const w = await coreWorld(t, { settings: { mode, runs: 1 } });
    w.issue(12, { title: 'Update checkout UI' });
    await w.tick();
    writeIn(w.job(12, 'build').cwd, 'web/checkout.tsx', 'export const Checkout = () => "<form/>";\n');
    const { pr } = w.build(12, {
      body: 'Fixes #12\n\nRuntime: PASS\nPath: d — web/checkout.tsx — unowned — no contract change — Test: done check',
    });
    await w.tick();
    w.review(12, 'PASS');
    w.suite(12, 0);

    await w.tick({
      validateE2e: async () => ({
        offlinePassed: true,
        offlineSummary: 'unit tests 8/8 passed',
        e2eChecks: [{
          kind: 'unit-mock',
          command: 'node --test test/checkout-unit.test.mjs',
          executed: true,
          exitCode: 0,
          passed: 8,
          failed: 0,
          skipped: 0,
        }],
        verifyCommand: 'npx playwright test tests/checkout.spec.ts',
      }),
    });

    assert.equal(w.job(12, 'repair'), undefined, `${mode}: 0 repair rounds for missing E2E`);
    assert.equal(pr.state, 'open', `${mode}: PR stays open`);
    assert.equal(pr.merged, false, `${mode}: never merged`);
    assert.ok(!w.labels(12).includes('pdd:would-merge'), `${mode}: never marked would-merge`);
    assert.ok(w.labels(12).includes('pdd:needs-decision'), `${mode}: hard-stopped as needs-person`);
    assert.ok(!w.labels(12).includes('pdd:working'), `${mode}: worker slot freed`);
    const cardComment = pr.comments.find((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body));
    assert.ok(cardComment, `${mode}: PR has human-boundary card`);
    assert.match(cardComment.body, /Passed offline: unit tests 8\/8 passed/);
    assert.match(cardComment.body, /Unverified boundary: web-ui/);
    assert.match(cardComment.body, /Verify command: npx playwright test tests\/checkout\.spec\.ts/);
  }
});

test('Planted Trap 3: bug-fix regression check passing on base enters repair (never merges/would-merge) and caps cleanly at MAX_VALIDATION_REPAIRS (3)', () => {
  assert.equal(MAX_VALIDATION_REPAIRS, 3);
  for (const mode of ['auto', 'observe']) {
    const basePass = evaluateValidationOutcome({
      mode,
      changedFiles: ['bin/sync.mjs'],
      isBugFix: true,
      offlinePassed: true,
      e2eChecks: [{
        kind: 'subprocess-cli',
        command: 'node test/e2e/sync.test.mjs',
        executed: true,
        exitCode: 0,
        passed: 2,
        failed: 0,
        skipped: 0,
      }],
      bugFixBaseControl: 'passed-on-base',
      repairAttempts: 0,
    });
    assert.equal(basePass.bucket, 1);
    assert.equal(basePass.decision, 'repair');
    assert.equal(basePass.eligible, false);
    assert.equal(basePass.repairRoundsToSpend, 1);
    assert.equal(basePass.repairAttemptsNext, 1);
  }

  const exhausted = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['bin/sync.mjs'],
    isBugFix: true,
    offlinePassed: true,
    e2eChecks: [{
      kind: 'subprocess-cli',
      command: 'node test/e2e/sync.test.mjs',
      executed: true,
      exitCode: 1,
      passed: 1,
      failed: 1,
      skipped: 0,
    }],
    bugFixBaseControl: 'ran-and-failed-on-base',
    repairAttempts: 3,
  });
  assert.equal(exhausted.bucket, 1);
  assert.equal(exhausted.decision, 'needs-person');
  assert.equal(exhausted.waitKind, 'repair-exhausted');
  assert.equal(exhausted.freeSlot, true);
  assert.equal(exhausted.repairRoundsToSpend, 0);
});

test('Planted Trap 4: expired external login/daemon (gcloud, aws, docker, 401, postgres) triggers Bucket 2 with 0 repair rounds, freed slot, cooldown, and status visibility', async (t) => {
  // Verify multi-tool universal classification
  for (const [diag, expectedTool, expectedCmd] of [
    ['ExpiredToken: The security token included in the request is expired', 'aws', 'aws sts get-caller-identity'],
    ['Cannot connect to the Docker daemon at unix:///var/run/docker.sock', 'docker', 'docker info'],
    ['401 Unauthorized: Stripe invalid api key', 'stripe', 'env | grep -i token'],
    ['connect ECONNREFUSED 127.0.0.1:5432 postgres', 'postgres', 'pg_isready'],
  ]) {
    const out = evaluateValidationOutcome({
      mode: 'auto',
      changedFiles: ['src/deploy.mjs'],
      offlinePassed: false,
      diagnostics: [diag],
      repairAttempts: 0,
    });
    assert.equal(out.bucket, 2, diag);
    assert.equal(out.decision, 'park-auth-wait', diag);
    assert.equal(out.repairRoundsToSpend, 0, diag);
    assert.equal(out.freeSlot, true, diag);
    assert.equal(out.cooldownTool, expectedTool, diag);
    assert.equal(out.checkCommand, expectedCmd, diag);
  }

  // Live coreWorld test: gcloud login expired during suite execution
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.issue(14, { title: 'Deploy Cloud Run via gcloud' });
  await w.tick();
  writeIn(w.job(14, 'build').cwd, 'src/gcp/deploy.mjs', 'export const deploy = () => true;\n');
  const { pr } = w.build(14, {
    body: 'Fixes #14\n\nRuntime: PASS\nPath: d — src/gcp/deploy.mjs — unowned — no contract change — Test: done check',
  });
  await w.tick();
  w.review(14, 'PASS');
  w.say(14, 'suite', 'ERROR: (gcloud.run.deploy) Reauthentication required. Run: gcloud auth login\n');
  w.suite(14, 1);
  await w.tick();

  assert.equal(w.job(14, 'repair'), undefined, '0 wasted repair rounds on expired gcloud login');
  assert.equal(pr.state, 'open', 'PR stays open');
  assert.equal(pr.merged, false, 'PR not merged');
  assert.ok(w.labels(14).includes('pdd:needs-decision'), 'issue parked for auth wait');
  assert.ok(!w.labels(14).includes('pdd:working'), 'worker slot freed immediately');
  assert.ok(pr.comments.some((c) => /<!-- pdd:autopilot-core:auth-wait:/.test(c.body) && /gcloud/.test(c.body)), 'PR auth-wait comment names gcloud');

  const statusText = coreStatus({ state: w.state, settings: w.settings }, w.ports());
  assert.match(statusText, /Tool cooldown: gcloud/);
  assert.match(statusText, /Validation wait: PR #100 .* waiting on gcloud/);
});

test('Planted Trap 5: tool cooldown skips same-tool issues, claims unrelated issues immediately, and auto-resumes validate-only on exact head with ZERO code rebuilds', async (t) => {
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.issue(15, { title: 'Fix gcloud Cloud Run deploy' });
  await w.tick();
  writeIn(w.job(15, 'build').cwd, 'src/gcp/run.mjs', 'export const run = () => "ok";\n');
  const { pr, head: savedHead } = w.build(15, {
    body: 'Fixes #15\n\nRuntime: PASS\nPath: d — src/gcp/run.mjs — unowned — no contract change — Test: done check',
  });
  await w.tick();
  w.review(15, 'PASS');
  w.say(15, 'suite', 'ERROR: (gcloud.run.deploy) Reauthentication required. Run: gcloud auth login\n');
  w.suite(15, 1);
  await w.tick();

  // Worker slot is now free and gcloud is on cooldown. Add a second gcloud issue (#16) and an unrelated CLI issue (#17).
  w.issue(16, { title: 'Update gcloud IAM policy' });
  w.issue(17, { title: 'Add --json flag to local formatter CLI' });
  await w.tick({ preflightCheck: async () => ({ exitCode: 1 }) });

  assert.equal(w.job(16, 'build'), undefined, 'gcloud issue #16 skipped during active gcloud cooldown');
  assert.ok(w.job(17, 'build'), 'unrelated CLI issue #17 claimed immediately by freed worker');

  // Finish issue #17 quickly so slot is free again, then make gcloud preflight healthy (exitCode 0).
  w.build(17, { body: 'Fixes #17\n\nRuntime: PASS\nPath: d — change-17.txt — unowned — no contract change — Test: done check' });
  await w.tick({ preflightCheck: async () => ({ exitCode: 1 }) });
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick({ preflightCheck: async () => ({ exitCode: 1 }) });
  assert.equal(w.github.prs.get(101).merged, true, 'unrelated issue #17 merged cleanly');

  // Now gcloud login is healthy again: preflight returns 0 -> parked PR #100 resumes validate-only on exact savedHead with ZERO code rebuild!
  const buildsBefore = w.started.filter((j) => j.issue === 15 && j.role === 'build').length;
  await w.tick({
    preflightCheck: async ({ tool }) => ({ exitCode: tool === 'gcloud' ? 0 : 1 }),
  });
  const buildsAfter = w.started.filter((j) => j.issue === 15 && j.role === 'build').length;
  assert.equal(buildsAfter, buildsBefore, 'ZERO code rebuild spawned on validate-only auto-resume');

  // Complete ONLY the validation suite on the exact saved head, with healthy real E2E proof -> PR merges!
  w.suite(15, 0);
  await w.tick({
    validateE2e: async ({ head }) => {
      assert.equal(head, savedHead, 'validate-only runs against exact saved commit head');
      return {
        offlinePassed: true,
        e2eChecks: [{
          kind: 'live-binding',
          command: 'npm run test:e2e:gcp',
          executed: true,
          exitCode: 0,
          passed: 2,
          failed: 0,
          skipped: 0,
        }],
      };
    },
  });
  assert.equal(pr.merged, true, 'resumed PR #100 merged cleanly after validate-only pass');
  assert.ok(pr.comments.some((c) => /Validation proof: surfaces=external-tool; commands=npm run test:e2e:gcp; exitCodes=0/.test(c.body)), 'recorded proof included on merge comment');

  // Verify head-changed-abort refuses validate-only resume if commit moved
  const aborted = planValidationResume({
    pr: pr.number,
    headSha: savedHead,
    currentPrHeadSha: 'deadbeef'.repeat(5),
    cooldownTool: 'gcloud',
    preflightExitCode: 0,
    userResumed: false,
  });
  assert.equal(aborted.action, 'head-changed-abort');
  assert.equal(aborted.runValidationOnly, false);
  assert.equal(aborted.rebuildCode, false);

  // Verify direct cooldown guard helper
  assert.equal(shouldClaimWithCooldowns({ issueRequiredTools: ['GCLOUD'], toolCooldowns: { gcloud: { active: true } } }).claimable, false);
});

test('Planted Trap 6: human-interaction boundary (OAuth/2FA/captcha/live Stripe payment) hard-stops at Bucket 3 in BOTH auto and observe modes with exact 3-line card', async (t) => {
  for (const mode of ['auto', 'observe']) {
    const w = await coreWorld(t, { settings: { mode, runs: 1 } });
    w.issue(18, { title: 'Add Stripe 3DS payment flow' });
    await w.tick();
    writeIn(w.job(18, 'build').cwd, 'src/stripe-checkout.mjs', 'export const pay = () => true;\n');
    const { pr } = w.build(18, {
      body: 'Fixes #18\n\nRuntime: PASS\nPath: d — src/stripe-checkout.mjs — unowned — no contract change — Test: done check',
    });
    await w.tick();
    w.review(18, 'PASS');
    w.suite(18, 0);
    await w.tick({
      validateE2e: async () => ({
        offlinePassed: true,
        offlineSummary: 'unit tests 9/9 passed',
        e2eChecks: [],
        needsHumanInteraction: true,
        humanBoundaryDetail: 'live Stripe 3DS browser challenge + 2FA',
        verifyCommand: 'npm run verify:stripe:3ds',
      }),
    });

    assert.equal(pr.state, 'open', `${mode}: PR stays open`);
    assert.equal(pr.merged, false, `${mode}: never merged`);
    assert.ok(!w.labels(18).includes('pdd:would-merge'), `${mode}: observe mode never marks would-merge on human boundary`);
    assert.ok(w.labels(18).includes('pdd:needs-decision'), `${mode}: hard-stopped as needs-person`);
    assert.ok(!w.labels(18).includes('pdd:working'), `${mode}: worker slot freed`);
    const card = pr.comments.find((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body));
    assert.ok(card, `${mode}: PR carries human-boundary marker`);
    assert.match(card.body, /Passed offline: unit tests 9\/9 passed/);
    assert.match(card.body, /Unverified boundary: live Stripe 3DS browser challenge \+ 2FA/);
    assert.match(card.body, /Verify command: npm run verify:stripe:3ds/);
  }
});

test('Planted Trap 7: backside deterministic lint (silent-validation-skip, boundary-mock-only-test, workspace-local rules/lint/*.json without origin/main) and frontside real-E2E rules', async (t) => {
  const repo = makeTempGitRepo(t, 'pdd-validator-lint-');
  writeFile(repo, 'api/orders.mjs', 'export function handleOrder() { return { ok: true }; }\n');
  writeFile(
    repo,
    'src/bad-validator.mjs',
    "export function bypass(err) { if (err === 'real-binding-unavailable') return { localSkipRow: true }; }\n",
  );
  writeFile(
    repo,
    'test/orders-mock.test.mjs',
    "import { mock } from 'node:test';\nimport { handleOrder } from '../api/orders.mjs';\nconst fakeClient = mock.fn(() => handleOrder());\n",
  );
  writeFile(
    repo,
    'rules/lint/01-validator.json',
    JSON.stringify({
      rules: {
        'silent-validation-skip': 'error',
        'boundary-mock-only-test': 'error',
      },
      custom_rules: [{
        id: 'no-skip-comment',
        target: 'code',
        severity: 'error',
        forbid_pattern: 'DISABLE_REAL_E2E',
        message: 'Never disable real E2E in production code.',
      }],
    }),
  );
  // Plant a symlinked rule file inside rules/lint/ to verify symlink safety guard skips it safely
  const outside = mkdtempSync(join(tmpdir(), 'pdd-outside-rule-'));
  t.after(() => rmSync(outside, { recursive: true, force: true }));
  writeFileSync(join(outside, 'evil.json'), JSON.stringify({ disable: ['silent-validation-skip'] }));
  symlinkSync(join(outside, 'evil.json'), join(repo, 'rules/lint/99-symlink.json'));
  commitAll(repo, 'fixture');

  const cfg = loadProjectLintConfig(repo);
  assert.equal(cfg.configured, true);
  assert.equal(cfg.ruleSeverities.get('silent-validation-skip'), 'error');
  assert.equal(cfg.ruleSeverities.get('boundary-mock-only-test'), 'error');
  assert.equal(cfg.disabledRules.has('silent-validation-skip'), false, 'symlinked rule file ignored');

  const report = lintRepoProject({ root: repo });
  assert.equal(report.ok, false, 'promoted error rules fail closed');
  const codes = new Set(report.findings.map((f) => f.code));
  assert.ok(codes.has('silent-validation-skip'), 'flags silent validation skip in production code');
  assert.ok(codes.has('boundary-mock-only-test'), 'flags mock-only boundary test lacking real E2E');

  // Add a real E2E test for api/orders.mjs and remove the silent skip -> boundary-mock-only-test clears cleanly!
  writeFile(
    repo,
    'test/orders-e2e.test.mjs',
    "import http from 'node:http';\nimport { handleOrder } from '../api/orders.mjs';\nconst s = http.createServer((q, r) => r.end(JSON.stringify(handleOrder()))).listen(0);\nawait fetch('http://127.0.0.1:' + s.address().port);\n",
  );
  writeFile(repo, 'src/bad-validator.mjs', 'export function clean() { return true; }\n');
  commitAll(repo, 'add real e2e');

  const cleanReport = lintRepoProject({ root: repo });
  assert.equal(cleanReport.ok, true, `expected clean lint after adding real E2E, got: ${cleanReport.errors.join('; ')}`);
  assert.equal(cleanReport.findings.some((f) => f.code === 'boundary-mock-only-test'), false);
  assert.equal(cleanReport.findings.some((f) => f.code === 'silent-validation-skip'), false);

  // Direct lint helper exports
  assert.ok(lintValidationSkips("test.skip('e2e login', () => {});", { path: 'test/login.test.mjs', kind: 'test' }).length > 0);
  assert.equal(lintBoundaryMockOnlyTests("import { mock } from 'node:test';\nimport { x } from '../api/x.mjs';\nconst fakeClient = mock.fn();", { path: 'test/x.test.mjs', hasRealE2eCoverage: false }).length, 1);
  assert.equal(lintBoundaryMockOnlyTests("import { mock } from 'node:test';\nimport { x } from '../api/x.mjs';\nconst fakeClient = mock.fn();", { path: 'test/x.test.mjs', hasRealE2eCoverage: true }).length, 0);

  // Verify frontside build prompt generated by Autopilot core teaches real E2E upfront
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.issue(19, { title: 'Add server endpoint' });
  await w.tick();
  const buildInput = w.job(19, 'build').input;
  assert.match(buildInput, /real end-to-end tests upfront/i);
  assert.match(buildInput, /never rewrite real end-to-end checks into mocks/i);
  assert.match(buildInput, /fails on base and passes on head/i);

  // Verify lintValidationCode returns clean ok on a clean production module
  assert.equal(lintValidationCode({ path: 'src/ok.mjs', kind: 'code', text: 'export const ok = () => true;\n', hasRealE2eCoverage: true }).ok, true);
});
