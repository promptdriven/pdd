import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import {
  MAX_VALIDATION_REPAIRS,
  detectChangedSurfaces,
  detectRealE2eKindsInTest,
  evaluateValidationOutcome,
  lintValidationCode,
  planValidationResume,
  scanJsPreserveLines,
  shouldClaimWithCooldowns,
} from '../src/autopilot-validator.mjs';
import { coreStatus, runDefaultPreflightCheck } from '../src/autopilot-core.mjs';
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

test('MF-1: production path WITHOUT ports.validateE2e fails closed when boundary code lacks real E2E, passes once real E2E exists, and enforces real bug-fix base control', async (t) => {
  // 1a) Auto and observe modes WITHOUT validateE2e port: web/checkout.tsx with zero real E2E MUST NOT merge or would-merge!
  for (const mode of ['auto', 'observe']) {
    const w = await coreWorld(t, { settings: { mode, runs: 1 } });
    w.issue(31, { title: `Add checkout widget (${mode})` });
    await w.tick();
    writeIn(w.job(31, 'build').cwd, 'web/checkout.tsx', 'export function Checkout() { return "pay"; }\n');
    const { pr } = w.build(31, {
      write: false,
      body: 'Fixes #31\n\nRuntime: PASS\nPath: d — web/checkout.tsx — unowned — no contract change — Test: done check',
    });
    await w.tick();
    w.review(31, 'PASS');
    w.suite(31, 0);
    // NO validateE2e port override -> exercises real collectRealValidationEvidence!
    await w.tick();

    assert.equal(pr.merged, false, `${mode}: zero-E2E web change MUST NOT merge without real E2E proof`);
    assert.equal(pr.comments.some((c) => /would merge/i.test(c.body)), false, `${mode}: zero-E2E web change MUST NOT say would merge`);
    assert.ok(
      pr.comments.some((c) => /Passed offline:/.test(c.body) && /Unverified boundary:/.test(c.body) && /Verify command:/.test(c.body)),
      `${mode}: zero-E2E web change posts 3-line Human Verification Card`,
    );
  }

  // 1b) Real local-server E2E test targeting api/billing.mjs passes WITHOUT validateE2e port, and real bug-fix base control blocks passed-on-base then passes on ran-and-failed-on-base!
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.baseCommit('api/billing.mjs', 'export function totalCents(a, b) { return a + b; }\n');
  w.issue(32, { title: 'Fix billing tax rounding bug', labels: ['bug'] });
  await w.tick();
  const buildCwd = w.job(32, 'build').cwd;
  writeIn(buildCwd, 'api/billing.mjs', 'export function totalCents(a, b) { return Math.round((a + b) * 1.1); }\n');
  // First write a test that ALREADY passes on base (does not check the fixed tax rounding -> passed-on-base!)
  writeIn(
    buildCwd,
    'test/billing-e2e.test.mjs',
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import http from 'node:http';",
      "import { totalCents } from '../api/billing.mjs';",
      "test('billing endpoint responds', async () => {",
      "  const s = http.createServer((_req, res) => res.end(String(totalCents(0, 0))));",
      "  await new Promise((resolve) => s.listen(0, '127.0.0.1', resolve));",
      "  const port = s.address().port;",
      "  try {",
      "    const r = await fetch(`http://127.0.0.1:${port}`);",
      "    assert.equal(await r.text(), '0');",
      "  } finally { s.close(); }",
      "});",
      '',
    ].join('\n'),
  );
  const { pr } = w.build(32, {
    write: false,
    body: 'Fixes #32\n\nRuntime: PASS\nPath: d — api/billing.mjs, test/billing-e2e.test.mjs — unowned — no contract change — Test: done check',
  });
  await w.tick();
  w.review(32, 'PASS');
  w.suite(32, 0);
  // Real production gate runs controlTree against base -> test passes on base -> enters repair, MUST NOT merge!
  await w.tick();
  assert.equal(pr.merged, false, 'bug-fix PR whose test passes on base MUST NOT merge');
  const repairJob = w.job(32, 'repair');
  assert.ok(repairJob, 'bug-fix passed-on-base enters bounded repair');
  assert.match(repairJob.input, /passed[- ]on[- ]base|bug-fix-passed-on-base/i);

  // Now update the real E2E test so it asserts the fixed tax rounding (fails on base, passes on head)!
  writeIn(
    repairJob.cwd,
    'test/billing-e2e.test.mjs',
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import http from 'node:http';",
      "import { totalCents } from '../api/billing.mjs';",
      "test('billing endpoint applies 10% tax rounding', async () => {",
      "  const s = http.createServer((_req, res) => res.end(String(totalCents(50, 50))));",
      "  await new Promise((resolve) => s.listen(0, '127.0.0.1', resolve));",
      "  const port = s.address().port;",
      "  try {",
      "    const r = await fetch(`http://127.0.0.1:${port}`);",
      "    assert.equal(await r.text(), '110');",
      "  } finally { s.close(); }",
      "});",
      '',
    ].join('\n'),
  );
  w.build(32, {
    role: 'repair',
    write: false,
    body: 'Fixes #32\n\nRuntime: PASS\nPath: d — api/billing.mjs, test/billing-e2e.test.mjs — unowned — no contract change — Test: done check',
  });
  await w.tick();
  w.review(32, 'PASS');
  w.suite(32, 0);
  await w.tick();
  assert.equal(pr.merged, true, 'bug-fix PR with real E2E that fails on base and passes on head merges cleanly without validateE2e mock');
});

test('MF-2: boundary-mock-only-test enforces per-target real E2E coverage even in mature repos with unrelated E2E tests', (t) => {
  const repo = makeTempGitRepo(t, 'pdd-mf2-per-target-');
  // Unrelated API module that DOES have real E2E coverage
  writeFile(repo, 'api/other.mjs', 'export const other = () => "ok";\n');
  writeFile(
    repo,
    'test/other-e2e.test.mjs',
    "import http from 'node:http';\nimport { other } from '../api/other.mjs';\nconst s = http.createServer((_q, r) => r.end(other())).listen(0);\nawait fetch(`http://127.0.0.1:${s.address().port}`);\n",
  );
  // New boundary module with ONLY a mock-only test
  writeFile(repo, 'api/billing.mjs', 'export const charge = () => "charged";\n');
  writeFile(
    repo,
    'test/billing-mock.test.mjs',
    "import { mock } from 'node:test';\nimport { charge } from '../api/billing.mjs';\nconst fakeClient = mock.fn(() => charge());\nfakeClient();\n",
  );
  commitAll(repo, 'mature repo with one untested boundary module');

  const before = lintRepoProject({ root: repo });
  const mockFindings = before.findings.filter((f) => f.code === 'boundary-mock-only-test');
  assert.equal(mockFindings.length, 1, 'unrelated api/other.mjs E2E must NOT hide mock-only test for api/billing.mjs');
  assert.equal(mockFindings[0].path, 'test/billing-mock.test.mjs');

  // Adding a real E2E test targeting api/billing.mjs clears the finding
  writeFile(
    repo,
    'test/billing-e2e.test.mjs',
    "import http from 'node:http';\nimport { charge } from '../api/billing.mjs';\nconst s = http.createServer((_q, r) => r.end(charge())).listen(0);\nawait fetch(`http://127.0.0.1:${s.address().port}`);\n",
  );
  commitAll(repo, 'add billing real e2e');
  const after = lintRepoProject({ root: repo });
  assert.equal(after.findings.some((f) => f.code === 'boundary-mock-only-test'), false, 'finding clears once api/billing.mjs has its own real E2E test');
});

test('MF-3: real-binding-unavailable closes RR6 stripped-row, PR-body-only, and stale-row bypasses', async (t) => {
  // 3a) Saved check with reason/codes/object-refusal real-binding-unavailable MUST still park at Bucket 2 (never silently merge)
  {
    const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
    w.runtimeEvidence = async () => ({
      stories: [{
        story: 'user_stories/live.md',
        pass: false,
        current: true,
        sent: true,
        failed: 0,
        reason: 'real-binding-unavailable',
        refusals: [{ code: 'real-binding-unavailable', message: 'db unreachable' }],
      }],
      storyFiles: ['user_stories/live.md'],
      footprints: { 'user_stories/live.md': ['prompts/live.prompt.md'] },
    });
    w.issue(33, { title: 'Update live binding story' });
    await w.tick();
    writeIn(w.job(33, 'build').cwd, 'user_stories/live.md', '# Live Story\n');
    const { pr } = w.build(33, {
      write: false,
      body: 'Fixes #33\n\nRuntime: not run (real-binding-unavailable)\nPath: d — user_stories/live.md — unowned — no contract change — Test: done check',
    });
    await w.tick();
    assert.equal(pr.merged, false, 'reason/object-refusal real-binding-unavailable MUST NOT merge');
    assert.ok(w.labels(33).includes('pdd:needs-decision'), 'parks at Bucket 2 needs-decision');
    assert.equal(w.started.filter((j) => j.issue === 33 && j.role === 'repair').length, 0, '0 repair rounds');
  }

  // 3b) PR body reporting Runtime: not run (real-binding-unavailable) with NO saved row still parks at Bucket 2
  {
    const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
    w.runtimeEvidence = async () => ({ stories: [], storyFiles: [], footprints: {} });
    w.issue(34, { title: 'PR body real-binding-unavailable without saved row' });
    await w.tick();
    const { pr } = w.build(34, {
      body: 'Fixes #34\n\nRuntime: not run (real-binding-unavailable)\nPath: d — change-34.txt — unowned — no contract change — Test: done check',
    });
    await w.tick();
    assert.equal(pr.merged, false, 'PR body real-binding-unavailable without saved row MUST NOT merge');
    assert.ok(w.labels(34).includes('pdd:needs-decision'), 'parks at Bucket 2');
  }

  // 3c) Newer passing saved check at the same head supersedes an earlier stale real-binding-unavailable row
  {
    const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
    w.runtimeEvidence = async () => ({
      stories: [
        { story: 'user_stories/live.md', pass: false, current: true, at: 1000, sent: true, failed: 0, refusals: ['real-binding-unavailable'] },
        { story: 'user_stories/live.md', pass: true, current: true, at: 2000, sent: true, failed: 0, refusals: [] },
      ],
      storyFiles: ['user_stories/live.md'],
      footprints: { 'user_stories/live.md': [] },
    });
    w.issue(35, { title: 'Stale real-binding-unavailable superseded by passing check' });
    await w.tick();
    const { pr } = w.build(35, {
      body: 'Fixes #35\n\nRuntime: PASS\nPath: d — change-35.txt — unowned — no contract change — Test: done check',
    });
    await w.tick();
    w.review(35, 'PASS');
    w.suite(35, 0);
    await w.tick();
    assert.equal(pr.merged, true, 'newer passing saved row supersedes stale real-binding-unavailable row');
  }
});

test('MF-4: Bucket 2 resume enforces review guard, keeps worktree, runs bindingRerun, resumes on human reply without rebuild, prunes orphan cooldowns, and validates runDefaultPreflightCheck', async (t) => {
  // 4a) Park BEFORE review passes (on real-binding-unavailable) -> worktree kept, review MUST run on resume (no review bypass!), bindingRerun runs, and human reply resumes validate-only (0 rebuilds)
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  let bindingHealthy = false;
  let rerunCalls = 0;
  w.runtimeEvidence = async () => ({
    stories: [{
      story: 'user_stories/live.md',
      pass: bindingHealthy,
      current: true,
      sent: true,
      failed: 0,
      refusals: bindingHealthy ? [] : ['real-binding-unavailable'],
    }],
    storyFiles: ['user_stories/live.md'],
    footprints: { 'user_stories/live.md': [] },
  });
  w.issue(36, { title: 'Live runtime binding job' });
  await w.tick();
  const wt36 = join(w.root, 'worktrees', '36');
  const { pr: pr36 } = w.build(36, {
    body: 'Fixes #36\n\nRuntime: not run (real-binding-unavailable)\nPath: d — change-36.txt — unowned — no contract change — Test: done check',
  });
  await w.tick();
  assert.equal(pr36.merged, false, 'parked before review');
  assert.ok(w.labels(36).includes('pdd:needs-decision'));
  assert.equal(existsSync(wt36), true, 'authWait retains worktree on disk for validate-only resume');
  assert.equal(w.started.filter((j) => j.issue === 36 && j.role === 'review').length, 0, 'review had not passed before park');

  // Human replies on the parked issue (keeping pdd:needs-decision label) -> must resume validate-only (0 rebuilds), NOT claim for full rebuild!
  const buildsBefore = w.started.filter((j) => j.issue === 36 && j.role === 'build').length;
  w.github.comment(36, 'Fixed the runtime binding, please re-validate.', 'acme');
  await w.tick({
    rerunRuntimeBinding: async () => { rerunCalls += 1; bindingHealthy = true; },
  });
  assert.equal(w.started.filter((j) => j.issue === 36 && j.role === 'build').length, buildsBefore, 'human reply on parked issue causes ZERO code rebuild');
  assert.equal(rerunCalls, 1, 'real-binding-unavailable resume triggers bindingRerun');
  assert.equal(w.started.filter((j) => j.issue === 36 && j.role === 'review').length, 1, 'review MUST run on resume because review had NOT passed before park');

  w.review(36, 'PASS');
  w.suite(36, 0);
  await w.tick();
  assert.equal(pr36.merged, true, 'PR merges cleanly once bindingRerun + fresh review + suite pass');

  // 4b) Closing a parked PR prunes its orphan cooldown on the next tick
  const w2 = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w2.issue(37, { title: 'Fix gcloud auth deploy' });
  await w2.tick();
  const { pr: pr37 } = w2.build(37, { body: 'Fixes #37\n\nRuntime: PASS\nPath: d — change-37.txt — unowned — no contract change — Test: done check' });
  await w2.tick();
  w2.review(37, 'PASS');
  w2.say(37, 'suite', 'ERROR: (gcloud.run.deploy) Reauthentication required. Run: gcloud auth login\n');
  w2.suite(37, 1);
  await w2.tick();
  const beforeClose = JSON.parse(readFileSync(join(w2.root, 'core.json'), 'utf8'));
  assert.equal(beforeClose.toolCooldowns?.gcloud?.active, true, 'gcloud cooldown active while PR #37 is parked');

  pr37.state = 'closed';
  await w2.tick();
  const afterClose = JSON.parse(readFileSync(join(w2.root, 'core.json'), 'utf8'));
  assert.equal(afterClose.toolCooldowns?.gcloud, undefined, 'closing parked PR prunes its orphan cooldown');

  // 4c) runDefaultPreflightCheck returns { exitCode: null } safely for unknown tools and non-zero cleanly for missing binary
  assert.deepEqual(await runDefaultPreflightCheck({ tool: 'unknown-tool-xyz' }), { exitCode: null });
  const badEnvProbe = await runDefaultPreflightCheck({ tool: 'gcloud', env: { PATH: '/nonexistent-bin-dir' } });
  assert.ok(badEnvProbe && badEnvProbe.exitCode !== 0 && badEnvProbe.exitCode !== null, 'missing binary returns non-zero cleanly');
});

test('MF-5: passing test titles mentioning 2FA/captcha/real-binding-unavailable do NOT trigger Bucket 2/3, while failed CI auth log triggers Bucket 2', async (t) => {
  // 5a) Suite fails on an ordinary AssertionError after passing tests whose titles mention 2FA/captcha/real-binding-unavailable
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.issue(38, { title: 'Fix local parser formatting' });
  await w.tick();
  const { pr } = w.build(38, { body: 'Fixes #38\n\nRuntime: PASS\nPath: d — change-38.txt — unowned — no contract change — Test: done check' });
  await w.tick();
  w.review(38, 'PASS');
  w.say(38, 'suite', [
    '✔ Planted Trap 1: real-binding-unavailable fails closed to Bucket 2 (12ms)',
    '✔ Planted Trap 6: human-interaction boundary (OAuth/2FA/captcha/live Stripe payment) (15ms)',
    '✖ formatter trims trailing space (2ms)',
    '  AssertionError [ERR_ASSERTION]: Expected values to be strictly equal:',
    '  + actual - expected',
    "  + 'hello '",
    "  - 'hello'",
  ].join('\n'));
  w.suite(38, 1);
  await w.tick();
  assert.equal(w.labels(38).includes('pdd:needs-decision'), false, 'passing test titles must NOT false-trigger Bucket 2 or Bucket 3');
  assert.ok(w.job(38, 'repair'), 'ordinary AssertionError enters normal repair');
  assert.equal(pr.merged, false);

  // 5b) Failed CI check log containing AWS ExpiredToken triggers Bucket 2 auth-wait (0 repairs)
  const w2 = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w2.issue(39, { title: 'Deploy AWS S3 artifact' });
  await w2.tick();
  const { head: head39 } = w2.build(39, {
    checks: null,
    body: 'Fixes #39\n\nRuntime: PASS\nPath: d — change-39.txt — unowned — no contract change — Test: done check',
  });
  w2.github.setChecks(head39, 'failure', 'completed', {
    runId: 7701,
    name: 'deploy-e2e',
    log: '2026-11-18T10:00:00Z An error occurred (ExpiredToken): The security token included in the request is expired\n',
  });
  await w2.tick();
  assert.ok(w2.labels(39).includes('pdd:needs-decision'), 'CI ExpiredToken failure parks at Bucket 2');
  assert.equal(w2.started.filter((j) => j.issue === 39 && j.role === 'repair').length, 0, '0 repair rounds on CI auth failure');
});

test('MF-6: silent-validation-skip catches node:test skip options, ignores comments/strings, has 0 false positives on this repo, and backside lint includes file:line', async (t) => {
  // node:test { skip: true } and { skip: 'reason' } caught
  assert.ok(lintValidationSkips("test('e2e login', { skip: true }, () => {});", { path: 'test/a.test.mjs', kind: 'test' }).length > 0);
  assert.ok(lintValidationSkips("it('e2e checkout', { skip: 'no creds' }, () => {});", { path: 'test/b.test.mjs', kind: 'test' }).length > 0);

  // Comments and string fixtures do NOT false-positive
  const cleanCode = [
    '// real-binding-unavailable is never skipped silently',
    "const PAT = 'real-binding-unavailable';",
    "const sample = `test.skip('x', () => {})`;",
    'export function check(x) { return x === PAT ? "block" : sample; }',
  ].join('\n');
  assert.equal(lintValidationSkips(cleanCode, { path: 'src/checker.mjs', kind: 'code' }).length, 0, 'comments and strings do not trigger silent-validation-skip');

  // 0 false positives on THIS worktree's own validator/core/lint/test files!
  const selfReport = lintRepoProject({ root: process.cwd() });
  const prFiles = new Set([
    'src/autopilot-validator.mjs',
    'src/autopilot-core.mjs',
    'src/autopilot-launcher.mjs',
    'src/repo-hygiene-lint.mjs',
    'src/pdd-cli.mjs',
    'test/autopilot-validator-v2.test.mjs',
    'test/autopilot-validator.vectors.test.mjs',
    'test/autopilot-hardening.test.mjs',
  ]);
  const selfHits = (selfReport.findings ?? []).filter(
    (f) => prFiles.has(f.path) && (f.code === 'silent-validation-skip' || f.code === 'boundary-mock-only-test'),
  );
  assert.deepEqual(selfHits, [], `0 false positives expected on PR files, got: ${JSON.stringify(selfHits)}`);

  // Backside lint repair feedback inside Autopilot core includes exact file:line
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.issue(40, { title: 'Add helper test' });
  await w.tick();
  writeIn(w.job(40, 'build').cwd, 'test/planted-skip.test.mjs', "import test from 'node:test';\ntest('e2e', { skip: true }, () => {});\n");
  w.build(40, {
    write: false,
    body: 'Fixes #40\n\nRuntime: PASS\nPath: d — test/planted-skip.test.mjs — unowned — no contract change — Test: done check',
  });
  await w.tick();
  w.review(40, 'PASS');
  w.suite(40, 0);
  await w.tick();
  const repair = w.job(40, 'repair');
  assert.ok(repair, 'planted node:test skip triggers backside lint repair');
  assert.match(repair.input, /test\/planted-skip\.test\.mjs:2/, 'repair feedback includes exact file:line');
});

test('MF-7: Bucket 1 validator failure runs all 3 bounded repair rounds and escalates at cap 3 with repair-exhausted PR comment', async (t) => {
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.issue(41, { title: 'Fix stubborn backside skip' });
  await w.tick();
  writeIn(w.job(41, 'build').cwd, 'test/stubborn-skip.test.mjs', "import test from 'node:test';\ntest.skip('e2e', () => {});\n");
  const { pr } = w.build(41, {
    write: false,
    body: 'Fixes #41\n\nRuntime: PASS\nPath: d — test/stubborn-skip.test.mjs — unowned — no contract change — Test: done check',
  });
  await w.tick();

  // Drive through all MAX_VALIDATION_REPAIRS (3) rounds without fixing the skip -> must NOT stop early at round 1 or 2!
  for (let round = 1; round <= MAX_VALIDATION_REPAIRS; round += 1) {
    w.review(41, 'PASS');
    w.suite(41, 0);
    await w.tick();
    const repairsSoFar = w.started.filter((j) => j.issue === 41 && j.role === 'repair').length;
    assert.equal(repairsSoFar, round, `Bucket 1 validator failure starts repair round ${round} of ${MAX_VALIDATION_REPAIRS}`);
    const rep = w.job(41, 'repair');
    writeIn(rep.cwd, 'test/stubborn-skip.test.mjs', `import test from 'node:test';\n// round ${round}\ntest.skip('e2e', () => {});\n`);
    w.build(41, {
      role: 'repair',
      write: false,
      body: 'Fixes #41\n\nRuntime: PASS\nPath: d — test/stubborn-skip.test.mjs — unowned — no contract change — Test: done check',
    });
    await w.tick();
  }

  // After round 3 completes and STILL fails validation, escalate cleanly at cap 3 -> needs-person + repair-exhausted PR comment (NOT needs-approval)
  w.review(41, 'PASS');
  w.suite(41, 0);
  await w.tick();
  assert.equal(pr.merged, false, 'repair-exhausted PR never merges');
  assert.equal(w.started.filter((j) => j.issue === 41 && j.role === 'repair').length, MAX_VALIDATION_REPAIRS, 'caps strictly at 3 repairs');
  assert.ok(w.labels(41).includes('pdd:needs-decision'), 'escalates to pdd:needs-decision');
  assert.ok(pr.comments.some((c) => c.body.includes(`<!-- pdd:autopilot-core:repair-exhausted:${pr.number} -->`)), 'posts repair-exhausted PR comment marker');
  assert.equal(pr.comments.some((c) => c.body.includes('needs-approval')), false, 'does NOT post misleading needs-approval comment');
});

test('MF-8 & Minor Notes: empty changedFiles fail closed, word-boundary surfaces, user_stories not docsOnly, Dockerfile/extra extensions, isBugFix not-applicable, and CLI rules/lint/*.json detection', (t) => {
  // Empty changedFiles -> NOT docsOnly, fails closed without proof
  const emptySurf = detectChangedSurfaces({ changedFiles: [] });
  assert.equal(emptySurf.docsOnly, false);
  assert.ok(emptySurf.requiredProofKinds.includes('real-execution'));
  const emptyEval = evaluateValidationOutcome({ mode: 'auto', changedFiles: [], offlinePassed: true, e2eChecks: [] });
  assert.equal(emptyEval.eligible, false, 'empty changedFiles must fail closed when no proof exists');

  // user_stories/ is NOT docsOnly
  assert.equal(detectChangedSurfaces({ changedFiles: ['user_stories/checkout.md'] }).docsOnly, false);

  // Word-boundary surface matchers + non-production directory exclusion: no false matches on cli/api/auth/payment
  assert.deepEqual(detectChangedSurfaces({ changedFiles: ['src/client.mjs'] }).surfaces, ['runtime-code']);
  assert.deepEqual(detectChangedSurfaces({ changedFiles: ['src/capital.mjs'] }).surfaces, ['runtime-code']);
  assert.deepEqual(detectChangedSurfaces({ changedFiles: ['src/author.mjs'] }).surfaces, ['runtime-code']);
  assert.deepEqual(detectChangedSurfaces({ changedFiles: ['prompts/cli/auth.prompt.md'] }).surfaces, []);
  assert.deepEqual(detectChangedSurfaces({ changedFiles: ['docs/stripe-guide.md'] }).surfaces, ['docs']);
  assert.equal(detectChangedSurfaces({ changedFiles: ['docs/stripe-guide.md'] }).docsOnly, true);

  // Dockerfile.* and extra runtime extensions (.zig, .dart) are runtime code, not docsOnly
  assert.equal(detectChangedSurfaces({ changedFiles: ['Dockerfile.prod'] }).docsOnly, false);
  assert.equal(detectChangedSurfaces({ changedFiles: ['src/engine.zig'] }).docsOnly, false);
  assert.equal(detectChangedSurfaces({ changedFiles: ['lib/main.dart'] }).docsOnly, false);

  // isBugFix: true with bugFixBaseControl: 'not-applicable' fails closed at Bucket 3 (never treated as passing)
  const missingCtrl = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/calc.mjs'],
    isBugFix: true,
    offlinePassed: true,
    e2eChecks: [{ kind: 'real-execution', command: 'npm test', executed: true, exitCode: 0, passed: 1, failed: 0, skipped: 0 }],
    bugFixBaseControl: 'not-applicable',
  });
  assert.equal(missingCtrl.eligible, false);
  assert.equal(missingCtrl.bucket, 3);
  assert.equal(missingCtrl.waitKind, 'missing-e2e');
  assert.match(missingCtrl.message, /base regression control/i);

  // Minor Note 1: `pdd lint --local` detects workspace-local rules/lint/*.json even without `"lint"` in pdd.json
  const repo = makeTempGitRepo(t, 'pdd-mf8-cli-rules-');
  writeFile(repo, 'pdd.json', JSON.stringify({ name: 'demo' }));
  writeFile(repo, 'src/skip.mjs', "export function bad(err) { if (err === 'real-binding-unavailable') return { ok: true, skipped: true }; }\n");
  writeFile(repo, 'rules/lint/10-strict.json', JSON.stringify({ rules: { 'silent-validation-skip': 'error' } }));
  commitAll(repo, 'rules without pdd.json lint key');

  let exitCode = 0;
  let combined = '';
  try {
    combined = execFileSync(process.execPath, [join(process.cwd(), 'bin/pdd.mjs'), 'lint', '--local'], {
      cwd: repo,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
  } catch (err) {
    exitCode = err.status ?? 1;
    combined = `${err.stdout ?? ''}\n${err.stderr ?? ''}`;
  }
  assert.notEqual(exitCode, 0, 'pdd lint --local must enforce rules/lint/*.json error even without lint key in pdd.json');
  assert.match(combined, /silent-validation-skip/);
});

test('R2-1a (MF-1 base control): links node_modules into controlTree and treats missing non-changed package as not-run', async (t) => {
  // Part 1: bug-fix test depends on an installed node_modules package -> controlTree symlinks node_modules so base control runs and reproduces the bug.
  const wOk = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  const fakePkgDir = join(wOk.state.cwd, 'node_modules', 'fake-base-dep');
  mkdirSync(fakePkgDir, { recursive: true });
  writeFileSync(join(fakePkgDir, 'package.json'), JSON.stringify({ name: 'fake-base-dep', type: 'module', main: 'index.mjs' }));
  writeFileSync(join(fakePkgDir, 'index.mjs'), 'export const bump = (n) => n + 1;\n');
  wOk.baseCommit('src/dep-bug.mjs', "import { bump } from 'fake-base-dep';\nexport const compute = (n) => bump(n) - 1;\n");

  wOk.issue(41, { title: 'Fix off-by-one using fake-base-dep', labels: ['pdd:bug'] });
  await wOk.tick();
  const cwd41 = wOk.job(41, 'build').cwd;
  writeIn(cwd41, 'src/dep-bug.mjs', "import { bump } from 'fake-base-dep';\nexport const compute = (n) => bump(n);\n");
  writeIn(
    cwd41,
    'test/dep-bug.test.mjs',
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import { compute } from '../src/dep-bug.mjs';",
      "test('compute returns n+1', () => { assert.equal(compute(4), 5); });",
      '',
    ].join('\n'),
  );
  wOk.build(41, {
    write: false,
    body: 'Fixes #41\n\nRuntime: not run (no prompt changed)\nPath: d — src/dep-bug.mjs, test/dep-bug.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wOk.tick();
  wOk.review(41, 'PASS');
  wOk.suite(41, 0);
  await wOk.tick();
  assert.equal(wOk.github.merges.length, 1, 'linking node_modules lets bug-fix base control genuinely fail on base and merge');

  // Part 2: missing non-changed npm package on base (ERR_MODULE_NOT_FOUND) MUST be classified as not-run (never falsely credited as ran-and-failed-on-base).
  const wMiss = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wMiss.baseCommit('src/calc-miss.mjs', 'export const add = (a, b) => a - b;\n');
  wMiss.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  wMiss.issue(42, { title: 'Fix add with missing pkg in test', labels: ['pdd:bug'] });
  await wMiss.tick();
  const cwd42 = wMiss.job(42, 'build').cwd;
  writeIn(cwd42, 'src/calc-miss.mjs', 'export const add = (a, b) => a + b;\n');
  writeIn(
    cwd42,
    'test/calc-miss.test.mjs',
    [
      "import test from 'node:test';",
      "import assert from 'node:assert/strict';",
      "import 'never-installed-pkg-r2-test';",
      "import { add } from '../src/calc-miss.mjs';",
      "test('add', () => { assert.equal(add(2, 3), 5); });",
      '',
    ].join('\n'),
  );
  wMiss.build(42, {
    write: false,
    body: 'Fixes #42\n\nRuntime: not run (no prompt changed)\nPath: d — src/calc-miss.mjs, test/calc-miss.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wMiss.tick();
  wMiss.review(42, 'PASS');
  wMiss.suite(42, 0);
  await wMiss.tick();
  assert.equal(wMiss.github.merges.length, 0, 'ERR_MODULE_NOT_FOUND for missing non-changed package must be not-run and fail closed');
  const pr42 = [...wMiss.github.prs.values()].find((p) => p.head?.ref?.includes('core-42')) ?? [...wMiss.github.prs.values()][0];
  assert.ok(
    pr42.comments.some((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body) && /base regression control/i.test(c.body)),
    'not-run base control blocks merge at Bucket 3 with base regression control reason',
  );
});

test('R2-1b (MF-1 suite scope, runtime-code per-file coverage, scanner regex/template, trivial subprocess)', async (t) => {
  // 1. Regex literals masked in codeNoStrings: /playwright/ does not grant browser-playwright, /localSkipRow/ does not trigger silent-validation-skip
  const regexBrowser = [
    "import test from 'node:test';",
    "test('mentions regex only', () => { const re = /playwright/; const ok = re.test('x'); return ok; });",
  ].join('\n');
  assert.ok(!detectRealE2eKindsInTest('test/regex-browser.test.mjs', regexBrowser).includes('browser-playwright'));

  const regexSkipLint = lintValidationCode({
    path: 'src/detector.mjs',
    kind: 'code',
    text: 'export function check(s) { return /\\blocalSkipRow\\b/i.test(s); }\n',
  });
  assert.equal(regexSkipLint.ok, true, 'regex literal /localSkipRow/ must not trigger silent-validation-skip');

  // 2. Template ${...} expressions are scanned as real code
  const tmplScanned = scanJsPreserveLines('const out = `val=${localSkipRow(row)}`;\n');
  assert.match(tmplScanned.codeNoStrings, /\blocalSkipRow\b/, 'template ${...} expression must remain visible in codeNoStrings');
  const tmplSkipLint = lintValidationCode({
    path: 'src/tmpl-skip.mjs',
    kind: 'code',
    text: 'export const run = (row) => `ok:${localSkipRow(row)}`;\n',
  });
  assert.ok(tmplSkipLint.codes.includes('silent-validation-skip'), 'localSkipRow inside template ${...} must be caught');

  // 3. Trivial spawnSync('echo', ...) must NOT grant subprocess-cli or live-binding; real gcloud invocation DOES
  const echoTest = [
    "import { spawnSync } from 'node:child_process';",
    "import { deploy } from '../src/gcloud-deploy.mjs';",
    "spawnSync('echo', ['hi']);",
    "spawnSync('echo', ['gcloud']);",
    'deploy();',
  ].join('\n');
  const echoKinds = detectRealE2eKindsInTest('test/gcloud-fake.test.mjs', echoTest);
  assert.ok(!echoKinds.includes('live-binding'), 'spawnSync(echo) must NOT grant live-binding');
  assert.ok(!echoKinds.includes('subprocess-cli'), 'spawnSync(echo) must NOT grant subprocess-cli');

  const realGcloudTest = [
    "import { execFileSync } from 'node:child_process';",
    "execFileSync('gcloud', ['auth', 'list']);",
  ].join('\n');
  const realKinds = detectRealE2eKindsInTest('test/gcloud-real.test.mjs', realGcloudTest);
  assert.ok(realKinds.includes('live-binding'), 'real gcloud subprocess grants live-binding');
  assert.ok(realKinds.includes('subprocess-cli'), 'real gcloud subprocess grants subprocess-cli');

  // 4. Unexecuted E2E file MUST NOT be credited when testCommand runs only test/unit.test.mjs
  const wScope = await coreWorld(t, { settings: { mode: 'auto', runs: 1, testCommand: 'node --test test/unit.test.mjs' } });
  wScope.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  wScope.issue(43, { title: 'Add orders endpoint' });
  await wScope.tick();
  const cwd43 = wScope.job(43, 'build').cwd;
  writeIn(cwd43, 'api/orders.mjs', 'export const handleOrders = () => ({ ok: true });\n');
  writeIn(cwd43, 'test/unit.test.mjs', "import test from 'node:test';\ntest('unit only', () => {});\n");
  writeIn(
    cwd43,
    'test/orders-e2e.test.mjs',
    [
      "import http from 'node:http';",
      "import { handleOrders } from '../api/orders.mjs';",
      'const s = http.createServer((req, res) => res.end(JSON.stringify(handleOrders())));',
      's.listen(0);',
      '',
    ].join('\n'),
  );
  const { pr: pr43 } = wScope.build(43, {
    write: false,
    body: 'Fixes #43\n\nRuntime: not run (no prompt changed)\nPath: d — api/orders.mjs, test/unit.test.mjs, test/orders-e2e.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wScope.tick();
  wScope.review(43, 'PASS');
  await wScope.tick(); // #3554 defers suiteState until review PASS because PR edits test/unit.test.mjs referenced by testCommand.
  wScope.suite(43, 0);
  await wScope.tick();
  assert.equal(wScope.github.merges.length, 0, 'unexecuted test/orders-e2e.test.mjs must NOT be credited when testCommand only runs test/unit.test.mjs');
  assert.ok(
    pr43.comments.some((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body)),
    'unexecuted E2E fails closed at Bucket 3 instead of merging',
  );

  // 5. Changing 2 runtime-code files (src/a.mjs + src/b.mjs) with tests covering only src/a.mjs MUST fail closed
  const wPartial = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wPartial.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  wPartial.issue(44, { title: 'Update two runtime modules' });
  await wPartial.tick();
  const cwd44 = wPartial.job(44, 'build').cwd;
  writeIn(cwd44, 'src/a.mjs', 'export const a = () => 1;\n');
  writeIn(cwd44, 'src/b.mjs', 'export const b = () => 2;\n');
  writeIn(cwd44, 'test/a.test.mjs', "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { a } from '../src/a.mjs';\ntest('a', () => assert.equal(a(), 1));\n");
  const { pr: pr44 } = wPartial.build(44, {
    write: false,
    body: 'Fixes #44\n\nRuntime: not run (no prompt changed)\nPath: d — src/a.mjs, src/b.mjs, test/a.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wPartial.tick();
  wPartial.review(44, 'PASS');
  wPartial.suite(44, 0);
  await wPartial.tick();
  assert.equal(wPartial.github.merges.length, 0, '1 of 2 changed src/*.mjs files untested must fail closed');
  assert.ok(
    pr44.comments.some((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body)),
    'untested second runtime-code file fails closed instead of merging',
  );
});

test('R2-2 (MF-3): multi-Story pr.body real-binding-unavailable parks when Story A passes and Story B is unverified, and coverage rows preserve reason/codes', async (t) => {
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.runtimeEvidence = () => ({
    stories: [
      { story: 'user_stories/a.md', pass: true, current: true, at: '2026-11-18T10:00:00Z', tests: ['test/a.json'], reason: null, codes: [] },
    ],
    storyFiles: ['user_stories/a.md', 'user_stories/b.md'],
    tests: [],
  });
  w.issue(45, { title: 'Multi-story change with binding unavailable on B' });
  await w.tick();
  const cwd45 = w.job(45, 'build').cwd;
  writeIn(cwd45, 'user_stories/a.md', '# Story A\n');
  writeIn(cwd45, 'user_stories/b.md', '# Story B\n');
  writeIn(cwd45, 'src/multi.mjs', 'export const m = 1;\n');
  writeIn(cwd45, 'test/multi.test.mjs', "import test from 'node:test';\nimport { m } from '../src/multi.mjs';\ntest('m', () => { if (m !== 1) throw new Error(); });\n");
  w.build(45, {
    write: false,
    body: [
      'Fixes #45',
      '',
      'Runtime: PASS (user_stories/a.md, 4/4 checks)',
      'Runtime: not run (user_stories/b.md: real-binding-unavailable)',
      'Path: d — user_stories/a.md, user_stories/b.md, src/multi.mjs, test/multi.test.mjs — unowned — no contract change — Test: done check',
    ].join('\n'),
    result: { promptChanged: true },
  });
  await w.tick();
  assert.equal(w.github.merges.length, 0, 'Story A passing must NOT let Story B real-binding-unavailable merge');
  const machine = JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
  assert.equal(machine.validationParks?.length, 1, 'PR parked at Bucket 2 for unverified Story B');
  assert.deepEqual(machine.validationParks[0].parkStories, ['user_stories/b.md']);
  assert.equal(machine.toolCooldowns?.['runtime-binding']?.active, true);

  // Verify job.coverage.rows preserves reason & codes (when runtimeCoverage records rows)
  const wCov = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wCov.runtimeEvidence = () => ({
    stories: [
      { story: 'user_stories/a.md', pass: true, current: true, at: '2026-11-18T10:00:00Z', reason: 'verified-live', codes: ['ok-live'] },
    ],
    storyFiles: ['user_stories/a.md'],
    tests: [],
  });
  wCov.issue(46, { title: 'Check coverage row fields' });
  await wCov.tick();
  const cwd46 = wCov.job(46, 'build').cwd;
  writeIn(cwd46, 'user_stories/a.md', '# Story A\n');
  wCov.build(46, {
    write: false,
    body: 'Fixes #46\n\nRuntime: PASS (user_stories/a.md, 1/1 checks)\nPath: d — user_stories/a.md — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wCov.tick();
  const job46 = JSON.parse(readFileSync(join(wCov.root, 'jobs', '46.json'), 'utf8'));
  assert.equal(job46.coverage?.rows?.[0]?.reason, 'verified-live', 'job.coverage.rows preserves reason');
  assert.deepEqual(job46.coverage?.rows?.[0]?.codes, ['ok-live'], 'job.coverage.rows preserves codes');
});

test('R2-3 (MF-4): resume cleans stale not-run line after bindingRerun, preserves needs-decision on claim failure, undoes claim on worktree failure, and never spawns zero-arg pdd test', async (t) => {
  // Part 1: Resuming real-binding-unavailable runs bindingRerun BEFORE syncVerifiedRuntimeLines and replaces stale not-run line with PASS
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  let bindingRestored = false;
  w.runtimeEvidence = () => ({
    stories: bindingRestored
      ? [{ story: 'user_stories/live.md', pass: true, current: true, at: '2026-11-18T11:00:00Z', passed: 3, total: 3 }]
      : [{ story: 'user_stories/live.md', pass: false, current: true, at: '2026-11-18T10:00:00Z', reason: 'real-binding-unavailable', codes: ['real-binding-unavailable'] }],
    storyFiles: ['user_stories/live.md'],
    tests: [],
  });
  w.issue(47, { title: 'Clean stale not-run line on resume' });
  await w.tick();
  const cwd47 = w.job(47, 'build').cwd;
  writeIn(cwd47, 'user_stories/live.md', '# Live\n');
  writeIn(cwd47, 'src/live-op.mjs', 'export const liveOp = () => 1;\n');
  writeIn(cwd47, 'test/live-op.test.mjs', "import test from 'node:test';\nimport { liveOp } from '../src/live-op.mjs';\ntest('live', () => { if (liveOp() !== 1) throw new Error(); });\n");
  const built47 = w.build(47, {
    write: false,
    body: 'Fixes #47\n\nRuntime: not run (user_stories/live.md: real-binding-unavailable)\nPath: d — user_stories/live.md, src/live-op.mjs, test/live-op.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await w.tick();
  const parkedMachine = JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
  assert.equal(parkedMachine.validationParks?.length, 1);

  // Resume via healthy preflight; rerunRuntimeBinding restores binding before syncVerifiedRuntimeLines runs
  await w.tick({
    preflightCheck: async () => ({ exitCode: 0 }),
    rerunRuntimeBinding: async () => { bindingRestored = true; },
  });
  assert.doesNotMatch(built47.pr.body, /real-binding-unavailable/i, 'stale Runtime: not run line must be replaced after bindingRerun passes');
  assert.match(built47.pr.body, /Runtime: PASS \(user_stories\/live\.md/, 'PR body must be updated to verified Runtime: PASS');
  w.review(47, 'PASS');
  w.suite(47, 0);
  await w.tick();
  assert.equal(w.github.merges.length, 1, 'cleaned PR merges without looping back to Bucket 2');

  // Part 2: Failed claimIssue leaves pdd:needs-decision and validationPark intact
  const wClaimFail = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wClaimFail.issue(48, { title: 'Keep needs-decision if claim fails' });
  await wClaimFail.tick();
  writeIn(wClaimFail.job(48, 'build').cwd, 'docs/c.md', '# C\n');
  wClaimFail.build(48, {
    write: false,
    body: 'Fixes #48\n\nRuntime: not run (no prompt changed)',
    result: { promptChanged: false },
  });
  await wClaimFail.tick();
  wClaimFail.say(48, 'suite', 'ERROR: (gcloud.run.deploy) Reauthentication required. Run: gcloud auth login\n');
  wClaimFail.suite(48, 1);
  await wClaimFail.tick();
  assert.ok(wClaimFail.labels(48).includes('pdd:needs-decision'));
  // Simulate another coordinator claiming #48 before our resume attempt
  wClaimFail.github.claim(48, { coordinatorId: 'other-coord', machine: 'other-host' });
  await wClaimFail.tick({ preflightCheck: async () => ({ exitCode: 0 }) });
  assert.ok(wClaimFail.labels(48).includes('pdd:needs-decision'), 'pdd:needs-decision must stay intact when claimIssue fails');
  const mClaimFail = JSON.parse(readFileSync(join(wClaimFail.root, 'core.json'), 'utf8'));
  assert.equal(mClaimFail.validationParks?.length, 1, 'park must stay intact when claimIssue fails');

  // Part 3: Failed git worktree add undoes claim, keeps park and pdd:needs-decision intact
  const wWtFail = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wWtFail.issue(49, { title: 'Undo claim if worktree add fails' });
  await wWtFail.tick();
  writeIn(wWtFail.job(49, 'build').cwd, 'docs/w.md', '# W\n');
  wWtFail.build(49, {
    write: false,
    body: 'Fixes #49\n\nRuntime: not run (no prompt changed)',
    result: { promptChanged: false },
  });
  await wWtFail.tick();
  wWtFail.say(49, 'suite', 'ERROR: (gcloud.run.deploy) Reauthentication required. Run: gcloud auth login\n');
  wWtFail.suite(49, 1);
  await wWtFail.tick();
  rmSync(join(wWtFail.root, 'worktrees', '49'), { recursive: true, force: true });
  await wWtFail.tick({
    preflightCheck: async () => ({ exitCode: 0 }),
    git: async (args, opts) => {
      if (args[0] === 'worktree' && args[1] === 'add') {
        throw new Error('fatal: simulated worktree add failure');
      }
      return wWtFail.git(args, opts);
    },
  });
  assert.equal(existsSync(join(wWtFail.root, 'jobs', '49.json')), false, 'no broken resumed job saved when worktree add fails');
  assert.ok(wWtFail.labels(49).includes('pdd:needs-decision'), 'pdd:needs-decision stays intact on worktree add failure');
  assert.ok(!wWtFail.labels(49).includes('pdd:working'), 'claim is undone when worktree add fails');
  const mWtFail = JSON.parse(readFileSync(join(wWtFail.root, 'core.json'), 'utf8'));
  assert.equal(mWtFail.validationParks?.length, 1, 'park stays intact when worktree add fails');

  // Part 4: Empty parkStories never spawns repo-wide zero-arg `pdd test --json`
  const wNoZeroArg = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wNoZeroArg.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  wNoZeroArg.issue(50, { title: 'Never spawn empty-args pdd test' });
  await wNoZeroArg.tick();
  writeIn(wNoZeroArg.job(50, 'build').cwd, 'docs/no-args.md', '# Docs\n');
  const built50 = wNoZeroArg.build(50, {
    write: false,
    body: 'Fixes #50\n\nRuntime: not run (no prompt changed)',
    result: { promptChanged: false },
  });
  const jobPath50 = join(wNoZeroArg.root, 'jobs', '50.json');
  const job50 = JSON.parse(readFileSync(jobPath50, 'utf8'));
  job50.bindingRerun = { head: built50.head, stories: [], state: 'pending', agent: null };
  writeFileSync(jobPath50, JSON.stringify(job50, null, 2));
  const startedBefore = wNoZeroArg.started.length;
  await wNoZeroArg.tick();
  const runtimeStarts = wNoZeroArg.started.slice(startedBefore).filter((j) => j.role === 'runtime');
  assert.equal(runtimeStarts.length, 0, 'empty parkStories with no story targets must NEVER spawn zero-arg repo-wide pdd test --json');
});

test('R2-4 (MF-5): node:test describe headers (▶), multiline assertion diffs, and test at/stack frames do NOT misclassify as Bucket 2/3', async (t) => {
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.issue(51, { title: 'Unit test failure mentioning Bucket 2/3 keywords in header and diff' });
  await w.tick();
  const cwd51 = w.job(51, 'build').cwd;
  writeIn(cwd51, 'src/parser.mjs', 'export const parse = () => "ok";\n');
  writeIn(cwd51, 'test/parser.test.mjs', "import test from 'node:test';\nimport { parse } from '../src/parser.mjs';\ntest('parse', () => parse());\n");
  const { pr } = w.build(51, {
    write: false,
    body: 'Fixes #51\n\nRuntime: not run (no prompt changed)\nPath: d — src/parser.mjs, test/parser.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await w.tick();
  w.say(51, 'suite', [
    '▶ Bucket 3: 2FA and captcha handling',
    '  ✖ maps real-binding-unavailable correctly (1.2ms)',
    '    AssertionError [ERR_ASSERTION]: Expected values to be strictly equal:',
    '',
    "    'real-binding-unavailable' !== 'ok'",
    '        at TestContext.<anonymous> (file:///repo/test/parser.test.mjs:42:10)',
    '  test at test/parser.test.mjs:40:1',
    "  location: 'test/parser.test.mjs:40:1'",
    "  failureType: 'testCodeFailure'",
    "  code: 'ERR_ASSERTION'",
    '  stack: |-',
    '    TestContext.<anonymous> (file:///repo/test/parser.test.mjs:42:10)',
  ].join('\n'));
  w.review(51, 'PASS');
  w.suite(51, 1);
  await w.tick();
  assert.ok(w.job(51, 'repair'), 'unit test failure enters Bucket 1 repair instead of Bucket 2/3');
  assert.ok(!pr.comments.some((c) => /<!-- pdd:autopilot-core:(?:auth-wait|human-boundary):/.test(c.body)), 'must not post auth-wait or human-boundary comment');
  const machine = JSON.parse(readFileSync(join(w.root, 'core.json'), 'utf8'));
  assert.equal(machine.validationParks?.length ?? 0, 0, 'must not park in validationParks');
});

test('R2-5 (MF-6): multiline node:test { skip: true } caught by lintValidationCode and collectBacksideLint surfaces human-readable message', async (t) => {
  const multiSkipSrc = [
    "import test from 'node:test';",
    "test('e2e login flow', {",
    '  skip: true,',
    '}, () => {});',
    '',
  ].join('\n');
  const lint = lintValidationCode({ path: 'test/login-e2e.test.mjs', kind: 'test', text: multiSkipSrc });
  assert.equal(lint.ok, false, 'multiline { skip: true } must fail lint');
  assert.ok(lint.codes.includes('silent-validation-skip'));
  assert.match(lint.warnings[0], /test\/login-e2e\.test\.mjs:2 \[silent-validation-skip\]/);

  // Live coreWorld check: collectBacksideLint reads f.message (not bare code)
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.issue(52, { title: 'Check backside lint detail message' });
  await w.tick();
  const cwd52 = w.job(52, 'build').cwd;
  writeIn(cwd52, 'src/auth-helper.mjs', 'export const ok = () => true;\n');
  writeIn(cwd52, 'test/login-e2e.test.mjs', multiSkipSrc);
  w.build(52, {
    write: false,
    body: 'Fixes #52\n\nRuntime: not run (no prompt changed)\nPath: d — src/auth-helper.mjs, test/login-e2e.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await w.tick();
  w.review(52, 'PASS');
  w.suite(52, 0);
  await w.tick();
  const repair52 = w.job(52, 'repair');
  assert.ok(repair52, 'multiline silent skip triggers backside lint repair');
  assert.match(repair52.input, /\[silent-validation-skip\]\s+.*unconditionally skips/i, 'collectBacksideLint must surface f.message detail, not bare code');
});

test('R2-6 (MF-7 & MF-8 & Minor): suite repair cap 3 escalates to repair-exhausted preserved by closeOtherPrs, unknown/extensionless files fail closed, and symlinked rules/ parent is ignored', async (t) => {
  // 1. Unknown extensions & extensionless production files fail closed as runtime-code
  for (const filePath of ['foo.unknown', 'config.yaml', 'Makefile', 'src/worker.nim']) {
    const surf = detectChangedSurfaces({ changedFiles: [filePath] });
    assert.deepEqual(surf.surfaces, ['runtime-code'], `${filePath} must classify as runtime-code`);
    assert.equal(surf.docsOnly, false, `${filePath} must NOT be docsOnly`);
    assert.equal(surf.requiresRealE2e, true, `${filePath} must require real execution proof`);
    const verdict = evaluateValidationOutcome({ mode: 'auto', changedFiles: [filePath], offlinePassed: true, e2eChecks: [] });
    assert.equal(verdict.eligible, false, `${filePath} must fail closed without execution proof`);
  }

  // 2. Suite failure reaches Bucket 1 cap 3 -> needs-person (repair-exhausted) and closeOtherPrs preserves that PR
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1, repairs: 2 } });
  w.issue(53, { title: 'Persistent suite failure hits cap 3 repair-exhausted' });
  await w.tick();
  const cwd53 = w.job(53, 'build').cwd;
  writeIn(cwd53, 'src/flaky.mjs', 'export const v = () => 1;\n');
  writeIn(cwd53, 'test/flaky.test.mjs', "import test from 'node:test';\nimport { v } from '../src/flaky.mjs';\ntest('v', () => { if (v() !== 2) throw new Error('still broken'); });\n");
  const built53 = w.build(53, {
    write: false,
    body: 'Fixes #53\n\nRuntime: not run (no prompt changed)\nPath: d — src/flaky.mjs, test/flaky.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  for (let round = 1; round <= MAX_VALIDATION_REPAIRS; round += 1) {
    await w.tick();
    w.say(53, 'suite', 'Error: still broken\n');
    w.review(53, 'PASS');
    w.suite(53, 1);
    await w.tick();
    const rep = w.job(53, 'repair');
    assert.ok(rep, `suite failure round ${round} enters repair instead of pdd:stuck`);
    writeIn(rep.cwd, 'src/flaky.mjs', `export const v = () => ${round + 10};\n`);
    w.build(53, {
      role: 'repair',
      write: false,
      body: 'Fixes #53\n\nRuntime: not run (no prompt changed)\nPath: d — src/flaky.mjs, test/flaky.test.mjs — unowned — no contract change — Test: done check',
      result: { promptChanged: false },
    });
  }
  await w.tick();
  w.say(53, 'suite', 'Error: still broken\n');
  w.review(53, 'PASS');
  w.suite(53, 1);
  await w.tick();
  assert.equal(w.started.filter((j) => j.issue === 53 && j.role === 'repair').length, MAX_VALIDATION_REPAIRS, 'exactly 3 repair attempts run');
  assert.equal(built53.pr.state, 'open', 'repair-exhausted PR stays open');
  assert.ok(built53.pr.comments.some((c) => /<!-- pdd:autopilot-core:repair-exhausted:/.test(c.body)), 'PR gets repair-exhausted marker comment');
  assert.ok(w.labels(53).includes('pdd:needs-decision'), 'issue gets pdd:needs-decision');
  assert.ok(!w.labels(53).includes('pdd:stuck'), 'issue is escalated as needs-decision, not pdd:stuck');

  // Remove pdd:needs-decision so Autopilot starts a new branch for #53; closeOtherPrs MUST keep the repair-exhausted PR open!
  w.github.unlabel(53, 'pdd:needs-decision');
  await w.tick();
  assert.equal(built53.pr.state, 'open', 'closeOtherPrs must preserve PRs with repair-exhausted marker');

  // 3. CLI hasWorkspaceLintRuleFiles ignores symlinked rules/ parent directory
  const repo = makeTempGitRepo(t, 'pdd-r2-rules-symlink-');
  const outside = mkdtempSync(join(tmpdir(), 'pdd-r2-outside-rules-'));
  t.after(() => rmSync(outside, { recursive: true, force: true }));
  writeFile(outside, 'lint/10-strict.json', JSON.stringify({ rules: { 'silent-validation-skip': 'error' } }));
  writeFile(repo, 'pdd.json', JSON.stringify({ name: 'demo' }));
  writeFile(repo, 'src/skip.mjs', "export function bad(err) { if (err === 'real-binding-unavailable') return { ok: true, skipped: true }; }\n");
  symlinkSync(outside, join(repo, 'rules'), 'dir');
  commitAll(repo, 'repo with symlinked rules parent');
  let symExit = 0;
  try {
    execFileSync(process.execPath, [join(process.cwd(), 'bin/pdd.mjs'), 'lint', '--local'], {
      cwd: repo,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
  } catch (err) {
    symExit = err.status ?? 1;
  }
  assert.equal(symExit, 0, 'symlinked rules/ parent directory must NOT load workspace lint rules');
});

test('R3-1: skipped or zero-pass suite logs fail closed and filePath-based silent skip lint catches untitled e2e skips', async (t) => {
  const realOrdersApi = 'export async function handleOrders(req, res) { res.end(JSON.stringify({ ok: true })); }\n';
  const realOrdersE2e = [
    "import test from 'node:test';",
    "import http from 'node:http';",
    "import { handleOrders } from '../api/orders.mjs';",
    "test('orders real http', async () => {",
    '  const srv = http.createServer(handleOrders);',
    '  await new Promise((r) => srv.listen(0, r));',
    '  const res = await fetch(`http://127.0.0.1:${srv.address().port}/orders`);',
    '  if (res.status !== 200) throw new Error("bad");',
    '  srv.close();',
    '});',
  ].join('\n');

  // (a) Skipped / zero-pass suite logs MUST fail closed (never merge)
  const badLogs = [
    { issue: 60, label: 'node TAP # pass 0 / # skipped 1', log: 'ok 1 - orders # SKIP\n# tests 1\n# pass 0\n# fail 0\n# skipped 1\n' },
    { issue: 61, label: 'TAP # SKIP line only', log: 'TAP version 13\nok 1 - orders real http # SKIP missing env\n' },
    { issue: 62, label: 'Vitest/Playwright 0 passed, 2 skipped', log: 'Tests: 0 passed, 2 skipped, 2 total\n' },
    { issue: 63, label: 'partial skip (1 passed, 1 skipped)', log: '# tests 2\n# pass 1\n# fail 0\n# skipped 1\n' },
  ];
  for (const { issue, label, log } of badLogs) {
    const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1, testCommand: 'node --test' } });
    w.issue(issue, { title: `R3-1 fail closed: ${label}` });
    await w.tick();
    const cwd = w.job(issue, 'build').cwd;
    writeIn(cwd, 'api/orders.mjs', realOrdersApi);
    writeIn(cwd, 'test/orders-e2e.test.mjs', realOrdersE2e);
    w.build(issue, {
      write: false,
      body: `Fixes #${issue}\n\nRuntime: not run (no prompt changed)\nPath: d — api/orders.mjs, test/orders-e2e.test.mjs — unowned — no contract change — Test: done check`,
      result: { promptChanged: false },
    });
    await w.tick();
    w.say(issue, 'suite', log);
    w.review(issue, 'PASS');
    w.suite(issue, 0);
    await w.tick();
    assert.equal(w.github.merges.length, 0, `${label}: skipped/zero-pass suite run must NOT merge`);
    assert.ok(w.job(issue, 'repair'), `${label}: skipped/zero-pass suite run must enter Bucket 1 repair`);
  }

  // (b) Passing test whose TITLE mentions "0 passed" / "2 skipped" must NOT false-positive
  const wPassTitle = await coreWorld(t, { settings: { mode: 'auto', runs: 1, testCommand: 'node --test' } });
  wPassTitle.issue(64, { title: 'R3-1 passing title containing skip words' });
  await wPassTitle.tick();
  const cwd64 = wPassTitle.job(64, 'build').cwd;
  writeIn(cwd64, 'api/orders.mjs', realOrdersApi);
  writeIn(cwd64, 'test/orders-e2e.test.mjs', realOrdersE2e);
  wPassTitle.build(64, {
    write: false,
    body: 'Fixes #64\n\nRuntime: not run (no prompt changed)\nPath: d — api/orders.mjs, test/orders-e2e.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wPassTitle.tick();
  wPassTitle.say(64, 'suite', 'ok 1 - rejects 0 passed and 2 skipped runs\n# tests 1\n# pass 1\n# fail 0\n# skipped 0\n');
  wPassTitle.review(64, 'PASS');
  wPassTitle.suite(64, 0);
  await wPassTitle.tick();
  assert.equal(wPassTitle.github.merges.length, 1, 'clean pass with skip words only inside test title must still merge');

  // (c) lintValidationCode checks SKIP_KEYWORD_RE against filePath as well as test(...) call snippet
  const e2eSkipSingle = lintValidationCode({
    path: 'test/orders-e2e.test.mjs',
    kind: 'test',
    text: "import test from 'node:test';\ntest.skip('runs login', () => {});\n",
  });
  assert.ok(e2eSkipSingle.codes.includes('silent-validation-skip'), 'test.skip inside *-e2e* file must be flagged even when title omits e2e');

  const e2eSkipMulti = lintValidationCode({
    path: 'test/checkout-validation.test.mjs',
    kind: 'test',
    text: "import test from 'node:test';\ntest('runs login', {\n  skip: true,\n}, () => {});\n",
  });
  assert.ok(e2eSkipMulti.codes.includes('silent-validation-skip'), 'multiline { skip: true } inside *validation* file must be flagged even when title omits validation');

  const unitSkip = lintValidationCode({
    path: 'test/math.test.mjs',
    kind: 'test',
    text: "import test from 'node:test';\ntest.skip('legacy rounding edge case', () => {});\n",
  });
  assert.ok(!unitSkip.codes.includes('silent-validation-skip'), 'plain non-e2e unit test skip without validation keywords must not false-positive');
});

test('R3-2: name/grep-filtered suite commands never credit unexecuted E2E files', async (t) => {
  const realOrdersApi = 'export async function handleOrders(req, res) { res.end(JSON.stringify({ ok: true })); }\n';
  const realOrdersE2e = [
    "import test from 'node:test';",
    "import http from 'node:http';",
    "import { handleOrders } from '../api/orders.mjs';",
    "test('orders real http', async () => {",
    '  const srv = http.createServer(handleOrders);',
    '  await new Promise((r) => srv.listen(0, r));',
    '  const res = await fetch(`http://127.0.0.1:${srv.address().port}/orders`);',
    '  if (res.status !== 200) throw new Error("bad");',
    '  srv.close();',
    '});',
  ].join('\n');

  const filteredCmds = [
    { issue: 65, cmd: 'node --test --test-name-pattern=unit' },
    { issue: 66, cmd: 'node --test --test-skip-pattern e2e' },
    { issue: 67, cmd: 'vitest run --grep=unit' },
    { issue: 68, cmd: 'npm test -- --test-name-pattern=unit' },
  ];
  for (const { issue, cmd } of filteredCmds) {
    const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1, testCommand: cmd } });
    w.issue(issue, { title: `R3-2 filtered suite: ${cmd}` });
    await w.tick();
    const cwd = w.job(issue, 'build').cwd;
    writeIn(cwd, 'api/orders.mjs', realOrdersApi);
    writeIn(cwd, 'test/orders-e2e.test.mjs', realOrdersE2e);
    const { pr } = w.build(issue, {
      write: false,
      body: `Fixes #${issue}\n\nRuntime: not run (no prompt changed)\nPath: d — api/orders.mjs, test/orders-e2e.test.mjs — unowned — no contract change — Test: done check`,
      result: { promptChanged: false },
    });
    await w.tick();
    w.say(issue, 'suite', 'ok 1 - unit\n# tests 1\n# pass 1\n# fail 0\n# skipped 0\n');
    w.review(issue, 'PASS');
    w.suite(issue, 0);
    await w.tick();
    assert.equal(w.github.merges.length, 0, `${cmd}: filtered run must NOT credit unexecuted test/orders-e2e.test.mjs`);
    assert.ok(
      pr.comments.some((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body)),
      `${cmd}: filtered run without real E2E coverage must fail closed at Bucket 3`,
    );
  }
});

test('R3-3 & R3-4: absolute-path trivial binaries do not grant subprocess/live-binding and regex literals after } are masked', () => {
  // R3-3: absolute-path trivial binaries and non-tool binary with tool keyword in args
  const absEcho = detectRealE2eKindsInTest(
    'test/deploy.test.mjs',
    "import { spawnSync } from 'node:child_process';\nspawnSync('/bin/echo', ['gcloud']);\n",
  );
  assert.ok(!absEcho.includes('subprocess-cli'), '/bin/echo must NOT grant subprocess-cli');
  assert.ok(!absEcho.includes('live-binding'), "/bin/echo ['gcloud'] must NOT grant live-binding");

  const absPrintf = detectRealE2eKindsInTest(
    'test/deploy.test.mjs',
    "import { execSync } from 'node:child_process';\nexecSync('/usr/bin/printf gcloud');\n",
  );
  assert.ok(!absPrintf.includes('subprocess-cli'), '/usr/bin/printf must NOT grant subprocess-cli');
  assert.ok(!absPrintf.includes('live-binding'), '/usr/bin/printf gcloud must NOT grant live-binding');

  const unrelatedToolArg = detectRealE2eKindsInTest(
    'test/deploy.test.mjs',
    "import { spawnSync } from 'node:child_process';\nspawnSync('/usr/local/bin/mytool', ['--tag=gcloud']);\n",
  );
  assert.ok(unrelatedToolArg.includes('subprocess-cli'), 'real non-trivial binary still grants subprocess-cli');
  assert.ok(!unrelatedToolArg.includes('live-binding'), 'non-external-tool binary with gcloud only in args must NOT grant live-binding');

  const realAbsGcloud = detectRealE2eKindsInTest(
    'test/deploy.test.mjs',
    "import { execFileSync } from 'node:child_process';\nexecFileSync('/usr/local/bin/gcloud', ['auth', 'list']);\n",
  );
  assert.ok(realAbsGcloud.includes('subprocess-cli'), '/usr/local/bin/gcloud grants subprocess-cli');
  assert.ok(realAbsGcloud.includes('live-binding'), '/usr/local/bin/gcloud grants live-binding');

  const shellWrappedGcloud = detectRealE2eKindsInTest(
    'test/deploy.test.mjs',
    "import { execSync } from 'node:child_process';\nexecSync('/bin/sh -c \"gcloud auth list\"');\n",
  );
  assert.ok(shellWrappedGcloud.includes('live-binding'), 'shell wrapper invoking gcloud still grants live-binding');

  // R3-4: regex literal immediately after closing brace `}` is masked as regex, not code
  const afterBraceSkip = 'if (ok) { run(); }\n/localSkipRow/.test(s);\n';
  assert.ok(!scanJsPreserveLines(afterBraceSkip).codeNoStrings.includes('localSkipRow'), 'regex after } must be masked by scanJsPreserveLines');
  assert.deepEqual(lintValidationCode({ path: 'src/helper.mjs', kind: 'code', text: afterBraceSkip }).codes, [], 'regex /localSkipRow/ after } must produce 0 findings');

  const afterBracePlaywright = 'if (ok) { run(); }\n/playwright/.test(s);\n';
  assert.ok(!detectRealE2eKindsInTest('test/ui.test.mjs', afterBracePlaywright).includes('browser-playwright'), 'regex /playwright/ after } must NOT grant browser-playwright');
});

test('R3-5: assertion diff context lines and Jest bullet titles do not misclassify as Bucket 2/3, while real gcloud errors still park Bucket 2', async (t) => {
  // (a) Jest ● title + assert.deepEqual unchanged object context line `reason: 'real-binding-unavailable',` -> Bucket 1 repair
  const w1 = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w1.issue(69, { title: 'R3-5 assertion diff context stays Bucket 1' });
  await w1.tick();
  const cwd69 = w1.job(69, 'build').cwd;
  writeIn(cwd69, 'src/widget.mjs', 'export const f = () => 1;\n');
  writeIn(cwd69, 'test/widget.test.mjs', "import test from 'node:test';\nimport { f } from '../src/widget.mjs';\ntest('f', () => { if (f() !== 2) throw new Error('mismatch'); });\n");
  const built69 = w1.build(69, {
    write: false,
    body: 'Fixes #69\n\nRuntime: not run (no prompt changed)\nPath: d — src/widget.mjs, test/widget.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await w1.tick();
  w1.say(69, 'suite', [
    '  ● Bucket 3 › 2FA and captcha handling',
    '',
    '  AssertionError [ERR_ASSERTION]: Expected values to be strictly deep-equal:',
    '  + actual - expected',
    '',
    '    {',
    '      pass: false,',
    "      reason: 'real-binding-unavailable',",
    '  +   count: 2',
    '  -   count: 1',
    '    }',
    '      at TestContext.<anonymous> (file:///repo/test/widget.test.mjs:10:5)',
    '',
  ].join('\n'));
  w1.review(69, 'PASS');
  w1.suite(69, 1);
  await w1.tick();
  assert.ok(w1.job(69, 'repair'), 'assertion diff context + Jest ● title must stay in Bucket 1 repair');
  const core1 = JSON.parse(readFileSync(join(w1.root, 'core.json'), 'utf8'));
  assert.equal((core1.validationParks ?? []).length, 0, 'no Bucket 2/3 park on assertion diff context');
  assert.ok(!built69.pr.comments.some((c) => /<!-- pdd:autopilot-core:(?:auth-wait|human-boundary):/.test(c.body)), 'no auth-wait or human-boundary comment');

  // (b) Earlier assertion diff followed by a REAL gcloud auth error -> still triggers Bucket 2
  const w2 = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w2.issue(70, { title: 'R3-5 real gcloud error after assertion diff still parks Bucket 2' });
  await w2.tick();
  const cwd70 = w2.job(70, 'build').cwd;
  writeIn(cwd70, 'src/deploy.mjs', 'export const deploy = () => true;\n');
  writeIn(cwd70, 'test/deploy.test.mjs', "import test from 'node:test';\nimport { deploy } from '../src/deploy.mjs';\ntest('deploy', () => { deploy(); });\n");
  const built70 = w2.build(70, {
    write: false,
    body: 'Fixes #70\n\nRuntime: not run (no prompt changed)\nPath: d — src/deploy.mjs, test/deploy.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await w2.tick();
  w2.say(70, 'suite', [
    '✖ unit check (1.0ms)',
    '  AssertionError [ERR_ASSERTION]: Expected values to be strictly deep-equal:',
    '  + actual - expected',
    '    {',
    "      reason: 'real-binding-unavailable',",
    '  +   ok: false',
    '  -   ok: true',
    '    }',
    '      at TestContext.<anonymous> (file:///repo/test/unit.test.mjs:10:5)',
    '',
    '✖ deploy e2e (50.0ms)',
    '  Error: ERROR: (gcloud.run.deploy) Reauthentication required. Please run `gcloud auth login`',
    '      at deploy (file:///repo/src/deploy.mjs:20:7)',
    '',
  ].join('\n'));
  w2.review(70, 'PASS');
  w2.suite(70, 1);
  await w2.tick();
  const core2 = JSON.parse(readFileSync(join(w2.root, 'core.json'), 'utf8'));
  assert.equal((core2.validationParks ?? []).length, 1, 'real gcloud auth error after assertion block must still park Bucket 2');
  assert.ok(built70.pr.comments.some((c) => /<!-- pdd:autopilot-core:auth-wait:/.test(c.body)), 'PR gets auth-wait comment');
});

test('R3-6 & polish: prior review repairs do not cut off Bucket 1 cap 3 into pdd:stuck, and coverage rows preserve object row.reason.code', async (t) => {
  // Part 1: 2 prior review-FAIL repairs (job.repairs = 2) with settings.repairs = 3, then 3 Bucket 1 suite repairs -> escalates to needs-decision (repair-exhausted), NEVER pdd:stuck
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1, repairs: 3 } });
  w.issue(71, { title: 'R3-6 prior review repairs do not starve Bucket 1 cap 3' });
  await w.tick();
  const cwd71 = w.job(71, 'build').cwd;
  writeIn(cwd71, 'src/service.mjs', 'export const svc = () => 1;\n');
  writeIn(cwd71, 'test/service.test.mjs', "import test from 'node:test';\nimport { svc } from '../src/service.mjs';\ntest('svc', () => { if (svc() !== 99) throw new Error('boom'); });\n");
  const built71 = w.build(71, {
    write: false,
    body: 'Fixes #71\n\nRuntime: not run (no prompt changed)\nPath: d — src/service.mjs, test/service.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });

  // Two prior review-FAIL repairs consume 2 of settings.repairs=3
  const reviewFindings = [
    'P1 src/service.mjs: rename alpha helper to match caller contract',
    'P1 src/service.mjs: guard against empty payload before parsing',
  ];
  for (let r = 0; r < reviewFindings.length; r += 1) {
    await w.tick();
    w.review(71, 'FAIL', [reviewFindings[r]]);
    w.suite(71, 0);
    await w.tick();
    const rep = w.job(71, 'repair');
    assert.ok(rep, `review-FAIL round ${r + 1} enters repair`);
    writeIn(rep.cwd, 'src/service.mjs', `export const svc = () => ${r + 2};\n`);
    w.build(71, {
      role: 'repair',
      write: false,
      body: 'Fixes #71\n\nRuntime: not run (no prompt changed)\nPath: d — src/service.mjs, test/service.test.mjs — unowned — no contract change — Test: done check',
      result: { promptChanged: false },
    });
  }

  // Now review PASSes and suite fails: all 3 Bucket 1 validation repair attempts must run (job.repairs goes 2 -> 5) before repair-exhausted escalation
  for (let round = 1; round <= MAX_VALIDATION_REPAIRS; round += 1) {
    await w.tick();
    w.say(71, 'suite', 'Error: boom\n');
    w.review(71, 'PASS');
    w.suite(71, 1);
    await w.tick();
    const rep = w.job(71, 'repair');
    assert.ok(rep, `validation failure round ${round} enters repair instead of cutting off into pdd:stuck`);
    assert.ok(!w.labels(71).includes('pdd:stuck'), `round ${round} must NOT mark pdd:stuck`);
    writeIn(rep.cwd, 'src/service.mjs', `export const svc = () => ${round + 20};\n`);
    w.build(71, {
      role: 'repair',
      write: false,
      body: 'Fixes #71\n\nRuntime: not run (no prompt changed)\nPath: d — src/service.mjs, test/service.test.mjs — unowned — no contract change — Test: done check',
      result: { promptChanged: false },
    });
  }

  // 4th suite failure exceeds cap 3 -> repair-exhausted (pdd:needs-decision, NOT pdd:stuck)
  await w.tick();
  w.say(71, 'suite', 'Error: boom\n');
  w.review(71, 'PASS');
  w.suite(71, 1);
  await w.tick();
  assert.equal(w.started.filter((j) => j.issue === 71 && j.role === 'repair').length, 2 + MAX_VALIDATION_REPAIRS, '2 review repairs + 3 validation repairs ran');
  assert.ok(w.labels(71).includes('pdd:needs-decision'), 'cap 3 escalates to pdd:needs-decision');
  assert.ok(!w.labels(71).includes('pdd:stuck'), 'cap 3 must NEVER label pdd:stuck');
  assert.ok(built71.pr.comments.some((c) => /<!-- pdd:autopilot-core:repair-exhausted:/.test(c.body)), 'PR gets repair-exhausted comment');

  // Part 2: job.coverage.rows preserves object row.reason.code (for both passing rows and real-binding-unavailable blockers)
  const wCov = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wCov.runtimeEvidence = () => ({
    stories: [
      { story: 'user_stories/obj-reason.md', pass: true, current: true, at: '2026-11-18T10:00:00Z', reason: { code: 'verified-live-obj', message: 'ok' } },
    ],
    storyFiles: ['user_stories/obj-reason.md'],
    tests: [],
  });
  wCov.issue(72, { title: 'Preserve object row.reason.code' });
  await wCov.tick();
  const cwd72 = wCov.job(72, 'build').cwd;
  writeIn(cwd72, 'user_stories/obj-reason.md', '# Story\n');
  wCov.build(72, {
    write: false,
    body: 'Fixes #72\n\nRuntime: PASS (user_stories/obj-reason.md, 1/1 checks)\nPath: d — user_stories/obj-reason.md — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wCov.tick();
  const job72 = JSON.parse(readFileSync(join(wCov.root, 'jobs', '72.json'), 'utf8'));
  assert.equal(job72.coverage?.rows?.[0]?.reason, 'verified-live-obj', 'job.coverage.rows preserves object row.reason.code');
});

test('R4 sync regression: package.json manifest is covered by executed real tests without excusing uncovered src modules or zero-test repos', async (t) => {
  // 1. package.json + covered src/a.mjs + real test passes Validator v2
  const wOk = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wOk.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  wOk.issue(73, { title: 'Add package.json and tested module' });
  await wOk.tick();
  const cwd73 = wOk.job(73, 'build').cwd;
  writeIn(cwd73, 'package.json', JSON.stringify({ name: 'demo', type: 'module', scripts: { test: 'node --test' } }, null, 2) + '\n');
  writeIn(cwd73, 'src/a.mjs', 'export const a = () => 1;\n');
  writeIn(cwd73, 'test/a.test.mjs', "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { a } from '../src/a.mjs';\ntest('a', () => assert.equal(a(), 1));\n");
  wOk.build(73, {
    write: false,
    body: 'Fixes #73\n\nRuntime: not run (no prompt changed)\nPath: d — package.json, src/a.mjs, test/a.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wOk.tick();
  wOk.review(73, 'PASS');
  await wOk.tick(); // #3554 defers suiteState until review PASS because PR modifies package.json.
  wOk.suite(73, 0);
  await wOk.tick();
  assert.equal(wOk.github.merges.length, 1, 'package.json + covered src/a.mjs + real test merges cleanly');

  // 2. package.json + covered src/a.mjs + UNCOVERED src/b.mjs MUST still fail closed
  const wPartial = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wPartial.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  wPartial.issue(74, { title: 'Manifest with one uncovered module' });
  await wPartial.tick();
  const cwd74 = wPartial.job(74, 'build').cwd;
  writeIn(cwd74, 'package.json', JSON.stringify({ name: 'demo', type: 'module', scripts: { test: 'node --test' } }, null, 2) + '\n');
  writeIn(cwd74, 'src/a.mjs', 'export const a = () => 1;\n');
  writeIn(cwd74, 'src/b.mjs', 'export const b = () => 2;\n');
  writeIn(cwd74, 'test/a.test.mjs', "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { a } from '../src/a.mjs';\ntest('a', () => assert.equal(a(), 1));\n");
  const { pr: pr74 } = wPartial.build(74, {
    write: false,
    body: 'Fixes #74\n\nRuntime: not run (no prompt changed)\nPath: d — package.json, src/a.mjs, src/b.mjs, test/a.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wPartial.tick();
  wPartial.review(74, 'PASS');
  await wPartial.tick(); // #3554 defers suiteState until review PASS because PR modifies package.json.
  wPartial.suite(74, 0);
  await wPartial.tick();
  assert.equal(wPartial.github.merges.length, 0, 'manifest coverage must NOT excuse uncovered src/b.mjs');
  assert.ok(pr74.comments.some((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body)));

  // 3. package.json alone with ZERO real tests MUST still fail closed
  const wEmpty = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  wEmpty.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  wEmpty.issue(75, { title: 'Manifest edit with zero tests' });
  await wEmpty.tick();
  const cwd75 = wEmpty.job(75, 'build').cwd;
  writeIn(cwd75, 'package.json', JSON.stringify({ name: 'demo', type: 'module', scripts: { test: 'node --test' } }, null, 2) + '\n');
  const { pr: pr75 } = wEmpty.build(75, {
    write: false,
    body: 'Fixes #75\n\nRuntime: not run (no prompt changed)\nPath: d — package.json — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await wEmpty.tick();
  wEmpty.review(75, 'PASS');
  await wEmpty.tick(); // #3554 defers suiteState until review PASS because PR modifies package.json.
  wEmpty.suite(75, 0);
  await wEmpty.tick();
  assert.equal(wEmpty.github.merges.length, 0, 'manifest-only change with zero real tests fails closed');
  assert.ok(pr75.comments.some((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body)));
});

test('3574 Part 4: native-only and os-boundary modules require non-mocked real-host smoke in both auto and observe modes', () => {
  const surf = detectChangedSurfaces({
    changedFiles: ['src/trust/service.mjs', 'src/os-sandbox.mjs'],
    nativeOnlyFiles: ['src/trust/service.mjs'],
  });
  assert.ok(surf.surfaces.includes('native-only'));
  assert.ok(surf.surfaces.includes('os-boundary'));
  assert.ok(surf.requiredProofKinds.includes('real-host-smoke'));

  for (const mode of ['auto', 'observe']) {
    const blocked = evaluateValidationOutcome({
      mode,
      changedFiles: ['src/trust/service.mjs'],
      nativeOnlyFiles: ['src/trust/service.mjs'],
      offlinePassed: true,
      offlineSummary: 'unit 4/4',
      e2eChecks: [{
        kind: 'real-execution',
        command: 'node --test test/trust-unit.test.mjs',
        executed: true,
        exitCode: 0,
        passed: 4,
        failed: 0,
        skipped: 0,
      }],
    });
    assert.equal(blocked.bucket, 3, `${mode}: in-process unit check must not satisfy native-only real-host gate`);
    assert.equal(blocked.decision, 'needs-person', `${mode}: fails closed`);
    assert.equal(blocked.waitKind, 'needs-real-host-smoke', `${mode}: reports needs-real-host-smoke`);
    assert.equal(blocked.eligible, false, `${mode}: never eligible`);

    const passed = evaluateValidationOutcome({
      mode,
      changedFiles: ['src/trust/service.mjs'],
      nativeOnlyFiles: ['src/trust/service.mjs'],
      offlinePassed: true,
      e2eChecks: [{
        kind: 'real-host-smoke',
        command: 'node --test test/trust-smoke.test.mjs --live-local',
        executed: true,
        exitCode: 0,
        passed: 2,
        failed: 0,
        skipped: 0,
      }],
    });
    assert.equal(passed.bucket, 1, `${mode}: real-host-smoke passes`);
    assert.equal(passed.decision, mode === 'observe' ? 'allow-would-merge' : 'allow-merge');
    assert.equal(passed.eligible, true);
  }
});
