import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import {
  MAX_VALIDATION_REPAIRS,
  detectChangedSurfaces,
  evaluateValidationOutcome,
  lintValidationCode,
  planValidationResume,
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
