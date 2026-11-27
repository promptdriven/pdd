import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join } from 'node:path';
import { performance } from 'node:perf_hooks';
import {
  MIN_REALISTIC_PAYLOAD_BYTES,
  REAL_HOST_FAILURE_CLASSES,
  detectChangedSurfaces,
  detectNativeOnlyModules,
  evaluateValidationOutcome,
} from '../src/autopilot-validator.mjs';
import { lintRepoProject } from '../src/repo-hygiene-lint.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { coreWorld } from './helpers/core-world.mjs';
import { sink } from './helpers/runtime-fake.mjs';

function makeTempGitRepo(t, prefix = 'pdd-3574-') {
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

test('3574 Part 4: detectNativeOnlyModules resolves native-only ownership via bindings, headers, and opening prose claims in O(N) time', () => {
  const prompts = [
    {
      path: 'prompts/trust/service.prompt.md',
      content: '---\nkind: native-only\nreason: Real SQLite + HTTP boundary.\n---\n\n# Trust service\n\nOwn `src/trust/prose-owned.mjs`.\n',
    },
    {
      path: 'prompts/calc.prompt.md',
      content: '# Calc\n\nOwn `src/calc.mjs`.\n',
    },
  ];
  const bindings = JSON.stringify({
    schema_version: 'pdd.bindings.v1',
    modules: [
      { module: 'src/trust/bound.mjs', stories: [], prompt: 'prompts/trust/service.prompt.md' },
      { module: 'src/calc.mjs', stories: [], prompt: 'prompts/calc.prompt.md' },
    ],
  });
  const fileHeads = [
    { path: 'src/trust/headed.mjs', content: `// Generated from prompts/trust/service.prompt.md (sha256: ${'0'.repeat(64)}).\nexport {};\n` },
    { path: 'src/calc.mjs', content: '// Prompt: prompts/calc.prompt.md\nexport {};\n' },
  ];

  const found = detectNativeOnlyModules({
    changedFiles: [
      'src/trust/bound.mjs',
      'src/trust/headed.mjs',
      'src/trust/prose-owned.mjs',
      'src/calc.mjs',
      'prompts/trust/service.prompt.md',
    ],
    promptFiles: prompts,
    bindings,
    fileHeads,
  });

  assert.deepEqual(found.nativeOnlyPrompts, ['prompts/trust/service.prompt.md']);
  assert.deepEqual(found.nativeOnlyModules, [
    'src/trust/bound.mjs',
    'src/trust/headed.mjs',
    'src/trust/prose-owned.mjs',
  ]);
  assert.deepEqual(
    found.matches.map((m) => [m.module, m.source]),
    [
      ['src/trust/bound.mjs', 'binding'],
      ['src/trust/headed.mjs', 'header'],
      ['src/trust/prose-owned.mjs', 'prose'],
    ],
  );

  // Linear O(N) performance on 40,000 blank lines in YAML frontmatter
  const hostileFrontmatter = `---\n${'\n'.repeat(40000)}kind: native-only\nreason: Perf check.\n---\n\n# Perf\n`;
  const t1 = performance.now();
  const fmDet = detectNativeOnlyModules({
    changedFiles: ['src/perf.mjs'],
    promptFiles: [{ path: 'prompts/perf.prompt.md', content: hostileFrontmatter }],
    fileHeads: [{ path: 'src/perf.mjs', content: '// Prompt: prompts/perf.prompt.md\n' }],
  });
  const fmMs1 = performance.now() - t1;
  assert.deepEqual(fmDet.nativeOnlyModules, ['src/perf.mjs']);
  assert.ok(fmMs1 < 100, `parseNativeOnlyPromptMeta took ${fmMs1.toFixed(1)}ms on 40k blank lines`);
});

test('3574 Part 4 policy: all 4 real-host OS/CLI failure classes, surface narrowing, and strictKind cross-surface isolation', () => {
  assert.equal(MIN_REALISTIC_PAYLOAD_BYTES, 4096);
  assert.deepEqual(REAL_HOST_FAILURE_CLASSES, [
    'nested-sandbox',
    'host-tty-ownership',
    'multi-turn-cli-state',
    'full-size-payload',
  ]);

  // Class 1: Nested OS sandbox execution
  const sandboxFail = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/os-sandbox.mjs'],
    offlinePassed: true,
    offlineSummary: 'unit 6/6',
    e2eChecks: [{ kind: 'unit-mock', command: 'node --test test/sandbox-prefix.test.mjs', executed: true, exitCode: 0, passed: 6, failed: 0, skipped: 0 }],
  });
  assert.equal(sandboxFail.bucket, 3);
  assert.equal(sandboxFail.decision, 'needs-person');
  assert.equal(sandboxFail.waitKind, 'needs-real-host-smoke');
  assert.equal(sandboxFail.eligible, false);
  assert.match(sandboxFail.humanVerificationCard[1], /nested OS sandbox/i);

  const sandboxPass = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/os-sandbox.mjs'],
    realHostClasses: ['nested-sandbox'],
    offlinePassed: true,
    e2eChecks: [{
      kind: 'real-host-smoke',
      command: 'node --test test/sandbox-live.test.mjs',
      executed: true,
      exitCode: 0,
      passed: 1,
      failed: 0,
      skipped: 0,
      realHostClasses: ['nested-sandbox'],
    }],
  });
  assert.equal(sandboxPass.bucket, 1);
  assert.equal(sandboxPass.decision, 'allow-merge');
  assert.equal(sandboxPass.eligible, true);

  // Class 2: Real host device/TTY ownership
  const ttyFail = evaluateValidationOutcome({
    mode: 'observe',
    changedFiles: ['src/tty-owner.mjs'],
    offlinePassed: true,
    e2eChecks: [{ kind: 'real-execution', command: 'node --test test/tty-mock.test.mjs', executed: true, exitCode: 0, passed: 2, failed: 0, skipped: 0 }],
  });
  assert.equal(ttyFail.bucket, 3);
  assert.equal(ttyFail.waitKind, 'needs-real-host-smoke');
  assert.equal(ttyFail.eligible, false);
  assert.match(ttyFail.humanVerificationCard[1], /\/dev\/tty/);

  const ttyPass = evaluateValidationOutcome({
    mode: 'observe',
    changedFiles: ['src/tty-owner.mjs'],
    realHostClasses: ['host-tty-ownership'],
    offlinePassed: true,
    e2eChecks: [{
      kind: 'real-host-smoke',
      command: 'node --test test/tty-live.test.mjs',
      executed: true,
      exitCode: 0,
      passed: 1,
      failed: 0,
      skipped: 0,
      realHostClasses: ['host-tty-ownership'],
    }],
  });
  assert.equal(ttyPass.bucket, 1);
  assert.equal(ttyPass.decision, 'allow-would-merge');
  assert.equal(ttyPass.eligible, true);

  // Class 3: Multi-turn real CLI state side effects (Turn 1 -> Turn 2; single-turn fails closed)
  const singleTurnOutcome = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/cli-session.mjs'],
    nativeOnlyFiles: ['src/cli-session.mjs'],
    realHostClasses: ['multi-turn-cli-state'],
    offlinePassed: true,
    e2eChecks: [{
      kind: 'subprocess-cli',
      command: 'node --test test/cli-session.test.mjs',
      executed: true,
      exitCode: 0,
      passed: 1,
      failed: 0,
      skipped: 0,
      turns: 1,
      realHostClasses: [],
    }],
  });
  assert.equal(singleTurnOutcome.bucket, 3);
  assert.equal(singleTurnOutcome.waitKind, 'needs-real-host-smoke');
  assert.match(singleTurnOutcome.message, /Turn 1 -> Turn 2/i);

  const multiTurnOutcome = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/cli-session.mjs'],
    nativeOnlyFiles: ['src/cli-session.mjs'],
    realHostClasses: ['multi-turn-cli-state'],
    offlinePassed: true,
    e2eChecks: [{
      kind: 'real-host-smoke',
      command: 'node --test test/cli-session-live.test.mjs --live-local',
      executed: true,
      exitCode: 0,
      passed: 2,
      failed: 0,
      skipped: 0,
      turns: 2,
      realHostClasses: ['multi-turn-cli-state'],
    }],
  });
  assert.equal(multiTurnOutcome.eligible, true);
  assert.equal(multiTurnOutcome.decision, 'allow-merge');

  // Class 4: Full-size realistic payload (> 4 KiB)
  const tinyOutcome = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/payload-preview.mjs'],
    nativeOnlyFiles: ['src/payload-preview.mjs'],
    realHostClasses: ['full-size-payload'],
    offlinePassed: true,
    e2eChecks: [{
      kind: 'real-host-smoke',
      command: 'node --test test/payload-tiny.test.mjs',
      executed: true,
      exitCode: 0,
      passed: 1,
      failed: 0,
      skipped: 0,
      payloadBytes: 256,
      realHostClasses: [],
    }],
  });
  assert.equal(tinyOutcome.bucket, 3);
  assert.equal(tinyOutcome.waitKind, 'needs-real-host-smoke');
  assert.match(tinyOutcome.message, /> 4096 bytes/);

  const fullOutcome = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/payload-preview.mjs'],
    nativeOnlyFiles: ['src/payload-preview.mjs'],
    realHostClasses: ['full-size-payload'],
    offlinePassed: true,
    e2eChecks: [{
      kind: 'real-host-smoke',
      command: 'node --test test/payload-full.test.mjs',
      executed: true,
      exitCode: 0,
      passed: 1,
      failed: 0,
      skipped: 0,
      payloadBytes: 12288,
      realHostClasses: ['full-size-payload'],
    }],
  });
  assert.equal(fullOutcome.eligible, true);
  assert.equal(fullOutcome.decision, 'allow-merge');

  // Surface narrowing & strictKind cross-surface isolation
  for (const ordinary of ['src/signal.mjs', 'src/namespace.mjs', 'src/fd-utils.mjs', 'src/exec.mjs', 'process/order.mjs', 'native/math.mjs']) {
    const s = detectChangedSurfaces({ changedFiles: [ordinary] });
    assert.deepEqual(s.surfaces, ['runtime-code'], `${ordinary} must stay runtime-code, got ${JSON.stringify(s.surfaces)}`);
  }
  assert.deepEqual(detectChangedSurfaces({ changedFiles: ['src/ui/card-preview.tsx'] }).realHostBoundaryClasses, []);
  assert.ok(detectChangedSurfaces({ changedFiles: ['src/truncate.mjs'], nativeOnlyFiles: ['src/truncate.mjs'] }).realHostBoundaryClasses.includes('full-size-payload'));
  assert.ok(detectChangedSurfaces({ changedFiles: ['bin/truncation-cli.mjs'] }).realHostBoundaryClasses.includes('full-size-payload'));

  const crossSurface = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['web/page.tsx', 'src/os-sandbox.mjs'],
    offlinePassed: true,
    e2eChecks: [{ kind: 'browser-playwright', command: 'npx playwright test', executed: true, exitCode: 0, passed: 3, failed: 0, skipped: 0 }],
  });
  assert.equal(crossSurface.bucket, 3);
  assert.equal(crossSurface.waitKind, 'needs-real-host-smoke');
  assert.equal(crossSurface.eligible, false);

  const strictBlockApiForNative = evaluateValidationOutcome({
    changedFiles: ['src/native.mjs', 'src/api-server.mjs'],
    nativeOnlyFiles: ['src/native.mjs'],
    offlinePassed: true,
    e2eChecks: [{ kind: 'local-server-or-db', strictKind: true, command: 'npm test', executed: true, exitCode: 0, passed: 1, failed: 0, skipped: 0 }],
  });
  assert.equal(strictBlockApiForNative.eligible, false);
  assert.equal(strictBlockApiForNative.waitKind, 'needs-real-host-smoke');
});

test('3574 Part 4 integration: Autopilot core fails closed on os-boundary and native-only PRs without explicit executed evidence (zero regex fabrication), and merges when real executed evidence is supplied', async (t) => {
  // 1. OS sandbox boundary PR without explicit executed evidence MUST fail closed (even when test source mentions sandbox-exec)
  const w1 = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w1.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  w1.issue(91, { title: 'Harden OS sandbox launcher' });
  await w1.tick();
  const buildCwd1 = w1.job(91, 'build').cwd;
  writeFile(buildCwd1, 'src/os-sandbox.mjs', 'export function launchArgs(cmd) { return ["sandbox-exec", ...cmd]; }\n');
  writeFile(
    buildCwd1,
    'test/os-sandbox-unit.test.mjs',
    "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { launchArgs } from '../src/os-sandbox.mjs';\ntest('prefix', () => assert.deepEqual(launchArgs(['a']), ['sandbox-exec', 'a']));\n",
  );
  const { pr: pr1 } = w1.build(91, {
    write: false,
    body: 'Fixes #91\n\nRuntime: not run (no prompt changed)\nPath: d — src/os-sandbox.mjs, test/os-sandbox-unit.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await w1.tick();
  w1.review(91, 'PASS');
  w1.suite(91, 0);
  await w1.tick();

  assert.equal(pr1.merged, false, 'os-boundary PR without explicit real-host evidence MUST fail closed');
  assert.ok(w1.labels(91).includes('pdd:needs-decision'), 'parks for person when real-host smoke is missing');
  assert.ok(
    pr1.comments.some((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body) && /nested OS sandbox/i.test(c.body)),
    'human verification card names missing nested OS sandbox real-host verification',
  );

  // 2. kind: native-only module PR with regex-only test source MUST fail closed, and merges once real executed evidence is supplied via validateE2e
  const w2 = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w2.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  w2.baseCommit('pdd-bindings.json', JSON.stringify({
    schema_version: 'pdd.bindings.v1',
    modules: [{ module: 'src/trust/store.mjs', prompt: 'prompts/trust/store.prompt.md' }],
  }, null, 2));
  w2.issue(102, { title: 'Update native-only trust store' });
  await w2.tick();
  const buildCwd2 = w2.job(102, 'build').cwd;
  writeFile(buildCwd2, 'prompts/trust/store.prompt.md', '---\nkind: native-only\nreason: Real SQLite adapter on host filesystem.\n---\n# Trust store\n\n## Dependencies\nNone.\n');
  writeFile(buildCwd2, 'src/trust/store.mjs', 'export function openTrustStore(db) { return db; }\n');
  writeFile(buildCwd2, 'test/trust-store-smoke.test.mjs', "import { DatabaseSync } from 'node:sqlite';\nexport const check = () => new DatabaseSync(':memory:');\n");
  const { pr: pr2 } = w2.build(102, {
    write: false,
    body: 'Fixes #102\n\nRuntime: not run (native-only prompt)\nPath: d — src/trust/store.mjs, test/trust-store-smoke.test.mjs — owned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await w2.tick();
  w2.review(102, 'PASS');
  w2.suite(102, 0);
  await w2.tick({
    validateE2e: async ({ nativeOnlyFiles }) => {
      assert.ok(nativeOnlyFiles.includes('src/trust/store.mjs'));
      return {
        offlinePassed: true,
        e2eChecks: [{
          kind: 'real-host-smoke',
          command: 'node --test test/trust-store-smoke.test.mjs --live-local',
          executed: true,
          exitCode: 0,
          passed: 1,
          failed: 0,
          skipped: 0,
          liveLocal: true,
        }],
      };
    },
  });
  assert.equal(pr2.merged, true, 'native-only PR with explicit executed real-host smoke evidence merges cleanly');

  // 3. Layer-1 lintRepoProject remains PDD-files-only (zero code-test noise)
  const repo = makeTempGitRepo(t, 'pdd-3574-native-lint-');
  writeFile(repo, 'prompts/trust/service.prompt.md', '---\nkind: native-only\nreason: Real SQLite adapter.\n---\n\n# Trust service\n\nOwn `src/trust/service.mjs`.\n\n## Dependencies\nNone.\n');
  writeFile(repo, 'src/trust/service.mjs', '// Prompt: prompts/trust/service.prompt.md\nexport function createTrustService(db) { return db; }\n');
  commitAll(repo, 'clean native-only service');
  const coreLint = lintRepoProject({ root: repo });
  assert.equal(coreLint.ok, true);
  assert.equal(coreLint.findings.some((f) => f.code === 'native-only-contract-incomplete'), false);
});

test('3574 docs & skills: prompting, product, and verification references define native-only contract and all 4 real-host classes without history words', () => {
  const promptingDoc = readFileSync(join(process.cwd(), 'skills/pdd/references/prompting.md'), 'utf8');
  const productDoc = readFileSync(join(process.cwd(), 'skills/pdd/references/product.md'), 'utf8');
  const verificationDoc = readFileSync(join(process.cwd(), 'skills/pdd/references/verification.md'), 'utf8');

  assert.match(promptingDoc, /## 3\. Dependency declarations and `kind: native-only`/);
  assert.match(promptingDoc, /Boundary & runtime contract/);
  assert.match(promptingDoc, /Error mapping & failure behavior/);
  assert.match(promptingDoc, /Real-host verification cases/);
  assert.match(promptingDoc, /complete executable boundary specification/i);
  assert.match(productDoc, /## 5\. `kind: native-only` boundary specs/);
  assert.match(productDoc, /prompting\.md#3-dependency-declarations-and-kind-native-only/);
  assert.doesNotMatch(productDoc, /thin\s+`kind: native-only`/i);

  for (const needle of [
    'nested OS sandbox',
    '/dev/tty',
    'multi-turn Turn 1 → Turn 2 CLI state',
    '4 KiB',
  ]) {
    assert.ok(verificationDoc.includes(needle), `skills/pdd/references/verification.md missing: ${needle}`);
  }

  for (const [name, content] of [
    ['skills/pdd/references/prompting.md', promptingDoc],
    ['skills/pdd/references/product.md', productDoc],
    ['skills/pdd/references/verification.md', verificationDoc],
  ]) {
    assert.doesNotMatch(content, /\b(?:no longer|used to|was renamed|moved to|since 0\.1|New in)\b/i, `${name} must use timeless current wording`);
  }
});

