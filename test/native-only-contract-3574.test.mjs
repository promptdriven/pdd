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
  detectRealE2eKindsInTest,
  detectRealHostProbesInTest,
  evaluateValidationOutcome,
  inspectTestBoundaryTargets,
  lintValidationCode,
} from '../src/autopilot-validator.mjs';
import {
  lintBoundaryMockOnlyTests,
  lintNativeOnlyContract,
  lintRepoProject,
} from '../src/repo-hygiene-lint.mjs';
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

test('3574 Part 1: lintNativeOnlyContract warns on thin stubs, passes complete specs, respects pdd.json overrides, and runs in O(N) time', async (t) => {
  const thinStub = [
    '---',
    'kind: native-only',
    'reason: Real SQLite adapter for trust access.',
    '---',
    '',
    '# Trust service',
    '',
    'Own `src/trust/service.mjs`. Adapts trust access.',
    '',
    '## Port wiring',
    '- `store.load`',
    '- `store.save`',
    '',
    '## Dependencies',
    '- [error handling](error-store.prompt.md)',
    '- [verification guide](verify-smoke.prompt.md)',
  ].join('\n');

  const stubWarnings = lintNativeOnlyContract(thinStub, { path: 'prompts/trust/service.prompt.md' });
  assert.equal(stubWarnings.length, 1, stubWarnings.join('\n'));
  assert.match(stubWarnings[0], /prompts\/trust\/service\.prompt\.md:1 \[native-only-contract-incomplete\]/);
  assert.match(stubWarnings[0], /boundary\/runtime contract/);
  assert.match(stubWarnings[0], /error mapping \/ failure behavior/);
  assert.match(stubWarnings[0], /real-host \/ native verification cases/);

  // Empty headings must not fool the contract check
  const emptyHeadingsStub = [
    '---',
    'kind: native-only',
    'reason: Real SQLite adapter.',
    '---',
    '',
    '# Trust service',
    '',
    '## Storage',
    '',
    '## Error mapping',
    '',
    '## Native verification',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');
  const emptyWarnings = lintNativeOnlyContract(emptyHeadingsStub, { path: 'prompts/trust/empty.prompt.md' });
  assert.equal(emptyWarnings.length, 1);
  assert.match(emptyWarnings[0], /boundary\/runtime contract/);
  assert.match(emptyWarnings[0], /error mapping \/ failure behavior/);
  assert.match(emptyWarnings[0], /real-host \/ native verification cases/);

  // Complete native-only prompt with DDL schema, locking, error mapping, and real-host smoke cases -> 0 warnings
  const completeSpec = [
    '---',
    'kind: native-only',
    'reason: Runs SQLite WAL storage, atomic locking, and HTTP routes.',
    '---',
    '',
    '# Trust service',
    '',
    'Own `src/trust/service.mjs`.',
    '',
    '## Storage & locking contract',
    '',
    '```sql',
    'CREATE TABLE trust_grants (',
    '  grant_id TEXT PRIMARY KEY,',
    '  subject_id TEXT NOT NULL,',
    '  revoked_at TEXT',
    ');',
    '```',
    '',
    'Open SQLite in WAL mode with `BEGIN IMMEDIATE` transactions and `busy_timeout=5000`.',
    '',
    '## Error mapping',
    '',
    'Map SQLite `SQLITE_BUSY` after timeout to HTTP 503 with retryable code; rollback failed writes atomically and fail closed on corrupt payloads.',
    '',
    '## Real-host verification cases',
    '',
    '- Real SQLite smoke test opening a file-backed DB on disk under concurrent writes (`node --test test/trust-sqlite-smoke.test.mjs`).',
    '- Real local HTTP route probe sending a 12 KiB payload (> 4 KiB) without truncation.',
    '',
    '## Dependencies',
    'None.',
  ].join('\n');
  assert.deepEqual(lintNativeOnlyContract(completeSpec, { path: 'prompts/trust/service.prompt.md' }), []);

  // Non-native-only prompts are unaffected
  assert.deepEqual(lintNativeOnlyContract('# Plain domain\n\nComputes subtotal.\n', { path: 'prompts/calc.prompt.md' }), []);

  // CLI pdd lint --local: default warn keeps exit 0, pdd.json error promotes to exit 1, off suppresses completely
  const scratch = mkdtempSync(join(tmpdir(), 'pdd-3574-contract-cli-'));
  t.after(() => rmSync(scratch, { recursive: true, force: true }));
  const repo = join(scratch, 'repo');
  const home = join(scratch, 'home');
  const state = join(scratch, 'state');
  mkdirSync(repo, { recursive: true });
  mkdirSync(home, { recursive: true });
  mkdirSync(state, { recursive: true });
  execFileSync('git', ['init', '-q', repo]);
  execFileSync('git', ['-C', repo, 'config', 'user.name', 'Test']);
  execFileSync('git', ['-C', repo, 'config', 'user.email', 'test@example.com']);
  writeFile(repo, 'prompts/trust/service.prompt.md', `${thinStub}\n`);
  commitAll(repo, 'thin native-only stub');
  const env = { HOME: home, PDD_STATE_DIR: state, PDD_RUNTIME_URL: 'invalid' };

  const warnOut = sink(), warnErr = sink();
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: warnOut, stderr: warnErr }), 0, warnErr.text);
  const warnParsed = JSON.parse(warnOut.text);
  assert.deepEqual(warnParsed.problems, []);
  assert.ok(warnParsed.warnings.some((w) => w.includes('[native-only-contract-incomplete]')));

  writeFile(repo, 'pdd.json', JSON.stringify({ lint: { rules: { 'native-only-contract-incomplete': 'error' } } }, null, 2) + '\n');
  execFileSync('git', ['-C', repo, 'add', 'pdd.json']);
  const errOut = sink(), errErr = sink();
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: errOut, stderr: errErr }), 1);
  const errParsed = JSON.parse(errOut.text);
  assert.ok(errParsed.problems.some((p) => p.includes('[native-only-contract-incomplete]')));

  writeFile(repo, 'pdd.json', JSON.stringify({ lint: { rules: { 'native-only-contract-incomplete': 'off' } } }, null, 2) + '\n');
  const offOut = sink(), offErr = sink();
  assert.equal(await runPdd(['lint', '--local', '--json'], { cwd: repo, env, stdout: offOut, stderr: offErr }), 0, offErr.text);
  const offParsed = JSON.parse(offOut.text);
  assert.deepEqual(offParsed.problems, []);
  assert.equal(offParsed.warnings.some((w) => w.includes('[native-only-contract-incomplete]')), false);

  // Linear O(N) performance on 100 KB adversarial input
  const hugePrompt = `---\nkind: native-only\nreason: Perf.\n---\n\n# Big\n\n${'a '.repeat(50000)}\n`;
  const t0 = performance.now();
  const perfRes = lintNativeOnlyContract(hugePrompt, { path: 'prompts/big.prompt.md' });
  const elapsedMs = performance.now() - t0;
  assert.equal(perfRes.length, 1);
  assert.ok(elapsedMs < 250, `expected linear O(N) scan on 100KB input, got ${elapsedMs.toFixed(1)}ms`);
});

test('3574 Part 4: detectNativeOnlyModules resolves native-only ownership via bindings, headers, and opening prose claims', () => {
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
    { path: 'src/trust/headed.mjs', content: '// Generated from prompts/trust/service.prompt.md (sha256: 0000).\nexport {};\n' },
    { path: 'src/calc.mjs', content: '// Generated from prompts/calc.prompt.md.\nexport {};\n' },
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
});

test('3574 Part 4: all 4 real-host OS/CLI failure classes fail closed when mocked/synthetic and pass with real-host probes', () => {
  assert.equal(MIN_REALISTIC_PAYLOAD_BYTES, 4096);
  assert.deepEqual(REAL_HOST_FAILURE_CLASSES, [
    'nested-sandbox',
    'host-tty-ownership',
    'multi-turn-cli-state',
    'full-size-payload',
  ]);

  // Class 1: Nested OS sandbox execution (mocked argv-prefix fails closed; real child process inside sandbox passes)
  const mockedSandboxTest = [
    "import { mock } from 'node:test';",
    "import { buildLaunchPrefix } from '../src/os-sandbox.mjs';",
    'const mockSpawn = mock.fn(() => ({ status: 0 }));',
    'const args = buildLaunchPrefix(["child-cli"]);',
    'mockSpawn(args);',
  ].join('\n');
  const sandboxMockProbe = detectRealHostProbesInTest('test/sandbox-prefix.test.mjs', mockedSandboxTest);
  assert.equal(sandboxMockProbe.hasRealHostSmoke, false);
  assert.equal(sandboxMockProbe.mockOnly, true);
  assert.deepEqual(sandboxMockProbe.classes, []);
  const sandboxLint = lintValidationCode({ path: 'test/sandbox-prefix.test.mjs', kind: 'test', text: mockedSandboxTest, hasRealE2eCoverage: false });
  assert.ok(sandboxLint.codes.includes('boundary-mock-only-test'));

  const sandboxFail = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/os-sandbox.mjs'],
    offlinePassed: true,
    offlineSummary: 'unit 6/6',
    e2eChecks: [{ kind: 'unit-mock', command: 'node --test test/sandbox-prefix.test.mjs', executed: true, exitCode: 0, passed: 6, failed: 0, skipped: 0 }],
    lintBlockingCodes: sandboxLint.codes,
  });
  assert.equal(sandboxFail.bucket, 3);
  assert.equal(sandboxFail.decision, 'needs-person');
  assert.equal(sandboxFail.waitKind, 'needs-real-host-smoke');
  assert.equal(sandboxFail.eligible, false);
  assert.match(sandboxFail.humanVerificationCard[1], /nested OS sandbox/i);

  const realSandboxTest = [
    "import { spawnSync } from 'node:child_process';",
    "import { runSandboxed } from '../src/os-sandbox.mjs';",
    "const res = spawnSync('sandbox-exec', ['-p', '(version 1)(allow default)', process.execPath, '-e', 'process.exit(0)']);",
    'runSandboxed(res);',
  ].join('\n');
  const sandboxRealProbe = detectRealHostProbesInTest('test/sandbox-live.test.mjs', realSandboxTest);
  assert.equal(sandboxRealProbe.hasRealHostSmoke, true);
  assert.ok(sandboxRealProbe.classes.includes('nested-sandbox'));
  assert.ok(detectRealE2eKindsInTest('test/sandbox-live.test.mjs', realSandboxTest).includes('real-host-smoke'));

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
      realHostClasses: sandboxRealProbe.classes,
    }],
  });
  assert.equal(sandboxPass.bucket, 1);
  assert.equal(sandboxPass.decision, 'allow-merge');
  assert.equal(sandboxPass.eligible, true);

  // Class 2: Real host device/TTY ownership (mocked TTY helper fails closed; real /dev/tty kernel probe passes)
  const mockedTtyTest = [
    "import { mock } from 'node:test';",
    "import { verifyControllingTty } from '../src/tty-owner.mjs';",
    'const fakeTty = mock.fn(() => ({ uid: 501 }));',
    'verifyControllingTty(fakeTty);',
  ].join('\n');
  assert.equal(detectRealHostProbesInTest('test/tty-mock.test.mjs', mockedTtyTest).hasRealHostSmoke, false);
  assert.ok(lintValidationCode({ path: 'test/tty-mock.test.mjs', kind: 'test', text: mockedTtyTest, hasRealE2eCoverage: false }).codes.includes('boundary-mock-only-test'));

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

  const realTtyTest = [
    "import { statSync } from 'node:fs';",
    "import { verifyControllingTty } from '../src/tty-owner.mjs';",
    "const st = statSync('/dev/tty');",
    'verifyControllingTty(st, process.getuid());',
  ].join('\n');
  const ttyRealProbe = detectRealHostProbesInTest('test/tty-live.test.mjs', realTtyTest);
  assert.equal(ttyRealProbe.hasRealHostSmoke, true);
  assert.ok(ttyRealProbe.classes.includes('host-tty-ownership'));
  assert.ok(detectRealE2eKindsInTest('test/tty-live.test.mjs', realTtyTest).includes('real-host-smoke'));

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
      realHostClasses: ttyRealProbe.classes,
    }],
  });
  assert.equal(ttyPass.bucket, 1);
  assert.equal(ttyPass.decision, 'allow-would-merge');
  assert.equal(ttyPass.eligible, true);

  // Class 3: Multi-turn real CLI state side effects (Turn 1 -> Turn 2; single-turn fails closed)
  const singleTurnCliTest = [
    "import { execFileSync } from 'node:child_process';",
    "import { mkdtempSync } from 'node:fs';",
    "const home = mkdtempSync('/tmp/cli-turn-');",
    "execFileSync(process.execPath, ['bin/cli.mjs', 'run'], { env: { HOME: home } });",
  ].join('\n');
  const singleTurnProbe = detectRealHostProbesInTest('test/cli-session.test.mjs', singleTurnCliTest);
  assert.equal(singleTurnProbe.detectedTurns, 1);
  assert.equal(singleTurnProbe.classes.includes('multi-turn-cli-state'), false);

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
      turns: singleTurnProbe.detectedTurns,
      realHostClasses: singleTurnProbe.classes,
    }],
  });
  assert.equal(singleTurnOutcome.bucket, 3);
  assert.equal(singleTurnOutcome.waitKind, 'needs-real-host-smoke');
  assert.match(singleTurnOutcome.message, /Turn 1 -> Turn 2/i);

  const multiTurnCliTest = [
    "import { execFileSync } from 'node:child_process';",
    "import { mkdtempSync, readdirSync } from 'node:fs';",
    "const home = mkdtempSync('/tmp/cli-turns-');",
    "const runTurn = (arg) => execFileSync(process.execPath, ['bin/cli.mjs', arg], { env: { HOME: home } });",
    "runTurn('turn-1');",
    "runTurn('turn-2');",
    'readdirSync(home);',
  ].join('\n');
  const multiTurnProbe = detectRealHostProbesInTest('test/cli-session-live.test.mjs', multiTurnCliTest);
  assert.ok(multiTurnProbe.detectedTurns >= 2);
  assert.ok(multiTurnProbe.classes.includes('multi-turn-cli-state'));

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
      turns: multiTurnProbe.detectedTurns,
      realHostClasses: multiTurnProbe.classes,
    }],
  });
  assert.equal(multiTurnOutcome.eligible, true);
  assert.equal(multiTurnOutcome.decision, 'allow-merge');

  // Class 4: Full-size realistic payload (> 4 KiB; tiny synthetic fixture fails closed)
  const tinyPayloadTest = [
    "import { execFileSync } from 'node:child_process';",
    "const payload = 'x'.repeat(256);",
    "execFileSync(process.execPath, ['bin/cli.mjs', '--stdin'], { input: payload });",
  ].join('\n');
  const tinyProbe = detectRealHostProbesInTest('test/payload-tiny.test.mjs', tinyPayloadTest);
  assert.equal(tinyProbe.maxDetectedPayloadBytes, 256);
  assert.equal(tinyProbe.classes.includes('full-size-payload'), false);

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
      payloadBytes: tinyProbe.maxDetectedPayloadBytes,
      realHostClasses: tinyProbe.classes,
    }],
  });
  assert.equal(tinyOutcome.bucket, 3);
  assert.equal(tinyOutcome.waitKind, 'needs-real-host-smoke');
  assert.match(tinyOutcome.message, /> 4096 bytes/);

  const fullPayloadTest = [
    "import { execFileSync } from 'node:child_process';",
    "const payload = 'a'.repeat(12 * 1024);",
    "execFileSync(process.execPath, ['bin/cli.mjs', '--live-local'], { input: payload });",
  ].join('\n');
  const fullProbe = detectRealHostProbesInTest('test/payload-full.test.mjs', fullPayloadTest);
  assert.equal(fullProbe.maxDetectedPayloadBytes, 12288);
  assert.equal(fullProbe.liveLocal, true);
  assert.ok(fullProbe.classes.includes('full-size-payload'));

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
      payloadBytes: fullProbe.maxDetectedPayloadBytes,
      realHostClasses: fullProbe.classes,
    }],
  });
  assert.equal(fullOutcome.eligible, true);
  assert.equal(fullOutcome.decision, 'allow-merge');
});

test('3574 Part 4 integration: lintRepoProject flags mock-only tests on kind: native-only modules and Autopilot core blocks mocked os-boundary PRs without touching autopilot-core', async (t) => {
  // 1. lintRepoProject resolves kind: native-only ownership automatically and flags mock-only test on an ordinary-named native-only module
  const repo = makeTempGitRepo(t, 'pdd-3574-native-lint-');
  writeFile(
    repo,
    'prompts/trust/service.prompt.md',
    [
      '---',
      'kind: native-only',
      'reason: Real SQLite adapter.',
      '---',
      '',
      '# Trust service',
      '',
      'Own `src/trust/service.mjs`.',
      '',
      '## Storage & error mapping',
      'SQLite WAL storage; fail closed on lock timeout.',
      '',
      '## Native verification',
      'Real SQLite file smoke test.',
      '',
      '## Dependencies',
      'None.',
    ].join('\n') + '\n',
  );
  writeFile(
    repo,
    'src/trust/service.mjs',
    '// Generated from prompts/trust/service.prompt.md.\nexport function createTrustService(db) { return db; }\n',
  );
  writeFile(
    repo,
    'test/trust-mock.test.mjs',
    "import { mock } from 'node:test';\nimport { createTrustService } from '../src/trust/service.mjs';\nconst fakeDb = mock.fn(() => ({ ok: true }));\ncreateTrustService(fakeDb);\n",
  );
  commitAll(repo, 'mock-only native-only service');

  const before = lintRepoProject({ root: repo });
  const mockHit = before.findings.find((f) => f.code === 'boundary-mock-only-test');
  assert.ok(mockHit, 'mock-only test on native-only module must emit boundary-mock-only-test');
  assert.equal(mockHit.path, 'test/trust-mock.test.mjs');
  assert.match(mockHit.message, /native-only/);

  // Direct lintBoundaryMockOnlyTests and inspectTestBoundaryTargets honor nativeOnlyTargets
  const targets = inspectTestBoundaryTargets('test/trust-mock.test.mjs', readFileSync(join(repo, 'test/trust-mock.test.mjs'), 'utf8'), {
    nativeOnlyTargets: ['src/trust/service.mjs'],
  });
  assert.ok(targets.boundarySurfaces.includes('native-only'));
  assert.equal(
    lintBoundaryMockOnlyTests(readFileSync(join(repo, 'test/trust-mock.test.mjs'), 'utf8'), {
      path: 'test/trust-mock.test.mjs',
      hasRealE2eCoverage: false,
      nativeOnlyTargets: ['src/trust/service.mjs'],
    }).length,
    1,
  );

  // Adding a real SQLite / subprocess smoke test clears boundary-mock-only-test cleanly
  writeFile(
    repo,
    'test/trust-smoke.test.mjs',
    "import { DatabaseSync } from 'node:sqlite';\nimport { createTrustService } from '../src/trust/service.mjs';\nconst db = new DatabaseSync(':memory:');\ncreateTrustService(db);\n",
  );
  commitAll(repo, 'add real sqlite smoke');
  const after = lintRepoProject({ root: repo });
  assert.equal(after.findings.some((f) => f.code === 'boundary-mock-only-test'), false);

  // 2. End-to-end coreWorld check: OS sandbox boundary file with only an argv-prefix unit test fails closed (Bucket 3) and merges once real subprocess smoke is added!
  const w = await coreWorld(t, { settings: { mode: 'auto', runs: 1 } });
  w.runtimeEvidence = () => ({ stories: [], storyFiles: [] });
  w.issue(91, { title: 'Harden OS sandbox launcher' });
  await w.tick();
  const buildCwd = w.job(91, 'build').cwd;
  writeFile(buildCwd, 'src/os-sandbox.mjs', 'export function launchArgs(cmd) { return ["sandbox-exec", ...cmd]; }\n');
  writeFile(
    buildCwd,
    'test/os-sandbox-unit.test.mjs',
    "import test from 'node:test';\nimport assert from 'node:assert/strict';\nimport { launchArgs } from '../src/os-sandbox.mjs';\ntest('prefix', () => assert.deepEqual(launchArgs(['a']), ['sandbox-exec', 'a']));\n",
  );
  const { pr } = w.build(91, {
    write: false,
    body: 'Fixes #91\n\nRuntime: not run (no prompt changed)\nPath: d — src/os-sandbox.mjs, test/os-sandbox-unit.test.mjs — unowned — no contract change — Test: done check',
    result: { promptChanged: false },
  });
  await w.tick();
  w.review(91, 'PASS');
  w.suite(91, 0);
  await w.tick();

  assert.equal(pr.merged, false, 'os-boundary PR with only argv-prefix unit test MUST fail closed');
  assert.ok(w.labels(91).includes('pdd:needs-decision'), 'parks for person when real-host smoke is missing');
  assert.ok(
    pr.comments.some((c) => /<!-- pdd:autopilot-core:human-boundary:/.test(c.body) && /nested OS sandbox/i.test(c.body)),
    'human verification card names missing nested OS sandbox real-host verification',
  );

  // 3. Linear O(N) safety for detectRealHostProbesInTest on 100 KB adversarial test input
  const hugeTest = `import { spawnSync } from 'node:child_process';\nconst s = '${'x'.repeat(100000)}';\nspawnSync(process.execPath, ['-e', '0']);\n`;
  const t0 = performance.now();
  const bigProbe = detectRealHostProbesInTest('test/big-payload.test.mjs', hugeTest);
  const bigMs = performance.now() - t0;
  assert.equal(bigProbe.hasRealHostSmoke, true);
  assert.equal(bigProbe.maxDetectedPayloadBytes, 100000);
  assert.ok(bigProbe.classes.includes('full-size-payload'));
  assert.ok(bigMs < 300, `expected linear O(N) probe scan on 100KB input, got ${bigMs.toFixed(1)}ms`);
});

test('3574 docs & skills: pdd-product contract and RUNBOOK §17 checklist define native-only contract and all 4 real-host classes without history words', () => {
  const filesDoc = readFileSync(join(process.cwd(), 'skills/pdd-product/references/files.md'), 'utf8');
  const planDoc = readFileSync(join(process.cwd(), 'skills/pdd-product/steps/plan.md'), 'utf8');
  const replaysDoc = readFileSync(join(process.cwd(), 'skills/pdd-prompting/runbook/replays-and-formal.md'), 'utf8');

  assert.match(filesDoc, /## Native-only prompt contract/);
  assert.match(filesDoc, /Boundary & runtime contract/);
  assert.match(filesDoc, /Error mapping & failure behavior/);
  assert.match(filesDoc, /Real-host \/ native verification cases/);
  assert.doesNotMatch(filesDoc, /thin `kind: native-only`/i);

  assert.match(planDoc, /specification contract/i);
  assert.doesNotMatch(planDoc, /thin\s+`kind: native-only`/i);

  for (const needle of [
    'needs-real-host-smoke',
    'Nested OS sandbox execution',
    'Real host device/TTY ownership',
    '/dev/tty',
    'Multi-turn real CLI state side effects',
    'Full-size realistic payload handling',
    '4 KiB',
  ]) {
    assert.ok(replaysDoc.includes(needle), `replays-and-formal.md missing: ${needle}`);
  }

  for (const [name, content] of [
    ['skills/pdd-product/references/files.md', filesDoc],
    ['skills/pdd-product/steps/plan.md', planDoc],
    ['skills/pdd-prompting/runbook/replays-and-formal.md', replaysDoc],
  ]) {
    assert.doesNotMatch(content, /\b(?:no longer|used to|was renamed|moved to|since 0\.1|New in)\b/i, `${name} must use timeless current wording`);
  }
});
