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
    { path: 'src/trust/headed.mjs', content: `// Generated from prompts/trust/service.prompt.md (sha256: ${'0'.repeat(64)}).\nexport {};\n` },
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

test('3574 R1 regressions (#1, #3-#10): ReDoS safety, mocked primitives, 4-class spoofs/false-negatives, surface narrowing, cross-surface/failing-suite precedence, contract bypasses, ownership alignment, batch call count, and parts.md', () => {
  // Finding #1 [P0]: 40,000 blank lines in YAML frontmatter run in linear O(N) time (< 50ms) in BOTH modules.
  const hostileFrontmatter = `---\n${'\n'.repeat(40000)}kind: native-only\nreason: Perf check.\n---\n\n# Perf\n`;
  const t1 = performance.now();
  const fmDet = detectNativeOnlyModules({
    changedFiles: ['src/perf.mjs'],
    promptFiles: [{ path: 'prompts/perf.prompt.md', content: hostileFrontmatter }],
    fileHeads: [{ path: 'src/perf.mjs', content: '// Generated from prompts/perf.prompt.md.\n' }],
  });
  const fmMs1 = performance.now() - t1;
  assert.deepEqual(fmDet.nativeOnlyModules, ['src/perf.mjs']);
  assert.ok(fmMs1 < 100, `parseNativeOnlyPromptMeta took ${fmMs1.toFixed(1)}ms on 40k blank lines`);

  const t2 = performance.now();
  const fmLint = lintNativeOnlyContract(hostileFrontmatter, { path: 'prompts/perf.prompt.md' });
  const fmMs2 = performance.now() - t2;
  assert.equal(fmLint.length, 1);
  assert.ok(fmMs2 < 100, `hasNativeOnlyFrontmatter took ${fmMs2.toFixed(1)}ms on 40k blank lines`);

  // Finding #3 [P1]: mocked/shadowed/module-mocked/fake-receiver primitives NEVER grant real-host smoke and ARE caught by boundary-mock-only-test.
  const spoofTests = [
    [
      'local shadowed spawnSync',
      "import { mock } from 'node:test';\nimport { run } from '../src/os-sandbox.mjs';\nconst spawnSync = mock.fn(() => ({ status: 0 }));\nspawnSync('sandbox-exec', ['-p', 'x']);\nrun();\n",
    ],
    [
      'fake receiver fake.spawnSync',
      "import { mock } from 'node:test';\nimport * as cp from 'node:child_process';\nimport { run } from '../src/os-sandbox.mjs';\nconst fake = { spawnSync: mock.fn(() => ({ status: 0 })) };\nfake.spawnSync('sandbox-exec', ['-p', 'x']);\nrun(cp);\n",
    ],
    [
      'vi.mock node:child_process',
      "import { vi } from 'vitest';\nvi.mock('node:child_process', () => ({ spawnSync: vi.fn() }));\nimport { spawnSync } from 'node:child_process';\nimport { run } from '../src/os-sandbox.mjs';\nspawnSync('sandbox-exec', ['-p', 'x']);\nrun();\n",
    ],
    [
      'mock.module node:http + shadowed fetch',
      "import { mock } from 'node:test';\nmock.module('node:http', { namedExports: { createServer: mock.fn() } });\nimport { createServer } from 'node:http';\nimport { serve } from '../api/orders.mjs';\nconst fetch = mock.fn();\ncreateServer(serve);\nfetch('http://127.0.0.1');\n",
    ],
    [
      'mock.method on fs.statSync',
      "import { mock } from 'node:test';\nimport fs from 'node:fs';\nimport { checkTty } from '../src/tty-owner.mjs';\nmock.method(fs, 'statSync', () => ({ uid: 501 }));\ncheckTty(fs.statSync('/dev/tty'));\n",
    ],
  ];
  for (const [label, src] of spoofTests) {
    const probe = detectRealHostProbesInTest('test/spoof.test.mjs', src);
    assert.equal(probe.hasRealHostSmoke, false, `${label}: must NOT grant hasRealHostSmoke`);
    assert.deepEqual(probe.classes, [], `${label}: must NOT credit any real-host class`);
    const lint = lintValidationCode({ path: 'test/spoof.test.mjs', kind: 'test', text: src, hasRealE2eCoverage: false });
    assert.ok(lint.codes.includes('boundary-mock-only-test'), `${label}: must trigger boundary-mock-only-test`);
  }

  // Finding #4 [P1]: spoofs rejected & real patterns recognized across all 4 real-host classes.
  // 4.1 nested-sandbox: filename or unrelated string literal alone MUST NOT spoof nested-sandbox.
  const spoofSandboxName = [
    "import { spawnSync } from 'node:child_process';",
    "const note = 'sandbox_apply: Operation not permitted';",
    "spawnSync(process.execPath, ['-e', 'process.exit(0)']);",
  ].join('\n');
  assert.equal(detectRealHostProbesInTest('test/sandbox-name.test.mjs', spoofSandboxName).classes.includes('nested-sandbox'), false);

  // 4.2 host-tty-ownership: real statSync('/dev/tty') with unrelated logSpy still passes, while dead string '/dev/tty' with unrelated statSync does NOT.
  const ttyWithUnrelatedSpy = [
    "import { mock } from 'node:test';",
    "import { statSync } from 'node:fs';",
    'const logSpy = mock.fn();',
    "const st = statSync('/dev/tty');",
    'logSpy(st.uid);',
  ].join('\n');
  assert.ok(detectRealHostProbesInTest('test/tty-real-spy.test.mjs', ttyWithUnrelatedSpy).classes.includes('host-tty-ownership'));

  const ttyDeadString = [
    "import { statSync } from 'node:fs';",
    "const doc = '/dev/tty';",
    "statSync('/tmp/other-file');",
  ].join('\n');
  assert.equal(detectRealHostProbesInTest('test/tty-dead-str.test.mjs', ttyDeadString).classes.includes('host-tty-ownership'), false);

  // 4.3 multi-turn-cli-state: preceding .map() and string 'HOME' do NOT spoof multi-turn; 6-line helper called twice + real fs DOES.
  const spoofMultiTurn = [
    "import { execFileSync } from 'node:child_process';",
    'const nums = [1, 2].map((x) => x + 1);',
    "const label = 'HOME containment check';",
    "execFileSync(process.execPath, ['bin/cli.mjs', String(nums[0])]);",
  ].join('\n');
  const spoofMultiProbe = detectRealHostProbesInTest('test/cli-single.test.mjs', spoofMultiTurn);
  assert.equal(spoofMultiProbe.detectedTurns, 1);
  assert.equal(spoofMultiProbe.classes.includes('multi-turn-cli-state'), false);

  const sixLineHelperMultiTurn = [
    "import { execFileSync } from 'node:child_process';",
    "import { mkdtempSync, readdirSync } from 'node:fs';",
    "const home = mkdtempSync('/tmp/turns-');",
    'function runTurn(arg) {',
    '  const env = { ...process.env, HOME: home };',
    '  const opts = { env, encoding: "utf8" };',
    '  const script = "bin/cli.mjs";',
    '  const args = [script, arg];',
    '  // 6 lines before real subprocess call',
    '  return execFileSync(process.execPath, args, opts);',
    '}',
    "runTurn('first');",
    "runTurn('second');",
    'readdirSync(home);',
  ].join('\n');
  const sixLineProbe = detectRealHostProbesInTest('test/cli-multi-helper.test.mjs', sixLineHelperMultiTurn);
  assert.ok(sixLineProbe.detectedTurns >= 2, `expected >= 2 turns, got ${sixLineProbe.detectedTurns}`);
  assert.ok(sixLineProbe.classes.includes('multi-turn-cli-state'));

  // 4.4 full-size-payload: regex literal /`/ and string 'Buffer.alloc(99999)' NEVER spoof payload size; real 'ab'.repeat(3000) = 6000 DOES.
  const spoofPayload = [
    "import { execFileSync } from 'node:child_process';",
    'const hasTick = /`/;',
    "const doc = 'Buffer.alloc(99999) and \"x\".repeat(12000)';",
    'const re = /Buffer\\.alloc\\(99999\\)/;',
    "execFileSync(process.execPath, ['-e', '0']);",
  ].join('\n');
  const spoofPayloadProbe = detectRealHostProbesInTest('test/payload-spoof.test.mjs', spoofPayload);
  assert.equal(spoofPayloadProbe.classes.includes('full-size-payload'), false);
  assert.ok((spoofPayloadProbe.maxDetectedPayloadBytes ?? 0) <= MIN_REALISTIC_PAYLOAD_BYTES);

  const realRepeatPayload = [
    "import { execFileSync } from 'node:child_process';",
    'const hasTick = /`/;',
    "const body = 'ab'.repeat(3000);",
    "execFileSync(process.execPath, ['bin/cli.mjs'], { input: body + String(hasTick) });",
  ].join('\n');
  const realRepeatProbe = detectRealHostProbesInTest('test/payload-repeat.test.mjs', realRepeatPayload);
  assert.equal(realRepeatProbe.maxDetectedPayloadBytes, 6000);
  assert.ok(realRepeatProbe.classes.includes('full-size-payload'));

  // Finding #5 [P1]: ordinary JS files stay runtime-code; truncate/truncation match full-size-payload; UI preview does NOT infer full-size-payload.
  for (const ordinary of ['src/signal.mjs', 'src/namespace.mjs', 'src/fd-utils.mjs', 'src/exec.mjs', 'process/order.mjs', 'native/math.mjs']) {
    const s = detectChangedSurfaces({ changedFiles: [ordinary] });
    assert.deepEqual(s.surfaces, ['runtime-code'], `${ordinary} must stay runtime-code, got ${JSON.stringify(s.surfaces)}`);
  }
  assert.deepEqual(detectChangedSurfaces({ changedFiles: ['src/ui/card-preview.tsx'] }).realHostBoundaryClasses, []);
  assert.ok(detectChangedSurfaces({ changedFiles: ['src/truncate.mjs'], nativeOnlyFiles: ['src/truncate.mjs'] }).realHostBoundaryClasses.includes('full-size-payload'));
  assert.ok(detectChangedSurfaces({ changedFiles: ['bin/truncation-cli.mjs'] }).realHostBoundaryClasses.includes('full-size-payload'));

  // Finding #6 [P1]: (1) browser-playwright cannot satisfy os-boundary; (2) metadata-free check cannot bypass class meta; (3) failed suite routes to Bucket 1 repair.
  const crossSurface = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['web/page.tsx', 'src/os-sandbox.mjs'],
    offlinePassed: true,
    e2eChecks: [{
      kind: 'browser-playwright',
      command: 'npx playwright test',
      executed: true,
      exitCode: 0,
      passed: 3,
      failed: 0,
      skipped: 0,
    }],
  });
  assert.equal(crossSurface.bucket, 3);
  assert.equal(crossSurface.waitKind, 'needs-real-host-smoke');
  assert.equal(crossSurface.eligible, false);

  const metaBypass = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/os-sandbox.mjs'],
    offlinePassed: true,
    e2eChecks: [
      { kind: 'real-host-smoke', command: 'node --test a', executed: true, exitCode: 0, passed: 1, failed: 0, skipped: 0, realHostClasses: [] },
      { kind: 'subprocess-cli', command: 'node --test b', executed: true, exitCode: 0, passed: 1, failed: 0, skipped: 0 },
    ],
  });
  assert.equal(metaBypass.bucket, 3);
  assert.equal(metaBypass.waitKind, 'needs-real-host-smoke');

  const failingSuite = evaluateValidationOutcome({
    mode: 'auto',
    changedFiles: ['src/os-sandbox.mjs'],
    offlinePassed: false,
    e2eChecks: [{
      kind: 'unit-mock',
      command: 'npm test',
      executed: true,
      exitCode: 1,
      passed: 0,
      failed: 1,
      skipped: 0,
    }],
    repairAttempts: 0,
  });
  assert.equal(failingSuite.bucket, 1);
  assert.equal(failingSuite.decision, 'repair');
  assert.equal(failingSuite.repairRoundsToSpend, 1);

  // Finding #7 [P1]: sibling ### flags don't leak, bare 512/443 doesn't spoof error mapping, port-only table ignored, thematic break & blank fence ignored, embedded native-only checked, combined boundary+port heading accepted.
  const siblingLeakPrompt = [
    '---',
    'kind: native-only',
    'reason: Real adapter.',
    '---',
    '# Adapter',
    '## Overview',
    '### Error mapping',
    '---',
    '### Native verification',
    '```sh',
    '   ',
    '```',
    '### Notes',
    'Payload buffer is 512 bytes on port 443.',
    '## Port wiring',
    '| Port | Op |',
    '| --- | --- |',
    '| store | load |',
    '## Dependencies',
    'None.',
  ].join('\n');
  const leakWarnings = lintNativeOnlyContract(siblingLeakPrompt, { path: 'prompts/leak.prompt.md' });
  assert.equal(leakWarnings.length, 1);
  assert.match(leakWarnings[0], /boundary\/runtime contract/);
  assert.match(leakWarnings[0], /error mapping \/ failure behavior/);
  assert.match(leakWarnings[0], /real-host \/ native verification cases/);

  const embeddedStubPrompt = [
    '# Embedded stub',
    'Own `src/embedded.mjs`.',
    '<details><summary>Runtime interface</summary>',
    '```json',
    '{"kind":"native-only","reason":"Legacy embedded stub."}',
    '```',
    '</details>',
  ].join('\n');
  assert.equal(lintNativeOnlyContract(embeddedStubPrompt, { path: 'prompts/embedded.prompt.md' }).length, 1);

  const combinedHeadingPrompt = [
    '---',
    'kind: native-only',
    'reason: Real SQLite adapter.',
    '---',
    '# Adapter',
    '## Boundary contract and port wiring',
    'Opens SQLite WAL database; maps SQLITE_BUSY to HTTP 503 and rolls back.',
    '## Real-host verification',
    'Runs real SQLite file smoke test.',
    '## Dependencies',
    'None.',
  ].join('\n');
  assert.deepEqual(lintNativeOnlyContract(combinedHeadingPrompt, { path: 'prompts/combined.prompt.md' }), []);

  // Finding #8 [P1]: unrelated prose JSON mentioning runtime interface + native-only does NOT trigger false positive; SQL `--` / C `/* */` / Rust `///` headers & relative links & repeated `./`/`//` normalization work.
  const falsePositivePrompt = [
    '# Regular checkable prompt',
    'Mentions runtime interface and native-only in prose.',
    '```json',
    '{"kind":"native-only","reason":"example payload, not a Runtime interface block"}',
    '```',
  ].join('\n');
  const fpDetected = detectNativeOnlyModules({
    changedFiles: ['src/regular.mjs'],
    promptFiles: [{ path: 'prompts/regular.prompt.md', content: falsePositivePrompt }],
    fileHeads: [{ path: 'src/regular.mjs', content: '// Generated from prompts/regular.prompt.md.\n' }],
  });
  assert.deepEqual(fpDetected.nativeOnlyPrompts, []);
  assert.deepEqual(fpDetected.nativeOnlyModules, []);

  const multiCommentDetected = detectNativeOnlyModules({
    changedFiles: ['././src//a.sql', 'src/b.c', 'src/c.rs', 'src/linked.mjs'],
    promptFiles: [{
      path: 'prompts/native/multi.prompt.md',
      content: '---\nkind: native-only\nreason: Native multi-lang.\n---\n\n# Multi\n\nOwns [linked](../../src/linked.mjs).\n',
    }],
    fileHeads: [
      { path: 'src/a.sql', content: '-- Generated from prompts/native/multi.prompt.md.\n' },
      { path: 'src/b.c', content: '/* Prompt: prompts/native/multi.prompt.md */\n' },
      { path: 'src/c.rs', content: '/// Generated from prompts/native/multi.prompt.md.\n' },
    ],
  });
  assert.deepEqual(multiCommentDetected.nativeOnlyModules, ['src/a.sql', 'src/b.c', 'src/c.rs', 'src/linked.mjs']);

  // Finding #9 [P2]: single-pass batch helper call counting is O(N) on huge single-line input with many calls.
  const hugeCalls = `import { execFileSync } from 'node:child_process';\nimport { mkdtempSync } from 'node:fs';\nconst run = (a) => execFileSync(process.execPath, [a]);\nmkdtempSync('/tmp/x-');\n${'run("x");'.repeat(8000)}\n`;
  const t9 = performance.now();
  const batchProbe = detectRealHostProbesInTest('test/batch-perf.test.mjs', hugeCalls);
  const ms9 = performance.now() - t9;
  assert.ok(batchProbe.detectedTurns >= 8000);
  assert.ok(batchProbe.classes.includes('multi-turn-cli-state'));
  assert.ok(ms9 < 250, `batch helper scan took ${ms9.toFixed(1)}ms on 8000 single-line calls`);

  // Finding #10 [P2]: skills/pdd-product/steps/parts.md no longer says "Thin kind: native-only".
  const partsDoc = readFileSync(join(process.cwd(), 'skills/pdd-product/steps/parts.md'), 'utf8');
  assert.doesNotMatch(partsDoc, /thin\s+`kind: native-only`/i);
  assert.match(partsDoc, /specification prompts/i);
  assert.doesNotMatch(partsDoc, /\b(?:no longer|used to|was renamed|moved to|since 0\.1|New in)\b/i);
});

test('R2 adversarial regression suite: R2-1 through R2-5', () => {
  // R2-1 [P1]: No stateful /g flip-flop on global fetch shadowing + window.fetch / bare fetch / uninit let / non-native import shadows.
  const globalFetchStub = `
    globalThis.fetch = async () => ({ ok: true });
    await fetch('http://127.0.0.1:3000/api');
  `;
  for (let run = 0; run < 4; run += 1) {
    const p = detectRealHostProbesInTest('test/api-fetch-stub.test.mjs', globalFetchStub);
    assert.equal(p.hasRealHostSmoke, false, `globalThis.fetch stub must stay rejected on call #${run + 1}`);
    assert.deepEqual(detectRealE2eKindsInTest('test/api-fetch-stub.test.mjs', globalFetchStub), ['real-execution']);
  }

  const fetchShadowVariants = [
    `window.fetch = async () => ({ ok: true }); await fetch('http://127.0.0.1:3000');`,
    `fetch = async () => ({ ok: true }); await fetch('http://127.0.0.1:3000');`,
    `let fetch; fetch = () => ({ ok: true }); await fetch('http://127.0.0.1:3000');`,
    `var fetch;\nawait fetch('http://127.0.0.1:3000');`,
    `let a = 1, fetch;\nawait fetch('http://127.0.0.1:3000');`,
    `import fetch from './fake-fetch.mjs'\nawait fetch('http://127.0.0.1:3000')`,
    `import { fakeFetch as fetch } from './helpers.mjs'\nawait fetch('http://127.0.0.1:3000')`,
    `const { fetch } = require('./fake-fetch.cjs')\nawait fetch('http://127.0.0.1:3000')`,
    `const fetch = require('fetch-mock')\nawait fetch('http://127.0.0.1:3000')`,
    `vi.stubGlobal(\n  'fetch',\n  vi.fn(),\n);\nawait fetch('http://127.0.0.1:3000');`,
  ];
  for (const code of fetchShadowVariants) {
    const p = detectRealHostProbesInTest('test/api-fetch-shadow.test.mjs', code);
    assert.equal(p.hasRealHostSmoke, false, `shadowed fetch must not count as real smoke: ${code}`);
    assert.ok(!detectRealE2eKindsInTest('test/api-fetch-shadow.test.mjs', code).includes('local-server-or-db'));
  }

  const uninitSpawnShadow = `
    import * as cp from 'node:child_process';
    let spawnSync;
    spawnSync = () => ({ status: 0 });
    spawnSync('git', ['status']);
  `;
  assert.equal(detectRealHostProbesInTest('test/uninit-spawn.test.mjs', uninitSpawnShadow).hasRealHostSmoke, false);

  // Genuine unshadowed global fetch still passes reliably across repeated calls.
  const realFetchTest = `await fetch('http://127.0.0.1:3000/health');`;
  for (let run = 0; run < 3; run += 1) {
    assert.equal(detectRealHostProbesInTest('test/api-real-fetch.test.mjs', realFetchTest).hasRealHostSmoke, true);
    assert.ok(detectRealE2eKindsInTest('test/api-real-fetch.test.mjs', realFetchTest).includes('local-server-or-db'));
  }

  // R2-2 [P1]: Semicolon-free consecutive ESM imports, multiline vi.mock/doMock/jest.doMock, and string-literal import spoofs.
  const semiFreeEsm = [
    `import assert from 'node:assert/strict'`,
    `import test from 'node:test'`,
    `import { spawnSync } from 'node:child_process'`,
    `import { mkdtempSync } from 'node:fs'`,
    `test('cli', () => {`,
    `  mkdtempSync('/tmp/semi-')`,
    `  spawnSync(process.execPath, ['-e', '0'])`,
    `  spawnSync(process.execPath, ['-e', '0'])`,
    `})`,
  ].join('\n');
  const semiFreeProbe = detectRealHostProbesInTest('test/semi-free.test.mjs', semiFreeEsm);
  assert.equal(semiFreeProbe.hasRealHostSmoke, true);
  assert.equal(semiFreeProbe.detectedTurns, 2);
  assert.ok(semiFreeProbe.classes.includes('multi-turn-cli-state'));

  const multilineMocks = [
    `import { spawnSync } from 'node:child_process'\nvi.mock(\n  'node:child_process',\n  () => ({ spawnSync: () => ({ status: 0 }) }),\n)\nspawnSync('git', ['status'])`,
    `import { spawnSync } from 'node:child_process'\nvi.doMock(\n  'node:child_process',\n  () => ({ spawnSync: () => ({ status: 0 }) }),\n)\nspawnSync('git', ['status'])`,
    `import { spawnSync } from 'node:child_process'\njest.doMock(\n  'node:child_process',\n  () => ({ spawnSync: () => ({ status: 0 }) }),\n)\nspawnSync('git', ['status'])`,
  ];
  for (const code of multilineMocks) {
    const p = detectRealHostProbesInTest('test/multiline-mock.test.mjs', code);
    assert.equal(p.hasRealHostSmoke, false);
    assert.equal(p.mockOnly, true);
  }

  const stringLiteralImportSpoof = `
    const doc = "import { spawnSync } from 'node:child_process'";
    const doc2 = "const { execFileSync } = require('node:child_process')";
    const spawnSync = () => ({ status: 0 });
    spawnSync('git', ['status']);
  `;
  assert.equal(detectRealHostProbesInTest('test/str-import-spoof.test.mjs', stringLiteralImportSpoof).hasRealHostSmoke, false);

  const stringLiteralMockDoesNotPoisonReal = `
    import { spawnSync } from 'node:child_process'
    const note = "vi.mock('node:child_process')"
    spawnSync(process.execPath, ['-e', '0'])
  `;
  assert.equal(detectRealHostProbesInTest('test/str-mock-inert.test.mjs', stringLiteralMockDoesNotPoisonReal).hasRealHostSmoke, true);

  // R2-3 [P1]: Unimported browser mocks, unused node:sqlite/node:tty imports, and mock.method(tty, 'isatty') bypass.
  const unimportedBrowserMocks = [
    `const page = { goto: async () => ({ ok: true }) }; await page.goto('http://127.0.0.1:3000');`,
    `const chromium = { launch: async () => ({}) }; await chromium.launch();`,
    `import { test } from '@playwright/test';\nconst page = { goto: async () => ({}) };\nawait page.goto('http://127.0.0.1:3000');`,
    `import { test } from '@playwright/test';\nconst browser = { newPage: () => ({ goto: () => {} }) };\nconst page = browser.newPage();\npage.goto('http://127.0.0.1:3000');`,
    `import { chromium } from 'playwright';\nmock.method(chromium, 'launch', async () => ({}));\nawait chromium.launch();`,
  ];
  for (const code of unimportedBrowserMocks) {
    const kinds = detectRealE2eKindsInTest('test/web-mock.test.mjs', code);
    assert.ok(!kinds.includes('browser-playwright'), `unimported/mocked browser must fail: ${code}`);
  }

  const realPlaywrightFixture = `
    import { test, expect } from '@playwright/test';
    test('loads home', async ({ page }) => {
      await page.goto('http://127.0.0.1:3000');
      await expect(page).toHaveTitle(/Home/);
    });
  `;
  assert.ok(detectRealE2eKindsInTest('test/web-real.test.mjs', realPlaywrightFixture).includes('browser-playwright'));

  const realPlaywrightLaunch = `
    import { chromium } from 'playwright';
    const browser = await chromium.launch();
    const page = await browser.newPage();
    await page.goto('http://127.0.0.1:3000');
  `;
  assert.ok(detectRealE2eKindsInTest('test/web-launch.test.mjs', realPlaywrightLaunch).includes('browser-playwright'));

  const unusedTtyImport = `import { isatty, ReadStream } from 'node:tty';\nconst x = 1;`;
  assert.equal(detectRealHostProbesInTest('test/unused-tty.test.mjs', unusedTtyImport).hasRealHostSmoke, false);

  const stubbedTtyIsatty = `
    import tty from 'node:tty';
    mock.method(tty, 'isatty', () => true);
    tty.isatty(0);
  `;
  assert.equal(detectRealHostProbesInTest('test/stubbed-tty.test.mjs', stubbedTtyIsatty).hasRealHostSmoke, false);

  const realTtyIsatty = `
    import { isatty } from 'node:tty';
    const ok = isatty(0);
  `;
  const realTtyProbe = detectRealHostProbesInTest('test/real-tty.test.mjs', realTtyIsatty);
  assert.equal(realTtyProbe.hasRealHostSmoke, true);
  assert.ok(realTtyProbe.classes.includes('host-tty-ownership'));

  const unusedSqliteImport = `import { DatabaseSync } from 'node:sqlite';\nconst ref = DatabaseSync;`;
  assert.equal(detectRealHostProbesInTest('test/unused-sqlite.test.mjs', unusedSqliteImport).hasRealHostSmoke, false);
  assert.ok(!detectRealE2eKindsInTest('test/unused-sqlite.test.mjs', unusedSqliteImport).includes('local-server-or-db'));

  const realSqliteUsage = `import { DatabaseSync } from 'node:sqlite';\nconst db = new DatabaseSync(':memory:');`;
  assert.equal(detectRealHostProbesInTest('test/real-sqlite.test.mjs', realSqliteUsage).hasRealHostSmoke, true);
  assert.ok(detectRealE2eKindsInTest('test/real-sqlite.test.mjs', realSqliteUsage).includes('local-server-or-db'));

  // R2-4 [P1]: Balanced call args (no bleed past ')'), whole-identifier devicePathVars, enclosing-only sameLineLoop, "".repeat(10000) == 0 bytes.
  const sameLineBleedSubprocess = `
    import { execFileSync } from 'node:child_process';
    execFileSync(process.execPath, ['-e', '0']); const x = 'sandbox-exec --live-local';
  `;
  const bleedSubProbe = detectRealHostProbesInTest('test/same-line-bleed.test.mjs', sameLineBleedSubprocess);
  assert.equal(bleedSubProbe.hasRealHostSmoke, true);
  assert.equal(bleedSubProbe.liveLocal, false);
  assert.ok(!bleedSubProbe.classes.includes('nested-sandbox'));

  const sameLineBleedFs = `
    import { statSync } from 'node:fs';
    statSync('/tmp/foo'); const p = '/dev/tty';
  `;
  assert.equal(detectRealHostProbesInTest('test/fs-bleed.test.mjs', sameLineBleedFs).hasRealHostSmoke, false);

  const substringVarFsSpoof = `
    import { statSync } from 'node:fs';
    const p = '/dev/tty';
    statSync('/tmp/p');
    statSync(path);
  `;
  assert.equal(detectRealHostProbesInTest('test/fs-substr-spoof.test.mjs', substringVarFsSpoof).hasRealHostSmoke, false);

  const realVarFsProbe = `
    import { statSync } from 'node:fs';
    const ttyPath = '/dev/tty';
    statSync(ttyPath);
  `;
  assert.ok(detectRealHostProbesInTest('test/fs-real-var.test.mjs', realVarFsProbe).classes.includes('host-tty-ownership'));

  const closedMapBeforeExec = `
    import { execFileSync } from 'node:child_process';
    import { mkdtempSync } from 'node:fs';
    mkdtempSync('/tmp/x-');
    const args = ['a'].map(x => x); execFileSync(process.execPath, args);
  `;
  const closedMapProbe = detectRealHostProbesInTest('test/closed-map.test.mjs', closedMapBeforeExec);
  assert.equal(closedMapProbe.detectedTurns, 1);
  assert.ok(!closedMapProbe.classes.includes('multi-turn-cli-state'));

  const closedForBeforeExec = `
    import { execFileSync } from 'node:child_process';
    import { mkdtempSync } from 'node:fs';
    mkdtempSync('/tmp/x-');
    for (let i = 0; i < 2; i++) { args.push(i); } execFileSync(process.execPath, args);
  `;
  assert.equal(detectRealHostProbesInTest('test/closed-for.test.mjs', closedForBeforeExec).detectedTurns, 1);

  const enclosingSameLineLoop = `
    import { execFileSync } from 'node:child_process';
    import { mkdtempSync } from 'node:fs';
    mkdtempSync('/tmp/x-');
    ['a', 'b'].forEach(x => execFileSync(process.execPath, ['-e', x]));
  `;
  const enclosingLoopProbe = detectRealHostProbesInTest('test/enclosing-loop.test.mjs', enclosingSameLineLoop);
  assert.ok(enclosingLoopProbe.detectedTurns >= 2);
  assert.ok(enclosingLoopProbe.classes.includes('multi-turn-cli-state'));

  const emptyRepeatSpoof = `
    import { execFileSync } from 'node:child_process';
    const empty1 = "".repeat(10000);
    const empty2 = '' .repeat(10000);
    const empty3 = \`\`.repeat(10000);
    execFileSync(process.execPath, ['-e', '0']);
  `;
  const emptyRepeatProbe = detectRealHostProbesInTest('test/empty-repeat.test.mjs', emptyRepeatSpoof);
  assert.ok((emptyRepeatProbe.maxDetectedPayloadBytes ?? 0) <= MIN_REALISTIC_PAYLOAD_BYTES);
  assert.ok(!emptyRepeatProbe.classes.includes('full-size-payload'));

  // R2-5 [P2]: Non-native frontmatter + embedded Runtime interface bodyOffset, attached comment closer in header, and schema fence inside port-only section.
  const fmPlusEmbeddedPrompt = [
    '---',
    'owner: platform',
    '---',
    '',
    '# Embedded OS adapter',
    '',
    'Owns `src/embedded-os.mjs`.',
    '',
    '<details><summary>Runtime interface</summary>',
    '```json',
    '{"kind":"native-only","reason":"OS boundary"}',
    '```',
    '</details>',
  ].join('\n');
  const fmEmbeddedDetected = detectNativeOnlyModules({
    changedFiles: ['src/embedded-os.mjs', 'src/attached-closer.c'],
    promptFiles: [{ path: 'prompts/embedded-os.prompt.md', content: fmPlusEmbeddedPrompt }],
    fileHeads: [
      { path: 'src/attached-closer.c', content: '/* Prompt: prompts/embedded-os.prompt.md*/\n' },
    ],
  });
  assert.deepEqual(fmEmbeddedDetected.nativeOnlyModules, ['src/attached-closer.c', 'src/embedded-os.mjs']);

  const portOnlySchemaFencePrompt = [
    '---',
    'kind: native-only',
    'reason: Real adapter.',
    '---',
    '# Adapter',
    '## Port wiring',
    '```json',
    '{"port": "store", "op": "load"}',
    '```',
    '## Error mapping',
    'Maps failures to HTTP 503.',
    '## Real-host verification',
    'Runs real-host smoke test.',
    '## Dependencies',
    'None.',
  ].join('\n');
  const portFenceWarnings = lintNativeOnlyContract(portOnlySchemaFencePrompt, { path: 'prompts/port-fence.prompt.md' });
  assert.equal(portFenceWarnings.length, 1);
  assert.match(portFenceWarnings[0], /boundary\/runtime contract/);
});

test('R3 adversarial + CodeQL regression suite: items 1 through 4', () => {
  // R3-1 [P0 CodeQL]: HTML comment closers (--> and --!>) parsed linearly without HTML-filtering regexes.
  const htmlCloserPrompt = '---\nkind: native-only\nreason: HTML comment header test.\n---\n# HTML\n';
  const sha = '0'.repeat(64);
  const htmlHeaderDetected = detectNativeOnlyModules({
    changedFiles: ['src/h1.html', 'src/h2.html', 'src/h3.html', 'src/h4.html', 'src/bad.html'],
    promptFiles: [{ path: 'prompts/html-closer.prompt.md', content: htmlCloserPrompt }],
    fileHeads: [
      { path: 'src/h1.html', content: `<!-- Generated from prompts/html-closer.prompt.md-->\n` },
      { path: 'src/h2.html', content: `<!-- Generated from prompts/html-closer.prompt.md--!>\n` },
      { path: 'src/h3.html', content: `<!-- Prompt: prompts/html-closer.prompt.md (sha256: ${sha}). --!>\n` },
      { path: 'src/h4.html', content: `<!-- Prompt: prompts/html-closer.prompt.md sha256=${sha} -->\n` },
      { path: 'src/bad.html', content: `<!-- Prompt: prompts/html-closer.prompt.md trailing garbage -->\n` },
    ],
  });
  assert.deepEqual(htmlHeaderDetected.nativeOnlyModules, ['src/h1.html', 'src/h2.html', 'src/h3.html', 'src/h4.html']);

  // R3-2 [P1]: isSameLineLoopEnclosing rejects closed .map() followed by assert.ok(execFileSync(...)) and accepts brace-less for (...).
  const closedMapWithAssert = `
    import { execFileSync } from 'node:child_process';
    import { mkdtempSync } from 'node:fs';
    mkdtempSync('/tmp/x-');
    const xs = ['a'].map(x => x); assert.ok(execFileSync(process.execPath, xs));
  `;
  const closedMapAssertProbe = detectRealHostProbesInTest('test/closed-map-assert.test.mjs', closedMapWithAssert);
  assert.equal(closedMapAssertProbe.detectedTurns, 1);
  assert.ok(!closedMapAssertProbe.classes.includes('multi-turn-cli-state'));

  const bracelessFor = `
    import { execFileSync } from 'node:child_process';
    import { mkdtempSync } from 'node:fs';
    mkdtempSync('/tmp/x-');
    for (const t of ['a', 'b']) execFileSync(process.execPath, ['-e', t]);
  `;
  const bracelessForProbe = detectRealHostProbesInTest('test/braceless-for.test.mjs', bracelessFor);
  assert.ok(bracelessForProbe.detectedTurns >= 2);
  assert.ok(bracelessForProbe.classes.includes('multi-turn-cli-state'));

  const closedBlockForWithAssert = `
    import { execFileSync } from 'node:child_process';
    import { mkdtempSync } from 'node:fs';
    mkdtempSync('/tmp/x-');
    for (let i = 0; i < 2; i++) { const o = { a: i }; } assert.ok(execFileSync(process.execPath, ['-e', '0']));
  `;
  assert.equal(detectRealHostProbesInTest('test/closed-block-for.test.mjs', closedBlockForWithAssert).detectedTurns, 1);

  // R3-3 [P1]: Direct namespace property assignment stubbing (cp.spawnSync=, fs.statSync=, bracket/defineProperty) + CJS/ESM aliased named bindings.
  const propAssignStubs = [
    `import * as cp from 'node:child_process';\ncp.spawnSync = () => ({ status: 0 });\ncp.spawnSync('git', ['status']);`,
    `import * as cp from 'node:child_process';\ncp['spawnSync'] = () => ({ status: 0 });\ncp.spawnSync('git', ['status']);`,
    `import * as cp from 'node:child_process';\nObject.defineProperty(cp, 'spawnSync', { value: () => ({ status: 0 }) });\ncp.spawnSync('git', ['status']);`,
    `import fs from 'node:fs';\nfs.statSync = () => ({ uid: 0 });\nfs.statSync('/dev/tty');`,
    `import tty from 'node:tty';\ntty.isatty = () => true;\ntty.isatty(0);`,
    `import sqlite from 'node:sqlite';\nsqlite.DatabaseSync = class {};\nnew sqlite.DatabaseSync(':memory:');`,
    `let { spawnSync: run } = require('node:child_process');\nrun = () => ({ status: 0 });\nrun(process.execPath, ['-e', '0']);`,
  ];
  for (const code of propAssignStubs) {
    assert.equal(
      detectRealHostProbesInTest('test/prop-stub.test.mjs', code).hasRealHostSmoke,
      false,
      `property-stubbed or reassigned binding must be rejected: ${code}`,
    );
  }

  const cjsAliasedSubprocess = `
    const { spawnSync: run } = require('node:child_process');
    const { mkdtempSync: makeTmp } = require('node:fs');
    makeTmp('/tmp/cjs-');
    run(process.execPath, ['-e', '0']);
    run(process.execPath, ['-e', '0']);
  `;
  const cjsAliasProbe = detectRealHostProbesInTest('test/cjs-alias.test.mjs', cjsAliasedSubprocess);
  assert.equal(cjsAliasProbe.hasRealHostSmoke, true);
  assert.equal(cjsAliasProbe.detectedTurns, 2);
  assert.ok(cjsAliasProbe.classes.includes('multi-turn-cli-state'));

  const esmAliasedSubprocess = `
    import { execFileSync as runCli } from 'node:child_process';
    runCli('sandbox-exec', ['-p', '(version 1)', '/usr/bin/true']);
  `;
  const esmAliasProbe = detectRealHostProbesInTest('test/esm-alias.test.mjs', esmAliasedSubprocess);
  assert.equal(esmAliasProbe.hasRealHostSmoke, true);
  assert.ok(esmAliasProbe.classes.includes('nested-sandbox'));

  const cjsAliasedFsAndDb = `
    const { statSync: checkDev } = require('node:fs');
    const { DatabaseSync: DB } = require('node:sqlite');
    checkDev('/dev/tty');
    const db = new DB(':memory:');
  `;
  const cjsFsDbProbe = detectRealHostProbesInTest('test/cjs-fs-db.test.mjs', cjsAliasedFsAndDb);
  assert.equal(cjsFsDbProbe.hasRealHostSmoke, true);
  assert.ok(cjsFsDbProbe.classes.includes('host-tty-ownership'));
  assert.ok(detectRealE2eKindsInTest('test/cjs-fs-db.test.mjs', cjsAliasedFsAndDb).includes('local-server-or-db'));

  // R3-4 [P2]: Mocked/reassigned/property-stubbed page.goto rejected even when Playwright is imported.
  const browserMockBypasses = [
    `import { test } from '@playwright/test';\nconst page = { goto: mock.fn() };\nawait page.goto('http://127.0.0.1:3000');`,
    `import { test } from '@playwright/test';\nconst page =\n  { goto: mock.fn() };\nawait page.goto('http://127.0.0.1:3000');`,
    `import { test } from '@playwright/test';\ntest('x', async ({ page }) => {\n  page = { goto: () => {} };\n  await page.goto('http://127.0.0.1:3000');\n});`,
    `import { test } from '@playwright/test';\ntest('x', async ({ page }) => {\n  page.goto = mock.fn();\n  await page.goto('http://127.0.0.1:3000');\n});`,
    `import { chromium } from 'playwright';\nawait page.goto('http://127.0.0.1:3000');`,
  ];
  for (const code of browserMockBypasses) {
    assert.ok(
      !detectRealE2eKindsInTest('test/browser-bypass.test.mjs', code).includes('browser-playwright'),
      `mocked/unlaunched browser must not pass: ${code}`,
    );
  }
});

test('R3b adversarial regression suite: items 1 through 5', () => {
  // R3b-1 [P1]: Object/class method shorthand `async fetch(url) { ... }` / `fetch(url) { ... }` does NOT spoof bare global fetch(...).
  const fetchMethodShorthands = [
    `const fakeClient = { async fetch(url) { return { ok: true, url }; } };`,
    `const fakeClient = { fetch(url) { return { ok: true, url }; } };`,
    `class FakeHttp { static fetch(url) { return url; } async fetch(url) { return url; } }`,
    `const fakeClient = { async fetch(url: string): Promise<Response> { return null; } };`,
  ];
  for (const code of fetchMethodShorthands) {
    assert.equal(detectRealHostProbesInTest('test/fetch-method.test.mjs', code).hasRealHostSmoke, false, `method shorthand must not spoof fetch: ${code}`);
    assert.ok(!detectRealE2eKindsInTest('test/fetch-method.test.mjs', code).includes('local-server-or-db'));
  }
  assert.equal(
    detectRealHostProbesInTest('test/fetch-if.test.mjs', `if (await fetch('http://127.0.0.1:3000/ok')) { console.log('ok'); }`).hasRealHostSmoke,
    true,
  );

  // R3b-2 [P1]: Span-scoped authentic require skipping, non-classified/non-browser import shadowing, comma-const, EOL `const page =`, and general destructured browser vars.
  const wrappedRequireShadow = `
    import { spawnSync } from 'node:child_process';
    const spawnSync = wrap(require('./fake-cp.cjs'));
    spawnSync('git', ['status']);
  `;
  assert.equal(detectRealHostProbesInTest('test/wrapped-req.test.mjs', wrappedRequireShadow).hasRealHostSmoke, false);

  const sameLineRequireAndShadow = `
    const { spawnSync } = require('node:child_process'); const fetch = () => ({ ok: true });
    await fetch('http://127.0.0.1:3000');
  `;
  assert.ok(!detectRealE2eKindsInTest('test/same-line-req-shadow.test.mjs', sameLineRequireAndShadow).includes('local-server-or-db'));

  const nonBrowserImportPage = `
    import { test } from '@playwright/test';
    import { page } from './fake-page.mjs';
    await page.goto('http://127.0.0.1:3000');
  `;
  assert.ok(!detectRealE2eKindsInTest('test/non-browser-page.test.mjs', nonBrowserImportPage).includes('browser-playwright'));

  const commaConstPageAndFetch = `
    import { test } from '@playwright/test';
    const a = 1, page = { goto: mock.fn() }, fetch = () => ({ ok: true });
    await page.goto('http://127.0.0.1:3000');
    await fetch('http://127.0.0.1:3000');
  `;
  assert.equal(detectRealHostProbesInTest('test/comma-const.test.mjs', commaConstPageAndFetch).hasRealHostSmoke, false);

  const destructuredCustomBrowserVar = `
    import { test } from '@playwright/test';
    const { p } = { p: { goto: mock.fn() } };
    await p.goto('http://127.0.0.1:3000');
  `;
  assert.ok(!detectRealE2eKindsInTest('test/destructured-p.test.mjs', destructuredCustomBrowserVar).includes('browser-playwright'));

  // R3b-3 [P2]: Spaced and multiline member access on authentic imported namespaces.
  const multilineHttp = `
    import http from 'node:http';
    const srv = http.
      createServer((req, res) => res.end('ok'));
  `;
  assert.ok(detectRealE2eKindsInTest('test/multiline-http.test.mjs', multilineHttp).includes('local-server-or-db'));

  const spacedAndMultilineCp = `
    import * as cp from 'node:child_process';
    cp. spawnSync(process.execPath, ['-e', '0']);
    cp.
      execFileSync(process.execPath, ['-e', '0']);
  `;
  const spacedCpProbe = detectRealHostProbesInTest('test/spaced-cp.test.mjs', spacedAndMultilineCp);
  assert.equal(spacedCpProbe.hasRealHostSmoke, true);
  assert.equal(spacedCpProbe.detectedTurns, 2);

  const spacedSqlite = `
    import sqlite from 'node:sqlite';
    const db = new sqlite.
      DatabaseSync(':memory:');
  `;
  assert.ok(detectRealE2eKindsInTest('test/spaced-sqlite.test.mjs', spacedSqlite).includes('local-server-or-db'));

  // R3b-4 [P2]: TypeScript inline `type` imports and unused node:sqlite + unrelated `new Client()`.
  const tsTypeOnlyPool = `
    import { type Pool } from 'pg';
    const p: Pool | null = null;
  `;
  assert.equal(detectRealHostProbesInTest('test/ts-type-pool.test.mjs', tsTypeOnlyPool).hasRealHostSmoke, false);
  assert.ok(!detectRealE2eKindsInTest('test/ts-type-pool.test.mjs', tsTypeOnlyPool).includes('local-server-or-db'));

  const unusedSqliteWithUnrelatedClient = `
    import { DatabaseSync } from 'node:sqlite';
    class Client {}
    const c = new Client();
  `;
  assert.equal(detectRealHostProbesInTest('test/unused-sqlite-client.test.mjs', unusedSqliteWithUnrelatedClient).hasRealHostSmoke, false);
  assert.ok(!detectRealE2eKindsInTest('test/unused-sqlite-client.test.mjs', unusedSqliteWithUnrelatedClient).includes('local-server-or-db'));

  // R3b-5 [P2]: Empty string repeat across comment/newline computes 0 bytes, `$`-named devicePathVar passes, spaced member access & object property key rejected.
  const commentedEmptyRepeat = `
    import { execFileSync } from 'node:child_process';
    const a = "" /* comment */ .repeat(10000);
    const b = ""
      // line comment
      .repeat(10000);
    execFileSync(process.execPath, ['-e', '0']);
  `;
  const commentedRepeatProbe = detectRealHostProbesInTest('test/comment-empty-repeat.test.mjs', commentedEmptyRepeat);
  assert.ok((commentedRepeatProbe.maxDetectedPayloadBytes ?? 0) <= MIN_REALISTIC_PAYLOAD_BYTES);
  assert.ok(!commentedRepeatProbe.classes.includes('full-size-payload'));

  const dollarDeviceVar = `
    import { statSync } from 'node:fs';
    const $tty = '/dev/tty';
    statSync($tty);
  `;
  assert.ok(detectRealHostProbesInTest('test/dollar-tty.test.mjs', dollarDeviceVar).classes.includes('host-tty-ownership'));

  const propKeyAndSpacedMemberFs = `
    import { statSync } from 'node:fs';
    const p = '/dev/tty';
    statSync('/tmp/foo', { p: true });
    statSync('/tmp/foo', { a: 1, p: true });
    statSync(obj . p);
  `;
  assert.equal(detectRealHostProbesInTest('test/fs-prop-key-spoof.test.mjs', propKeyAndSpacedMemberFs).hasRealHostSmoke, false);
});

test('R4 adversarial regression suite: items 1 through 8', () => {
  // R4-1 [P1]: Semicolon-free CJS `const cp = require(...)` works AND earlier shadows on prior lines are NOT swallowed into authenticRequireSpans.
  const semiFreeCjs = [
    `const x = 1`,
    `const cp = require('node:child_process')`,
    `cp.execFileSync(process.execPath, ['-e', '0'])`,
  ].join('\n');
  assert.equal(detectRealHostProbesInTest('test/semi-free-cjs.test.mjs', semiFreeCjs).hasRealHostSmoke, true);

  const priorLineFetchShadowBeforeRequire = [
    `const fetch = () => ({ ok: true })`,
    `const cp = require('node:child_process')`,
    `await fetch('http://127.0.0.1:3000')`,
  ].join('\n');
  assert.equal(detectRealHostProbesInTest('test/prior-shadow-cjs.test.mjs', priorLineFetchShadowBeforeRequire).hasRealHostSmoke, false);
  assert.ok(!detectRealE2eKindsInTest('test/prior-shadow-cjs.test.mjs', priorLineFetchShadowBeforeRequire).includes('local-server-or-db'));

  // R4-2 [P1]: Shadowed or reassigned imported namespace bindings are rejected.
  const namespaceShadowCases = [
    `let cp = require('node:child_process');\ncp = { spawnSync: () => ({ status: 0 }) };\ncp.spawnSync('git', ['status']);`,
    `import * as cp from 'node:child_process';\nfunction run() { const cp = fakeCp; cp.spawnSync('git', ['status']); }`,
    `import * as cp from 'node:child_process';\nconst { cp } = { cp: fakeCp };\ncp.spawnSync('git', ['status']);`,
    `import fs from 'node:fs';\nlet fs = { statSync: () => ({}) };\nfs.statSync('/dev/tty');`,
  ];
  for (const code of namespaceShadowCases) {
    assert.equal(detectRealHostProbesInTest('test/ns-shadow.test.mjs', code).hasRealHostSmoke, false, `shadowed namespace must fail: ${code}`);
  }

  // R4-3 [P1]: Spaced/multiline member `fakeClient . fetch(...)` and `fakeClient.\n fetch(...)` do NOT pass as bare global fetch.
  const spacedMemberFetchCases = [
    `fakeClient . fetch('http://127.0.0.1:3000');`,
    `fakeClient.\n  fetch('http://127.0.0.1:3000');`,
  ];
  for (const code of spacedMemberFetchCases) {
    assert.equal(detectRealHostProbesInTest('test/spaced-fetch.test.mjs', code).hasRealHostSmoke, false, `member fetch must not spoof global fetch: ${code}`);
  }

  // R4-4 [P1]: 3-hop `a.b.page.goto` rejected AND multiline destructuring shadows `page` / `fetch`.
  const threeHopBrowser = `
    import { test } from '@playwright/test';
    await a.b.page.goto('http://127.0.0.1:3000');
  `;
  assert.ok(!detectRealE2eKindsInTest('test/three-hop-browser.test.mjs', threeHopBrowser).includes('browser-playwright'));

  const multilineDestructureShadow = `
    import { test } from '@playwright/test';
    const {
      page,
      fetch,
    } = { page: { goto: mock.fn() }, fetch: () => ({ ok: true }) };
    await page.goto('http://127.0.0.1:3000');
    await fetch('http://127.0.0.1:3000');
  `;
  assert.equal(detectRealHostProbesInTest('test/multiline-destr.test.mjs', multilineDestructureShadow).hasRealHostSmoke, false);

  // R4-5 [P2]: Pass-order bypasses (destructured browser / prop-stubbed chromium.launch before derived page) are rejected.
  const browserPassOrderCases = [
    `import { test } from '@playwright/test';\nconst { browser } = { browser: { newPage: () => ({ goto: () => {} }) } };\nconst page = browser.newPage();\nawait page.goto('http://127.0.0.1:3000');`,
    `import { chromium } from 'playwright';\nchromium.launch = async () => ({ newPage: async () => ({ goto: async () => {} }) });\nconst browser = await chromium.launch();\nconst page = await browser.newPage();\nawait page.goto('http://127.0.0.1:3000');`,
    `import { chromium } from 'playwright';\nconst browser = await chromium.launch();\nconst page = await browser.newPage();\nchromium.launch = async () => ({});\nawait page.goto('http://127.0.0.1:3000');`,
  ];
  for (const code of browserPassOrderCases) {
    assert.ok(!detectRealE2eKindsInTest('test/browser-pass-order.test.mjs', code).includes('browser-playwright'), `pass-order bypass must fail: ${code}`);
  }

  // R4-6 [P2]: TS non-async `fetch(url: string): Promise<Response> { ... }` method shorthand rejected, while ternary `cond ? fetch(url) : ...` passes.
  const tsNonAsyncFetchMethod = `
    class FakeHttp {
      fetch(url: string): Promise<Response> { return Promise.resolve(null as any); }
    }
  `;
  assert.equal(detectRealHostProbesInTest('test/ts-fetch-method.test.mjs', tsNonAsyncFetchMethod).hasRealHostSmoke, false);
  const tsGenericFetchMethod = `
    const fake = {
      fetch(url: string): Promise<{ ok: boolean }> { return Promise.resolve({ ok: true }); }
    };
  `;
  assert.equal(detectRealHostProbesInTest('test/ts-fetch-generic.test.mjs', tsGenericFetchMethod).hasRealHostSmoke, false);
  assert.equal(
    detectRealHostProbesInTest('test/ternary-fetch.test.mjs', `const r = ok ? fetch('http://127.0.0.1:3000') : () => { return null; };`).hasRealHostSmoke,
    true,
  );
  assert.equal(
    detectRealHostProbesInTest('test/ternary-fetch-obj.test.mjs', `const r = ok ? fetch('http://127.0.0.1:3000') : { ok: false };`).hasRealHostSmoke,
    true,
  );

  // R4-7 [P2]: `obj.for(1) || execFileSync(...)` and `for (...) if (true) {} execFileSync(...)` report 1 turn (NOT 2).
  const memberForSpoof = `
    import { execFileSync } from 'node:child_process';
    import { mkdtempSync } from 'node:fs';
    mkdtempSync('/tmp/x-');
    obj.for(1) || execFileSync(process.execPath, ['-e', '0']);
  `;
  assert.equal(detectRealHostProbesInTest('test/member-for.test.mjs', memberForSpoof).detectedTurns, 1);

  const spacedMemberForSpoof = `
    import { execFileSync } from 'node:child_process';
    import { mkdtempSync } from 'node:fs';
    mkdtempSync('/tmp/x-');
    obj . while(1) || execFileSync(process.execPath, ['-e', '0']);
  `;
  assert.equal(detectRealHostProbesInTest('test/spaced-member-while.test.mjs', spacedMemberForSpoof).detectedTurns, 1);

  const bracelessForClosedIfBlock = `
    import { execFileSync } from 'node:child_process';
    import { mkdtempSync } from 'node:fs';
    mkdtempSync('/tmp/x-');
    for (const x of [1, 2]) if (true) {} execFileSync(process.execPath, ['-e', '0']);
  `;
  assert.equal(detectRealHostProbesInTest('test/for-if-closed.test.mjs', bracelessForClosedIfBlock).detectedTurns, 1);

  // R4-8 [P2]: `$`-prefixed bindings (`$run(...)`, `$cp.spawnSync(...)`) work cleanly AND multiline `cp.\n spawnSync = ...` is caught.
  const dollarAliasedBindings = `
    const { spawnSync: $run } = require('node:child_process');
    const $cp = require('node:child_process');
    $run(process.execPath, ['-e', '0']);
    $cp.execFileSync(process.execPath, ['-e', '0']);
  `;
  const dollarProbe = detectRealHostProbesInTest('test/dollar-bindings.test.mjs', dollarAliasedBindings);
  assert.equal(dollarProbe.hasRealHostSmoke, true);
  assert.equal(dollarProbe.detectedTurns, 2);

  const multilinePropStub = `
    import * as $cp from 'node:child_process';
    $cp.
      spawnSync = () => ({ status: 0 });
    $cp.spawnSync('git', ['status']);
  `;
  assert.equal(detectRealHostProbesInTest('test/multiline-prop-stub.test.mjs', multilinePropStub).hasRealHostSmoke, false);
});
