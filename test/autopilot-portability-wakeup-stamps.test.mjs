import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, existsSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { coreWorld } from './helpers/core-world.mjs';
import { runAutopilotLauncher, tickAutopilot } from '../src/autopilot-launcher.mjs';
import { detectTestCommand, readCoreSettings, openPullRequest } from '../src/autopilot-core.mjs';
import { jobEnvironment, startAgentJob, readAgentJob, stopAgentJob, waitForAgentJob } from '../src/agent-job.mjs';

const tempDir = t => {
  const dir = mkdtempSync(join(tmpdir(), 'pdd-3460-'));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
};

const until = async (check, ms = 8000) => {
  const deadline = Date.now() + ms;
  while (Date.now() < deadline) {
    const value = check();
    if (value) return value;
    await new Promise(resolve => setTimeout(resolve, 20));
  }
  assert.fail('condition not reached before timeout');
};

function seedRepo(w, files) {
  for (const [rel, content] of Object.entries(files)) {
    const target = join(w.cwd, rel);
    mkdirSync(join(target, '..'), { recursive: true });
    writeFileSync(target, content);
  }
  w.git(w.cwd, 'add', '.');
  w.git(w.cwd, 'commit', '-qm', 'seed files');
  w.git(w.cwd, 'push', '-q', 'origin', 'main');
}

function launcherPortsForWorld(w, extra = {}) {
  const cwd = w.git(w.cwd, 'rev-parse', '--show-toplevel');
  const stateRoot = join(w.dir, 'launcher-state');
  const id = createHash('sha256').update(cwd).digest('hex').slice(0, 20);
  const stateFile = join(stateRoot, `${id}.json`);
  const projectDir = join(stateRoot, id);
  mkdirSync(stateRoot, { recursive: true });
  const env = { HOME: process.env.HOME, PATH: process.env.PATH, GH_TOKEN: 'ghs_secret_token_for_build' };
  const ghCalls = [];
  const ports = {
    stateRoot,
    now: w.now,
    env,
    timer: async () => true,
    warn: () => {},
    doctorPorts: {
      run: async () => ({ code: 0, stdout: 'ok', stderr: '' }),
      checkAgents: async () => [{ id: 'codex', kind: 'codex', command: 'codex', ok: true }],
      selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex' }),
    },
    selectAgent: async () => ({ id: 'codex', kind: 'codex', command: 'codex' }),
    allocationCheck: async () => ({ state: 'ready', message: '' }),
    run: async (command, args, options = {}) => {
      if (command === 'gh') {
        ghCalls.push(args);
        if (args[0] === 'repo' && args[1] === 'view') {
          return { code: 0, stdout: JSON.stringify({ nameWithOwner: 'acme/widgets', defaultBranchRef: { name: 'main' }, url: 'https://github.com/acme/widgets' }), stderr: '' };
        }
        if (args[0] === 'auth') return { code: 0, stdout: 'logged in', stderr: '' };
        return w.gh(args, options);
      }
      if (command === 'git') {
        const r = spawnSync('git', args, { cwd: options.cwd ?? cwd, encoding: 'utf8' });
        return { code: r.status ?? 1, stdout: r.stdout ?? '', stderr: r.stderr ?? '' };
      }
      return { code: 0, stdout: '', stderr: '' };
    },
    machineGuard: w.machineGuard,
    corePorts: {
      jobs: w.jobs,
      checkBase: async () => ({ exitCode: 0, message: 'ok' }),
      agentReady: async () => true,
      ...extra.corePorts,
    },
    ...extra.ports,
  };
  return { cwd, stateRoot, stateFile, projectDir, ghCalls, ports };
}

test('3460-1a: external repo without pdd.json accepts start --engine core --mode observe/auto with --label', async t => {
  const w = await coreWorld(t);
  rmSync(join(w.cwd, 'pdd.json'), { force: true });
  assert.equal(existsSync(join(w.cwd, 'pdd.json')), false);
  const { cwd, stateFile, ports } = launcherPortsForWorld(w);

  // Without --mode and no pdd.json, start stays off and asks the user to choose observe or auto; --mode off is rejected with exit 2.
  const withoutMode = await runAutopilotLauncher({ command: 'start', engine: 'core', label: 'pdd:autopilot', cwd, packageRoot: resolve('.'), env: ports.env, issues: [] }, ports);
  assert.equal(withoutMode.exitCode, 0);
  assert.match(withoutMode.message, /Choose observe or auto/);
  assert.equal(JSON.parse(readFileSync(stateFile, 'utf8')).enabled, false, 'not enabled without --mode when pdd.json is absent');

  let timerStops = 0, timerStarts = 0;
  const trackedPorts = { ...ports, timer: async action => { if (action === 'start') { timerStarts++; return true; } if (action === 'stop') { timerStops++; return false; } return false; } };

  // Passing --mode observe on an external repo without pdd.json succeeds and keeps pdd.json absent.
  const started = await runAutopilotLauncher({ command: 'start', engine: 'core', mode: 'observe', label: 'pdd:autopilot', cwd, packageRoot: resolve('.'), env: ports.env, issues: [] }, trackedPorts);
  assert.equal(started.exitCode, 0, started.message);
  assert.equal(existsSync(join(w.cwd, 'pdd.json')), false, 'external repo is not polluted with pdd.json');
  assert.equal(timerStarts, 1);
  const saved = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(saved.enabled, true);
  assert.equal(saved.mode, 'observe');
  assert.equal(saved.engine, 'core');
  assert.equal(saved.label, 'pdd:autopilot');

  // Passing --mode off on an enabled installation saves mode off, disables Autopilot, and stops the timer.
  const turnedOff = await runAutopilotLauncher({ command: 'start', engine: 'core', mode: 'off', label: 'pdd:autopilot', cwd, packageRoot: resolve('.'), env: ports.env, issues: [] }, trackedPorts);
  assert.equal(turnedOff.exitCode, 0, turnedOff.message);
  assert.match(turnedOff.message, /mode off is saved and the timer is stopped/);
  assert.equal(timerStops, 1, 'active timer stopped by --mode off');
  const disabledState = JSON.parse(readFileSync(stateFile, 'utf8'));
  assert.equal(disabledState.enabled, false, 'disabled when --mode off');
  assert.equal(disabledState.mode, 'off');
  assert.equal(disabledState.timerInstalled, false);
});

test('3460-1b: detectTestCommand and readCoreSettings auto-detect standard external repo runners and lockfile suite installs', async t => {
  const root = tempDir(t);
  const cases = [
    ['pnpm', { 'pnpm-lock.yaml': 'lockfileVersion: 9.0\n', 'package.json': '{}' }, 'pnpm test'],
    ['yarn', { 'yarn.lock': '# yarn\n', 'package.json': '{}' }, 'yarn test'],
    ['bunb', { 'bun.lockb': '' }, 'bun test'],
    ['bun', { 'bun.lock': '{}' }, 'bun test'],
    ['pyproject', { 'pyproject.toml': '[project]\nname = "demo"\n' }, 'pytest'],
    ['pytest', { 'pytest.ini': '[pytest]\n' }, 'pytest'],
    ['cargo', { 'Cargo.toml': '[package]\nname = "demo"\n' }, 'cargo test'],
    ['go', { 'go.mod': 'module example.com/demo\n' }, 'go test ./...'],
    ['npm-pkg', { 'package.json': '{"name":"demo"}' }, 'npm test'],
    ['empty', {}, null],
  ];
  for (const [name, files, expected] of cases) {
    const dir = join(root, name);
    mkdirSync(dir, { recursive: true });
    for (const [rel, body] of Object.entries(files)) writeFileSync(join(dir, rel), body);
    assert.equal(detectTestCommand(dir), expected, `detectTestCommand for ${name}`);
    assert.equal(readCoreSettings(dir).testCommand, expected, `readCoreSettings for ${name}`);
  }
  // Explicit pdd.json autopilot.testCommand always overrides auto-detection.
  const customDir = join(root, 'custom');
  mkdirSync(customDir, { recursive: true });
  writeFileSync(join(customDir, 'Cargo.toml'), '[package]\nname = "demo"\n');
  writeFileSync(join(customDir, 'pdd.json'), JSON.stringify({ autopilot: { testCommand: 'cargo nextest run' } }));
  assert.equal(readCoreSettings(customDir).testCommand, 'cargo nextest run');

  // External pnpm repo runs pnpm install --frozen-lockfile before pnpm test in suiteState.
  const w = await coreWorld(t, { settings: { testCommand: null } });
  seedRepo(w, { 'pnpm-lock.yaml': 'lockfileVersion: 9.0\n', 'package.json': JSON.stringify({ name: 'ext', devDependencies: { vitest: '^2.0.0' }, scripts: { test: 'vitest run' } }) });
  w.settings.testCommand = readCoreSettings(w.cwd).testCommand;
  assert.equal(w.settings.testCommand, 'pnpm test');
  w.issue(17);
  await w.tick();
  w.build(17, { body: 'Fixes #17\n\nRuntime: not run (no prompt changed)\nEvidence: runtime=not-run; vectors=not-run; formal=not-applicable; tests=pass (1/1)' });
  await w.tick();
  const suiteJob = w.job(17, 'suite');
  assert.ok(suiteJob, 'suite job started');
  assert.match(suiteJob.args.join(' '), /pnpm install --frozen-lockfile --ignore-scripts/);
  assert.match(suiteJob.args.join(' '), /pnpm test/);

  // External Yarn Modern repo selects --immutable --mode=skip-build instead of Classic-only --ignore-scripts.
  const wy = await coreWorld(t, { settings: { testCommand: null } });
  seedRepo(wy, {
    'yarn.lock': '# This file is generated by running "yarn install".\n\n__metadata:\n  version: 8\n',
    '.yarnrc.yml': 'nodeLinker: node-modules\n',
    'package.json': JSON.stringify({ name: 'ext-yarn', packageManager: 'yarn@4.5.1', devDependencies: { vitest: '^2.0.0' }, scripts: { test: 'vitest run' } }),
  });
  wy.settings.testCommand = readCoreSettings(wy.cwd).testCommand;
  assert.equal(wy.settings.testCommand, 'yarn test');
  wy.issue(18);
  await wy.tick();
  wy.build(18, { body: 'Fixes #18\n\nRuntime: not run (no prompt changed)\nEvidence: runtime=not-run; vectors=not-run; formal=not-applicable; tests=pass (1/1)' });
  await wy.tick();
  const yarnSuiteJob = wy.job(18, 'suite');
  assert.ok(yarnSuiteJob, 'yarn modern suite job started');
  const yarnShellScript = yarnSuiteJob.args[1];
  assert.match(yarnShellScript, /yarn install --immutable --mode=skip-build/);
  assert.match(yarnShellScript, /\*\) yarn install --immutable --mode=skip-build ;;/, 'static fallback for Yarn Modern also uses --immutable --mode=skip-build');
  assert.match(yarnSuiteJob.args.join(' '), /yarn test/);
});

test('3460-2: tickAutopilot persists GitHub ETags across poll ticks so unchanged core GETs send If-None-Match and reuse 304 responses', async t => {
  const w = await coreWorld(t);
  w.issue(17, { labels: ['pdd:autopilot'] });
  const { cwd, stateFile, projectDir, ghCalls, ports } = launcherPortsForWorld(w);
  writeFileSync(stateFile, JSON.stringify({
    enabled: true,
    engine: 'core',
    mode: 'observe',
    label: 'pdd:autopilot',
    cwd,
    repo: 'acme/widgets',
    defaultBranch: 'main',
    coordinatorId: 'coord-a',
    machine: 'machine-a',
    agent: { id: 'codex', kind: 'codex', command: 'codex' },
    packageRoot: resolve('.'),
  }));

  await tickAutopilot(stateFile, ports);
  const { githubEtagCache } = await import('../src/github-calls.mjs');
  const etagFile = githubEtagCache({ root: dirname(stateFile), repository: 'acme/widgets' }).file;
  assert.equal(existsSync(etagFile), true, 'ETag cache file persisted after first tick');
  const savedEntries = JSON.parse(readFileSync(etagFile, 'utf8'));
  assert.ok(Object.keys(savedEntries).length > 0, 'ETag cache holds GET endpoints from tickCore');

  ghCalls.length = 0;
  w.advance(60_000);
  await tickAutopilot(stateFile, ports);
  const conditionalGets = ghCalls.filter(args => args.some(arg => String(arg).startsWith('If-None-Match:')));
  assert.ok(conditionalGets.length > 0, 'second tick sends If-None-Match headers from persisted github-etags.json');
});

test('3460-3: startAgentJob fires wake immediately on normal exit, skips wake on stopAgentJob, and waitForAgentJob resolves with zero-poll latency', async t => {
  const dir = tempDir(t);
  const wakeMarker = join(dir, 'woke.json');
  const wakeScript = `require('fs').writeFileSync(${JSON.stringify(wakeMarker)}, JSON.stringify({ at: Date.now() }));`;

  const startedAt = Date.now();
  const fastJob = startAgentJob({
    id: '42-build-fast',
    dir,
    cwd: dir,
    command: process.execPath,
    args: ['-e', 'setTimeout(() => process.exit(0), 60);'],
    input: 'work\n',
    env: { PATH: process.env.PATH },
    wake: { command: process.execPath, args: ['-e', wakeScript], cwd: dir, env: { PATH: process.env.PATH } },
  });

  const waited = await waitForAgentJob([fastJob], { timeoutMs: 5000 });
  const elapsedMs = Date.now() - startedAt;
  assert.equal(waited.reason, 'worker-exit');
  assert.equal(waited.seen?.state, 'exited');
  assert.equal(waited.seen?.exit?.code, 0);
  assert.ok(elapsedMs < 1500, `waitForAgentJob resolved immediately without blind poll sleep (${elapsedMs}ms)`);

  await until(() => existsSync(wakeMarker));
  assert.ok(JSON.parse(readFileSync(wakeMarker, 'utf8')).at >= startedAt, 'detached wake fired right on normal worker completion');

  // A stopped job (stopAgentJob) must NOT fire wake.
  const stoppedWakeMarker = join(dir, 'stopped-woke.json');
  const slowJob = startAgentJob({
    id: '43-build-slow',
    dir,
    cwd: dir,
    command: process.execPath,
    args: ['-e', 'setInterval(() => {}, 1000);'],
    input: 'hang\n',
    env: { PATH: process.env.PATH },
    wake: { command: process.execPath, args: ['-e', `require('fs').writeFileSync(${JSON.stringify(stoppedWakeMarker)}, 'bad');`], cwd: dir, env: { PATH: process.env.PATH } },
  });
  await new Promise(resolve => setTimeout(resolve, 80));
  stopAgentJob(slowJob);
  await until(() => readAgentJob(slowJob).state === 'exited', 5000);
  await new Promise(resolve => setTimeout(resolve, 100));
  assert.equal(existsSync(stoppedWakeMarker), false, 'stopped worker does not fire wake');
});

test('3460-4: openPullRequest and advance deterministically create and stamp PR metadata without LLM hand-typed Path/Runtime/Evidence lines', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seedRepo(w, {
    'prompts/duration.prompt.md': '# Duration\n\nFormat seconds for the dashboard.\n',
    'user_stories/duration.md': '# Duration story\n\nUnder one minute shows seconds.\n',
    'src/duration.js': '// Generated from prompts/duration.prompt.md\nexport const formatDuration = s => `${Math.floor(s / 60)}m`;\n',
    'test/duration.test.js': 'import assert from "node:assert/strict";\nimport { formatDuration } from "../src/duration.js";\nassert.equal(typeof formatDuration, "function");\n',
    'pdd-bindings.json': JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [{ module: 'src/duration.js', prompt: 'prompts/duration.prompt.md', stories: ['user_stories/duration.md'] }],
    }),
  });
  w.issue(17, { title: 'Show seconds under one minute', body: 'Make formatDuration(45) return "45s".' });
  await w.tick();

  const buildJob = w.job(17, 'build');
  // Builder edits prompt, story, owned module, test, and an unowned README, pushes branch, and does NOT run gh pr create or type Path/Runtime/Evidence!
  writeFileSync(join(buildJob.cwd, 'prompts/duration.prompt.md'), '# Duration\n\nFormat durations under 60s as "<N>s" and 60s+ as minutes.\n');
  writeFileSync(join(buildJob.cwd, 'src/duration.js'), '// Generated from prompts/duration.prompt.md\nexport const formatDuration = s => s < 60 ? `${s}s` : `${Math.floor(s / 60)}m`;\n');
  writeFileSync(join(buildJob.cwd, 'test/duration.test.js'), 'import assert from "node:assert/strict";\nimport { formatDuration } from "../src/duration.js";\nassert.equal(formatDuration(45), "45s");\n');
  writeFileSync(join(buildJob.cwd, 'README.md'), '# Widgets\n\nUpdated docs.\n');
  w.git(buildJob.cwd, 'add', '.');
  w.git(buildJob.cwd, 'commit', '-qm', 'implement seconds formatting');
  w.git(buildJob.cwd, 'push', '-q', 'origin', `HEAD:${buildJob.branch}`);
  const head = w.git(buildJob.cwd, 'rev-parse', 'HEAD');
  w.github.setChecks(head, 'success');

  w.finish(17, 'build', {
    result: {
      outcome: 'pr',
      head,
      title: 'fix: show seconds under one minute',
      summary: 'Formats durations below 60 seconds with an `s` suffix.',
      choices: ['Keep 60s and above in whole minutes (preserves existing minute labels)'],
      tests: { state: 'pass', passed: 4, total: 4 },
      runtime: { state: 'not-run', cause: 'real-binding-unavailable: no live binding in local test sandbox' },
    },
  });

  await w.tick();
  assert.equal(w.github.prs.size, 1, 'openPullRequest created PR on GitHub via REST API');
  const [pr] = [...w.github.prs.values()];
  assert.equal(pr.title, 'fix: show seconds under one minute');
  assert.match(pr.body, /^Fixes #17\b/m);
  assert.match(pr.body, /Choices Autopilot made:\n- Keep 60s and above in whole minutes/);
  assert.match(pr.body, /^Path: a — prompts\/duration\.prompt\.md, src\/duration\.js — prompts\/duration\.prompt\.md — prompt changed — Test: test\/duration\.test\.js$/m);
  assert.match(pr.body, /^Path: d — README\.md, test\/duration\.test\.js — unowned — no contract change — Test: test\/duration\.test\.js$/m);
  assert.match(pr.body, /^Runtime: PASS \(user_stories\/all\.md\)$/m);
  assert.match(pr.body, /^Evidence: runtime=pass; vectors=not-run; formal=not-applicable; tests=pass \(4\/4\)$/m);

  // Verify the deterministically stamped PR passes every mergeCheck rule and merges cleanly!
  assert.ok(w.job(17, 'review'), 'mergeCheck accepted stamped PR body and started review');
  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick();
  assert.equal(pr.merged, true, 'deterministically stamped PR merged cleanly with zero stamp repair rounds');

  // Direct openPullRequest call updates an existing PR idempotently without duplicating metadata lines.
  const second = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 17, branch: buildJob.branch, head, worktree: w.cwd, pr: pr.number, runtime: { state: 'not-run', cause: 'real-binding-unavailable' } },
    { pr: pr.number, head, summary: pr.body, tests: { state: 'pass', passed: 4, total: 4 }, ports: w.ports() },
  );
  assert.equal((second.body.match(/^Evidence:/gm) ?? []).length, 1, 'exactly one Evidence line after re-stamping');
  assert.equal((second.body.match(/^Fixes #17\b/gm) ?? []).length, 1, 'exactly one closing keyword line after re-stamping');

  // When no verified saved pdd test check exists at head, openPullRequest stamps honest Runtime: not run and never invents PASS.
  const noCheckStamp = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 17, branch: buildJob.branch, head, worktree: w.cwd, pr: pr.number, runtime: { state: 'not-run', cause: 'real-binding-unavailable' } },
    {
      pr: pr.number,
      head,
      summary: 'Summary only.',
      tests: { state: 'pass', passed: 4, total: 4 },
      ports: w.ports({ runtimeEvidence: async () => ({ tests: [], storyFiles: ['user_stories/duration.md'], checks: [] }) }),
    },
  );
  assert.match(noCheckStamp.body, /^Runtime: not run \(.+\)$/m);
  assert.match(noCheckStamp.body, /^Evidence: runtime=not-run; vectors=not-run; formal=not-applicable; tests=pass \(4\/4\)$/m);

  // #3654: Plain-Markdown prompt without a matching Story or caller cause stamps "no Story reaches ...", never "has no Runtime interface".
  const plainNoCauseStamp = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 17, branch: buildJob.branch, head, worktree: w.cwd, pr: pr.number },
    {
      pr: pr.number,
      head,
      summary: 'Summary only.',
      tests: { state: 'pass', passed: 4, total: 4 },
      ports: w.ports({ runtimeEvidence: async () => ({ tests: [], storyFiles: [], checks: [] }) }),
    },
  );
  assert.match(plainNoCauseStamp.body, /^Runtime: not run \(no Story reaches prompts\/duration\.prompt\.md\)$/m);
  assert.doesNotMatch(plainNoCauseStamp.body, /has no Runtime interface/);

  // #3654: Frontmatter kind: native-only prompt stamps "Runtime: not run (native-only prompt)", while malformed native-only (missing reason) does not.
  const nativeParent = mkdtempSync(join(tmpdir(), 'pdd-native-3654-'));
  t.after(() => rmSync(nativeParent, { recursive: true, force: true }));
  const nativeWorktree = join(nativeParent, 'wt');
  w.git(w.cwd, 'worktree', 'add', '-q', '-b', 'feat/native-only-3654', nativeWorktree, 'origin/main');
  writeFileSync(join(nativeWorktree, 'prompts/duration.prompt.md'), '---\nkind: native-only\nreason: direct host clock binding\n---\n# Duration\n\nFormat durations.\n');
  w.git(nativeWorktree, 'add', 'prompts/duration.prompt.md');
  w.git(nativeWorktree, 'commit', '-qm', 'mark native-only');
  w.git(nativeWorktree, 'push', '-q', 'origin', 'HEAD:feat/native-only-3654');
  const nativeHead = w.git(nativeWorktree, 'rev-parse', 'HEAD');
  const nativeStamp = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 17, branch: 'feat/native-only-3654', head: nativeHead, worktree: w.cwd, pr: pr.number },
    {
      pr: pr.number,
      head: nativeHead,
      summary: 'Summary only.',
      tests: { state: 'pass', passed: 4, total: 4 },
      ports: w.ports({ runtimeEvidence: async () => ({ tests: [], storyFiles: [], checks: [] }) }),
    },
  );
  assert.match(nativeStamp.body, /^Runtime: not run \(native-only prompt\)$/m);

  writeFileSync(join(nativeWorktree, 'prompts/duration.prompt.md'), '---\nkind: native-only\n---\n# Duration\n\nFormat durations.\n');
  w.git(nativeWorktree, 'add', 'prompts/duration.prompt.md');
  w.git(nativeWorktree, 'commit', '-qm', 'malformed native-only');
  w.git(nativeWorktree, 'push', '-q', 'origin', 'HEAD:feat/native-only-3654');
  const badNativeHead = w.git(nativeWorktree, 'rev-parse', 'HEAD');
  const badNativeStamp = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 17, branch: 'feat/native-only-3654', head: badNativeHead, worktree: w.cwd, pr: pr.number },
    {
      pr: pr.number,
      head: badNativeHead,
      summary: 'Summary only.',
      tests: { state: 'pass', passed: 4, total: 4 },
      ports: w.ports({ runtimeEvidence: async () => ({ tests: [], storyFiles: [], checks: [] }) }),
    },
  );
  assert.doesNotMatch(badNativeStamp.body, /native-only prompt/);
  assert.match(badNativeStamp.body, /^Runtime: not run \(no Story reaches prompts\/duration\.prompt\.md\)$/m);
});

test('3460-5: clean repair resets untracked wreckage + injects 1-line round history, caps owner/issue context, and strips GitHub tokens from review env', async t => {
  // Verify jobEnvironment token stripping directly.
  const stripped = jobEnvironment({
    PATH: '/usr/bin',
    GH_TOKEN: 'secret1',
    GITHUB_TOKEN: 'secret2',
    GH_ENTERPRISE_TOKEN: 'secret3',
    GITHUB_ENTERPRISE_TOKEN: 'secret4',
    GITHUB_PERSONAL_ACCESS_TOKEN: 'secret5',
  }, { stripGithubTokens: true });
  assert.deepEqual(stripped, { PATH: '/usr/bin' });

  const w = await coreWorld(t, { settings: { runs: 1 } });
  // Seed 55 owned files (including src/z999.js cited by the issue) to test <= 40 ownerBrief cap + citation priority.
  const manyModules = Object.fromEntries(Array.from({ length: 55 }, (_, i) => [`src/m${String(i).padStart(3, '0')}.js`, `export const v = ${i};\n`]));
  manyModules['src/z999.js'] = 'export const target = 1;\n';
  seedRepo(w, {
    ...manyModules,
    'prompts/mod.prompt.md': '# Modules\n\nOwned modules.\n',
    'pdd-bindings.json': JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: Object.keys(manyModules).map(m => ({ module: m, prompt: 'prompts/mod.prompt.md', stories: ['user_stories/s.md'] })),
    }),
  });

  // Add 12 sibling trusted open issues to verify <= 5 sibling issue cap.
  for (let n = 2; n <= 13; n++) w.github.add(n, { title: `Sibling open issue ${n}`, body: `Details for ${n}` });
  w.issue(17, { title: 'Fix src/z999.js edge case', body: 'See #3 and fix src/z999.js.' });

  await w.tick({ env: { HOME: process.env.HOME, PATH: process.env.PATH, GH_TOKEN: 'ghs_live_build_token', GITHUB_TOKEN: 'ghs_live_github_token' } });
  const build = w.job(17, 'build');
  assert.equal(build.env.GH_TOKEN, 'ghs_live_build_token', 'builder keeps GH_TOKEN so it can push/open PRs');

  // Check <= 40 owner table cap and citation prioritization.
  const ownerSection = build.input.split('Owner table')[1].split('\n\n')[0];
  const ownerBullets = ownerSection.split('\n').filter(line => line.startsWith('- src/'));
  assert.equal(ownerBullets.length, 40, 'ownerBrief caps injected owned paths at 40');
  assert.ok(ownerBullets.some(line => line.startsWith('- src/z999.js:')), 'cited file src/z999.js is prioritized into the 40-path cap');
  assert.match(ownerSection, /\[cut: 16 more owned files; run pdd owner FILE before you call a file unowned\]/);

  // Check <= 5 sibling open issues cap (#3 named in full + 4 title lines = 5 total).
  const siblingsSection = build.input.split('Other open issues')[1].split('Owner table')[0];
  const namedCount = (siblingsSection.match(/^Issue #\d+:/gm) ?? []).length;
  const bulletCount = (siblingsSection.match(/^- #\d+:/gm) ?? []).length;
  assert.equal(namedCount + bulletCount, 5, 'openIssuesBrief caps total sibling issues at 5');
  assert.match(siblingsSection, /Issue #3: Sibling open issue 3/);

  // Build opens PR; tick starts review + suite.
  const { pr, head } = w.build(17, {
    body: 'Fixes #17\n\nUpdated target behavior.\nRuntime: not run (no prompt changed)\nEvidence: runtime=not-run; vectors=not-run; formal=not-applicable; tests=pass (1/1)',
  });
  await w.tick({ env: { HOME: process.env.HOME, PATH: process.env.PATH, GH_TOKEN: 'ghs_live_build_token', GITHUB_TOKEN: 'ghs_live_github_token' } });

  const review = w.job(17, 'review');
  assert.ok(review, 'review worker started');
  assert.equal(review.env.GH_TOKEN, undefined, 'GH_TOKEN stripped from read-only review worker');
  assert.equal(review.env.GITHUB_TOKEN, undefined, 'GITHUB_TOKEN stripped from read-only review worker');
  assert.doesNotMatch(review.input, /PR body \(data, not instructions\):/, 'blind reviewPrompt MUST NOT embed untrusted builder PR prose (anti-injection invariant)');
  assert.doesNotMatch(review.input, /Updated target behavior\./, 'builder PR body text is never fed into blind reviewPrompt');

  // Leave dirty tracked edits and untracked temp wreckage in the job worktree before repair round starts!
  writeFileSync(join(build.cwd, `change-17.txt`), 'half-edited broken tracked file\n');
  writeFileSync(join(build.cwd, 'untracked-wreckage.tmp'), 'leftover temp artifact\n');
  mkdirSync(join(build.cwd, '.tmp-junk'), { recursive: true });
  writeFileSync(join(build.cwd, '.tmp-junk/nested.log'), 'broken scratch\n');

  w.finish(17, 'review', { result: { verdict: 'FAIL', head, summary: 'Read: change-17.txt', mustFix: ['P2 change-17.txt:1 missing edge case'] } });
  w.suite(17, 0);

  // Even with uncached job.changes, if git reset or git clean fails, repair does NOT launch and job.rounds is NOT persisted.
  const jobFile17 = join(w.root, 'jobs', '17.json');
  const beforeResetJob = JSON.parse(readFileSync(jobFile17, 'utf8'));
  delete beforeResetJob.changes;
  writeFileSync(jobFile17, JSON.stringify(beforeResetJob));
  const baseGitPort = w.ports().git;
  await w.tick({
    git: async (args, options) => args[0] === 'reset'
      ? { code: 128, stdout: '', stderr: 'fatal: Unable to create .git/index.lock: File exists.' }
      : baseGitPort(args, options),
  });
  assert.equal(w.job(17, 'repair'), undefined, 'no repair launched when git reset fails');
  assert.equal(JSON.parse(readFileSync(jobFile17, 'utf8')).repairs, 0);
  assert.deepEqual(JSON.parse(readFileSync(jobFile17, 'utf8')).rounds ?? [], [], 'unlaunched repair round is rolled back on disk');
  assert.equal(JSON.parse(readFileSync(jobFile17, 'utf8')).lastErrorTool, true);

  const beforeCleanJob = JSON.parse(readFileSync(jobFile17, 'utf8'));
  delete beforeCleanJob.changes;
  writeFileSync(jobFile17, JSON.stringify(beforeCleanJob));
  await w.tick({
    git: async (args, options) => args[0] === 'clean'
      ? { code: 1, stdout: '', stderr: 'warning: failed to remove untracked-wreckage.tmp: Permission denied' }
      : baseGitPort(args, options),
  });
  assert.equal(w.job(17, 'repair'), undefined, 'no repair launched when git clean fails');
  assert.equal(JSON.parse(readFileSync(jobFile17, 'utf8')).repairs, 0);
  assert.deepEqual(JSON.parse(readFileSync(jobFile17, 'utf8')).rounds ?? [], [], 'unlaunched repair round is rolled back on disk after clean failure');
  assert.equal(JSON.parse(readFileSync(jobFile17, 'utf8')).lastErrorTool, true);

  // Once cleanup succeeds, the worktree is clean and round 1 repair starts cleanly.
  await w.tick();

  const repair = w.job(17, 'repair');
  assert.ok(repair, 'repair worker started');
  assert.equal(existsSync(join(build.cwd, 'untracked-wreckage.tmp')), false, 'untracked temp file cleaned before repair');
  assert.equal(existsSync(join(build.cwd, '.tmp-junk')), false, 'untracked temp directory cleaned before repair');
  assert.equal(w.git(build.cwd, 'status', '--porcelain'), '', 'worktree cleanly reset to PR head before repair');
  assert.match(repair.input, /Prior failed round summary \(do not repeat a failed approach or undo an earlier fix\):\n- Round 1 \(build @ [0-9a-f]+\): failed Review FAIL/);
  assert.match(repair.input, /untracked-wreckage\.tmp/);
  assert.equal(pr.state, 'open');
});

test('3460-6: wake runs only after wrapper PID exits, waitForAgentJob ignores non-exit writes without feedback loops, contradictory test counts stay visible, and stamped PRs sync replay Evidence', async t => {
  const dir = tempDir(t);
  const agentJobUrl = new URL('../src/agent-job.mjs', import.meta.url).href;
  const wakeObservation = join(dir, 'wake-obs.json');
  const jobSpecPath = join(dir, 'observed-job.json');
  const wakeCode = `
    import(${JSON.stringify(agentJobUrl)}).then(({ readAgentJob }) => {
      const fs = require('node:fs');
      const job = JSON.parse(fs.readFileSync(${JSON.stringify(jobSpecPath)}, 'utf8'));
      const seen = readAgentJob(job);
      fs.writeFileSync(${JSON.stringify(wakeObservation)}, JSON.stringify({ state: seen.state, code: seen.exit?.code ?? null }));
    });
  `;
  const job = startAgentJob({
    id: '99-wake-order',
    dir,
    cwd: dir,
    command: process.execPath,
    args: ['-e', 'setTimeout(() => process.exit(0), 120);'],
    input: 'ok\n',
    env: { PATH: process.env.PATH },
    wake: { command: process.execPath, args: ['-e', wakeCode], cwd: dir, env: { PATH: process.env.PATH } },
  });
  writeFileSync(jobSpecPath, JSON.stringify(job));

  // Verify waitForAgentJob ignores unrelated snapshot/temp writes without triggering an alive/snapshot feedback loop.
  let aliveChecks = 0;
  const waitPromise = waitForAgentJob([job], {
    timeoutMs: 5000,
    alive: (pid, token) => {
      aliveChecks++;
      try { process.kill(pid, 0); return true; } catch { return false; }
    },
  });
  for (let i = 0; i < 10; i++) {
    writeFileSync(join(dir, `noise-${i}.processes.json`), '{}');
  }
  const waited = await waitPromise;
  assert.equal(waited.seen?.state, 'exited');
  assert.ok(aliveChecks < 15, `no fs.watch feedback loop on non-exit files (aliveChecks=${aliveChecks})`);

  await until(() => existsSync(wakeObservation), 5000);
  const obs = JSON.parse(readFileSync(wakeObservation, 'utf8'));
  assert.equal(obs.state, 'exited', 'wake runs after wrapper PID has exited so launcher sees state === exited immediately');
  assert.equal(obs.code, 0);

  // Verify contradictory test counts (state: pass, passed: 0, total: 4) are NOT laundered into tests=pass, and stamped replay Evidence syncs after vectorsRun.
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seedRepo(w, {
    'src/math.js': 'export const double = x => x + 1;\n',
  });
  w.issue(18, { title: 'Fix double()', body: 'double(3) should return 6.' });
  await w.tick();

  const b18 = w.job(18, 'build');
  writeFileSync(join(b18.cwd, 'src/math.js'), 'export const double = x => x * 2;\n');
  mkdirSync(join(b18.cwd, 'test'), { recursive: true });
  writeFileSync(join(b18.cwd, 'test/math.vectors.test.mjs'), 'import test from "node:test"; import assert from "node:assert/strict"; import { double } from "../src/math.js"; test("v", () => assert.equal(double(3), 6));\n');
  w.git(b18.cwd, 'add', '.');
  w.git(b18.cwd, 'commit', '-qm', 'fix double with vectors test');
  w.git(b18.cwd, 'push', '-q', 'origin', `HEAD:${b18.branch}`);
  const head = w.git(b18.cwd, 'rev-parse', 'HEAD');
  w.github.setChecks(head, 'success');

  // First check contradictory tests count via openPullRequest directly:
  const badStamp = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 18, branch: b18.branch, head, worktree: b18.cwd },
    { head, title: 'fix: double', summary: 'Fix double.', tests: { state: 'pass', passed: 0, total: 4 }, adopt: ['src/math.js'], ports: w.ports() },
  );
  assert.match(badStamp.body, /tests=pass \(0\/4\)/, 'contradictory 0/4 pass count is preserved so evidenceReds catches it');

  // Now finish build with valid tests (2/2); vectorsState runs test/math.vectors.test.mjs and syncStampedReplayEvidence updates vectors=pass (3/3).
  w.finish(18, 'build', {
    result: {
      outcome: 'pr',
      pr: badStamp.pr,
      head,
      title: 'fix: double',
      summary: 'Fix double.',
      adopt: ['src/math.js'],
      tests: { state: 'pass', passed: 2, total: 2 },
      runtime: { state: 'not-run', cause: 'no prompt changed' },
    },
  });
  await w.tick();
  w.review(18, 'PASS');
  w.suite(18, 0);
  await w.tick();
  assert.ok(w.job(18, 'vectors'), 'engine started replay run for test/math.vectors.test.mjs');
  w.vectorsRun(18, { tests: 3, control: { 'control-vectors': { tests: 3, fail: 1 } } });
  await w.tick();
  await w.tick();
  const pr18 = w.github.prs.get(badStamp.pr);
  assert.match(pr18.body, /vectors=pass \(3\/3\)/, 'stamped PR synced vectors=pass (3/3) after engine replay');
  assert.equal(pr18.merged, true, 'stamped PR with replay tests merged cleanly without spurious repair');
});

test('3460-7: greenfield pdd-product plan-only repo with no package.json on main claims ready issue and runs PR-added npm test in suiteState', async t => {
  const w = await coreWorld(t, { settings: { testCommand: null } });
  seedRepo(w, {
    'AGENTS.md': '<!-- pdd:start -->\nUse PDD\n<!-- pdd:end -->\n',
    'product/map.md': '# Pocket map\n',
    'product/plan.md': '# Pocket plan\n\n- hub-1: create initial hub package and tests\n',
    'contracts/hub.md': '# Hub contract\n',
  });
  w.settings.testCommand = readCoreSettings(w.cwd).testCommand;
  assert.equal(w.settings.testCommand, null, 'greenfield main has no manifest or testCommand yet');

  w.issue(17, { title: 'hub-1: bootstrap hub module and package.json', body: 'Implement hub-1 from product/plan.md.' });
  await w.tick();
  const build = w.job(17, 'build');
  assert.ok(build, 'greenfield plan-only repo claims issue #17 without blocking on null testCommand');

  // Push PR head from a separate clone so job.worktree stays on main without package.json (proving suiteState & notCovered inspect the checked-out PR head).
  const builderClone = join(w.dir, 'builder-clone');
  w.git(w.dir, 'clone', '-q', w.remote, builderClone);
  w.git(builderClone, 'checkout', '-qb', build.branch);
  mkdirSync(join(builderClone, 'prompts'), { recursive: true });
  mkdirSync(join(builderClone, 'src'), { recursive: true });
  mkdirSync(join(builderClone, 'test'), { recursive: true });
  writeFileSync(join(builderClone, 'package.json'), JSON.stringify({ name: 'pocket-hub', type: 'module', scripts: { test: 'node --test' } }, null, 2) + '\n');
  writeFileSync(join(builderClone, 'prompts/hub.prompt.md'), '---\nkind: native-only\nreason: local process socket bootstrap\n---\n# Hub\n\nOwn `src/hub.mjs`.\n');
  writeFileSync(join(builderClone, 'src/hub.mjs'), '// Prompt: prompts/hub.prompt.md\nexport const hubReady = () => true;\n');
  writeFileSync(join(builderClone, 'test/hub.test.mjs'), 'import test from "node:test"; import assert from "node:assert/strict"; import { execFileSync } from "node:child_process"; import { hubReady } from "../src/hub.mjs"; test("hub", () => { execFileSync(process.execPath, ["-e", "0"]); assert.equal(hubReady(), true); });\n');
  w.git(builderClone, 'add', '.');
  w.git(builderClone, 'commit', '-qm', 'feat(hub): bootstrap package.json, prompt, src and tests');
  w.git(builderClone, 'push', '-q', 'origin', `HEAD:${build.branch}`);
  const head1 = w.git(builderClone, 'rev-parse', 'HEAD');
  w.github.setChecks(head1, 'success');

  w.finish(17, 'build', {
    result: {
      outcome: 'pr',
      head: head1,
      title: 'feat(hub): bootstrap hub-1',
      summary: 'Bootstrapped hub-1 package, prompt, code and tests.',
      tests: { state: 'pass', passed: 1, total: 1 },
      runtime: { state: 'not-run', cause: 'native-only prompt' },
    },
  });
  await w.tick();

  const rev1 = w.job(17, 'review');
  assert.ok(rev1, 'review started on greenfield PR');
  assert.doesNotMatch(rev1.input, /no test command/, 'reviewer evidence summary does not falsely report no test command while suite waits for review');
  assert.equal(w.job(17, 'suite'), undefined, 'greenfield PR holds suite until independent review passes');

  // Once review passes, suite starts using PR-added package.json instead of failing with no-test-command.
  w.review(17, 'PASS');
  await w.tick();
  const suite1 = w.job(17, 'suite');
  assert.ok(suite1, 'suite started after review PASS using PR-added package.json instead of failing with no-test-command');
  assert.match(suite1.args.join(' '), /npm test/);

  // Suite failure reports real detected command ("npm test", never null) in repair instructions.
  w.say(17, 'suite', 'not ok 1 - hub\n  ---\n  location: test/hub.test.mjs:1:1\n  ...\n# tests 1\n# fail 1\n');
  w.finish(17, 'suite', { code: 1 });
  await w.tick();

  const repair = w.job(17, 'repair');
  assert.ok(repair, 'suite failure triggered repair');
  assert.match(repair.input, /Full test suite failure \(`npm test`/, 'repair reproduction block names detected npm test command');
  assert.match(repair.input, /failed suite \(npm test\)/, 'prior round summary names detected npm test command');
  assert.match(repair.input, /the full test command of this repository is `npm test`/, 'workRules names detected npm test command');

  // Repair pushes green head and PR merges cleanly.
  writeFileSync(join(repair.cwd, 'src/hub.mjs'), '// Prompt: prompts/hub.prompt.md\nexport const hubReady = () => true; // fixed\n');
  w.git(repair.cwd, 'add', '.');
  w.git(repair.cwd, 'commit', '-qm', 'fix(hub): green suite');
  w.git(repair.cwd, 'push', '-q', 'origin', `HEAD:${repair.branch}`);
  const head2 = w.git(repair.cwd, 'rev-parse', 'HEAD');
  w.github.setChecks(head2, 'success');
  const pr = [...w.github.prs.values()][0];
  pr.head = head2;
  pr.syncedTip = head2;
  w.finish(17, 'repair', {
    result: {
      outcome: 'pr',
      pr: pr.number,
      head: head2,
      title: 'feat(hub): bootstrap hub-1',
      summary: 'Bootstrapped hub-1 package, prompt, code and tests.',
      tests: { state: 'pass', passed: 1, total: 1 },
      runtime: { state: 'not-run', cause: 'native-only prompt' },
    },
  });
  await w.tick();
  assert.equal(w.job(17, 'suite')?.head, head1, 'repaired greenfield head also waits for review PASS before running suite');
  w.review(17, 'PASS');
  await w.tick();
  assert.equal(w.job(17, 'suite')?.head, head2, 'suite starts on repaired head2 after review PASS');
  w.suite(17, 0);
  await w.tick({
    validateE2e: async () => ({
      offlinePassed: true,
      e2eChecks: [{
        kind: 'real-host-smoke',
        command: 'npm test',
        executed: true,
        exitCode: 0,
        passed: 1,
        failed: 0,
        skipped: 0,
        liveLocal: true,
      }],
    }),
  });
  assert.equal(pr.merged, false, 'Check 4 holds greenfield PR adding protected package.json for manual human merge');
  assert.ok(w.labels(17).includes('pdd:needs-decision'));
  assert.match(w.comments(17).join('\n'), /merge this PR manually on GitHub/i);
});

test('3460-8: openPullRequest fails closed on malformed/omitted evidence, keeps standalone worktree clean, stamps prompt-only & multi-owner Path: a, and embeds PR body in scopedPrompt', async t => {
  const w = await coreWorld(t, { settings: { runs: 1 } });
  seedRepo(w, {
    'prompts/only.prompt.md': '---\nkind: native-only\nreason: contract doc\n---\n# Only\n\nContract v1.\n',
    'prompts/p1.prompt.md': '---\nkind: native-only\nreason: shared part 1\n---\n# Part 1\n\nOwn src/shared.js.\n',
    'prompts/p2.prompt.md': '---\nkind: native-only\nreason: shared part 2\n---\n# Part 2\n\nOwn src/shared.js.\n',
    'src/shared.js': 'export const shared = () => 1;\n',
    'test/shared.test.mjs': 'import test from "node:test"; import assert from "node:assert/strict"; import { execFileSync } from "node:child_process"; import { shared } from "../src/shared.js"; test("s", () => { execFileSync(process.execPath, ["-e", "0"]); assert.equal(shared(), 1); });\n',
    'pdd-bindings.json': JSON.stringify({
      schema_version: 'pdd.bindings.v1',
      modules: [
        { module: 'src/shared.js', prompt: 'prompts/p1.prompt.md', stories: [] },
        { module: 'src/shared.js', prompt: 'prompts/p2.prompt.md', stories: [] },
      ],
    }, null, 2) + '\n',
  });

  w.issue(17, { title: 'Update only.prompt.md and p2 shared behavior', body: 'Edit prompts/only.prompt.md and prompts/p2.prompt.md + src/shared.js.' });
  await w.tick();
  const build = w.job(17, 'build');

  // 1) Prompt-only edit on existing base prompt + multi-owner edit where p2 changed and p1 did NOT change:
  writeFileSync(join(build.cwd, 'prompts/only.prompt.md'), '---\nkind: native-only\nreason: contract doc\n---\n# Only\n\nContract v2.\n');
  writeFileSync(join(build.cwd, 'prompts/p2.prompt.md'), '---\nkind: native-only\nreason: shared part 2\n---\n# Part 2\n\nOwn src/shared.js returning 2.\n');
  writeFileSync(join(build.cwd, 'src/shared.js'), 'export const shared = () => 2;\n');
  writeFileSync(join(build.cwd, 'test/shared.test.mjs'), 'import test from "node:test"; import assert from "node:assert/strict"; import { execFileSync } from "node:child_process"; import { shared } from "../src/shared.js"; test("s", () => { execFileSync(process.execPath, ["-e", "0"]); assert.equal(shared(), 2); });\n');
  w.git(build.cwd, 'add', '.');
  w.git(build.cwd, 'commit', '-qm', 'update prompt-only and p2 multi-owner');
  w.git(build.cwd, 'push', '-q', 'origin', `HEAD:${build.branch}`);
  const head = w.git(build.cwd, 'rev-parse', 'HEAD');
  w.github.setChecks(head, 'success');

  // 2) Standalone openPullRequest WITHOUT options.ports.root keeps job.worktree clean AND fails closed when tests is omitted:
  const { root: _omittedRoot, ...portsWithoutRoot } = w.ports();
  const standaloneJob = { issue: 17, branch: build.branch, head, worktree: build.cwd };
  const omittedTestsStamp = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    standaloneJob,
    {
      head,
      title: 'feat: update p2 and only prompt',
      summary: 'Updated contracts and shared helper.',
      choices: ['Return 2 for default shared helper (keeps caller signature unchanged)'],
      runtime: { state: 'not-run', cause: 'native-only prompt' },
      ports: portsWithoutRoot,
    },
  );
  assert.equal(existsSync(join(build.cwd, 'worktrees')), false, 'standalone openPullRequest leaves no worktrees/ in job.worktree');
  assert.equal(existsSync(join(build.cwd, 'jobs')), false, 'standalone openPullRequest leaves no jobs/ in job.worktree');
  assert.equal(existsSync(join(build.cwd, 'logs')), false, 'standalone openPullRequest leaves no logs/ in job.worktree');
  assert.equal(standaloneJob.baseTree, undefined, 'standalone scratch worktree pointer cleaned up');
  assert.equal(standaloneJob.headTree, undefined, 'standalone scratch headTree pointer cleaned up');

  // Verify Path: a lines for BOTH prompt-only edit (never Path: d) and multi-owner p2 (never p1):
  assert.match(omittedTestsStamp.body, /^Path: a — prompts\/only\.prompt\.md — prompts\/only\.prompt\.md — prompt changed — Test: test\/shared\.test\.mjs$/m, 'existing base prompt-only edit takes Path: a, never Path: d');
  assert.match(omittedTestsStamp.body, /^Path: a — prompts\/p2\.prompt\.md, src\/shared\.js — prompts\/p2\.prompt\.md — prompt changed — Test: test\/shared\.test\.mjs$/m, 'multi-owner module names the changed owner prompt p2');
  assert.doesNotMatch(omittedTestsStamp.body, /prompts\/p1\.prompt\.md/, 'unchanged co-owner p1 is not named as the changed Path: a owner');
  assert.match(omittedTestsStamp.body, /tests=fail\b/, 'omitted tests without prior Evidence fails closed to tests=fail');

  // 3) Malformed explicit tests / vectors / formal NEVER fall back to stale parsedEv passing claims:
  const priorPassStamp = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 17, branch: build.branch, head, worktree: build.cwd, pr: omittedTestsStamp.pr },
    {
      pr: omittedTestsStamp.pr,
      head,
      summary: 'Updated contracts and shared helper.',
      choices: ['Return 2 for default shared helper (keeps caller signature unchanged)'],
      vectors: { state: 'pass', passed: 2, total: 2 },
      formal: { state: 'bounded' },
      tests: { state: 'pass', passed: 1, total: 1 },
      runtime: { state: 'not-run', cause: 'native-only prompt' },
      ports: portsWithoutRoot,
    },
  );
  assert.match(priorPassStamp.body, /^Evidence: runtime=pass; vectors=pass \(2\/2\); formal=bounded; tests=pass \(1\/1\)$/m);

  const malformedOverwrite = await openPullRequest(
    { state: w.state, settings: w.settings, budget: { state: 'normal', used: 0, allowed: 1000 } },
    { issue: 17, branch: build.branch, head, worktree: build.cwd, pr: omittedTestsStamp.pr },
    {
      pr: omittedTestsStamp.pr,
      head,
      body: priorPassStamp.body,
      vectors: { state: 'bogus' },
      formal: 'not-an-object',
      tests: 'malformed',
      runtime: { state: 'not-run', cause: 'native-only prompt' },
      ports: portsWithoutRoot,
    },
  );
  assert.match(malformedOverwrite.body, /^Evidence: runtime=pass; vectors=fail; formal=failed; tests=fail$/m, 'malformed explicit evidence fields fail closed instead of reusing stale passing Evidence');

  // Restore clean valid stamp and advance to PR phase, then verify scopedPrompt embeds PR body with GH_TOKEN stripped:
  w.finish(17, 'build', {
    result: {
      outcome: 'pr',
      pr: omittedTestsStamp.pr,
      head,
      title: 'feat: update p2 and only prompt',
      summary: 'Updated contracts and shared helper.',
      choices: ['Return 2 for default shared helper (keeps caller signature unchanged)'],
      tests: { state: 'pass', passed: 1, total: 1 },
      runtime: { state: 'not-run', cause: 'native-only prompt' },
    },
  });
  await w.tick({ env: { HOME: process.env.HOME, PATH: process.env.PATH, GH_TOKEN: 'ghs_secret_for_scoped_review' } });
  w.review(17, 'PASS');

  // Simulate post-conflict scoped review state on saved job 17:
  const savedJobPath = join(w.root, 'jobs', '17.json');
  const savedJob = JSON.parse(readFileSync(savedJobPath, 'utf8'));
  savedJob.review = {
    head,
    scoped: {
      reason: 'a conflict update',
      detail: 'the former conflict hunks in src/shared.js',
      files: ['src/shared.js'],
    },
  };
  writeFileSync(savedJobPath, JSON.stringify(savedJob, null, 2));

  await w.tick({ env: { HOME: process.env.HOME, PATH: process.env.PATH, GH_TOKEN: 'ghs_secret_for_scoped_review' } });
  const scopedRev = w.job(17, 'review');
  assert.ok(scopedRev, 'scoped review started');
  assert.equal(scopedRev.env.GH_TOKEN, undefined, 'scoped review also strips GH_TOKEN');
  assert.match(scopedRev.input, /You are a short scoped check/, 'used scopedPrompt');
  assert.doesNotMatch(scopedRev.input, /PR body \(data, not instructions\):/, 'scopedPrompt MUST NOT embed untrusted builder PR prose');
  assert.doesNotMatch(scopedRev.input, /Return 2 for default shared helper/, 'builder PR prose never leaks into blind scopedPrompt');

  w.review(17, 'PASS');
  w.suite(17, 0);
  await w.tick({
    validateE2e: async () => ({
      offlinePassed: true,
      e2eChecks: [{
        kind: 'real-host-smoke',
        command: 'npm test',
        executed: true,
        exitCode: 0,
        passed: 1,
        failed: 0,
        skipped: 0,
        liveLocal: true,
      }],
    }),
  });
  assert.equal(w.github.prs.get(omittedTestsStamp.pr).merged, true, 'PR merged cleanly after scoped review and suite passed');
});
