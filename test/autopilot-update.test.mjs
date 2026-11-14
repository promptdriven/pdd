import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  autoUpdateStatusLine,
  detectGlobalInstallPrefix,
  hasMidWriteJobs,
  maybeAutoUpdateAutopilot,
} from '../src/autopilot-update.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';

const packageRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..');

test('#2710 detectGlobalInstallPrefix accepts user-owned @promptdriven/pdd or pdd global prefixes and rejects git checkouts or foreign UIDs', t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-autoupdate-prefix-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const uid = process.getuid();

  const scopedPkg = join(root, 'nvm/lib/node_modules/@promptdriven/pdd');
  mkdirSync(scopedPkg, { recursive: true });
  writeFileSync(join(scopedPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.31' }));
  const detected = detectGlobalInstallPrefix(scopedPkg, { uid });
  assert.ok(detected);
  assert.ok(detected.prefix.endsWith('/nvm'));

  // Foreign UID (e.g. root-owned /usr/local) is rejected.
  assert.equal(detectGlobalInstallPrefix(scopedPkg, { uid: uid + 1 }), null);

  // Source checkout with .git is rejected even inside node_modules.
  mkdirSync(join(scopedPkg, '.git'));
  assert.equal(detectGlobalInstallPrefix(scopedPkg, { uid }), null);
});

test('#2710 maybeAutoUpdateAutopilot defers on mid-write jobs, updates global install + skills when idle, and throttles for 1h', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-autoupdate-run-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  const prefix = join(root, 'global');
  const globalPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  const coreRoot = join(root, 'state-core');
  const stateRoot = join(root, 'state');
  const repoDir = join(root, 'repo');
  mkdirSync(globalPkg, { recursive: true });
  mkdirSync(join(coreRoot, 'jobs'), { recursive: true });
  mkdirSync(stateRoot, { recursive: true });
  mkdirSync(repoDir, { recursive: true });
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.30' }));

  // 1. Mid-write job (phase: 'ending') defers without consuming the 1h throttle.
  writeFileSync(join(coreRoot, 'jobs/42.json'), JSON.stringify({ issue: 42, phase: 'ending' }));
  assert.equal(hasMidWriteJobs(coreRoot), true);
  let commands = [];
  let skillsRefreshed = 0;
  let now = 1_700_000_000_000;
  const runUpdate = () => maybeAutoUpdateAutopilot({
    state: { cwd: repoDir, baseBranch: 'main', autoUpdate: 'release' },
    packageRoot: globalPkg,
    coreRoot,
    stateRoot,
    env: { HOME: root },
  }, {
    now: () => now,
    uid: process.getuid(),
    fetchLatestRelease: async () => ({ tag_name: 'alpha-v0.1.32', draft: false }),
    claimUpdateLock: async () => () => {},
    setupSkills: () => { skillsRefreshed++; return []; },
    execute: async (file, args) => {
      commands.push([file, ...args]);
      if (file === 'git' && args[0] === 'rev-parse') return { code: 0, stdout: 'main\n', stderr: '' };
      if (file === 'git' && args[0] === 'status') return { code: 0, stdout: '', stderr: '' };
      if (file === 'git' && args[0] === 'pull') return { code: 0, stdout: 'Already up to date.\n', stderr: '' };
      if (file === 'npm') {
        writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.32' }));
        return { code: 0, stdout: 'updated\n', stderr: '' };
      }
      return { code: 0, stdout: '', stderr: '' };
    },
  });

  const deferred = await runUpdate();
  assert.equal(deferred.action, 'deferred');
  assert.equal(commands.length, 0);

  // 2. Job finishes ending -> update runs immediately, fast-forwards clean baseBranch, installs tag, refreshes skills, and writes status.
  writeFileSync(join(coreRoot, 'jobs/42.json'), JSON.stringify({ issue: 42, phase: 'done' }));
  const updated = await runUpdate();
  assert.deepEqual(updated, { action: 'updated', fromVersion: '0.1.30', toVersion: '0.1.32' });
  assert.equal(skillsRefreshed, 1);
  assert.ok(commands.some(cmd => cmd[0] === 'git' && cmd[1] === 'pull' && cmd[3] === 'origin' && cmd[4] === 'main'));
  assert.ok(commands.some(cmd => cmd[0] === 'npm' && cmd.includes('--ignore-scripts') && cmd.includes('github:promptdriven/pdd#alpha-v0.1.32')));
  assert.match(autoUpdateStatusLine({ stateRoot }), /updated pdd 0\.1\.30 -> 0\.1\.32/);

  // 3. Subsequent tick 10 minutes later is throttled.
  now += 10 * 60 * 1000;
  const throttled = await runUpdate();
  assert.equal(throttled.action, 'throttled');
});

test('#2710 maybeAutoUpdateAutopilot fails closed on gh api errors, supports prerelease-only arrays, pins main SHA with --ignore-scripts, and defers across sibling repo jobs', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-autoupdate-safety-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  const prefix = join(root, 'global');
  const globalPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  const stateRoot = join(root, 'state');
  const coreRoot = join(stateRoot, 'repoA-core');
  const siblingCore = join(stateRoot, 'repoB-core');
  mkdirSync(globalPkg, { recursive: true });
  mkdirSync(join(coreRoot, 'jobs'), { recursive: true });
  mkdirSync(join(siblingCore, 'jobs'), { recursive: true });
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.31' }));
  writeFileSync(join(stateRoot, 'repoB.json'), JSON.stringify({ enabled: true }));

  // 1. Active Runtime check child in a sibling repository under stateRoot defers self-update.
  writeFileSync(join(siblingCore, 'jobs/99.json'), JSON.stringify({ issue: 99, phase: 'pr', runtimeWait: { state: 'sent' } }));
  assert.equal(hasMidWriteJobs({ coreRoot, stateRoot }), true);
  let now = 1_700_000_000_000;
  const deferredSibling = await maybeAutoUpdateAutopilot({
    state: { autoUpdate: 'release' },
    packageRoot: globalPkg,
    coreRoot,
    stateRoot,
    env: { HOME: root },
  }, {
    now: () => now,
    uid: process.getuid(),
    execute: async () => ({ code: 0, stdout: '[]', stderr: '' }),
  });
  assert.equal(deferredSibling.action, 'deferred');

  // Clear sibling runtimeWait -> no longer mid-write.
  writeFileSync(join(siblingCore, 'jobs/99.json'), JSON.stringify({ issue: 99, phase: 'pr', runtimeWait: { state: 'done' } }));
  assert.equal(hasMidWriteJobs({ coreRoot, stateRoot }), false);

  // 2. Non-zero gh api exit status records failed + lastError (never up-to-date).
  const ghFailed = await maybeAutoUpdateAutopilot({
    state: { autoUpdate: 'release' },
    packageRoot: globalPkg,
    coreRoot,
    stateRoot,
    env: { HOME: root },
  }, {
    now: () => now,
    uid: process.getuid(),
    execute: async (file) => {
      if (file === 'gh') return { code: 1, stdout: '', stderr: 'HTTP 401 Bad credentials\n' };
      return { code: 0, stdout: '', stderr: '' };
    },
  });
  assert.equal(ghFailed.action, 'failed');
  assert.match(autoUpdateStatusLine({ stateRoot }), /last try failed \(HTTP 401 Bad credentials\)/);

  // 3. After 1h backoff, prerelease-only releases?per_page=10 list picks newest non-draft alpha-v tag.
  now += 61 * 60 * 1000;
  const releaseCmds = [];
  const preUpdated = await maybeAutoUpdateAutopilot({
    state: { autoUpdate: 'release' },
    packageRoot: globalPkg,
    coreRoot,
    stateRoot,
    env: { HOME: root },
  }, {
    now: () => now,
    uid: process.getuid(),
    setupSkills: () => [],
    execute: async (file, args) => {
      releaseCmds.push([file, ...args]);
      if (file === 'gh') {
        return {
          code: 0,
          stdout: JSON.stringify([
            { tag_name: 'alpha-v0.1.99', draft: true, prerelease: true, published_at: '2026-11-13T12:00:00Z' },
            { tag_name: 'alpha-v0.1.33', draft: false, prerelease: true, published_at: '2026-11-13T11:00:00Z' },
          ]),
          stderr: '',
        };
      }
      if (file === 'npm') {
        writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.33' }));
        return { code: 0, stdout: 'ok\n', stderr: '' };
      }
      return { code: 0, stdout: '', stderr: '' };
    },
  });
  assert.deepEqual(preUpdated, { action: 'updated', fromVersion: '0.1.31', toVersion: '0.1.33' });
  assert.ok(releaseCmds.some(c => c[0] === 'gh' && c[2] === 'repos/promptdriven/pdd/releases?per_page=10'));
  assert.ok(releaseCmds.some(c => c[0] === 'npm' && c.includes('--ignore-scripts') && c.includes('github:promptdriven/pdd#alpha-v0.1.33')));

  // 4. In main mode, installs pinned commit SHA (not mutable #main) with --ignore-scripts.
  now += 61 * 60 * 1000;
  const pinnedSha = 'a1b2c3d4e5f60718293a4b5c6d7e8f9012345678';
  const mainCmds = [];
  const mainUpdated = await maybeAutoUpdateAutopilot({
    state: { autoUpdate: 'main' },
    packageRoot: globalPkg,
    coreRoot,
    stateRoot,
    env: { HOME: root },
  }, {
    now: () => now,
    uid: process.getuid(),
    setupSkills: () => [],
    execute: async (file, args) => {
      mainCmds.push([file, ...args]);
      if (file === 'gh') return { code: 0, stdout: JSON.stringify({ sha: pinnedSha }), stderr: '' };
      if (file === 'npm') return { code: 0, stdout: 'ok\n', stderr: '' };
      return { code: 0, stdout: '', stderr: '' };
    },
  });
  assert.equal(mainUpdated.action, 'updated');
  assert.ok(mainCmds.some(c => c[0] === 'npm' && c.includes('--ignore-scripts') && c.includes(`github:promptdriven/pdd#${pinnedSha}`)));
  assert.ok(!mainCmds.some(c => c.includes('github:promptdriven/pdd#main')));
});

test('#2710 runAutopilotLauncher validates --auto-update values before effects', async () => {
  const bad = await runAutopilotLauncher({
    command: 'start',
    cwd: packageRoot,
    packageRoot,
    env: { HOME: tmpdir() },
    autoUpdate: 'invalid',
  });
  assert.equal(bad.exitCode, 2);
  assert.match(bad.message, /--auto-update release, --auto-update main or --auto-update off/);
});
