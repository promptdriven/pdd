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
  assert.ok(commands.some(cmd => cmd[0] === 'npm' && cmd.includes('github:promptdriven/pdd#alpha-v0.1.32')));
  assert.match(autoUpdateStatusLine({ stateRoot }), /updated pdd 0\.1\.30 -> 0\.1\.32/);

  // 3. Subsequent tick 10 minutes later is throttled.
  now += 10 * 60 * 1000;
  const throttled = await runUpdate();
  assert.equal(throttled.action, 'throttled');
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
