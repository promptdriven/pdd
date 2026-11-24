import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as nativeFs from 'node:fs';
import { cpSync, existsSync, lstatSync, mkdtempSync, mkdirSync, readdirSync, readFileSync, readlinkSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import * as autopilotUpdateMod from '../src/autopilot-update.mjs';
import {
  autoUpdateStatusLine,
  detectGlobalInstallPrefix,
  hasLegacyUnscopedPdd,
  hasMidWriteJobs,
  maybeAutoUpdateAutopilot,
} from '../src/autopilot-update.mjs';
import { runCliUpgrade } from '../src/setup/cli-upgrade.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { PDD_SKILL_NAMES } from '../src/skills-install.mjs';

const packageRoot = resolve(dirname(fileURLToPath(import.meta.url)), '..');

test('#3645 src/autopilot-update.mjs no longer exports duplicate runCliUpgrade (single source of truth in src/setup/cli-upgrade.mjs)', () => {
  assert.equal('runCliUpgrade' in autopilotUpdateMod, false);
  assert.equal('resolveReleaseUpgradeTarget' in autopilotUpdateMod, false);
  assert.equal('resolveMainCommitTarget' in autopilotUpdateMod, false);
});

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

test('#2710/#3645 maybeAutoUpdateAutopilot defers on mid-write jobs, prefers npm with github fallback, delegates post-upgrade sync to newly installed binary, and throttles for 1h', async t => {
  const root = mkdtempSync(join(tmpdir(), 'pdd-autoupdate-run-'));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  const prefix = join(root, 'global');
  const globalPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  const coreRoot = join(root, 'state-core');
  const stateRoot = join(root, 'state');
  const repoDir = join(root, 'repo');
  mkdirSync(join(globalPkg, 'bin'), { recursive: true });
  mkdirSync(join(coreRoot, 'jobs'), { recursive: true });
  mkdirSync(stateRoot, { recursive: true });
  mkdirSync(repoDir, { recursive: true });
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.30', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(globalPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n');

  // 1. Mid-write job (phase: 'ending') defers without consuming the 1h throttle.
  writeFileSync(join(coreRoot, 'jobs/42.json'), JSON.stringify({ issue: 42, phase: 'ending' }));
  assert.equal(hasMidWriteJobs(coreRoot), true);
  let commands = [];
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
    execute: async (file, args) => {
      commands.push([file, ...args]);
      if (file === 'git' && args[0] === 'rev-parse') return { code: 0, stdout: 'main\n', stderr: '' };
      if (file === 'git' && args[0] === 'status') return { code: 0, stdout: '', stderr: '' };
      if (file === 'git' && args[0] === 'pull') return { code: 0, stdout: 'Already up to date.\n', stderr: '' };
      if (file === 'npm') {
        writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.32', bin: { pdd: 'bin/pdd.mjs' } }));
        return { code: 0, stdout: 'updated\n', stderr: '' };
      }
      return { code: 0, stdout: '', stderr: '' };
    },
  });

  const deferred = await runUpdate();
  assert.equal(deferred.action, 'deferred');
  assert.equal(commands.length, 0);

  // 2. Job finishes ending -> installs npm @promptdriven/pdd@0.1.32 first, then delegates to newly installed binary's `setup --upgrade`!
  writeFileSync(join(coreRoot, 'jobs/42.json'), JSON.stringify({ issue: 42, phase: 'done' }));
  const updated = await runUpdate();
  assert.deepEqual(updated, { action: 'updated', fromVersion: '0.1.30', toVersion: '0.1.32' });
  assert.ok(commands.some(cmd => cmd[0] === 'git' && cmd[1] === 'pull' && cmd[3] === 'origin' && cmd[4] === 'main'));
  assert.ok(commands.some(cmd => cmd[0] === 'npm' && cmd.includes('--ignore-scripts') && cmd.includes('@promptdriven/pdd@0.1.32')));
  assert.ok(commands.some(cmd => cmd[0] === process.execPath && cmd[1] === join(realpathSync(globalPkg), 'bin/pdd.mjs') && cmd[2] === 'setup' && cmd[3] === '--upgrade'), JSON.stringify(commands));
  assert.match(autoUpdateStatusLine({ stateRoot }), /updated pdd 0\.1\.30 -> 0\.1\.32/);

  // 3. Subsequent tick 10 minutes later is throttled.
  now += 10 * 60 * 1000;
  const throttled = await runUpdate();
  assert.equal(throttled.action, 'throttled');
});

test('#2710/#3645 maybeAutoUpdateAutopilot fails closed on gh api errors, falls back from npm to github tag, pins main SHA, and defers across sibling repo jobs', async t => {
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

  // 3. After 1h backoff, tries npm @promptdriven/pdd@0.1.33 first and falls back to github:promptdriven/pdd#alpha-v0.1.33 on E404.
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
        if (args.includes('@promptdriven/pdd@0.1.33')) return { code: 1, stdout: '', stderr: 'npm error code E404\n' };
        writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.33' }));
        return { code: 0, stdout: 'ok\n', stderr: '' };
      }
      return { code: 0, stdout: '', stderr: '' };
    },
  });
  assert.deepEqual(preUpdated, { action: 'updated', fromVersion: '0.1.31', toVersion: '0.1.33' });
  assert.ok(releaseCmds.some(c => c[0] === 'gh' && c[2] === 'repos/promptdriven/pdd/releases?per_page=10'));
  assert.ok(releaseCmds.some(c => c[0] === 'npm' && c.includes('--ignore-scripts') && c.includes('@promptdriven/pdd@0.1.33')));
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

const captureStream = () => ({ text: '', write(s) { this.text += s; } });

test('#3424/#3645 pdd upgrade updates global CLI via npm-first, spawns newly installed binary setup --upgrade, clears release-check.json, handles repeated upgrades, and pins --main SHA', async t => {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cli-upgrade-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const prefix = join(sandbox, 'global');
  const globalPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  const home = join(sandbox, 'home');
  const repoDir = join(sandbox, 'repo');
  mkdirSync(globalPkg, { recursive: true });
  mkdirSync(home, { recursive: true });
  mkdirSync(repoDir, { recursive: true });
  for (const part of ['bin', 'src', 'skills']) cpSync(join(packageRoot, part), join(globalPkg, part), { recursive: true });
  symlinkSync(join(packageRoot, 'node_modules'), join(globalPkg, 'node_modules'), 'dir');
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.12', bin: { pdd: 'bin/pdd.mjs' } }));

  const targetVersion = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
  const releaseCache = join(home, '.local/state/pdd/release-check.json');
  mkdirSync(dirname(releaseCache), { recursive: true });
  writeFileSync(releaseCache, JSON.stringify({ checkedAt: Date.now(), latestTag: `alpha-v${targetVersion}`, latestVersion: targetVersion }));

  // Seed older .pdd-skill.json-marked folders in .agents/skills, .codex/skills and .claude/skills + retired skills + custom skills.
  const marker = '.pdd-skill.json';
  for (const rel of ['.agents/skills', '.codex/skills', '.claude/skills']) {
    const folder = join(home, rel);
    for (const name of PDD_SKILL_NAMES) {
      cpSync(join(packageRoot, 'skills', name), join(folder, name), { recursive: true });
      writeFileSync(join(folder, name, marker), JSON.stringify({ package: 'pdd', version: '0.1.12', digest: 'old' }));
    }
  }
  for (const retiredName of ['pdd-check', 'pdd-feature']) {
    mkdirSync(join(home, '.agents/skills', retiredName), { recursive: true });
    writeFileSync(join(home, '.agents/skills', retiredName, 'SKILL.md'), 'old retired\n');
    writeFileSync(join(home, '.agents/skills', retiredName, marker), JSON.stringify({ package: 'pdd', version: '0.1.12', digest: 'old' }));
  }
  mkdirSync(join(home, '.agents/skills/pdd-autopilot'), { recursive: true });
  writeFileSync(join(home, '.agents/skills/pdd-autopilot/SKILL.md'), 'user custom autopilot\n');
  mkdirSync(join(home, '.codex/skills/finish-pr'), { recursive: true });
  writeFileSync(join(home, '.codex/skills/finish-pr/SKILL.md'), 'user custom finish-pr\n');

  const { spawnSync: realSpawnSync } = await import('node:child_process');
  const spawned = [];
  const spawnSyncImpl = (file, args, opts) => {
    spawned.push([file, ...args]);
    if (file === 'npm') {
      writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: targetVersion, bin: { pdd: 'bin/pdd.mjs' } }));
      return { status: 0, stdout: 'updated\n', stderr: '' };
    }
    // Delegate real `node <globalPkg>/bin/pdd.mjs setup --upgrade` to the actual installed binary!
    return realSpawnSync(file, args, opts);
  };
  const fetchImpl = async url => ({
    ok: true,
    json: async () => url.includes('/commits/main')
      ? { sha: '0123456789abcdef0123456789abcdef01234567' }
      : [{ tag_name: `alpha-v${targetVersion}`, draft: false, prerelease: true, published_at: '2026-11-15T12:00:00Z' }],
  });

  // 1. Run `pdd upgrade` via CLI dispatcher.
  const out1 = captureStream(), err1 = captureStream();
  const code1 = await runPdd(['upgrade'], {
    cwd: repoDir,
    packageRoot: globalPkg,
    env: { HOME: home, PATH: '' },
    stdout: out1,
    stderr: err1,
    cliUpgradePorts: { uid: process.getuid() },
    cliUpgrade: {
      runCliUpgrade: (opts, ports) => runCliUpgrade({ ...opts, spawnSyncImpl, fetchImpl }, ports),
    },
  });
  assert.equal(code1, 0, err1.text);
  assert.equal(err1.text, '');
  assert.ok(out1.text.includes(`Upgraded pdd 0.1.12 -> ${targetVersion} (alpha-v${targetVersion}).`), out1.text);
  assert.match(out1.text, /Updated 1 PDD skill in .*\.agents\/skills: pdd/);
  assert.match(out1.text, /Removed retired PDD skills from .*\.agents\/skills: pdd-check, pdd-feature/);
  assert.equal(existsSync(releaseCache), false);
  assert.ok(spawned.some(cmd => cmd[0] === 'npm' && cmd.includes('--ignore-scripts') && cmd.includes(`@promptdriven/pdd@${targetVersion}`)));
  assert.ok(spawned.some(cmd => cmd[0] === process.execPath && cmd[1] === join(globalPkg, 'bin/pdd.mjs') && cmd[2] === 'setup' && cmd[3] === '--upgrade'));

  for (const rel of ['.agents/skills', '.codex/skills', '.claude/skills']) {
    for (const name of PDD_SKILL_NAMES) {
      assert.equal(JSON.parse(readFileSync(join(home, rel, name, marker), 'utf8')).version, targetVersion, `${rel}/${name}`);
    }
  }
  assert.equal(existsSync(join(home, '.agents/skills/pdd-check')), false);
  assert.equal(existsSync(join(home, '.agents/skills/pdd-feature')), false);
  assert.equal(readFileSync(join(home, '.agents/skills/pdd-autopilot/SKILL.md'), 'utf8'), 'user custom autopilot\n');
  assert.equal(readFileSync(join(home, '.codex/skills/finish-pr/SKILL.md'), 'utf8'), 'user custom finish-pr\n');

  // 2. Repeated upgrade skips npm and delegates cleanly to `setup --upgrade` (already current).
  spawned.length = 0;
  const out2 = captureStream(), err2 = captureStream();
  const res2 = await runCliUpgrade({
    env: { HOME: home, PATH: '' },
    stdout: out2,
    stderr: err2,
    spawnSyncImpl,
    fetchImpl,
    packageRoot: globalPkg,
    home,
    cwd: repoDir,
  }, { uid: process.getuid() });
  assert.equal(res2.exitCode, 0, err2.text);
  assert.equal(res2.cliUpdated, false);
  assert.deepEqual(res2.updatedSkills, []);
  assert.equal(spawned.some(cmd => cmd[0] === 'npm'), false, 'must not spawn npm when already up to date');
  assert.equal(out2.text, `pdd ${targetVersion} is already up to date. PDD skills are current.\n`);

  // 2b. When project-local retired skills remain in cwd, `pdd upgrade` must NOT falsely say "PDD skills are current."!
  mkdirSync(join(repoDir, '.agents/skills/pdd-bug'), { recursive: true });
  writeFileSync(join(repoDir, '.agents/skills/pdd-bug/SKILL.md'), '---\nname: pdd-bug\nmetadata:\n  pdd-skills: 0.1.39\n---\n');
  const outProj = captureStream(), errProj = captureStream();
  const resProj = await runCliUpgrade({
    env: { HOME: home, PATH: '' },
    stdout: outProj,
    stderr: errProj,
    spawnSyncImpl,
    fetchImpl,
    packageRoot: globalPkg,
    home,
    cwd: repoDir,
  }, { uid: process.getuid() });
  assert.equal(resProj.exitCode, 0, errProj.text);
  assert.equal(outProj.text.includes('PDD skills are current.'), false, outProj.text);
  assert.match(outProj.text, /Retired PDD skills remain in .*repo\/\.agents\/skills/);
  rmSync(join(repoDir, '.agents'), { recursive: true, force: true });

  // 3. `pdd upgrade --main` pins exact 40-char commit SHA with --ignore-scripts (never mutable #main).
  const outMain = captureStream(), errMain = captureStream();
  const resMain = await runCliUpgrade({
    env: { HOME: home, PATH: '' },
    stdout: outMain,
    stderr: errMain,
    main: true,
    spawnSyncImpl,
    fetchImpl,
    packageRoot: globalPkg,
    home,
    cwd: repoDir,
  }, { uid: process.getuid() });
  assert.equal(resMain.exitCode, 0, errMain.text);
  assert.ok(spawned.some(cmd => cmd[0] === 'npm' && cmd.includes('--ignore-scripts') && cmd.includes('github:promptdriven/pdd#0123456789abcdef0123456789abcdef01234567')));
  assert.ok(!spawned.some(cmd => cmd.includes('github:promptdriven/pdd#main')));
});

test('#3424/#3645 pdd upgrade passes env to skillsInstall port, handles exit-2 older binary fallback, reports failures, and refuses git checkout', async t => {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cli-upgrade-cases-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const targetVersion = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
  const prefix = join(sandbox, 'global');
  const globalPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(globalPkg, 'bin'), { recursive: true });
  cpSync(join(packageRoot, 'skills'), join(globalPkg, 'skills'), { recursive: true });
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: targetVersion, bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(globalPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n');

  const fetchImpl = async () => ({
    ok: true,
    json: async () => [{ tag_name: `alpha-v${targetVersion}`, draft: false, prerelease: true, published_at: '2026-11-15T12:00:00Z' }],
  });

  // Case A: Injected ports.skillsInstall receives env cleanly and surfaces failed folder with exit 1.
  const homeA = join(sandbox, 'home-a');
  mkdirSync(homeA, { recursive: true });
  let receivedEnv = null;
  const outFail = captureStream(), errFail = captureStream();
  const testEnv = { HOME: homeA, XDG_STATE_HOME: join(sandbox, 'xdg-state') };
  const resFail = await runCliUpgrade({
    env: testEnv,
    stdout: outFail,
    stderr: errFail,
    fetchImpl,
    spawnSyncImpl: () => ({ status: 0, stdout: '', stderr: '' }),
    packageRoot: globalPkg,
    home: homeA,
    cwd: join(sandbox, 'empty-cwd'),
  }, {
    uid: process.getuid(),
    skillsInstall: {
      syncOwnedUserSkills: ({ env, onError }) => {
        receivedEnv = env;
        onError(join(homeA, '.codex/skills'), Object.assign(Error('permission denied'), { code: 'EACCES' }));
        return { updated: [] };
      },
      findSkills: () => [],
    },
  });
  assert.equal(resFail.exitCode, 1);
  assert.equal(receivedEnv, testEnv, 'syncOwnedUserSkills must receive env');
  assert.match(errFail.text, /Failed to update PDD skills in .*\.codex\/skills \(EACCES\)\. To recover, run: pdd setup/);

  // Case B: Older target binary returning exit 2 for unknown `--upgrade` falls back cleanly to local skills sync.
  const homeB = join(sandbox, 'home-b');
  cpSync(join(packageRoot, 'skills/pdd'), join(homeB, '.agents/skills/pdd'), { recursive: true });
  writeFileSync(join(homeB, '.agents/skills/pdd/.pdd-skill.json'), JSON.stringify({ package: 'pdd', version: '0.1.12', digest: 'old' }));
  const outB = captureStream(), errB = captureStream();
  const resB = await runCliUpgrade({
    env: { HOME: homeB, PDD_STATE_DIR: join(sandbox, 'state-b') },
    stdout: outB,
    stderr: errB,
    fetchImpl,
    spawnSyncImpl: (file, args) => {
      if (args.includes('--upgrade')) return { status: 2, stdout: '', stderr: 'Unknown option "--upgrade". Run pdd setup --help.\n' };
      return { status: 0, stdout: '', stderr: '' };
    },
    packageRoot: globalPkg,
    home: homeB,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });
  assert.equal(resB.exitCode, 0, errB.text);
  assert.equal(JSON.parse(readFileSync(join(homeB, '.agents/skills/pdd/.pdd-skill.json'), 'utf8')).version, targetVersion);

  // Case C: Git checkout / non-global packageRoot refuses cleanly with 4-part remediation.
  const outCheckout = captureStream(), errCheckout = captureStream();
  const resCheckout = await runCliUpgrade({
    env: { HOME: homeA },
    stdout: outCheckout,
    stderr: errCheckout,
    packageRoot,
    home: homeA,
  });
  assert.equal(resCheckout.exitCode, 1);
  assert.match(errCheckout.text, /git pull && npm install/);
});

test('#3474 hasLegacyUnscopedPdd guards and Autopilot self-update unscoped migration with safe backup rollback', async t => {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-legacy-unscoped-3474-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const targetVersion = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;

  // 0. Guard checks on hasLegacyUnscopedPdd: rejects unrelated 'pdd' packages, symlinks, .git checkouts, foreign UIDs, and dangling bin/pdd links.
  const guardRoot = join(sandbox, 'guards');
  const foreignPkgPrefix = join(guardRoot, 'unrelated-pdd');
  mkdirSync(join(foreignPkgPrefix, 'lib/node_modules/pdd'), { recursive: true });
  writeFileSync(join(foreignPkgPrefix, 'lib/node_modules/pdd/package.json'), JSON.stringify({ name: 'pdd', version: '2.0.0', bin: { pdd: 'cli.js' } }));
  assert.equal(hasLegacyUnscopedPdd(foreignPkgPrefix), false, 'unrelated npm package named pdd without bin/pdd.mjs must not match');

  const danglingPrefix = join(guardRoot, 'dangling-link');
  mkdirSync(join(danglingPrefix, 'bin'), { recursive: true });
  symlinkSync('../lib/node_modules/pdd/bin/pdd.mjs', join(danglingPrefix, 'bin/pdd'));
  assert.equal(hasLegacyUnscopedPdd(danglingPrefix), false, 'standalone/dangling bin/pdd symlink without node_modules/pdd must not match');

  const symlinkPkgTarget = join(guardRoot, 'real-target');
  mkdirSync(join(symlinkPkgTarget, 'bin'), { recursive: true });
  writeFileSync(join(symlinkPkgTarget, 'package.json'), JSON.stringify({ name: 'pdd', version: '0.1.31', bin: 'bin/pdd.mjs' }));
  writeFileSync(join(symlinkPkgTarget, 'bin/pdd.mjs'), '#!/usr/bin/env node\n');
  const symlinkPrefix = join(guardRoot, 'symlink-pkg');
  mkdirSync(join(symlinkPrefix, 'lib/node_modules'), { recursive: true });
  symlinkSync(symlinkPkgTarget, join(symlinkPrefix, 'lib/node_modules/pdd'));
  assert.equal(hasLegacyUnscopedPdd(symlinkPrefix), false, 'symlinked node_modules/pdd must not match');

  const gitPkgPrefix = join(guardRoot, 'git-pkg');
  mkdirSync(join(gitPkgPrefix, 'lib/node_modules/pdd/bin'), { recursive: true });
  mkdirSync(join(gitPkgPrefix, 'lib/node_modules/pdd/.git'), { recursive: true });
  writeFileSync(join(gitPkgPrefix, 'lib/node_modules/pdd/package.json'), JSON.stringify({ name: 'pdd', version: '0.1.31', bin: './bin/pdd.mjs' }));
  writeFileSync(join(gitPkgPrefix, 'lib/node_modules/pdd/bin/pdd.mjs'), '#!/usr/bin/env node\n');
  assert.equal(hasLegacyUnscopedPdd(gitPkgPrefix), false, '.git checkout inside node_modules/pdd must not match');

  const home = join(sandbox, 'home');
  mkdirSync(home, { recursive: true });

  // 1. maybeAutoUpdateAutopilot removes unscoped pdd before installing @promptdriven/pdd (even at same version) and rolls back if install fails.
  const autoPrefix = join(sandbox, "auto 'prefix'");
  const autoQuoted = `'${autoPrefix.replace(/'/g, "'\\''")}'`;
  const autoLegacy = join(autoPrefix, 'lib/node_modules/pdd');
  const autoScoped = join(autoPrefix, 'lib/node_modules/@promptdriven/pdd');
  const stateRoot = join(sandbox, 'auto-state');
  const coreRoot = join(sandbox, 'auto-core');
  mkdirSync(join(autoLegacy, 'bin'), { recursive: true });
  mkdirSync(join(autoPrefix, 'bin'), { recursive: true });
  mkdirSync(stateRoot, { recursive: true });
  mkdirSync(join(coreRoot, 'jobs'), { recursive: true });
  writeFileSync(join(autoLegacy, 'package.json'), JSON.stringify({ name: 'pdd', version: targetVersion, bin: 'bin/pdd.mjs' }));
  writeFileSync(join(autoLegacy, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  symlinkSync('../lib/node_modules/pdd/bin/pdd.mjs', join(autoPrefix, 'bin/pdd'));

  assert.equal(hasLegacyUnscopedPdd(autoPrefix, { uid: process.getuid() }), true);
  assert.equal(hasLegacyUnscopedPdd(autoPrefix, { uid: process.getuid() + 1 }), false, 'foreign uid must not match');

  // 1a. Install failure (both npm and github fallback fail) rolls back autoLegacy + bin/pdd intact.
  const autoFailRes = await maybeAutoUpdateAutopilot({
    state: { autoUpdate: 'release' },
    packageRoot: autoLegacy,
    coreRoot,
    stateRoot,
    env: { HOME: home },
  }, {
    now: () => 1_700_000_000_000,
    uid: process.getuid(),
    fetchLatestRelease: async () => ({ tag_name: `alpha-v${targetVersion}`, draft: false }),
    setupSkills: () => [],
    execute: async (file, args) => {
      if (file === 'npm' && args[0] === 'uninstall') {
        rmSync(join(autoPrefix, 'bin/pdd'), { force: true });
        rmSync(autoLegacy, { recursive: true, force: true });
        return { code: 0, stdout: 'removed\n', stderr: '' };
      }
      if (file === 'npm' && args[0] === 'install') {
        return { code: 1, stdout: '', stderr: 'npm error ETIMEDOUT\n' };
      }
      return { code: 0, stdout: '', stderr: '' };
    },
  });
  assert.equal(autoFailRes.action, 'failed');
  assert.equal(hasLegacyUnscopedPdd(autoPrefix, { uid: process.getuid() }), true, 'Autopilot self-update rolled back unscoped pdd after install failure');
  assert.equal(readlinkSync(join(autoPrefix, 'bin/pdd')), '../lib/node_modules/pdd/bin/pdd.mjs');

  // 1b. Subsequent tick (>1h later) succeeds in migrating unscoped pdd -> @promptdriven/pdd via npm-first.
  const autoCmds = [];
  const autoRes = await maybeAutoUpdateAutopilot({
    state: { autoUpdate: 'release' },
    packageRoot: autoLegacy,
    coreRoot,
    stateRoot,
    env: { HOME: home },
  }, {
    now: () => 1_700_004_000_000,
    uid: process.getuid(),
    fetchLatestRelease: async () => ({ tag_name: `alpha-v${targetVersion}`, draft: false }),
    setupSkills: () => [],
    execute: async (file, args) => {
      autoCmds.push([file, ...args]);
      if (file === 'npm' && args[0] === 'uninstall') {
        rmSync(join(autoPrefix, 'bin/pdd'), { force: true });
        rmSync(autoLegacy, { recursive: true, force: true });
        return { code: 0, stdout: 'removed\n', stderr: '' };
      }
      if (file === 'npm' && args[0] === 'install') {
        mkdirSync(autoScoped, { recursive: true });
        writeFileSync(join(autoScoped, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: targetVersion }));
        return { code: 0, stdout: 'installed\n', stderr: '' };
      }
      return { code: 0, stdout: '', stderr: '' };
    },
  });
  assert.deepEqual(autoRes, { action: 'updated', fromVersion: targetVersion, toVersion: targetVersion });
  assert.deepEqual(autoCmds[0], ['npm', 'uninstall', '-g', '--prefix', autoPrefix, '--ignore-scripts', '--no-audit', '--no-fund', 'pdd']);
  assert.deepEqual(autoCmds[1], ['npm', 'install', '-g', '--prefix', autoPrefix, '--ignore-scripts', '--no-audit', '--no-fund', `@promptdriven/pdd@${targetVersion}`]);

  // 1c. When rollback itself fails in maybeAutoUpdateAutopilot, backupDir is preserved and lastError includes its path + quoted restore command.
  const restoreFailFs = {
    ...nativeFs,
    cpSync(src, dst, opts) {
      if (String(src).includes('.pdd-upgrade-backup-')) throw Error('ENOSPC');
      return nativeFs.cpSync(src, dst, opts);
    },
  };
  mkdirSync(join(autoLegacy, 'bin'), { recursive: true });
  writeFileSync(join(autoLegacy, 'package.json'), JSON.stringify({ name: 'pdd', version: targetVersion, bin: 'bin/pdd.mjs' }));
  writeFileSync(join(autoLegacy, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  const autoRbFail = await maybeAutoUpdateAutopilot({
    state: { autoUpdate: 'release' },
    packageRoot: autoLegacy,
    coreRoot,
    stateRoot,
    env: { HOME: home },
  }, {
    now: () => 1_700_008_000_000,
    uid: process.getuid(),
    fs: restoreFailFs,
    fetchLatestRelease: async () => ({ tag_name: `alpha-v${targetVersion}`, draft: false }),
    setupSkills: () => [],
    execute: async (file, args) => {
      if (file === 'npm' && args[0] === 'uninstall') {
        rmSync(autoLegacy, { recursive: true, force: true });
        return { code: 0, stdout: 'removed\n', stderr: '' };
      }
      return { code: 1, stdout: '', stderr: 'npm error ETIMEDOUT\n' };
    },
  });
  assert.equal(autoRbFail.action, 'failed');
  const preservedAutoBackup = readdirSync(autoPrefix).find(entry => entry.startsWith('.pdd-upgrade-backup-'));
  assert.ok(preservedAutoBackup, 'staged backup directory preserved in maybeAutoUpdateAutopilot when restore fails');
  assert.match(autoRbFail.error, /unscoped pdd was removed and rollback failed \(staged backup preserved at /);
  assert.ok(autoRbFail.error.includes(preservedAutoBackup), autoRbFail.error);
  assert.ok(autoRbFail.error.includes(`npm install -g --prefix ${autoQuoted} --ignore-scripts github:promptdriven/pdd#alpha-v${targetVersion}`), autoRbFail.error);
});
