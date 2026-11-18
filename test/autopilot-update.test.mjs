import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import * as nativeFs from 'node:fs';
import { cpSync, existsSync, lstatSync, mkdtempSync, mkdirSync, readdirSync, readFileSync, readlinkSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  autoUpdateStatusLine,
  detectGlobalInstallPrefix,
  hasLegacyUnscopedPdd,
  hasMidWriteJobs,
  maybeAutoUpdateAutopilot,
  runCliUpgrade,
} from '../src/autopilot-update.mjs';
import { runAutopilotLauncher } from '../src/autopilot-launcher.mjs';
import { runPdd } from '../src/pdd-cli.mjs';
import { PDD_SKILL_NAMES } from '../src/skills-install.mjs';

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

const captureStream = () => ({ text: '', write(s) { this.text += s; } });

test('#3424 pdd upgrade updates global CLI and marked skills across agent folders (including 6-skill 0.1.12 bundles and .codex/skills), clears release-check.json, handles repeated upgrades, and pins --main SHA', async t => {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cli-upgrade-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const prefix = join(sandbox, 'global');
  const globalPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  const home = join(sandbox, 'home');
  const repoDir = join(sandbox, 'repo');
  mkdirSync(globalPkg, { recursive: true });
  mkdirSync(home, { recursive: true });
  mkdirSync(repoDir, { recursive: true });
  cpSync(join(packageRoot, 'skills'), join(globalPkg, 'skills'), { recursive: true });
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.12' }));

  const targetVersion = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
  const releaseCache = join(home, '.local/state/pdd/release-check.json');
  mkdirSync(dirname(releaseCache), { recursive: true });
  writeFileSync(releaseCache, JSON.stringify({ checkedAt: Date.now(), latestTag: `alpha-v${targetVersion}`, latestVersion: targetVersion }));

  // Seed older 6-skill .pdd-skill.json-marked folders in .agents/skills, .codex/skills and .claude/skills.
  const marker = '.pdd-skill.json';
  for (const rel of ['.agents/skills', '.codex/skills', '.claude/skills']) {
    const folder = join(home, rel);
    for (const name of PDD_SKILL_NAMES.filter(n => n !== 'pdd-graph')) {
      cpSync(join(packageRoot, 'skills', name), join(folder, name), { recursive: true });
      writeFileSync(join(folder, name, marker), JSON.stringify({ package: 'pdd', version: '0.1.12', digest: 'old' }));
    }
  }
  // Marked retired pdd-check is removed; unmarked pdd-autopilot and finish-pr are preserved.
  mkdirSync(join(home, '.agents/skills/pdd-check'), { recursive: true });
  writeFileSync(join(home, '.agents/skills/pdd-check/SKILL.md'), 'old retired\n');
  writeFileSync(join(home, '.agents/skills/pdd-check', marker), JSON.stringify({ package: 'pdd', version: '0.1.12', digest: 'old' }));
  mkdirSync(join(home, '.agents/skills/pdd-autopilot'), { recursive: true });
  writeFileSync(join(home, '.agents/skills/pdd-autopilot/SKILL.md'), 'user custom autopilot\n');
  mkdirSync(join(home, '.codex/skills/finish-pr'), { recursive: true });
  writeFileSync(join(home, '.codex/skills/finish-pr/SKILL.md'), 'user custom finish-pr\n');

  const spawned = [];
  const spawnSyncImpl = (file, args) => {
    spawned.push([file, ...args]);
    if (file === 'npm') {
      writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: targetVersion }));
      return { status: 0, stdout: 'updated\n', stderr: '' };
    }
    return { status: 0, stdout: '', stderr: '' };
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
  assert.match(out1.text, /Updated PDD skills to .* in: .*\.agents\/skills.*\.codex\/skills.*\.claude\/skills/);
  assert.equal(existsSync(releaseCache), false);
  assert.ok(spawned.some(cmd => cmd[0] === 'npm' && cmd.includes('--ignore-scripts') && cmd.includes(`github:promptdriven/pdd#alpha-v${targetVersion}`)));

  for (const rel of ['.agents/skills', '.codex/skills', '.claude/skills']) {
    for (const name of PDD_SKILL_NAMES) {
      assert.equal(JSON.parse(readFileSync(join(home, rel, name, marker), 'utf8')).version, targetVersion, `${rel}/${name}`);
    }
  }
  assert.equal(existsSync(join(home, '.agents/skills/pdd-check')), false);
  assert.equal(readFileSync(join(home, '.agents/skills/pdd-autopilot/SKILL.md'), 'utf8'), 'user custom autopilot\n');
  assert.equal(readFileSync(join(home, '.codex/skills/finish-pr/SKILL.md'), 'utf8'), 'user custom finish-pr\n');

  // 2. Repeated upgrade is a clean no-op with zero subprocess spawns.
  spawned.length = 0;
  const out2 = captureStream(), err2 = captureStream();
  const res2 = await runCliUpgrade({
    env: { HOME: home },
    stdout: out2,
    stderr: err2,
    spawnSyncImpl,
    fetchImpl,
    packageRoot: globalPkg,
    home,
    cwd: repoDir,
  }, { uid: process.getuid() });
  assert.equal(res2.exitCode, 0);
  assert.equal(res2.cliUpdated, false);
  assert.deepEqual(res2.updatedSkills, []);
  assert.equal(spawned.length, 0);
  assert.equal(out2.text, `pdd ${targetVersion} is already up to date. PDD skills are current.\n`);

  // 3. `pdd upgrade --main` pins exact 40-char commit SHA with --ignore-scripts (never mutable #main).
  const outMain = captureStream(), errMain = captureStream();
  const resMain = await runCliUpgrade({
    env: { HOME: home },
    stdout: outMain,
    stderr: errMain,
    main: true,
    spawnSyncImpl,
    fetchImpl,
    packageRoot: globalPkg,
    home,
    cwd: repoDir,
  }, { uid: process.getuid() });
  assert.equal(resMain.exitCode, 0);
  assert.ok(spawned.some(cmd => cmd[0] === 'npm' && cmd.includes('--ignore-scripts') && cmd.includes('github:promptdriven/pdd#0123456789abcdef0123456789abcdef01234567')));
  assert.ok(!spawned.some(cmd => cmd.includes('github:promptdriven/pdd#main')));
});

test('#3424 pdd upgrade refreshes stale marked skills when CLI is already current, never overwrites unmarked or symlinked skills, prints actionable npx hints, and reports failed skill updates', async t => {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cli-upgrade-cases-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const targetVersion = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
  const marker = '.pdd-skill.json';
  const prefix = join(sandbox, 'global');
  const globalPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  mkdirSync(globalPkg, { recursive: true });
  cpSync(join(packageRoot, 'skills'), join(globalPkg, 'skills'), { recursive: true });
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: targetVersion }));

  const fetchImpl = async () => ({
    ok: true,
    json: async () => [{ tag_name: `alpha-v${targetVersion}`, draft: false, prerelease: true, published_at: '2026-11-15T12:00:00Z' }],
  });

  // Case A: Already at latest CLI version + stale .pdd-skill.json-marked folders -> updates ONLY folders that actually changed, zero subprocesses.
  const homeMarked = join(sandbox, 'home-marked');
  for (const name of PDD_SKILL_NAMES.filter(n => n !== 'pdd-graph')) {
    cpSync(join(packageRoot, 'skills', name), join(homeMarked, '.agents/skills', name), { recursive: true });
    writeFileSync(join(homeMarked, '.agents/skills', name, marker), JSON.stringify({ package: 'pdd', version: '0.1.12', digest: 'old' }));
  }
  cpSync(join(packageRoot, 'skills/pdd-bug'), join(homeMarked, '.codex/skills/pdd-bug'), { recursive: true });
  writeFileSync(join(homeMarked, '.codex/skills/pdd-bug', marker), JSON.stringify({ package: 'pdd', version: '0.1.12', digest: 'old' }));

  const cmdsMarked = [];
  const outMarked = captureStream(), errMarked = captureStream();
  const resMarked = await runCliUpgrade({
    env: { HOME: homeMarked },
    stdout: outMarked,
    stderr: errMarked,
    fetchImpl,
    spawnSyncImpl: (file, args) => { cmdsMarked.push([file, ...args]); return { status: 0, stdout: '', stderr: '' }; },
    packageRoot: globalPkg,
    home: homeMarked,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });
  assert.equal(resMarked.exitCode, 0, errMarked.text);
  assert.equal(resMarked.cliUpdated, false);
  assert.equal(cmdsMarked.length, 0, 'must not spawn npm or npx');
  assert.deepEqual(resMarked.updatedSkills, [join(homeMarked, '.agents/skills'), join(homeMarked, '.codex/skills')]);
  assert.deepEqual(resMarked.skippedSkills, []);
  assert.ok(outMarked.text.includes(`pdd ${targetVersion} is already up to date.`), outMarked.text);
  assert.ok(outMarked.text.includes(`Updated PDD skills to ${targetVersion} in: ${join(homeMarked, '.agents/skills')}, ${join(homeMarked, '.codex/skills')}.`), outMarked.text);
  for (const rel of ['.agents/skills', '.codex/skills']) {
    for (const name of PDD_SKILL_NAMES) {
      assert.equal(JSON.parse(readFileSync(join(homeMarked, rel, name, marker), 'utf8')).version, targetVersion);
    }
  }

  // Case B: Unmarked skills, .skill-lock.json copies, symlinks, .codex/skills/$CODEX_HOME/skills unmarked copies, and custom skills are NEVER modified or falsely marked updated.
  const homeUnmarked = join(sandbox, 'home-unmarked');
  const customCodex = join(sandbox, 'custom-codex');
  mkdirSync(join(homeUnmarked, '.agents/skills'), { recursive: true });
  writeFileSync(join(homeUnmarked, '.agents/.skill-lock.json'), JSON.stringify({
    version: 3,
    skills: { 'pdd-feature': { source: 'promptdriven/pdd', sourceType: 'github' } },
  }));
  for (const name of PDD_SKILL_NAMES.filter(n => n !== 'pdd-graph')) {
    cpSync(join(packageRoot, 'skills', name), join(homeUnmarked, '.agents/skills', name), { recursive: true });
    const file = join(homeUnmarked, '.agents/skills', name, 'SKILL.md');
    writeFileSync(file, readFileSync(file, 'utf8').replace(/^(  pdd-skills:).*$/m, '$1 0.1.12'));
  }
  const externalGraph = join(sandbox, 'external-pdd-graph');
  cpSync(join(packageRoot, 'skills/pdd-graph'), externalGraph, { recursive: true });
  const externalGraphMd = readFileSync(join(externalGraph, 'SKILL.md'), 'utf8').replace(/^(  pdd-skills:).*$/m, '$1 0.1.12');
  writeFileSync(join(externalGraph, 'SKILL.md'), externalGraphMd);
  symlinkSync(externalGraph, join(homeUnmarked, '.agents/skills/pdd-graph'));

  cpSync(join(packageRoot, 'skills/pdd-bug'), join(homeUnmarked, '.codex/skills/pdd-bug'), { recursive: true });
  const codexBugMd = readFileSync(join(homeUnmarked, '.codex/skills/pdd-bug/SKILL.md'), 'utf8').replace(/^(  pdd-skills:).*$/m, '$1 0.1.12');
  writeFileSync(join(homeUnmarked, '.codex/skills/pdd-bug/SKILL.md'), codexBugMd);

  cpSync(join(packageRoot, 'skills/pdd-feature'), join(customCodex, 'skills/pdd-feature'), { recursive: true });
  const customFeatureMd = readFileSync(join(customCodex, 'skills/pdd-feature/SKILL.md'), 'utf8').replace(/^(  pdd-skills:).*$/m, '$1 0.1.12');
  writeFileSync(join(customCodex, 'skills/pdd-feature/SKILL.md'), customFeatureMd);

  mkdirSync(join(homeUnmarked, '.agents/skills/pdd-autopilot'), { recursive: true });
  writeFileSync(join(homeUnmarked, '.agents/skills/pdd-autopilot/SKILL.md'), 'custom autopilot\n');
  mkdirSync(join(homeUnmarked, '.agents/skills/finish-pr'), { recursive: true });
  writeFileSync(join(homeUnmarked, '.agents/skills/finish-pr/SKILL.md'), 'custom finish-pr\n');

  const cmdsUnmarked = [];
  const outUnmarked = captureStream(), errUnmarked = captureStream();
  const resUnmarked = await runCliUpgrade({
    env: { HOME: homeUnmarked, CODEX_HOME: customCodex },
    stdout: outUnmarked,
    stderr: errUnmarked,
    fetchImpl,
    spawnSyncImpl: (file, args) => { cmdsUnmarked.push([file, ...args]); return { status: 0, stdout: '', stderr: '' }; },
    packageRoot: globalPkg,
    home: homeUnmarked,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });
  assert.equal(resUnmarked.exitCode, 0, errUnmarked.text);
  assert.equal(cmdsUnmarked.length, 0, 'must never spawn npx skills add');
  assert.deepEqual(resUnmarked.updatedSkills, [], 'must never falsely report unmarked folders as updated');
  assert.equal(outUnmarked.text.includes('Updated PDD skills'), false, outUnmarked.text);
  assert.deepEqual(resUnmarked.skippedSkills.map(s => s.folder), [
    join(homeUnmarked, '.agents/skills'),
    join(customCodex, 'skills'),
    join(homeUnmarked, '.codex/skills'),
  ]);
  assert.ok(outUnmarked.text.includes(`Skipped unmarked PDD skills in ${join(homeUnmarked, '.agents/skills')}`), outUnmarked.text);
  assert.ok(outUnmarked.text.includes(`Skipped unmarked PDD skills in ${join(customCodex, 'skills')} (pdd-feature is 0.1.12)`), outUnmarked.text);
  assert.ok(outUnmarked.text.includes(`Skipped unmarked PDD skills in ${join(homeUnmarked, '.codex/skills')} (pdd-bug is 0.1.12)`), outUnmarked.text);
  assert.ok(outUnmarked.text.includes("To update unmarked skills, run: npx skills add promptdriven/pdd -g --skill '*'"), outUnmarked.text);
  assert.equal(existsSync(join(homeUnmarked, '.agents/skills/pdd-feature', marker)), false);
  assert.equal(lstatSync(join(homeUnmarked, '.agents/skills/pdd-graph')).isSymbolicLink(), true);
  assert.equal(readFileSync(join(externalGraph, 'SKILL.md'), 'utf8'), externalGraphMd);
  assert.equal(readFileSync(join(homeUnmarked, '.codex/skills/pdd-bug/SKILL.md'), 'utf8'), codexBugMd);
  assert.equal(readFileSync(join(customCodex, 'skills/pdd-feature/SKILL.md'), 'utf8'), customFeatureMd);
  assert.equal(readFileSync(join(homeUnmarked, '.agents/skills/pdd-autopilot/SKILL.md'), 'utf8'), 'custom autopilot\n');
  assert.equal(readFileSync(join(homeUnmarked, '.agents/skills/finish-pr/SKILL.md'), 'utf8'), 'custom finish-pr\n');

  // Case C: Customized ('differs') skill copy and project-local stale copy are preserved untouched and reported with global vs project npx commands.
  const homeCustom = join(sandbox, 'home-custom');
  const projectCustom = join(sandbox, 'project-custom');
  mkdirSync(join(homeCustom, '.agents/skills'), { recursive: true });
  for (const name of PDD_SKILL_NAMES) {
    cpSync(join(packageRoot, 'skills', name), join(homeCustom, '.agents/skills', name), { recursive: true });
  }
  const editedSkill = join(homeCustom, '.agents/skills/pdd-bug/SKILL.md');
  const editedText = `${readFileSync(editedSkill, 'utf8')}\nLocal customization.\n`;
  writeFileSync(editedSkill, editedText);

  cpSync(join(packageRoot, 'skills/pdd-feature'), join(projectCustom, '.agents/skills/pdd-feature'), { recursive: true });
  const projFeature = join(projectCustom, '.agents/skills/pdd-feature/SKILL.md');
  const projFeatureText = readFileSync(projFeature, 'utf8').replace(/^(  pdd-skills:).*$/m, '$1 0.1.20');
  writeFileSync(projFeature, projFeatureText);

  const cmdsCustom = [];
  const outCustom = captureStream(), errCustom = captureStream();
  const resCustom = await runCliUpgrade({
    env: { HOME: homeCustom },
    stdout: outCustom,
    stderr: errCustom,
    fetchImpl,
    spawnSyncImpl: (file, args) => { cmdsCustom.push([file, ...args]); return { status: 0, stdout: '', stderr: '' }; },
    packageRoot: globalPkg,
    home: homeCustom,
    cwd: projectCustom,
  }, { uid: process.getuid() });
  assert.equal(resCustom.exitCode, 0);
  assert.equal(cmdsCustom.length, 0);
  assert.equal(readFileSync(editedSkill, 'utf8'), editedText);
  assert.equal(readFileSync(projFeature, 'utf8'), projFeatureText);
  assert.ok(outCustom.text.includes(`Skipped customized PDD skills in ${join(homeCustom, '.agents/skills')} (pdd-bug differs (version ${targetVersion})) (preserved without overwriting). To update unmarked skills, run: npx skills add promptdriven/pdd -g --skill '*'`), outCustom.text);
  assert.ok(outCustom.text.includes(`Skipped unmarked PDD skills in ${join(projectCustom, '.agents/skills')} (pdd-feature is 0.1.20) (preserved without overwriting). To update unmarked skills, run: npx skills add promptdriven/pdd --skill '*'`), outCustom.text);

  // Case D: Failed marker-owned folder write reports actionable recovery command (`pdd setup`) and exits 1.
  const outFailOwned = captureStream(), errFailOwned = captureStream();
  const resFailOwned = await runCliUpgrade({
    env: { HOME: homeMarked },
    stdout: outFailOwned,
    stderr: errFailOwned,
    fetchImpl,
    spawnSyncImpl: () => ({ status: 0, stdout: '', stderr: '' }),
    packageRoot: globalPkg,
    home: homeMarked,
    cwd: join(sandbox, 'empty-cwd'),
  }, {
    uid: process.getuid(),
    skillsInstall: {
      syncOwnedUserSkills: ({ onError }) => {
        onError(join(homeMarked, '.codex/skills'), Object.assign(Error('permission denied'), { code: 'EACCES' }));
        return { updated: [] };
      },
      findSkills: () => [],
    },
  });
  assert.equal(resFailOwned.exitCode, 1);
  assert.match(errFailOwned.text, /Failed to update PDD skills in .*\.codex\/skills \(EACCES\)\. To recover, run: pdd setup/);

  // Case E: Git checkout / non-global packageRoot refuses cleanly with recovery command.
  const outCheckout = captureStream(), errCheckout = captureStream();
  const resCheckout = await runCliUpgrade({
    env: { HOME: homeMarked },
    stdout: outCheckout,
    stderr: errCheckout,
    packageRoot,
    home: homeMarked,
  });
  assert.equal(resCheckout.exitCode, 1);
  assert.match(errCheckout.text, /npm install -g github:promptdriven\/pdd && pdd setup/);
});

test('#3474 pdd upgrade and Autopilot self-update uninstall unscoped pdd before installing @promptdriven/pdd to avoid EEXIST on bin/pdd without --force', async t => {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-legacy-unscoped-3474-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const targetVersion = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
  const marker = '.pdd-skill.json';

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

  // 1. Migrate unscoped pdd@0.1.31 owning <prefix>/bin/pdd -> @promptdriven/pdd@<targetVersion> without EEXIST or --force.
  const prefix = join(sandbox, "my 'npm' prefix");
  const expectedQuotedPrefix = `'${prefix.replace(/'/g, "'\\''")}'`;
  const legacyPkg = join(prefix, 'lib/node_modules/pdd');
  const scopedPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  const binDir = join(prefix, 'bin');
  const home = join(sandbox, 'home');
  mkdirSync(join(legacyPkg, 'bin'), { recursive: true });
  mkdirSync(binDir, { recursive: true });
  mkdirSync(home, { recursive: true });
  writeFileSync(join(legacyPkg, 'package.json'), JSON.stringify({ name: 'pdd', version: '0.1.31', bin: { pdd: './bin/pdd.mjs' } }));
  writeFileSync(join(legacyPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  symlinkSync('../lib/node_modules/pdd/bin/pdd.mjs', join(binDir, 'pdd'));

  for (const name of PDD_SKILL_NAMES) {
    cpSync(join(packageRoot, 'skills', name), join(home, '.agents/skills', name), { recursive: true });
    writeFileSync(join(home, '.agents/skills', name, marker), JSON.stringify({ package: 'pdd', version: '0.1.31', digest: 'old' }));
  }

  assert.equal(hasLegacyUnscopedPdd(prefix, { uid: process.getuid() }), true);
  assert.equal(hasLegacyUnscopedPdd(prefix, { uid: process.getuid() + 1 }), false, 'foreign uid must not match');

  const spawned = [];
  const spawnSyncImpl = (file, args) => {
    spawned.push([file, ...args]);
    assert.ok(!args.includes('--force'), 'must never pass --force during migration');
    if (file === 'npm' && args[0] === 'uninstall') {
      rmSync(join(binDir, 'pdd'), { force: true });
      rmSync(legacyPkg, { recursive: true, force: true });
      return { status: 0, stdout: 'removed 1 package\n', stderr: '' };
    }
    if (file === 'npm' && args[0] === 'install') {
      if (existsSync(join(binDir, 'pdd')) && existsSync(join(legacyPkg, 'package.json'))) {
        return {
          status: 1,
          stdout: '',
          stderr: `npm error code EEXIST\nnpm error path ${join(binDir, 'pdd')}\nnpm error EEXIST: file already exists\n`,
        };
      }
      mkdirSync(join(scopedPkg, 'bin'), { recursive: true });
      cpSync(join(packageRoot, 'skills'), join(scopedPkg, 'skills'), { recursive: true });
      writeFileSync(join(scopedPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: targetVersion, bin: { pdd: 'bin/pdd.mjs' } }));
      writeFileSync(join(scopedPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
      rmSync(join(binDir, 'pdd'), { force: true });
      symlinkSync('../lib/node_modules/@promptdriven/pdd/bin/pdd.mjs', join(binDir, 'pdd'));
      return { status: 0, stdout: 'added 1 package\n', stderr: '' };
    }
    return { status: 0, stdout: '', stderr: '' };
  };
  const fetchImpl = async () => ({
    ok: true,
    json: async () => [{ tag_name: `alpha-v${targetVersion}`, draft: false, prerelease: true, published_at: '2026-11-16T12:00:00Z' }],
  });

  const out = captureStream(), err = captureStream();
  const res = await runCliUpgrade({
    env: { HOME: home },
    stdout: out,
    stderr: err,
    spawnSyncImpl,
    fetchImpl,
    packageRoot: legacyPkg,
    home,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });

  assert.equal(res.exitCode, 0, err.text);
  assert.equal(res.cliUpdated, true);
  assert.equal(res.fromVersion, '0.1.31');
  assert.equal(res.toVersion, targetVersion);
  assert.equal(existsSync(legacyPkg), false, 'unscoped pdd directory removed');
  assert.equal(hasLegacyUnscopedPdd(prefix), false, 'scoped @promptdriven/pdd no longer triggers legacy unscoped detection');
  assert.equal(readdirSync(prefix).some(entry => entry.startsWith('.pdd-upgrade-backup-')), false, 'staged backup cleaned up after install');
  assert.equal(spawned.length, 2);
  assert.deepEqual(spawned[0], ['npm', 'uninstall', '-g', '--prefix', prefix, '--ignore-scripts', '--no-audit', '--no-fund', 'pdd']);
  assert.deepEqual(spawned[1], ['npm', 'install', '-g', '--prefix', prefix, '--ignore-scripts', '--no-audit', '--no-fund', `github:promptdriven/pdd#alpha-v${targetVersion}`]);
  assert.ok(out.text.includes(`Upgraded pdd 0.1.31 -> ${targetVersion} (alpha-v${targetVersion}).`), out.text);
  assert.deepEqual(res.updatedSkills, [join(home, '.agents/skills')]);

  // 2. Non-legacy EEXIST (when hasLegacyUnscopedPdd is false, e.g. Python pdd-cli or manual symlink at bin/pdd):
  //    does NOT suggest a no-op `npm uninstall -g ... pdd` or `--force`, explains non-npm binary/symlink, and quotes prefix with spaces/quotes.
  const outEexist = captureStream(), errEexist = captureStream();
  const resEexist = await runCliUpgrade({
    env: { HOME: home },
    stdout: outEexist,
    stderr: errEexist,
    main: true,
    fetchImpl: async () => ({ ok: true, json: async () => ({ sha: '0123456789abcdef0123456789abcdef01234567' }) }),
    spawnSyncImpl: () => ({
      status: 1,
      stdout: '',
      stderr: `npm error code EEXIST\nnpm error path ${join(binDir, 'pdd')}\n`,
    }),
    packageRoot: scopedPkg,
    home,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });
  assert.equal(resEexist.exitCode, 1);
  assert.doesNotMatch(errEexist.text, /npm uninstall/);
  assert.doesNotMatch(errEexist.text, /--force/);
  assert.match(errEexist.text, /already exists from a non-npm binary or symlink/);
  assert.ok(errEexist.text.includes(`npm install -g --prefix ${expectedQuotedPrefix} --ignore-scripts github:promptdriven/pdd#0123456789abcdef0123456789abcdef01234567 && pdd setup`), errEexist.text);

  // 3. Rollback in runCliUpgrade when npm install fails AFTER npm uninstall removes legacy unscoped pdd,
  //    while protecting a `<prefix>/pdd` directory (e.g. `~/pdd` clone), a `.git`/symlinked sibling `node_modules/pdd`, and unrelated root files:
  const rbPrefix = join(sandbox, "rollback 'cli' prefix");
  const rbQuoted = `'${rbPrefix.replace(/'/g, "'\\''")}'`;
  const rbLegacy = join(rbPrefix, 'lib/node_modules/pdd');
  const rbCloneDir = join(rbPrefix, 'pdd');
  const rbSiblingGit = join(rbPrefix, 'node_modules/pdd');
  mkdirSync(join(rbLegacy, 'bin'), { recursive: true });
  mkdirSync(join(rbPrefix, 'bin'), { recursive: true });
  mkdirSync(join(rbCloneDir, '.git'), { recursive: true });
  mkdirSync(join(rbSiblingGit, '.git'), { recursive: true });
  writeFileSync(join(rbCloneDir, 'precious.txt'), 'user git clone at ~/pdd\n');
  writeFileSync(join(rbSiblingGit, 'package.json'), JSON.stringify({ name: 'pdd', version: '0.1.31', bin: 'bin/pdd.mjs' }));
  writeFileSync(join(rbSiblingGit, 'sibling-checkout.txt'), 'unverified .git sibling\n');
  writeFileSync(join(rbPrefix, 'pdd.cmd'), 'REM unrelated user script\r\n');
  writeFileSync(join(rbPrefix, 'pdd.ps1'), '#!/usr/bin/env pwsh\n& node "$basedir/node_modules/pdd/bin/pdd.mjs" $args\n');
  writeFileSync(join(rbLegacy, 'package.json'), JSON.stringify({ name: 'pdd', version: '0.1.31', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(rbLegacy, 'bin/pdd.mjs'), '#!/usr/bin/env node\nconsole.log("0.1.31");\n', { mode: 0o755 });
  symlinkSync('../lib/node_modules/pdd/bin/pdd.mjs', join(rbPrefix, 'bin/pdd'));

  const outRb = captureStream(), errRb = captureStream();
  const resRb = await runCliUpgrade({
    env: { HOME: home },
    stdout: outRb,
    stderr: errRb,
    fetchImpl,
    spawnSyncImpl: (file, args) => {
      if (file === 'npm' && args[0] === 'uninstall') {
        rmSync(join(rbPrefix, 'bin/pdd'), { force: true });
        rmSync(join(rbPrefix, 'pdd.ps1'), { force: true });
        rmSync(rbLegacy, { recursive: true, force: true });
        return { status: 0, stdout: 'removed\n', stderr: '' };
      }
      if (file === 'npm' && args[0] === 'install') {
        return { status: 1, stdout: '', stderr: 'npm error ECONNRESET network failure\n' };
      }
      return { status: 0, stdout: '', stderr: '' };
    },
    packageRoot: rbLegacy,
    home,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });
  assert.equal(resRb.exitCode, 1);
  assert.equal(hasLegacyUnscopedPdd(rbPrefix, { uid: process.getuid() }), true, 'legacy unscoped pdd restored on disk');
  assert.equal(readlinkSync(join(rbPrefix, 'bin/pdd')), '../lib/node_modules/pdd/bin/pdd.mjs', 'bin/pdd symlink restored');
  assert.match(readFileSync(join(rbPrefix, 'pdd.ps1'), 'utf8'), /node_modules\/pdd\/bin\/pdd\.mjs/, 'verified Windows npm shim restored');
  assert.equal(lstatSync(rbCloneDir).isDirectory(), true, '<prefix>/pdd directory preserved untouched');
  assert.equal(readFileSync(join(rbCloneDir, 'precious.txt'), 'utf8'), 'user git clone at ~/pdd\n');
  assert.equal(readFileSync(join(rbSiblingGit, 'sibling-checkout.txt'), 'utf8'), 'unverified .git sibling\n');
  assert.equal(readFileSync(join(rbPrefix, 'pdd.cmd'), 'utf8'), 'REM unrelated user script\r\n');
  assert.equal(readdirSync(rbPrefix).some(entry => entry.startsWith('.pdd-upgrade-backup-')), false, 'backup dir cleaned up after rollback');
  assert.ok(errRb.text.includes(`npm uninstall -g --prefix ${rbQuoted} pdd && npm install -g --prefix ${rbQuoted} --ignore-scripts github:promptdriven/pdd#alpha-v${targetVersion} && pdd setup`), errRb.text);

  // Also verify a symlinked sibling `<prefix>/node_modules/pdd` remains an untouched symlink across staging and rollback:
  rmSync(rbSiblingGit, { recursive: true, force: true });
  symlinkSync(symlinkPkgTarget, rbSiblingGit);
  const resRbSym = await runCliUpgrade({
    env: { HOME: home },
    stdout: captureStream(),
    stderr: captureStream(),
    fetchImpl,
    spawnSyncImpl: (file, args) => {
      if (file === 'npm' && args[0] === 'uninstall') {
        rmSync(join(rbPrefix, 'bin/pdd'), { force: true });
        rmSync(rbLegacy, { recursive: true, force: true });
        return { status: 0, stdout: 'removed\n', stderr: '' };
      }
      return { status: 1, stdout: '', stderr: 'npm error ECONNRESET\n' };
    },
    packageRoot: rbLegacy,
    home,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });
  assert.equal(resRbSym.exitCode, 1);
  assert.equal(lstatSync(rbSiblingGit).isSymbolicLink(), true, 'symlinked sibling node_modules/pdd untouched');
  rmSync(rbSiblingGit, { force: true });

  // 3b. When rollback itself fails during restore, backupDir is preserved on disk (never deleted) and stderr prints its path + quoted restore command.
  const outRbFail = captureStream(), errRbFail = captureStream();
  const restoreFailFs = {
    ...nativeFs,
    cpSync(src, dst, opts) {
      if (String(src).includes('.pdd-upgrade-backup-')) throw Error('ENOSPC');
      return nativeFs.cpSync(src, dst, opts);
    },
  };
  const resRbFail = await runCliUpgrade({
    env: { HOME: home },
    stdout: outRbFail,
    stderr: errRbFail,
    fetchImpl,
    spawnSyncImpl: (file, args) => {
      if (file === 'npm' && args[0] === 'uninstall') {
        rmSync(join(rbPrefix, 'bin/pdd'), { force: true });
        rmSync(rbLegacy, { recursive: true, force: true });
        return { status: 0, stdout: 'removed\n', stderr: '' };
      }
      return { status: 1, stdout: '', stderr: 'npm error ECONNRESET\n' };
    },
    packageRoot: rbLegacy,
    home,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid(), fs: restoreFailFs });
  assert.equal(resRbFail.exitCode, 1);
  const preservedCliBackup = readdirSync(rbPrefix).find(entry => entry.startsWith('.pdd-upgrade-backup-'));
  assert.ok(preservedCliBackup, 'staged backup directory preserved when restore fails');
  assert.equal(existsSync(join(rbPrefix, preservedCliBackup, 'items/lib/node_modules/pdd/package.json')), true);
  assert.match(errRbFail.text, /Warning: unscoped pdd was removed .* automatic rollback failed \(staged backup preserved at /);
  assert.ok(errRbFail.text.includes(preservedCliBackup), errRbFail.text);
  assert.ok(errRbFail.text.includes(`Restore pdd with: npm install -g --prefix ${rbQuoted} --ignore-scripts github:promptdriven/pdd#alpha-v${targetVersion} && pdd setup`), errRbFail.text);

  // 4. maybeAutoUpdateAutopilot removes unscoped pdd before installing @promptdriven/pdd (even at same version) and rolls back if install fails.
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

  // 4a. Install failure rolls back autoLegacy + bin/pdd intact.
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

  // 4b. Subsequent tick (>1h later) succeeds in migrating unscoped pdd -> @promptdriven/pdd.
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
  assert.deepEqual(autoCmds[1], ['npm', 'install', '-g', '--prefix', autoPrefix, '--ignore-scripts', '--no-audit', '--no-fund', `github:promptdriven/pdd#alpha-v${targetVersion}`]);

  // 4c. When rollback itself fails in maybeAutoUpdateAutopilot, backupDir is preserved and lastError includes its path + quoted restore command.
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
