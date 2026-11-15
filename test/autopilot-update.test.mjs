import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, existsSync, mkdtempSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  autoUpdateStatusLine,
  detectGlobalInstallPrefix,
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
  assert.match(out1.text, new RegExp(`Upgraded pdd 0\\.1\\.12 -> ${targetVersion.replace(/\./g, '\\.')} \\(alpha-v${targetVersion.replace(/\./g, '\\.')}\\)\\.`));
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
  assert.match(out2.text, new RegExp(`pdd ${targetVersion.replace(/\./g, '\\.')} is already up to date\\. PDD skills are current\\.`));

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

test('#3424 pdd upgrade refreshes stale skills when CLI is already current, supports .skill-lock.json npx refresh, skips customized copies, and reports failed skill updates with recovery commands', async t => {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cli-upgrade-cases-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const targetVersion = JSON.parse(readFileSync(join(packageRoot, 'package.json'), 'utf8')).version;
  const prefix = join(sandbox, 'global');
  const globalPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  mkdirSync(globalPkg, { recursive: true });
  cpSync(join(packageRoot, 'skills'), join(globalPkg, 'skills'), { recursive: true });
  writeFileSync(join(globalPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: targetVersion }));

  const fetchImpl = async () => ({
    ok: true,
    json: async () => [{ tag_name: `alpha-v${targetVersion}`, draft: false, prerelease: true, published_at: '2026-11-15T12:00:00Z' }],
  });

  // Case A: Already at latest CLI version + .agents/.skill-lock.json (`promptdriven/pdd`) + unmarked 0.1.12 6-skill install + custom skills.
  const homeA = join(sandbox, 'home-lock');
  mkdirSync(join(homeA, '.agents/skills'), { recursive: true });
  writeFileSync(join(homeA, '.agents/.skill-lock.json'), JSON.stringify({
    version: 3,
    skills: { 'pdd-feature': { source: 'promptdriven/pdd', sourceType: 'github' } },
  }));
  for (const name of PDD_SKILL_NAMES.filter(n => n !== 'pdd-graph')) {
    cpSync(join(packageRoot, 'skills', name), join(homeA, '.agents/skills', name), { recursive: true });
    const file = join(homeA, '.agents/skills', name, 'SKILL.md');
    writeFileSync(file, readFileSync(file, 'utf8').replace(/^(  pdd-skills:).*$/m, '$1 0.1.12'));
  }
  mkdirSync(join(homeA, '.agents/skills/pdd-autopilot'), { recursive: true });
  writeFileSync(join(homeA, '.agents/skills/pdd-autopilot/SKILL.md'), 'custom autopilot\n');
  mkdirSync(join(homeA, '.agents/skills/finish-pr'), { recursive: true });
  writeFileSync(join(homeA, '.agents/skills/finish-pr/SKILL.md'), 'custom finish-pr\n');

  const cmdsA = [];
  const outA = captureStream(), errA = captureStream();
  const resA = await runCliUpgrade({
    env: { HOME: homeA },
    stdout: outA,
    stderr: errA,
    fetchImpl,
    spawnSyncImpl: (file, args) => { cmdsA.push([file, ...args]); return { status: 0, stdout: 'ok\n', stderr: '' }; },
    packageRoot: globalPkg,
    home: homeA,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });
  assert.equal(resA.exitCode, 0, errA.text);
  assert.equal(resA.cliUpdated, false);
  assert.equal(cmdsA.some(c => c[0] === 'npm'), false, 'must not reinstall already-current CLI');
  assert.deepEqual(cmdsA, [['npx', '--yes', 'skills', 'add', `promptdriven/pdd#alpha-v${targetVersion}`, '-g', '-a', 'codex', '-a', 'claude-code', '-y']]);
  assert.match(outA.text, /is already up to date\./);
  assert.match(outA.text, /Updated PDD skills to .* in: .*\.agents\/skills/);
  assert.equal(readFileSync(join(homeA, '.agents/skills/pdd-autopilot/SKILL.md'), 'utf8'), 'custom autopilot\n');
  assert.equal(readFileSync(join(homeA, '.agents/skills/finish-pr/SKILL.md'), 'utf8'), 'custom finish-pr\n');

  // Case B: Customized ('differs') skill copy is preserved and reported as skipped even when .skill-lock.json exists.
  const homeB = join(sandbox, 'home-custom');
  mkdirSync(join(homeB, '.agents/skills'), { recursive: true });
  writeFileSync(join(homeB, '.agents/.skill-lock.json'), JSON.stringify({ source: 'promptdriven/pdd' }));
  for (const name of PDD_SKILL_NAMES) {
    cpSync(join(packageRoot, 'skills', name), join(homeB, '.agents/skills', name), { recursive: true });
  }
  const editedSkill = join(homeB, '.agents/skills/pdd-bug/SKILL.md');
  const editedText = `${readFileSync(editedSkill, 'utf8')}\nLocal customization.\n`;
  writeFileSync(editedSkill, editedText);

  const cmdsB = [];
  const outB = captureStream(), errB = captureStream();
  const resB = await runCliUpgrade({
    env: { HOME: homeB },
    stdout: outB,
    stderr: errB,
    fetchImpl,
    spawnSyncImpl: (file, args) => { cmdsB.push([file, ...args]); return { status: 0, stdout: '', stderr: '' }; },
    packageRoot: globalPkg,
    home: homeB,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });
  assert.equal(resB.exitCode, 0);
  assert.equal(cmdsB.length, 0);
  assert.equal(readFileSync(editedSkill, 'utf8'), editedText);
  assert.match(outB.text, /Skipped customized PDD skills in .*\.agents\/skills \(preserved without overwriting\)\. To replace them, run: npx skills add promptdriven\/pdd -g -a codex -a claude-code -y/);

  // Case C: Failed skill update (npx failure & direct folder write failure) reports actionable recovery command and exits 1.
  const outFailNpx = captureStream(), errFailNpx = captureStream();
  const resFailNpx = await runCliUpgrade({
    env: { HOME: homeA },
    stdout: outFailNpx,
    stderr: errFailNpx,
    fetchImpl,
    spawnSyncImpl: () => ({ status: 1, stdout: '', stderr: 'registry offline\n' }),
    packageRoot: globalPkg,
    home: homeA,
    cwd: join(sandbox, 'empty-cwd'),
  }, { uid: process.getuid() });
  assert.equal(resFailNpx.exitCode, 1);
  assert.match(errFailNpx.text, /Failed to update PDD skills in .*\.agents\/skills \(registry offline\)\. To recover, run: npx skills add promptdriven\/pdd -g -a codex -a claude-code -y/);

  const outFailOwned = captureStream(), errFailOwned = captureStream();
  const resFailOwned = await runCliUpgrade({
    env: { HOME: homeA },
    stdout: outFailOwned,
    stderr: errFailOwned,
    fetchImpl,
    spawnSyncImpl: () => ({ status: 0, stdout: '', stderr: '' }),
    packageRoot: globalPkg,
    home: homeA,
    cwd: join(sandbox, 'empty-cwd'),
  }, {
    uid: process.getuid(),
    skillsInstall: {
      syncOwnedUserSkills: ({ onError }) => {
        onError(join(homeA, '.codex/skills'), Object.assign(Error('permission denied'), { code: 'EACCES' }));
        return { updated: [] };
      },
      findSkills: () => [],
    },
  });
  assert.equal(resFailOwned.exitCode, 1);
  assert.match(errFailOwned.text, /Failed to update PDD skills in .*\.codex\/skills \(EACCES\)\. To recover, run: pdd setup/);

  // Case D: Git checkout / non-global packageRoot refuses cleanly with recovery command.
  const outCheckout = captureStream(), errCheckout = captureStream();
  const resCheckout = await runCliUpgrade({
    env: { HOME: homeA },
    stdout: outCheckout,
    stderr: errCheckout,
    packageRoot,
    home: homeA,
  });
  assert.equal(resCheckout.exitCode, 1);
  assert.match(errCheckout.text, /npm install -g github:promptdriven\/pdd && pdd setup/);
});
