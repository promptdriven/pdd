import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { cpSync, existsSync, lstatSync, mkdtempSync, mkdirSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
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

function makeMigrationInstall(t) {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-upgrade-migration-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));
  const prefix = join(sandbox, "developer's npm");
  const legacy = join(prefix, 'lib/node_modules/pdd');
  const scoped = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  const bin = join(prefix, 'bin/pdd');
  mkdirSync(join(legacy, 'bin'), { recursive: true });
  mkdirSync(scoped, { recursive: true });
  mkdirSync(dirname(bin), { recursive: true });
  writeFileSync(join(legacy, 'package.json'), '{"name":"pdd","version":"0.1.31"}');
  writeFileSync(join(scoped, 'package.json'), '{"name":"@promptdriven/pdd","version":"0.1.34"}');
  writeFileSync(join(legacy, 'bin/pdd.mjs'), '');
  symlinkSync('../lib/node_modules/pdd/bin/pdd.mjs', bin);
  const quotedPrefix = `'${sandbox}/developer'\\''s npm'`;
  const commands = `npm uninstall -g --prefix ${quotedPrefix} pdd && npm install -g --prefix ${quotedPrefix} --ignore-scripts github:promptdriven/pdd`;
  return { sandbox, legacy, scoped, bin, commands };
}

test('#3474 pdd upgrade --main explains the legacy collision before invoking npm, even if launched from the scoped package', async t => {
  const { sandbox, legacy, scoped, bin, commands } = makeMigrationInstall(t);
  const stdout = captureStream(), stderr = captureStream();
  const cache = join(sandbox, 'release-check.json');
  writeFileSync(cache, '{}');
  const subprocesses = [], lookups = [];
  const exit = await runPdd(['upgrade', '--main'], {
    packageRoot: scoped,
    cwd: sandbox,
    env: { HOME: sandbox, PDD_STATE_DIR: sandbox, PATH: '' },
    stdout,
    stderr,
    cliUpgrade: {
      runCliUpgrade: (opts, ports) => runCliUpgrade({
        ...opts,
        fetchImpl: async url => {
          lookups.push(url);
          return { ok: true, json: async () => ({ sha: 'a'.repeat(40) }) };
        },
        spawnSyncImpl: (...args) => {
          subprocesses.push(args);
          return { status: 1, stderr: 'npm error code EEXIST' };
        },
      }, ports),
    },
  });
  assert.equal(exit, 1);
  assert.equal(stdout.text, '');
  assert.match(stderr.text, /unscoped npm package pdd can block @promptdriven\/pdd/);
  assert.ok(stderr.text.includes(commands), stderr.text);
  assert.deepEqual(lookups, []);
  assert.deepEqual(subprocesses, []);
  assert.equal(readFileSync(cache, 'utf8'), '{}');
  assert.equal(realpathSync(bin), join(legacy, 'bin/pdd.mjs'));
});

test('#3474 auto-update keeps the legacy package intact and reports the complete migration commands with backoff', async t => {
  const { sandbox, legacy, scoped, bin, commands } = makeMigrationInstall(t);
  for (const packageRoot of [legacy, scoped]) {
    const stateRoot = join(sandbox, packageRoot === legacy ? 'legacy-state' : 'scoped-state');
    const subprocesses = [], lookups = [];
    const input = { state: { autoUpdate: 'release' }, packageRoot, stateRoot, env: { HOME: sandbox } };
    const ports = {
      now: () => 1_700_000_000_000,
      fetchLatestRelease: async () => {
        lookups.push('release');
        return { tag_name: 'alpha-v0.1.35' };
      },
      execute: async (...args) => {
        subprocesses.push(args);
        return { code: 1, stderr: 'npm error code EEXIST' };
      },
    };
    const result = await maybeAutoUpdateAutopilot(input, ports);
    assert.equal(result.action, 'failed');
    assert.ok(result.error.includes(commands), result.error);
    const status = autoUpdateStatusLine({ stateRoot });
    assert.ok(status.endsWith(commands), status);
    assert.deepEqual(lookups, []);
    assert.deepEqual(subprocesses, []);
    assert.deepEqual(await maybeAutoUpdateAutopilot(input, ports), { action: 'throttled' });
    assert.equal(realpathSync(bin), join(legacy, 'bin/pdd.mjs'));
  }
});

test('#3424 pdd upgrade updates global CLI and marked skills across agent folders (including 6-skill 0.1.12 bundles and .codex/skills), clears release-check.json, handles repeated upgrades, and pins --main SHA', async t => {
  const sandbox = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-cli-upgrade-')));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const prefix = join(sandbox, 'global');
  const globalPkg = join(prefix, 'lib/node_modules/@promptdriven/pdd');
  const home = join(sandbox, 'home');
  const repoDir = join(sandbox, 'repo');
  mkdirSync(globalPkg, { recursive: true });
  mkdirSync(join(prefix, 'lib/node_modules/pdd'), { recursive: true });
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
