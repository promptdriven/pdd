import './helpers/test-home.mjs';
import assert from 'node:assert/strict';
import { mkdirSync, mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import test from 'node:test';
import {
  classifyInstallKind,
  detectGlobalInstallPrefix,
  hasLegacyUnscopedPdd,
  resolveInstalledBinEntry,
  resolveVoltaNpmBin,
  scrubVoltaEnv,
} from '../src/shared/install-kind.mjs';
import { runCliUpgrade as runSetupCliUpgrade } from '../src/setup/cli-upgrade.mjs';
import { maybeAutoUpdateAutopilot } from '../src/autopilot-update.mjs';

function tempDir(t, prefix) {
  const dir = realpathSync(mkdtempSync(join(tmpdir(), prefix)));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  return dir;
}

function makeVoltaFixture(t, { packageName = '@promptdriven/pdd', version = '0.1.40', layout = 'posix' } = {}) {
  const sandbox = tempDir(t, 'pdd-volta-3628-');
  const voltaHome = join(sandbox, '.volta');
  const home = join(sandbox, 'home');
  const stateDir = join(sandbox, 'state');
  mkdirSync(join(voltaHome, 'bin'), { recursive: true });
  mkdirSync(home, { recursive: true });
  mkdirSync(stateDir, { recursive: true });
  writeFileSync(join(voltaHome, 'bin', 'npm'), '#!/bin/sh\nexit 0\n', { mode: 0o755 });

  const pkgRel = layout === 'flat'
    ? join('tools/image/packages', packageName)
    : layout === 'win'
      ? join('tools/image/packages', packageName, 'node_modules', packageName)
      : join('tools/image/packages', packageName, 'lib/node_modules', packageName);
  const pkgRoot = join(voltaHome, pkgRel);
  mkdirSync(join(pkgRoot, 'bin'), { recursive: true });
  writeFileSync(join(pkgRoot, 'bin/pdd.mjs'), '#!/usr/bin/env node\n');
  writeFileSync(join(pkgRoot, 'package.json'), JSON.stringify({
    name: packageName,
    version,
    bin: { pdd: 'bin/pdd.mjs' },
  }));
  return { sandbox, voltaHome, home, stateDir, pkgRoot };
}

test('#3628 classifyInstallKind & detectGlobalInstallPrefix detect Volta installs before node_modules (POSIX, flat, legacy unscoped, Windows)', t => {
  const scoped = makeVoltaFixture(t, { packageName: '@promptdriven/pdd', version: '0.1.41', layout: 'posix' });
  const cScoped = classifyInstallKind(scoped.pkgRoot, { env: { VOLTA_HOME: scoped.voltaHome } });
  assert.equal(cScoped.kind, 'volta');
  assert.equal(cScoped.voltaHome, scoped.voltaHome);
  assert.equal(cScoped.prefix, scoped.voltaHome);
  assert.equal(cScoped.npmBin, join(scoped.voltaHome, 'bin', 'npm'));
  assert.equal(cScoped.packageName, '@promptdriven/pdd');
  assert.equal(cScoped.isLegacyUnscoped, false);
  assert.equal(cScoped.realPackageRoot, scoped.pkgRoot);

  // Derived <voltaHome> works even when VOLTA_HOME is unset.
  const cDerived = classifyInstallKind(scoped.pkgRoot, { env: {} });
  assert.equal(cDerived.kind, 'volta');
  assert.equal(cDerived.voltaHome, scoped.voltaHome);
  assert.equal(cDerived.npmBin, join(scoped.voltaHome, 'bin', 'npm'));

  const dScoped = detectGlobalInstallPrefix(scoped.pkgRoot, { env: {} });
  assert.equal(dScoped?.kind, 'volta');
  assert.equal(dScoped?.voltaHome, scoped.voltaHome);

  // Foreign UID is refused cleanly.
  if (typeof process.getuid === 'function') {
    const uid = process.getuid();
    assert.equal(classifyInstallKind(scoped.pkgRoot, { uid: uid + 1 }).kind, 'unowned-prefix');
    assert.equal(detectGlobalInstallPrefix(scoped.pkgRoot, { uid: uid + 1 }), null);
  }

  // Legacy unscoped `pdd` under Volta is flagged as legacy unscoped.
  const legacy = makeVoltaFixture(t, { packageName: 'pdd', version: '0.1.40', layout: 'posix' });
  const cLegacy = classifyInstallKind(legacy.pkgRoot, { env: {} });
  assert.equal(cLegacy.kind, 'volta');
  assert.equal(cLegacy.packageName, 'pdd');
  assert.equal(cLegacy.isLegacyUnscoped, true);
  assert.equal(hasLegacyUnscopedPdd(cLegacy), true);
  assert.equal(hasLegacyUnscopedPdd(legacy.voltaHome), true);

  // Flat Volta image directory without nested node_modules.
  const flat = makeVoltaFixture(t, { packageName: '@promptdriven/pdd', version: '0.1.41', layout: 'flat' });
  assert.equal(classifyInstallKind(flat.pkgRoot, { env: {} }).kind, 'volta');

  // Windows Volta path with mocked fs and platform: 'win32' resolves <voltaHome>\\bin\\npm.cmd.
  const winVoltaHome = 'C:\\Users\\dev\\.volta';
  const winPkgRoot = `${winVoltaHome}\\tools\\image\\packages\\@promptdriven\\pdd\\node_modules\\@promptdriven\\pdd`;
  const mockWinFs = {
    realpathSync: p => p,
    statSync: () => ({ isDirectory: () => true, uid: 1000 }),
    existsSync: p => p === `${winVoltaHome}\\bin\\npm.cmd`,
  };
  const cWin = classifyInstallKind(winPkgRoot, { fs: mockWinFs, uid: 1000, env: { VOLTA_HOME: winVoltaHome }, platform: 'win32' });
  assert.equal(cWin.kind, 'volta');
  assert.equal(cWin.voltaHome, winVoltaHome);
  assert.equal(cWin.npmBin, `${winVoltaHome}\\bin\\npm.cmd`);
  assert.equal(resolveVoltaNpmBin(winVoltaHome, { fs: mockWinFs, platform: 'win32' }), `${winVoltaHome}\\bin\\npm.cmd`);
});

test('#3628 scrubVoltaEnv strips _VOLTA_TOOL_RECURSION, VOLTA_UNSAFE_GLOBAL, and npm_config_prefix (case-insensitive) and sets VOLTA_HOME', () => {
  const cleaned = scrubVoltaEnv({
    PATH: '/usr/bin',
    HOME: '/home/dev',
    _VOLTA_TOOL_RECURSION: '1',
    VOLTA_UNSAFE_GLOBAL: '1',
    npm_config_prefix: '/bad/prefix',
    NPM_CONFIG_PREFIX: '/also/bad',
    VOLTA_HOME: '/wrong/volta',
  }, '/real/.volta');
  assert.equal('_VOLTA_TOOL_RECURSION' in cleaned, false);
  assert.equal('VOLTA_UNSAFE_GLOBAL' in cleaned, false);
  assert.equal('npm_config_prefix' in cleaned, false);
  assert.equal('NPM_CONFIG_PREFIX' in cleaned, false);
  assert.equal(cleaned.VOLTA_HOME, '/real/.volta');
  assert.equal(cleaned.PATH, '/usr/bin');
  assert.equal(cleaned.HOME, '/home/dev');
});

test('#3628 src/setup/cli-upgrade.mjs upgrades scoped Volta install via <voltaHome>/bin/npm without --prefix and scrubs Volta env', async t => {
  const { voltaHome, home, stateDir, pkgRoot } = makeVoltaFixture(t, { packageName: '@promptdriven/pdd', version: '0.1.40' });
  const env = {
    HOME: home,
    PDD_STATE_DIR: stateDir,
    VOLTA_HOME: voltaHome,
    _VOLTA_TOOL_RECURSION: '1',
    VOLTA_UNSAFE_GLOBAL: '1',
    npm_config_prefix: join(voltaHome, 'tools/image/packages/@promptdriven/pdd'),
  };
  const calls = [];
  let syncedRoot = null;
  let out = '', err = '';
  const res = await runSetupCliUpgrade(
    {
      packageRoot: pkgRoot,
      env,
      stdout: { write: s => { out += s; } },
      stderr: { write: s => { err += s; } },
      fetchImpl: async () => ({ ok: true, json: async () => [{ tag_name: 'v0.2.0', draft: false, prerelease: false }] }),
      spawnSyncImpl: (cmd, args, opts) => {
        calls.push({ cmd, args, env: opts?.env });
        writeFileSync(join(pkgRoot, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.2.0', bin: { pdd: 'bin/pdd.mjs' } }));
        return { status: 0, stdout: 'added 1 package\n', stderr: '' };
      },
    },
    {
      skillsInstall: {
        syncOwnedUserSkills: ({ packageRoot }) => { syncedRoot = packageRoot; return { updated: [join(home, '.agents/skills')] }; },
        findSkills: () => [],
      },
    },
  );
  assert.equal(res.exitCode, 0, err);
  assert.equal(res.cliUpdated, true);
  assert.equal(res.fromVersion, '0.1.40');
  assert.equal(res.toVersion, '0.2.0');
  assert.equal(calls.length, 1);
  assert.equal(calls[0].cmd, join(voltaHome, 'bin', 'npm'));
  assert.deepEqual(calls[0].args, ['install', '-g', '--ignore-scripts', '--no-audit', '--no-fund', '@promptdriven/pdd@0.2.0']);
  assert.equal(calls[0].args.includes('--prefix'), false);
  assert.equal('_VOLTA_TOOL_RECURSION' in calls[0].env, false);
  assert.equal('VOLTA_UNSAFE_GLOBAL' in calls[0].env, false);
  assert.equal('npm_config_prefix' in calls[0].env, false);
  assert.equal(calls[0].env.VOLTA_HOME, voltaHome);
  assert.equal(syncedRoot, pkgRoot);
  assert.match(out, /Upgraded pdd 0\.1\.40 -> 0\.2\.0/);
});

test('#3628 src/setup/cli-upgrade.mjs migrates legacy unscoped pdd -> @promptdriven/pdd under Volta without --prefix and formats Volta-safe recovery', async t => {
  const { voltaHome, home, stateDir, pkgRoot } = makeVoltaFixture(t, { packageName: 'pdd', version: '0.2.0' });
  const env = {
    HOME: home,
    PDD_STATE_DIR: stateDir,
    _VOLTA_TOOL_RECURSION: '1',
    VOLTA_UNSAFE_GLOBAL: '1',
    npm_config_prefix: '/stale/prefix',
  };
  const scopedRoot = join(voltaHome, 'tools/image/packages/@promptdriven/pdd/lib/node_modules/@promptdriven/pdd');
  const calls = [];
  let syncedRoot = null;
  let out = '', err = '';
  const res = await runSetupCliUpgrade(
    {
      packageRoot: pkgRoot,
      env,
      stdout: { write: s => { out += s; } },
      stderr: { write: s => { err += s; } },
      fetchImpl: async () => ({ ok: true, json: async () => [{ tag_name: 'v0.2.0', draft: false, prerelease: false }] }),
      spawnSyncImpl: (cmd, args, opts) => {
        calls.push({ cmd, args, env: opts?.env });
        if (args[0] === 'uninstall') {
          rmSync(join(voltaHome, 'tools/image/packages/pdd'), { recursive: true, force: true });
          return { status: 0, stdout: 'removed 1 package\n', stderr: '' };
        }
        mkdirSync(join(scopedRoot, 'bin'), { recursive: true });
        writeFileSync(join(scopedRoot, 'bin/pdd.mjs'), '#!/usr/bin/env node\n');
        writeFileSync(join(scopedRoot, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.2.0', bin: { pdd: 'bin/pdd.mjs' } }));
        return { status: 0, stdout: 'added 1 package\n', stderr: '' };
      },
    },
    {
      skillsInstall: {
        syncOwnedUserSkills: ({ packageRoot }) => { syncedRoot = packageRoot; return { updated: [] }; },
        findSkills: () => [],
      },
    },
  );
  assert.equal(res.exitCode, 0, err);
  assert.equal(res.cliUpdated, true);
  assert.equal(calls.length, 2);
  assert.equal(calls[0].cmd, join(voltaHome, 'bin', 'npm'));
  assert.deepEqual(calls[0].args, ['uninstall', '-g', '--ignore-scripts', '--no-audit', '--no-fund', 'pdd']);
  assert.equal(calls[1].cmd, join(voltaHome, 'bin', 'npm'));
  assert.deepEqual(calls[1].args, ['install', '-g', '--ignore-scripts', '--no-audit', '--no-fund', '@promptdriven/pdd@0.2.0']);
  for (const call of calls) {
    assert.equal(call.args.includes('--prefix'), false);
    assert.equal('_VOLTA_TOOL_RECURSION' in call.env, false);
    assert.equal('VOLTA_UNSAFE_GLOBAL' in call.env, false);
    assert.equal('npm_config_prefix' in call.env, false);
    assert.equal(call.env.VOLTA_HOME, voltaHome);
  }
  assert.equal(syncedRoot, scopedRoot, 'targetPkgRoot re-resolved to scoped packages/@promptdriven/pdd');
  assert.match(out, /Upgraded pdd 0\.2\.0 -> 0\.2\.0/);

  // Failure recovery messages under Volta must NEVER contain `--prefix`.
  let failErr = '';
  const failRes = await runSetupCliUpgrade(
    {
      packageRoot: scopedRoot,
      env,
      stdout: { write() {} },
      stderr: { write: s => { failErr += s; } },
      fetchImpl: async () => ({ ok: true, json: async () => [{ tag_name: 'v0.3.0', draft: false, prerelease: false }] }),
      spawnSyncImpl: () => ({ status: 1, stdout: '', stderr: 'npm error code EEXIST\nFile exists' }),
    },
    { skillsInstall: { syncOwnedUserSkills: () => ({ updated: [] }), findSkills: () => [] } },
  );
  assert.equal(failRes.exitCode, 1);
  assert.doesNotMatch(failErr, /--prefix/);
  assert.match(failErr, /npm install -g --ignore-scripts @promptdriven\/pdd@0\.3\.0 && pdd setup/);
});

test('#3628/#3645 maybeAutoUpdateAutopilot & runCliUpgrade upgrade Volta installs without --prefix, scrub env, and delegate setup --upgrade to newly installed binary', async t => {
  // 1. maybeAutoUpdateAutopilot: legacy unscoped pdd -> @promptdriven/pdd under Volta (npm-first + delegated setup --upgrade).
  const { voltaHome, home, stateDir, pkgRoot } = makeVoltaFixture(t, { packageName: 'pdd', version: '0.1.40' });
  const scopedRoot = join(voltaHome, 'tools/image/packages/@promptdriven/pdd/lib/node_modules/@promptdriven/pdd');
  const coreRoot = join(stateDir, 'repo-core');
  mkdirSync(coreRoot, { recursive: true });
  const execCalls = [];
  const autoRes = await maybeAutoUpdateAutopilot(
    {
      state: { autoUpdate: 'release' },
      packageRoot: pkgRoot,
      coreRoot,
      stateRoot: stateDir,
      env: {
        HOME: home,
        VOLTA_HOME: voltaHome,
        _VOLTA_TOOL_RECURSION: '1',
        VOLTA_UNSAFE_GLOBAL: '1',
        npm_config_prefix: '/bad/prefix',
      },
    },
    {
      now: () => 1_700_000_000_000,
      fetchLatestRelease: async () => [{ tag_name: 'v0.2.0', draft: false, prerelease: false }],
      execute: async (cmd, args, opts) => {
        execCalls.push({ cmd, args, opts });
        if (args[0] === 'uninstall') {
          rmSync(join(voltaHome, 'tools/image/packages/pdd'), { recursive: true, force: true });
          return { code: 0, stdout: '', stderr: '' };
        }
        if (args[0] === 'install') {
          mkdirSync(join(scopedRoot, 'bin'), { recursive: true });
          writeFileSync(join(scopedRoot, 'bin/pdd.mjs'), '#!/usr/bin/env node\n');
          writeFileSync(join(scopedRoot, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.2.0', bin: { pdd: 'bin/pdd.mjs' } }));
          return { code: 0, stdout: '', stderr: '' };
        }
        return { code: 0, stdout: '', stderr: '' };
      },
    },
  );
  assert.equal(autoRes.action, 'updated', JSON.stringify(autoRes));
  assert.equal(autoRes.fromVersion, '0.1.40');
  assert.equal(autoRes.toVersion, '0.2.0');
  assert.equal(execCalls.length, 3);
  assert.equal(execCalls[0].cmd, join(voltaHome, 'bin', 'npm'));
  assert.deepEqual(execCalls[0].args, ['uninstall', '-g', '--ignore-scripts', '--no-audit', '--no-fund', 'pdd']);
  assert.equal(execCalls[1].cmd, join(voltaHome, 'bin', 'npm'));
  assert.deepEqual(execCalls[1].args, ['install', '-g', '--ignore-scripts', '--no-audit', '--no-fund', '@promptdriven/pdd@0.2.0']);
  assert.equal(execCalls[2].cmd, process.execPath);
  assert.deepEqual(execCalls[2].args, [join(scopedRoot, 'bin/pdd.mjs'), 'setup', '--upgrade']);
  for (const call of execCalls) {
    assert.equal(call.args.includes('--prefix'), false);
    assert.equal('_VOLTA_TOOL_RECURSION' in call.opts.env, false);
    assert.equal('VOLTA_UNSAFE_GLOBAL' in call.opts.env, false);
    assert.equal('npm_config_prefix' in call.opts.env, false);
    assert.equal(call.opts.env.VOLTA_HOME, voltaHome);
  }

  // 2. runSetupCliUpgrade on scoped Volta install delegates `setup --upgrade` with scrubbed Volta env + Volta-safe failure text.
  const cliCalls = [];
  let cliOut = '', cliErr = '';
  const cliOk = await runSetupCliUpgrade(
    {
      packageRoot: scopedRoot,
      env: { HOME: home, PDD_STATE_DIR: stateDir, _VOLTA_TOOL_RECURSION: '1', VOLTA_UNSAFE_GLOBAL: '1', npm_config_prefix: '/bad' },
      stdout: { write: s => { cliOut += s; } },
      stderr: { write: s => { cliErr += s; } },
      fetchImpl: async () => ({ ok: true, json: async () => [{ tag_name: 'v0.3.0', draft: false, prerelease: false }] }),
      spawnSyncImpl: (cmd, args, opts) => {
        cliCalls.push({ cmd, args, env: opts?.env });
        if (args[0] === 'install') {
          writeFileSync(join(scopedRoot, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.3.0', bin: { pdd: 'bin/pdd.mjs' } }));
        }
        return { status: 0, stdout: '', stderr: '' };
      },
    },
  );
  assert.equal(cliOk.exitCode, 0, cliErr);
  assert.equal(cliCalls.length, 2);
  assert.equal(cliCalls[0].cmd, join(voltaHome, 'bin', 'npm'));
  assert.equal(cliCalls[1].cmd, process.execPath);
  assert.deepEqual(cliCalls[1].args, [join(scopedRoot, 'bin/pdd.mjs'), 'setup', '--upgrade']);
  for (const call of cliCalls) {
    assert.equal(call.args.includes('--prefix'), false);
    assert.equal('_VOLTA_TOOL_RECURSION' in call.env, false);
    assert.equal('VOLTA_UNSAFE_GLOBAL' in call.env, false);
    assert.equal('npm_config_prefix' in call.env, false);
    assert.equal(call.env.VOLTA_HOME, voltaHome);
  }

  // Failure recovery under Volta falls back npm -> github tag and NEVER prints `--prefix`.
  let failErr = '';
  const cliFail = await runSetupCliUpgrade(
    {
      packageRoot: scopedRoot,
      env: { HOME: home, PDD_STATE_DIR: stateDir, _VOLTA_TOOL_RECURSION: '1', VOLTA_UNSAFE_GLOBAL: '1', npm_config_prefix: '/bad' },
      stdout: { write() {} },
      stderr: { write: s => { failErr += s; } },
      fetchImpl: async () => ({ ok: true, json: async () => [{ tag_name: 'v0.4.0', draft: false, prerelease: false }] }),
      spawnSyncImpl: () => ({ status: 1, stdout: '', stderr: 'network timeout' }),
    },
  );
  assert.equal(cliFail.exitCode, 1);
  assert.doesNotMatch(failErr, /--prefix/);
  assert.match(failErr, /npm install -g --ignore-scripts github:promptdriven\/pdd#v0\.4\.0 && pdd setup/);

  // Security & reliability guards:
  // 1. resolveInstalledBinEntry rejects `..` traversal, absolute paths, and escaping symlinks.
  const { symlinkSync } = await import('node:fs');
  const secDir = tempDir(t, 'pdd-bin-sec-');
  const evilFile = join(secDir, 'evil.mjs');
  writeFileSync(evilFile, '#!/usr/bin/env node\n');
  const travPkg = join(secDir, 'pkg');
  mkdirSync(join(travPkg, 'bin'), { recursive: true });
  writeFileSync(join(travPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.50', bin: { pdd: '../evil.mjs' } }));
  assert.equal(resolveInstalledBinEntry(travPkg), null, 'must reject ../ traversal in package.json bin');
  writeFileSync(join(travPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.50', bin: { pdd: evilFile } }));
  assert.equal(resolveInstalledBinEntry(travPkg), null, 'must reject absolute path in package.json bin');
  writeFileSync(join(travPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.50', bin: { pdd: 'bin/pdd.mjs' } }));
  symlinkSync(evilFile, join(travPkg, 'bin/pdd.mjs'));
  assert.equal(resolveInstalledBinEntry(travPkg), null, 'must reject symlink escaping pkgRoot');

  // 2. Signal-killed child (`status: null, signal: 'SIGKILL'`) fails with exitCode 1 (never treated as 0).
  let sigErr = '';
  const sigRes = await runSetupCliUpgrade({
    packageRoot: scopedRoot,
    env: { HOME: home, PDD_STATE_DIR: stateDir },
    stdout: { write() {} },
    stderr: { write: s => { sigErr += s; } },
    fetchImpl: async () => ({ ok: true, json: async () => [{ tag_name: 'v0.3.0', draft: false, prerelease: false }] }),
    spawnSyncImpl: () => ({ status: null, signal: 'SIGKILL', stdout: '', stderr: '' }),
  });
  assert.equal(sigRes.exitCode, 1);
  assert.match(sigErr, /killed by SIGKILL/);
});
