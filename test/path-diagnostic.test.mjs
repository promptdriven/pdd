import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { diagnoseHostInstalls, formatHostInstallWarnings, pathDiagnostic, shortenHomePath } from '../src/path-diagnostic.mjs';

const bin = resolve(import.meta.dirname, '../bin/pdd.mjs');
const version = JSON.parse(readFileSync(new URL('../package.json', import.meta.url))).version;
function fixture(t) {
  // Setup needs a regular config path even when the OS temp directory is linked.
  const root = realpathSync(mkdtempSync(join(tmpdir(), "pdd-path ' proof-")));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const old = join(root, 'conda-bin'), alpha = join(root, 'alpha-bin'), nodeBin = join(root, 'node-bin'), home = join(root, 'home'), cwd = join(root, 'project');
  for (const path of [old, alpha, nodeBin, home, cwd]) mkdirSync(path);
  symlinkSync(process.execPath, join(nodeBin, 'node'));
  writeFileSync(join(nodeBin, 'codex'), '#!/bin/sh\necho Logged in\n', { mode: 0o755 });
  const legacy = '#!/bin/sh\nprintf "pdd, version 0.0.305.dev214\\n"\n';
  writeFileSync(join(old, 'pdd'), legacy, { mode: 0o755 });
  symlinkSync(bin, join(alpha, 'pdd'));
  const env = { ...process.env, HOME: home, CODEX_HOME: join(home, '.codex'), CLAUDE_CONFIG_DIR: '', PATH: [old, alpha, nodeBin, '/usr/bin', '/bin'].join(':') };
  delete env.PDD_PATH_PROBE;
  const run = (...args) => spawnSync(process.execPath, [bin, ...args], { cwd, env, encoding: 'utf8', timeout: 10000 });
  return { root, old, alpha, nodeBin, cwd, env, run, legacy };
}

test('PATH1: setup and version identify the running Alpha, selected legacy version, all paths and activation order', t => {
  const f = fixture(t);
  for (const args of [['setup'], ['--version']]) {
    const r = f.run(...args);
    assert.equal(r.status, 0, r.stderr);
    if (args[0] === '--version') assert.equal(r.stdout, `${version}\n`);
    assert.ok(r.stderr.includes(bin)); assert.ok(r.stderr.includes(`Running pdd ${version}`));
    assert.ok(r.stderr.includes(join(f.old, 'pdd'))); assert.ok(r.stderr.includes(join(f.alpha, 'pdd')));
    assert.match(r.stderr, /PATH selects:.*pdd, version 0\.0\.305\.dev214/);
    assert.match(r.stderr, /conda/); assert.match(r.stderr, /after.*activat/i); assert.match(r.stderr, /shadow this pdd again/);
    assert.ok(r.stderr.includes(process.execPath)); assert.match(r.stderr, /export PATH=.*hash -r/);
    assert.equal(readFileSync(join(f.old, 'pdd'), 'utf8'), f.legacy);
  }
});

test('PATH2: PATH correction selects Alpha and a second version check terminates without recursive probes', t => {
  const f = fixture(t);
  f.env.PATH = [f.alpha, f.old, f.nodeBin, '/usr/bin', '/bin'].join(':');
  const r = f.run('--version');
  assert.equal(r.status, 0, r.stderr); assert.equal(r.stdout, `${version}\n`);
  assert.match(r.stderr, new RegExp(`PATH selects:.*\\(pdd ${version.replaceAll('.', '\\.')}\\)`));
  assert.ok(r.stderr.includes(join(f.old, 'pdd')));
  rmSync(join(f.old, 'pdd'));
  assert.equal(f.run('--version').stderr, '');
});

test('PATH3: an unreportable version stays visible and help makes no version probe', t => {
  const f = fixture(t), mark = join(f.root, 'probed');
  writeFileSync(join(f.old, 'pdd'), '#!/bin/sh\necho probed > "'+mark+'"\nexit 7\n', { mode: 0o755 });
  assert.equal(f.run('--help').stderr, '');
  assert.throws(() => readFileSync(mark), { code: 'ENOENT' });
  const r = f.run('--version');
  assert.equal(r.status, 0); assert.match(r.stderr, /PATH selects:.*version unavailable/);
  assert.equal(readFileSync(mark, 'utf8'), 'probed\n');
});

test('PATH5: without which, relative PATH entries and symlinked Alpha still resolve correctly', t => {
  const f = fixture(t);
  f.env.PATH = '../conda-bin:../alpha-bin';
  const r = f.run('--version');
  assert.equal(r.status, 0, r.stderr); assert.equal(r.stdout, `${version}\n`);
  assert.match(r.stderr, /PATH selects:.*0\.0\.305\.dev214/);
  assert.ok(r.stderr.includes(join(f.alpha, 'pdd')));
});

test('PATH6: probing another Alpha installation terminates and keeps version-only stdout', t => {
  const f = fixture(t), other = join(f.root, 'other-alpha');
  mkdirSync(other);
  for (const name of ['src', 'bin', 'package.json']) cpSync(resolve(import.meta.dirname, '..', name), join(other, name), { recursive: true });
  symlinkSync(resolve(import.meta.dirname, '..', 'node_modules'), join(other, 'node_modules'), 'dir');
  rmSync(join(f.old, 'pdd')); symlinkSync(join(other, 'bin/pdd.mjs'), join(f.old, 'pdd'));
  const r = f.run('--version');
  assert.equal(r.status, 0, r.stderr); assert.equal(r.stdout, `${version}\n`);
  assert.match(r.stderr, new RegExp(`PATH selects:.*\\(${version.replaceAll('.', '\\.')}\\)`));
});

test('PATH7: a hanging external version probe is bounded and leaves the installation intact', t => {
  const f = fixture(t), hanging = '#!/bin/sh\nexec /bin/sleep 10\n';
  writeFileSync(join(f.old, 'pdd'), hanging, { mode: 0o755 });
  const r = f.run('--version');
  assert.equal(r.status, 0); assert.match(r.stderr, /PATH selects:.*version unavailable/);
  assert.equal(readFileSync(join(f.old, 'pdd'), 'utf8'), hanging);
});


test('PATH8: #2715 package uses @promptdriven/pdd and pathDiagnostic flags an unrelated unscoped npm "pdd" package', t => {
  const pkgMeta = JSON.parse(readFileSync(new URL('../package.json', import.meta.url), 'utf8'));
  assert.equal(pkgMeta.name, '@promptdriven/pdd');
  assert.equal(pkgMeta.bin.pdd, 'bin/pdd.mjs');

  const f = fixture(t);
  rmSync(join(f.old, 'pdd'));
  const npmPrefix = join(f.root, 'npm-global');
  const npmBin = join(npmPrefix, 'bin');
  const foreignPkg = join(npmPrefix, 'lib/node_modules/pdd');
  mkdirSync(npmBin, { recursive: true });
  mkdirSync(foreignPkg, { recursive: true });
  writeFileSync(join(foreignPkg, 'package.json'), JSON.stringify({ name: 'pdd', version: '0.4.14', description: 'PDD Framework' }));
  f.env.PATH = [npmBin, f.alpha, f.nodeBin, '/usr/bin', '/bin'].join(':');

  const r = f.run('--version');
  assert.equal(r.status, 0, r.stderr);
  assert.equal(r.stdout, `${version}\n`);
  assert.match(r.stderr, /Found the unrelated npm package "pdd"/);
  assert.match(r.stderr, /npm uninstall -g pdd && npm install -g @promptdriven\/pdd/);
});

test('PATH9: #3474 pathDiagnostic flags an unscoped PDD npm package owning bin/pdd and recommends explicit uninstall before install', t => {
  const f = fixture(t);
  rmSync(join(f.old, 'pdd'));
  const npmPrefix = join(f.root, 'npm-legacy-pdd');
  const npmBin = join(npmPrefix, 'bin');
  const legacyPkg = join(npmPrefix, 'lib/node_modules/pdd');
  mkdirSync(npmBin, { recursive: true });
  mkdirSync(join(legacyPkg, 'bin'), { recursive: true });
  writeFileSync(join(legacyPkg, 'package.json'), JSON.stringify({ name: 'pdd', version: '0.1.31', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(legacyPkg, 'bin/pdd.mjs'), '#!/bin/sh\nprintf "0.1.31\\n"\n', { mode: 0o755 });
  symlinkSync('../lib/node_modules/pdd/bin/pdd.mjs', join(npmBin, 'pdd'));
  f.env.PATH = [npmBin, f.alpha, f.nodeBin, '/usr/bin', '/bin'].join(':');

  const r = f.run('--version');
  assert.equal(r.status, 0, r.stderr);
  assert.equal(r.stdout, `${version}\n`);
  assert.match(r.stderr, /Found unscoped npm package "pdd".*blocks @promptdriven\/pdd on bin\/pdd/);
  assert.match(r.stderr, /npm uninstall -g pdd && npm install -g @promptdriven\/pdd/);
  assert.doesNotMatch(r.stderr, /--force/);
});

test('PATH10: clean setup stays quiet on PATH diagnostics when no conflict exists', t => {
  const f = fixture(t);
  rmSync(join(f.old, 'pdd'));
  f.env.PATH = [f.alpha, f.nodeBin, '/usr/bin', '/bin'].join(':');
  const r = f.run('setup');
  assert.equal(r.status, 0, r.stderr);
  assert.doesNotMatch(r.stderr, /Running pdd|PATH selects:/);
});

test('PATH11: diagnoseHostInstalls deduplicates symlinks, matching Volta shims, and matching pnpm wrappers without false alarms', t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-host-diag-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  // 1. Volta shim pointing via tools/user/bins/pdd.json to the running Volta package root -> 0 duplicates.
  const home = join(root, 'home');
  const voltaHome = join(home, '.volta');
  const voltaPkg = join(voltaHome, 'tools/image/packages/@promptdriven/pdd/lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(voltaHome, 'bin'), { recursive: true });
  mkdirSync(join(voltaHome, 'tools/user/bins'), { recursive: true });
  mkdirSync(join(voltaPkg, 'bin'), { recursive: true });
  writeFileSync(join(voltaPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.50', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(voltaPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  writeFileSync(join(voltaHome, 'bin/volta-shim'), '#!/bin/sh\nexit 0\n', { mode: 0o755 });
  symlinkSync('volta-shim', join(voltaHome, 'bin/pdd'));
  writeFileSync(join(voltaHome, 'tools/user/bins/pdd.json'), JSON.stringify({ name: 'pdd', package: '@promptdriven/pdd' }));

  // Also add an extra PATH symlink pointing directly to the same bin/pdd.mjs.
  const aliasBin = join(root, 'alias-bin');
  mkdirSync(aliasBin, { recursive: true });
  symlinkSync(join(voltaPkg, 'bin/pdd.mjs'), join(aliasBin, 'pdd'));

  const voltaDiag = diagnoseHostInstalls({
    packageRoot: voltaPkg,
    currentBin: join(voltaPkg, 'bin/pdd.mjs'),
    cwd: root,
    home,
    env: { HOME: home, VOLTA_HOME: voltaHome, PATH: `${join(voltaHome, 'bin')}:${aliasBin}` },
    systemRoots: [],
    checkLoginShells: false,
  });
  assert.equal(voltaDiag.hasConflict, false, JSON.stringify(voltaDiag, null, 2));
  assert.equal(voltaDiag.installs.length, 1);
  assert.equal(voltaDiag.duplicates.length, 0);
  assert.equal(voltaDiag.current.kind, 'volta');
  assert.equal(voltaDiag.pathSelected?.isCurrent, true);

  // 2. pnpm shell wrapper invoking the running pnpm global bin/pdd.mjs -> 0 duplicates.
  const pnpmHome = join(home, '.local/share/pnpm');
  const pnpmPkg = join(pnpmHome, 'global/5/.pnpm/@promptdriven+pdd@0.1.50/node_modules/@promptdriven/pdd');
  mkdirSync(join(pnpmPkg, 'bin'), { recursive: true });
  writeFileSync(join(pnpmPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.50', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(pnpmPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  writeFileSync(
    join(pnpmHome, 'pdd'),
    '#!/bin/sh\nbasedir=$(dirname "$(echo "$0" | sed -e \'s,\\\\,/,g\')")\nexec node "$basedir/global/5/.pnpm/@promptdriven+pdd@0.1.50/node_modules/@promptdriven/pdd/bin/pdd.mjs" "$@"\n',
    { mode: 0o755 },
  );

  const pnpmDiag = diagnoseHostInstalls({
    packageRoot: pnpmPkg,
    currentBin: join(pnpmPkg, 'bin/pdd.mjs'),
    cwd: root,
    home: join(root, 'pnpm-only-home'),
    env: { HOME: join(root, 'pnpm-only-home'), PNPM_HOME: pnpmHome, PATH: pnpmHome },
    systemRoots: [],
    checkLoginShells: false,
  });
  assert.equal(pnpmDiag.hasConflict, false, JSON.stringify(pnpmDiag, null, 2));
  assert.equal(pnpmDiag.installs.length, 1);
  assert.equal(pnpmDiag.duplicates.length, 0);
  assert.equal(pnpmDiag.current.kind, 'pnpm');
});

test('PATH12: diagnoseHostInstalls discovers Volta, nvm, pnpm, conda/Python, and Homebrew duplicates with exact remediations and respects PDD_PATH_DIAG_DONE', t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-multi-mgr-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home');
  const pkgRoot = resolve(import.meta.dirname, '..');
  const currentBin = join(pkgRoot, 'bin/pdd.mjs');

  // Volta stale copy
  const voltaPkg = join(home, '.volta/tools/image/packages/@promptdriven/pdd/lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(home, '.volta/bin'), { recursive: true });
  mkdirSync(join(home, '.volta/tools/user/bins'), { recursive: true });
  mkdirSync(join(voltaPkg, 'bin'), { recursive: true });
  writeFileSync(join(voltaPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.40', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(voltaPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  writeFileSync(join(home, '.volta/bin/volta-shim'), '#!/bin/sh\nexit 0\n', { mode: 0o755 });
  symlinkSync('volta-shim', join(home, '.volta/bin/pdd'));
  writeFileSync(join(home, '.volta/tools/user/bins/pdd.json'), JSON.stringify({ name: 'pdd', package: '@promptdriven/pdd' }));

  // nvm stale copy
  const nvmPrefix = join(home, '.nvm/versions/node/v20.11.0');
  const nvmPkg = join(nvmPrefix, 'lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(nvmPrefix, 'bin'), { recursive: true });
  mkdirSync(join(nvmPkg, 'bin'), { recursive: true });
  writeFileSync(join(nvmPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.38', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(nvmPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  symlinkSync('../lib/node_modules/@promptdriven/pdd/bin/pdd.mjs', join(nvmPrefix, 'bin/pdd'));

  // conda/Python stale copy
  const condaBin = join(home, 'miniconda3/bin');
  mkdirSync(condaBin, { recursive: true });
  writeFileSync(join(condaBin, 'pdd'), '#!/usr/bin/env python3\nprint("0.0.305")\n', { mode: 0o755 });

  // pnpm stale copy
  const pnpmDir = join(home, '.local/share/pnpm');
  mkdirSync(pnpmDir, { recursive: true });
  writeFileSync(join(pnpmDir, 'pdd'), '#!/bin/sh\necho 0.1.35\n', { mode: 0o755 });

  let spawnCount = 0;
  const diag = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home,
    env: { HOME: home, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: (cmd, args) => {
      spawnCount += 1;
      if (cmd.includes('miniconda3')) return { status: 0, stdout: 'pdd, version 0.0.305\n', stderr: '' };
      if (cmd.includes('pnpm')) return { status: 0, stdout: '0.1.35\n', stderr: '' };
      return { status: 1, stdout: '', stderr: '' };
    },
  });

  assert.equal(diag.hasConflict, true);
  assert.equal(diag.duplicates.length, 4, JSON.stringify(diag.duplicates, null, 2));
  const byKind = new Map(diag.duplicates.map(d => [d.kind, d]));
  assert.equal(byKind.get('volta')?.version, '0.1.40');
  assert.equal(byKind.get('volta')?.remediation, 'volta uninstall @promptdriven/pdd');
  assert.equal(byKind.get('npm-global')?.version, '0.1.38');
  assert.match(byKind.get('npm-global')?.remediation ?? '', /npm uninstall -g @promptdriven\/pdd --prefix/);
  assert.equal(byKind.get('pypi')?.remediation, 'pip uninstall pdd-cli');
  assert.equal(byKind.get('pnpm')?.remediation, 'pnpm remove -g @promptdriven/pdd');
  // Volta & nvm versions came directly from package.json with zero subprocesses!
  assert.equal(spawnCount, 2);

  // Recursion guard PDD_PATH_DIAG_DONE=1 skips all subprocesses and returns quiet warnings.
  let guardedSpawns = 0;
  const guarded = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home,
    env: { HOME: home, PATH: '/usr/bin:/bin', PDD_PATH_DIAG_DONE: '1' },
    systemRoots: [],
    checkLoginShells: true,
    spawnSync: () => { guardedSpawns += 1; return { status: 0, stdout: '', stderr: '' }; },
  });
  assert.equal(guardedSpawns, 0);
  assert.ok(guarded.loginShells.every(s => s.status === 'skipped'));
  assert.deepEqual(formatHostInstallWarnings({ packageRoot: pkgRoot, cwd: root, home, env: { HOME: home, PDD_PATH_DIAG_DONE: '1' } }), []);
  assert.equal(shortenHomePath(join(home, '.volta/bin/pdd'), home), '~/.volta/bin/pdd');
});

test('PATH13: Homebrew Volta (~/.volta/bin/pdd -> Cellar/volta/.../volta-shim), custom ASDF_DATA_DIR, and Homebrew Cellar/node npm-global classify cleanly', t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-brew-volta-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home');

  // 1. Homebrew Volta: ~/.volta/bin/pdd -> <cellar>/volta/2.0.0/bin/volta-shim
  const cellarVoltaBin = join(root, 'opt/homebrew/Cellar/volta/2.0.0/bin');
  const voltaHome = join(home, '.volta');
  const voltaPkg = join(voltaHome, 'tools/image/packages/@promptdriven/pdd/lib/node_modules/@promptdriven/pdd');
  mkdirSync(cellarVoltaBin, { recursive: true });
  mkdirSync(join(voltaHome, 'bin'), { recursive: true });
  mkdirSync(join(voltaHome, 'tools/user/bins'), { recursive: true });
  mkdirSync(join(voltaPkg, 'bin'), { recursive: true });
  writeFileSync(join(cellarVoltaBin, 'volta-shim'), '#!/bin/sh\nexit 0\n', { mode: 0o755 });
  symlinkSync(join(cellarVoltaBin, 'volta-shim'), join(voltaHome, 'bin/pdd'));
  writeFileSync(join(voltaHome, 'tools/user/bins/pdd.json'), JSON.stringify({ name: 'pdd', package: '@promptdriven/pdd' }));
  writeFileSync(join(voltaPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.50', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(voltaPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });

  const brewVoltaDiag = diagnoseHostInstalls({
    packageRoot: voltaPkg,
    currentBin: join(voltaPkg, 'bin/pdd.mjs'),
    cwd: root,
    home,
    env: { HOME: home, PATH: join(voltaHome, 'bin') },
    systemRoots: [],
    checkLoginShells: false,
  });
  assert.equal(brewVoltaDiag.hasConflict, false, JSON.stringify(brewVoltaDiag, null, 2));
  assert.equal(brewVoltaDiag.installs.length, 1);
  assert.equal(brewVoltaDiag.current.kind, 'volta');
  assert.equal(brewVoltaDiag.pathSelected?.isCurrent, true);

  // Fast pathDiagnostic (`pdd --version` / `pdd setup`) must ALSO stay quiet on clean Homebrew Volta!
  assert.deepEqual(pathDiagnostic({ packageRoot: voltaPkg, cwd: root, env: { HOME: home, PATH: join(voltaHome, 'bin') }, mode: 'version' }), []);
  assert.deepEqual(pathDiagnostic({ packageRoot: voltaPkg, cwd: root, env: { HOME: home, PATH: join(voltaHome, 'bin') }, mode: 'setup' }), []);

  // 2. Custom ASDF_DATA_DIR (~/.local/share/asdf) shim targeting current install -> 0 duplicates.
  const asdfDir = join(home, '.local/share/asdf');
  const asdfPkg = join(asdfDir, 'installs/nodejs/22.20.0/lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(asdfDir, 'shims'), { recursive: true });
  mkdirSync(join(asdfPkg, 'bin'), { recursive: true });
  writeFileSync(join(asdfPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.50', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(asdfPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  writeFileSync(join(asdfDir, 'shims/pdd'), '#!/usr/bin/env bash\nexec asdf exec "pdd" "$@"\n', { mode: 0o755 });

  const asdfDiag = diagnoseHostInstalls({
    packageRoot: asdfPkg,
    currentBin: join(asdfPkg, 'bin/pdd.mjs'),
    cwd: root,
    home: join(root, 'asdf-home'),
    env: { HOME: join(root, 'asdf-home'), ASDF_DATA_DIR: asdfDir, PATH: join(asdfDir, 'shims') },
    systemRoots: [],
    checkLoginShells: false,
  });
  assert.equal(asdfDiag.hasConflict, false, JSON.stringify(asdfDiag, null, 2));
  assert.equal(asdfDiag.installs.length, 1);

  // 3. Homebrew Cellar/node/.../node_modules/@promptdriven/pdd classifies as npm-global (NOT brew uninstall pdd!).
  const cellarNodePrefix = join(root, 'opt/homebrew/Cellar/node/22.20.0');
  const cellarNodePkg = join(cellarNodePrefix, 'lib/node_modules/@promptdriven/pdd');
  mkdirSync(join(cellarNodePrefix, 'bin'), { recursive: true });
  mkdirSync(join(cellarNodePkg, 'bin'), { recursive: true });
  writeFileSync(join(cellarNodePkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.45', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(cellarNodePkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  symlinkSync('../lib/node_modules/@promptdriven/pdd/bin/pdd.mjs', join(cellarNodePrefix, 'bin/pdd'));

  const cellarNodeDiag = diagnoseHostInstalls({
    packageRoot: voltaPkg,
    currentBin: join(voltaPkg, 'bin/pdd.mjs'),
    cwd: root,
    home: join(root, 'cellar-node-home'),
    env: { HOME: join(root, 'cellar-node-home'), PATH: join(cellarNodePrefix, 'bin') },
    systemRoots: [],
    checkLoginShells: false,
  });
  assert.equal(cellarNodeDiag.duplicates.length, 1);
  assert.equal(cellarNodeDiag.duplicates[0].kind, 'npm-global');
  assert.match(cellarNodeDiag.duplicates[0].remediation ?? '', /npm uninstall -g @promptdriven\/pdd --prefix/);
});

test('PATH14: noisy .zprofile stdout and alias pdd=... never create phantom rm -f duplicates, and win32 %dp0% wrappers deduplicate cleanly', t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-login-noise-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const pkgRoot = resolve(import.meta.dirname, '..');
  const currentBin = join(pkgRoot, 'bin/pdd.mjs');

  // 1. Login shell exits 1 while printing a path-like MOTD / conda banner, and another returns an alias -> zero phantom duplicates.
  const noisyDiag = diagnoseHostInstalls(
    {
      packageRoot: pkgRoot,
      currentBin,
      cwd: root,
      home: join(root, 'empty-home'),
      env: { HOME: join(root, 'empty-home'), PATH: '/usr/bin:/bin' },
      systemRoots: [],
      loginShells: ['/bin/zsh', '/bin/bash'],
    },
    {
      spawnSync: cmd => {
        if (cmd === '/bin/zsh') return { status: 1, stdout: '/Users/dev/.nvm\n/Users/dev/important-project\n', stderr: '' };
        if (cmd === '/bin/bash') return { status: 0, stdout: '\n__PDD_WHICH__=alias pdd=/usr/local/bin/pdd\n', stderr: '' };
        return { status: 1, stdout: '', stderr: '' };
      },
    },
  );
  assert.equal(noisyDiag.hasConflict, false, JSON.stringify(noisyDiag, null, 2));
  assert.equal(noisyDiag.duplicates.length, 0);
  assert.equal(noisyDiag.shellSplits.length, 0);
  assert.ok(noisyDiag.loginShells.every(s => s.status === 'not-found'));

  // 2. Windows win32 cmd-shim (`%dp0%` wrapper, `;` PATH, quoted PATH entry, case-insensitive dedup).
  const winPrefix = join(root, 'win-npm');
  const winPkg = join(winPrefix, 'node_modules/@promptdriven/pdd');
  mkdirSync(join(winPkg, 'bin'), { recursive: true });
  writeFileSync(join(winPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.1.50', bin: { pdd: 'bin/pdd.mjs' } }));
  writeFileSync(join(winPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  writeFileSync(
    join(winPrefix, 'pdd.cmd'),
    '@ECHO off\r\nSET dp0=%~dp0\r\n"%_prog%" "%dp0%\\node_modules\\@promptdriven\\pdd\\bin\\pdd.mjs" %*\r\n',
    { mode: 0o755 },
  );
  const winDiag = diagnoseHostInstalls(
    {
      packageRoot: winPkg,
      currentBin: join(winPkg, 'bin/pdd.mjs'),
      cwd: root,
      home: join(root, 'win-home'),
      env: { HOME: join(root, 'win-home'), PATH: `"${winPrefix}";C:\\Windows\\System32` },
      systemRoots: [],
    },
    { platform: 'win32' },
  );
  assert.equal(winDiag.hasConflict, false, JSON.stringify(winDiag, null, 2));
  assert.equal(winDiag.installs.length, 1);
  assert.equal(winDiag.duplicates.length, 0);
  assert.equal(winDiag.pathSelected?.isCurrent, true);
  assert.deepEqual(winDiag.loginShells, []);
});

test('PATH15: pathDiagnostic recognizes matching Volta shims and pnpm shell wrappers without false conflict warnings, while still flagging shadowed ones', t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-path-shims-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));

  // 1. Matching Volta shim: <voltaHome>/bin/pdd -> volta-shim while packageRoot lives under <voltaHome>/tools/image/packages/@promptdriven/pdd/...
  const voltaHome = join(root, '.volta');
  const voltaBin = join(voltaHome, 'bin');
  const voltaPkg = join(voltaHome, 'tools/image/packages/@promptdriven/pdd/lib/node_modules/@promptdriven/pdd');
  mkdirSync(voltaBin, { recursive: true });
  mkdirSync(join(voltaPkg, 'bin'), { recursive: true });
  writeFileSync(join(voltaPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version }));
  writeFileSync(join(voltaPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  writeFileSync(join(voltaBin, 'volta-shim'), '#!/bin/sh\nexit 0\n', { mode: 0o755 });
  symlinkSync(join(voltaBin, 'volta-shim'), join(voltaBin, 'pdd'));
  assert.deepEqual(
    pathDiagnostic({ packageRoot: voltaPkg, cwd: root, env: { PATH: `${voltaBin}:/usr/bin:/bin` }, mode: 'version' }),
    [],
    'matching Volta shim must not trigger false PATH conflict',
  );
  // Shadowing from an unrelated Volta home IS still caught.
  const otherVoltaBin = join(root, 'other-volta/bin');
  mkdirSync(otherVoltaBin, { recursive: true });
  writeFileSync(join(otherVoltaBin, 'volta-shim'), '#!/bin/sh\nprintf "0.0.1\\n"\n', { mode: 0o755 });
  symlinkSync(join(otherVoltaBin, 'volta-shim'), join(otherVoltaBin, 'pdd'));
  const voltaShadow = pathDiagnostic({ packageRoot: voltaPkg, cwd: root, env: { PATH: `${otherVoltaBin}:${voltaBin}:/usr/bin:/bin` }, mode: 'version' });
  assert.ok(voltaShadow.some(line => /PATH selects:.*0\.0\.1/.test(line)), voltaShadow.join('\n'));

  // 2. Matching pnpm global shell wrapper: $PNPM_HOME/pdd invokes "$basedir/.../bin/pdd.mjs".
  const pnpmRoot = join(root, 'pnpm');
  const pnpmBin = join(pnpmRoot, 'bin');
  const pnpmPkg = join(pnpmRoot, 'global/5/node_modules/@promptdriven/pdd');
  mkdirSync(pnpmBin, { recursive: true });
  mkdirSync(join(pnpmPkg, 'bin'), { recursive: true });
  writeFileSync(join(pnpmPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version }));
  writeFileSync(join(pnpmPkg, 'bin/pdd.mjs'), '#!/usr/bin/env node\n', { mode: 0o755 });
  writeFileSync(
    join(pnpmBin, 'pdd'),
    '#!/bin/sh\nbasedir=$(dirname "$(echo "$0" | sed -e \'s,\\\\,/,g\')")\nexec node  "$basedir/../global/5/node_modules/@promptdriven/pdd/bin/pdd.mjs" "$@"\n',
    { mode: 0o755 },
  );
  assert.deepEqual(
    pathDiagnostic({ packageRoot: pnpmPkg, cwd: root, env: { PATH: `${pnpmBin}:/usr/bin:/bin` }, mode: 'version' }),
    [],
    'matching pnpm shell wrapper must not trigger false PATH conflict',
  );
  // Wrapper pointing to a DIFFERENT package IS still caught as shadowed.
  const otherPnpmBin = join(root, 'other-pnpm-bin');
  mkdirSync(otherPnpmBin, { recursive: true });
  writeFileSync(
    join(otherPnpmBin, 'pdd'),
    '#!/bin/sh\nprintf "0.0.2\\n"\n',
    { mode: 0o755 },
  );
  const pnpmShadow = pathDiagnostic({ packageRoot: pnpmPkg, cwd: root, env: { PATH: `${otherPnpmBin}:${pnpmBin}:/usr/bin:/bin` }, mode: 'version' });
  assert.ok(pnpmShadow.some(line => /PATH selects:.*0\.0\.2/.test(line)), pnpmShadow.join('\n'));
});

test('PATH16 (#3726 Bug 2): unexposed internal uv/pipx tool venvs are not flagged, while exposed entrypoints via ~/.local/bin, PATH, or login shell are caught', t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-uv-pipx-unexposed-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const home = join(root, 'home');
  const pkgRoot = resolve(import.meta.dirname, '..');
  const currentBin = join(pkgRoot, 'bin/pdd.mjs');

  // Set up internal uv and pipx venv binaries + non-colliding ~/.local/bin/pdd-v1 wrapper (no ~/.local/bin/pdd).
  const uvVenv = join(home, '.local/share/uv/tools/pdd-cli');
  const uvBin = join(uvVenv, 'bin');
  const uvDist = join(uvVenv, 'lib/python3.12/site-packages/pdd_cli-0.0.246.dist-info');
  mkdirSync(uvBin, { recursive: true });
  mkdirSync(uvDist, { recursive: true });
  writeFileSync(join(uvBin, 'pdd'), `#!${join(uvBin, 'python3')}\nfrom pdd.cli import cli\n`, { mode: 0o755 });
  writeFileSync(join(uvDist, 'METADATA'), 'Metadata-Version: 2.3\nName: pdd-cli\nVersion: 0.0.246\n');

  const pipxVenv = join(home, '.local/pipx/venvs/pdd-cli');
  const pipxBin = join(pipxVenv, 'bin');
  const pipxDist = join(pipxVenv, 'lib/python3.11/site-packages/pdd_cli-0.0.240.dist-info');
  mkdirSync(pipxBin, { recursive: true });
  mkdirSync(pipxDist, { recursive: true });
  writeFileSync(join(pipxBin, 'pdd'), `#!${join(pipxBin, 'python3')}\nfrom pdd.cli import cli\n`, { mode: 0o755 });
  writeFileSync(join(pipxDist, 'METADATA'), 'Metadata-Version: 2.3\nName: pdd-cli\nVersion: 0.0.240\n');

  const localBin = join(home, '.local/bin');
  mkdirSync(localBin, { recursive: true });
  writeFileSync(join(localBin, 'pdd-v1'), `#!/bin/sh\nexec "${join(uvBin, 'pdd')}" "$@"\n`, { mode: 0o755 });

  let spawns = 0;
  const unexposed = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home,
    env: { HOME: home, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { spawns += 1; return { status: 0, stdout: 'should not spawn', stderr: '' }; },
  });
  assert.equal(unexposed.hasConflict, false, JSON.stringify(unexposed, null, 2));
  assert.equal(unexposed.duplicates.length, 0);
  assert.equal(unexposed.installs.length, 1);
  assert.equal(spawns, 0);
  assert.deepEqual(
    formatHostInstallWarnings({ packageRoot: pkgRoot, currentBin, cwd: root, home, env: { HOME: home, PATH: '/usr/bin:/bin' }, systemRoots: [], checkLoginShells: false }),
    [],
  );

  // 1. Exposed via ~/.local/bin/pdd symlink to uv venv (even when ~/.local/bin is not in current PATH).
  symlinkSync(join(uvBin, 'pdd'), join(localBin, 'pdd'));
  const uvSymlink = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home,
    env: { HOME: home, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { spawns += 1; return { status: 0, stdout: '', stderr: '' }; },
  });
  assert.equal(uvSymlink.hasConflict, true);
  assert.equal(uvSymlink.duplicates.length, 1);
  assert.equal(uvSymlink.duplicates[0].kind, 'pypi');
  assert.equal(uvSymlink.duplicates[0].version, '0.0.246');
  assert.equal(uvSymlink.duplicates[0].remediation, 'uv tool uninstall pdd-cli');
  assert.equal(spawns, 0);

  // 2. Exposed via non-symlink trampoline script in ~/.local/bin/pdd pointing to uv venv interpreter.
  rmSync(join(localBin, 'pdd'));
  writeFileSync(join(localBin, 'pdd'), `#!${join(uvBin, 'python3')}\nfrom pdd_cli.cli import main\n`, { mode: 0o755 });
  const uvTrampoline = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home,
    env: { HOME: home, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { spawns += 1; return { status: 0, stdout: '', stderr: '' }; },
  });
  assert.equal(uvTrampoline.hasConflict, true);
  assert.equal(uvTrampoline.duplicates.length, 1);
  assert.equal(uvTrampoline.duplicates[0].kind, 'pypi');
  assert.equal(uvTrampoline.duplicates[0].version, '0.0.246');
  assert.equal(uvTrampoline.duplicates[0].remediation, 'uv tool uninstall pdd-cli');
  assert.equal(spawns, 0);

  // 2b. Unquoted long-path '''exec' trampoline (pip/uv format on >127-char POSIX paths without spaces).
  writeFileSync(join(localBin, 'pdd'), `#!/bin/sh\n'''exec' ${join(uvBin, 'python3.13t')} "$0" "$@"\n' '''\n`, { mode: 0o755 });
  const uvUnquotedExec = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home,
    env: { HOME: home, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { spawns += 1; return { status: 0, stdout: '', stderr: '' }; },
  });
  assert.equal(uvUnquotedExec.hasConflict, true);
  assert.equal(uvUnquotedExec.duplicates[0].kind, 'pypi');
  assert.equal(uvUnquotedExec.duplicates[0].version, '0.0.246');
  assert.equal(uvUnquotedExec.duplicates[0].remediation, 'uv tool uninstall pdd-cli');
  assert.equal(spawns, 0);

  // 2c. Double-quoted '''exec' trampoline with spaces and apostrophe in venv path.
  const spacedHome = join(root, "O'Brien Home");
  const spacedUvVenv = join(spacedHome, '.local/share/uv/tools/pdd-cli');
  const spacedUvBin = join(spacedUvVenv, 'bin');
  const spacedUvDist = join(spacedUvVenv, 'lib/python3.12/site-packages/pdd_cli-0.0.249.dist-info');
  const spacedLocalBin = join(spacedHome, '.local/bin');
  mkdirSync(spacedUvBin, { recursive: true });
  mkdirSync(spacedUvDist, { recursive: true });
  mkdirSync(spacedLocalBin, { recursive: true });
  writeFileSync(join(spacedUvDist, 'METADATA'), 'Metadata-Version: 2.3\nName: pdd-cli\nVersion: 0.0.249\n');
  writeFileSync(join(spacedLocalBin, 'pdd'), `#!/bin/sh\n'''exec' "${join(spacedUvBin, 'python3')}" "$0" "$@"\n' '''\n`, { mode: 0o755 });
  const spacedDiag = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home: spacedHome,
    env: { HOME: spacedHome, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { spawns += 1; return { status: 0, stdout: '', stderr: '' }; },
  });
  assert.equal(spacedDiag.hasConflict, true);
  assert.equal(spacedDiag.duplicates.length, 1);
  assert.equal(spacedDiag.duplicates[0].kind, 'pypi');
  assert.equal(spacedDiag.duplicates[0].version, '0.0.249');
  assert.equal(spacedDiag.duplicates[0].remediation, 'uv tool uninstall pdd-cli');
  assert.equal(spawns, 0);

  // 3. Exposed via ~/.local/bin/pdd symlink to pipx venv.
  rmSync(join(localBin, 'pdd'));
  symlinkSync(join(pipxBin, 'pdd'), join(localBin, 'pdd'));
  const pipxSymlink = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home,
    env: { HOME: home, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { spawns += 1; return { status: 0, stdout: '', stderr: '' }; },
  });
  assert.equal(pipxSymlink.hasConflict, true);
  assert.equal(pipxSymlink.duplicates.length, 1);
  assert.equal(pipxSymlink.duplicates[0].kind, 'pypi');
  assert.equal(pipxSymlink.duplicates[0].version, '0.0.240');
  assert.equal(pipxSymlink.duplicates[0].remediation, 'pipx uninstall pdd-cli');
  assert.equal(spawns, 0);

  // 4. Removed ~/.local/bin/pdd, but explicitly placed internal uv bin dir onto PATH -> caught!
  rmSync(join(localBin, 'pdd'));
  const onPathUv = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home,
    env: { HOME: home, PATH: `${uvBin}:/usr/bin:/bin` },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { spawns += 1; return { status: 0, stdout: '', stderr: '' }; },
  });
  assert.equal(onPathUv.hasConflict, true);
  assert.equal(onPathUv.duplicates.length, 1);
  assert.equal(onPathUv.duplicates[0].version, '0.0.246');
  assert.equal(onPathUv.duplicates[0].remediation, 'uv tool uninstall pdd-cli');
  assert.equal(spawns, 0);

  // 5. Exposed via login shell resolution -> caught!
  const loginUv = diagnoseHostInstalls(
    {
      packageRoot: pkgRoot,
      currentBin,
      cwd: root,
      home,
      env: { HOME: home, PATH: '/usr/bin:/bin' },
      systemRoots: [],
      loginShells: ['/bin/zsh'],
    },
    {
      spawnSync: cmd => {
        if (cmd === '/bin/zsh') return { status: 0, stdout: `\n__PDD_WHICH__=${join(uvBin, 'pdd')}\n`, stderr: '' };
        spawns += 1;
        return { status: 1, stdout: '', stderr: '' };
      },
    },
  );
  assert.equal(loginUv.hasConflict, true);
  assert.equal(loginUv.shellSplits.length, 1);
  assert.equal(loginUv.shellSplits[0].version, '0.0.246');
  assert.equal(loginUv.shellSplits[0].remediation, 'uv tool uninstall pdd-cli');
  assert.equal(spawns, 0);
});

test('PATH17 (#3726 Bug 3): pypi version reads dist-info METADATA statically across POSIX, large README, CRLF, and Windows Lib/site-packages, falling back to --version when absent', t => {
  const root = realpathSync(mkdtempSync(join(tmpdir(), 'pdd-pypi-metadata-')));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const pkgRoot = resolve(import.meta.dirname, '..');
  const currentBin = join(pkgRoot, 'bin/pdd.mjs');

  // 1. Conda install with large (>20 KiB) CRLF METADATA whose body contains a decoy Version line.
  const home = join(root, 'home');
  const condaRoot = join(home, 'miniconda3');
  const condaBin = join(condaRoot, 'bin');
  const condaDist = join(condaRoot, 'lib/python3.11/site-packages/pdd_cli-0.0.305.dev214.dist-info');
  mkdirSync(condaBin, { recursive: true });
  mkdirSync(condaDist, { recursive: true });
  writeFileSync(join(condaBin, 'pdd'), '#!/usr/bin/env python3\nfrom pdd_cli.cli import main\n', { mode: 0o755 });
  const bigBody = `# Long README\r\nVersion: 9.9.9\r\n${'x'.repeat(24000)}`;
  writeFileSync(
    join(condaDist, 'METADATA'),
    `Metadata-Version: 2.3\r\nName: pdd-cli\r\nVersion: 0.0.305.dev214\r\nSummary: PDD\r\n\r\n${bigBody}`,
  );

  let spawns = 0;
  const condaDiag = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home,
    env: { HOME: home, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { spawns += 1; return { status: 0, stdout: 'wrong', stderr: '' }; },
  });
  assert.equal(condaDiag.duplicates.length, 1);
  assert.equal(condaDiag.duplicates[0].kind, 'pypi');
  assert.equal(condaDiag.duplicates[0].version, '0.0.305.dev214');
  assert.equal(condaDiag.duplicates[0].versionTimedOut, false);
  assert.equal(spawns, 0);

  // 2. Windows layout (<venv>/Scripts/pdd.exe + <venv>/Lib/site-packages/pdd_cli-*.dist-info/METADATA).
  const winVenv = join(root, 'win-home/.venv');
  const winScripts = join(winVenv, 'Scripts');
  const winDist = join(winVenv, 'Lib/site-packages/pdd_cli-0.0.250.dist-info');
  mkdirSync(winScripts, { recursive: true });
  mkdirSync(winDist, { recursive: true });
  writeFileSync(join(winScripts, 'pdd.exe'), 'MZ-fake-exe', { mode: 0o755 });
  writeFileSync(join(winDist, 'METADATA'), 'Metadata-Version: 2.1\r\nName: pdd-cli\r\nVersion: 0.0.250\r\n');

  let winSpawns = 0;
  const winDiag = diagnoseHostInstalls(
    {
      packageRoot: pkgRoot,
      currentBin,
      cwd: root,
      home: join(root, 'win-home'),
      env: { HOME: join(root, 'win-home'), PATH: winScripts },
      systemRoots: [],
      checkLoginShells: false,
    },
    {
      platform: 'win32',
      spawnSync: () => { winSpawns += 1; return { status: 0, stdout: 'wrong', stderr: '' }; },
    },
  );
  assert.equal(winDiag.duplicates.length, 1);
  assert.equal(winDiag.duplicates[0].kind, 'pypi');
  assert.equal(winDiag.duplicates[0].version, '0.0.250');
  assert.equal(winSpawns, 0);

  // 3. Header-only guard & fallback: METADATA missing Version header (only decoy Version in body) falls back to --version.
  const fallbackHome = join(root, 'fallback-home');
  const fbConda = join(fallbackHome, 'miniconda3');
  const fbDist = join(fbConda, 'lib/python3.12/site-packages/pdd_cli-0.0.100.dist-info');
  mkdirSync(join(fbConda, 'bin'), { recursive: true });
  mkdirSync(fbDist, { recursive: true });
  writeFileSync(join(fbConda, 'bin/pdd'), '#!/usr/bin/env python3\nprint("0.0.100")\n', { mode: 0o755 });
  writeFileSync(join(fbDist, 'METADATA'), 'Metadata-Version: 2.3\nName: pdd-cli\n\nVersion: 9.9.9\n');

  let fbSpawns = 0;
  const fbDiag = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home: fallbackHome,
    env: { HOME: fallbackHome, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { fbSpawns += 1; return { status: 0, stdout: 'pdd, version 0.0.100\n', stderr: '' }; },
  });
  assert.equal(fbDiag.duplicates.length, 1);
  assert.equal(fbDiag.duplicates[0].version, 'pdd, version 0.0.100');
  assert.equal(fbSpawns, 1);

  // 4. Leading blank line (empty header section) must NOT match body Version and must fall back to --version.
  writeFileSync(join(fbDist, 'METADATA'), '\nVersion: 9.9.9\n');
  let blankSpawns = 0;
  const blankDiag = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home: fallbackHome,
    env: { HOME: fallbackHome, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { blankSpawns += 1; return { status: 0, stdout: 'pdd, version 0.0.101\n', stderr: '' }; },
  });
  assert.equal(blankDiag.duplicates[0].version, 'pdd, version 0.0.101');
  assert.equal(blankSpawns, 1);

  // 5. UTF-8 BOM-prefixed first-line Version header parses statically with 0 spawns.
  writeFileSync(join(fbDist, 'METADATA'), '\uFEFFVersion: 0.0.247\nName: pdd-cli\n');
  let bomSpawns = 0;
  const bomDiag = diagnoseHostInstalls({
    packageRoot: pkgRoot,
    currentBin,
    cwd: root,
    home: fallbackHome,
    env: { HOME: fallbackHome, PATH: '/usr/bin:/bin' },
    systemRoots: [],
    checkLoginShells: false,
    spawnSync: () => { bomSpawns += 1; return { status: 0, stdout: 'wrong\n', stderr: '' }; },
  });
  assert.equal(bomDiag.duplicates[0].version, '0.0.247');
  assert.equal(bomSpawns, 0);
});
