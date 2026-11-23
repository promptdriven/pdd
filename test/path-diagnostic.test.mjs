import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { cpSync, mkdtempSync, mkdirSync, readFileSync, rmSync, symlinkSync, writeFileSync, realpathSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';

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

test('PATH11: pathDiagnostic recognizes matching Volta shims and pnpm shell wrappers without false conflict warnings, while still flagging shadowed ones', async t => {
  const { pathDiagnostic } = await import('../src/path-diagnostic.mjs');
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
