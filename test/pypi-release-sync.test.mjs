import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { chmodSync, cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  checkVersionParity,
  normalizeReleaseTag,
  readPyprojectVersion,
  readPythonInitVersion,
  stagePypiBundle,
  syncPypiVersion,
} from '../scripts/sync-pypi-version.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const syncScript = join(root, 'scripts', 'sync-pypi-version.mjs');
const pythonPkgRoot = join(root, 'python');
const PY_NO_BYTECODE_ENV = { ...process.env, PYTHONDONTWRITEBYTECODE: '1' };

function findPython3() {
  for (const cmd of ['python3', 'python']) {
    const res = spawnSync(cmd, ['-B', '-c', 'import sys; print(sys.executable)'], {
      env: PY_NO_BYTECODE_ENV,
      encoding: 'utf8',
    });
    if (!res.error && res.status === 0 && res.stdout.trim()) return res.stdout.trim();
  }
  return null;
}

test('#3498 package.json, python/pyproject.toml, and python/pdd_cli/__init__.py stay on the exact same version and explicit package layout', () => {
  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  const pyproject = readFileSync(join(root, 'python', 'pyproject.toml'), 'utf8');
  const pyInit = readFileSync(join(root, 'python', 'pdd_cli', '__init__.py'), 'utf8');

  assert.equal(pkg.name, '@promptdriven/pdd');
  assert.equal(pkg.publishConfig?.access, 'public');
  assert.equal(pkg.private, undefined);
  assert.match(pkg.scripts?.version ?? '', /sync-pypi-version\.mjs/);
  assert.match(pyproject, /^requires\s*=\s*\["setuptools>=77",\s*"wheel"\]/m);
  assert.match(pyproject, /^name\s*=\s*"pdd-cli"/m);
  assert.match(pyproject, /^license\s*=\s*"MIT"/m);
  assert.match(pyproject, /^pdd\s*=\s*"pdd_cli\.cli:main"/m);
  assert.match(pyproject, /^\[tool\.setuptools\]\s*\npackages\s*=\s*\["pdd_cli"\]/m);
  assert.doesNotMatch(pyproject, /packages\.find/);

  assert.equal(readPyprojectVersion(pyproject), pkg.version);
  assert.equal(readPythonInitVersion(pyInit), pkg.version);

  const parity = checkVersionParity({ root, tag: `alpha-v${pkg.version}` });
  assert.equal(parity.ok, true, parity.problems.join('\n'));
  assert.equal(parity.version, pkg.version);
});

test('#3498 sync-pypi-version updates pyproject.toml + __init__.py on version bump and enforces release tag parity', t => {
  const sandbox = mkdtempSync(join(tmpdir(), 'pdd-pypi-sync-'));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  mkdirSync(join(sandbox, 'python', 'pdd_cli'), { recursive: true });
  cpSync(join(root, 'python', 'pyproject.toml'), join(sandbox, 'python', 'pyproject.toml'));
  cpSync(join(root, 'python', 'pdd_cli', '__init__.py'), join(sandbox, 'python', 'pdd_cli', '__init__.py'));
  writeFileSync(join(sandbox, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: '0.2.99' }, null, 2) + '\n');

  const drift = spawnSync(process.execPath, [syncScript, '--check', '--root', sandbox], { encoding: 'utf8' });
  assert.equal(drift.status, 1);
  assert.match(drift.stderr, /0\.2\.99/);

  assert.equal(syncPypiVersion({ root: sandbox }), '0.2.99');

  for (const validTag of ['0.2.99', 'v0.2.99', 'alpha-v0.2.99', 'refs/tags/alpha-v0.2.99']) {
    assert.equal(normalizeReleaseTag(validTag), '0.2.99');
    const ok = spawnSync(process.execPath, [syncScript, '--check', '--root', sandbox, '--tag', validTag], { encoding: 'utf8' });
    assert.equal(ok.status, 0, ok.stderr);
  }

  for (const badTag of ['alpha-v0.2.98', 'v9.9.9', 'not-a-semver-tag']) {
    const bad = spawnSync(process.execPath, [syncScript, '--check', '--root', sandbox, '--tag', badTag], { encoding: 'utf8' });
    assert.equal(bad.status, 1);
  }
});

test('#3498 release workflow validates release tags, smoke-tests offline PyPI pdd with empty stderr + lint --local, and sets attestations: false on token fallback', () => {
  const workflow = readFileSync(join(root, '.github', 'workflows', 'release.yml'), 'utf8');
  assert.match(workflow, /^\s*release:\s*\n\s*types:\s*\[published\]/m);
  assert.match(workflow, /^\s*workflow_dispatch:/m);
  assert.match(workflow, /INPUT_TAG#refs\/tags\//);
  assert.match(workflow, /\^\[A-Za-z0-9\._-\]\+\$/);
  assert.match(workflow, /sync-pypi-version\.mjs --check/);
  assert.match(workflow, /sync-pypi-version\.mjs --stage-bundle/);
  assert.match(workflow, /test ! -s "\$smoke_dir\/ver\.err"/);
  assert.match(workflow, /lint --local/);
  assert.match(workflow, /npm publish[\s\S]*--access public --provenance/);
  assert.match(workflow, /environment:\s*pypi-publish/);
  assert.match(workflow, /pypa\/gh-action-pypi-publish@release\/v1/);
  assert.match(workflow, /password:\s*\$\{\{\s*secrets\.PYPI_API_TOKEN\s*\}\}[\s\S]*?attestations:\s*false/);
});

test('#3498 stagePypiBundle + Python pdd_cli wrapper run offline with empty stderr, preserve real PATH shadowing warnings, support Windows pdd.cmd + signals, and write no repo __pycache__', t => {
  const py = findPython3();
  if (!py) {
    t.skip('python3 not available in test environment');
    return;
  }

  const sandbox = mkdtempSync(join(tmpdir(), 'pdd-pypi-cli-'));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const pkgVersion = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8')).version;
  const home = join(sandbox, 'home');
  const stateDir = join(sandbox, 'state');
  const cacheDir = join(sandbox, 'cache');
  const nodeOnlyBinDir = join(sandbox, 'node-bin');
  mkdirSync(home, { recursive: true });
  mkdirSync(stateDir, { recursive: true });
  mkdirSync(nodeOnlyBinDir, { recursive: true });
  symlinkSync(process.execPath, join(nodeOnlyBinDir, 'node'));
  for (const sysTool of ['/usr/bin/which', '/bin/which', '/usr/bin/git']) {
    const toolName = sysTool.split('/').at(-1);
    if (existsSync(sysTool) && !existsSync(join(nodeOnlyBinDir, toolName))) {
      symlinkSync(sysTool, join(nodeOnlyBinDir, toolName));
    }
  }

  // 1. Stage the real bundled @promptdriven/pdd CLI into an isolated copy of python/ via stagePypiBundle (never touching repo working tree).
  const isolatedPyPkg = join(sandbox, 'isolated-python');
  cpSync(pythonPkgRoot, isolatedPyPkg, { recursive: true });
  const stagedBundleDir = stagePypiBundle({
    root,
    bundleDir: join(isolatedPyPkg, 'pdd_cli', '_bundled'),
  });
  assert.equal(existsSync(join(stagedBundleDir, 'bin', 'pdd.mjs')), true);
  assert.equal(existsSync(join(root, 'python', 'pdd_cli', '_bundled')), false, 'repo working tree stays clean');

  const pyBinDir = join(sandbox, 'venv', 'bin');
  mkdirSync(pyBinDir, { recursive: true });
  writeFileSync(join(sandbox, 'venv', 'pyvenv.cfg'), 'home = /usr/bin\n');
  const siblingTool = join(pyBinDir, 'venv-helper');
  writeFileSync(siblingTool, '#!/bin/sh\necho ok\n', { mode: 0o755 });

  const pyWrapperBin = join(pyBinDir, 'pdd');
  writeFileSync(
    pyWrapperBin,
    `#!${py}\nimport sys\nsys.path.insert(0, ${JSON.stringify(isolatedPyPkg)})\nfrom pdd_cli.cli import main\nraise SystemExit(main())\n`,
  );
  chmodSync(pyWrapperBin, 0o755);

  // 2. Running real bin/pdd.mjs --version via both `<venv>/bin/pdd` and `python -m pdd_cli` with `pyBinDir` on PATH emits empty stderr (zero false PATH conflict warnings!).
  const baseOfflineEnv = {
    ...PY_NO_BYTECODE_ENV,
    HOME: home,
    PDD_STATE_DIR: stateDir,
    PDD_CLI_CACHE_DIR: cacheDir,
    PDD_CLI_OFFLINE: '1',
    PDD_CLI_IGNORE_CHECKOUT: '1',
    PDD_CLI_NO_EXEC: '1',
    PDD_NO_UPDATE_CHECK: '1',
    PYTHONPATH: isolatedPyPkg,
    PATH: [pyBinDir, nodeOnlyBinDir].join(delimiter),
  };

  const wrapperVer = spawnSync(pyWrapperBin, ['--version'], { cwd: sandbox, env: baseOfflineEnv, encoding: 'utf8' });
  assert.equal(wrapperVer.status, 0, wrapperVer.stderr);
  assert.equal(wrapperVer.stdout, `${pkgVersion}\n`);
  assert.equal(wrapperVer.stderr, '');

  const moduleVer = spawnSync(py, ['-B', '-m', 'pdd_cli', '--version'], { cwd: sandbox, env: baseOfflineEnv, encoding: 'utf8' });
  assert.equal(moduleVer.status, 0, moduleVer.stderr);
  assert.equal(moduleVer.stdout, `${pkgVersion}\n`);
  assert.equal(moduleVer.stderr, '');

  // 3. Offline `pdd lint --local` on a git-initialized harbor fixture succeeds with empty stderr.
  const harborDir = join(sandbox, 'harbor');
  cpSync(join(root, 'test', 'fixtures', 'harbor'), harborDir, { recursive: true });
  execFileSync('git', ['-C', harborDir, 'init', '-q']);
  const lintRun = spawnSync(pyWrapperBin, ['lint', '--local'], { cwd: harborDir, env: baseOfflineEnv, encoding: 'utf8' });
  assert.equal(lintRun.status, 0, lintRun.stderr);
  assert.equal(lintRun.stderr, '');
  assert.match(lintRun.stdout, /0 warnings\./);

  // 4. Real PATH shadowing ahead of `pyBinDir` is NOT hidden: stale `/fake-old-bin/pdd` ahead of `pyBinDir` still triggers the shadowed warning!
  const fakeOldBinDir = join(sandbox, 'fake-old-bin');
  mkdirSync(fakeOldBinDir, { recursive: true });
  const fakeOldPdd = join(fakeOldBinDir, 'pdd');
  writeFileSync(fakeOldPdd, `#!${process.execPath}\nconsole.log('0.0.242');\n`, { mode: 0o755 });

  const shadowedEnv = {
    ...baseOfflineEnv,
    PATH: [fakeOldBinDir, pyBinDir, nodeOnlyBinDir].join(delimiter),
  };
  const shadowedMod = spawnSync(py, ['-B', '-m', 'pdd_cli', '--version'], { cwd: sandbox, env: shadowedEnv, encoding: 'utf8' });
  assert.equal(shadowedMod.status, 0);
  assert.equal(shadowedMod.stdout, `${pkgVersion}\n`);
  assert.match(shadowedMod.stderr, /PATH selects: .*fake-old-bin\/pdd \(0\.0\.242\)/);

  const shadowedWrap = spawnSync(pyWrapperBin, ['--version'], { cwd: sandbox, env: shadowedEnv, encoding: 'utf8' });
  assert.equal(shadowedWrap.status, 0);
  assert.equal(shadowedWrap.stdout, `${pkgVersion}\n`);
  assert.match(shadowedWrap.stderr, /PATH selects: .*fake-old-bin\/pdd \(0\.0\.242\)/);

  // 5. Unbundled installed PATH resolution + mirrored sibling binaries + fresh-machine npm cache fallback:
  const unbundledPyDir = join(sandbox, 'unbundled-bin');
  const npmPrefix = join(sandbox, 'npm-global');
  const npmBinDir = join(npmPrefix, 'bin');
  const fakeJsPkg = join(npmPrefix, 'lib', 'node_modules', '@promptdriven', 'pdd');
  mkdirSync(unbundledPyDir, { recursive: true });
  mkdirSync(npmBinDir, { recursive: true });
  mkdirSync(join(fakeJsPkg, 'bin'), { recursive: true });
  writeFileSync(join(unbundledPyDir, 'sibling-tool'), '#!/bin/sh\nexit 0\n', { mode: 0o755 });

  const unbundledWrapper = join(unbundledPyDir, 'pdd');
  writeFileSync(
    unbundledWrapper,
    `#!${py}\nimport sys\nsys.path.insert(0, ${JSON.stringify(pythonPkgRoot)})\nfrom pdd_cli.cli import main\nraise SystemExit(main())\n`,
  );
  chmodSync(unbundledWrapper, 0o755);

  const fakeEntry = join(fakeJsPkg, 'bin', 'pdd.mjs');
  writeFileSync(join(fakeJsPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: pkgVersion }));
  writeFileSync(
    fakeEntry,
    '#!/usr/bin/env node\nimport { existsSync } from "node:fs";\nimport { join } from "node:path";\nconst first = process.env.PATH.split(":")[0];\nconsole.log(JSON.stringify({ delegated: process.argv.slice(2), hasSibling: existsSync(join(first, "sibling-tool")) }));\n',
  );
  chmodSync(fakeEntry, 0o755);
  symlinkSync(fakeEntry, join(npmBinDir, 'pdd'));

  const pathDelegated = spawnSync(unbundledWrapper, ['lint', '--local', '--json'], {
    cwd: sandbox,
    env: {
      ...PY_NO_BYTECODE_ENV,
      HOME: home,
      PDD_CLI_CACHE_DIR: cacheDir,
      PDD_CLI_IGNORE_CHECKOUT: '1',
      PDD_CLI_NO_EXEC: '1',
      PATH: [unbundledPyDir, npmBinDir, nodeOnlyBinDir].join(delimiter),
    },
    encoding: 'utf8',
  });
  assert.equal(pathDelegated.status, 0, pathDelegated.stderr);
  assert.deepEqual(JSON.parse(pathDelegated.stdout.trim()), { delegated: ['lint', '--local', '--json'], hasSibling: true });

  const fakeNpmDir = join(sandbox, 'fake-npm-bin');
  const freshCache = join(sandbox, 'fresh-cache');
  mkdirSync(fakeNpmDir, { recursive: true });
  const fakeNpm = join(fakeNpmDir, 'npm');
  writeFileSync(
    fakeNpm,
    [
      `#!${process.execPath}`,
      "import { chmodSync, mkdirSync, writeFileSync } from 'node:fs';",
      "import { join } from 'node:path';",
      'const args = process.argv.slice(2);',
      'const prefix = args[args.indexOf("--prefix") + 1];',
      "console.log('noisy npm install stdout');",
      "const pkgDir = join(prefix, 'node_modules', '@promptdriven', 'pdd');",
      "mkdirSync(join(pkgDir, 'bin'), { recursive: true });",
      `writeFileSync(join(pkgDir, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: ${JSON.stringify(pkgVersion)} }));`,
      "const entry = join(pkgDir, 'bin', 'pdd.mjs');",
      `writeFileSync(entry, '#!/usr/bin/env node\\nconsole.log(${JSON.stringify(pkgVersion)});\\n');`,
      'chmodSync(entry, 0o755);',
    ].join('\n') + '\n',
  );
  chmodSync(fakeNpm, 0o755);

  const cachedRun = spawnSync(unbundledWrapper, ['--version'], {
    cwd: sandbox,
    env: {
      ...PY_NO_BYTECODE_ENV,
      HOME: home,
      PDD_CLI_CACHE_DIR: freshCache,
      PDD_CLI_IGNORE_CHECKOUT: '1',
      PDD_CLI_NO_EXEC: '1',
      PATH: [unbundledPyDir, fakeNpmDir, nodeOnlyBinDir].join(delimiter),
    },
    encoding: 'utf8',
  });
  assert.equal(cachedRun.status, 0, cachedRun.stderr);
  assert.equal(cachedRun.stdout, `${pkgVersion}\n`);

  // 6. Windows pdd.cmd fallback, argv0 forwarding, KeyboardInterrupt (130), signal exit code (128+sig), and missing Node (127):
  const winNpmBin = join(sandbox, 'win-npm');
  const winEntry = join(winNpmBin, 'node_modules', '@promptdriven', 'pdd', 'bin', 'pdd.mjs');
  mkdirSync(dirname(winEntry), { recursive: true });
  writeFileSync(join(winNpmBin, 'pdd.cmd'), '@ECHO off\r\n');
  writeFileSync(join(winNpmBin, 'node_modules', '@promptdriven', 'pdd', 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: pkgVersion }));
  writeFileSync(winEntry, '#!/usr/bin/env node\n');

  const unitCheck = spawnSync(
    py,
    [
      '-B',
      '-c',
      [
        'import os, subprocess, unittest.mock as mock',
        'from pathlib import Path',
        'from pdd_cli import __version__, cli',
        `win_dir = ${JSON.stringify(winNpmBin)}`,
        `expected = Path(${JSON.stringify(winEntry)}).resolve()`,
        'found = cli._find_installed_on_path(__version__, {"PATH": win_dir}, None, is_windows=True)',
        'assert found == expected, f"expected {expected}, got {found}"',
        'with mock.patch.object(subprocess, "run", side_effect=KeyboardInterrupt):',
        '    assert cli._run_interruptible(["true"], {}) == 130',
        'class NegProc: returncode = -15',
        'with mock.patch.object(subprocess, "run", return_value=NegProc()):',
        '    assert cli._run_interruptible(["true"], {}) == 143',
      ].join('\n'),
    ],
    {
      cwd: sandbox,
      env: { ...PY_NO_BYTECODE_ENV, PYTHONPATH: pythonPkgRoot },
      encoding: 'utf8',
    },
  );
  assert.equal(unitCheck.status, 0, unitCheck.stderr);

  const noNode = spawnSync(unbundledWrapper, ['--version'], {
    cwd: sandbox,
    env: {
      ...PY_NO_BYTECODE_ENV,
      HOME: home,
      PDD_CLI_CACHE_DIR: cacheDir,
      PDD_CLI_IGNORE_CHECKOUT: '1',
      PDD_CLI_NO_EXEC: '1',
      PATH: unbundledPyDir,
    },
    encoding: 'utf8',
  });
  assert.equal(noNode.status, 127);
  assert.match(noNode.stderr, /Node\.js >=22\.16\.0/);

  assert.equal(existsSync(join(root, 'python', 'pdd_cli', '__pycache__')), false, 'no __pycache__ written to repo working tree');
});
