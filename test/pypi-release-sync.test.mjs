import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { chmodSync, cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, realpathSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  checkVersionParity,
  normalizeReleaseTag,
  readPyprojectVersion,
  readPythonInitVersion,
  resolveProductionDependencies,
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
  assert.match(pyproject, /^pdd-codex\s*=\s*"pdd_cli\.cli:main_codex"/m);
  assert.match(pyproject, /^pdd-claude\s*=\s*"pdd_cli\.cli:main_claude"/m);
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
  const mkdirIdx = workflow.indexOf('mkdir -p') >= 0 ? workflow.search(/mkdir -p [^\n]*"\$smoke_dir\/npm-dist"/) : -1;
  const npmPackIdx = workflow.indexOf('npm pack --ignore-scripts --pack-destination "$smoke_dir/npm-dist"');
  assert.equal(mkdirIdx >= 0 && mkdirIdx < npmPackIdx, true, 'verify-release creates $smoke_dir/npm-dist before npm pack --pack-destination');
  assert.match(workflow, /test ! -s "\$smoke_dir\/ver\.err"/);
  assert.match(workflow, /pdd-codex" --pdd-help/);
  assert.match(workflow, /pdd-claude" --pdd-help/);
  assert.match(workflow, /lint --local/);
  assert.match(workflow, /npm publish[\s\S]*--access public --provenance/);
  assert.match(workflow, /environment:\s*pypi-publish/);
  assert.match(workflow, /npm ci --ignore-scripts/);
  assert.doesNotMatch(workflow, /ci-install\.mjs/);
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
  assert.equal(existsSync(join(stagedBundleDir, 'bin', 'pdd-codex.mjs')), true);
  assert.equal(existsSync(join(stagedBundleDir, 'bin', 'pdd-claude.mjs')), true);
  assert.equal(existsSync(join(stagedBundleDir, 'prompts', 'cli')), false, 'prompts/cli/ must not be staged in PyPI _bundled');
  assert.equal(existsSync(join(root, 'python', 'pdd_cli', '_bundled')), false, 'repo working tree stays clean');

  // 2. Create a real `python -m venv --without-pip` with a site-packages module (`demo_mod.py`) to verify:
  //    (a) `<venv>/bin/pdd --version` and `<venv>/bin/python -m pdd_cli --version` run offline with empty stderr, and
  //    (b) invoking `python` via the shimmed child PATH preserves `sys.prefix == realpath(venv)` and imports `demo_mod`!
  const realVenv = join(sandbox, 'real-venv');
  execFileSync(py, ['-B', '-m', 'venv', '--without-pip', realVenv], { env: PY_NO_BYTECODE_ENV });
  const venvPy = join(realVenv, 'bin', 'python');
  const sitePackagesDir = execFileSync(
    venvPy,
    ['-B', '-c', 'import sysconfig; print(sysconfig.get_path("purelib"))'],
    { env: PY_NO_BYTECODE_ENV, encoding: 'utf8' },
  ).trim();
  mkdirSync(sitePackagesDir, { recursive: true });
  writeFileSync(join(sitePackagesDir, 'demo_mod.py'), 'VALUE = 42\n');

  const pyBinDir = join(realVenv, 'bin');
  const pyWrapperBin = join(pyBinDir, 'pdd');
  writeFileSync(
    pyWrapperBin,
    `#!${venvPy}\nimport sys\nsys.path.insert(0, ${JSON.stringify(isolatedPyPkg)})\nfrom pdd_cli.cli import main\nraise SystemExit(main())\n`,
  );
  chmodSync(pyWrapperBin, 0o755);

  const pyCodexBin = join(pyBinDir, 'pdd-codex');
  writeFileSync(
    pyCodexBin,
    `#!${venvPy}\nimport sys\nsys.path.insert(0, ${JSON.stringify(isolatedPyPkg)})\nfrom pdd_cli.cli import main_codex\nraise SystemExit(main_codex())\n`,
  );
  chmodSync(pyCodexBin, 0o755);

  const pyClaudeBin = join(pyBinDir, 'pdd-claude');
  writeFileSync(
    pyClaudeBin,
    `#!${venvPy}\nimport sys\nsys.path.insert(0, ${JSON.stringify(isolatedPyPkg)})\nfrom pdd_cli.cli import main_claude\nraise SystemExit(main_claude())\n`,
  );
  chmodSync(pyClaudeBin, 0o755);

  writeFileSync(
    join(nodeOnlyBinDir, 'codex'),
    `#!${process.execPath}\nconsole.log(JSON.stringify({ bin: 'fake-codex', argv: process.argv.slice(2) }));\n`,
    { mode: 0o755 },
  );
  writeFileSync(
    join(nodeOnlyBinDir, 'claude'),
    `#!${process.execPath}\nconsole.log(JSON.stringify({ bin: 'fake-claude', argv: process.argv.slice(2) }));\n`,
    { mode: 0o755 },
  );

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

  const moduleVer = spawnSync(venvPy, ['-B', '-m', 'pdd_cli', '--version'], { cwd: sandbox, env: baseOfflineEnv, encoding: 'utf8' });
  assert.equal(moduleVer.status, 0, moduleVer.stderr);
  assert.equal(moduleVer.stdout, `${pkgVersion}\n`);
  assert.equal(moduleVer.stderr, '');

  const codexHelp = spawnSync(pyCodexBin, ['--pdd-help'], { cwd: sandbox, env: baseOfflineEnv, encoding: 'utf8' });
  assert.equal(codexHelp.status, 0, codexHelp.stderr);
  assert.match(codexHelp.stdout, /pdd-codex/);
  assert.equal(codexHelp.stderr, '');

  const claudeHelp = spawnSync(pyClaudeBin, ['--pdd-help'], { cwd: sandbox, env: baseOfflineEnv, encoding: 'utf8' });
  assert.equal(claudeHelp.status, 0, claudeHelp.stderr);
  assert.match(claudeHelp.stdout, /pdd-claude/);
  assert.equal(claudeHelp.stderr, '');

  const codexVer = spawnSync(pyCodexBin, ['--version'], { cwd: sandbox, env: baseOfflineEnv, encoding: 'utf8' });
  assert.equal(codexVer.status, 0, codexVer.stderr);
  assert.deepEqual(JSON.parse(codexVer.stdout.trim()), { bin: 'fake-codex', argv: ['--version'] });
  assert.equal(codexVer.stderr, '');

  const claudeVer = spawnSync(pyClaudeBin, ['--version'], { cwd: sandbox, env: baseOfflineEnv, encoding: 'utf8' });
  assert.equal(claudeVer.status, 0, claudeVer.stderr);
  assert.deepEqual(JSON.parse(claudeVer.stdout.trim()), { bin: 'fake-claude', argv: ['--version'] });
  assert.equal(claudeVer.stderr, '');

  const entryCheck = spawnSync(
    venvPy,
    [
      '-B',
      '-c',
      [
        'import os',
        'from pathlib import Path',
        'from pdd_cli import __version__, cli',
        'codex_entry, codex_err = cli.resolve_cli_entry(__version__, os.environ, command="pdd-codex")',
        `assert codex_entry == Path(${JSON.stringify(join(stagedBundleDir, 'bin', 'pdd-codex.mjs'))}).resolve(), f"{codex_entry} ({codex_err})"`,
        'claude_entry, claude_err = cli.resolve_cli_entry(__version__, os.environ, command="pdd-claude")',
        `assert claude_entry == Path(${JSON.stringify(join(stagedBundleDir, 'bin', 'pdd-claude.mjs'))}).resolve(), f"{claude_entry} ({claude_err})"`,
      ].join('\n'),
    ],
    { cwd: sandbox, env: baseOfflineEnv, encoding: 'utf8' },
  );
  assert.equal(entryCheck.status, 0, entryCheck.stderr);

  const shimmedPathOut = spawnSync(
    venvPy,
    [
      '-B',
      '-c',
      [
        'import os',
        'from pathlib import Path',
        'from pdd_cli import cli',
        `entry = Path(${JSON.stringify(join(stagedBundleDir, 'bin', 'pdd.mjs'))})`,
        `child_env = cli._prepare_child_env(entry, os.environ, 0, argv0=${JSON.stringify(pyWrapperBin)})`,
        'print(child_env["PATH"])',
      ].join('\n'),
    ],
    { cwd: sandbox, env: baseOfflineEnv, encoding: 'utf8' },
  );
  assert.equal(shimmedPathOut.status, 0, shimmedPathOut.stderr);
  const shimmedPath = shimmedPathOut.stdout.trim();
  const venvCheck = spawnSync(
    'python',
    ['-B', '-c', 'import os, sys, demo_mod; assert demo_mod.VALUE == 42; print(os.path.realpath(sys.prefix))'],
    {
      cwd: sandbox,
      env: { ...PY_NO_BYTECODE_ENV, PATH: [shimmedPath, '/bin', '/usr/bin'].join(delimiter) },
      encoding: 'utf8',
    },
  );
  assert.equal(venvCheck.status, 0, venvCheck.stderr);
  assert.equal(venvCheck.stdout.trim(), realpathSync(realVenv));

  // 3. Offline `pdd lint --local` on a git-initialized harbor fixture succeeds with empty stderr.
  const harborDir = join(sandbox, 'harbor');
  cpSync(join(root, 'test', 'fixtures', 'harbor'), harborDir, { recursive: true });
  execFileSync('git', ['-C', harborDir, 'init', '-q']);
  const lintRun = spawnSync(pyWrapperBin, ['lint', '--local'], { cwd: harborDir, env: baseOfflineEnv, encoding: 'utf8' });
  assert.equal(lintRun.status, 0, lintRun.stderr);
  assert.equal(lintRun.stderr, '');
  assert.match(lintRun.stdout, /0 warnings\./);

  // 4. Real PATH shadowing ahead of `pyBinDir` is NOT hidden — BOTH for a foreign `pdd` binary AND for a competing stale `pdd_cli` install in another prefix (e.g. pipx)!
  const fakeOldBinDir = join(sandbox, 'fake-old-bin');
  mkdirSync(fakeOldBinDir, { recursive: true });
  writeFileSync(join(fakeOldBinDir, 'pdd'), `#!${process.execPath}\nconsole.log('0.0.242');\n`, { mode: 0o755 });

  const shadowedEnv = {
    ...baseOfflineEnv,
    PATH: [fakeOldBinDir, pyBinDir, nodeOnlyBinDir].join(delimiter),
  };
  const shadowedMod = spawnSync(venvPy, ['-B', '-m', 'pdd_cli', '--version'], { cwd: sandbox, env: shadowedEnv, encoding: 'utf8' });
  assert.equal(shadowedMod.status, 0);
  assert.equal(shadowedMod.stdout, `${pkgVersion}\n`);
  assert.match(shadowedMod.stderr, /PATH selects: .*fake-old-bin\/pdd \(0\.0\.242\)/);

  const shadowedWrap = spawnSync(pyWrapperBin, ['--version'], { cwd: sandbox, env: shadowedEnv, encoding: 'utf8' });
  assert.equal(shadowedWrap.status, 0);
  assert.equal(shadowedWrap.stdout, `${pkgVersion}\n`);
  assert.match(shadowedWrap.stderr, /PATH selects: .*fake-old-bin\/pdd \(0\.0\.242\)/);

  const stalePipxVenv = join(sandbox, 'stale-pipx-venv');
  execFileSync(py, ['-B', '-m', 'venv', '--without-pip', stalePipxVenv], { env: PY_NO_BYTECODE_ENV });
  const stalePipxBin = join(sandbox, 'stale-pipx-bin');
  mkdirSync(stalePipxBin, { recursive: true });
  writeFileSync(
    join(stalePipxBin, 'pdd'),
    `#!${join(stalePipxVenv, 'bin', 'python')}\n# stale pdd_cli console_script wrapper\nprint("0.1.10")\n`,
    { mode: 0o755 },
  );
  const stalePipxEnv = {
    ...baseOfflineEnv,
    PATH: [stalePipxBin, pyBinDir, nodeOnlyBinDir].join(delimiter),
  };
  const staleWrap = spawnSync(pyWrapperBin, ['--version'], { cwd: sandbox, env: stalePipxEnv, encoding: 'utf8' });
  assert.equal(staleWrap.status, 0);
  assert.equal(staleWrap.stdout, `${pkgVersion}\n`);
  assert.match(staleWrap.stderr, /PATH selects: .*stale-pipx-bin\/pdd \(0\.1\.10\)/);

  const staleMod = spawnSync(venvPy, ['-B', '-m', 'pdd_cli', '--version'], { cwd: sandbox, env: stalePipxEnv, encoding: 'utf8' });
  assert.equal(staleMod.status, 0);
  assert.equal(staleMod.stdout, `${pkgVersion}\n`);
  assert.match(staleMod.stderr, /PATH selects: .*stale-pipx-bin\/pdd \(0\.1\.10\)/);

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
        `assert cli._real_or_none(${JSON.stringify(join(sandbox, 'definitely-missing-path'))}) is None`,
        // Bare argv0="pdd" resolves via PATH (shutil.which) rather than cwd, skipping self-wrapper on PATH:
        `cwd_decoy = Path(${JSON.stringify(join(sandbox, 'pdd'))})`,
        'cwd_decoy.mkdir(exist_ok=True)',
        `bare_env = {"PATH": os.pathsep.join([${JSON.stringify(unbundledPyDir)}, ${JSON.stringify(npmBinDir)}]), "PDD_CLI_IGNORE_CHECKOUT": "1", "PDD_CLI_OFFLINE": "1", "PDD_CLI_CACHE_DIR": ${JSON.stringify(cacheDir)}}`,
        'resolved_entry, err = cli.resolve_cli_entry(__version__, bare_env, argv0="pdd")',
        `assert resolved_entry == Path(${JSON.stringify(fakeEntry)}).resolve(), f"got {resolved_entry} ({err})"`,
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

test('stagePypiBundle stages full resolved production npm dependency closure (scoped, hoisted, nested, cyclic, optional) and excludes devDependencies', t => {
  const sandbox = mkdtempSync(join(tmpdir(), 'pdd-pypi-closure-'));
  t.after(() => rmSync(sandbox, { recursive: true, force: true }));

  const writePkg = (relDir, manifest, indexSource) => {
    const abs = join(sandbox, relDir);
    mkdirSync(abs, { recursive: true });
    writeFileSync(join(abs, 'package.json'), `${JSON.stringify(manifest, null, 2)}\n`);
    if (indexSource !== undefined) writeFileSync(join(abs, 'index.mjs'), indexSource);
  };

  mkdirSync(join(sandbox, 'bin'), { recursive: true });
  mkdirSync(join(sandbox, 'python', 'pdd_cli'), { recursive: true });
  writeFileSync(
    join(sandbox, 'package.json'),
    `${JSON.stringify({
      name: '@promptdriven/pdd',
      version: '0.9.1',
      type: 'module',
      bin: {
        pdd: 'bin/pdd.mjs',
        'pdd-codex': 'bin/pdd-codex.mjs',
        'pdd-claude': 'bin/pdd-claude.mjs',
      },
      files: ['bin/'],
      dependencies: {
        '@scope/direct-dep': '1.0.0',
        'cycle-a': '1.0.0',
      },
      optionalDependencies: {
        'opt-present': '1.0.0',
        'opt-missing': '1.0.0',
      },
      devDependencies: {
        'dev-only-pkg': '1.0.0',
      },
    }, null, 2)}\n`,
  );
  writeFileSync(
    join(sandbox, 'bin', 'pdd.mjs'),
    [
      '#!/usr/bin/env node',
      'import { directValue } from "@scope/direct-dep";',
      'import { cycleA } from "cycle-a";',
      'import { optPresent } from "opt-present";',
      'if (process.argv[2] === "--version") { console.log("0.9.1"); process.exit(0); }',
      'console.log(JSON.stringify({ directValue, cycleA, optPresent }));',
    ].join('\n') + '\n',
    { mode: 0o755 },
  );
  writeFileSync(join(sandbox, 'bin', 'pdd-codex.mjs'), '#!/usr/bin/env node\nconsole.log("codex");\n', { mode: 0o644 });
  writeFileSync(join(sandbox, 'bin', 'pdd-claude.mjs'), '#!/usr/bin/env node\nconsole.log("claude");\n', { mode: 0o644 });
  writeFileSync(
    join(sandbox, 'python', 'pyproject.toml'),
    '[project]\nname = "pdd-cli"\nversion = "0.9.1"\n',
  );
  writeFileSync(join(sandbox, 'python', 'pdd_cli', '__init__.py'), '__version__ = "0.9.1"\n');

  writePkg(
    'node_modules/@scope/direct-dep',
    { name: '@scope/direct-dep', version: '1.0.0', type: 'module', main: 'index.mjs', dependencies: { 'hoisted-trans': '1.0.0', 'nested-trans': '1.0.0' } },
    'import { hoisted } from "hoisted-trans";\nimport { nested } from "nested-trans";\nexport const directValue = `${hoisted}+${nested}`;\n',
  );
  writePkg(
    'node_modules/hoisted-trans',
    { name: 'hoisted-trans', version: '1.0.0', type: 'module', main: 'index.mjs' },
    'export const hoisted = "hoisted-ok";\n',
  );
  writePkg(
    'node_modules/@scope/direct-dep/node_modules/nested-trans',
    { name: 'nested-trans', version: '1.0.0', type: 'module', main: 'index.mjs', dependencies: { '@scope/deep-trans': '1.0.0' } },
    'import { deep } from "@scope/deep-trans";\nexport const nested = `nested(${deep})`;\n',
  );
  writePkg(
    'node_modules/@scope/deep-trans',
    { name: '@scope/deep-trans', version: '1.0.0', type: 'module', main: 'index.mjs' },
    'export const deep = "deep-ok";\n',
  );
  writePkg(
    'node_modules/cycle-a',
    { name: 'cycle-a', version: '1.0.0', type: 'module', main: 'index.mjs', dependencies: { 'cycle-b': '1.0.0' } },
    'import { cycleB } from "cycle-b";\nexport const cycleA = `a->${cycleB}`;\n',
  );
  writePkg(
    'node_modules/cycle-b',
    { name: 'cycle-b', version: '1.0.0', type: 'module', main: 'index.mjs', dependencies: { 'cycle-a': '1.0.0' } },
    'export const cycleB = "b-ok";\n',
  );
  writePkg(
    'node_modules/opt-present',
    { name: 'opt-present', version: '1.0.0', type: 'module', main: 'index.mjs' },
    'export const optPresent = "opt-ok";\n',
  );
  writePkg(
    'node_modules/dev-only-pkg',
    { name: 'dev-only-pkg', version: '1.0.0', type: 'module', main: 'index.mjs' },
    'export const devOnly = true;\n',
  );

  const resolved = resolveProductionDependencies(sandbox).map(item => item.relPath);
  assert.deepEqual(resolved, [
    'node_modules/@scope/deep-trans',
    'node_modules/@scope/direct-dep',
    'node_modules/@scope/direct-dep/node_modules/nested-trans',
    'node_modules/cycle-a',
    'node_modules/cycle-b',
    'node_modules/hoisted-trans',
    'node_modules/opt-present',
  ]);

  const outBundle = join(sandbox, 'staged-bundle');
  stagePypiBundle({ root: sandbox, bundleDir: outBundle });
  assert.equal(existsSync(join(outBundle, 'node_modules', 'dev-only-pkg')), false, 'devDependencies must not be staged');
  assert.equal(existsSync(join(outBundle, 'node_modules', '@scope', 'deep-trans', 'index.mjs')), true);
  assert.equal(existsSync(join(outBundle, 'node_modules', '@scope', 'direct-dep', 'node_modules', 'nested-trans', 'index.mjs')), true);

  const probe = spawnSync(process.execPath, [join(outBundle, 'bin', 'pdd.mjs'), '--probe'], {
    cwd: tmpdir(),
    encoding: 'utf8',
  });
  assert.equal(probe.status, 0, probe.stderr);
  assert.deepEqual(JSON.parse(probe.stdout.trim()), {
    directValue: 'hoisted-ok+nested(deep-ok)',
    cycleA: 'a->b-ok',
    optPresent: 'opt-ok',
  });

  // Missing required transitive dependency fails closed with a 4-part diagnostic.
  rmSync(join(sandbox, 'node_modules', '@scope', 'deep-trans'), { recursive: true, force: true });
  assert.throws(
    () => resolveProductionDependencies(sandbox),
    err => /^Location: /m.test(err.message)
      && /^Invariant: /m.test(err.message)
      && /^Fix: /m.test(err.message)
      && /^Rerun: /m.test(err.message)
      && err.message.includes('@scope/deep-trans'),
  );
});
