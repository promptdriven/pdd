import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { chmodSync, cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { delimiter, dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import {
  checkVersionParity,
  normalizeReleaseTag,
  readPyprojectVersion,
  readPythonInitVersion,
  syncPypiVersion,
} from '../scripts/sync-pypi-version.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const syncScript = join(root, 'scripts', 'sync-pypi-version.mjs');
const pythonPkgRoot = join(root, 'python');

function findPython3() {
  for (const cmd of ['python3', 'python']) {
    const res = spawnSync(cmd, ['-c', 'import sys; print(sys.executable)'], { encoding: 'utf8' });
    if (!res.error && res.status === 0 && res.stdout.trim()) return res.stdout.trim();
  }
  return null;
}

test('#3498 package.json, python/pyproject.toml, and python/pdd_cli/__init__.py stay on the exact same version', () => {
  const pkg = JSON.parse(readFileSync(join(root, 'package.json'), 'utf8'));
  const pyproject = readFileSync(join(root, 'python', 'pyproject.toml'), 'utf8');
  const pyInit = readFileSync(join(root, 'python', 'pdd_cli', '__init__.py'), 'utf8');

  assert.equal(pkg.name, '@promptdriven/pdd');
  assert.equal(pkg.publishConfig?.access, 'public');
  assert.equal(pkg.private, undefined);
  assert.match(pkg.scripts?.version ?? '', /sync-pypi-version\.mjs/);
  assert.match(pyproject, /^name\s*=\s*"pdd-cli"/m);
  assert.match(pyproject, /^pdd\s*=\s*"pdd_cli\.cli:main"/m);

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

  // Before syncing, --check detects the version drift and exits 1.
  const drift = spawnSync(process.execPath, [syncScript, '--check', '--root', sandbox], { encoding: 'utf8' });
  assert.equal(drift.status, 1);
  assert.match(drift.stderr, /0\.2\.99/);

  // Running sync updates both Python version declarations to match package.json.
  assert.equal(syncPypiVersion({ root: sandbox }), '0.2.99');

  for (const validTag of ['0.2.99', 'v0.2.99', 'alpha-v0.2.99', 'refs/tags/alpha-v0.2.99']) {
    assert.equal(normalizeReleaseTag(validTag), '0.2.99');
    const ok = spawnSync(process.execPath, [syncScript, '--check', '--root', sandbox, '--tag', validTag], { encoding: 'utf8' });
    assert.equal(ok.status, 0, ok.stderr);
  }

  // Mismatched or malformed GitHub Release tags fail parity verification.
  for (const badTag of ['alpha-v0.2.98', 'v9.9.9', 'not-a-semver-tag']) {
    const bad = spawnSync(process.execPath, [syncScript, '--check', '--root', sandbox, '--tag', badTag], { encoding: 'utf8' });
    assert.equal(bad.status, 1);
  }
});

test('#3498 release workflow triggers on published GitHub Releases + workflow_dispatch and publishes npm and PyPI with parity checks', () => {
  const workflow = readFileSync(join(root, '.github', 'workflows', 'release.yml'), 'utf8');
  assert.match(workflow, /^\s*release:\s*\n\s*types:\s*\[published\]/m);
  assert.match(workflow, /^\s*workflow_dispatch:/m);
  assert.match(workflow, /sync-pypi-version\.mjs --check/);
  assert.match(workflow, /sync-pypi-version\.mjs --stage-bundle/);
  assert.match(workflow, /npm publish[\s\S]*--access public --provenance/);
  assert.match(workflow, /environment:\s*pypi-publish/);
  assert.match(workflow, /pypa\/gh-action-pypi-publish@release\/v1/);
  assert.match(workflow, /PYPI_API_TOKEN/);
});

test('#3498 Python pdd_cli wrapper delegates to matching @promptdriven/pdd without self-recursion, installs into cache when needed, and reports missing Node', t => {
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
  mkdirSync(home, { recursive: true });
  mkdirSync(stateDir, { recursive: true });

  // 1. Source/bundled resolution: running `python3 -m pdd_cli --version` delegates to bin/pdd.mjs and prints exact version.
  const direct = spawnSync(py, ['-m', 'pdd_cli', '--version'], {
    cwd: sandbox,
    env: {
      ...process.env,
      HOME: home,
      PDD_STATE_DIR: stateDir,
      PDD_CLI_CACHE_DIR: cacheDir,
      PDD_CLI_NO_EXEC: '1',
      PDD_NO_UPDATE_CHECK: '1',
      PYTHONPATH: pythonPkgRoot,
    },
    encoding: 'utf8',
  });
  assert.equal(direct.status, 0, direct.stderr);
  assert.equal(direct.stdout.trim(), pkgVersion);

  // 2. Installed PATH resolution with Python wrapper first on PATH: skips itself and delegates to matching npm @promptdriven/pdd.
  const pyBinDir = join(sandbox, 'py-bin');
  const npmPrefix = join(sandbox, 'npm-global');
  const npmBinDir = join(npmPrefix, 'bin');
  const fakeJsPkg = join(npmPrefix, 'lib', 'node_modules', '@promptdriven', 'pdd');
  mkdirSync(pyBinDir, { recursive: true });
  mkdirSync(npmBinDir, { recursive: true });
  mkdirSync(join(fakeJsPkg, 'bin'), { recursive: true });

  const pyWrapperBin = join(pyBinDir, 'pdd');
  writeFileSync(
    pyWrapperBin,
    `#!${execFileSync(py, ['-c', 'import sys; print(sys.executable)'], { encoding: 'utf8' }).trim()}\nimport sys\nsys.path.insert(0, ${JSON.stringify(pythonPkgRoot)})\nfrom pdd_cli.cli import main\nraise SystemExit(main())\n`,
  );
  chmodSync(pyWrapperBin, 0o755);

  const fakeEntry = join(fakeJsPkg, 'bin', 'pdd.mjs');
  writeFileSync(join(fakeJsPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: pkgVersion }));
  writeFileSync(
    fakeEntry,
    '#!/usr/bin/env node\nconsole.log(JSON.stringify({ delegated: process.argv.slice(2), firstPath: process.env.PATH.split(":")[0] }));\nprocess.exit(0);\n',
  );
  chmodSync(fakeEntry, 0o755);
  symlinkSync(fakeEntry, join(npmBinDir, 'pdd'));

  const pathDelegated = spawnSync(pyWrapperBin, ['lint', '--local', '--json'], {
    cwd: sandbox,
    env: {
      ...process.env,
      HOME: home,
      PDD_CLI_CACHE_DIR: cacheDir,
      PDD_CLI_IGNORE_CHECKOUT: '1',
      PDD_CLI_NO_EXEC: '1',
      PATH: [pyBinDir, npmBinDir, dirname(process.execPath)].join(delimiter),
    },
    encoding: 'utf8',
  });
  assert.equal(pathDelegated.status, 0, pathDelegated.stderr);
  const payload = JSON.parse(pathDelegated.stdout.trim());
  assert.deepEqual(payload.delegated, ['lint', '--local', '--json']);

  // 3. Unbundled fresh-machine fallback: installs @promptdriven/pdd@<version> into user cache via npm without polluting stdout.
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
      "const prefixIdx = args.indexOf('--prefix');",
      'const prefix = args[prefixIdx + 1];',
      'const spec = args.at(-1);',
      "console.log('noisy npm install stdout for ' + spec);",
      "const pkgDir = join(prefix, 'node_modules', '@promptdriven', 'pdd');",
      "mkdirSync(join(pkgDir, 'bin'), { recursive: true });",
      `writeFileSync(join(pkgDir, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: ${JSON.stringify(pkgVersion)} }));`,
      "const entry = join(pkgDir, 'bin', 'pdd.mjs');",
      `writeFileSync(entry, '#!/usr/bin/env node\\nconsole.log(${JSON.stringify(pkgVersion)});\\n');`,
      'chmodSync(entry, 0o755);',
    ].join('\n') + '\n',
  );
  chmodSync(fakeNpm, 0o755);

  const cachedRun = spawnSync(pyWrapperBin, ['--version'], {
    cwd: sandbox,
    env: {
      ...process.env,
      HOME: home,
      PDD_CLI_CACHE_DIR: freshCache,
      PDD_CLI_IGNORE_CHECKOUT: '1',
      PDD_CLI_NO_EXEC: '1',
      PATH: [pyBinDir, fakeNpmDir, dirname(process.execPath)].join(delimiter),
    },
    encoding: 'utf8',
  });
  assert.equal(cachedRun.status, 0, cachedRun.stderr);
  assert.equal(cachedRun.stdout, `${pkgVersion}\n`);

  // 4. Bundled wheel layout (_bundled/bin/pdd.mjs) runs completely offline without npm on PATH.
  const isolatedPyPkg = join(sandbox, 'isolated-python');
  cpSync(pythonPkgRoot, isolatedPyPkg, { recursive: true });
  const bundledPkg = join(isolatedPyPkg, 'pdd_cli', '_bundled');
  mkdirSync(join(bundledPkg, 'bin'), { recursive: true });
  writeFileSync(join(bundledPkg, 'package.json'), JSON.stringify({ name: '@promptdriven/pdd', version: pkgVersion }));
  const bundledEntry = join(bundledPkg, 'bin', 'pdd.mjs');
  writeFileSync(bundledEntry, `#!/usr/bin/env node\nconsole.log('bundled:${pkgVersion}');\n`);

  const bundledRun = spawnSync(py, ['-m', 'pdd_cli', '--version'], {
    cwd: sandbox,
    env: {
      ...process.env,
      HOME: home,
      PDD_CLI_CACHE_DIR: cacheDir,
      PDD_CLI_IGNORE_CHECKOUT: '1',
      PDD_CLI_OFFLINE: '1',
      PDD_CLI_NO_EXEC: '1',
      PYTHONPATH: isolatedPyPkg,
      PATH: dirname(process.execPath),
    },
    encoding: 'utf8',
  });
  assert.equal(bundledRun.status, 0, bundledRun.stderr);
  assert.equal(bundledRun.stdout.trim(), `bundled:${pkgVersion}`);

  // 5. Missing Node.js prints a clear error message and exits 127.
  const noNode = spawnSync(pyWrapperBin, ['--version'], {
    cwd: sandbox,
    env: {
      ...process.env,
      HOME: home,
      PDD_CLI_CACHE_DIR: cacheDir,
      PDD_CLI_IGNORE_CHECKOUT: '1',
      PDD_CLI_NO_EXEC: '1',
      PATH: pyBinDir,
    },
    encoding: 'utf8',
  });
  assert.equal(noNode.status, 127);
  assert.match(noNode.stderr, /Node\.js >=22\.16\.0/);
});
