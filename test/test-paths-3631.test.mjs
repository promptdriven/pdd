import './helpers/test-home.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { isTestOwnedPath } from '../src/file-owner.mjs';
import { analyzeChangedMap } from '../src/core/changed-map.mjs';
import { isProductionSurfaceFile, matchVerifyPaths, parseVerifyConfig } from '../src/core/verify-paths.mjs';
import { runProve } from '../src/core/prove.mjs';
import { NON_PRODUCTION_DIR_RE, classifyProductionPathSurfaces } from '../src/autopilot/validator/surfaces.mjs';
import { lintChangedTestPrivateImports } from '../src/autopilot/validator/test-probes.mjs';
import {
  COLOCATED_TEST_PATH_RE,
  TEST_FILE_PATH_RE,
  isNonProductionPyprojectEdit,
  isTestHelperSpecifier,
  readPytestTestpaths,
} from '../src/shared/test-paths.mjs';

test('#3631 all 6 reopen rows: tests_py/, trusted-base pytest testpaths, narrow pyproject.toml manifest rule, and test-helper private imports', t => {
  // Row 1: file-owner + changed-map recognize tests_py/ helpers.
  assert.equal(isTestOwnedPath('tests_py/pdd_harness.py'), true);
  assert.equal(isTestOwnedPath('tests_py/conftest.py'), true);
  assert.equal(isTestOwnedPath('equity_ledger/trust/service.py'), false);

  // Row 2: verify-paths excludes tests_py/ while keeping real production files.
  assert.equal(isProductionSurfaceFile('tests_py/pdd_harness.py'), false);
  assert.equal(isProductionSurfaceFile('equity_ledger/trust/service.py'), true);

  // Row 3: prove COLOCATED_TEST_PATH_RE includes tests_py/.
  assert.equal(COLOCATED_TEST_PATH_RE.test('tests_py/pdd_harness.py'), true);

  // Row 4: validator surfaces NON_PRODUCTION_DIR_RE includes tests_py/.
  assert.equal(NON_PRODUCTION_DIR_RE.test('tests_py/pdd_harness.py'), true);
  assert.deepEqual(classifyProductionPathSurfaces('tests_py/pdd_harness.py'), []);

  // Row 5: test-probes BACKSIDE_TEST_FILE_RE (TEST_FILE_PATH_RE) includes tests_py/.
  assert.equal(TEST_FILE_PATH_RE.test('tests_py/pdd_harness.py'), true);
  assert.equal(TEST_FILE_PATH_RE.test('tests_py/test_wave1.py'), true);

  // Row 6 + BREAK-IT F4: test-helper private imports are exempt, while production modules (incl. equity_ledger.helpers/auth_harness/conftest/fixtures) stay flagged!
  assert.equal(isTestHelperSpecifier('tests_py.pdd_harness', 'tests_py/test_a.py'), true);
  assert.equal(isTestHelperSpecifier('.pdd_harness', 'tests_py/test_a.py'), true);
  assert.equal(isTestHelperSpecifier('equity_ledger.trust.service', 'tests_py/test_a.py'), false);
  assert.equal(isTestHelperSpecifier('equity_ledger.helpers', 'tests_py/test_a.py'), false);
  assert.equal(isTestHelperSpecifier('equity_ledger.auth_harness', 'tests_py/test_a.py'), false);
  assert.equal(isTestHelperSpecifier('equity_ledger.conftest', 'tests_py/test_a.py'), false);
  assert.equal(isTestHelperSpecifier('equity_ledger.fixtures', 'tests_py/test_a.py'), false);
  assert.equal(isTestHelperSpecifier('...equity_ledger.trust', 'tests_py/sub/test_a.py'), false);
  assert.equal(isTestHelperSpecifier('.common', 'tests_py/test_a.py', [], new Set(['tests_py/common.py', 'tests_py/test_a.py'])), true);
  assert.equal(isTestHelperSpecifier('.service', 'tests/test_b.py', [], new Set(['tests/test_b.py'])), false);

  // Narrow pyproject.toml manifest rule (+ BREAK-IT F3 & F6):
  // - dev-only ([tool.ruff], [project.optional-dependencies].dev, [dependency-groups], comments) ARE exempt
  // - [project.scripts], [project].dependencies, [tool.pytest.ini_options] (e.g. addopts), and TOML Date changes are NOT exempt!
  const basePyproject = [
    '[project]',
    'name = "demo"',
    'version = "0.1.0"',
    'dependencies = ["fastapi>=0.115"]',
    '',
    '[project.optional-dependencies]',
    'dev = ["pytest>=8.0"]',
    '',
    '[project.scripts]',
    'equity = "equity_ledger.cli.terminal:cli_entrypoint"',
    '',
    '[tool.release]',
    'date = 2026-01-01',
    'big_id = 9007199254740993',
    '',
    '[tool.pytest.ini_options]',
    'testpaths = ["tests_py"]',
  ].join('\n') + '\n';
  const ruffOnlyPyproject = `${basePyproject}\n[tool.ruff]\nline-length = 100\n`;
  const devDepPyproject = basePyproject.replace('"pytest>=8.0"', '"pytest>=8.0", "httpx>=0.27"');
  const pytestAddoptsPyproject = `${basePyproject}addopts = ["-k", "test_smoke"]\n`;
  const cliScriptEditPyproject = basePyproject.replace('cli_entrypoint', 'other_entrypoint');
  const depEditPyproject = basePyproject.replace('fastapi>=0.115', 'fastapi>=0.116');
  const dateEditPyproject = basePyproject.replace('2026-01-01', '2099-12-31');

  assert.equal(isNonProductionPyprojectEdit(basePyproject, ruffOnlyPyproject), true, 'ruff + BigInt in pyproject.toml must remain exempt');
  assert.equal(isNonProductionPyprojectEdit(basePyproject, devDepPyproject), true, 'dev optional-dependencies edit must remain exempt');
  assert.equal(isNonProductionPyprojectEdit(basePyproject, pytestAddoptsPyproject), false, 'pytest addopts edit must NOT be auto-exempt (BREAK-IT F3)');
  assert.equal(isNonProductionPyprojectEdit(basePyproject, cliScriptEditPyproject), false, 'CLI entrypoint edits in [project.scripts] must remain production surfaces');
  assert.equal(isNonProductionPyprojectEdit(basePyproject, depEditPyproject), false, 'dependency edits in [project] must remain production surfaces');
  assert.equal(isNonProductionPyprojectEdit(basePyproject, dateEditPyproject), false, 'TOML Date production edits must NOT collapse to {} (BREAK-IT F6)');

  // End-to-end repo check: changed-map, matchVerifyPaths, lintChangedTestPrivateImports, trusted-base testpaths, and multi-line pytest.ini / setup.cfg.
  const repo = mkdtempSync(join(tmpdir(), 'pdd-3631-e2e-'));
  t.after(() => rmSync(repo, { recursive: true, force: true }));
  mkdirSync(join(repo, 'tests_py'), { recursive: true });
  mkdirSync(join(repo, 'py_suite'), { recursive: true });
  mkdirSync(join(repo, 'equity_ledger/trust'), { recursive: true });

  writeFileSync(join(repo, 'pyproject.toml'), basePyproject.replace('["tests_py"]', '["tests_py", "py_suite"]'));
  writeFileSync(join(repo, 'pytest.ini'), '[pytest]\ntestpaths =\n    custom_a\n    custom_b\n');
  writeFileSync(join(repo, 'setup.cfg'), '[other_section]\ntestpaths = equity_ledger\n');
  writeFileSync(join(repo, 'tests_py/pdd_harness.py'), 'def _helper():\n    return 1\n');
  writeFileSync(join(repo, 'tests_py/common.py'), 'def _shared():\n    return 2\n');
  writeFileSync(join(repo, 'tests_py/test_ok.py'), 'from tests_py.pdd_harness import _helper\nfrom .pdd_harness import _helper as h2\nfrom .common import _shared\n');
  writeFileSync(join(repo, 'tests_py/test_bad.py'), 'from equity_ledger.trust.service import _secret\nfrom equity_ledger.helpers import _h\nfrom equity_ledger.auth_harness import _a\n');
  writeFileSync(join(repo, 'py_suite/helper.py'), 'X = 1\n');
  writeFileSync(join(repo, 'equity_ledger/trust/service.py'), 'def _secret():\n    return 42\n');

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });
  const baseSha = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: repo, encoding: 'utf8' }).trim();

  // BREAK-IT F7: multi-line pytest.ini parsed completely; unrelated setup.cfg section ignored!
  assert.deepEqual(readPytestTestpaths(repo), ['tests_py', 'py_suite', 'custom_a', 'custom_b']);
  assert.deepEqual(readPytestTestpaths(repo, { gitRef: baseSha }), ['tests_py', 'py_suite', 'custom_a', 'custom_b']);

  // Row 6 live check on files:
  const okFindings = lintChangedTestPrivateImports({
    root: repo,
    files: ['tests_py/test_ok.py', 'tests_py/common.py', 'tests_py/pdd_harness.py'],
    changedFiles: ['tests_py/test_ok.py'],
  }).findings;
  assert.deepEqual(okFindings, [], 'tests_py helper & sibling imports must emit 0 [test-private-import] warnings');
  const badFindings = lintChangedTestPrivateImports({ root: repo, files: ['tests_py/test_bad.py'], changedFiles: ['tests_py/test_bad.py'] }).findings;
  assert.equal(badFindings.length, 3, 'all 3 production private imports (incl. helpers/auth_harness) must stay flagged');

  // Edit tests_py/pdd_harness.py, custom py_suite/helper.py, and dev-only [tool.ruff] section of pyproject.toml:
  writeFileSync(join(repo, 'tests_py/pdd_harness.py'), 'def _helper():\n    return 2\n');
  writeFileSync(join(repo, 'py_suite/helper.py'), 'X = 2\n');
  writeFileSync(join(repo, 'pyproject.toml'), `${basePyproject.replace('["tests_py"]', '["tests_py", "py_suite"]')}\n[tool.ruff]\nline-length = 100\n`);

  const cm = analyzeChangedMap({ cwd: repo });
  assert.equal(cm.ok, true);
  assert.equal(cm.report.unowned.some(u => u.path === 'tests_py/pdd_harness.py'), false, 'tests_py/pdd_harness.py must not be reported as unowned');

  const cfg = parseVerifyConfig({ test: 'true', paths: [] });
  const m1 = matchVerifyPaths(cfg, ['tests_py/pdd_harness.py', 'py_suite/helper.py', 'pyproject.toml'], { root: repo, baseSha });
  assert.deepEqual(m1.changedSurfaces, [], 'tests_py, configured base testpaths, and dev-only pyproject.toml edit must have 0 unmapped production surfaces');
  assert.deepEqual(m1.unmappedSurfaces, []);

  // BREAK-IT F1: untrusted working-tree pyproject.toml adding testpaths = ["equity_ledger"] MUST NOT hide equity_ledger/trust/service.py!
  writeFileSync(join(repo, 'pyproject.toml'), basePyproject.replace('["tests_py"]', '["tests_py", "equity_ledger"]'));
  const mBypass = matchVerifyPaths(cfg, ['equity_ledger/trust/service.py', 'pyproject.toml'], { root: repo, baseSha });
  assert.deepEqual(mBypass.changedSurfaces, ['equity_ledger/trust/service.py', 'pyproject.toml'], 'untrusted working-tree testpaths MUST NOT hide production files');

  // BREAK-IT F2: split base/head config in lintChangedTestPrivateImports MUST read testpaths from trusted config dir, NOT untrusted head root!
  const trustedBaseDir = mkdtempSync(join(tmpdir(), 'pdd-3631-base-'));
  t.after(() => rmSync(trustedBaseDir, { recursive: true, force: true }));
  writeFileSync(join(trustedBaseDir, 'pyproject.toml'), basePyproject);
  const splitFindings = lintChangedTestPrivateImports({
    root: repo,
    files: ['tests_py/test_bad.py'],
    changedFiles: ['tests_py/test_bad.py'],
    config: trustedBaseDir,
  }).findings;
  assert.equal(splitFindings.length, 3, 'untrusted head pyproject.toml testpaths MUST NOT silence [test-private-import] when trusted config root is provided');

  // BREAK-IT F3: untrusted [tool.pytest.ini_options] addopts edit MUST be blocked by runProve even when verify.test invokes pytest!
  writeFileSync(join(repo, 'pyproject.toml'), `${basePyproject.replace('["tests_py"]', '["tests_py", "py_suite"]')}addopts = ["-k", "test_smoke"]\n`);
  const outF3 = { text: '', write(s) { this.text += s; return true; } };
  const errF3 = { text: '', write(s) { this.text += s; return true; } };
  const proveF3 = runProve({ cwd: repo, base: baseSha, json: true }, { stdout: outF3, stderr: errF3, spawnSync: () => ({ status: 0, stdout: '1 passed\n', stderr: '' }) });
  assert.equal(proveF3.receipt.changedSurfaces.includes('pyproject.toml'), true, 'pytest addopts edit must stay in changedSurfaces');
  assert.equal(proveF3.receipt.notProvedReasons.some(r => r.includes('pytest configuration')), true, 'untrusted pytest config edit must block proof');

  // Neighbor control 1: editing [project.scripts] in pyproject.toml MUST appear in changedSurfaces!
  writeFileSync(join(repo, 'pyproject.toml'), cliScriptEditPyproject.replace('["tests_py"]', '["tests_py", "py_suite"]'));
  const m2 = matchVerifyPaths(cfg, ['pyproject.toml'], { root: repo, baseSha });
  assert.deepEqual(m2.changedSurfaces, ['pyproject.toml'], 'CLI entrypoint edit in pyproject.toml must remain a production surface');

  // Restore dev-only [tool.ruff] edit in pyproject.toml and verify runProve has ZERO mention of tests_py/pdd_harness.py or pyproject.toml!
  writeFileSync(join(repo, 'pyproject.toml'), `${basePyproject.replace('["tests_py"]', '["tests_py", "py_suite"]')}\n[tool.ruff]\nline-length = 100\n`);
  const out = { text: '', write(s) { this.text += s; return true; } };
  const err = { text: '', write(s) { this.text += s; return true; } };
  const proveRes = runProve({ cwd: repo, base: baseSha, json: true }, { stdout: out, stderr: err, spawnSync: () => ({ status: 0, stdout: '1 passed\n', stderr: '' }) });
  assert.equal(proveRes.receipt.changedSurfaces.includes('tests_py/pdd_harness.py'), false);
  assert.equal(proveRes.receipt.changedSurfaces.includes('pyproject.toml'), false);
  assert.equal(proveRes.receipt.notProvedReasons.some(r => r.includes('tests_py/pdd_harness.py') || r.includes('pyproject.toml')), false);
});
