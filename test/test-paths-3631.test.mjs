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

test('#3631 all 6 reopen rows: tests_py/, configured pytest testpaths, narrow pyproject.toml manifest rule, and test-helper private imports', t => {
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

  // Row 6: test-helper private imports are exempt, while production private imports stay flagged!
  assert.equal(isTestHelperSpecifier('tests_py.pdd_harness', 'tests_py/test_a.py'), true);
  assert.equal(isTestHelperSpecifier('.pdd_harness', 'tests_py/test_a.py'), true);
  assert.equal(isTestHelperSpecifier('equity_ledger.trust.service', 'tests_py/test_a.py'), false);
  assert.equal(isTestHelperSpecifier('...equity_ledger.trust', 'tests_py/sub/test_a.py'), false);

  // Narrow pyproject.toml manifest rule: test-only [tool.pytest.ini_options] edits exempt; [project.scripts] CLI entrypoints NOT exempt!
  const basePyproject = [
    '[project]',
    'name = "demo"',
    'version = "0.1.0"',
    'dependencies = ["fastapi>=0.115"]',
    '',
    '[project.scripts]',
    'equity = "equity_ledger.cli.terminal:cli_entrypoint"',
    '',
    '[tool.pytest.ini_options]',
    'testpaths = ["tests_py"]',
  ].join('\n') + '\n';
  const testOnlyPyproject = `${basePyproject}addopts = ["-q"]\n`;
  const cliScriptEditPyproject = basePyproject.replace('cli_entrypoint', 'other_entrypoint');
  const depEditPyproject = basePyproject.replace('fastapi>=0.115', 'fastapi>=0.116');
  assert.equal(isNonProductionPyprojectEdit(basePyproject, testOnlyPyproject), true);
  assert.equal(isNonProductionPyprojectEdit(basePyproject, cliScriptEditPyproject), false, 'CLI entrypoint edits in [project.scripts] must remain production surfaces');
  assert.equal(isNonProductionPyprojectEdit(basePyproject, depEditPyproject), false, 'dependency edits in [project] must remain production surfaces');

  // End-to-end repo check: changed-map, matchVerifyPaths, lintChangedTestPrivateImports, and custom pytest testpaths.
  const repo = mkdtempSync(join(tmpdir(), 'pdd-3631-e2e-'));
  t.after(() => rmSync(repo, { recursive: true, force: true }));
  mkdirSync(join(repo, 'tests_py'), { recursive: true });
  mkdirSync(join(repo, 'py_suite'), { recursive: true });
  mkdirSync(join(repo, 'equity_ledger/trust'), { recursive: true });

  writeFileSync(join(repo, 'pyproject.toml'), basePyproject.replace('["tests_py"]', '["tests_py", "py_suite"]'));
  writeFileSync(join(repo, 'tests_py/pdd_harness.py'), 'def _helper():\n    return 1\n');
  writeFileSync(join(repo, 'tests_py/test_ok.py'), 'from tests_py.pdd_harness import _helper\nfrom .pdd_harness import _helper as h2\n');
  writeFileSync(join(repo, 'tests_py/test_bad.py'), 'from equity_ledger.trust.service import _secret\n');
  writeFileSync(join(repo, 'py_suite/helper.py'), 'X = 1\n');
  writeFileSync(join(repo, 'equity_ledger/trust/service.py'), 'def _secret():\n    return 42\n');

  execFileSync('git', ['init', '-q'], { cwd: repo });
  execFileSync('git', ['add', '.'], { cwd: repo });
  execFileSync('git', ['-c', 'user.name=Test', '-c', 'user.email=test@example.com', 'commit', '-q', '-m', 'init'], { cwd: repo });
  const baseSha = execFileSync('git', ['rev-parse', 'HEAD'], { cwd: repo, encoding: 'utf8' }).trim();

  assert.deepEqual(readPytestTestpaths(repo), ['tests_py', 'py_suite']);

  // Row 6 live check on files:
  const okFindings = lintChangedTestPrivateImports({ root: repo, files: ['tests_py/test_ok.py'], changedFiles: ['tests_py/test_ok.py'] }).findings;
  assert.deepEqual(okFindings, [], 'tests_py helper imports must emit 0 [test-private-import] warnings');
  const badFindings = lintChangedTestPrivateImports({ root: repo, files: ['tests_py/test_bad.py'], changedFiles: ['tests_py/test_bad.py'] }).findings;
  assert.equal(badFindings.length, 1);
  assert.match(badFindings[0].formatted, /\[test-private-import\].*"_secret"/);

  // Edit tests_py/pdd_harness.py, custom py_suite/helper.py, and test-only section of pyproject.toml:
  writeFileSync(join(repo, 'tests_py/pdd_harness.py'), 'def _helper():\n    return 2\n');
  writeFileSync(join(repo, 'py_suite/helper.py'), 'X = 2\n');
  writeFileSync(join(repo, 'pyproject.toml'), `${basePyproject.replace('["tests_py"]', '["tests_py", "py_suite"]')}addopts = ["-q"]\n`);

  const cm = analyzeChangedMap({ cwd: repo });
  assert.equal(cm.ok, true);
  assert.equal(cm.report.unowned.some(u => u.path === 'tests_py/pdd_harness.py'), false, 'tests_py/pdd_harness.py must not be reported as unowned');

  const cfg = parseVerifyConfig({ test: 'true', paths: [] });
  const m1 = matchVerifyPaths(cfg, ['tests_py/pdd_harness.py', 'py_suite/helper.py', 'pyproject.toml'], { root: repo, baseSha });
  assert.deepEqual(m1.changedSurfaces, [], 'tests_py, configured testpaths, and test-only pyproject.toml edit must have 0 unmapped production surfaces');
  assert.deepEqual(m1.unmappedSurfaces, []);

  // Neighbor control 1: editing [project.scripts] in pyproject.toml MUST appear in changedSurfaces!
  writeFileSync(join(repo, 'pyproject.toml'), cliScriptEditPyproject.replace('["tests_py"]', '["tests_py", "py_suite"]'));
  const m2 = matchVerifyPaths(cfg, ['pyproject.toml'], { root: repo, baseSha });
  assert.deepEqual(m2.changedSurfaces, ['pyproject.toml'], 'CLI entrypoint edit in pyproject.toml must remain a production surface');

  // Neighbor control 2: editing a real production file MUST appear in changedSurfaces and trigger prove unmapped check!
  const m3 = matchVerifyPaths(cfg, ['equity_ledger/trust/service.py'], { root: repo, baseSha });
  assert.deepEqual(m3.changedSurfaces, ['equity_ledger/trust/service.py']);
  assert.deepEqual(m3.unmappedSurfaces, ['equity_ledger/trust/service.py']);

  // Restore test-only pyproject.toml and run runProve to verify receipt.notProvedReasons has ZERO mention of tests_py/pdd_harness.py or pyproject.toml.
  writeFileSync(join(repo, 'pyproject.toml'), `${basePyproject.replace('["tests_py"]', '["tests_py", "py_suite"]')}addopts = ["-q"]\n`);
  const out = { text: '', write(s) { this.text += s; return true; } };
  const err = { text: '', write(s) { this.text += s; return true; } };
  const proveRes = runProve({ cwd: repo, base: baseSha, json: true }, { stdout: out, stderr: err, spawnSync: () => ({ status: 0, stdout: '1 passed\n', stderr: '' }) });
  assert.equal(proveRes.receipt.changedSurfaces.includes('tests_py/pdd_harness.py'), false);
  assert.equal(proveRes.receipt.changedSurfaces.includes('pyproject.toml'), false);
  assert.equal(proveRes.receipt.notProvedReasons.some(r => r.includes('tests_py/pdd_harness.py') || r.includes('pyproject.toml')), false);
});
