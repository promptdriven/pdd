// Prompt: prompts/cli/autopilot-validator.prompt.md

// Live production evidence collector for Autopilot merge checks:
// wires `pdd prove` / merge-base `verify.paths`, G3 polyglot report-diff & base-owned test oracle,
// post-review isolated test-env secret injection, and bound 13-field harness receipts.
import { execFile as cbExecFile, spawnSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { tmpdir } from 'node:os';
import { basename, dirname, join, posix } from 'node:path';
import { promisify } from 'node:util';
import { discoverFormalScope, isProductionCodeFile, runFormalVerification } from '../../core/formal-verify.mjs';
import { OUTCOME_FAILED, OUTCOME_NOT_PROVED, OUTCOME_PROVED, runProve } from '../../core/prove.mjs';
import { canonicalRepoPath, readSafeUtf8, scrubChildEnv } from '../../core/lint/diagnostics.mjs';
import { loadVerifyConfig, matchVerifyPaths } from '../../core/verify-paths.mjs';
import { isLintableStoryPath } from '../../story-lint.mjs';
import { computeCanonicalDigest } from '../gates/evidence-contract.mjs';
import {
  buildPostReviewSandboxEnv,
  loadAutopilotTestEnv,
  probeMachineCapabilities,
  registerTestEnvSecrets,
  summarizeTestEnvMetadata,
} from '../gates/test-env.mjs';
import { diffTestReports, parseStandardTestReport, runBaseOwnedTestOracle } from './report-diff.mjs';
import {
  buildRunnerEnv,
  buildRunnerInvocation,
  detectTestRunner,
  extractTestCases,
  parsePytestVerboseReport,
  parseVitestVerboseReport,
  resolvePytestBinary,
} from './test-runners.mjs';

const execFileAsync = promisify(cbExecFile);
const TEST_FILE_RE = /(?:(?:^|\/)(?:test|tests|__tests__|spec)\/|\.(?:test|spec)\.[a-z0-9]+$|_test\.(?:go|rs|py)$|(?:^|\/)test_[^/]+\.py$)/i;
const JS_TEST_RE = /\.(?:mjs|cjs|js|ts|tsx|jsx)$/i;
const PY_TEST_RE = /(?:(?:^|\/)test_[^/]+\.py$|_test\.py$)/i;
const PY_FORMAL_TEST_RE = /(?:(?:^|\/)(?:test_formal_[^/]+|[^/]+_formal_test)\.py$|(?:^|\/)formal\/test_[^/]+\.py$)/i;
const GO_TEST_RE = /_test\.go$/i;
const RUST_TEST_RE = /(?:(?:^|\/)tests\/[^/]+\.rs$|_test\.rs$)/i;
const GIT_SHA_RE = /^[0-9a-f]{40}$/i;
const isObj = v => v !== null && typeof v === 'object' && !Array.isArray(v);
const nonEmpty = v => typeof v === 'string' && v.trim().length > 0;
const HOST_CAPABILITY_CACHE = new Map();
const MAX_HOST_CAPABILITY_CACHE = 16;

function probeCachedCapabilities({ rawTestEnv, env, probeOptions }) {
  const hasCustomOptions = isObj(probeOptions) && Object.keys(probeOptions).length > 0;
  if (hasCustomOptions) {
    return [...probeMachineCapabilities({ testEnv: rawTestEnv, env, ...probeOptions }).capabilities];
  }
  const accountsKey = rawTestEnv?.ok === true && isObj(rawTestEnv.accounts)
    ? Object.keys(rawTestEnv.accounts).sort().join(',')
    : '';
  const cacheKey = `${String(env?.PATH ?? '')}\0${accountsKey}`;
  if (HOST_CAPABILITY_CACHE.has(cacheKey)) {
    return [...HOST_CAPABILITY_CACHE.get(cacheKey)];
  }
  const caps = [...probeMachineCapabilities({ testEnv: rawTestEnv, env }).capabilities];
  if (HOST_CAPABILITY_CACHE.size >= MAX_HOST_CAPABILITY_CACHE) {
    HOST_CAPABILITY_CACHE.clear();
  }
  HOST_CAPABILITY_CACHE.set(cacheKey, caps);
  return [...caps];
}

function readGitTreeSha(cwd, ref = 'HEAD') {
  if (!nonEmpty(cwd)) return null;
  try {
    const res = spawnSync('git', ['rev-parse', `${ref}^{tree}`], {
      cwd, encoding: 'utf8', timeout: 5000, stdio: ['ignore', 'pipe', 'ignore'],
    });
    const sha = String(res.stdout ?? '').trim();
    return res.status === 0 && GIT_SHA_RE.test(sha) ? sha : null;
  } catch { return null; }
}

const SKIP_WALK_DIRS = new Set([
  '.git', 'node_modules', 'dist', 'build', '.venv', 'venv', 'target', 'vendor', '.pdd', '__pycache__',
  'test', 'tests', '__tests__', 'spec', 'docs', 'doc', 'fixtures', '__fixtures__', 'examples', 'prompts', 'user_stories',
]);

function hasAnyProductionCodeFile(root, fs = nativeFs) {
  if (!nonEmpty(root)) return false;
  const stack = [''];
  let visited = 0;
  while (stack.length > 0 && visited < 50_000) {
    const relDir = stack.pop();
    const absDir = relDir ? join(root, relDir) : root;
    let entries;
    try { entries = fs.readdirSync(absDir, { withFileTypes: true }); } catch { continue; }
    for (const entry of entries) {
      if (entry.isSymbolicLink()) continue;
      const rel = relDir ? `${relDir}/${entry.name}` : entry.name;
      if (entry.isDirectory()) {
        if (!SKIP_WALK_DIRS.has(entry.name.toLowerCase())) stack.push(rel);
      } else if (entry.isFile()) {
        visited += 1;
        if (isProductionCodeFile(rel)) return true;
      }
    }
  }
  return false;
}

function isRegularFileNoSymlink(root, relPath, fs = nativeFs) {
  if (!nonEmpty(root) || !canonicalRepoPath(relPath)) return false;
  const parts = relPath.split('/');
  let cur = root;
  for (let i = 0; i < parts.length; i += 1) {
    cur = join(cur, parts[i]);
    try {
      const st = fs.lstatSync(cur);
      if (st.isSymbolicLink()) return false;
      if (i === parts.length - 1) return st.isFile();
      if (!st.isDirectory()) return false;
    } catch {
      return false;
    }
  }
  return false;
}

function defaultToolchainLabel(runnerKind = null) {
  return runnerKind ? `${runnerKind}@node-${process.version}` : `node-${process.version}`;
}

function isPolyglotEnvError(text, changedProdFiles = []) {
  const s = String(text ?? '');
  if (/ENOENT|command not found|not recognized as an internal|No module named|ModuleNotFoundError/i.test(s)) return true;
  if (/Cannot find (?:package|module)/i.test(s)) {
    const prodSet = new Set(changedProdFiles.map(f => String(f).replace(/\\/g, '/').toLowerCase()));
    const refs = [...s.matchAll(/Cannot find (?:package|module)\s+['"`]([^'"`]+)['"`]/gi)].map(m => m[1]);
    if (!refs.length) return true;
    return refs.some(ref => {
      const norm = ref.replace(/\\/g, '/').toLowerCase();
      return ![...prodSet].some(ch => norm === ch || norm.endsWith(`/${ch}`));
    });
  }
  return false;
}

function readOptionalXmlReport(fs, junitPath) {
  if (!junitPath) return null;
  try {
    if (!fs.existsSync(junitPath)) return null;
    const xml = fs.readFileSync(junitPath, 'utf8');
    return nonEmpty(xml) ? xml : null;
  } catch {
    return null;
  }
}

function parsePolyglotBatchReport({ kind, reportFormat, stdout, stderr, junitXml }) {
  if (nonEmpty(junitXml)) {
    const parsedXml = parseStandardTestReport(junitXml, 'junit');
    if (parsedXml.ok) return { parsed: parsedXml, cases: parsedXml.cases, rawReport: junitXml };
  }
  const combined = `${stdout ?? ''}\n${stderr ?? ''}`;
  const parsedStd = parseStandardTestReport(stdout ?? '', reportFormat);
  if (parsedStd.ok) return { parsed: parsedStd, cases: parsedStd.cases, rawReport: stdout ?? '' };
  if (kind === 'pytest') {
    const parsedVerb = parsePytestVerboseReport(combined);
    if (parsedVerb.ok) return { parsed: parsedVerb, cases: parsedVerb.cases, rawReport: parsedVerb };
  } else if (kind === 'vitest') {
    const parsedVerb = parseVitestVerboseReport(combined);
    if (parsedVerb.ok) return { parsed: parsedVerb, cases: parsedVerb.cases, rawReport: parsedVerb };
  }
  const cases = extractTestCases(combined, kind ?? 'auto');
  return { parsed: { ok: false, cases: [] }, cases, rawReport: null };
}

/**
 * Polyglot bug-fix base-control runner across JS/node:test, Vitest (`--reporter=junit`),
 * Pytest (`-v --junitxml`, `.venv/bin/pytest`, `PYTHONPATH=src`, per-file formal isolation),
 * Go (`go test -json`), and Rust (`cargo test`).
 */
export async function runPolyglotBaseControl({
  baseDir, changedFiles = [], changedProdFiles = [], env = process.env, execFn = null, timeoutMs = 60_000, fs = nativeFs,
} = {}) {
  if (!nonEmpty(baseDir) || !changedProdFiles.length) {
    return { state: 'not-run', runnerKind: null, command: null, exitCode: null, report: null };
  }
  const detected = detectTestRunner(baseDir);
  const kind = detected?.kind ?? null;
  const testFiles = (Array.isArray(changedFiles) ? changedFiles : []).filter(f => nonEmpty(f) && TEST_FILE_RE.test(f));
  if (!testFiles.length) return { state: 'not-run', runnerKind: kind, command: null, exitCode: null, report: null };

  let matched = [];
  let effectiveKind = kind ?? 'node:test';
  if (kind === 'vitest') {
    matched = testFiles.filter(f => JS_TEST_RE.test(f));
  } else if (kind === 'pytest') {
    matched = testFiles.filter(f => PY_TEST_RE.test(f));
  } else if (kind === 'go') {
    matched = testFiles.filter(f => GO_TEST_RE.test(f));
  } else if (kind === 'cargo') {
    matched = testFiles.filter(f => RUST_TEST_RE.test(f));
  } else {
    effectiveKind = 'node:test';
    matched = testFiles.filter(f => /\.(?:mjs|cjs|js)$/i.test(f));
  }
  if (!matched.length) return { state: 'not-run', runnerKind: kind, command: null, exitCode: null, report: null };

  const baseEnv = buildRunnerEnv(effectiveKind, baseDir, { ...scrubChildEnv(env), CI: 'true' });
  delete baseEnv.NODE_TEST_CONTEXT;
  delete baseEnv.NODE_OPTIONS;

  const runExec = execFn ?? (async (command, cmdArgs, opts) => {
    try {
      const { stdout, stderr } = await execFileAsync(command, cmdArgs, opts);
      return { exitCode: 0, stdout: String(stdout ?? ''), stderr: String(stderr ?? ''), killed: false, code: null };
    } catch (err) {
      return {
        exitCode: typeof err?.code === 'number' ? err.code : 1,
        stdout: String(err?.stdout ?? ''),
        stderr: String(err?.stderr ?? ''),
        killed: Boolean(err?.killed),
        code: typeof err?.code === 'string' ? err.code : null,
        message: String(err?.message ?? ''),
      };
    }
  });

  const tempDir = (effectiveKind === 'pytest' || effectiveKind === 'vitest')
    ? fs.mkdtempSync(join(tmpdir(), 'pdd-polyglot-ctrl-'))
    : null;
  try {
    // #3561 / #3634: Isolate Python formal test files into separate pytest subprocesses (prevents Z3 main_ctx deadlocks).
    const formalPyFiles = effectiveKind === 'pytest' ? matched.filter(f => PY_FORMAL_TEST_RE.test(f)) : [];
    const isolateFormalPy = effectiveKind === 'pytest' && formalPyFiles.length > 0 && (matched.length > 1 || formalPyFiles.length > 1);
    if (isolateFormalPy) {
      const regularFiles = matched.filter(f => !PY_FORMAL_TEST_RE.test(f));
      const batches = [
        ...(regularFiles.length ? [regularFiles] : []),
        ...formalPyFiles.map(f => [f]),
      ];
      const commands = [];
      const allCases = [];
      const pytestBin = resolvePytestBinary(baseDir);
      let failedExit = null;
      for (let idx = 0; idx < batches.length; idx += 1) {
        const batch = batches[idx];
        const junitPath = tempDir ? join(tempDir, `junit-${idx}.xml`) : null;
        const inv = buildRunnerInvocation('pytest', { root: baseDir, files: batch, junitPath, pytestBin });
        commands.push(`${inv.bin} ${inv.args.join(' ')}`);
        const res = await runExec(inv.bin, inv.args, { cwd: baseDir, env: baseEnv, timeout: timeoutMs, maxBuffer: 4 * 1024 * 1024 });
        const combined = `${res.stdout ?? ''}\n${res.stderr ?? ''}`;
        const junitXml = readOptionalXmlReport(fs, junitPath);
        const { cases: batchCases } = parsePolyglotBatchReport({
          kind: 'pytest',
          reportFormat: inv.reportFormat,
          stdout: res.stdout,
          stderr: res.stderr,
          junitXml,
        });
        allCases.push(...batchCases);
        if (res.killed || res.code === 'ENOENT' || isPolyglotEnvError(`${combined}\n${res.message ?? ''}`, changedProdFiles)) {
          return { state: 'not-run', runnerKind: 'pytest', command: commands.join(' && '), exitCode: res.exitCode ?? null, report: null, cases: allCases, isolatedFiles: formalPyFiles };
        }
        if (res.exitCode !== 0 && failedExit === null) failedExit = res.exitCode ?? 1;
      }
      const cmdDisplay = commands.join(' && ');
      if (failedExit !== null) {
        return { state: 'ran-and-failed-on-base', runnerKind: 'pytest', command: cmdDisplay, exitCode: failedExit, report: null, cases: allCases, isolatedFiles: formalPyFiles };
      }
      return { state: 'passed-on-base', runnerKind: 'pytest', command: cmdDisplay, exitCode: 0, report: null, cases: allCases, isolatedFiles: formalPyFiles };
    }

    const junitPath = tempDir ? join(tempDir, 'junit.xml') : null;
    const inv = buildRunnerInvocation(effectiveKind, { root: baseDir, files: matched, junitPath });
    const cmdDisplay = `${inv.bin} ${inv.args.join(' ')}`;
    const res = await runExec(inv.bin, inv.args, { cwd: baseDir, env: baseEnv, timeout: timeoutMs, maxBuffer: 4 * 1024 * 1024 });
    const combined = `${res.stdout ?? ''}\n${res.stderr ?? ''}`;
    const junitXml = readOptionalXmlReport(fs, junitPath);
    const { parsed, cases } = parsePolyglotBatchReport({
      kind: effectiveKind,
      reportFormat: inv.reportFormat,
      stdout: res.stdout,
      stderr: res.stderr,
      junitXml,
    });
    if (res.exitCode === 0 && !res.killed) {
      return { state: 'passed-on-base', runnerKind: effectiveKind, command: cmdDisplay, exitCode: 0, report: parsed.ok ? parsed : null, cases };
    }
    if (res.killed || res.code === 'ENOENT' || isPolyglotEnvError(`${combined}\n${res.message ?? ''}`, changedProdFiles)) {
      return { state: 'not-run', runnerKind: effectiveKind, command: cmdDisplay, exitCode: res.exitCode ?? null, report: null, cases };
    }
    return { state: 'ran-and-failed-on-base', runnerKind: effectiveKind, command: cmdDisplay, exitCode: res.exitCode ?? 1, report: parsed.ok ? parsed : null, cases };
  } finally {
    if (tempDir) {
      try { fs.rmSync(tempDir, { recursive: true, force: true }); } catch {}
    }
  }
}

function listTreeTestFilesSafe(treeDir, fs = nativeFs) {
  const found = [];
  const walk = (absDir, relPrefix, depth) => {
    if (depth > 8 || found.length >= 2000) return;
    let entries;
    try { entries = fs.readdirSync(absDir, { withFileTypes: true }); } catch { return; }
    for (const entry of entries) {
      if (found.length >= 2000) break;
      if (entry.isSymbolicLink?.()) continue;
      const name = entry.name;
      if (name === '.git' || name === 'node_modules' || name === '.venv' || name === 'venv' || name === '__pycache__' || name === 'fixtures' || name === 'helpers' || name === 'target') continue;
      const rel = relPrefix ? `${relPrefix}/${name}` : name;
      if (entry.isDirectory?.()) walk(join(absDir, name), rel, depth + 1);
      else if (entry.isFile?.() && canonicalRepoPath(rel) && TEST_FILE_RE.test(rel)) found.push(rel);
    }
  };
  walk(treeDir, '', 0);
  return found.sort();
}

/**
 * #3561 Path `b` pure-refactor equivalence verifier:
 * Runs untouched base-owned test/vector suites against BOTH `baseTree` and `headTree` and compares
 * structured reports via `diffTestReports` so pure structural refactors cannot silently break behavior.
 */
export async function runRefactorEquivalenceCheck({
  baseTree,
  headTree,
  changedFiles = [],
  env = process.env,
  execFn = null,
  timeoutMs = 120_000,
  fs = nativeFs,
} = {}) {
  const notApplicable = reason => ({
    applicable: false,
    status: 'not-applicable',
    verdict: 'ALLOW',
    reason,
    runnerKind: null,
    untouchedTests: [],
    baseResult: null,
    headResult: null,
    reportDiff: null,
  });
  if (!nonEmpty(baseTree) || !nonEmpty(headTree)) return notApplicable('missing_trees');
  const changedSet = new Set((Array.isArray(changedFiles) ? changedFiles : []).filter(nonEmpty));
  const baseTests = listTreeTestFilesSafe(baseTree, fs);
  const untouched = baseTests.filter(f => !changedSet.has(f) && isRegularFileNoSymlink(headTree, f, fs));
  if (!untouched.length) return notApplicable('no_untouched_base_tests');

  const detected = detectTestRunner(baseTree) ?? detectTestRunner(headTree);
  const kind = detected?.kind ?? 'node:test';
  const matchForKind = f => {
    if (kind === 'vitest') return JS_TEST_RE.test(f);
    if (kind === 'pytest') return PY_TEST_RE.test(f);
    if (kind === 'go') return GO_TEST_RE.test(f);
    if (kind === 'cargo') return RUST_TEST_RE.test(f);
    return /\.(?:mjs|cjs|js)$/i.test(f);
  };
  const selected = untouched.filter(matchForKind);
  if (!selected.length) return notApplicable('no_matching_runner_tests');

  const runExec = execFn ?? (async (command, cmdArgs, opts) => {
    try {
      const { stdout, stderr } = await execFileAsync(command, cmdArgs, opts);
      return { exitCode: 0, stdout: String(stdout ?? ''), stderr: String(stderr ?? ''), killed: false, code: null };
    } catch (err) {
      return {
        exitCode: typeof err?.code === 'number' ? err.code : 1,
        stdout: String(err?.stdout ?? ''),
        stderr: String(err?.stderr ?? ''),
        killed: Boolean(err?.killed),
        code: typeof err?.code === 'string' ? err.code : null,
        message: String(err?.message ?? ''),
      };
    }
  });

  const escapeXml = s => String(s ?? '').replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
  const buildMergedJunitXml = (name, cases) => {
    const failed = cases.filter(c => c.status === 'fail' || c.status === 'error').length;
    const skipped = cases.filter(c => c.status === 'skip').length;
    const body = cases.map(c => {
      const tag = `<testcase classname="${escapeXml(name)}" name="${escapeXml(c.id)}"`;
      if (c.status === 'fail' || c.status === 'error') return `${tag}><failure message="failed"/></testcase>`;
      if (c.status === 'skip') return `${tag}><skipped/></testcase>`;
      return `${tag}/>`;
    }).join('');
    return `<testsuites><testsuite name="${escapeXml(name)}" tests="${cases.length}" failures="${failed}" skipped="${skipped}">${body}</testsuite></testsuites>`;
  };

  const tempDir = fs.mkdtempSync(join(tmpdir(), 'pdd-refactor-eq-'));
  try {
    const runOnTree = async (treeDir, label) => {
      const runEnv = buildRunnerEnv(kind, treeDir, { ...scrubChildEnv(env), CI: 'true' });
      delete runEnv.NODE_TEST_CONTEXT;
      delete runEnv.NODE_OPTIONS;

      // Isolate Python formal test files into separate pytest subprocesses (prevents Z3 main_ctx deadlocks).
      const formalPyFiles = kind === 'pytest' ? selected.filter(f => PY_FORMAL_TEST_RE.test(f)) : [];
      if (kind === 'pytest' && formalPyFiles.length > 0 && selected.length > 1) {
        const regularFiles = selected.filter(f => !PY_FORMAL_TEST_RE.test(f));
        const batches = [...(regularFiles.length ? [regularFiles] : []), ...formalPyFiles.map(f => [f])];
        const pytestBin = resolvePytestBinary(treeDir);
        const commands = [];
        const allCases = [];
        let worstExit = 0;
        let allParsed = true;
        for (let idx = 0; idx < batches.length; idx += 1) {
          const junitPath = join(tempDir, `${label}-${idx}.xml`);
          const inv = buildRunnerInvocation('pytest', { root: treeDir, files: batches[idx], junitPath, pytestBin });
          commands.push(`${inv.bin} ${inv.args.join(' ')}`);
          const res = await runExec(inv.bin, inv.args, { cwd: treeDir, env: runEnv, timeout: timeoutMs, maxBuffer: 8 * 1024 * 1024 });
          if (res.killed || res.code === 'ENOENT') {
            return { command: commands.join(' && '), exitCode: res.exitCode, killed: Boolean(res.killed), code: res.code ?? null, parsed: { ok: false, counts: null }, cases: allCases, rawReport: null };
          }
          if (res.exitCode !== 0 && worstExit === 0) worstExit = res.exitCode;
          const junitXml = readOptionalXmlReport(fs, junitPath);
          const batchParsed = parsePolyglotBatchReport({ kind: 'pytest', reportFormat: inv.reportFormat, stdout: res.stdout, stderr: res.stderr, junitXml });
          if (!batchParsed.parsed?.ok) allParsed = false;
          allCases.push(...batchParsed.cases);
        }
        const passed = allCases.filter(c => c.status === 'pass').length;
        const failed = allCases.filter(c => c.status === 'fail' || c.status === 'error').length;
        const skipped = allCases.filter(c => c.status === 'skip').length;
        return {
          command: commands.join(' && '),
          exitCode: worstExit,
          killed: false,
          code: null,
          parsed: allParsed ? { ok: true, complete: true, format: 'junit', cases: allCases, counts: { total: allCases.length, passed, failed, skipped } } : { ok: false, complete: false, cases: allCases, counts: null },
          cases: allCases,
          rawReport: allParsed ? buildMergedJunitXml(label, allCases) : null,
        };
      }

      const junitPath = (kind === 'pytest' || kind === 'vitest') ? join(tempDir, `${label}.xml`) : null;
      const inv = buildRunnerInvocation(kind, { root: treeDir, files: selected, junitPath });
      const res = await runExec(inv.bin, inv.args, { cwd: treeDir, env: runEnv, timeout: timeoutMs, maxBuffer: 8 * 1024 * 1024 });
      const junitXml = readOptionalXmlReport(fs, junitPath);
      const { parsed, cases, rawReport } = parsePolyglotBatchReport({
        kind,
        reportFormat: inv.reportFormat,
        stdout: res.stdout,
        stderr: res.stderr,
        junitXml,
      });
      return {
        command: `${inv.bin} ${inv.args.join(' ')}`,
        exitCode: res.exitCode,
        killed: Boolean(res.killed),
        code: res.code ?? null,
        parsed,
        cases,
        rawReport,
      };
    };

    const baseResult = await runOnTree(baseTree, 'base');
    const headResult = await runOnTree(headTree, 'head');

    if (baseResult.killed || headResult.killed || baseResult.code === 'ENOENT' || headResult.code === 'ENOENT') {
      return {
        applicable: true,
        status: 'unknown',
        verdict: 'HOLD',
        reason: 'refactor_equivalence_runner_unavailable',
        runnerKind: kind,
        untouchedTests: selected,
        baseResult,
        headResult,
        reportDiff: null,
      };
    }

    if (baseResult.exitCode !== 0) {
      return {
        applicable: true,
        status: 'fail',
        verdict: 'HOLD',
        reason: `refactor_base_failed:exit_${baseResult.exitCode}`,
        runnerKind: kind,
        untouchedTests: selected,
        baseResult,
        headResult,
        reportDiff: null,
      };
    }

    if (!baseResult.parsed?.ok || !headResult.parsed?.ok || !baseResult.rawReport || !headResult.rawReport) {
      return {
        applicable: true,
        status: 'unknown',
        verdict: 'HOLD',
        reason: 'refactor_equivalence_unparsed_report',
        runnerKind: kind,
        untouchedTests: selected,
        baseResult,
        headResult,
        reportDiff: null,
      };
    }

    const baseTotal = baseResult.parsed.counts?.total ?? baseResult.cases.length;
    const headTotal = headResult.parsed.counts?.total ?? headResult.cases.length;
    if (baseTotal === 0 || headTotal === 0) {
      return {
        applicable: true,
        status: 'unknown',
        verdict: 'HOLD',
        reason: 'refactor_equivalence_zero_tests',
        runnerKind: kind,
        untouchedTests: selected,
        baseResult,
        headResult,
        reportDiff: null,
      };
    }

    const meta = {
      baseSha: 'refactor-equiv-base',
      policyDigest: 'refactor-equiv-policy',
      recipeDigest: computeCanonicalDigest({ kind, selected }),
      toolchain: defaultToolchainLabel(kind),
      platform: process.platform,
      profile: kind,
    };
    const reportDiff = diffTestReports({
      baseReport: baseResult.rawReport,
      headReport: headResult.rawReport,
      baseMeta: { ...meta, exitCode: baseResult.exitCode },
      headMeta: { ...meta, exitCode: headResult.exitCode },
    });

    if (headResult.exitCode !== 0 || !reportDiff || reportDiff.verdict !== 'ALLOW' || reportDiff.status !== 'pass') {
      return {
        applicable: true,
        status: 'fail',
        verdict: 'HOLD',
        reason: reportDiff && reportDiff.verdict !== 'ALLOW'
          ? `refactor_regression:${reportDiff.reason}`
          : `refactor_head_failed:exit_${headResult.exitCode}`,
        runnerKind: kind,
        untouchedTests: selected,
        baseResult,
        headResult,
        reportDiff,
      };
    }

    return {
      applicable: true,
      status: 'pass',
      verdict: 'ALLOW',
      reason: 'equivalence_verified',
      runnerKind: kind,
      untouchedTests: selected,
      baseResult,
      headResult,
      reportDiff,
    };
  } finally {
    try { fs.rmSync(tempDir, { recursive: true, force: true }); } catch {}
  }
}

function oracleCommandForRunner(detected, suiteCmd) {
  if (!detected) return nonEmpty(suiteCmd) ? suiteCmd : null;
  if (detected.kind === 'node:test') return [process.execPath, '--test', '--test-reporter=tap'];
  if (detected.kind === 'go') return ['go', 'test', '-json', './...'];
  if (detected.kind === 'cargo') return ['cargo', 'test'];
  return detected.command || suiteCmd || null;
}

const SCRIPT_EXT_RE = /\.(?:[cm]?js|[cm]?ts|sh|bash|py|rb|pl|ps1)$/i;

function tokenizeShellCommand(cmd) {
  const tokens = [];
  let cur = '';
  let quote = null;
  const src = String(cmd ?? '');
  for (let i = 0; i < src.length; i += 1) {
    const ch = src[i];
    if (quote) {
      if (ch === '\\' && quote === '"' && i + 1 < src.length) {
        cur += src[i + 1];
        i += 1;
        continue;
      }
      if (ch === quote) { quote = null; continue; }
      cur += ch;
      continue;
    }
    if (ch === '\'' || ch === '"') { quote = ch; continue; }
    if (ch === '\\' && i + 1 < src.length) { cur += src[i + 1]; i += 1; continue; }
    if (ch === '(' || ch === ')') {
      if (cur) { tokens.push(cur); cur = ''; }
      tokens.push(ch);
      continue;
    }
    if (/[\s;&|<>`]/.test(ch)) {
      if (cur) { tokens.push(cur); cur = ''; }
      continue;
    }
    cur += ch;
  }
  if (cur) tokens.push(cur);
  return tokens;
}

function recordScriptToken(raw, curDir, baseCtx, found) {
  const trimmedRaw = typeof raw === 'string' ? raw.trim() : '';
  if (!trimmedRaw || trimmedRaw.startsWith('-') || trimmedRaw.startsWith('/') || trimmedRaw.includes('\\') || trimmedRaw.includes('\0')) return;
  // Resolve raw un-collapsed operands against the trusted Git tree FIRST so symlinks before `..`
  // (e.g. `links/bench/../benchmark/file`) follow OS symlink-first traversal before collapsing `..`.
  const rawCandidates = new Set();
  if (curDir) rawCandidates.add(`${curDir}/${trimmedRaw}`);
  rawCandidates.add(trimmedRaw);
  if (baseCtx.hasBaseLookup) {
    for (const rawCand of rawCandidates) {
      const phys = resolvePhysicalBasePath(rawCand, baseCtx, { recordSymlinksInto: found });
      if (phys.ok && phys.path && !TEST_FILE_RE.test(phys.path)) {
        const targetEntry = inspectBaseEntry(phys.path, baseCtx);
        if (targetEntry?.kind === 'file' || SCRIPT_EXT_RE.test(phys.path)) {
          found.add(phys.path);
        }
      }
    }
  }
  const relCandidates = new Set();
  if (curDir) {
    const joined = normalizeCandidateRepoPath(`${curDir}/${trimmedRaw}`);
    if (joined) relCandidates.add(joined);
  }
  const rootCand = normalizeCandidateRepoPath(trimmedRaw);
  if (rootCand) relCandidates.add(rootCand);
  for (const cand of relCandidates) {
    if (TEST_FILE_RE.test(cand)) continue;
    const directEntry = baseCtx.hasBaseLookup ? inspectBaseEntry(cand, baseCtx) : null;
    if (SCRIPT_EXT_RE.test(cand)) {
      found.add(cand);
      if (!cand.includes('/') && (!baseCtx.hasBaseLookup || directEntry?.kind !== 'file')) {
        found.add(`**/${cand}`);
      }
    } else if (directEntry?.kind === 'file') {
      found.add(cand);
    }
    if (baseCtx.hasBaseLookup && directEntry?.kind !== 'file') {
      const phys = resolvePhysicalBasePath(cand, baseCtx, { recordSymlinksInto: found });
      if (phys.ok && phys.path && phys.path !== cand && !TEST_FILE_RE.test(phys.path)) {
        const targetEntry = inspectBaseEntry(phys.path, baseCtx);
        if (targetEntry?.kind === 'file' || SCRIPT_EXT_RE.test(phys.path)) {
          found.add(phys.path);
        }
      }
    }
  }
}

function scanCommandScripts(cmd, initialDir, initialPrevDir, depth, baseCtx, found) {
  const tokens = tokenizeShellCommand(cmd);
  let curDir = initialDir;
  let prevDir = initialPrevDir;
  const dirStack = [];
  const subshellStack = [];
  for (let i = 0; i < tokens.length; i += 1) {
    const tok = tokens[i];
    if (tok === '(') {
      subshellStack.push({ curDir, prevDir, dirStack: [...dirStack] });
      continue;
    }
    if (tok === ')') {
      if (subshellStack.length > 0) {
        const saved = subshellStack.pop();
        curDir = saved.curDir;
        prevDir = saved.prevDir;
        dirStack.length = 0;
        dirStack.push(...saved.dirStack);
      }
      continue;
    }
    if ((tok === 'cd' || tok === 'pushd') && i + 1 < tokens.length) {
      let j = i + 1;
      let physical = false;
      let sawDashDash = false;
      while (j < tokens.length && (tokens[j] === '--' || /^-[LP]+$/.test(tokens[j]))) {
        const flag = tokens[j];
        j += 1;
        if (flag === '--') { sawDashDash = true; break; }
        for (const ch of flag.slice(1)) {
          if (ch === 'P') physical = true;
          else if (ch === 'L') physical = false;
        }
      }
      if (j < tokens.length) {
        const arg = String(tokens[j] ?? '').trim();
        if (tok === 'pushd') dirStack.push(curDir);
        if (arg === '-') {
          if (physical) {
            if (!baseCtx.hasBaseLookup) {
              baseCtx.unresolvedPhysical.push(`${tok} -P - (no trusted base tree available)`);
            } else {
              const phys = resolvePhysicalBasePath(prevDir, baseCtx, { recordSymlinksInto: found, requireDirectory: true });
              if (!phys.ok) {
                baseCtx.unresolvedPhysical.push(`${tok} -P - (${phys.reason})`);
              } else {
                prevDir = curDir;
                curDir = phys.path;
              }
            }
          } else {
            const next = prevDir;
            prevDir = curDir;
            curDir = next;
          }
        } else if (!sawDashDash && arg.startsWith('-')) {
          baseCtx.unresolvedPhysical.push(`${tok} ${arg} (unsupported flag)`);
        } else if (arg && !arg.startsWith('/') && !arg.includes('\\') && !arg.includes('\0')) {
          const rawDir = curDir ? `${curDir}/${arg}` : arg;
          if (physical) {
            if (!baseCtx.hasBaseLookup) {
              baseCtx.unresolvedPhysical.push(`${tok} -P ${arg} (no trusted base tree available)`);
            } else {
              const phys = resolvePhysicalBasePath(rawDir, baseCtx, { recordSymlinksInto: found, requireDirectory: true });
              if (!phys.ok) {
                baseCtx.unresolvedPhysical.push(`${tok} -P ${arg} (${phys.reason})`);
              } else {
                prevDir = curDir;
                curDir = phys.path;
              }
            }
          } else {
            const normDir = posix.normalize(rawDir).replace(/^(?:\.\/)+/, '');
            if (normDir === '.' || normDir === '') {
              prevDir = curDir;
              curDir = '';
            } else if (!normDir.startsWith('..')) {
              prevDir = curDir;
              curDir = normDir;
            }
          }
        }
        i = j;
        continue;
      }
    }
    if (tok === 'popd') {
      if (dirStack.length > 0) {
        prevDir = curDir;
        curDir = dirStack.pop();
      }
      continue;
    }
    recordScriptToken(tok, curDir, baseCtx, found);
    const eqIdx = tok.indexOf('=');
    if (eqIdx > 0 && eqIdx < tok.length - 1) {
      recordScriptToken(tok.slice(eqIdx + 1), curDir, baseCtx, found);
    }
    const cleanToken = tok.replace(/^(?:\.\/)+/, '');
    const exactBaseFile = Boolean(
      baseCtx.hasBaseLookup
      && cleanToken
      && !cleanToken.startsWith('-')
      && !cleanToken.startsWith('/')
      && !cleanToken.includes('..')
      && !cleanToken.includes('\\')
      && !cleanToken.includes('\0')
      && (fileExistsInBase(cleanToken, baseCtx) || (curDir && fileExistsInBase(normalizeCandidateRepoPath(`${curDir}/${cleanToken}`), baseCtx))),
    );
    // Recurse into nested shell commands (e.g. `sh -c '...'`) inheriting curDir and prevDir (OLDPWD) without mutating parent state.
    if (depth < 3 && !exactBaseFile && /[\s"'`=<>|&;()]/.test(tok)) {
      scanCommandScripts(tok, curDir, prevDir, depth + 1, baseCtx, found);
    }
  }
}

function readGitHeadSha(cwd) {
  if (!nonEmpty(cwd)) return null;
  try {
    const res = spawnSync('git', ['rev-parse', '--verify', 'HEAD^{commit}'], {
      cwd, encoding: 'utf8', timeout: 5000, stdio: ['ignore', 'pipe', 'ignore'],
    });
    const sha = String(res.stdout ?? '').trim();
    return res.status === 0 && GIT_SHA_RE.test(sha) ? sha : null;
  } catch { return null; }
}

function inspectBaseEntry(relPath, baseCtx) {
  if (!relPath || relPath.startsWith('/') || relPath.includes('\0')) return null;
  if (baseCtx.entryCache.has(relPath)) return baseCtx.entryCache.get(relPath);
  let entry = null;
  // When a verified merge-base commit SHA is known, consult ONLY the case-sensitive Git commit object
  // (never local filesystem lstatSync, which can false-match untracked files or macOS case-insensitive names).
  if (baseCtx.baseTipValid) {
    const gitCwd = baseCtx.headTree || baseCtx.baseTree;
    if (gitCwd) {
      try {
        const res = spawnSync('git', ['--literal-pathspecs', 'ls-tree', '--full-tree', '-z', baseCtx.baseTip, '--', relPath], {
          cwd: gitCwd, encoding: 'utf8', timeout: 3000, stdio: ['ignore', 'pipe', 'ignore'],
        });
        if (res.status === 0) {
          const rec = String(res.stdout ?? '').split('\0').find(Boolean);
          const tabIdx = rec ? rec.indexOf('\t') : -1;
          if (tabIdx > 0 && rec.slice(tabIdx + 1) === relPath) {
            const [mode, type] = rec.slice(0, tabIdx).split(/\s+/);
            if (mode === '120000' && type === 'blob') {
              const tgt = spawnSync('git', ['cat-file', '-p', `${baseCtx.baseTip}:${relPath}`], {
                cwd: gitCwd, encoding: 'utf8', timeout: 3000, stdio: ['ignore', 'pipe', 'ignore'],
              });
              entry = { kind: 'symlink', target: tgt.status === 0 ? String(tgt.stdout ?? '') : null };
            } else if (type === 'blob') {
              entry = { kind: 'file' };
            } else if (type === 'tree') {
              entry = { kind: 'dir' };
            }
          }
        }
      } catch { entry = null; }
    }
  } else if (baseCtx.baseTree) {
    try {
      const full = join(baseCtx.baseTree, relPath);
      const st = baseCtx.fs.lstatSync(full);
      if (st.isSymbolicLink()) {
        let target = null;
        try { target = baseCtx.fs.readlinkSync(full); } catch { target = null; }
        entry = { kind: 'symlink', target };
      } else if (st.isFile()) {
        entry = { kind: 'file' };
      } else if (st.isDirectory()) {
        entry = { kind: 'dir' };
      }
    } catch { entry = null; }
  }
  baseCtx.entryCache.set(relPath, entry);
  return entry;
}

function fileExistsInBase(relPath, baseCtx) {
  return inspectBaseEntry(relPath, baseCtx)?.kind === 'file';
}

function resolvePhysicalBasePath(rawPath, baseCtx, { recordSymlinksInto = null, requireDirectory = false } = {}) {
  const clean = String(rawPath ?? '');
  if (!clean) return { ok: true, path: '' };
  if (clean.startsWith('/') || clean.includes('\0') || clean.includes('\\')) {
    return { ok: false, reason: 'invalid-path' };
  }
  const queue = clean.split('/').filter(Boolean);
  const resolved = [];
  let hops = 0;
  while (queue.length > 0) {
    const seg = queue.shift();
    if (seg === '.') continue;
    if (seg === '..') {
      if (resolved.length === 0) return { ok: false, reason: 'escapes-repo' };
      resolved.pop();
      continue;
    }
    const candidate = resolved.length ? `${resolved.join('/')}/${seg}` : seg;
    const entry = baseCtx.hasBaseLookup ? inspectBaseEntry(candidate, baseCtx) : null;
    if (entry?.kind === 'symlink') {
      if (recordSymlinksInto && !TEST_FILE_RE.test(candidate)) recordSymlinksInto.add(candidate);
      hops += 1;
      if (hops > 16) return { ok: false, reason: 'symlink-loop' };
      const target = typeof entry.target === 'string' ? entry.target : '';
      if (!target || target.startsWith('/') || target.includes('\0') || target.includes('\\')) {
        return { ok: false, reason: 'external-or-unreadable-symlink' };
      }
      queue.unshift(...target.split('/').filter(Boolean));
      continue;
    }
    if (requireDirectory || queue.length > 0) {
      if (!entry) return { ok: false, reason: 'missing-directory' };
      if (entry.kind !== 'dir') return { ok: false, reason: `not-a-directory:${entry.kind}` };
    }
    resolved.push(seg);
  }
  return { ok: true, path: resolved.join('/') };
}

function normalizeCandidateRepoPath(raw) {
  if (typeof raw !== 'string') return '';
  const trimmed = raw.trim();
  if (!trimmed || trimmed.startsWith('-') || trimmed.startsWith('/') || trimmed.includes('\\') || trimmed.includes('\0')) return '';
  const norm = posix.normalize(trimmed).replace(/^(?:\.\/)+/, '');
  if (!norm || norm === '.' || norm === '..' || norm.startsWith('../')) return '';
  return norm;
}

function extractRecipeScriptPaths(baseVerify, { headTree = null, baseTree = null, baseTip = null, baseTipValid = false, fs = nativeFs } = {}) {
  const found = new Set();
  const commands = [
    ...(nonEmpty(baseVerify?.test) ? [baseVerify.test] : []),
    ...(nonEmpty(baseVerify?.formalCommand) ? [baseVerify.formalCommand] : []),
    ...(nonEmpty(baseVerify?.mutationCommand) ? [baseVerify.mutationCommand] : []),
    ...(Array.isArray(baseVerify?.paths) ? baseVerify.paths.map(p => p?.run).filter(nonEmpty) : []),
  ];
  const hasBaseLookup = Boolean((baseTipValid && (headTree || baseTree)) || (!baseTipValid && baseTree));
  const baseCtx = { hasBaseLookup, headTree, baseTree, baseTip, baseTipValid, fs, entryCache: new Map(), unresolvedPhysical: [] };
  for (const cmd of commands) {
    scanCommandScripts(cmd, '', '', 0, baseCtx, found);
  }
  return { paths: [...found].sort(), unresolved: [...baseCtx.unresolvedPhysical] };
}

function redactTextWithValues(text, sandbox, secretValues = []) {
  if (typeof text !== 'string') return text;
  let out = sandbox && typeof sandbox.redact === 'function' ? sandbox.redact(text) : text;
  for (const secret of secretValues) {
    if (secret && out.includes(secret)) out = out.split(secret).join('[redacted]');
  }
  return out;
}

function deepRedactValue(value, sandbox, secretValues = [], depth = 0, seen = new WeakSet()) {
  // Unconditional fail-closed depth cap BEFORE type dispatch: no value beyond depth 64 survives unredacted.
  if (depth > 64) return '[redacted]';
  if (value === null || value === undefined) return value;
  if (typeof value === 'string') return redactTextWithValues(value, sandbox, secretValues);
  if (typeof value !== 'object') return value;
  if (seen.has(value)) return '[redacted]';
  seen.add(value);
  try {
    if (Array.isArray(value)) {
      return value.map(item => deepRedactValue(item, sandbox, secretValues, depth + 1, seen));
    }
    const out = {};
    for (const [k, v] of Object.entries(value)) {
      const redactedKey = redactTextWithValues(k, sandbox, secretValues);
      out[redactedKey] = deepRedactValue(v, sandbox, secretValues, depth + 1, seen);
    }
    return out;
  } finally {
    seen.delete(value);
  }
}

function redactProveReceipt(receipt, sandbox, secretValues = []) {
  // Returns receipt unchanged only when neither sandbox nor injected secret values exist.
  if (!receipt || (!sandbox && !secretValues.length)) return receipt;
  return deepRedactValue(receipt, sandbox, secretValues, 0, new WeakSet());
}

/**
 * Real production evidence collector invoked on every Autopilot merge check (`runValidatorV2Gate`).
 * - Reads `verify` config strictly from merge-base `pdd.json` (never untrusted PR-head edits), failing closed
 *   when base policy is unreadable or invalid (never falling back to no-map advisory mode on error).
 * - Invokes real `runProve` when merge-base `verify.paths` is configured, isolating each recipe's `account:*`
 *   credentials strictly by `(phase, recipeId)` via `ports.envForStep` ONLY when `reviewApproved: true`.
 * - Runs G3 polyglot `diffTestReports` with distinct `baseMeta` / `headMeta` and un-spoofable comparator veto,
 *   plus `runBaseOwnedTestOracle`.
 * - Enforces Check 4 protected paths unconditionally in Autopilot (including deletions, renames, gate modules,
 *   and trusted recipe scripts) with zero fabricated approvals or receipts.
 */
export async function collectLiveEvidenceContract({
  repo = 'local/repo',
  job = {},
  headTree = null,
  suiteTree = null,
  baseTree = null,
  baseTip = null,
  changedFiles = [],
  allTouchedFiles = null,
  changedFilesError = false,
  suite = null,
  suiteCmd = 'npm test',
  suiteLog = '',
  baseReport = null,
  headReport = null,
  baseReportMeta = null,
  headReportMeta = null,
  env = process.env,
  fs = nativeFs,
  probeOptions = {},
  testEnvPath = null,
  runProveFn = runProve,
  runOracleFn = runBaseOwnedTestOracle,
  runFormalFn = runFormalVerification,
  runEquivalenceFn = runRefactorEquivalenceCheck,
  isPathBPureRefactor = false,
  strictWithoutVerifyPaths = false,
} = {}) {
  const cleanRepo = nonEmpty(repo) ? repo.trim() : 'local/repo';
  const cleanHead = nonEmpty(job?.head) ? job.head.trim() : '0'.repeat(40);
  const cleanBaseTip = nonEmpty(baseTip) ? baseTip.trim() : 'base-unresolved';
  const cleanFiles = [...new Set((Array.isArray(changedFiles) ? changedFiles : []).filter(nonEmpty))].sort();
  const protectedCheckFiles = [...new Set([
    ...cleanFiles,
    ...(Array.isArray(allTouchedFiles) ? allTouchedFiles.filter(nonEmpty) : []),
  ])].sort();
  const effectiveSuiteCmd = nonEmpty(suiteCmd) ? suiteCmd.trim() : 'npm test';
  const baseTipValid = GIT_SHA_RE.test(cleanBaseTip);

  // 1. Load verify config strictly from trusted merge-base (`baseTip:pdd.json` or verified `baseTree/pdd.json`).
  // Enter no-map advisory mode ONLY after establishing the trusted base genuinely has no verify.paths.
  let baseVerify = { configured: false, source: 'pdd.json', test: null, report: null, paths: [], errors: [], loadStatus: 'unreadable' };
  if (headTree && baseTipValid) {
    baseVerify = loadVerifyConfig(headTree, { gitRef: cleanBaseTip });
  }
  if (baseVerify.loadStatus === 'unreadable' && baseTree) {
    // Only trust a fallback baseTree when either no commit SHA was requested OR baseTree actually points at cleanBaseTip;
    // when baseTree is inside a Git checkout matching cleanBaseTip, load from the commit object so subdirs cannot miss root pdd.json.
    const baseTreeHead = readGitHeadSha(baseTree);
    if (baseTipValid && baseTreeHead !== null && baseTreeHead.toLowerCase() === cleanBaseTip.toLowerCase()) {
      baseVerify = loadVerifyConfig(baseTree, { gitRef: cleanBaseTip });
    } else if (!baseTipValid) {
      baseVerify = baseTreeHead ? loadVerifyConfig(baseTree, { gitRef: baseTreeHead }) : loadVerifyConfig(baseTree);
    }
  }
  const basePolicyInvalid = baseVerify.loadStatus === 'invalid'
    || (Array.isArray(baseVerify.errors) && baseVerify.errors.length > 0);
  const basePolicyUnreadable = !basePolicyInvalid && baseVerify.loadStatus === 'unreadable';
  const hasVerifyPaths = !basePolicyInvalid
    && !basePolicyUnreadable
    && baseVerify.configured
    && Array.isArray(baseVerify.paths)
    && baseVerify.paths.length > 0;
  const recipeScripts = extractRecipeScriptPaths(baseVerify, { headTree, baseTree, baseTip: cleanBaseTip, baseTipValid, fs });
  const recipeProtectedPatterns = recipeScripts.unresolved.length > 0
    ? [...new Set([...recipeScripts.paths, '**'])]
    : recipeScripts.paths;
  const { matched, changedSurfaces, unmappedSurfaces } = matchVerifyPaths(baseVerify, cleanFiles);

  // 2. Load 0600 test-env metadata & probe host capabilities ONLY when merge-base verify.paths (or explicit probeOptions) need them;
  // inject sandbox credentials ONLY post-review and strictly keyed by unique `recipe.id` via `ports.envForStep`.
  const hasCustomProbeOptions = isObj(probeOptions) && Object.keys(probeOptions).length > 0;
  const shouldLoadTestEnv = hasVerifyPaths || hasCustomProbeOptions || nonEmpty(testEnvPath);
  const rawTestEnv = shouldLoadTestEnv
    ? loadAutopilotTestEnv({ filePath: testEnvPath, env, fs })
    : { ok: false, path: null, accounts: {}, errors: [] };
  if (rawTestEnv.ok === true) registerTestEnvSecrets(rawTestEnv);
  const availableCapabilities = (hasVerifyPaths || hasCustomProbeOptions)
    ? probeCachedCapabilities({ rawTestEnv, env, probeOptions })
    : [];
  const testEnvMeta = summarizeTestEnvMetadata(rawTestEnv);

  const reviewApproved = job?.review?.verdict === 'PASS'
    && nonEmpty(job?.review?.head)
    && job.review.head.trim().toLowerCase() === cleanHead.toLowerCase();
  const neededAccounts = [...new Set(
    matched.flatMap(r => r.needs ?? [])
      .filter(c => typeof c === 'string' && c.startsWith('account:'))
      .map(c => c.slice('account:'.length))
      .filter(Boolean),
  )];
  let postReviewSandbox = null;
  const recipeSandboxesById = new Map();
  if (hasVerifyPaths && neededAccounts.length > 0 && reviewApproved && rawTestEnv.ok === true) {
    postReviewSandbox = buildPostReviewSandboxEnv({
      baseEnv: env,
      testEnv: rawTestEnv,
      reviewApproved: true,
      approvedHead: job.review.head,
      currentHead: cleanHead,
      allowedAccounts: neededAccounts,
    });
    for (const m of matched) {
      const recipeAccounts = [...new Set(
        (m.needs ?? [])
          .filter(c => typeof c === 'string' && c.startsWith('account:'))
          .map(c => c.slice('account:'.length))
          .filter(Boolean),
      )];
      if (recipeAccounts.length > 0) {
        recipeSandboxesById.set(m.id, buildPostReviewSandboxEnv({
          baseEnv: env,
          testEnv: rawTestEnv,
          reviewApproved: true,
          approvedHead: job.review.head,
          currentHead: cleanHead,
          allowedAccounts: recipeAccounts,
        }));
      }
    }
  } else if (neededAccounts.length > 0 && !reviewApproved) {
    // Never treat account:* credentials as usable before blind review approves this exact head!
    for (const acct of neededAccounts) {
      const idx = availableCapabilities.indexOf(`account:${acct}`);
      if (idx >= 0) availableCapabilities.splice(idx, 1);
    }
  }

  // 3. Build deterministic 13-field contract bindings.
  const detectedHeadRunner = (suiteTree ? detectTestRunner(suiteTree) : null) ?? (headTree ? detectTestRunner(headTree) : null);
  const detectedBaseRunner = (baseTree ? detectTestRunner(baseTree) : null) ?? detectedHeadRunner;
  const toolchain = defaultToolchainLabel(detectedHeadRunner?.kind ?? null);
  const baseToolchain = defaultToolchainLabel(detectedBaseRunner?.kind ?? null);
  const integratedTree = readGitTreeSha(headTree, 'HEAD')
    ?? computeCanonicalDigest({ head: cleanHead, files: cleanFiles }).slice(0, 40);
  const acRevision = computeCanonicalDigest({
    issue: job?.issue ?? null,
    title: job?.title ?? '',
    body: job?.body ?? '',
  }).slice(0, 16);
  const trustedPolicyDigest = computeCanonicalDigest({
    baseTip: cleanBaseTip,
    verify: baseVerify.configured
      ? {
          test: baseVerify.test,
          report: baseVerify.report,
          formalCommand: baseVerify.formalCommand ?? null,
          mutationCommand: baseVerify.mutationCommand ?? null,
          paths: baseVerify.paths.map(p => ({ id: p.id, when: p.when, run: p.run, needs: p.needs })),
        }
      : null,
  });
  const recipeDigest = computeCanonicalDigest({
    suiteCmd: effectiveSuiteCmd,
    matched: matched.map(m => ({ id: m.id, run: m.run, needs: m.needs })),
  });
  const expectedBinding = {
    repo: cleanRepo,
    acRevision,
    targetTip: cleanBaseTip,
    candidateHead: cleanHead,
    integratedTree,
    trustedPolicyDigest,
    recipeDigest,
  };

  // 4. Parse head/base structured test reports (reading merge-base configured verify.report from suiteTree first,
  // then headTree; always auto-detecting JUnit/TAP/Go/Cargo format) & run G3 polyglot diffTestReports with
  // distinct baseMeta and headMeta so platform/toolchain/SHA/shard mismatches are always caught.
  const strictMode = hasVerifyPaths || strictWithoutVerifyPaths === true;
  const readConfiguredReport = (...treeDirs) => {
    if (!baseVerify.report) return null;
    for (const dir of treeDirs) {
      if (!nonEmpty(dir)) continue;
      try {
        const text = readSafeUtf8(dir, baseVerify.report);
        if (nonEmpty(text)) return text;
      } catch { /* try next candidate tree */ }
    }
    return null;
  };
  const resolvedHeadReport = headReport !== null && headReport !== undefined
    ? headReport
    : (baseVerify.report ? readConfiguredReport(suiteTree, headTree) : (nonEmpty(suiteLog) ? suiteLog : null));
  const resolvedBaseReport = baseReport !== null && baseReport !== undefined
    ? baseReport
    : (baseVerify.report ? readConfiguredReport(baseTree) : null);
  const reportParseFormat = (baseVerify.report || (headReport !== null && headReport !== undefined))
    ? 'auto'
    : (detectedHeadRunner?.reportFormat ?? 'auto');
  const parsedHead = nonEmpty(resolvedHeadReport)
    ? parseStandardTestReport(resolvedHeadReport, reportParseFormat)
    : { ok: false, cases: [] };
  let reportDiff = null;
  if (nonEmpty(resolvedBaseReport) && nonEmpty(resolvedHeadReport)) {
    const rawBaseMeta = isObj(baseReportMeta) ? baseReportMeta : (isObj(job?.baseTestReportMeta) ? job.baseTestReportMeta : {});
    const rawHeadMeta = isObj(headReportMeta) ? headReportMeta : (isObj(job?.headTestReportMeta) ? job.headTestReportMeta : {});
    const effectiveBaseMeta = {
      baseSha: cleanBaseTip,
      policyDigest: trustedPolicyDigest,
      recipeDigest,
      toolchain: baseToolchain,
      platform: process.platform,
      profile: detectedBaseRunner?.kind ?? 'default',
      format: reportParseFormat,
      ...rawBaseMeta,
    };
    const effectiveHeadMeta = {
      baseSha: cleanBaseTip,
      policyDigest: trustedPolicyDigest,
      recipeDigest,
      toolchain,
      platform: process.platform,
      profile: detectedHeadRunner?.kind ?? 'default',
      format: reportParseFormat,
      ...rawHeadMeta,
    };
    reportDiff = diffTestReports({
      baseReport: resolvedBaseReport,
      headReport: resolvedHeadReport,
      baseMeta: effectiveBaseMeta,
      headMeta: effectiveHeadMeta,
      approvedRemovals: Array.isArray(job?.approvedTestRemovals) ? job.approvedTestRemovals : [],
    });
  }

  const testResults = [];
  const expectedTestIds = [];
  const reportReadErrors = [];
  if (parsedHead.ok && parsedHead.cases.length > 0) {
    for (const c of parsedHead.cases) {
      testResults.push({
        id: c.id,
        status: c.status === 'pass' ? 'pass' : (c.status === 'skip' ? 'skip' : 'fail'),
        source: 'harness',
      });
    }
  } else if (strictMode && (Boolean(baseVerify.report) || (headReport !== null && headReport !== undefined))) {
    // Missing, empty, or unreadable configured/supplied test report MUST fail closed independently of test IDs.
    reportReadErrors.push('report:unreadable');
    testResults.push({ id: 'report:unreadable', status: 'unknown', source: 'harness' });
  }
  if (strictMode && Boolean(baseVerify.report) && !nonEmpty(resolvedBaseReport)) {
    // Configured verify.report without a base baseline MUST fail closed independently of test IDs.
    reportReadErrors.push('report:base-missing');
    testResults.push({ id: 'report:base-missing', status: 'unknown', source: 'harness' });
  } else if (baseReport !== null && baseReport !== undefined && !nonEmpty(resolvedBaseReport)) {
    // Explicitly supplied empty/whitespace base report MUST fail closed in both strict and advisory modes.
    reportReadErrors.push('report:base-empty');
    testResults.push({ id: 'report:base-empty', status: 'unknown', source: 'harness' });
  }
  let reportDiffVerdict = null;
  if (reportDiff) {
    reportDiffVerdict = {
      verdict: reportDiff.verdict,
      status: reportDiff.status,
      reason: reportDiff.reason,
    };
    for (const id of reportDiff.missingIds) expectedTestIds.push(id);
    for (const id of reportDiff.newlySkippedIds) {
      testResults.push({ id, status: 'skip', source: 'harness' });
    }
    for (const id of reportDiff.newlyFailingIds) {
      testResults.push({ id, status: 'fail', source: 'harness' });
    }
    // Always append comparator HOLD unconditionally (never skipping on test-ID collision) AND pass `reportDiffVerdict`.
    if (reportDiff.verdict !== 'ALLOW' || reportDiff.status !== 'pass') {
      const diffStatus = reportDiff.status === 'fail' ? 'fail' : 'unknown';
      testResults.push({ id: `report-diff:${reportDiff.status || 'hold'}`, status: diffStatus, source: 'harness' });
    }
  }

  // 5. Run G3 base-owned edited-test oracle when existing base test files were modified on a runnable/configured repo.
  const editedTestFiles = cleanFiles.filter(f => TEST_FILE_RE.test(f));
  const editedExistingBaseTests = baseTree
    ? editedTestFiles.filter(rel => {
        try { return fs.existsSync(join(baseTree, rel)); } catch { return false; }
      })
    : [];
  const shouldRunBaseOracle = Boolean(
    editedExistingBaseTests.length > 0
    && baseTree
    && headTree
    && !changedFilesError
    && (hasVerifyPaths || parsedHead.ok || runOracleFn !== runBaseOwnedTestOracle),
  );
  let baseOracle = null;
  let oracleResult = null;
  if (shouldRunBaseOracle) {
    const oracleCmd = oracleCommandForRunner(detectedHeadRunner, baseVerify.test || effectiveSuiteCmd);
    oracleResult = await runOracleFn({
      baseTree,
      headTree,
      editedTestFiles: editedExistingBaseTests,
      testCommand: oracleCmd,
      intendedChanges: Array.isArray(job?.intendedTestChanges) ? job.intendedTestChanges : [],
      format: detectedHeadRunner?.reportFormat ?? 'auto',
      env,
    });
    baseOracle = {
      status: oracleResult.status === 'pass' ? 'passed' : (oracleResult.status === 'fail' ? 'failed' : 'unknown'),
      unlistedFailures: (oracleResult.regressions ?? []).map(r => (typeof r === 'string' ? r : r.id)).filter(Boolean),
      unknowns: oracleResult.status === 'unknown' ? [oracleResult.reason || 'oracle_unknown'] : [],
    };
  }

  // 6. Execute live `pdd prove` when merge-base `verify.paths` is configured and diff/checkouts are valid;
  // fail closed on diff error, unreadable/invalid base policy, or unavailable head checkout; enter no-map
  // advisory mode ONLY when trusted base policy was verified absent/unconfigured with zero errors.
  let proveResult = null;
  let proveOutcome = OUTCOME_NOT_PROVED;
  let proveReasons = [];
  const receipts = [];
  let touchedPaths = [];
  const requiredCapabilitiesByPath = {};
  let gapCheck = null;
  let requireGapCheck = false;
  let stampReceipt = null;

  if (changedFilesError === true) {
    proveOutcome = OUTCOME_NOT_PROVED;
    proveReasons = ['Git diff failed; changed and deleted files could not be enumerated safely.'];
    gapCheck = { missingPathIds: [], unprovedAcIds: [], flags: ['INSUFFICIENT_SCOPE'] };
    requireGapCheck = true;
  } else if (basePolicyInvalid) {
    proveOutcome = OUTCOME_NOT_PROVED;
    proveReasons = baseVerify.errors.length
      ? [...baseVerify.errors]
      : ['Merge-base pdd.json verify policy is invalid.'];
    gapCheck = { missingPathIds: [], unprovedAcIds: [], flags: ['INSUFFICIENT_SCOPE'] };
    requireGapCheck = true;
  } else if (basePolicyUnreadable) {
    proveOutcome = OUTCOME_NOT_PROVED;
    proveReasons = ['Could not inspect merge-base pdd.json verify policy (missing checkout or unavailable base commit).'];
    gapCheck = { missingPathIds: [], unprovedAcIds: [], flags: ['INSUFFICIENT_SCOPE'] };
    requireGapCheck = true;
  } else if (recipeScripts.unresolved.length > 0) {
    proveOutcome = OUTCOME_NOT_PROVED;
    proveReasons = recipeScripts.unresolved.map(r => `Could not resolve physical recipe directory safely against trusted base tree: ${r}`);
    gapCheck = { missingPathIds: [], unprovedAcIds: [], flags: ['INSUFFICIENT_SCOPE'] };
    requireGapCheck = true;
  } else if (!headTree) {
    proveOutcome = OUTCOME_NOT_PROVED;
    proveReasons = ['Head checkout unavailable; cannot verify candidate changes or merge-base verify.paths recipes.'];
    gapCheck = { missingPathIds: matched.map(m => m.id), unprovedAcIds: [], flags: ['INSUFFICIENT_SCOPE'] };
    requireGapCheck = true;
  } else if (hasVerifyPaths) {
    const sink = { write() {} };
    // Collect EVERY configured account key name across rawTestEnv so inherited parent env vars can NEVER leak
    // into verify.test or sibling recipes; then inject ONLY the exact recipe's authorized keys by `(phase, recipeId)`.
    const allConfiguredAccountKeys = new Set();
    if (rawTestEnv?.ok === true && isObj(rawTestEnv.accounts)) {
      for (const vars of Object.values(rawTestEnv.accounts)) {
        if (!isObj(vars)) continue;
        for (const k of Object.keys(vars)) allConfiguredAccountKeys.add(k);
      }
    }
    const cleanProveBaseEnv = { ...(env ?? {}) };
    for (const k of allConfiguredAccountKeys) delete cleanProveBaseEnv[k];

    const injectedSecretValues = [...new Set(
      [...recipeSandboxesById.values()]
        .flatMap(sb => sb.injectedKeys.map(k => sb.env[k]))
        .filter(v => typeof v === 'string' && v.length > 0),
    )].sort((a, b) => b.length - a.length);

    const provePorts = { stdout: sink, stderr: sink };
    if ((recipeSandboxesById.size > 0 || allConfiguredAccountKeys.size > 0) && runProveFn === runProve) {
      provePorts.envForStep = ({ phase, recipeId, baseEnv }) => {
        const sanitized = { ...(baseEnv ?? {}) };
        for (const k of allConfiguredAccountKeys) delete sanitized[k];
        if (phase !== 'path' || !recipeId) return sanitized;
        const recipeSandbox = recipeSandboxesById.get(recipeId);
        if (!recipeSandbox) return sanitized;
        for (const key of recipeSandbox.injectedKeys) {
          if (typeof recipeSandbox.env[key] === 'string') sanitized[key] = recipeSandbox.env[key];
        }
        return sanitized;
      };
    }
    proveResult = await runProveFn(
      {
        cwd: headTree,
        base: baseTipValid ? cleanBaseTip : undefined,
        capabilities: availableCapabilities,
        env: cleanProveBaseEnv,
        json: true,
      },
      provePorts,
    );
    const redactText = text => redactTextWithValues(String(text ?? ''), postReviewSandbox, injectedSecretValues);
    const sanitizedReceipt = redactProveReceipt(proveResult?.receipt ?? null, postReviewSandbox, injectedSecretValues);
    if (proveResult && sanitizedReceipt) proveResult = { ...proveResult, receipt: sanitizedReceipt };

    proveOutcome = proveResult?.outcome ?? OUTCOME_NOT_PROVED;
    const proveDirty = proveResult?.receipt?.dirty === true
      || proveResult?.receipt?.proofScope === 'working-tree'
      || proveResult?.receipt?.proofScope === 'unknown';
    const rawNotProved = Array.isArray(proveResult?.receipt?.notProvedReasons) ? proveResult.receipt.notProvedReasons : [];
    const rawLintErrors = Array.isArray(proveResult?.receipt?.lint?.errors) ? proveResult.receipt.lint.errors : [];
    const rawDiffErrors = Array.isArray(proveResult?.receipt?.diff?.errors) ? proveResult.receipt.diff.errors : [];
    const testFailedReason = proveResult?.receipt?.test && proveResult.receipt.test.ok === false
      ? [`pdd prove test suite failed (exit ${proveResult.receipt.test.exitCode ?? 'null'}): ${proveResult.receipt.test.summary || ''}`.trim()]
      : [];
    const provePaths = Array.isArray(proveResult?.receipt?.paths) ? proveResult.receipt.paths : [];
    const failedPathReasons = provePaths
      .filter(p => p.status === 'failed')
      .map(p => `Verify path "${p.id}" failed (exit ${p.exitCode ?? 'null'}): ${p.summary || ''}`.trim());
    const dirtyReasons = proveDirty
      ? [proveResult?.receipt?.proofScope === 'unknown'
          ? 'Could not inspect candidate checkout cleanliness (unknown proof scope cannot authorize commit-bound merge).'
          : `Candidate checkout was dirty${Array.isArray(proveResult?.receipt?.dirtyFiles) && proveResult.receipt.dirtyFiles.length ? ` (${proveResult.receipt.dirtyFiles.slice(0, 4).join(', ')})` : ''} (working-tree proof cannot authorize commit-bound merge).`]
      : [];
    if (proveDirty && proveOutcome === OUTCOME_PROVED) proveOutcome = OUTCOME_NOT_PROVED;
    proveReasons = [...rawLintErrors, ...rawDiffErrors, ...testFailedReason, ...failedPathReasons, ...dirtyReasons, ...rawNotProved]
      .filter(nonEmpty)
      .map(redactText);

    touchedPaths = matched.map(m => m.id);
    for (const m of matched) requiredCapabilitiesByPath[m.id] = [...(m.needs ?? [])];

    for (const p of provePaths) {
      const outcome = p.status === 'proved'
        ? (proveDirty ? 'failed' : 'proved')
        : (Array.isArray(p.missingCapabilities) && p.missingCapabilities.length > 0 ? 'missing_capability' : 'failed');
      const rawSummary = redactText(p.summary ?? '');
      receipts.push({
        ...expectedBinding,
        writtenBy: 'harness',
        pathId: p.id,
        testProfile: 'verify-path',
        command: p.run || effectiveSuiteCmd,
        toolchain,
        capability: p.missingCapabilities?.[0] ?? p.needs?.[0] ?? null,
        outcome,
        artifactDigest: computeCanonicalDigest({ id: p.id, status: p.status, exitCode: p.exitCode ?? null, summary: rawSummary }),
      });
    }
    if (unmappedSurfaces.length > 0 && changedSurfaces.length > 0) {
      gapCheck = { missingPathIds: [], unprovedAcIds: [], flags: ['UNMAPPED_CHANGE'] };
      requireGapCheck = true;
    }
    const anyMissingCap = receipts.find(r => r.outcome === 'missing_capability');
    const anyFailed = receipts.find(r => r.outcome === 'failed');
    // Overall receipt outcome MUST strictly honor `proveOutcome` and clean-commit scope; NEVER stamp `proved` otherwise.
    const overallOutcome = (proveOutcome === OUTCOME_PROVED && !proveDirty)
      ? 'proved'
      : (anyMissingCap ? 'missing_capability' : 'failed');
    if (proveOutcome === OUTCOME_FAILED && !anyFailed) {
      receipts.push({
        ...expectedBinding,
        writtenBy: 'harness',
        pathId: 'pdd-prove',
        testProfile: 'pdd-prove',
        command: effectiveSuiteCmd,
        toolchain,
        capability: null,
        outcome: 'failed',
        artifactDigest: computeCanonicalDigest({ proveOutcome, proveReasons }),
      });
    } else if (proveOutcome === OUTCOME_NOT_PROVED && !anyMissingCap && !anyFailed && !gapCheck) {
      gapCheck = { missingPathIds: [], unprovedAcIds: [], flags: ['INSUFFICIENT_SCOPE'] };
      requireGapCheck = true;
    }
    stampReceipt = {
      ...expectedBinding,
      ...(touchedPaths.length ? { pathIds: touchedPaths } : {}),
      testProfile: 'pdd-prove',
      command: matched.length ? matched.map(m => m.run).join(' && ') : effectiveSuiteCmd,
      toolchain,
      capability: anyMissingCap?.capability ?? null,
      outcome: overallOutcome,
      artifactDigest: computeCanonicalDigest({
        proveOutcome,
        proveDirty,
        proveReasons,
        paths: provePaths.map(p => ({ id: p.id, status: p.status, exitCode: p.exitCode ?? null })),
        unmappedSurfaces,
      }),
    };
  } else {
    // Verified absent/unconfigured merge-base verify.paths: compatibility advisory mode (Not proved, zero forged receipts).
    proveReasons = ['No merge-base verify.paths Feature Map configured in pdd.json.'];
    if (strictWithoutVerifyPaths === true) {
      gapCheck = { missingPathIds: [], unprovedAcIds: [], flags: ['INSUFFICIENT_SCOPE'] };
      requireGapCheck = true;
    }
  }

  // Unconditional Check 4 manual merge in Autopilot: never auto-approve protected paths via job state.
  const humanApprovedPaths = [];

  // Always enumerate ALL touched Stories (including deletions from allTouchedFiles) BEFORE applying any
  // issue-level `acNotApplicableReason`; fail closed on deleted/unreadable Stories and cover every numbered criterion.
  const changedStoryFiles = strictMode ? protectedCheckFiles.filter(isLintableStoryPath) : [];
  const changedStoryAcRefs = [];
  const unreadableStoryRefs = [];
  let changedStoryCount = 0;
  if (strictMode && changedStoryFiles.length > 0) {
    for (const rel of changedStoryFiles) {
      const storyText = headTree ? readSafeUtf8(headTree, rel) : null;
      if (typeof storyText !== 'string') {
        unreadableStoryRefs.push(`${rel}#unreadable`);
        continue;
      }
      let inCriteria = false;
      let acIndex = 0;
      for (const line of storyText.split(/\r?\n/)) {
        if (/^##\s+/.test(line)) {
          inCriteria = /^##\s+Acceptance(?:\s+criteria)?\s*$/i.test(line.trim());
          continue;
        }
        if (inCriteria && /^\s*\d+[.)]\s+\S/.test(line)) {
          acIndex += 1;
          changedStoryAcRefs.push({ ref: `${rel}#AC${acIndex}`, index: acIndex });
        }
      }
      if (acIndex > 0) changedStoryCount += 1;
    }
  }
  const suppliedFrozenAcs = Array.isArray(job?.frozenAcs) ? [...job.frozenAcs] : [];
  const effectiveFrozenAcs = [...suppliedFrozenAcs];
  for (const unreadableRef of unreadableStoryRefs) {
    effectiveFrozenAcs.push({ id: unreadableRef, testIds: [], pathIds: [] });
  }
  if (changedStoryAcRefs.length > 0) {
    const singleChangedStory = changedStoryCount === 1 && unreadableStoryRefs.length === 0;
    const suppliedIdSet = new Set(
      suppliedFrozenAcs
        .map(ac => (typeof ac === 'string' ? ac : (isObj(ac) ? ac.id : '')))
        .filter(nonEmpty)
        .map(id => id.trim().toLowerCase()),
    );
    for (const item of changedStoryAcRefs) {
      const refLower = item.ref.toLowerCase();
      const matchedAc = suppliedIdSet.has(refLower)
        || (singleChangedStory && (
          suppliedIdSet.has(`ac${item.index}`)
          || suppliedIdSet.has(`ac-${item.index}`)
          || suppliedIdSet.has(String(item.index))
        ));
      if (!matchedAc) {
        effectiveFrozenAcs.push({ id: item.ref, testIds: [], pathIds: [] });
      }
    }
  }
  const hasChangedStoryRequirements = changedStoryAcRefs.length > 0 || unreadableStoryRefs.length > 0;
  const requireFrozenAcs = effectiveFrozenAcs.length > 0
    || job?.requireFrozenAcs === true
    || hasChangedStoryRequirements
    || (strictMode && !nonEmpty(job?.acNotApplicableReason) && job?.hasAcceptanceCriteria === true);

  // 7. #3151 Live code-bound formal proof wiring: reuse `proveResult.receipt.formal` when present,
  // else invoke the shared Layer-1 formal verifier whenever formal files, merge-base verify.formal_command,
  // or positive formal claims apply. Populates real `formalProofs`, `formalTargetModules`, and `requireCodeBoundFormal`.
  const rawClaimedFormalState = typeof job?.evidence?.formal?.state === 'string'
    ? job.evidence.formal.state.trim().toLowerCase()
    : null;
  const formalClaimUnchecked = Boolean(job?.unchecked?.formal);
  const claimedFormalState = formalClaimUnchecked ? 'not-run' : rawClaimedFormalState;
  const claimedSolverCode = claimedFormalState === 'proved_solver_code';
  const hasRepoProductionCode = cleanFiles.some(isProductionCodeFile)
    || (headTree ? hasAnyProductionCodeFile(headTree, fs) : false);
  const claimedCodeBound = claimedSolverCode
    || (hasRepoProductionCode && (claimedFormalState === 'proved' || claimedFormalState === 'bounded'));
  // Scrub parent secrets + all configured test-env account keys before running untrusted PR formal/refactor checks.
  const scrubbedNoAccountEnv = scrubChildEnv(env);
  if (rawTestEnv?.ok === true && isObj(rawTestEnv.accounts)) {
    for (const acctVars of Object.values(rawTestEnv.accounts)) {
      if (isObj(acctVars)) for (const k of Object.keys(acctVars)) delete scrubbedNoAccountEnv[k];
    }
  }
  let formalVerification = proveResult?.receipt?.formal ?? null;
  if (!formalVerification && headTree && !changedFilesError) {
    const scope = discoverFormalScope({
      root: headTree,
      touchedFiles: cleanFiles,
      formalCommand: baseVerify.formalCommand ?? null,
    });
    if (scope.formalFiles.length > 0 || Boolean(baseVerify.formalCommand) || claimedSolverCode) {
      formalVerification = runFormalFn({
        root: headTree,
        touchedFiles: cleanFiles,
        baseVerify,
        claimedTier: claimedCodeBound ? claimedFormalState : null,
        mutationControl: job?.formalMutationControl ?? null,
        targetModules: Array.isArray(job?.formalTargetModules) && job.formalTargetModules.length ? job.formalTargetModules : null,
        env: scrubbedNoAccountEnv,
      });
    }
  }
  const collectedFormalProofs = Array.isArray(formalVerification?.formalProofs)
    ? formalVerification.formalProofs.map(p => ({
        ...p,
        // Never falsely label a Tier-1 `bounded` property test or test-only fixture as claiming Tier-2 `proved_solver_code`,
        // while ALWAYS marking an unbound spec model that claimed code verification so checkFormalProofBinding fails closed.
        ...(p.codeBound === false && claimedCodeBound
          ? { tier: 'proved_solver_code', satisfiesCode: true, forCodeVerification: true }
          : ((p.tier === 'bounded' && !claimedSolverCode) || !claimedCodeBound
              ? { satisfiesCode: false, forCodeVerification: false }
              : {})),
      }))
    : [];
  const mergedFormalProofs = [
    ...collectedFormalProofs,
    ...(Array.isArray(job?.formalProofs) ? job.formalProofs : []),
  ];
  const mergedFormalTargetModules = [
    ...new Set([
      ...(Array.isArray(formalVerification?.targetModules) ? formalVerification.targetModules : []),
      ...(Array.isArray(job?.formalTargetModules) ? job.formalTargetModules : []),
    ]),
  ].sort();
  const requireCodeBoundFormal = job?.requireCodeBoundFormal === true
    || claimedSolverCode
    || (formalVerification?.tier === 'proved_spec_model' && claimedCodeBound);
  if (formalVerification && formalVerification.state === 'failed' && formalVerification.errors?.length) {
    for (const err of formalVerification.errors) {
      if (!proveReasons.includes(err)) proveReasons.push(err);
    }
    reportReadErrors.push('formal:failed');
    testResults.push({ id: 'formal:failed', status: 'fail', source: 'harness' });
  } else if (formalVerification && formalVerification.state === 'not-run' && formalVerification.notProvedReasons?.length && !formalClaimUnchecked) {
    for (const r of formalVerification.notProvedReasons) {
      if (!proveReasons.includes(r)) proveReasons.push(r);
    }
    reportReadErrors.push('formal:not-run');
    testResults.push({ id: 'formal:not-run', status: 'fail', source: 'harness' });
  }

  // 8. #3561 Path `b` pure-refactor equivalence: run untouched base-owned tests against base & head.
  let refactorEquivalence = null;
  if (isPathBPureRefactor === true && baseTree && headTree && !changedFilesError && cleanFiles.some(isProductionCodeFile)) {
    refactorEquivalence = await runEquivalenceFn({
      baseTree,
      headTree,
      changedFiles: cleanFiles,
      env: scrubbedNoAccountEnv,
      fs,
    });
    if (refactorEquivalence?.applicable && refactorEquivalence.verdict !== 'ALLOW') {
      reportReadErrors.push(`refactor-equivalence:${refactorEquivalence.reason || 'failed'}`);
      testResults.push({ id: `refactor-equivalence:${refactorEquivalence.reason || 'failed'}`, status: 'fail', source: 'harness' });
    }
  }

  return {
    source: 'live-production',
    verifyPathsConfigured: hasVerifyPaths,
    advisory: !strictMode && !basePolicyInvalid && !basePolicyUnreadable && Boolean(headTree) && !changedFilesError,
    proveOutcome,
    proveReasons,
    proveReceipt: proveResult?.receipt ?? null,
    formalVerification,
    refactorEquivalence,
    reportDiff,
    oracleResult,
    postReviewSandboxUsed: Boolean(postReviewSandbox),
    postReviewInjectedKeys: postReviewSandbox?.injectedKeys ?? [],
    testEnvMeta,
    availableCapabilities,
    contractInput: {
      changedFiles: protectedCheckFiles,
      humanApprovedPaths,
      protectedPatterns: recipeProtectedPatterns,
      frozenAcs: effectiveFrozenAcs,
      requireFrozenAcs,
      touchedPaths,
      receipts,
      expectedBinding,
      availableCapabilities,
      requiredCapabilitiesByPath,
      testResults,
      expectedTestIds,
      approvedSkippedIds: Array.isArray(job?.approvedSkippedIds) ? job.approvedSkippedIds : [],
      baseOracle,
      editedTestFiles: shouldRunBaseOracle ? editedExistingBaseTests : [],
      requireBaseOracle: shouldRunBaseOracle,
      reportDiffVerdict,
      reportReadErrors,
      gapCheck,
      requireGapCheck,
      formalProofs: mergedFormalProofs,
      formalTargetModules: mergedFormalTargetModules,
      requireCodeBoundFormal,
      stampReceipt,
      postStandaloneReceiptComment: strictMode,
    },
  };
}
