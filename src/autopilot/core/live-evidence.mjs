// Prompt: prompts/cli/autopilot-validator.prompt.md

// Live production evidence collector for Autopilot merge checks:
// wires `pdd prove` / merge-base `verify.paths`, G3 polyglot report-diff & base-owned test oracle,
// post-review isolated test-env secret injection, and bound 13-field harness receipts.
import { execFile as cbExecFile, spawnSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { basename, dirname, join } from 'node:path';
import { promisify } from 'node:util';
import { OUTCOME_FAILED, OUTCOME_NOT_PROVED, OUTCOME_PROVED, runProve } from '../../core/prove.mjs';
import { readSafeUtf8 } from '../../core/lint/diagnostics.mjs';
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
import { detectTestRunner, extractTestCases } from './test-runners.mjs';

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

/**
 * Polyglot bug-fix base-control runner across JS/node:test, Vitest, Pytest, Go (`go test -json`), and Rust (`cargo test`).
 */
export async function runPolyglotBaseControl({
  baseDir, changedFiles = [], changedProdFiles = [], env = process.env, execFn = null, timeoutMs = 60_000,
} = {}) {
  if (!nonEmpty(baseDir) || !changedProdFiles.length) {
    return { state: 'not-run', runnerKind: null, command: null, exitCode: null, report: null };
  }
  const detected = detectTestRunner(baseDir);
  const kind = detected?.kind ?? null;
  const testFiles = (Array.isArray(changedFiles) ? changedFiles : []).filter(f => nonEmpty(f) && TEST_FILE_RE.test(f));
  if (!testFiles.length) return { state: 'not-run', runnerKind: kind, command: null, exitCode: null, report: null };

  let bin = null, args = [], reportFormat = detected?.reportFormat ?? 'auto';
  if (kind === 'vitest') {
    const matched = testFiles.filter(f => JS_TEST_RE.test(f));
    if (!matched.length) return { state: 'not-run', runnerKind: kind, command: null, exitCode: null, report: null };
    bin = 'npx'; args = ['vitest', 'run', ...matched];
  } else if (kind === 'pytest') {
    const matched = testFiles.filter(f => PY_TEST_RE.test(f));
    if (!matched.length) return { state: 'not-run', runnerKind: kind, command: null, exitCode: null, report: null };
    bin = 'pytest'; args = ['-q', ...matched];
  } else if (kind === 'go') {
    const matched = testFiles.filter(f => GO_TEST_RE.test(f));
    if (!matched.length) return { state: 'not-run', runnerKind: kind, command: null, exitCode: null, report: null };
    const pkgs = [...new Set(matched.map(f => { const d = dirname(f); return d === '.' ? './.' : `./${d}`; }))];
    bin = 'go'; args = ['test', '-json', ...pkgs]; reportFormat = 'go-json';
  } else if (kind === 'cargo') {
    const matched = testFiles.filter(f => RUST_TEST_RE.test(f));
    if (!matched.length) return { state: 'not-run', runnerKind: kind, command: null, exitCode: null, report: null };
    const integrationTargets = matched.filter(f => /^tests\/[^/]+\.rs$/i.test(f)).map(f => basename(f, '.rs'));
    bin = 'cargo';
    args = integrationTargets.length ? ['test', ...integrationTargets.flatMap(t => ['--test', t])] : ['test'];
    reportFormat = 'cargo';
  } else {
    const matched = testFiles.filter(f => /\.(?:mjs|cjs|js)$/i.test(f));
    if (!matched.length) return { state: 'not-run', runnerKind: kind, command: null, exitCode: null, report: null };
    bin = process.execPath; args = ['--test', '--test-reporter=tap', ...matched]; reportFormat = 'tap';
  }

  const baseEnv = { ...env, CI: 'true' };
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

  // #3561 / #3634: Run Python formal test files in per-file subprocess isolation to prevent Z3 main_ctx() cross-file deadlocks.
  const pytestFiles = kind === 'pytest' ? args.slice(1) : [];
  const isolateFormalPy = kind === 'pytest' && pytestFiles.length > 1 && pytestFiles.some(f => PY_FORMAL_TEST_RE.test(f));
  if (isolateFormalPy) {
    const formalFiles = pytestFiles.filter(f => PY_FORMAL_TEST_RE.test(f));
    const regularFiles = pytestFiles.filter(f => !PY_FORMAL_TEST_RE.test(f));
    const batches = [
      ...(regularFiles.length ? [regularFiles] : []),
      ...formalFiles.map(f => [f]),
    ];
    const commands = [];
    const allCases = [];
    let failedExit = null;
    for (const batch of batches) {
      const batchArgs = ['-q', ...batch];
      commands.push(`${bin} ${batchArgs.join(' ')}`);
      const res = await runExec(bin, batchArgs, { cwd: baseDir, env: baseEnv, timeout: timeoutMs, maxBuffer: 4 * 1024 * 1024 });
      const combined = `${res.stdout ?? ''}\n${res.stderr ?? ''}`;
      const parsed = parseStandardTestReport(res.stdout ?? '', reportFormat);
      const batchCases = parsed.ok ? parsed.cases : extractTestCases(combined, kind);
      allCases.push(...batchCases);
      if (res.killed || res.code === 'ENOENT' || isPolyglotEnvError(`${combined}\n${res.message ?? ''}`, changedProdFiles)) {
        return { state: 'not-run', runnerKind: kind, command: commands.join(' && '), exitCode: res.exitCode ?? null, report: null, cases: allCases, isolatedFiles: formalFiles };
      }
      if (res.exitCode !== 0 && failedExit === null) failedExit = res.exitCode ?? 1;
    }
    const cmdDisplay = commands.join(' && ');
    if (failedExit !== null) {
      return { state: 'ran-and-failed-on-base', runnerKind: kind, command: cmdDisplay, exitCode: failedExit, report: null, cases: allCases, isolatedFiles: formalFiles };
    }
    return { state: 'passed-on-base', runnerKind: kind, command: cmdDisplay, exitCode: 0, report: null, cases: allCases, isolatedFiles: formalFiles };
  }

  const cmdDisplay = `${bin} ${args.join(' ')}`;
  const res = await runExec(bin, args, { cwd: baseDir, env: baseEnv, timeout: timeoutMs, maxBuffer: 4 * 1024 * 1024 });
  const combined = `${res.stdout ?? ''}\n${res.stderr ?? ''}`;
  const parsed = parseStandardTestReport(res.stdout ?? '', reportFormat);
  const cases = parsed.ok ? parsed.cases : extractTestCases(combined, kind ?? 'auto');
  if (res.exitCode === 0 && !res.killed) {
    return { state: 'passed-on-base', runnerKind: kind ?? 'node:test', command: cmdDisplay, exitCode: 0, report: parsed.ok ? parsed : null, cases };
  }
  if (res.killed || res.code === 'ENOENT' || isPolyglotEnvError(`${combined}\n${res.message ?? ''}`, changedProdFiles)) {
    return { state: 'not-run', runnerKind: kind ?? 'node:test', command: cmdDisplay, exitCode: res.exitCode ?? null, report: null, cases };
  }
  return { state: 'ran-and-failed-on-base', runnerKind: kind ?? 'node:test', command: cmdDisplay, exitCode: res.exitCode ?? 1, report: parsed.ok ? parsed : null, cases };
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
    if (/[\s;&|()<>`]/.test(ch)) {
      if (cur) { tokens.push(cur); cur = ''; }
      continue;
    }
    cur += ch;
  }
  if (cur) tokens.push(cur);
  return tokens;
}

function collectCommandCandidates(cmd, depth = 0, out = []) {
  for (const token of tokenizeShellCommand(cmd)) {
    out.push(token);
    const eqIdx = token.indexOf('=');
    if (eqIdx > 0 && eqIdx < token.length - 1) {
      out.push(token.slice(eqIdx + 1));
    }
    if (depth < 3 && /[\s"'`=<>|&;()]/.test(token)) {
      collectCommandCandidates(token, depth + 1, out);
    }
  }
  return out;
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

function fileExistsInBase(relPath, { headTree, baseTree, baseTip, baseTipValid, fs }) {
  if (baseTree) {
    try {
      const st = fs.lstatSync(join(baseTree, relPath));
      if (st.isFile() && !st.isSymbolicLink()) return true;
    } catch { /* fall through to git cat-file */ }
  }
  if (headTree && baseTipValid) {
    try {
      const res = spawnSync('git', ['cat-file', '-t', `${baseTip}:${relPath}`], {
        cwd: headTree, encoding: 'utf8', timeout: 3000, stdio: ['ignore', 'pipe', 'ignore'],
      });
      if (res.status === 0 && String(res.stdout ?? '').trim() === 'blob') return true;
    } catch { /* absent */ }
  }
  return false;
}

function extractRecipeScriptPaths(baseVerify, { headTree = null, baseTree = null, baseTip = null, baseTipValid = false, fs = nativeFs } = {}) {
  const found = new Set();
  const commands = [
    ...(nonEmpty(baseVerify?.test) ? [baseVerify.test] : []),
    ...(Array.isArray(baseVerify?.paths) ? baseVerify.paths.map(p => p?.run).filter(nonEmpty) : []),
  ];
  const candidateTokens = [];
  for (const cmd of commands) {
    collectCommandCandidates(cmd, 0, candidateTokens);
  }
  const hasBaseLookup = Boolean(baseTree || (headTree && baseTipValid));
  for (const raw of candidateTokens) {
    const cand = raw.replace(/^(?:\.\/)+/, '');
    if (!cand || cand.startsWith('-') || cand.startsWith('/') || cand.includes('..') || cand.includes('\\') || cand.includes('\0')) continue;
    if (TEST_FILE_RE.test(cand)) continue;
    if (SCRIPT_EXT_RE.test(cand)) {
      found.add(cand);
      continue;
    }
    if (hasBaseLookup && fileExistsInBase(cand, { headTree, baseTree, baseTip, baseTipValid, fs })) {
      found.add(cand);
    }
  }
  return [...found].sort();
}

function redactTextWithValues(text, sandbox, secretValues = []) {
  if (typeof text !== 'string') return text;
  let out = sandbox && typeof sandbox.redact === 'function' ? sandbox.redact(text) : text;
  for (const secret of secretValues) {
    if (secret && out.includes(secret)) out = out.split(secret).join('[redacted]');
  }
  return out;
}

function deepRedactValue(value, sandbox, secretValues = [], depth = 0) {
  if (depth > 12 || value === null || value === undefined) return value;
  if (typeof value === 'string') return redactTextWithValues(value, sandbox, secretValues);
  if (Array.isArray(value)) return value.map(item => deepRedactValue(item, sandbox, secretValues, depth + 1));
  if (isObj(value)) {
    const out = {};
    for (const [k, v] of Object.entries(value)) {
      out[k] = deepRedactValue(v, sandbox, secretValues, depth + 1);
    }
    return out;
  }
  return value;
}

function redactProveReceipt(receipt, sandbox, secretValues = []) {
  if (!receipt || (!sandbox && !secretValues.length)) return receipt;
  return deepRedactValue(receipt, sandbox, secretValues, 0);
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
  const recipeProtectedPatterns = extractRecipeScriptPaths(baseVerify, { headTree, baseTree, baseTip: cleanBaseTip, baseTipValid, fs });
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

  return {
    source: 'live-production',
    verifyPathsConfigured: hasVerifyPaths,
    advisory: !strictMode && !basePolicyInvalid && !basePolicyUnreadable && Boolean(headTree) && !changedFilesError,
    proveOutcome,
    proveReasons,
    proveReceipt: proveResult?.receipt ?? null,
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
      formalProofs: Array.isArray(job?.formalProofs) ? job.formalProofs : [],
      formalTargetModules: Array.isArray(job?.formalTargetModules) ? job.formalTargetModules : [],
      requireCodeBoundFormal: job?.requireCodeBoundFormal === true,
      stampReceipt,
      postStandaloneReceiptComment: strictMode,
    },
  };
}
