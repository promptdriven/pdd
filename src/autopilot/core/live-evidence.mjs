// Prompt: prompts/cli/autopilot-validator.prompt.md

// Live production evidence collector for Autopilot merge checks:
// wires `pdd prove` / merge-base `verify.paths`, G3 polyglot report-diff & base-owned test oracle,
// post-review isolated test-env secret injection, and bound 13-field harness receipts.
import { execFile as cbExecFile, spawnSync } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { basename, dirname, join } from 'node:path';
import { promisify } from 'node:util';
import { OUTCOME_NOT_PROVED, OUTCOME_PROVED, runProve } from '../../core/prove.mjs';
import { loadVerifyConfig, matchVerifyPaths } from '../../core/verify-paths.mjs';
import { computeCanonicalDigest, isProtectedPath } from '../gates/evidence-contract.mjs';
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
  const cmdDisplay = `${bin} ${args.join(' ')}`;

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

/**
 * Real production evidence collector invoked on every Autopilot merge check (`runValidatorV2Gate`).
 * - Reads `verify` config strictly from merge-base `pdd.json` (never untrusted PR-head edits).
 * - Invokes real `runProve` when merge-base `verify.paths` is configured, using `buildPostReviewSandboxEnv`
 *   when `reviewApproved: true` and matched recipes require `account:<name>` credentials.
 * - Runs G3 polyglot `diffTestReports` (when base & head structured reports are available) and
 *   `runBaseOwnedTestOracle` (when existing base test files are edited on a configured/runnable repo).
 * - Always returns a complete evidence-contract payload + bound 13-field `stampReceipt` (strict when
 *   merge-base `verify.paths` is configured; explicit `Not proved` advisory mode when unconfigured).
 */
export async function collectLiveEvidenceContract({
  repo = 'local/repo',
  job = {},
  headTree = null,
  baseTree = null,
  baseTip = null,
  changedFiles = [],
  suite = null,
  suiteCmd = 'npm test',
  suiteLog = '',
  baseReport = null,
  headReport = null,
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
  const effectiveSuiteCmd = nonEmpty(suiteCmd) ? suiteCmd.trim() : 'npm test';

  // 1. Load verify config strictly from trusted merge-base (`baseTip:pdd.json` or `baseTree/pdd.json`).
  let baseVerify = headTree && GIT_SHA_RE.test(cleanBaseTip)
    ? loadVerifyConfig(headTree, { gitRef: cleanBaseTip })
    : { configured: false, source: 'pdd.json', test: null, report: null, paths: [], errors: [] };
  if (!baseVerify.configured && baseTree) {
    baseVerify = loadVerifyConfig(baseTree);
  }
  const hasVerifyPaths = baseVerify.configured && Array.isArray(baseVerify.paths) && baseVerify.paths.length > 0;
  const { matched, changedSurfaces, unmappedSurfaces } = matchVerifyPaths(baseVerify, cleanFiles);

  // 2. Load 0600 test-env metadata & probe host capabilities ONLY when merge-base verify.paths (or explicit probeOptions) need them;
  // inject sandbox credentials ONLY post-review!
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
  let recipeEnv = env;
  if (hasVerifyPaths && neededAccounts.length > 0 && reviewApproved && rawTestEnv.ok === true) {
    postReviewSandbox = buildPostReviewSandboxEnv({
      baseEnv: env,
      testEnv: rawTestEnv,
      reviewApproved: true,
      approvedHead: job.review.head,
      currentHead: cleanHead,
      allowedAccounts: neededAccounts,
    });
    recipeEnv = postReviewSandbox.env;
  } else if (neededAccounts.length > 0 && !reviewApproved) {
    // Never treat account:* credentials as usable before blind review approves this exact head!
    for (const acct of neededAccounts) {
      const idx = availableCapabilities.indexOf(`account:${acct}`);
      if (idx >= 0) availableCapabilities.splice(idx, 1);
    }
  }

  // 3. Build deterministic 13-field contract bindings.
  const detectedRunner = headTree ? detectTestRunner(headTree) : null;
  const toolchain = defaultToolchainLabel(detectedRunner?.kind ?? null);
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

  // 4. Parse head/base structured test reports & run G3 polyglot diffTestReports when both exist.
  const effectiveHeadReport = headReport ?? (nonEmpty(suiteLog) ? suiteLog : null);
  const parsedHead = effectiveHeadReport ? parseStandardTestReport(effectiveHeadReport, detectedRunner?.reportFormat ?? 'auto') : { ok: false, cases: [] };
  let reportDiff = null;
  if (baseReport && effectiveHeadReport) {
    const sharedMeta = {
      baseSha: cleanBaseTip,
      policyDigest: trustedPolicyDigest,
      recipeDigest,
      toolchain,
      platform: process.platform,
      profile: detectedRunner?.kind ?? 'default',
      format: detectedRunner?.reportFormat ?? 'auto',
    };
    reportDiff = diffTestReports({
      baseReport,
      headReport: effectiveHeadReport,
      baseMeta: sharedMeta,
      headMeta: sharedMeta,
      approvedRemovals: Array.isArray(job?.approvedTestRemovals) ? job.approvedTestRemovals : [],
    });
  }

  const testResults = [];
  const expectedTestIds = [];
  if (parsedHead.ok && parsedHead.cases.length > 0) {
    for (const c of parsedHead.cases) {
      testResults.push({
        id: c.id,
        status: c.status === 'pass' ? 'pass' : (c.status === 'skip' ? 'skip' : 'fail'),
        source: 'harness',
      });
    }
  }
  if (reportDiff) {
    for (const id of reportDiff.missingIds) expectedTestIds.push(id);
    for (const id of reportDiff.newlySkippedIds) {
      if (!testResults.some(t => t.id === id)) testResults.push({ id, status: 'skip', source: 'harness' });
    }
    for (const id of reportDiff.newlyFailingIds) {
      if (!testResults.some(t => t.id === id)) testResults.push({ id, status: 'fail', source: 'harness' });
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
    && (hasVerifyPaths || parsedHead.ok || runOracleFn !== runBaseOwnedTestOracle),
  );
  let baseOracle = null;
  let oracleResult = null;
  if (shouldRunBaseOracle) {
    const oracleCmd = oracleCommandForRunner(detectedRunner, baseVerify.test || effectiveSuiteCmd);
    oracleResult = await runOracleFn({
      baseTree,
      headTree,
      editedTestFiles: editedExistingBaseTests,
      testCommand: oracleCmd,
      intendedChanges: Array.isArray(job?.intendedTestChanges) ? job.intendedTestChanges : [],
      format: detectedRunner?.reportFormat ?? 'auto',
      env: recipeEnv,
    });
    baseOracle = {
      status: oracleResult.status === 'pass' ? 'passed' : (oracleResult.status === 'fail' ? 'failed' : 'unknown'),
      unlistedFailures: (oracleResult.regressions ?? []).map(r => (typeof r === 'string' ? r : r.id)).filter(Boolean),
      unknowns: oracleResult.status === 'unknown' ? [oracleResult.reason || 'oracle_unknown'] : [],
    };
  }

  // 6. Execute live `pdd prove` when merge-base `verify.paths` is configured; otherwise emit explicit advisory `Not proved`.
  let proveResult = null;
  let proveOutcome = OUTCOME_NOT_PROVED;
  const receipts = [];
  let touchedPaths = [];
  const requiredCapabilitiesByPath = {};
  let gapCheck = null;
  let requireGapCheck = false;
  let stampReceipt = null;

  if (hasVerifyPaths && headTree) {
    const sink = { write() {} };
    // When blind review approved this exact head and matched verify.paths recipes require `account:*`
    // credentials, forward ONLY the strictly allowlisted `postReviewSandbox` injected keys to those
    // matched post-review recipes (never pre-review, never unrelated env vars).
    const accountRecipeCommands = new Set(
      matched.filter(m => (m.needs ?? []).some(c => typeof c === 'string' && c.startsWith('account:'))).map(m => m.run),
    );
    const provePorts = { stdout: sink, stderr: sink };
    if (postReviewSandbox && accountRecipeCommands.size > 0 && runProveFn === runProve) {
      provePorts.spawnSync = (cmd, opts) => {
        if (accountRecipeCommands.has(cmd)) {
          const mergedEnv = { ...(opts?.env ?? {}) };
          for (const key of postReviewSandbox.injectedKeys) {
            if (typeof postReviewSandbox.env[key] === 'string') mergedEnv[key] = postReviewSandbox.env[key];
          }
          return spawnSync(cmd, { ...opts, env: mergedEnv });
        }
        return spawnSync(cmd, opts);
      };
    }
    proveResult = await runProveFn(
      {
        cwd: headTree,
        base: GIT_SHA_RE.test(cleanBaseTip) ? cleanBaseTip : undefined,
        capabilities: availableCapabilities,
        env: recipeEnv,
        json: true,
      },
      provePorts,
    );
    proveOutcome = proveResult?.outcome ?? OUTCOME_NOT_PROVED;
    touchedPaths = matched.map(m => m.id);
    for (const m of matched) requiredCapabilitiesByPath[m.id] = [...(m.needs ?? [])];

    const provePaths = Array.isArray(proveResult?.receipt?.paths) ? proveResult.receipt.paths : [];
    for (const p of provePaths) {
      const outcome = p.status === 'proved'
        ? 'proved'
        : (Array.isArray(p.missingCapabilities) && p.missingCapabilities.length > 0 ? 'missing_capability' : 'failed');
      const rawSummary = postReviewSandbox ? postReviewSandbox.redact(p.summary ?? '') : String(p.summary ?? '');
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
    const overallOutcome = proveOutcome === OUTCOME_PROVED
      ? 'proved'
      : (anyMissingCap ? 'missing_capability' : (anyFailed ? 'failed' : (suite?.state === 'pass' ? 'proved' : 'failed')));
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
        paths: provePaths.map(p => ({ id: p.id, status: p.status, exitCode: p.exitCode ?? null })),
        unmappedSurfaces,
      }),
    };
  } else {
    // No merge-base verify.paths configured: produce an explicit advisory `Not proved` live evidence record
    // AND a real bound 13-field harness receipt for the executed suite so evaluateEvidenceContract + stamping run live.
    const suiteOutcome = suite?.state === 'pass' ? 'proved' : 'failed';
    const suiteReceipt = {
      ...expectedBinding,
      writtenBy: 'harness',
      testProfile: 'full-suite',
      command: effectiveSuiteCmd,
      toolchain,
      capability: null,
      outcome: suiteOutcome,
      artifactDigest: computeCanonicalDigest({
        suiteCmd: effectiveSuiteCmd,
        suiteState: suite?.state ?? 'unknown',
        verifyPathsConfigured: false,
        proveOutcome: OUTCOME_NOT_PROVED,
        parsedTestCount: parsedHead.ok ? parsedHead.cases.length : 0,
      }),
    };
    receipts.push(suiteReceipt);
    stampReceipt = suiteReceipt;
  }

  const strictMode = hasVerifyPaths || strictWithoutVerifyPaths === true;
  const advisoryProtectedPaths = !strictMode ? cleanFiles.filter(f => isProtectedPath(f)) : [];
  const humanApprovedPaths = [
    ...(Array.isArray(job?.humanApprovedPaths) ? job.humanApprovedPaths : []),
    ...advisoryProtectedPaths,
  ];

  return {
    source: 'live-production',
    verifyPathsConfigured: hasVerifyPaths,
    advisory: !strictMode,
    proveOutcome,
    proveReceipt: proveResult?.receipt ?? null,
    reportDiff,
    oracleResult,
    postReviewSandboxUsed: Boolean(postReviewSandbox),
    postReviewInjectedKeys: postReviewSandbox?.injectedKeys ?? [],
    testEnvMeta,
    availableCapabilities,
    contractInput: {
      changedFiles: cleanFiles,
      humanApprovedPaths,
      frozenAcs: Array.isArray(job?.frozenAcs) ? job.frozenAcs : [],
      requireFrozenAcs: Array.isArray(job?.frozenAcs) && job.frozenAcs.length > 0,
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
