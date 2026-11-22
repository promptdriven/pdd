// Unified stateless `pdd prove` (G1): zero-flag merge-base verification + 5-bug-fixed bug-contrast mode.
import { spawnSync } from 'node:child_process';
import { closeSync, constants, existsSync, fstatSync, lstatSync, mkdirSync, mkdtempSync, openSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { isTestOwnedPath } from '../file-owner.mjs';
import { causeText } from '../shared/safe-read.mjs';
import { canonicalRepoPath, formatTeachingDetail, readSafeUtf8, resolveDefaultBaseRef, scrubChildEnv } from './lint/diagnostics.mjs';
import { lintRepoProject } from './lint/project-lint.mjs';
import { compileGlobMatcher } from './lint/regex-safety.mjs';
import { runDiffSpotlight } from './lint/test-inventory.mjs';
import { detectHostCapabilities, loadVerifyConfig, matchCapabilities, matchVerifyPaths } from './verify-paths.mjs';

export const OUTCOME_PROVED = 'Proved';
export const OUTCOME_FAILED = 'Failed';
export const OUTCOME_NOT_PROVED = 'Not proved';
export const EXIT_PROVED = 0;
export const EXIT_FAILED = 1;
export const EXIT_USAGE = 2;
export const EXIT_NOT_PROVED = 3;

const SETUP_FAILURE_RE = /(?:(?:^|\n)\s*(?:#\s*)?(?:Error:\s*Cannot find module|Error \[ERR_MODULE_NOT_FOUND\]|ERR_MODULE_NOT_FOUND|Cannot find package|ModuleNotFoundError:|ImportError:|No module named|SyntaxError:|FileNotFoundError:|Error:\s*ENOENT|ENOENT:|ERROR collecting|command not found|not recognized as an internal|cannot find package|no Go files|error\[E\d+\]:|failed to compile)|\[build failed\])/i;
const COLOCATED_TEST_RE = /(?:\.(?:test|spec)\.(?:[cm]?[jt]s|[jt]sx)|(?:^|\/)test_[^/]+\.py$|_test\.(?:py|go|rs)$|^(?:test|tests|__tests__|fixtures)\/)/i;

const gitExec = (cwd, args) => spawnSync('git', args, { cwd, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
const resolveGitRoot = cwd => { const r = gitExec(cwd, ['rev-parse', '--show-toplevel']); return r.status === 0 && r.stdout.trim() ? realpathSync(r.stdout.trim()) : realpathSync(cwd); };
const resolveCommit = (root, ref) => { const r = gitExec(root, ['rev-parse', '--verify', `${ref}^{commit}`]); return r.status === 0 && r.stdout.trim() ? r.stdout.trim() : null; };

function execShellCommand(command, { cwd, env, timeoutMs }, ports = {}) {
  const runner = ports.spawnSync ?? spawnSync;
  const started = Date.now();
  const proc = runner(command, { cwd, env: scrubChildEnv(env), shell: true, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
  const stdout = String(proc.stdout ?? ''), stderr = String(proc.stderr ?? '');
  const timedOut = proc.error?.code === 'ETIMEDOUT';
  const exitCode = typeof proc.status === 'number' ? proc.status : null;
  const signal = proc.signal ?? '';
  const setupMatch = exitCode !== 0 ? SETUP_FAILURE_RE.exec(`${stderr}\n${stdout}`) : null;
  const setupError = proc.error && !timedOut
    ? causeText(proc.error.message)
    : (signal && !timedOut
        ? `Process terminated by signal ${signal}`
        : ([126, 127].includes(exitCode) ? `Command exited ${exitCode}` : (setupMatch ? causeText(setupMatch[0]) : '')));
  return {
    command, ok: exitCode === 0 && !proc.error && !signal, exitCode, signal, timedOut,
    durationMs: Math.max(0, Date.now() - started), stdout, stderr, setupError,
    summary: causeText(stderr || stdout || setupError || (timedOut ? 'command timed out' : '')),
  };
}

export function detectRepoTestCommand(root) {
  const pkgRaw = readSafeUtf8(root, 'package.json');
  if (pkgRaw) {
    try {
      const pkg = JSON.parse(pkgRaw);
      const testScript = typeof pkg?.scripts?.test === 'string' ? pkg.scripts.test.trim() : '';
      if (testScript && !/no test specified/i.test(testScript)) {
        if (existsSync(join(root, 'pnpm-lock.yaml'))) return 'pnpm test';
        if (existsSync(join(root, 'yarn.lock'))) return 'yarn test';
        return 'npm test';
      }
      if (pkg?.dependencies?.vitest || pkg?.devDependencies?.vitest) return 'npx vitest run';
    } catch {}
  }
  if (existsSync(join(root, 'go.mod'))) return 'go test ./...';
  if (existsSync(join(root, 'Cargo.toml'))) return 'cargo test';
  if (existsSync(join(root, 'pyproject.toml')) || existsSync(join(root, 'pytest.ini')) || existsSync(join(root, 'setup.cfg'))) return 'pytest';
  return null;
}

function listChangedFiles(root, ref) {
  const seen = new Set();
  if (ref) {
    const diff = gitExec(root, ['diff', '--name-only', '-z', ref, '--']);
    if (diff.status === 0 && diff.stdout) for (const p of diff.stdout.split('\0').filter(Boolean)) seen.add(p);
  }
  const untracked = gitExec(root, ['ls-files', '--others', '--exclude-standard', '-z']);
  if (untracked.status === 0 && untracked.stdout) for (const p of untracked.stdout.split('\0').filter(Boolean)) seen.add(p);
  return [...seen].filter(canonicalRepoPath).sort();
}

function lstatSafe(fullPath) {
  try { return lstatSync(fullPath); }
  catch (err) { if (err?.code === 'ENOENT') return null; throw err; }
}

function walkCheckedSegments(baseReal, relPath, { createDirs = false } = {}) {
  const parts = relPath.split('/');
  let cur = baseReal;
  for (let i = 0; i < parts.length - 1; i++) {
    cur = join(cur, parts[i]);
    let st = lstatSafe(cur);
    if (!st) {
      if (!createDirs) return { fullPath: join(baseReal, relPath), leafStat: null };
      mkdirSync(cur);
      st = lstatSync(cur);
    }
    if (st.isSymbolicLink() || !st.isDirectory()) throw new Error(`Refused symlink or non-directory path segment: ${parts.slice(0, i + 1).join('/')}`);
  }
  const fullPath = join(cur, parts.at(-1));
  const leafStat = lstatSafe(fullPath);
  if (leafStat?.isSymbolicLink()) throw new Error(`Refused symlinked overlay path: ${relPath}`);
  return { fullPath, leafStat };
}

function copyWorkingTreeOverlay(root, worktree, relPaths, { deleteMissing = false } = {}) {
  const rootReal = realpathSync(root), wtReal = realpathSync(worktree);
  const mirrored = [];
  for (const rel of relPaths) {
    if (!canonicalRepoPath(rel)) throw new Error(`Unsafe overlay path: ${rel}`);
    const srcInfo = walkCheckedSegments(rootReal, rel);
    if (!srcInfo.leafStat) {
      if (deleteMissing) {
        const dstInfo = walkCheckedSegments(wtReal, rel);
        if (dstInfo.leafStat) {
          if (!dstInfo.leafStat.isFile()) throw new Error(`Refused non-regular deletion target in worktree: ${rel}`);
          rmSync(dstInfo.fullPath, { force: true });
          mirrored.push(rel);
        }
      }
      continue;
    }
    if (!srcInfo.leafStat.isFile()) throw new Error(`Refused non-regular overlay file: ${rel}`);
    const rfd = openSync(srcInfo.fullPath, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
    let bytes;
    try {
      if (!fstatSync(rfd).isFile()) throw new Error(`Overlay path changed to non-regular file: ${rel}`);
      bytes = readFileSync(rfd);
    } finally { closeSync(rfd); }
    const dstInfo = walkCheckedSegments(wtReal, rel, { createDirs: true });
    if (dstInfo.leafStat && !dstInfo.leafStat.isFile()) throw new Error(`Refused non-regular destination in worktree: ${rel}`);
    const mode = srcInfo.leafStat.mode & 0o777;
    const wfd = openSync(dstInfo.fullPath, constants.O_WRONLY | constants.O_CREAT | constants.O_TRUNC | (constants.O_NOFOLLOW ?? 0), mode);
    try { writeFileSync(wfd, bytes); } finally { closeSync(wfd); }
    mirrored.push(rel);
  }
  return mirrored;
}

function rawVerifyFingerprint(rawText) {
  if (typeof rawText !== 'string') return null;
  try {
    const parsed = JSON.parse(rawText);
    return parsed && typeof parsed === 'object' && !Array.isArray(parsed) && Object.hasOwn(parsed, 'verify')
      ? JSON.stringify(parsed.verify)
      : null;
  } catch { return '__INVALID__'; }
}

function runBugContrastProve({ root, base, test, expect, overlay, setup, timeoutMinutes, json, env }, ports = {}) {
  const stdout = ports.stdout ?? process.stdout, stderr = ports.stderr ?? process.stderr;
  if (typeof test !== 'string' || !test.trim() || typeof expect !== 'string' || !expect.trim()) {
    stderr.write('pdd prove bug-contrast mode requires nonblank --test CMD and --expect TEXT.\n');
    return { exitCode: EXIT_USAGE, outcome: OUTCOME_FAILED, receipt: null };
  }
  if (!Number.isInteger(timeoutMinutes) || timeoutMinutes < 1 || timeoutMinutes > 120) {
    stderr.write('pdd prove --timeout takes whole minutes from 1 to 120.\n');
    return { exitCode: EXIT_USAGE, outcome: OUTCOME_FAILED, receipt: null };
  }

  const headSha = resolveCommit(root, 'HEAD');
  const requestedBase = base || resolveDefaultBaseRef(root) || 'HEAD~1';
  const resolvedBaseCommit = resolveCommit(root, requestedBase);
  const mbRes = resolvedBaseCommit && headSha ? gitExec(root, ['merge-base', headSha, resolvedBaseCommit]) : null;
  const baseSha = base
    ? resolvedBaseCommit
    : (mbRes?.status === 0 && mbRes.stdout.trim() && mbRes.stdout.trim() !== headSha
        ? mbRes.stdout.trim()
        : (resolveCommit(root, 'HEAD~1') ?? resolvedBaseCommit));

  if (!baseSha || !headSha) {
    const receipt = {
      schema_version: 'pdd.prove.v1', mode: 'bug-contrast', outcome: OUTCOME_NOT_PROVED, reason: 'base-unavailable',
      exit_code: EXIT_NOT_PROVED, baseRef: requestedBase, baseSha, headSha, overlayPaths: [], test, expect,
      base: null, head: null, notProvedReasons: [`Offline base ref "${requestedBase}" or HEAD could not be resolved locally.`],
    };
    if (json) stdout.write(`${JSON.stringify(receipt, null, 2)}\n`);
    else stderr.write(`Not proved: offline base ref "${requestedBase}" not found locally.\n`);
    return { exitCode: EXIT_NOT_PROVED, outcome: OUTCOME_NOT_PROVED, receipt };
  }

  const overlayGlobs = (Array.isArray(overlay) ? overlay : (overlay ? [overlay] : [])).map(compileGlobMatcher);
  if (overlayGlobs.some(m => m === null)) {
    stderr.write('pdd prove --overlay contains an invalid glob pattern.\n');
    return { exitCode: EXIT_USAGE, outcome: OUTCOME_FAILED, receipt: null };
  }

  const changedFromBase = listChangedFiles(root, baseSha);
  const overlayPaths = changedFromBase.filter(f => (overlayGlobs.length > 0 && overlayGlobs.some(m => m.test(f))) || COLOCATED_TEST_RE.test(f) || isTestOwnedPath(f));
  const timeoutMs = timeoutMinutes * 60_000;
  const worktreeParent = mkdtempSync(join(tmpdir(), 'pdd-prove-'));
  const baseWorktree = join(worktreeParent, 'base');
  const headWorktree = join(worktreeParent, 'head');
  const createdWorktrees = [];
  let basePhase = null, headPhase = null, setupError = '', copiedPaths = [];

  try {
    const wtBase = gitExec(root, ['worktree', 'add', '--detach', baseWorktree, baseSha]);
    if (wtBase.status !== 0) throw new Error(wtBase.stderr || wtBase.stdout || 'git worktree add base failed');
    createdWorktrees.push(baseWorktree);
    copiedPaths = copyWorkingTreeOverlay(root, baseWorktree, overlayPaths, { deleteMissing: true });

    // Always isolate head inside its own disposable worktree so `pdd prove` NEVER mutates the caller's checkout.
    const wtHead = gitExec(root, ['worktree', 'add', '--detach', headWorktree, headSha]);
    if (wtHead.status !== 0) throw new Error(wtHead.stderr || wtHead.stdout || 'git worktree add head failed');
    createdWorktrees.push(headWorktree);
    copyWorkingTreeOverlay(root, headWorktree, listChangedFiles(root, headSha), { deleteMissing: true });

    if (setup) {
      const baseSetup = execShellCommand(setup, { cwd: baseWorktree, env, timeoutMs }, ports);
      if (!baseSetup.ok) throw new Error(`base --setup failed (exit ${baseSetup.exitCode}): ${baseSetup.summary}`);
      const headSetup = execShellCommand(setup, { cwd: headWorktree, env, timeoutMs }, ports);
      if (!headSetup.ok) throw new Error(`head --setup failed (exit ${headSetup.exitCode}): ${headSetup.summary}`);
    }

    basePhase = execShellCommand(test, { cwd: baseWorktree, env, timeoutMs }, ports);
    basePhase.expectedFound = !basePhase.setupError && !basePhase.signal && (basePhase.stdout.includes(expect) || basePhase.stderr.includes(expect));
    headPhase = execShellCommand(test, { cwd: headWorktree, env, timeoutMs }, ports);
  } catch (err) {
    setupError = causeText(err?.message || String(err));
  } finally {
    for (const wt of createdWorktrees) gitExec(root, ['worktree', 'remove', '--force', wt]);
    rmSync(worktreeParent, { recursive: true, force: true });
  }

  let outcome, reason, exitCode;
  const notProvedReasons = [];
  if (setupError || basePhase?.setupError || headPhase?.setupError || (!basePhase?.timedOut && basePhase?.signal) || (!headPhase?.timedOut && headPhase?.signal)) {
    outcome = OUTCOME_NOT_PROVED; reason = 'setup-error'; exitCode = EXIT_NOT_PROVED;
    notProvedReasons.push(`Setup/dependency/compile failure prevented causal bug-contrast proof: ${setupError || basePhase?.setupError || headPhase?.setupError || basePhase?.signal || headPhase?.signal}`);
  } else if (basePhase?.timedOut || headPhase?.timedOut) {
    outcome = OUTCOME_FAILED; reason = basePhase?.timedOut ? 'base-timeout' : 'head-timeout'; exitCode = EXIT_FAILED;
  } else if (!headPhase?.ok) {
    outcome = OUTCOME_FAILED; reason = 'head-fails'; exitCode = EXIT_FAILED;
  } else if (basePhase?.ok) {
    outcome = OUTCOME_FAILED; reason = 'base-passes'; exitCode = EXIT_FAILED;
  } else if (!basePhase?.expectedFound) {
    outcome = OUTCOME_NOT_PROVED; reason = 'wrong-reason'; exitCode = EXIT_NOT_PROVED;
    notProvedReasons.push(`Base failed (exit ${basePhase?.exitCode}), but output did not contain expected symptom ${JSON.stringify(expect)} (observed: ${basePhase?.summary || 'no output'}).`);
  } else {
    outcome = OUTCOME_PROVED; reason = 'proved'; exitCode = EXIT_PROVED;
  }

  const summarize = p => p ? { exitCode: p.exitCode, signal: p.signal || null, ok: p.ok, timedOut: p.timedOut, durationMs: p.durationMs, setupError: p.setupError, expectedFound: Boolean(p.expectedFound), summary: p.summary } : null;
  const receipt = {
    schema_version: 'pdd.prove.v1', mode: 'bug-contrast', outcome, reason, exit_code: exitCode,
    baseRef: requestedBase, baseSha, headSha, overlayPaths: copiedPaths, test, expect,
    base: summarize(basePhase), head: summarize(headPhase), notProvedReasons,
  };
  if (json) stdout.write(`${JSON.stringify(receipt, null, 2)}\n`);
  else if (outcome === OUTCOME_PROVED) stdout.write(`Proved: \`${test}\` failed on base (${baseSha.slice(0, 7)}) with expected ${JSON.stringify(expect)} and passed on head.\n`);
  else stderr.write(`${outcome} [${reason}]: ${notProvedReasons[0] || `base exit ${basePhase?.exitCode ?? 'none'}, head exit ${headPhase?.exitCode ?? 'none'}`}\n`);
  return { exitCode, outcome, receipt };
}

export function runProve(
  { cwd = process.cwd(), base, test, expect, overlay, setup, timeoutMinutes = 10, json = false, capabilities, env = process.env } = {},
  ports = {},
) {
  const stdout = ports.stdout ?? process.stdout, stderr = ports.stderr ?? process.stderr;
  const root = resolveGitRoot(cwd);
  if (test !== undefined || expect !== undefined) return runBugContrastProve({ root, base, test, expect, overlay, setup, timeoutMinutes, json, env }, ports);
  if (!Number.isInteger(timeoutMinutes) || timeoutMinutes < 1 || timeoutMinutes > 120) {
    stderr.write('pdd prove --timeout takes whole minutes from 1 to 120.\n');
    return { exitCode: EXIT_USAGE, outcome: OUTCOME_FAILED, receipt: null };
  }

  const headSha = resolveCommit(root, 'HEAD');
  const baseRef = base || resolveDefaultBaseRef(root);
  const baseCommit = baseRef ? resolveCommit(root, baseRef) : null;
  const mb = baseCommit && headSha ? gitExec(root, ['merge-base', headSha, baseCommit]) : null;
  const baseSha = mb?.status === 0 && mb.stdout.trim() ? mb.stdout.trim() : baseCommit;
  const timeoutMs = timeoutMinutes * 60_000;

  const lint = lintRepoProject({ root });
  const diff = runDiffSpotlight({ cwd: root, baseRef: baseSha || baseRef || undefined });
  const notProvedReasons = [];

  if (!baseSha || !diff.baseAvailable) {
    notProvedReasons.push(diff.baseError || `Base ref "${baseRef || 'default'}" could not be resolved locally; refusing to assume an empty diff.`);
    const receipt = {
      schema_version: 'pdd.prove.v1', mode: 'verify', outcome: OUTCOME_NOT_PROVED, exit_code: EXIT_NOT_PROVED,
      baseRef: baseRef ?? null, baseSha: null, headSha, configSource: null, touchedFiles: [], changedSurfaces: [],
      lint: { ok: lint.ok, errors: lint.errors, warnings: lint.warnings },
      diff: { ok: false, errors: diff.errors.map(e => e.formatted), advisories: diff.advisories },
      test: null, paths: [], notProvedReasons,
    };
    if (json) stdout.write(`${JSON.stringify(receipt, null, 2)}\n`);
    else stdout.write(`Not proved:\n${notProvedReasons.map(r => `  - ${r}`).join('\n')}\n`);
    return { exitCode: EXIT_NOT_PROVED, outcome: OUTCOME_NOT_PROVED, receipt };
  }

  // Always trust verify config strictly from git merge base (`baseSha:pdd.json`), NEVER from untrusted working-tree edits.
  const baseVerify = loadVerifyConfig(root, { gitRef: baseSha });
  const worktreeVerify = loadVerifyConfig(root);
  const baseRaw = gitExec(root, ['show', `${baseSha}:pdd.json`]);
  const baseFp = baseRaw.status === 0 ? rawVerifyFingerprint(baseRaw.stdout) : null;
  const worktreeFp = rawVerifyFingerprint(readSafeUtf8(root, 'pdd.json'));
  if (!baseVerify.configured && worktreeVerify.configured) {
    notProvedReasons.push('verify config in pdd.json exists only in the working tree/branch and is not yet trusted on merge base; human review required.');
  } else if (baseVerify.configured && worktreeFp !== baseFp) {
    notProvedReasons.push('Working-tree/branch edits to "verify" in pdd.json are not yet trusted on merge base; executed merge-base recipes only.');
  }

  const testCommand = baseVerify.test || detectRepoTestCommand(root);
  let testResult = null;
  if (testCommand) {
    const r = execShellCommand(testCommand, { cwd: root, env, timeoutMs }, ports);
    testResult = { command: testCommand, ok: r.ok, exitCode: r.exitCode, durationMs: r.durationMs, setupError: r.setupError, summary: r.summary };
  } else {
    notProvedReasons.push('No verify.test command configured in merge-base pdd.json and no standard test runner detected.');
  }

  const { matched, changedSurfaces, unmappedSurfaces } = matchVerifyPaths(baseVerify, diff.touchedFiles);
  const capState = detectHostCapabilities(matched.flatMap(r => r.needs), { env, capabilities, probe: ports.probeCapability, isTTY: ports.isTTY });
  const pathResults = [];
  for (const recipe of matched) {
    const { satisfied, missing } = matchCapabilities(recipe.needs, capState);
    if (!satisfied) {
      pathResults.push({ id: recipe.id, name: recipe.name, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs, status: 'not-proved', missingCapabilities: missing, ok: false });
      notProvedReasons.push(`Recipe "${recipe.id}" (${recipe.name}) skipped: missing required capability [${missing.join(', ')}].`);
      continue;
    }
    const r = execShellCommand(recipe.run, { cwd: root, env, timeoutMs }, ports);
    pathResults.push({ id: recipe.id, name: recipe.name, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs, status: r.ok ? 'proved' : 'failed', exitCode: r.exitCode, durationMs: r.durationMs, ok: r.ok, summary: r.summary });
  }
  if (unmappedSurfaces.length > 0) notProvedReasons.push(`No verify.paths recipe covers changed production surface(s): ${unmappedSurfaces.join(', ')}.`);

  const failedErrors = [
    ...baseVerify.errors.map(e => formatTeachingDetail({ invariant: e, fix: 'Fix the invalid "verify" block in pdd.json', rerun: 'pdd prove' })),
    ...lint.errors,
    ...diff.errors.filter(e => e.code !== 'diff-base-unavailable').map(e => e.formatted),
    ...(testResult && !testResult.ok ? [`Test suite failed (\`${testResult.command}\`, exit ${testResult.exitCode}): ${testResult.summary}`] : []),
    ...pathResults.filter(p => p.status === 'failed').map(p => `Verify path "${p.id}" failed (\`${p.run}\`, exit ${p.exitCode}): ${p.summary}`),
  ];

  const outcome = failedErrors.length > 0 ? OUTCOME_FAILED : (notProvedReasons.length > 0 ? OUTCOME_NOT_PROVED : OUTCOME_PROVED);
  const exitCode = outcome === OUTCOME_FAILED ? EXIT_FAILED : (outcome === OUTCOME_NOT_PROVED ? EXIT_NOT_PROVED : EXIT_PROVED);
  const receipt = {
    schema_version: 'pdd.prove.v1', mode: 'verify', outcome, exit_code: exitCode, baseRef, baseSha, headSha,
    configSource: baseVerify.source, touchedFiles: diff.touchedFiles, changedSurfaces,
    lint: { ok: lint.ok, errors: lint.errors, warnings: lint.warnings },
    diff: { ok: diff.ok, errors: diff.errors.map(e => e.formatted), advisories: diff.advisories },
    test: testResult, paths: pathResults, notProvedReasons,
  };

  if (json) stdout.write(`${JSON.stringify(receipt, null, 2)}\n`);
  else if (outcome === OUTCOME_PROVED) stdout.write(`Proved: lint clean, tests passed, ${pathResults.length} verify path(s) green.\n`);
  else if (outcome === OUTCOME_NOT_PROVED) stdout.write(`Not proved:\n${notProvedReasons.map(r => `  - ${r}`).join('\n')}\n`);
  else { for (const err of failedErrors) stderr.write(`${err}\n`); stderr.write(`Failed: ${failedErrors.length} check(s) failed.\n`); }
  return { exitCode, outcome, receipt };
}
