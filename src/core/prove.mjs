// Prompt: prompts/cli/prove.prompt.md

// Unified stateless `pdd prove` (G1): zero-flag merge-base verification + 5-bug-fixed bug-contrast mode.
import { spawnSync } from 'node:child_process';
import { closeSync, constants, existsSync, fchmodSync, fstatSync, lstatSync, mkdirSync, mkdtempSync, openSync, readFileSync, realpathSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, sep } from 'node:path';
import { isTestOwnedPath } from '../file-owner.mjs';
import { causeText } from '../shared/safe-read.mjs';
import { canonicalRepoPath, formatTeachingDetail, readSafeUtf8, resolveDefaultBaseRef, scrubChildEnv } from './lint/diagnostics.mjs';
import { lintRepoProject } from './lint/project-lint.mjs';
import { compileGlobMatcher } from './lint/regex-safety.mjs';
import { detectShadowBinaries, runDiffSpotlight } from './lint/test-inventory.mjs';
import { detectHostCapabilities, inspectMultiPartIntegrationGuard, loadVerifyConfig, matchCapabilities, matchVerifyPaths } from './verify-paths.mjs';

export const OUTCOME_PROVED = 'Proved';
export const OUTCOME_FAILED = 'Failed';
export const OUTCOME_NOT_PROVED = 'Not proved';
export const EXIT_PROVED = 0;
export const EXIT_FAILED = 1;
export const EXIT_USAGE = 2;
export const EXIT_NOT_PROVED = 3;

const SETUP_FAILURE_LINE_RE = /^(?:(?:Error:\s*Cannot find module\b|Error \[ERR_MODULE_NOT_FOUND\]|ERR_MODULE_NOT_FOUND\b|Cannot find package\b|ModuleNotFoundError:|ImportError:|No module named\b|SyntaxError:|FileNotFoundError:|Error:\s*ENOENT\b|ENOENT:|ERROR collecting\b|command not found\b|not recognized as an internal\b|cannot find package\b|no Go files\b|error\[E\d+\]:|failed to compile\b)|.*\[build failed\])/i;
const DIAG_PREFIX_RE = /^\s*(?:#\s*|E\s+)?/;
const TARGETABLE_ERROR_CLASS_RE = /^(SyntaxError|ImportError|FileNotFoundError):/i;
const COLOCATED_TEST_RE = /(?:\.(?:test|spec)\.(?:[cm]?[jt]s|[jt]sx)|(?:^|\/)test_[^/]+\.py$|_test\.(?:py|go|rs)$|^(?:test|tests|__tests__|fixtures)\/)/i;

function findSetupFailureLine(stderr, stdout) {
  // Scan stderr first so an actual diagnostic on stderr is NEVER shadowed by an arbitrary stdout banner.
  for (const stream of [stderr, stdout]) {
    for (const rawLine of String(stream ?? '').split(/\r?\n/)) {
      const normalizedLine = rawLine.replace(DIAG_PREFIX_RE, '').trim();
      if (!normalizedLine) continue;
      if (SETUP_FAILURE_LINE_RE.test(normalizedLine)) {
        const classMatch = TARGETABLE_ERROR_CLASS_RE.exec(normalizedLine);
        return { rawLine, normalizedLine, errorClass: classMatch ? classMatch[1] : null };
      }
    }
  }
  return null;
}

const gitExec = (cwd, args) => spawnSync('git', args, { cwd, encoding: 'utf8', maxBuffer: 32 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
const resolveGitRoot = cwd => { const r = gitExec(cwd, ['rev-parse', '--show-toplevel']); return r.status === 0 && r.stdout.trim() ? realpathSync(r.stdout.trim()) : realpathSync(cwd); };
const resolveCommit = (root, ref) => { const r = gitExec(root, ['rev-parse', '--verify', `${ref}^{commit}`]); return r.status === 0 && r.stdout.trim() ? r.stdout.trim() : null; };

const SEPARATOR_LINE_RE = /^[=\-*_~#\s]+$/;
const TEST_SUMMARY_LINE_RE = /\b(?:\d+\s+(?:passed|failed|passing|failing|errors?|skipped)|tests?\s+\d+|fail\s+\d+|pass\s+\d+|FAILED\b|ERROR\b|test result:|ok\s+\S+|FAIL\s+\S+)/i;

function summarizeTestOutput(stdout, stderr, setupError, timedOut) {
  const combined = `${stdout || ''}\n${stderr || ''}`
    .split(/\r?\n/)
    .map(l => l.trim())
    .filter(l => l && !SEPARATOR_LINE_RE.test(l));
  for (let i = combined.length - 1; i >= 0; i--) {
    if (TEST_SUMMARY_LINE_RE.test(combined[i])) return causeText(combined[i]);
  }
  if (combined.length > 0) return causeText(combined.at(-1));
  return causeText(setupError || (timedOut ? 'command timed out' : ''));
}

function execShellCommand(command, { cwd, env, timeoutMs, preScrubbed = false }, ports = {}) {
  const runner = ports.spawnSync ?? spawnSync;
  const started = Date.now();
  const proc = runner(command, { cwd, env: preScrubbed ? env : scrubChildEnv(env), shell: true, encoding: 'utf8', timeout: timeoutMs, maxBuffer: 16 * 1024 * 1024, stdio: ['ignore', 'pipe', 'pipe'] });
  const stdout = String(proc.stdout ?? ''), stderr = String(proc.stderr ?? '');
  const timedOut = proc.error?.code === 'ETIMEDOUT';
  const exitCode = typeof proc.status === 'number' ? proc.status : null;
  const signal = proc.signal ?? '';
  const hardSetupFailure = Boolean(
    (proc.error && !timedOut)
    || (signal && !timedOut)
    || (exitCode !== null && exitCode >= 129 && exitCode <= 192)
    || [126, 127].includes(exitCode),
  );
  const setupFailure = exitCode !== 0 && !hardSetupFailure ? findSetupFailureLine(stderr, stdout) : null;
  const setupError = proc.error && !timedOut
    ? causeText(proc.error.message)
    : (signal && !timedOut
        ? `Process terminated by signal ${signal}`
        : (exitCode !== null && exitCode >= 129 && exitCode <= 192
            ? `Command terminated by signal (exit ${exitCode})`
            : ([126, 127].includes(exitCode) ? `Command exited ${exitCode}` : (setupFailure ? causeText(setupFailure.normalizedLine) : ''))));
  return {
    command, ok: exitCode === 0 && !proc.error && !signal, exitCode, signal, timedOut,
    durationMs: Math.max(0, Date.now() - started), stdout, stderr, setupError, setupFailure, hardSetupFailure,
    summary: summarizeTestOutput(stdout, stderr, setupError, timedOut),
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
  if (existsSync(join(root, 'pyproject.toml')) || existsSync(join(root, 'pytest.ini')) || existsSync(join(root, 'setup.cfg'))) {
    return existsSync(join(root, 'src')) ? 'PYTHONPATH=src pytest' : 'pytest';
  }
  return null;
}

function listChangedFiles(root, ref) {
  const seen = new Set();
  if (ref) {
    const diff = gitExec(root, ['diff', '--no-renames', '--name-only', '-z', ref, '--']);
    if (diff.status !== 0) throw new Error(`git diff failed for ref "${ref}": ${causeText(diff.stderr || 'unknown error')}`);
    if (diff.stdout) for (const p of diff.stdout.split('\0').filter(Boolean)) seen.add(p);
  }
  const untracked = gitExec(root, ['ls-files', '--others', '--exclude-standard', '-z']);
  if (untracked.status !== 0) throw new Error(`git ls-files failed: ${causeText(untracked.stderr || 'unknown error')}`);
  if (untracked.stdout) for (const p of untracked.stdout.split('\0').filter(Boolean)) seen.add(p);
  return [...seen].filter(canonicalRepoPath).sort();
}

function lstatSafe(fullPath) {
  try { return lstatSync(fullPath); }
  catch (err) { if (err?.code === 'ENOENT') return null; throw err; }
}

function assertDirWithin(baseReal, fullPath, relPath) {
  const dirReal = realpathSync(dirname(fullPath));
  if (dirReal !== baseReal && !dirReal.startsWith(`${baseReal}${sep}`)) {
    throw new Error(`Refused escaping parent directory for overlay path: ${relPath}`);
  }
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
  assertDirWithin(baseReal, fullPath, relPath);
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
          assertDirWithin(wtReal, dstInfo.fullPath, rel);
          rmSync(dstInfo.fullPath, { force: true });
          assertDirWithin(wtReal, dstInfo.fullPath, rel);
          mirrored.push(rel);
        }
      }
      continue;
    }
    if (!srcInfo.leafStat.isFile()) throw new Error(`Refused non-regular overlay file: ${rel}`);
    assertDirWithin(rootReal, srcInfo.fullPath, rel);
    const rfd = openSync(srcInfo.fullPath, constants.O_RDONLY | (constants.O_NOFOLLOW ?? 0));
    let bytes, mode;
    try {
      const rst = fstatSync(rfd);
      if (!rst.isFile()) throw new Error(`Overlay path changed to non-regular file: ${rel}`);
      assertDirWithin(rootReal, srcInfo.fullPath, rel);
      mode = rst.mode & 0o777;
      bytes = readFileSync(rfd);
    } finally { closeSync(rfd); }
    const dstInfo = walkCheckedSegments(wtReal, rel, { createDirs: true });
    if (dstInfo.leafStat && !dstInfo.leafStat.isFile()) throw new Error(`Refused non-regular destination in worktree: ${rel}`);
    assertDirWithin(wtReal, dstInfo.fullPath, rel);
    const wfd = openSync(dstInfo.fullPath, constants.O_WRONLY | constants.O_CREAT | constants.O_TRUNC | (constants.O_NOFOLLOW ?? 0), mode);
    try {
      writeFileSync(wfd, bytes);
      fchmodSync(wfd, mode);
    } finally { closeSync(wfd); }
    assertDirWithin(wtReal, dstInfo.fullPath, rel);
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

const NPM_BUILTIN_SUBCMDS = new Set([
  'install', 'i', 'ci', 'exec', 'dlx', 'add', 'remove', 'rm', 'update', 'up', 'publish', 'pack',
  'version', 'audit', 'list', 'ls', 'outdated', 'config', 'cache', 'whoami', 'login', 'logout',
  'info', 'view', 'init', 'create', 'link', 'unlink', 'prune', 'dedupe', 'why', 'explain', 'help', 'run',
]);

function extractReferencedNpmScripts(commands = []) {
  const names = new Set(['test', 'pretest', 'posttest']);
  for (const cmd of commands) {
    if (typeof cmd !== 'string' || !cmd.trim()) continue;
    for (const m of cmd.matchAll(/(?:^|[;&|]\s*)(?:npm|pnpm|yarn)\s+(?:run\s+)?([A-Za-z0-9_.:-]+)/g)) {
      const token = m[1];
      if (!token || token.startsWith('-') || NPM_BUILTIN_SUBCMDS.has(token)) continue;
      const script = (token === 't' || token === 'tst') ? 'test' : token;
      names.add(script);
      names.add(`pre${script}`);
      names.add(`post${script}`);
    }
  }
  return [...names];
}

function detectUntrustedPackageTestScriptEdits(root, baseSha, commands) {
  const baseRes = gitExec(root, ['show', `${baseSha}:package.json`]);
  const baseRaw = baseRes.status === 0 && typeof baseRes.stdout === 'string' ? baseRes.stdout : null;
  const wtRaw = readSafeUtf8(root, 'package.json');
  if (baseRaw === null && wtRaw === null) return [];
  if (baseRaw === wtRaw) return [];

  let baseScripts = null, wtScripts = null;
  let baseInvalid = false, wtInvalid = false;
  if (baseRaw !== null) {
    try { baseScripts = JSON.parse(baseRaw)?.scripts ?? {}; } catch { baseInvalid = true; }
  }
  if (wtRaw !== null) {
    try { wtScripts = JSON.parse(wtRaw)?.scripts ?? {}; } catch { wtInvalid = true; }
  }
  if (baseInvalid || wtInvalid) return ['package.json'];

  const changed = [];
  for (const name of extractReferencedNpmScripts(commands)) {
    const bVal = typeof baseScripts?.[name] === 'string' ? baseScripts[name] : undefined;
    const wVal = typeof wtScripts?.[name] === 'string' ? wtScripts[name] : undefined;
    if (bVal !== wVal) changed.push(`scripts.${name}`);
  }
  return changed;
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
  const baseSha = mbRes?.status === 0 && mbRes.stdout.trim() ? mbRes.stdout.trim() : null;

  if (!baseSha || !headSha) {
    const receipt = {
      schema_version: 'pdd.prove.v1', mode: 'bug-contrast', outcome: OUTCOME_NOT_PROVED, reason: 'base-unavailable',
      exit_code: EXIT_NOT_PROVED, baseRef: requestedBase, baseSha, headSha, overlayPaths: [], test, expect,
      base: null, head: null, notProvedReasons: [`Offline merge-base between HEAD and "${requestedBase}" could not be resolved locally.`],
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

  const timeoutMs = timeoutMinutes * 60_000;
  const worktreeParent = mkdtempSync(join(tmpdir(), 'pdd-prove-'));
  const baseWorktree = join(worktreeParent, 'base');
  const headWorktree = join(worktreeParent, 'head');
  const createdWorktrees = [];
  let basePhase = null, headPhase = null, setupError = '', copiedPaths = [];

  try {
    const changedFromBase = listChangedFiles(root, baseSha);
    // Always union colocated/repo test files with explicit --overlay globs so fixture overlays never drop the regression test.
    const overlayPaths = changedFromBase.filter(
      f => COLOCATED_TEST_RE.test(f) || isTestOwnedPath(f) || overlayGlobs.some(m => m.test(f)),
    );
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
    const baseTextHasExpect = !basePhase.signal && !basePhase.timedOut && (basePhase.stdout.includes(expect) || basePhase.stderr.includes(expect));
    // Clear SyntaxError/ImportError/FileNotFoundError ONLY when --expect names that error class WITH detail
    // (never bare class alone) AND matches the ACTUAL normalized diagnostic error line (never a separate banner).
    const trimmedExpect = expect.trim();
    const errLine = basePhase.setupFailure;
    const expectTargetsErrorClass = Boolean(
      !basePhase.hardSetupFailure
      && errLine?.errorClass
      && trimmedExpect.toLowerCase() !== errLine.errorClass.toLowerCase()
      && trimmedExpect.toLowerCase() !== `${errLine.errorClass.toLowerCase()}:`
      && new RegExp(`\\b${errLine.errorClass}\\b`, 'i').test(trimmedExpect)
      && errLine.normalizedLine.includes(trimmedExpect),
    );
    if (expectTargetsErrorClass) basePhase.setupError = '';
    basePhase.expectedFound = !basePhase.setupError && baseTextHasExpect;
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
    notProvedReasons.push(`Setup/dependency/compile failure prevented causal bug-contrast proof: ${setupError || basePhase?.setupError || headPhase?.setupError || basePhase?.signal || headPhase?.signal}. Pass --setup CMD if dependencies must be installed in fresh worktrees.`);
  } else if (basePhase?.timedOut || headPhase?.timedOut) {
    outcome = OUTCOME_NOT_PROVED; reason = basePhase?.timedOut ? 'base-timeout' : 'head-timeout'; exitCode = EXIT_NOT_PROVED;
    notProvedReasons.push(`Bug-contrast ${basePhase?.timedOut ? 'base' : 'head'} run timed out after ${timeoutMinutes} min; rerun with --timeout MIN.`);
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
  const baseSha = mb?.status === 0 && mb.stdout.trim() ? mb.stdout.trim() : null;
  const timeoutMs = timeoutMinutes * 60_000;

  const lint = lintRepoProject({ root, enforceBaseTrust: true, trustBaseRef: baseSha || baseRef || undefined, requireFullStoryCriteria: true });
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
  if (lint.untrustedConfigOverrides?.length > 0) {
    notProvedReasons.push(`Working-tree/branch lint overrides (${lint.untrustedConfigOverrides.join(', ')}) are not yet trusted on merge base; human review required.`);
  }

  const testCommand = baseVerify.test || detectRepoTestCommand(root);
  const changedPkgScripts = detectUntrustedPackageTestScriptEdits(root, baseSha, [testCommand, ...baseVerify.paths.map(r => r.run)]);
  if (changedPkgScripts.length > 0) {
    notProvedReasons.push(`Working-tree/branch edits to package.json test scripts (${changedPkgScripts.join(', ')}) are not yet trusted on merge base; human review required.`);
  }

  const shadowBins = detectShadowBinaries(root, { touchedFiles: diff.touchedFiles, baseSha });
  const extraShadowErrors = [];
  for (const hit of shadowBins) {
    if (!diff.errors.some(e => e.code === 'diff-shadow-bin' && e.path === hit.path)) {
      const detail = formatTeachingDetail({
        invariant: `Shadow binary "${hit.path}" detected (${hit.reason})`,
        fix: `Remove "${hit.path}" so repository commands execute the authentic host toolchain`,
        rerun: 'pdd prove',
      });
      extraShadowErrors.push(`Error: diff gate: ${hit.path}:1 [diff-shadow-bin] ${detail}`);
    }
  }

  // Inspect checkout cleanliness BEFORE executing tests/recipes so generated reports don't falsely dirty a clean commit,
  // and fail closed as `Not proved` if `git status` itself fails (NEVER certifying an uninspected checkout as clean).
  const statusRes = gitExec(root, ['status', '--porcelain']);
  const statusFailed = statusRes.status !== 0 || Boolean(statusRes.error);
  const dirtyFiles = !statusFailed && statusRes.stdout
    ? statusRes.stdout.split(/\r?\n/).map(l => l.slice(3).trim()).filter(Boolean)
    : [];
  const dirty = statusFailed || dirtyFiles.length > 0;
  const proofScope = statusFailed ? 'unknown' : (dirty ? 'working-tree' : 'commit');
  if (statusFailed) {
    notProvedReasons.push(`Could not inspect working-tree cleanliness (git status exited ${statusRes.status ?? 'error'}).`);
  }

  let testResult = null;
  const { matched, changedSurfaces, unmappedSurfaces } = matchVerifyPaths(baseVerify, diff.touchedFiles);
  const pathResults = [];
  const scrubbedBaseEnv = scrubChildEnv(env);
  const resolveStepEnv = (phase, recipeId, command) => (
    typeof ports.envForStep === 'function'
      ? ports.envForStep({ phase, recipeId, command, baseEnv: scrubbedBaseEnv })
      : scrubbedBaseEnv
  );
  if (shadowBins.length === 0) {
    if (testCommand) {
      const testEnv = resolveStepEnv('test', null, testCommand);
      const r = execShellCommand(testCommand, { cwd: root, env: testEnv, timeoutMs, preScrubbed: true }, ports);
      testResult = { command: testCommand, ok: r.ok, timedOut: r.timedOut, exitCode: r.exitCode, durationMs: r.durationMs, setupError: r.setupError, summary: r.summary };
      if (r.timedOut) {
        notProvedReasons.push(`Test suite timed out after ${timeoutMinutes} min (\`${testCommand}\`); rerun with --timeout MIN.`);
      }
    } else {
      notProvedReasons.push('No verify.test command configured in merge-base pdd.json and no standard test runner detected.');
    }

    const capState = detectHostCapabilities(matched.flatMap(r => r.needs), { env, capabilities, probe: ports.probeCapability, isTTY: ports.isTTY });
    for (const recipe of matched) {
      const { satisfied, missing } = matchCapabilities(recipe.needs, capState);
      if (!satisfied) {
        pathResults.push({ id: recipe.id, name: recipe.name, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs, status: 'not-proved', missingCapabilities: missing, ok: false });
        notProvedReasons.push(`Recipe "${recipe.id}" (${recipe.name}) skipped: missing required capability [${missing.join(', ')}].`);
        continue;
      }
      const recipeEnv = resolveStepEnv('path', recipe.id, recipe.run);
      const r = execShellCommand(recipe.run, { cwd: root, env: recipeEnv, timeoutMs, preScrubbed: true }, ports);
      if (r.timedOut) {
        pathResults.push({ id: recipe.id, name: recipe.name, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs, status: 'not-proved', timedOut: true, exitCode: r.exitCode, durationMs: r.durationMs, ok: false, summary: r.summary });
        notProvedReasons.push(`Verify path "${recipe.id}" timed out after ${timeoutMinutes} min (\`${recipe.run}\`); rerun with --timeout MIN.`);
        continue;
      }
      pathResults.push({ id: recipe.id, name: recipe.name, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs, status: r.ok ? 'proved' : 'failed', timedOut: false, exitCode: r.exitCode, durationMs: r.durationMs, ok: r.ok, summary: r.summary });
    }
  }
  if (unmappedSurfaces.length > 0) notProvedReasons.push(`No verify.paths recipe covers changed production surface(s): ${unmappedSurfaces.join(', ')}.`);
  const multiPartGuard = inspectMultiPartIntegrationGuard(root, baseVerify, { executedPathResults: pathResults, changedSurfaces });
  if (multiPartGuard.applicable && !multiPartGuard.covered && multiPartGuard.reason) {
    notProvedReasons.push(multiPartGuard.reason);
  }

  const touchedSet = new Set(diff.touchedFiles);
  for (const finding of lint.findings) {
    if (finding.code === 'product-boundary-unwired' || finding.code === 'product-boundaries-unparseable') {
      notProvedReasons.push(`${finding.path}:${finding.line} [${finding.code}] ${finding.message}`);
    } else if (finding.code === 'story-unbound-criteria') {
      const slug = finding.path.split('/').at(-1).replace(/\.md$/i, '');
      const touched = touchedSet.has(finding.path)
        || diff.touchedFiles.some(tf => /(?:^|\/)(?:tests?|__tests__)\/.*\.json$/i.test(tf) && (tf.endsWith(`/${slug}.json`) || tf.includes(`/${slug}.`)));
      if (touched) notProvedReasons.push(`${finding.path}:${finding.line} [story-unbound-criteria] ${finding.message}`);
    }
  }
  if (diff.newSkips.length > 0) {
    notProvedReasons.push(`[diff-new-skips] Diff introduces ${diff.newSkips.length} new skipped test(s) (${diff.newSkips.slice(0, 6).map(s => `${s.path}:${s.line} ${s.name}`).join(', ')}); human review required.`);
  }
  if (diff.assertionDrops.length > 0) {
    notProvedReasons.push(`[diff-assertion-drops] Diff reduces assertion count in ${diff.assertionDrops.length} kept test(s) (${diff.assertionDrops.slice(0, 6).map(a => `${a.path}::${a.name} ${a.before}->${a.after}`).join(', ')}); human review required.`);
  }
  if (diff.removedTests.length > 0) {
    notProvedReasons.push(`[diff-removed-tests] Diff removes ${diff.removedTests.length} test(s) (${diff.removedTests.slice(0, 6).map(r => `${r.path}::${r.name}`).join(', ')}); human review required.`);
  }
  if (diff.tableDrops.length > 0) {
    notProvedReasons.push(`[diff-table-drops] Diff reduces table-driven test case count in ${diff.tableDrops.map(t => `${t.path} (${t.before}->${t.after})`).join(', ')}; human review required.`);
  }
  if (diff.mockOnlyBoundaryTests?.length > 0) {
    for (const entry of diff.mockOnlyBoundaryTests) {
      const detail = formatTeachingDetail({
        invariant: `Changed I/O/subprocess boundary file(s) (${entry.prodFiles.join(', ')}) are only covered by mocked tests (${entry.testFiles.join(', ')}) with zero real unmocked boundary calls`,
        fix: `Add a real non-mocked integration test exercising ${entry.prodFiles.join(', ')} against an actual local server or subprocess`,
        rerun: 'pdd prove',
      });
      notProvedReasons.push(`${entry.testFiles[0]}:1 [diff-mock-only-boundary] ${detail}`);
    }
  }

  const failedErrors = [
    ...baseVerify.errors.map(e => formatTeachingDetail({ invariant: e, fix: 'Fix the invalid "verify" block in pdd.json', rerun: 'pdd prove' })),
    ...lint.errors,
    ...diff.errors.filter(e => e.code !== 'diff-base-unavailable').map(e => e.formatted),
    ...extraShadowErrors,
    ...(testResult && !testResult.ok && !testResult.timedOut ? [`Test suite failed (\`${testResult.command}\`, exit ${testResult.exitCode}): ${testResult.summary}`] : []),
    ...pathResults.filter(p => p.status === 'failed').map(p => `Verify path "${p.id}" failed (\`${p.run}\`, exit ${p.exitCode}): ${p.summary}`),
  ];

  const outcome = failedErrors.length > 0 ? OUTCOME_FAILED : (notProvedReasons.length > 0 ? OUTCOME_NOT_PROVED : OUTCOME_PROVED);
  const exitCode = outcome === OUTCOME_FAILED ? EXIT_FAILED : (outcome === OUTCOME_NOT_PROVED ? EXIT_NOT_PROVED : EXIT_PROVED);
  const receipt = {
    schema_version: 'pdd.prove.v1', mode: 'verify', outcome, exit_code: exitCode, baseRef, baseSha, headSha,
    dirty, proofScope, ...(dirtyFiles.length ? { dirtyFiles: dirtyFiles.slice(0, 12) } : {}),
    configSource: baseVerify.configured ? baseVerify.source : (testCommand ? 'auto-detected' : null), touchedFiles: diff.touchedFiles, changedSurfaces,
    lint: { ok: lint.ok, errors: lint.errors, warnings: lint.warnings },
    diff: { ok: diff.ok, errors: diff.errors.map(e => e.formatted), advisories: diff.advisories },
    test: testResult, paths: pathResults, notProvedReasons,
  };

  const scopeSuffix = statusFailed
    ? ' (unknown checkout cleanliness)'
    : (dirty ? ` (working tree, uncommitted changes: ${dirtyFiles.slice(0, 4).join(', ')})` : '');
  if (json) stdout.write(`${JSON.stringify(receipt, null, 2)}\n`);
  else if (outcome === OUTCOME_PROVED) stdout.write(`Proved${scopeSuffix}: lint clean, tests passed, ${pathResults.length} verify path(s) green.\n`);
  else if (outcome === OUTCOME_NOT_PROVED) stdout.write(`Not proved${scopeSuffix}:\n${notProvedReasons.map(r => `  - ${r}`).join('\n')}\n`);
  else { for (const err of failedErrors) stderr.write(`${err}\n`); stderr.write(`Failed${scopeSuffix}: ${failedErrors.length} check(s) failed.\n`); }
  return { exitCode, outcome, receipt };
}
