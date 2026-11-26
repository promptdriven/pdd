// Prompt: prompts/cli/prove.prompt.md

// Unified stateless `pdd prove` (G1): zero-flag merge-base verification + 5-bug-fixed bug-contrast mode.
import { spawn, spawnSync } from 'node:child_process';
import { closeSync, constants, existsSync, fchmodSync, fstatSync, lstatSync, mkdirSync, mkdtempSync, openSync, readFileSync, realpathSync, rmSync, symlinkSync, unlinkSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { dirname, join, sep } from 'node:path';
import { isTestOwnedPath } from '../file-owner.mjs';
import { READONLY_PROVIDERS, redactReadonlyOutput, runReadonlyAgent } from '../shared/readonly-agent.mjs';
import { causeText } from '../shared/safe-read.mjs';
import { executableMissing } from '../shared/subprocess.mjs';
import { COLOCATED_TEST_PATH_RE, TEST_SCENARIO_JSON_RE, TEST_TARGET_FILE_RE, detectPytestConfigEdits, isConfiguredTestPath, readPytestTestpaths } from '../shared/test-paths.mjs';
import { canonicalRepoPath, formatTeachingDetail, readSafeUtf8, resolveDefaultBaseRef, scrubChildEnv } from './lint/diagnostics.mjs';
import { lintRepoProject } from './lint/project-lint.mjs';
import { compileGlobMatcher } from './lint/regex-safety.mjs';
import { detectShadowBinaries, runDiffSpotlight } from './lint/test-inventory.mjs';
import { runFormalVerification } from './formal-verify.mjs';
import { classifyVerifyPathTier, detectHostCapabilities, formatProofTiersLine, inspectMultiPartIntegrationGuard, loadVerifyConfig, matchCapabilities, matchVerifyPaths, summarizeProofTiers } from './verify-paths.mjs';

export const OUTCOME_PROVED = 'Proved';
export const OUTCOME_FAILED = 'Failed';
export const OUTCOME_NOT_PROVED = 'Not proved';
export const EXIT_PROVED = 0;
export const EXIT_FAILED = 1;
export const EXIT_USAGE = 2;
export const EXIT_NOT_PROVED = 3;

const DEFAULT_IDLE_WINDOW_MS = 5 * 60_000;
const DEFAULT_REPEAT_LOOP_THRESHOLD = 50;
const DEFAULT_OFFLINE_REPEAT_FLOOR = 200;
const DEFAULT_MAX_LLM_CONTINUES = 6;
const DEFAULT_MAX_SILENT_LLM_CONTINUES = 3;
const MAX_CAPTURE_BYTES = 16 * 1024 * 1024;
const TAIL_CAPTURE_BYTES = 2 * 1024 * 1024;
const STUCK_CHECK_TAIL_LINES = 50;
const FROZEN_TAIL_REPORT_LINES = 15;
const KILL_GRACE_MS = 2000;

const SETUP_FAILURE_LINE_RE = /^(?:(?:Error:\s*Cannot find module\b|Error \[ERR_MODULE_NOT_FOUND\]|ERR_MODULE_NOT_FOUND\b|Cannot find package\b|ModuleNotFoundError:|ImportError:|No module named\b|SyntaxError:|FileNotFoundError:|Error:\s*ENOENT\b|ENOENT:|ERROR collecting\b|command not found\b|not recognized as an internal\b|cannot find package\b|no Go files\b|error\[E\d+\]:|failed to compile\b)|.*\[build failed\])/i;
const MISSING_RUNNER_OUTPUT_RE = /(?:^|\n)\s*(?:.*:\s*)?(?:No module named ['"]?(?:pytest|unittest)['"]?|command not found\b|not recognized as an internal\b|executable file not found in \$PATH\b)/i;
const DIAG_PREFIX_RE = /^\s*(?:#\s*|E\s+)?/;
const TARGETABLE_ERROR_CLASS_RE = /^(SyntaxError|ImportError|FileNotFoundError):/i;
const COLOCATED_TEST_RE = COLOCATED_TEST_PATH_RE;

const DEP_MANIFEST_OR_LOCKFILE_RE = /(?:^|\/)(?:package\.json|package-lock\.json|npm-shrinkwrap\.json|pnpm-lock\.yaml|yarn\.lock|bun\.lockb?|pyproject\.toml|poetry\.lock|uv\.lock|Pipfile(?:\.lock)?|setup\.(?:py|cfg)|requirements(?:[-_.][^/]*)?\.txt)$/;
const LOCAL_DEP_DIRS = Object.freeze(['node_modules', '.venv', 'venv']);

const STUCK_CHECK_SCHEMA = Object.freeze({
  type: 'object',
  required: ['verdict', 'reason'],
  additionalProperties: false,
  properties: {
    verdict: { type: 'string', enum: ['progress', 'stuck'] },
    reason: { type: 'string', minLength: 1, maxLength: 300 },
  },
});

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
const WARNING_LINE_RE = /^(?:[A-Za-z0-9_.-]*Warning:|\[?WARN(?:ING)?\]?[:\s]|WARNING\b|DeprecationWarning:|PendingDeprecationWarning:|UserWarning:|RuntimeWarning:|ResourceWarning:|FutureWarning:|Pytest[A-Za-z]*Warning:)|\b(?:Pytest[A-Za-z]*Warning|DeprecationWarning|PendingDeprecationWarning|UserWarning|ResourceWarning|FutureWarning|RuntimeWarning):/i;
const CANONICAL_SUMMARY_LINE_RE = /(?:^=+\s+.*\b\d+\s+(?:passed|failed|error(?:s)?|skipped|xfailed|xpassed|deselected|warnings?)\b.*=+$|\b\d+\s+(?:passed|failed|passing|failing|errors?|skipped)\b|^#\s*(?:tests|pass|fail)\s+\d+\b|^test result:\s+(?:ok|FAILED)\.|^(?:ok|FAIL)\s+\S+(?:\s+[\d.]+s|\s+\[)|^(?:Test Files|Tests|Test Suites:)\s+\d+|\b\d+\s+examples?,\s+\d+\s+failures?\b|\bTests run:\s*\d+,\s*Failures:\s*\d+|\b\d+%\s+tests passed,\s+\d+\s+tests failed out of\s+\d+|\bExecuted\s+\d+\s+tests?,\s+with\s+\d+\s+failures?\b)/i;
const GENERIC_SUMMARY_LINE_RE = /(?:\b(?:tests?\s+\d+|fail\s+\d+|pass\s+\d+|test result:)|\bFAILED\b|\bERROR\b|^(?:ok|FAIL)\s+\S+)/;

export function summarizeTestOutput(stdout, stderr, setupError, timedOut, stuckReason = '') {
  const combined = `${stdout || ''}\n${stderr || ''}`
    .split(/\r?\n/)
    .map(l => l.trim())
    .filter(l => l && !SEPARATOR_LINE_RE.test(l));
  const nonWarning = combined.filter(l => !WARNING_LINE_RE.test(l));
  for (let i = nonWarning.length - 1; i >= 0; i--) {
    if (CANONICAL_SUMMARY_LINE_RE.test(nonWarning[i])) return causeText(nonWarning[i]);
  }
  for (let i = nonWarning.length - 1; i >= 0; i--) {
    if (GENERIC_SUMMARY_LINE_RE.test(nonWarning[i])) return causeText(nonWarning[i]);
  }
  if (nonWarning.length > 0) return causeText(nonWarning.at(-1));
  if (combined.length > 0) return causeText(combined.at(-1));
  return causeText(stuckReason || setupError || (timedOut ? 'command timed out' : ''));
}

const TIMESTAMP_PREFIX_RE = /^(?:\[?\d{4}-\d{2}-\d{2}[T ]\d{2}:\d{2}:\d{2}(?:\.\d+)?Z?\]?\s*|\[\d{2}:\d{2}:\d{2}(?:\.\d+)?\]\s*|\d{2}:\d{2}:\d{2}(?:\.\d+)?\s+)/;
const DOTS_OR_SPINNER_RE = /^[.\s|/\\-]+$/;

function normalizeProgressLine(line) {
  const trimmed = String(line ?? '').trim();
  if (!trimmed || trimmed.length < 4 || SEPARATOR_LINE_RE.test(trimmed) || DOTS_OR_SPINNER_RE.test(trimmed)) return '';
  return trimmed.replace(TIMESTAMP_PREFIX_RE, '').trim();
}

function formatDurationBrief(ms) {
  const totalSec = Math.max(0, Math.round(ms / 1000));
  if (totalSec < 60) return `${totalSec}s`;
  const mins = Math.floor(totalSec / 60);
  const secs = totalSec % 60;
  return secs > 0 ? `${mins}m ${secs}s` : `${mins}m`;
}

function formatCompletedPhases(completedPhases) {
  if (!Array.isArray(completedPhases) || completedPhases.length === 0) return 'none';
  return completedPhases.map(p => `${p.phase} (${p.status})`).join(', ');
}

function formatFrozenTail(frozenTail) {
  if (!Array.isArray(frozenTail) || frozenTail.length === 0) return '(no output captured)';
  return causeText(frozenTail.slice(-5).join(' | '));
}

function getTailLines(recentLines, stdoutCarry, stderrCarry, maxLines) {
  const merged = [...recentLines];
  for (const carry of [stdoutCarry, stderrCarry]) {
    const t = String(carry ?? '').trim();
    if (t) merged.push(t.slice(0, 500));
  }
  return merged.slice(-maxLines);
}

function buildShellResult({
  command, stdout, stderr, exitCode, signal, procError, timedOut, stuck, stuckReason, stuckTrigger, stuckSource,
  frozenTail, durationMs,
}) {
  const ok = exitCode === 0 && !procError && !signal && !timedOut && !stuck;
  const hardSetupFailure = Boolean(
    (procError && !timedOut && !stuck)
    || (signal && !timedOut && !stuck)
    || (exitCode !== null && exitCode >= 129 && exitCode <= 192)
    || [126, 127].includes(exitCode),
  );
  const missingRunnerFailure = Boolean(
    !ok
    && !timedOut
    && !stuck
    && (hardSetupFailure || MISSING_RUNNER_OUTPUT_RE.test(`${stderr}\n${stdout}`)),
  );
  const setupFailure = exitCode !== 0 && !hardSetupFailure && !timedOut && !stuck ? findSetupFailureLine(stderr, stdout) : null;
  const setupError = procError && !timedOut && !stuck
    ? causeText(procError.message)
    : (signal && !timedOut && !stuck
        ? `Process terminated by signal ${signal}`
        : (exitCode !== null && exitCode >= 129 && exitCode <= 192
            ? `Command terminated by signal (exit ${exitCode})`
            : ([126, 127].includes(exitCode) ? `Command exited ${exitCode}` : (setupFailure ? causeText(setupFailure.normalizedLine) : ''))));
  return {
    command,
    ok,
    exitCode,
    signal,
    timedOut,
    stuck,
    stuckReason,
    stuckTrigger,
    stuckSource,
    frozenTail,
    durationMs,
    stdout,
    stderr,
    setupError,
    setupFailure,
    hardSetupFailure,
    missingRunnerFailure,
    summary: summarizeTestOutput(stdout, stderr, setupError, timedOut, stuckReason),
  };
}

async function defaultStuckCheck({ phase, command, trigger, idleMs, elapsedMs, tailLines, cwd, env, signal }) {
  if (String(env?.PDD_PROVE_LLM_WATCH ?? '').trim() === '0') return null;
  const preferred = String(env?.PDD_PROVE_LLM_PROVIDER ?? '').trim().toLowerCase();
  const ordered = [
    ...(READONLY_PROVIDERS.includes(preferred) ? [preferred] : []),
    ...READONLY_PROVIDERS.filter(p => p !== preferred),
  ];
  const provider = ordered.find(p => !executableMissing(p, { cwd, env }));
  if (!provider) return null;

  const redactedTail = redactReadonlyOutput((tailLines ?? []).slice(-STUCK_CHECK_TAIL_LINES).join('\n'), { env });
  const triggerText = trigger === 'repeat-loop'
    ? 'repeated identical output lines in a tight loop'
    : `produced no new output for ${formatDurationBrief(idleMs)}`;
  const prompt = [
    'You are monitoring a running command for `pdd prove`.',
    `Phase: ${phase}`,
    `Command: ${command}`,
    `Elapsed: ${formatDurationBrief(elapsedMs)}`,
    `Observation: ${triggerText}`,
    '',
    'Last ~50 output lines:',
    '```',
    redactedTail || '(no output)',
    '```',
    '',
    'Decide whether this command is making genuine slow progress (compiling, linking, or running a large test) or is stuck/hung/deadlocked/looping.',
    'Reply strictly with JSON: {"verdict":"progress"|"stuck","reason":"<one short sentence>"}',
  ].join('\n');

  try {
    const res = await runReadonlyAgent({
      provider,
      prompt,
      cwd,
      env,
      signal,
      timeoutMs: 30_000,
      disableTools: true,
      jsonSchema: STUCK_CHECK_SCHEMA,
    });
    if (res?.ok && (res.parsed?.verdict === 'progress' || res.parsed?.verdict === 'stuck')) {
      return {
        verdict: res.parsed.verdict,
        reason: String(res.parsed.reason || '').trim() || res.parsed.verdict,
        source: `llm:${provider}`,
      };
    }
  } catch {
    // Fall back cleanly to offline idle policy.
  }
  return null;
}

function appendBounded(current, chunkText) {
  const next = current + chunkText;
  if (next.length <= MAX_CAPTURE_BYTES) return next;
  return next.slice(next.length - TAIL_CAPTURE_BYTES);
}

async function execShellCommand(
  command,
  {
    cwd,
    env,
    rawEnv = env,
    timeoutMs = null,
    idleTimeoutMs = DEFAULT_IDLE_WINDOW_MS,
    repeatLoopThreshold = DEFAULT_REPEAT_LOOP_THRESHOLD,
    explicitRepeatThreshold = false,
    phase = 'command',
    preScrubbed = false,
  },
  ports = {},
) {
  const childEnv = preScrubbed ? env : scrubChildEnv(env);
  if (typeof ports.spawnSync === 'function') {
    const started = Date.now();
    const proc = ports.spawnSync(command, {
      cwd,
      env: childEnv,
      shell: true,
      encoding: 'utf8',
      ...(timeoutMs ? { timeout: timeoutMs } : {}),
      maxBuffer: MAX_CAPTURE_BYTES,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    const stdout = String(proc.stdout ?? '');
    const stderr = String(proc.stderr ?? '');
    const timedOut = proc.error?.code === 'ETIMEDOUT';
    const exitCode = typeof proc.status === 'number' ? proc.status : null;
    const signal = proc.signal ?? '';
    const lines = `${stdout}\n${stderr}`.split(/\r?\n/).map(l => l.trim()).filter(Boolean);
    return buildShellResult({
      command,
      stdout,
      stderr,
      exitCode,
      signal,
      procError: proc.error ?? null,
      timedOut,
      stuck: false,
      stuckReason: '',
      stuckTrigger: null,
      stuckSource: null,
      frozenTail: timedOut ? lines.slice(-FROZEN_TAIL_REPORT_LINES) : [],
      durationMs: Math.max(0, Date.now() - started),
    });
  }

  const spawner = ports.spawn ?? spawn;
  const stuckChecker = typeof ports.checkStuck === 'function'
    ? ports.checkStuck
    : (typeof ports.stuckCheck === 'function' ? ports.stuckCheck : defaultStuckCheck);
  const effectiveIdleMs = Math.max(25, Number.isFinite(idleTimeoutMs) && idleTimeoutMs > 0 ? idleTimeoutMs : DEFAULT_IDLE_WINDOW_MS);
  const effectiveRepeat = Math.max(2, Number.isInteger(repeatLoopThreshold) && repeatLoopThreshold > 0 ? repeatLoopThreshold : DEFAULT_REPEAT_LOOP_THRESHOLD);
  const offlineRepeatKill = explicitRepeatThreshold ? effectiveRepeat : Math.max(effectiveRepeat, DEFAULT_OFFLINE_REPEAT_FLOOR);
  const maxLlmContinues = Number.isInteger(ports.maxLlmContinues) && ports.maxLlmContinues > 0 ? ports.maxLlmContinues : DEFAULT_MAX_LLM_CONTINUES;
  const maxSilentContinues = Number.isInteger(ports.maxSilentContinues) && ports.maxSilentContinues > 0 ? ports.maxSilentContinues : DEFAULT_MAX_SILENT_LLM_CONTINUES;

  return new Promise(resolveRun => {
    const started = Date.now();
    let child = null;
    let stdout = '';
    let stderr = '';
    let stdoutCarry = '';
    let stderrCarry = '';
    const recentLines = [];
    let lastActivityAt = started;
    let lastNormLine = '';
    let repeatCount = 0;
    let checkingStuck = false;
    let llmContinueCount = 0;
    let silentContinueCount = 0;
    let hadNewBytesSinceCheck = false;
    let settled = false;
    let stopping = false;
    let timedOut = false;
    let stuck = false;
    let stuckReason = '';
    let stuckTrigger = null;
    let stuckSource = null;
    let hardTimer = null;
    let idleInterval = null;
    let killTimer = null;
    let failsafeTimer = null;
    const stuckAbort = new AbortController();

    const clearAllTimers = () => {
      if (hardTimer) { clearTimeout(hardTimer); hardTimer = null; }
      if (idleInterval) { clearInterval(idleInterval); idleInterval = null; }
      if (killTimer) { clearTimeout(killTimer); killTimer = null; }
      if (failsafeTimer) { clearTimeout(failsafeTimer); failsafeTimer = null; }
      if (!stuckAbort.signal.aborted) stuckAbort.abort();
    };

    const finish = (procError, exitCode, signal) => {
      if (settled) return;
      settled = true;
      clearAllTimers();
      const tail = (timedOut || stuck) ? getTailLines(recentLines, stdoutCarry, stderrCarry, FROZEN_TAIL_REPORT_LINES) : [];
      resolveRun(buildShellResult({
        command,
        stdout,
        stderr,
        exitCode: typeof exitCode === 'number' ? exitCode : null,
        signal: signal ?? '',
        procError: procError ?? null,
        timedOut,
        stuck,
        stuckReason,
        stuckTrigger,
        stuckSource,
        frozenTail: tail,
        durationMs: Math.max(0, Date.now() - started),
      }));
    };

    const killChildGroup = () => {
      if (!child || stopping) return;
      stopping = true;
      const sendSig = sig => {
        try {
          if (process.platform !== 'win32' && Number.isInteger(child.pid) && child.pid > 0) {
            process.kill(-child.pid, sig);
            return;
          }
        } catch {}
        try { child.kill(sig); } catch {}
      };
      sendSig('SIGTERM');
      killTimer = setTimeout(() => sendSig('SIGKILL'), KILL_GRACE_MS);
      killTimer.unref();
      failsafeTimer = setTimeout(() => finish(null, null, 'SIGKILL'), KILL_GRACE_MS + 1000);
      failsafeTimer.unref();
    };

    const evaluateStuck = async trigger => {
      if (settled || stopping || checkingStuck) return;
      checkingStuck = true;
      const now = Date.now();
      const idleMs = Math.max(0, now - lastActivityAt);
      const elapsedMs = Math.max(0, now - started);
      const tailLines = getTailLines(recentLines, stdoutCarry, stderrCarry, STUCK_CHECK_TAIL_LINES);
      let verdictObj = null;
      try {
        verdictObj = await stuckChecker({
          phase,
          command,
          trigger,
          idleMs,
          elapsedMs,
          tailLines,
          cwd,
          env: rawEnv,
          signal: stuckAbort.signal,
        });
      } catch {
        verdictObj = null;
      }
      if (settled || stopping) return;

      if (verdictObj && verdictObj.verdict === 'stuck') {
        stuck = true;
        stuckTrigger = trigger;
        stuckSource = verdictObj.source || 'llm';
        stuckReason = String(verdictObj.reason || '').trim() || 'process appears stuck';
        killChildGroup();
        return;
      }

      if (verdictObj && verdictObj.verdict === 'progress') {
        llmContinueCount += 1;
        if (trigger === 'idle') {
          silentContinueCount = hadNewBytesSinceCheck ? 1 : silentContinueCount + 1;
        }
        hadNewBytesSinceCheck = false;
        if (silentContinueCount > maxSilentContinues || llmContinueCount > maxLlmContinues) {
          stuck = true;
          stuckTrigger = trigger;
          stuckSource = 'llm-limit';
          stuckReason = String(verdictObj.reason || '').trim() || `process remained ${trigger === 'repeat-loop' ? 'looping' : 'idle'} across consecutive checks`;
          killChildGroup();
          return;
        }
        lastActivityAt = Date.now();
        repeatCount = 0;
        checkingStuck = false;
        return;
      }

      // Offline / no-LLM fallback policy (never kills actively progressing runs).
      if (trigger === 'idle') {
        stuck = true;
        stuckTrigger = 'idle';
        stuckSource = 'offline-idle';
        stuckReason = `no output for ${formatDurationBrief(idleMs)}`;
        killChildGroup();
        return;
      }
      if (repeatCount >= offlineRepeatKill) {
        stuck = true;
        stuckTrigger = 'repeat-loop';
        stuckSource = 'offline-repeat';
        stuckReason = `repeated identical output line ${repeatCount} times`;
        killChildGroup();
        return;
      }
      checkingStuck = false;
    };

    const handleChunk = (streamName, chunk) => {
      const text = typeof chunk === 'string' ? chunk : chunk.toString('utf8');
      if (!text) return;
      hadNewBytesSinceCheck = true;
      if (streamName === 'stdout') stdout = appendBounded(stdout, text);
      else stderr = appendBounded(stderr, text);

      const combined = (streamName === 'stdout' ? stdoutCarry : stderrCarry) + text;
      const parts = combined.split(/\r?\n/);
      const carry = parts.pop() ?? '';
      if (streamName === 'stdout') stdoutCarry = carry;
      else stderrCarry = carry;

      if (parts.length === 0) {
        // Inline progress output (e.g. pytest dots without trailing newline) still counts as activity.
        lastActivityAt = Date.now();
        silentContinueCount = 0;
        return;
      }

      for (const rawLine of parts) {
        const trimmed = rawLine.trim();
        if (!trimmed) continue;
        recentLines.push(trimmed.slice(0, 500));
        if (recentLines.length > 80) recentLines.shift();
        const norm = normalizeProgressLine(trimmed);
        if (norm) {
          if (norm === lastNormLine) {
            repeatCount += 1;
          } else {
            lastNormLine = norm;
            repeatCount = 1;
            lastActivityAt = Date.now();
            silentContinueCount = 0;
          }
        } else {
          lastActivityAt = Date.now();
          silentContinueCount = 0;
        }
      }

      if (!timeoutMs && !stopping && !checkingStuck && repeatCount >= effectiveRepeat) {
        void evaluateStuck('repeat-loop');
      }
    };

    try {
      child = spawner(command, {
        cwd,
        env: childEnv,
        shell: true,
        detached: process.platform !== 'win32',
        stdio: ['ignore', 'pipe', 'pipe'],
      });
    } catch (err) {
      finish(err, null, '');
      return;
    }

    if (timeoutMs) {
      hardTimer = setTimeout(() => {
        timedOut = true;
        killChildGroup();
      }, timeoutMs);
      hardTimer.unref();
    } else {
      const pollMs = Math.max(20, Math.min(5000, Math.floor(effectiveIdleMs / 4)));
      idleInterval = setInterval(() => {
        if (settled || stopping || checkingStuck) return;
        if (Date.now() - lastActivityAt >= effectiveIdleMs) {
          void evaluateStuck('idle');
        }
      }, pollMs);
      idleInterval.unref();
    }

    child.stdout?.on('data', chunk => handleChunk('stdout', chunk));
    child.stderr?.on('data', chunk => handleChunk('stderr', chunk));
    child.on('error', err => finish(err, null, ''));
    child.on('close', (code, sig) => finish(null, code, sig));
  });
}

function lstatSafe(fullPath) {
  try { return lstatSync(fullPath); }
  catch (err) { if (err?.code === 'ENOENT') return null; throw err; }
}

function resolveSafeLocalVenvPytest(root) {
  const inGitRepo = existsSync(join(root, '.git'));
  for (const venvDir of ['.venv', 'venv']) {
    const dirPath = join(root, venvDir);
    const binDir = join(dirPath, 'bin');
    const candidate = join(binDir, 'pytest');
    const dst = lstatSafe(dirPath);
    if (!dst || dst.isSymbolicLink() || !dst.isDirectory()) continue;
    const bst = lstatSafe(binDir);
    if (!bst || bst.isSymbolicLink() || !bst.isDirectory()) continue;
    const fst = lstatSafe(candidate);
    if (!fst || fst.isSymbolicLink() || !fst.isFile()) continue;
    if (inGitRepo) {
      const rel = `${venvDir}/bin/pytest`;
      const tracked = gitExec(root, ['ls-files', '--error-unmatch', '--', rel]);
      if (tracked.status !== 1) continue;
    }
    return `${venvDir}/bin/pytest`;
  }
  return null;
}

function canExecuteBin(bin, { root, env, probe }) {
  if (typeof probe === 'function') return Boolean(probe(bin));
  return !executableMissing(bin, { cwd: root, env });
}

function python3HasPytest({ root, env, probe }) {
  if (typeof probe === 'function') return Boolean(probe('python3 -m pytest'));
  if (!canExecuteBin('python3', { root, env })) return false;
  const res = spawnSync(
    'python3',
    ['-c', 'import importlib.util, sys; sys.exit(0 if importlib.util.find_spec("pytest") else 1)'],
    { cwd: root, env, stdio: ['ignore', 'ignore', 'ignore'], timeout: 5000 },
  );
  return res.status === 0;
}

export function detectRepoTestCommand(root, { env = process.env, probe } = {}) {
  const pkgRaw = readSafeUtf8(root, 'package.json');
  if (pkgRaw) {
    try {
      const pkg = JSON.parse(pkgRaw);
      const testScript = typeof pkg?.scripts?.test === 'string' ? pkg.scripts.test.trim() : '';
      if (testScript && !/no test specified/i.test(testScript)) {
        if (existsSync(join(root, 'pnpm-lock.yaml'))) return 'pnpm test';
        if (existsSync(join(root, 'yarn.lock'))) return 'yarn test';
        if (existsSync(join(root, 'bun.lock')) || existsSync(join(root, 'bun.lockb'))) return 'bun run test';
        return 'npm test';
      }
      if (pkg?.dependencies?.vitest || pkg?.devDependencies?.vitest) return 'npx vitest run';
      if (existsSync(join(root, 'bun.lock')) || existsSync(join(root, 'bun.lockb'))) return 'bun test';
    } catch {}
  }
  if (existsSync(join(root, 'go.mod'))) return 'go test ./...';
  if (existsSync(join(root, 'Cargo.toml'))) return 'cargo test';
  if (
    existsSync(join(root, 'pyproject.toml'))
    || existsSync(join(root, 'pytest.ini'))
    || existsSync(join(root, 'setup.cfg'))
    || existsSync(join(root, 'conftest.py'))
  ) {
    const prefix = existsSync(join(root, 'src')) ? 'PYTHONPATH=src ' : '';
    const venvPytest = resolveSafeLocalVenvPytest(root);
    if (venvPytest) return `${prefix}${venvPytest}`;
    const pyprojectText = readSafeUtf8(root, 'pyproject.toml') ?? '';
    if ((existsSync(join(root, 'uv.lock')) || /\[tool\.uv\b/i.test(pyprojectText)) && canExecuteBin('uv', { root, env, probe })) {
      return `${prefix}uv run pytest`;
    }
    if ((existsSync(join(root, 'poetry.lock')) || /\[tool\.poetry\b/i.test(pyprojectText)) && canExecuteBin('poetry', { root, env, probe })) {
      return `${prefix}poetry run pytest`;
    }
    if (!canExecuteBin('pytest', { root, env, probe }) && python3HasPytest({ root, env, probe })) {
      return `${prefix}python3 -m pytest`;
    }
    return `${prefix}pytest`;
  }
  if (
    existsSync(join(root, 'Gemfile'))
    && (existsSync(join(root, '.rspec')) || existsSync(join(root, 'spec')) || /\brspec\b/i.test(readSafeUtf8(root, 'Gemfile') ?? ''))
  ) {
    return 'bundle exec rspec';
  }
  if (existsSync(join(root, 'Package.swift'))) return 'swift test';
  if (existsSync(join(root, 'gradlew'))) return './gradlew test';
  if (existsSync(join(root, 'pom.xml'))) return 'mvn test';
  if (existsSync(join(root, 'CTestTestfile.cmake')) || existsSync(join(root, 'CMakeLists.txt'))) return 'ctest';
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

function symlinkLocalDependencyDirs(root, worktrees, changedFromBase) {
  if (changedFromBase.some(f => DEP_MANIFEST_OR_LOCKFILE_RE.test(f))) return { links: [], dirs: [] };
  const rootReal = realpathSync(root);
  const links = [];
  const dirs = [];
  for (const dirName of LOCAL_DEP_DIRS) {
    const srcPath = join(rootReal, dirName);
    const srcStat = lstatSafe(srcPath);
    if (!srcStat || srcStat.isSymbolicLink() || !srcStat.isDirectory()) continue;
    const tracked = gitExec(rootReal, ['ls-files', '--error-unmatch', '--', dirName]);
    if (tracked.status === 0) continue;
    let linkedAny = false;
    for (const wt of worktrees) {
      const dstPath = join(wt, dirName);
      if (lstatSafe(dstPath)) continue;
      try {
        symlinkSync(srcPath, dstPath, 'dir');
        links.push(dstPath);
        linkedAny = true;
      } catch {
        // Skip silently when symlinking is unavailable on the filesystem.
      }
    }
    if (linkedAny) dirs.push(dirName);
  }
  return { links, dirs };
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
    for (const m of cmd.matchAll(/(?:^|[;&|]\s*)(?:npm|pnpm|yarn|bun)\s+(?:run\s+)?([A-Za-z0-9_.:-]+)/g)) {
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

const SCRIPT_TOKEN_EXT_RE = /\.(?:[cm]?js|[cm]?ts|sh|bash|py|rb|pl)$/i;

function extractReferencedRepoScripts(commands = []) {
  const refs = new Set();
  for (const cmd of commands) {
    if (typeof cmd !== 'string' || !cmd.trim()) continue;
    const tokens = cmd.match(/(?:'[^']*'|"[^"]*"|\S+)/g) ?? [];
    let expectingImportPath = false;
    for (const raw of tokens) {
      const tok = raw.replace(/^['"]|['"]$/g, '');
      if (!tok || tok === '&&' || tok === '||' || tok === ';' || tok === '|') {
        expectingImportPath = false;
        continue;
      }
      if (tok === '--import' || tok === '-r' || tok === '--require') {
        expectingImportPath = true;
        continue;
      }
      const importEq = /^(?:--import|--require)=([^=]+)$/.exec(tok);
      const candidate = importEq ? importEq[1] : tok;
      const isImportArg = expectingImportPath || Boolean(importEq);
      expectingImportPath = false;
      if (candidate.startsWith('-') || candidate.includes('://') || candidate.includes('*')) continue;
      if (!isImportArg && !SCRIPT_TOKEN_EXT_RE.test(candidate) && !candidate.startsWith('./') && !candidate.startsWith('scripts/') && !candidate.startsWith('tools/')) continue;
      const norm = candidate.replace(/\\/g, '/').replace(/^(?:\.\/)+/, '');
      if (!norm || norm.startsWith('/') || norm.startsWith('..') || norm.includes('/../')) continue;
      if (!isImportArg && TEST_TARGET_FILE_RE.test(norm)) continue;
      if (SCRIPT_TOKEN_EXT_RE.test(norm) || isImportArg || /^(?:scripts|tools|bin)\//.test(norm)) {
        refs.add(norm);
      }
    }
  }
  return [...refs].sort();
}

function detectUntrustedReferencedScriptEdits(root, baseSha, commands, touchedFiles = []) {
  const refs = extractReferencedRepoScripts(commands);
  if (!refs.length) return [];
  const touchedSet = new Set((Array.isArray(touchedFiles) ? touchedFiles : []).map(f => String(f).replace(/\\/g, '/').replace(/^(?:\.\/)+/, '')));
  const changed = new Set();
  for (const ref of refs) {
    if (touchedSet.has(ref)) { changed.add(ref); continue; }
    const diffRes = gitExec(root, ['diff', '--name-only', '-z', baseSha, '--', ref]);
    if (diffRes.status === 0 && diffRes.stdout && diffRes.stdout.split('\0').some(Boolean)) {
      changed.add(ref);
      continue;
    }
    const untracked = gitExec(root, ['ls-files', '--others', '--exclude-standard', '-z', '--', ref]);
    if (untracked.status === 0 && untracked.stdout && untracked.stdout.split('\0').some(Boolean)) {
      changed.add(ref);
    }
  }
  return [...changed].sort();
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

async function runBugContrastProve(
  { root, base, test, expect, overlay, setup, timeoutMinutes, idleTimeoutMs, repeatLoopThreshold, explicitRepeatThreshold, json, env },
  ports = {},
) {
  const stdout = ports.stdout ?? process.stdout, stderr = ports.stderr ?? process.stderr;
  if (typeof test !== 'string' || !test.trim() || typeof expect !== 'string' || !expect.trim()) {
    stderr.write('pdd prove bug-contrast mode requires nonblank --test CMD and --expect TEXT.\n');
    return { exitCode: EXIT_USAGE, outcome: OUTCOME_FAILED, receipt: null };
  }
  if (timeoutMinutes !== null && timeoutMinutes !== undefined && (!Number.isInteger(timeoutMinutes) || timeoutMinutes < 1 || timeoutMinutes > 120)) {
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

  const explicitTimeoutMs = Number.isInteger(timeoutMinutes) ? timeoutMinutes * 60_000 : null;
  const worktreeParent = mkdtempSync(join(tmpdir(), 'pdd-prove-'));
  const baseWorktree = join(worktreeParent, 'base');
  const headWorktree = join(worktreeParent, 'head');
  const createdWorktrees = [];
  let linkedDepLinks = [];
  let linkedDepDirs = [];
  let basePhase = null, headPhase = null, setupError = '', copiedPaths = [];

  try {
    const changedFromBase = listChangedFiles(root, baseSha);
    // Always union colocated/repo test files with explicit --overlay globs so fixture overlays never drop the regression test.
    const configuredTestpaths = readPytestTestpaths(root, { gitRef: baseSha });
    const overlayPaths = changedFromBase.filter(
      f => COLOCATED_TEST_RE.test(f) || isTestOwnedPath(f) || isConfiguredTestPath(f, configuredTestpaths) || overlayGlobs.some(m => m.test(f)),
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

    const execOpts = {
      env,
      rawEnv: env,
      timeoutMs: explicitTimeoutMs,
      idleTimeoutMs,
      repeatLoopThreshold,
      explicitRepeatThreshold,
    };

    if (setup) {
      const baseSetup = await execShellCommand(setup, { ...execOpts, cwd: baseWorktree, phase: 'bug-contrast:base-setup' }, ports);
      if (!baseSetup.ok) throw new Error(`base --setup failed (exit ${baseSetup.exitCode}): ${baseSetup.summary}`);
      const headSetup = await execShellCommand(setup, { ...execOpts, cwd: headWorktree, phase: 'bug-contrast:head-setup' }, ports);
      if (!headSetup.ok) throw new Error(`head --setup failed (exit ${headSetup.exitCode}): ${headSetup.summary}`);
    } else {
      const linked = symlinkLocalDependencyDirs(root, [baseWorktree, headWorktree], changedFromBase);
      linkedDepLinks = linked.links;
      linkedDepDirs = linked.dirs;
    }

    basePhase = await execShellCommand(test, { ...execOpts, cwd: baseWorktree, phase: 'bug-contrast:base' }, ports);
    const baseTextHasExpect = !basePhase.signal && !basePhase.timedOut && !basePhase.stuck && (basePhase.stdout.includes(expect) || basePhase.stderr.includes(expect));
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
    headPhase = await execShellCommand(test, { ...execOpts, cwd: headWorktree, phase: 'bug-contrast:head' }, ports);
  } catch (err) {
    setupError = causeText(err?.message || String(err));
  } finally {
    // Explicitly unlink temporary dependency symlinks BEFORE removing worktrees so caller deps can NEVER be touched.
    for (const linkPath of linkedDepLinks) {
      try {
        if (lstatSafe(linkPath)?.isSymbolicLink()) unlinkSync(linkPath);
      } catch {}
    }
    for (const wt of createdWorktrees) gitExec(root, ['worktree', 'remove', '--force', wt]);
    rmSync(worktreeParent, { recursive: true, force: true });
  }

  let outcome, reason, exitCode;
  const notProvedReasons = [];
  if (setupError || basePhase?.setupError || headPhase?.setupError || (!basePhase?.timedOut && !basePhase?.stuck && basePhase?.signal) || (!headPhase?.timedOut && !headPhase?.stuck && headPhase?.signal)) {
    outcome = OUTCOME_NOT_PROVED; reason = 'setup-error'; exitCode = EXIT_NOT_PROVED;
    notProvedReasons.push(`Setup/dependency/compile failure prevented causal bug-contrast proof: ${setupError || basePhase?.setupError || headPhase?.setupError || basePhase?.signal || headPhase?.signal}. Pass --setup CMD if dependencies must be installed in fresh worktrees.`);
  } else if (basePhase?.timedOut || headPhase?.timedOut) {
    const phaseName = basePhase?.timedOut ? 'base' : 'head';
    const tail = basePhase?.timedOut ? basePhase.frozenTail : headPhase.frozenTail;
    outcome = OUTCOME_NOT_PROVED; reason = basePhase?.timedOut ? 'base-timeout' : 'head-timeout'; exitCode = EXIT_NOT_PROVED;
    notProvedReasons.push(`Bug-contrast ${phaseName} run timed out after ${timeoutMinutes} min; rerun with --timeout MIN. Frozen log tail: ${formatFrozenTail(tail)}`);
  } else if (basePhase?.stuck || headPhase?.stuck) {
    const phaseName = basePhase?.stuck ? 'base' : 'head';
    const aborted = basePhase?.stuck ? basePhase : headPhase;
    outcome = OUTCOME_NOT_PROVED; reason = basePhase?.stuck ? 'base-stuck' : 'head-stuck'; exitCode = EXIT_NOT_PROVED;
    notProvedReasons.push(`Bug-contrast ${phaseName} run aborted as stuck (${aborted.stuckReason || 'no progress'}). Frozen log tail: ${formatFrozenTail(aborted.frozenTail)}`);
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

  const summarize = p => p ? {
    exitCode: p.exitCode,
    signal: p.signal || null,
    ok: p.ok,
    timedOut: p.timedOut,
    stuck: Boolean(p.stuck),
    ...(p.stuckReason ? { stuckReason: p.stuckReason } : {}),
    ...(p.frozenTail?.length ? { frozenTail: p.frozenTail } : {}),
    durationMs: p.durationMs,
    setupError: p.setupError,
    expectedFound: Boolean(p.expectedFound),
    summary: p.summary,
  } : null;
  const receipt = {
    schema_version: 'pdd.prove.v1', mode: 'bug-contrast', outcome, reason, exit_code: exitCode,
    baseRef: requestedBase, baseSha, headSha, overlayPaths: copiedPaths,
    ...(linkedDepDirs.length ? { linkedDependencyDirs: linkedDepDirs } : {}),
    test, expect,
    base: summarize(basePhase), head: summarize(headPhase), notProvedReasons,
  };
  if (json) stdout.write(`${JSON.stringify(receipt, null, 2)}\n`);
  else if (outcome === OUTCOME_PROVED) stdout.write(`Proved: \`${test}\` failed on base (${baseSha.slice(0, 7)}) with expected ${JSON.stringify(expect)} and passed on head.\n`);
  else stderr.write(`${outcome} [${reason}]: ${notProvedReasons[0] || `base exit ${basePhase?.exitCode ?? 'none'}, head exit ${headPhase?.exitCode ?? 'none'}`}\n`);
  return { exitCode, outcome, receipt };
}

export async function runProve(
  {
    cwd = process.cwd(),
    base,
    test,
    expect,
    overlay,
    setup,
    timeoutMinutes = null,
    idleTimeoutMs,
    repeatLoopThreshold,
    json = false,
    capabilities,
    env = process.env,
  } = {},
  ports = {},
) {
  const stdout = ports.stdout ?? process.stdout, stderr = ports.stderr ?? process.stderr;
  const root = resolveGitRoot(cwd);
  const resolvedIdleMs = idleTimeoutMs ?? ports.idleTimeoutMs ?? DEFAULT_IDLE_WINDOW_MS;
  const explicitRepeatThreshold = repeatLoopThreshold !== undefined || ports.repeatLoopThreshold !== undefined;
  const resolvedRepeat = repeatLoopThreshold ?? ports.repeatLoopThreshold ?? DEFAULT_REPEAT_LOOP_THRESHOLD;

  if (test !== undefined || expect !== undefined) {
    return runBugContrastProve(
      { root, base, test, expect, overlay, setup, timeoutMinutes, idleTimeoutMs: resolvedIdleMs, repeatLoopThreshold: resolvedRepeat, explicitRepeatThreshold, json, env },
      ports,
    );
  }
  if (timeoutMinutes !== null && timeoutMinutes !== undefined && (!Number.isInteger(timeoutMinutes) || timeoutMinutes < 1 || timeoutMinutes > 120)) {
    stderr.write('pdd prove --timeout takes whole minutes from 1 to 120.\n');
    return { exitCode: EXIT_USAGE, outcome: OUTCOME_FAILED, receipt: null };
  }

  const headSha = resolveCommit(root, 'HEAD');
  const baseRef = base || resolveDefaultBaseRef(root);
  const baseCommit = baseRef ? resolveCommit(root, baseRef) : null;
  const mb = baseCommit && headSha ? gitExec(root, ['merge-base', headSha, baseCommit]) : null;
  const baseSha = mb?.status === 0 && mb.stdout.trim() ? mb.stdout.trim() : null;
  const explicitTimeoutMs = Number.isInteger(timeoutMinutes) ? timeoutMinutes * 60_000 : null;
  const completedPhases = [];

  const lint = lintRepoProject({ root, enforceBaseTrust: true, trustBaseRef: baseSha || baseRef || undefined, requireFullStoryCriteria: true });
  completedPhases.push({ phase: 'lint', status: lint.ok ? 'ok' : 'failed' });
  const diff = runDiffSpotlight({ cwd: root, baseRef: baseSha || baseRef || undefined });
  completedPhases.push({ phase: 'diff', status: diff.ok ? 'ok' : 'failed' });
  const notProvedReasons = [];

  if (!baseSha || !diff.baseAvailable) {
    notProvedReasons.push(diff.baseError || `Base ref "${baseRef || 'default'}" could not be resolved locally; refusing to assume an empty diff.`);
    const receipt = {
      schema_version: 'pdd.prove.v1', mode: 'verify', outcome: OUTCOME_NOT_PROVED, exit_code: EXIT_NOT_PROVED,
      baseRef: baseRef ?? null, baseSha: null, headSha, configSource: null, touchedFiles: [], changedSurfaces: [],
      completedPhases,
      lint: { ok: lint.ok, errors: lint.errors, warnings: lint.warnings },
      diff: { ok: false, errors: diff.errors.map(e => e.formatted), advisories: diff.advisories },
      test: null, formal: null, paths: [], notProvedReasons,
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

  const testCommand = baseVerify.test || detectRepoTestCommand(root, { env, probe: ports.probeRunner });
  const allVerifyCommands = [
    testCommand,
    baseVerify.formalCommand,
    baseVerify.mutationCommand,
    ...baseVerify.paths.map(r => r.run),
  ];
  const changedPkgScripts = detectUntrustedPackageTestScriptEdits(root, baseSha, allVerifyCommands);
  if (changedPkgScripts.length > 0) {
    notProvedReasons.push(`Working-tree/branch edits to package.json test scripts (${changedPkgScripts.join(', ')}) are not yet trusted on merge base; human review required.`);
  }
  const changedReferencedScripts = detectUntrustedReferencedScriptEdits(root, baseSha, allVerifyCommands, diff.touchedFiles);
  if (changedReferencedScripts.length > 0) {
    notProvedReasons.push(`Working-tree/branch edits to verify-referenced script(s) (${changedReferencedScripts.join(', ')}) are not yet trusted on merge base; human review required.`);
  }
  const usesPytest = allVerifyCommands.some(c => typeof c === 'string' && /\bpytest\b/i.test(c));
  const changedPytestConfigs = usesPytest ? detectPytestConfigEdits(root, baseSha, diff.touchedFiles) : [];
  if (changedPytestConfigs.length > 0) {
    notProvedReasons.push(`Working-tree/branch edits to pytest configuration (${changedPytestConfigs.join(', ')}) are not yet trusted on merge base; human review required.`);
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
  let formalResult = null;
  let abortedPhase = null;
  const { matched, changedSurfaces, unmappedSurfaces } = matchVerifyPaths(baseVerify, diff.touchedFiles, { root, baseSha });
  const pathResults = [];
  const scrubbedBaseEnv = scrubChildEnv(env);
  const resolveStepEnv = (phase, recipeId, command) => (
    typeof ports.envForStep === 'function'
      ? ports.envForStep({ phase, recipeId, command, baseEnv: scrubbedBaseEnv })
      : scrubbedBaseEnv
  );

  if (shadowBins.length === 0 && changedPkgScripts.length === 0 && changedReferencedScripts.length === 0 && changedPytestConfigs.length === 0) {
    // 1. Run fast targeted checks first: matched verify.paths recipes, then formal verification, BEFORE the full test suite.
    const capState = detectHostCapabilities(matched.flatMap(r => r.needs), { env, capabilities, probe: ports.probeCapability, isTTY: ports.isTTY });
    for (const recipe of matched) {
      const { satisfied, missing } = matchCapabilities(recipe.needs, capState);
      const tier = classifyVerifyPathTier(recipe);
      const tierMeta = { ...(recipe.scope ? { scope: recipe.scope } : {}), tier };
      if (!satisfied) {
        pathResults.push({ id: recipe.id, name: recipe.name, ...tierMeta, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs, status: 'not-proved', missingCapabilities: missing, ok: false });
        notProvedReasons.push(`Recipe "${recipe.id}" (${recipe.name}) skipped: missing required capability [${missing.join(', ')}].`);
        continue;
      }
      const recipeEnv = resolveStepEnv('path', recipe.id, recipe.run);
      const r = await execShellCommand(
        recipe.run,
        {
          cwd: root,
          env: recipeEnv,
          rawEnv: env,
          timeoutMs: explicitTimeoutMs,
          idleTimeoutMs: resolvedIdleMs,
          repeatLoopThreshold: resolvedRepeat,
          explicitRepeatThreshold,
          phase: `path:${recipe.id}`,
          preScrubbed: true,
        },
        ports,
      );
      if (r.timedOut) {
        abortedPhase = `path:${recipe.id}`;
        pathResults.push({
          id: recipe.id, name: recipe.name, ...tierMeta, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs,
          status: 'not-proved', timedOut: true, stuck: false, frozenTail: r.frozenTail, exitCode: r.exitCode, durationMs: r.durationMs, ok: false, summary: r.summary,
        });
        notProvedReasons.push(`Verify path "${recipe.id}" timed out after ${timeoutMinutes} min (\`${recipe.run}\`); rerun with --timeout MIN. Completed phases: ${formatCompletedPhases(completedPhases)}. Frozen log tail: ${formatFrozenTail(r.frozenTail)}`);
        continue;
      }
      if (r.stuck) {
        abortedPhase = `path:${recipe.id}`;
        pathResults.push({
          id: recipe.id, name: recipe.name, ...tierMeta, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs,
          status: 'not-proved', timedOut: false, stuck: true, stuckReason: r.stuckReason, frozenTail: r.frozenTail, exitCode: r.exitCode, durationMs: r.durationMs, ok: false, summary: r.summary,
        });
        notProvedReasons.push(`Verify path "${recipe.id}" aborted as stuck (${r.stuckReason || 'no progress'}) (\`${recipe.run}\`). Completed phases: ${formatCompletedPhases(completedPhases)}. Frozen log tail: ${formatFrozenTail(r.frozenTail)}`);
        continue;
      }
      if (r.missingRunnerFailure) {
        pathResults.push({
          id: recipe.id, name: recipe.name, ...tierMeta, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs,
          status: 'not-proved', timedOut: false, stuck: false, hardSetupFailure: r.hardSetupFailure, setupError: r.setupError, exitCode: r.exitCode, durationMs: r.durationMs, ok: false, summary: r.summary,
        });
        const detail = formatTeachingDetail({
          invariant: `Verify path "${recipe.id}" runner unavailable or environment setup failed (\`${recipe.run}\`, exit ${r.exitCode ?? 'error'}): ${r.setupError || r.summary || 'command failed to start'}`,
          fix: 'Install the required runner or local environment on PATH and ensure the command in pdd.json verify.paths is executable',
          rerun: 'pdd prove',
        });
        notProvedReasons.push(`[verify-path-runner-unavailable] ${detail}`);
        continue;
      }
      pathResults.push({
        id: recipe.id, name: recipe.name, ...tierMeta, run: recipe.run, matchedFiles: recipe.matchedFiles, needs: recipe.needs,
        status: r.ok ? 'proved' : 'failed', timedOut: false, stuck: false, exitCode: r.exitCode, durationMs: r.durationMs, ok: r.ok, summary: r.summary,
      });
    }
    if (matched.length > 0) {
      const okCount = pathResults.filter(p => p.status === 'proved').length;
      const failCount = pathResults.filter(p => p.status === 'failed').length;
      const npCount = pathResults.filter(p => p.status === 'not-proved').length;
      completedPhases.push({
        phase: 'paths',
        status: failCount > 0 ? `${okCount}/${matched.length} ok, ${failCount} failed` : (npCount > 0 ? `${okCount}/${matched.length} ok, ${npCount} not-proved` : `${okCount}/${matched.length} ok`),
      });
    }

    const formalEnv = resolveStepEnv('formal', null, baseVerify.formalCommand || '');
    formalResult = runFormalVerification(
      {
        root,
        touchedFiles: diff.touchedFiles,
        baseVerify,
        ...(explicitTimeoutMs ? { timeoutMs: explicitTimeoutMs } : {}),
        env: formalEnv,
      },
      ports,
    );
    completedPhases.push({ phase: 'formal', status: formalResult.state || 'not-applicable' });
    if (formalResult.notProvedReasons?.length) {
      notProvedReasons.push(...formalResult.notProvedReasons);
    }

    // 2. Run the full repository test suite after fast checks complete.
    if (testCommand) {
      const testEnv = resolveStepEnv('test', null, testCommand);
      const r = await execShellCommand(
        testCommand,
        {
          cwd: root,
          env: testEnv,
          rawEnv: env,
          timeoutMs: explicitTimeoutMs,
          idleTimeoutMs: resolvedIdleMs,
          repeatLoopThreshold: resolvedRepeat,
          explicitRepeatThreshold,
          phase: 'test',
          preScrubbed: true,
        },
        ports,
      );
      const isNotProved = Boolean(r.timedOut || r.stuck || r.missingRunnerFailure);
      testResult = {
        command: testCommand,
        ok: r.ok,
        timedOut: r.timedOut,
        stuck: r.stuck,
        ...(r.stuckReason ? { stuckReason: r.stuckReason } : {}),
        ...(r.frozenTail.length ? { frozenTail: r.frozenTail } : {}),
        hardSetupFailure: r.hardSetupFailure,
        notProved: isNotProved,
        exitCode: r.exitCode,
        durationMs: r.durationMs,
        setupError: r.setupError,
        summary: r.summary,
      };
      if (r.timedOut) {
        abortedPhase = 'test';
        notProvedReasons.push(`Test suite timed out after ${timeoutMinutes} min during phase "test" (\`${testCommand}\`); rerun with --timeout MIN. Completed phases: ${formatCompletedPhases(completedPhases)}. Frozen log tail: ${formatFrozenTail(r.frozenTail)}`);
      } else if (r.stuck) {
        abortedPhase = 'test';
        notProvedReasons.push(`Test suite aborted as stuck (${r.stuckReason || 'no progress'}) during phase "test" (\`${testCommand}\`). Completed phases: ${formatCompletedPhases(completedPhases)}. Frozen log tail: ${formatFrozenTail(r.frozenTail)}`);
      } else if (r.missingRunnerFailure) {
        const detail = formatTeachingDetail({
          invariant: `Test runner unavailable or environment setup failed (\`${testCommand}\`, exit ${r.exitCode ?? 'error'}): ${r.setupError || r.summary || 'command failed to start'}`,
          fix: 'Install the test runner on PATH, create a repo-local environment (such as .venv), or configure "verify": { "test": "<command>" } in pdd.json',
          rerun: 'pdd prove',
        });
        notProvedReasons.push(`[test-runner-unavailable] ${detail}`);
        completedPhases.push({ phase: 'test', status: 'not-proved' });
      } else {
        completedPhases.push({ phase: 'test', status: r.ok ? 'ok' : 'failed' });
      }
    } else {
      notProvedReasons.push('No verify.test command configured in merge-base pdd.json and no standard test runner detected.');
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
        || diff.touchedFiles.some(tf => TEST_SCENARIO_JSON_RE.test(tf) && (tf.endsWith(`/${slug}.json`) || tf.includes(`/${slug}.`)));
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
    ...(testResult && !testResult.ok && !testResult.notProved ? [`Test suite failed (\`${testResult.command}\`, exit ${testResult.exitCode}): ${testResult.summary}`] : []),
    ...pathResults.filter(p => p.status === 'failed').map(p => `Verify path "${p.id}" failed (\`${p.run}\`, exit ${p.exitCode}): ${p.summary}`),
    ...(formalResult?.errors ?? []),
  ];

  const outcome = failedErrors.length > 0 ? OUTCOME_FAILED : (notProvedReasons.length > 0 ? OUTCOME_NOT_PROVED : OUTCOME_PROVED);
  const exitCode = outcome === OUTCOME_FAILED ? EXIT_FAILED : (outcome === OUTCOME_NOT_PROVED ? EXIT_NOT_PROVED : EXIT_PROVED);
  const proofTiers = summarizeProofTiers({ testResult, pathResults });
  const proofTiersLine = formatProofTiersLine(proofTiers);
  const receipt = {
    schema_version: 'pdd.prove.v1', mode: 'verify', outcome, exit_code: exitCode, baseRef, baseSha, headSha,
    dirty, proofScope, ...(dirtyFiles.length ? { dirtyFiles: dirtyFiles.slice(0, 12) } : {}),
    configSource: baseVerify.configured ? baseVerify.source : (testCommand ? 'auto-detected' : null), touchedFiles: diff.touchedFiles, changedSurfaces,
    completedPhases,
    ...(abortedPhase ? { abortedPhase } : {}),
    lint: { ok: lint.ok, errors: lint.errors, warnings: lint.warnings },
    diff: { ok: diff.ok, errors: diff.errors.map(e => e.formatted), advisories: diff.advisories },
    test: testResult, formal: formalResult, paths: pathResults, proofTiers, notProvedReasons,
  };

  const scopeSuffix = statusFailed
    ? ' (unknown checkout cleanliness)'
    : (dirty ? ` (working tree, uncommitted changes: ${dirtyFiles.slice(0, 4).join(', ')})` : '');
  const formalLine = formalResult?.summary || 'Formal: not-applicable';
  if (json) stdout.write(`${JSON.stringify(receipt, null, 2)}\n`);
  else if (outcome === OUTCOME_PROVED) stdout.write(`Proved${scopeSuffix}: lint clean, tests passed, ${pathResults.length} verify path(s) green. ${formalLine}.\n${proofTiersLine}\n`);
  else if (outcome === OUTCOME_NOT_PROVED) stdout.write(`Not proved${scopeSuffix} (${formalLine}):\n${notProvedReasons.map(r => `  - ${r}`).join('\n')}\n${proofTiersLine}\n`);
  else { for (const err of failedErrors) stderr.write(`${err}\n`); stderr.write(`Failed${scopeSuffix} (${formalLine}): ${failedErrors.length} check(s) failed.\n${proofTiersLine}\n`); }
  return { exitCode, outcome, receipt };
}
