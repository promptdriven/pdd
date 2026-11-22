// Generated from prompts/cli/accounts-cli.prompt.md.
// Legacy interactive Codex auto-rotation supervisor (PDD_LEGACY_PTY_ROTATE=1) and plain non-TTY runner.
import { spawn } from 'node:child_process';
import * as nativeFs from 'node:fs';
import { resolve } from 'node:path';
import {
  classifyRateLimitFailure,
  extractRateLimitReport,
  isCloudAccountsActive,
  isReauthRequiredAccount,
  isReauthRequiredFailure,
  leaseCloudAccount,
  localCodexHome,
  markLocalAccountReauthRequired,
  pddManagedCodexHome,
  readCloudAccountsState,
  reportCloudAccountUsage,
  writeCloudAccountsState,
} from '../login-pool.mjs';
import { redactSecrets } from '../secret-redaction.mjs';
import { formatAccountQuotaSummary } from './cli-format.mjs';
import { runSyncCommand } from './cli-status-sync.mjs';
import { applyMaterializedLease, hasLocalMaterializedFile } from './enroll-login.mjs';
import {
  buildCodexExecutionEnv,
  buildCodexResumeArgs,
  checkCloudAccountQuotaExhausted,
  findRolloutPathBySessionId,
  inspectCodexInvocation,
  safeFileSize,
  snapshotPreSpawnCodexSessions,
} from './legacy-pty-rollout.mjs';
import { runSingleSupervisedCodexTurn } from './legacy-pty-turn.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

function exitCodeFromSignalOrStatus(code, signal) {
  if (signal === 'SIGINT') return 130;
  if (signal === 'SIGTERM') return 143;
  if (signal === 'SIGHUP') return 129;
  if (signal) return 1;
  return typeof code === 'number' ? code : 1;
}

function writeStreamChunk(stream, chunk) {
  if (chunk == null) return;
  if (typeof chunk === 'string' && chunk.length === 0) return;
  if (chunk instanceof Uint8Array && chunk.byteLength === 0) return;
  try { stream?.write?.(chunk); } catch {}
}

export async function runPlainCodexOnce(args, { cwd, env, stdin, stdout, stderr }, ports = {}) {
  if (typeof ports.spawnCodexPty === 'function') {
    const res = await ports.spawnCodexPty({
      command: 'codex', args, cwd, env, turn: 0, signal: new AbortController().signal,
      onOutput(chunk) { writeStreamChunk(stdout, chunk); },
    });
    return { exitCode: res?.signal ? exitCodeFromSignalOrStatus(null, res.signal) : (res?.code ?? 0), message: '' };
  }
  if (typeof ports.run === 'function') {
    const res = await ports.run('codex', args, { cwd, env, input: '', timeoutMs: 300_000, maxBytes: 1_048_576 });
    writeStreamChunk(stdout, res?.stdout);
    writeStreamChunk(stderr, res?.stderr);
    return { exitCode: exitCodeFromSignalOrStatus(res?.code, res?.signal), message: '' };
  }
  const inheritStdin = stdin == null || stdin === process.stdin;
  const inheritStdout = !stdout || stdout === process.stdout;
  const inheritStderr = !stderr || stderr === process.stderr;
  const stdio = inheritStdin && inheritStdout && inheritStderr
    ? 'inherit'
    : [inheritStdin ? 'inherit' : 'pipe', inheritStdout ? 'inherit' : 'pipe', inheritStderr ? 'inherit' : 'pipe'];
  return new Promise(resolveExit => {
    let settled = false;
    const child = (ports.spawn ?? spawn)('codex', args, { cwd, env, stdio });
    const forward = sig => { try { child.kill(sig); } catch {} };
    const onSigInt = () => forward('SIGINT'), onSigTerm = () => forward('SIGTERM'), onSigHup = () => forward('SIGHUP');
    process.on('SIGINT', onSigInt); process.on('SIGTERM', onSigTerm); process.on('SIGHUP', onSigHup);
    const finish = result => {
      if (settled) return;
      settled = true;
      process.off('SIGINT', onSigInt); process.off('SIGTERM', onSigTerm); process.off('SIGHUP', onSigHup);
      if (child.stdin && stdin && typeof stdin.unpipe === 'function') { try { stdin.unpipe(child.stdin); } catch {} }
      resolveExit(result);
    };
    if (child.stdin) {
      child.stdin.on('error', () => {});
      if (typeof stdin === 'string' || stdin instanceof Uint8Array) { try { child.stdin.end(stdin); } catch {} }
      else if (stdin && typeof stdin.pipe === 'function') stdin.pipe(child.stdin);
      else { try { child.stdin.end(); } catch {} }
    }
    child.stdout?.on('data', chunk => writeStreamChunk(stdout, chunk));
    child.stderr?.on('data', chunk => writeStreamChunk(stderr, chunk));
    child.on('error', err => finish({ exitCode: 1, message: err?.code === 'ENOENT' ? 'codex CLI not found on PATH.' : redactSecrets(`Failed to run codex: ${err?.message ?? 'spawn error'}`) }));
    child.on('close', (code, signal) => finish({ exitCode: exitCodeFromSignalOrStatus(code, signal), message: '' }));
  });
}

async function leaseNextHealthyCodexForRotation(skipAccountIds, { cwd, env }, ports = {}) {
  const skipIds = [...new Set(skipAccountIds.filter(Boolean))];
  for (let attempt = 0; attempt < 8; attempt += 1) {
    let reply = null;
    try {
      reply = await leaseCloudAccount({
        provider: 'codex', currentAccountId: null, skipAccountIds: skipIds, holderId: 'codex-pty', updateState: false,
      }, { cwd, env, timeoutMs: ports.leaseTimeoutMs ?? 8000 }, ports);
    } catch (err) {
      if (isReauthRequiredFailure(err)) {
        const failedId = err?.payload?.account_id ?? err?.payload?.detail?.account_id ?? null;
        if (failedId && !skipIds.includes(failedId)) { markLocalAccountReauthRequired(failedId, { env }, ports); skipIds.push(failedId); continue; }
        return { state: 'reauth_required', reply: null };
      }
      return { state: 'error', error: err, reply: null };
    }
    if (reply?.state === 'all_cooling') {
      const latestSaved = readCloudAccountsState({ env }, ports);
      if (latestSaved.enrolled && latestSaved.providers.includes('codex')) {
        writeCloudAccountsState({ ...latestSaved, cooling: { ...latestSaved.cooling, codex: { wake_at: reply.wake_at ?? null } } }, { env }, ports);
      }
      return { state: 'all_cooling', reply };
    }
    if (!reply || reply.state !== 'leased' || !object(reply.account) || !object(reply.lease)) return { state: 'unavailable', reply };
    const acc = reply.account;
    if (isReauthRequiredAccount(acc) && acc.account_id && !skipIds.includes(acc.account_id)) { markLocalAccountReauthRequired(acc.account_id, { env }, ports); skipIds.push(acc.account_id); continue; }
    if (((typeof acc.five_hour_used_percent === 'number' && acc.five_hour_used_percent >= 100)
      || (typeof acc.weekly_used_percent === 'number' && acc.weekly_used_percent >= 100)) && acc.account_id && !skipIds.includes(acc.account_id)) {
      skipIds.push(acc.account_id);
      continue;
    }
    return { state: 'leased', reply };
  }
  return { state: 'unavailable', reply: null };
}

export async function runInteractiveCodexWithAutoRotate({ args = [], cwd, env, stdin }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const activeStdin = ports.stdin ?? stdin ?? process.stdin;
  const activeStdout = ports.stdout ?? process.stdout;
  const activeStderr = ports.stderr ?? process.stderr;
  const initialArgs = [...args];
  const invocation = inspectCodexInvocation(initialArgs, cwd);

  let managedHome = '';
  const expectedManagedHome = pddManagedCodexHome(env);
  if (isCloudAccountsActive({ env, provider: 'codex' }, ports)) {
    const synced = await runSyncCommand({ provider: 'codex', quiet: true, printCodexHome: true, timeoutMs: ports.syncTimeoutMs ?? 2000, cwd, env }, ports);
    managedHome = synced.message.trim();
    if (!managedHome && hasLocalMaterializedFile(fs, 'codex', env)) {
      const curState = readCloudAccountsState({ env }, ports);
      if (curState.active?.codex?.state === 'ready') managedHome = expectedManagedHome;
    }
  }
  if (!managedHome) {
    const fallbackEnv = { ...env };
    if (fallbackEnv.CODEX_HOME && resolve(fallbackEnv.CODEX_HOME) === resolve(expectedManagedHome)) delete fallbackEnv.CODEX_HOME;
    return runPlainCodexOnce(initialArgs, { cwd, env: fallbackEnv, stdin: activeStdin, stdout: activeStdout, stderr: activeStderr }, ports);
  }
  if (!invocation.interactive) {
    return runPlainCodexOnce(initialArgs, { cwd, env: buildCodexExecutionEnv(env, managedHome), stdin: activeStdin, stdout: activeStdout, stderr: activeStderr }, ports);
  }

  const userCodexHome = localCodexHome({ ...env, CODEX_HOME: '' });
  const codexHomes = [managedHome, userCodexHome];
  const preSpawnSnapshot = snapshotPreSpawnCodexSessions(fs, codexHomes);
  const initialResumeSessionId = invocation.isResume ? (invocation.explicitSessionId ?? null) : null;
  const excludedForkSessionId = invocation.isFork ? (invocation.explicitSessionId ?? null) : null;
  const sessionState = {
    sessionId: initialResumeSessionId,
    rolloutPath: initialResumeSessionId ? findRolloutPathBySessionId(fs, codexHomes, initialResumeSessionId) : null,
  };

  let currentArgs = initialArgs;
  const triedAccountIds = new Set(), maxRotations = 8;
  for (let turn = 0; turn <= maxRotations; turn += 1) {
    const turnStartedMs = (ports.now ?? Date.now)();
    const activeBefore = readCloudAccountsState({ env }, ports).active?.codex ?? null;
    const turnRes = await runSingleSupervisedCodexTurn({
      fs, args: currentArgs, cwd, env: buildCodexExecutionEnv(env, managedHome),
      stdin: activeStdin, stdout: activeStdout, stderr: activeStderr, turn, turnStartedMs,
      activeEntry: activeBefore, codexHomes, preSpawnSnapshot, expectedCwd: invocation.effectiveCwd,
      sessionState, excludedSessionId: excludedForkSessionId,
      initialRolloutOffset: sessionState.rolloutPath ? safeFileSize(fs, sessionState.rolloutPath) : 0,
    }, ports);

    if (turnRes.abortedByParentSignal) return { exitCode: turnRes.code ?? 1, message: '' };
    let hitQuota = turnRes.quotaExhausted, cloudExhaustedAcc = turnRes.exhaustedAccountSnapshot;
    if (!hitQuota && turnRes.code !== 0 && turnRes.code !== 130 && turnRes.signal !== 'SIGINT') {
      if (activeBefore?.account_id) {
        cloudExhaustedAcc = await checkCloudAccountQuotaExhausted(activeBefore.account_id, { cwd, env }, ports);
        if (cloudExhaustedAcc) hitQuota = true;
      }
      if (!hitQuota && !sessionState.rolloutPath && classifyRateLimitFailure(turnRes.rollingPlain, activeBefore) === 'quota_exhausted') hitQuota = true;
    }
    if (!hitQuota) return { exitCode: turnRes.code ?? 0, message: '' };

    const exhaustedEntry = readCloudAccountsState({ env }, ports).active?.codex ?? activeBefore;
    const exhaustedId = exhaustedEntry?.account_id ?? null;
    if (exhaustedId) {
      triedAccountIds.add(exhaustedId);
      const reportSourceText = turnRes.quotaReasonText || (!sessionState.rolloutPath ? turnRes.rollingPlain : 'usage_limit_reached');
      await reportCloudAccountUsage(exhaustedId, extractRateLimitReport(reportSourceText, cloudExhaustedAcc ?? exhaustedEntry, (ports.now ?? Date.now)()), { cwd, env, timeoutMs: 3500 }, ports).catch(() => {});
    }
    if (turn >= maxRotations) return { exitCode: 1, message: 'Reached maximum automatic Codex account rotations for this session.' };

    const nextLease = await leaseNextHealthyCodexForRotation([...triedAccountIds], { cwd, env }, ports);
    if (nextLease.state !== 'leased' || !nextLease.reply) {
      const wakeAt = nextLease.reply?.wake_at;
      return { exitCode: 1, message: nextLease.state === 'all_cooling' ? `All codex accounts are cooling${wakeAt ? ` until ${wakeAt}` : ''}.` : 'No additional ready Codex Cloud accounts are available to resume this session.' };
    }

    applyMaterializedLease(nextLease.reply, { env }, ports);
    const prevLabel = exhaustedEntry?.label ?? exhaustedId ?? 'previous';
    const nextLabel = nextLease.reply.account?.label ?? nextLease.reply.account?.account_id ?? 'next';
    const quotaInfo = formatAccountQuotaSummary(nextLease.reply.account);
    const keepInitialPromptArgs = !sessionState.sessionId && !invocation.isResume;
    const resumeDesc = sessionState.sessionId ? `session ${sessionState.sessionId}` : (keepInitialPromptArgs ? 'initial arguments' : '--last');
    try { activeStderr?.write?.(redactSecrets(`\n[pdd accounts] Quota reached on "${prevLabel}"; switched active Codex account to "${nextLabel}"${quotaInfo} and resuming (${resumeDesc}).\n`)); } catch {}
    currentArgs = keepInitialPromptArgs ? [...initialArgs] : buildCodexResumeArgs(initialArgs, sessionState.sessionId);
  }
  return { exitCode: 1, message: 'No additional ready Codex Cloud accounts are available.' };
}
