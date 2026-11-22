// Generated from prompts/cli/accounts-cli.prompt.md.
// Interactive provider login, temp private dir management, local lease materialization, and prompt IO.
import { spawn, spawnSync } from 'node:child_process';
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { join } from 'node:path';
import { createInterface } from 'node:readline';
import {
  CloudAccountsError,
  isReauthRequiredAccount,
  leaseCloudAccount,
  managedClaudeSettingsPath,
  managedCodexAuthPath,
  managedCodexConfigPath,
  markLocalAccountReauthRequired,
  materializeLocalClaudeAuth,
  materializeLocalCodexAuth,
  readCloudAccountsState,
  readCodexUsageWindows,
  reportCloudAccountUsage,
  saveActiveLeaseMetadata,
  stopCodexAppServerDaemon,
  writeCloudAccountsState,
} from '../login-pool.mjs';
import { runAgentProcess } from '../shared/agent-process.mjs';
import { resolvePddStateBase } from '../shared/state-dir.mjs';
import { accountDisplayState } from './cli-format.mjs';
import { parseClaudeTokenText, readClaudeTokenFromPath } from './import-auth.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

export function createTempPrivateDir(fs, prefix, tmpRoot, env = process.env) {
  const rootDir = tmpRoot
    || (typeof env?.PDD_CODEX_RUNTIME_ROOT === 'string' && env.PDD_CODEX_RUNTIME_ROOT.trim())
    || join(resolvePddStateBase(env), 'codex-runtime');
  fs.mkdirSync(rootDir, { recursive: true, mode: 0o700 });
  try { (fs.chmodSync ?? nativeFs.chmodSync)(rootDir, 0o700); } catch {}
  let dir;
  if (typeof fs.mkdtempSync === 'function') dir = fs.mkdtempSync(join(rootDir, prefix));
  else if (fs === nativeFs) dir = nativeFs.mkdtempSync(join(rootDir, prefix));
  else { dir = join(rootDir, `${prefix}${randomBytes(8).toString('hex')}`); fs.mkdirSync(dir, { recursive: true, mode: 0o700 }); }
  try { (fs.chmodSync ?? nativeFs.chmodSync)(dir, 0o700); } catch {}
  return dir;
}

export function removeTempPrivateDir(fs, dir) {
  if (!dir) return;
  try { (fs.rmSync ?? nativeFs.rmSync)(dir, { recursive: true, force: true }); } catch {}
}

export function hasLocalMaterializedFile(fs, provider, env) {
  try {
    if (provider === 'claude') return Boolean(fs.statSync(managedClaudeSettingsPath(env))?.isFile());
    return Boolean(fs.statSync(managedCodexAuthPath(env))?.isFile()) && Boolean(fs.statSync(managedCodexConfigPath(env))?.isFile());
  } catch { return false; }
}

function runInteractiveClaudeSetupToken({ cwd, env, stdin, stdout, stderr, timeoutMs = 300_000 }, ports = {}) {
  const spawnImpl = ports.spawnInteractive ?? spawn;
  return new Promise((resolveRun, rejectRun) => {
    let child = null, stdoutBuf = '', stderrBuf = '', settled = false, killTimer = null, interrupted = false;
    const stopChild = () => {
      if (!child) return;
      try { child.kill('SIGTERM'); } catch {}
      killTimer = setTimeout(() => { try { child.kill('SIGKILL'); } catch {} }, 500);
      killTimer.unref?.();
    };
    const finish = (err, code, signal) => {
      if (settled) return;
      settled = true; clearTimeout(timer); if (killTimer) clearTimeout(killTimer);
      process.off('SIGINT', onSigint);
      if (err) { err.stdout = stdoutBuf; err.stderr = stderrBuf; rejectRun(err); return; }
      resolveRun({ code: interrupted || signal === 'SIGINT' ? 130 : (code ?? 1), signal: interrupted ? 'SIGINT' : (signal ?? null), stdout: stdoutBuf, stderr: stderrBuf });
    };
    const onSigint = () => { interrupted = true; stopChild(); finish(null, 130, 'SIGINT'); };
    const timer = setTimeout(() => { stopChild(); finish(new CloudAccountsError('claude setup-token timed out waiting for browser OAuth completion.', { code: 'timeout' })); }, timeoutMs);
    timer.unref?.();
    const useInheritedStdin = stdin === process.stdin || !stdin || typeof stdin.pipe !== 'function';
    try {
      child = spawnImpl('claude', ['setup-token'], {
        cwd, env: { ...env, COLUMNS: env?.COLUMNS || '500' },
        stdio: [useInheritedStdin ? 'inherit' : 'pipe', 'pipe', 'pipe'], shell: false,
      });
    } catch (err) { finish(err); return; }
    process.on('SIGINT', onSigint);
    if (!useInheritedStdin && child.stdin) { stdin.pipe(child.stdin); child.stdin.on('error', () => {}); }
    child.stdout?.on('data', chunk => { stdoutBuf += String(chunk); try { stdout?.write?.(chunk); } catch {} });
    child.stderr?.on('data', chunk => { stderrBuf += String(chunk); try { stderr?.write?.(chunk); } catch {} });
    child.on('error', err => finish(err));
    child.on('close', (code, signal) => finish(null, code, signal));
  });
}

export async function runProviderLogin(provider, { cwd, env, deviceAuth = false, stdin = process.stdin }, ports = {}) {
  if (typeof ports.runLogin === 'function') return ports.runLogin(provider, { cwd, env, deviceAuth });
  const cmd = provider === 'claude' ? 'claude' : 'codex';
  const args = provider === 'claude' ? ['setup-token'] : ['login', '-c', 'cli_auth_credentials_store="file"', ...(deviceAuth ? ['--device-auth'] : [])];
  if (typeof ports.run === 'function') return ports.run(cmd, args, { cwd, env, input: '', timeoutMs: 120_000, maxBytes: 65_536 });
  const activeStdin = ports.stdin ?? stdin ?? process.stdin;
  const activeStdout = ports.stdout ?? process.stdout;
  const activeStderr = ports.stderr ?? process.stderr;
  if (provider === 'claude') {
    if (!activeStdin?.isTTY || !activeStdout?.isTTY) {
      throw new CloudAccountsError('claude setup-token requires an interactive terminal (TTY) to paste the OAuth authorization code. Run "pdd accounts add --provider claude" in an interactive terminal, pipe a token to stdin, or run "pdd accounts import --provider claude".', { code: 'non_interactive_claude_login', exitCode: 1 });
    }
    return runInteractiveClaudeSetupToken({ cwd, env, stdin: activeStdin, stdout: activeStdout, stderr: activeStderr, timeoutMs: ports.claudeLoginTimeoutMs ?? 300_000 }, ports);
  }
  if (provider === 'codex' && activeStdin?.isTTY && activeStdout?.isTTY) {
    const res = spawnSync(cmd, args, { cwd, env, stdio: 'inherit' });
    return { code: res.signal === 'SIGINT' ? 130 : (res.status ?? 1), signal: res.signal ?? null, stdout: '', stderr: '' };
  }
  return runAgentProcess(cmd, args, { cwd, env, input: '', timeoutMs: 120_000, maxBytes: 65_536 });
}

export function applyMaterializedLease(leaseReply, { env }, ports = {}) {
  const saved = readCloudAccountsState({ env }, ports);
  const provider = leaseReply?.account?.provider, lease = leaseReply?.lease;
  if (provider === 'codex') {
    const prevCodex = saved.active?.codex;
    const prevManagedGateway = Boolean(prevCodex?.managed_codex_gateway);
    const prevModelProvider = prevCodex?.previous_codex_model_provider ?? null;
    if (lease?.delivery_mode === 'gateway_grant') {
      const leasePlanType = lease.plan_type ?? leaseReply?.account?.plan_type ?? leaseReply?.account?.plan;
      const leaseInput = lease.plan_type === undefined && typeof leasePlanType === 'string' && leasePlanType.trim() ? { ...lease, plan_type: leasePlanType } : lease;
      const mat = materializeLocalCodexAuth(leaseInput, { env, previousManagedCodexGateway: prevManagedGateway, previousCodexModelProvider: prevModelProvider }, ports);
      stopCodexAppServerDaemon(mat.codexHome, { env, fs: ports.fs ?? nativeFs, spawnSync: ports.spawnSync });
      saveActiveLeaseMetadata(leaseReply, {
        env, materializedLocal: true, managedCodexGateway: mat.managedCodexGateway, codexGatewayUrl: mat.codexGatewayUrl, previousCodexModelProvider: mat.previousCodexModelProvider,
      }, ports);
      return;
    }
    if (object(lease?.codex_auth_json)) {
      const mat = materializeLocalCodexAuth(lease.codex_auth_json, { env, previousManagedCodexGateway: prevManagedGateway, previousCodexModelProvider: prevModelProvider }, ports);
      stopCodexAppServerDaemon(mat.codexHome, { env, fs: ports.fs ?? nativeFs, spawnSync: ports.spawnSync });
      saveActiveLeaseMetadata(leaseReply, {
        env, materializedLocal: true, managedCodexGateway: false, codexGatewayUrl: null, previousCodexModelProvider: null,
      }, ports);
      return;
    }
  }
  if (provider === 'claude') {
    const { managedBaseUrl } = materializeLocalClaudeAuth(lease, { env }, ports);
    saveActiveLeaseMetadata(leaseReply, { env, materializedLocal: true, managedBaseUrl }, ports);
  }
}

export async function probeInitialCodexUsageIfUnpopulated(acc, authJson, _probeCodexHome, { fs, cwd, env }, ports = {}) {
  if (!acc?.account_id) return acc;
  if ((acc.five_hour_used_percent ?? 0) !== 0 || (acc.weekly_used_percent ?? 0) !== 0 || acc.five_hour_reset_at || acc.weekly_reset_at) return acc;
  let tempProbeDir = null;
  try {
    tempProbeDir = createTempPrivateDir(fs, 'pdd-cx-probe-', ports.tmpRoot, env);
    const probeAuthJson = object(authJson) && object(authJson.tokens) ? { ...authJson, tokens: { ...authJson.tokens, refresh_token: '' } } : authJson;
    fs.writeFileSync(join(tempProbeDir, 'auth.json'), `${JSON.stringify(probeAuthJson, null, 2)}\n`, { mode: 0o600 });
    const windows = await (ports.readCodexUsageWindows ?? readCodexUsageWindows)(
      { command: 'codex', cwd, env: { ...env, CODEX_HOME: tempProbeDir }, weeklyStopPercent: 100, timeoutMs: ports.usageProbeTimeoutMs ?? 3000 },
      ports.codexLimitPorts,
    );
    removeTempPrivateDir(fs, tempProbeDir); tempProbeDir = null;
    const hasFiveH = typeof windows?.five_hour_used_percent === 'number' && Number.isFinite(windows.five_hour_used_percent);
    const hasSevenD = typeof windows?.weekly_used_percent === 'number' && Number.isFinite(windows.weekly_used_percent);
    if (hasFiveH || hasSevenD) {
      const fiveH = hasFiveH ? windows.five_hour_used_percent : 0, sevenD = hasSevenD ? windows.weekly_used_percent : 0;
      const reported = await reportCloudAccountUsage(acc.account_id, {
        five_hour_used_percent: fiveH, five_hour_reset_at: windows.five_hour_reset_at ?? null,
        weekly_used_percent: sevenD, weekly_reset_at: windows.weekly_reset_at ?? null,
        limit_reached: Boolean(windows.limit_reached || fiveH >= 100 || sevenD >= 100),
      }, { cwd, env, timeoutMs: 3500 }, ports);
      if (object(reported?.account)) return reported.account;
    }
  } catch {} finally { removeTempPrivateDir(fs, tempProbeDir); }
  return acc;
}

export async function askPromptRaw(question, { stdin, stdout }, ports = {}) {
  const promptFn = ports.prompt ?? ports.confirm ?? null;
  if (typeof promptFn === 'function') { try { return await promptFn(question); } catch { return undefined; } }
  const rl = createInterface({ input: stdin, output: stdout });
  try {
    return await new Promise(resolveAnswer => {
      let settled = false;
      const finish = val => { if (!settled) { settled = true; resolveAnswer(val); } };
      rl.once('SIGINT', () => { finish(undefined); rl.close(); });
      rl.once('close', () => finish(undefined));
      rl.question(question, val => finish(val));
    });
  } finally { rl.close(); }
}

export async function askLoopContinue(question, { stdin, stdout }, ports = {}) {
  const answer = await askPromptRaw(question, { stdin, stdout }, ports);
  if (answer === undefined || answer === null || answer === false) return false;
  if (answer === true) return true;
  const normalized = String(answer).trim().toLowerCase();
  return normalized === '' || normalized === 'y' || normalized === 'yes';
}

export async function leaseAndSyncAfterEnroll(provider, acc, fallbackLabel, _fallbackAuthJson, _fallbackOauthToken, { cwd, env }, ports = {}) {
  const fs = ports.fs ?? nativeFs, nowMs = (ports.now ?? Date.now)();
  if (acc?.account_id) {
    const pre = readCloudAccountsState({ env }, ports);
    if (pre.reauth?.[acc.account_id]) {
      const cleanedReauth = { ...pre.reauth };
      delete cleanedReauth[acc.account_id];
      writeCloudAccountsState({ ...pre, reauth: cleanedReauth }, { env }, ports);
    }
  }
  try {
    const leased = await leaseCloudAccount({ provider, preferredLabel: acc.label, holderId: 'local-cli', updateState: false }, { cwd, env }, ports);
    if (leased?.state === 'leased' && !isReauthRequiredAccount(leased.account)) {
      applyMaterializedLease(leased, { env }, ports);
      return { materialized: Boolean(hasLocalMaterializedFile(fs, provider, env)) };
    }
    if (leased?.state === 'leased' && isReauthRequiredAccount(leased.account)) {
      markLocalAccountReauthRequired(leased.account?.account_id ?? acc.account_id, { env }, ports);
      return { materialized: false };
    }
    const current = readCloudAccountsState({ env }, ports);
    writeCloudAccountsState({
      enrolled: true,
      providers: [...new Set([...current.providers, provider])],
      active: current.active,
      cooling: leased?.state === 'all_cooling' ? { ...current.cooling, [provider]: { wake_at: leased.wake_at ?? null } } : current.cooling,
    }, { env }, ports);
    return { materialized: false };
  } catch {
    const current = readCloudAccountsState({ env }, ports);
    writeCloudAccountsState({
      enrolled: true,
      providers: [...new Set([...current.providers, provider])],
      active: {
        ...current.active,
        [provider]: {
          account_id: acc.account_id, label: acc.label ?? fallbackLabel, provider, state: accountDisplayState(acc),
          lease_id: null, leased_at: new Date(nowMs).toISOString(), expires_at: new Date(nowMs + 5 * 60 * 1000).toISOString(),
          last_refresh_at: acc.last_refresh_at ?? new Date(nowMs).toISOString(), materialized_local: false, delivery_mode: 'gateway_grant',
          five_hour_used_percent: acc.five_hour_used_percent ?? null, five_hour_reset_at: acc.five_hour_reset_at ?? null,
          weekly_used_percent: acc.weekly_used_percent ?? null, weekly_reset_at: acc.weekly_reset_at ?? null,
        },
      },
      cooling: current.cooling,
    }, { env }, ports);
    return { materialized: false };
  }
}

export function extractIsolatedClaudeSetupToken(fs, tempClaudeDir, loginOutput, nowFn) {
  const nowMs = (typeof nowFn === 'function' ? nowFn : Date.now)();
  if (typeof loginOutput === 'string' && loginOutput.trim()) {
    const fromOutput = parseClaudeTokenText(loginOutput, 'claude setup-token output', nowMs, { allowBareToken: false });
    if (fromOutput) return fromOutput;
  }
  if (tempClaudeDir) {
    try {
      const fromTempDir = readClaudeTokenFromPath(fs, tempClaudeDir, { now: nowFn });
      if (fromTempDir) return fromTempDir;
    } catch (err) {
      if (err instanceof CloudAccountsError && err.code === 'expired_local_login') throw err;
    }
  }
  throw new CloudAccountsError('No Claude OAuth token found in claude setup-token output. Run "pdd accounts add --provider claude" in an interactive terminal and complete the browser sign-in.', { code: 'missing_local_login' });
}
