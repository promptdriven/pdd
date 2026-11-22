// Generated from prompts/cli/login-pool.prompt.md.
// Cloud account leasing, pool login selection, and exhaustion/rotation reporting.
import {
  cloudAccountsRequest,
  extractRateLimitReport,
  isAuthFailureMessage,
  isExplicitReauthCodeFailure,
  isGatewayGrantRevokedFailure,
  isQuotaExhaustionMessage,
  isReauthRequiredAccount,
  isReauthRequiredFailure,
  reportCloudAccountUsage,
  resolveMachineIdentity,
} from './cloud-client.mjs';
import { CloudAccountsError } from './cloud-error.mjs';
import {
  markLocalAccountReauthRequired,
  readCloudAccountsState,
  saveActiveLeaseMetadata,
  writeCloudAccountsState,
} from './cloud-state.mjs';
import { CLOUD_PROVIDERS, CONFIG_VAR, isCreditOrResetAccount, loginEnvironment } from './pool-env.mjs';
import { prepareCloudStepExecution } from './step-overlay.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

const agentSpecOf = login => ({
  id: login.id,
  kind: login.kind,
  command: login.command,
  ...(login.model ? { model: login.model } : {}),
});

export async function leaseCloudAccount({
  provider = 'codex',
  currentAccountId = undefined,
  preferredLabel = null,
  skipAccountIds = [],
  holderId = 'pdd-step',
  updateState = true,
  autoRotate = undefined,
} = {}, { cwd = process.cwd(), env = process.env, timeoutMs = 15_000, maxRetries, now } = {}, ports = {}) {
  const nowFn = now ?? ports.now ?? Date.now;
  const effectivePorts = ports.now ? ports : { ...ports, now: nowFn };
  const { machineLabel } = resolveMachineIdentity(env, effectivePorts);
  const saved = readCloudAccountsState({ env }, effectivePorts);
  const savedActive = saved.active?.[provider];
  const locallyRevokedIds = Object.keys(saved.reauth ?? {});
  const savedStickyRevoked = currentAccountId === undefined && savedActive?.account_id
    && (savedActive?.state === 'reauth_required' || locallyRevokedIds.includes(savedActive.account_id));
  const stickyId = currentAccountId !== undefined ? currentAccountId : (savedStickyRevoked ? null : (savedActive?.account_id ?? null));
  const skip = [...new Set([
    ...(Array.isArray(skipAccountIds) ? skipAccountIds : []).filter(Boolean),
    ...(savedStickyRevoked && !preferredLabel ? [savedActive.account_id] : []),
    ...(!preferredLabel ? locallyRevokedIds : []),
  ])];
  let activeStickyId = stickyId;
  const maxReauthSkips = preferredLabel ? 0 : (maxRetries === 0 ? 1 : 4);
  const totalBudgetMs = typeof timeoutMs === 'number' && Number.isFinite(timeoutMs) && timeoutMs > 0 ? timeoutMs : 15_000;
  const deadlineMs = nowFn() + totalBudgetMs;
  let reply;
  for (let attempt = 0; ; attempt++) {
    const remainingMs = deadlineMs - nowFn();
    if (remainingMs <= 0) throw new CloudAccountsError('Cloud Accounts request timed out.', { code: 'timeout' });
    const reqCurrentId = activeStickyId && !skip.includes(activeStickyId) ? activeStickyId : null;
    try {
      reply = await cloudAccountsRequest('POST', '/v1/accounts/lease', {
        body: {
          provider,
          current_account_id: reqCurrentId,
          preferred_label: preferredLabel ?? null,
          skip_account_ids: [...skip],
          machine_label: machineLabel,
          holder_id: holderId,
          ...(typeof autoRotate === 'boolean' ? { auto_rotate: autoRotate } : {}),
        },
        cwd, env, timeoutMs: remainingMs, deadlineMs, maxRetries,
      }, effectivePorts);
    } catch (error) {
      if (attempt < maxReauthSkips && isReauthRequiredFailure(error) && (deadlineMs - nowFn()) > 0) {
        const explicitAccountId = error?.payload?.account_id ?? error?.payload?.detail?.account_id ?? error?.payload?.account?.account_id ?? null;
        if (typeof explicitAccountId === 'string' && explicitAccountId) markLocalAccountReauthRequired(explicitAccountId, { env }, effectivePorts);
        const skipCandidate = explicitAccountId ?? reqCurrentId;
        if (typeof skipCandidate === 'string' && skipCandidate && !skip.includes(skipCandidate)) {
          skip.push(skipCandidate);
          activeStickyId = null;
          continue;
        }
      }
      throw error;
    }
    if (attempt < maxReauthSkips && reply?.state === 'leased' && isReauthRequiredAccount(reply.account) && (deadlineMs - nowFn()) > 0) {
      const revokedId = reply.account?.account_id;
      if (typeof revokedId === 'string' && revokedId && !skip.includes(revokedId)) {
        markLocalAccountReauthRequired(revokedId, { env }, effectivePorts);
        skip.push(revokedId);
        activeStickyId = null;
        continue;
      }
    }
    break;
  }
  if (reply?.state === 'leased' && updateState && !isReauthRequiredAccount(reply.account)) {
    saveActiveLeaseMetadata(reply, { env }, effectivePorts);
  } else if (reply?.state === 'leased' && isReauthRequiredAccount(reply.account)) {
    markLocalAccountReauthRequired(reply.account?.account_id, { env }, effectivePorts);
  } else if (reply?.state === 'all_cooling' && updateState) {
    const latestSaved = readCloudAccountsState({ env }, effectivePorts);
    if (latestSaved.enrolled && latestSaved.providers.includes(provider)) {
      writeCloudAccountsState({ ...latestSaved, cooling: { ...latestSaved.cooling, [provider]: { wake_at: reply.wake_at ?? null } } }, { env }, effectivePorts);
    }
  }
  return reply;
}

function candidateCloudProviders({ fallbackAgent, allowedKinds, savedState }) {
  const allowed = Array.isArray(allowedKinds) ? CLOUD_PROVIDERS.filter(p => allowedKinds.includes(p)) : [...CLOUD_PROVIDERS];
  const enrolledAllowed = allowed.filter(p => Array.isArray(savedState?.providers) && savedState.providers.includes(p));
  if (!enrolledAllowed.length) return [];
  const preferred = CLOUD_PROVIDERS.includes(fallbackAgent?.kind) ? fallbackAgent.kind : null;
  return preferred && enrolledAllowed.includes(preferred) ? [preferred, ...enrolledAllowed.filter(p => p !== preferred)] : enrolledAllowed;
}

export async function selectCloudPoolLogin({
  cwd = process.cwd(),
  env = process.env,
  fallbackAgent,
  allowedKinds,
  skipAccountIds = [],
  preferredAccountId = undefined,
  holderId = 'autopilot-step',
  allowCredits = false,
} = {}, ports = {}) {
  const saved = readCloudAccountsState({ env }, ports);
  const providers = candidateCloudProviders({ fallbackAgent, allowedKinds, savedState: saved });
  if (!providers.length) {
    return { state: 'unavailable', cloud: true, configured: true, poolPath: null, poolSize: 0, resetAt: null, cooling: [], unavailable: [] };
  }
  const cooling = [], unavailable = [];
  let earliestWakeAt = null, earliestResetMs = null;

  for (const provider of providers) {
    const tried = new Set(Array.isArray(skipAccountIds) ? skipAccountIds.filter(Boolean) : []);
    for (let round = 0; round < 12; round++) {
      const roundCurrentId = round === 0 && preferredAccountId !== undefined ? preferredAccountId : (round === 0 ? (saved.active?.[provider]?.account_id ?? undefined) : undefined);
      let reply;
      try {
        reply = await leaseCloudAccount({
          provider,
          currentAccountId: round === 0 && preferredAccountId !== undefined ? preferredAccountId : undefined,
          skipAccountIds: [...tried],
          holderId,
        }, { cwd, env, timeoutMs: ports.timeoutMs ?? 15_000 }, ports);
      } catch (error) {
        if (isReauthRequiredFailure(error)) {
          const failedAccId = error?.payload?.account_id ?? (typeof roundCurrentId === 'string' && !tried.has(roundCurrentId) ? roundCurrentId : null);
          if (failedAccId && !tried.has(failedAccId)) {
            markLocalAccountReauthRequired(failedAccId, { env }, ports);
            unavailable.push({ id: failedAccId, reason: 'reauth_required' });
            tried.add(failedAccId);
            continue;
          }
          unavailable.push({ id: provider, reason: 'reauth_required' });
          break;
        }
        unavailable.push({ id: provider, reason: error.code ?? 'unavailable' });
        break;
      }

      if (reply?.state === 'all_cooling') {
        const wakeAt = typeof reply.wake_at === 'string' ? reply.wake_at : null;
        const resetMs = wakeAt ? Date.parse(wakeAt) : null;
        const validMs = Number.isFinite(resetMs) ? resetMs : null;
        cooling.push({ id: provider, until: validMs, resetAt: validMs, wakeAt, reason: wakeAt ? `Waiting on AI quota until ${wakeAt}` : 'all_cooling' });
        if (validMs != null && (earliestResetMs == null || validMs < earliestResetMs)) { earliestResetMs = validMs; earliestWakeAt = wakeAt; }
        else if (!earliestWakeAt && wakeAt) earliestWakeAt = wakeAt;
        break;
      }
      if (reply?.state !== 'leased' || !object(reply.account) || !object(reply.lease)) { unavailable.push({ id: provider, reason: 'invalid_lease' }); break; }

      const acc = reply.account;
      if (isReauthRequiredAccount(acc)) {
        markLocalAccountReauthRequired(acc.account_id, { env }, ports);
        unavailable.push({ id: acc.account_id, reason: 'reauth_required' });
        tried.add(acc.account_id);
        continue;
      }
      if (!allowCredits && isCreditOrResetAccount(acc)) {
        unavailable.push({ id: acc.account_id, reason: 'credit_or_reset_guarded' });
        tried.add(acc.account_id);
        continue;
      }
      if ((typeof acc.five_hour_used_percent === 'number' && acc.five_hour_used_percent >= 100)
        || (typeof acc.weekly_used_percent === 'number' && acc.weekly_used_percent >= 100)) {
        await reportCloudAccountUsage(acc.account_id, {
          five_hour_used_percent: acc.five_hour_used_percent ?? null,
          five_hour_reset_at: acc.five_hour_reset_at ?? null,
          weekly_used_percent: acc.weekly_used_percent ?? null,
          weekly_reset_at: acc.weekly_reset_at ?? null,
          limit_reached: true,
        }, { cwd, env }, ports).catch(() => {});
        tried.add(acc.account_id);
        continue;
      }

      if (provider === 'codex' && reply.lease?.delivery_mode !== 'gateway_grant' && (ports.readCodexUsageWindows || ports.readCodexLimits)) {
        const probeStep = prepareCloudStepExecution(reply, env, ports);
        let probeLimits;
        try {
          const cmd = (fallbackAgent?.kind === 'codex' && fallbackAgent?.command) ? fallbackAgent.command : 'codex';
          probeLimits = ports.readCodexUsageWindows
            ? await ports.readCodexUsageWindows({ command: cmd, cwd, env: probeStep.env, weeklyStopPercent: 100 }, ports.codexLimitPorts)
            : await ports.readCodexLimits({ command: cmd, cwd, env: probeStep.env, weeklyStopPercent: 100 }, ports.codexLimitPorts);
        } finally { probeStep.cleanup(); }
        if (probeLimits?.state === 'signed_out' || isReauthRequiredFailure(probeLimits?.detail ?? probeLimits?.error)) {
          markLocalAccountReauthRequired(acc.account_id, { env }, ports);
          unavailable.push({ id: acc.account_id, reason: 'reauth_required' });
          tried.add(acc.account_id);
          continue;
        }
        if (probeLimits?.state === 'limited') {
          const now = (ports.now ?? Date.now)();
          const report = probeLimits.five_hour_used_percent !== undefined
            ? { ...probeLimits, limit_reached: true }
            : {
                five_hour_used_percent: probeLimits.usedPercent ?? 100,
                five_hour_reset_at: probeLimits.resetAt ? new Date(probeLimits.resetAt).toISOString() : new Date(now + 5 * 3600 * 1000).toISOString(),
                weekly_used_percent: acc.weekly_used_percent ?? 0,
                weekly_reset_at: acc.weekly_reset_at ?? null,
                limit_reached: true,
              };
          await reportCloudAccountUsage(acc.account_id, report, { cwd, env }, ports).catch(() => {});
          tried.add(acc.account_id);
          continue;
        }
      }

      const command = (fallbackAgent?.kind === provider && typeof fallbackAgent?.command === 'string' && fallbackAgent.command.trim()) ? fallbackAgent.command.trim() : provider;
      const model = fallbackAgent?.kind === provider && typeof fallbackAgent?.model === 'string' && fallbackAgent.model.trim() ? fallbackAgent.model.trim() : null;
      const login = {
        id: acc.account_id, label: acc.label ?? acc.account_id, kind: provider, command, model,
        plan: acc.plan ?? null, credits: acc.credits === true, allowReset: acc.allowReset === true || acc.allow_reset === true,
        paused: false, configVar: CONFIG_VAR[provider], configDir: null, env: {},
      };
      return {
        state: 'ready', cloud: true, configured: true, poolPath: null,
        poolSize: Math.max(8, Number.isSafeInteger(reply.pool_size) ? reply.pool_size : 8),
        login, agent: agentSpecOf(login), env: loginEnvironment(env, login), account: acc, lease: reply.lease,
        prepareStep: (stepBaseEnv = env, stepOpts = {}) => prepareCloudStepExecution(reply, stepBaseEnv, ports, stepOpts),
      };
    }
  }

  return {
    state: 'exhausted', cloud: true, configured: true, poolPath: null, poolSize: 1,
    resetAt: earliestResetMs, wakeAt: earliestWakeAt ?? (earliestResetMs != null ? new Date(earliestResetMs).toISOString() : null),
    cooling, unavailable,
  };
}

export async function exhaustCloudPoolLogin({
  cwd = process.cwd(),
  env = process.env,
  fallbackAgent,
  loginId,
  accountWindows = null,
  reason = 'quota',
  allowedKinds,
  skipAccountIds = [],
  holderId = 'autopilot-step',
  allowCredits = false,
} = {}, ports = {}) {
  const now = (ports.now ?? Date.now)();
  if (loginId) {
    if (isQuotaExhaustionMessage(reason)) {
      await reportCloudAccountUsage(loginId, extractRateLimitReport(reason, accountWindows, now), { cwd, env }, ports).catch(() => {});
    } else if (isExplicitReauthCodeFailure(reason)) {
      markLocalAccountReauthRequired(loginId, { env }, ports);
    } else if (isGatewayGrantRevokedFailure(reason)) {
      // Revoked borrower lease/share rotates cleanly without tainting the account as reauth_required.
    } else if (isAuthFailureMessage(reason)) {
      const savedForCheck = readCloudAccountsState({ env }, ports);
      const cachedActive = Object.values(savedForCheck.active ?? {}).find(row => row?.account_id === loginId);
      const isBorrowed = typeof accountWindows?.is_owner === 'boolean' ? !accountWindows.is_owner : (accountWindows?.shared === true ? true : cachedActive?.is_owner === false);
      if (!isBorrowed) markLocalAccountReauthRequired(loginId, { env }, ports);
    } else {
      await reportCloudAccountUsage(loginId, extractRateLimitReport(reason, accountWindows, now), { cwd, env }, ports).catch(() => {});
    }
  }
  const skip = [...new Set([...(Array.isArray(skipAccountIds) ? skipAccountIds : []), ...(loginId ? [loginId] : [])])];
  return selectCloudPoolLogin({ cwd, env, fallbackAgent, allowedKinds, skipAccountIds: skip, holderId, allowCredits }, ports);
}
