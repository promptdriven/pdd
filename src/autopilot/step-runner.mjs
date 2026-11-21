// Generated from prompts/cli/agent-adapters.prompt.md.
// Layer-2 Autopilot/step agent launcher with model tiering, telemetry, and Cloud step failover.
import { runAgentProcess } from '../shared/agent-process.mjs';

const TIER_PROFILES = {
  codex: {
    worker: { model: 'gpt-5.4-mini', reasoningEffort: 'medium' },
    reviewer: { model: 'gpt-5.4', reasoningEffort: 'high' },
  },
  claude: {
    worker: { model: 'claude-sonnet-4-6', reasoningEffort: 'medium' },
    reviewer: { model: 'claude-opus-4-6', reasoningEffort: 'high' },
  },
  gemini: {
    worker: { model: 'gemini-2.5-flash', reasoningEffort: 'medium' },
    reviewer: { model: 'gemini-2.5-pro', reasoningEffort: 'high' },
  },
  agy: {
    worker: { model: 'gemini-2.5-flash', reasoningEffort: 'medium' },
    reviewer: { model: 'gemini-2.5-pro', reasoningEffort: 'high' },
  },
};

const WORKER_STEPS = new Set([
  'intake', 'triage', 'sort', 'dependencies', 'improve', 'groom', 'clarify',
  'small-change', 'worker', 'story', 'story/pr1', 'pr1', 'prompt', 'prompts',
  'code', 'code/pr2', 'pr2', 'implement', 'build', 'repair', 'fix', 'rebase',
  'base-refresh', 'conflict',
]);
const REVIEWER_STEPS = new Set(['review', 'check', 'independent-review', 'audit', 'merge', 'publish']);
const VALID_EFFORTS = new Set(['low', 'medium', 'high', 'xhigh']);

function checkModel(model) {
  if (model === undefined || model === null || model === '') return null;
  if (typeof model !== 'string' || !model.length || model !== model.trim() || /^-|[\x00-\x1f\x7f]/.test(model)) {
    throw new Error('Invalid model name: must be nonblank without control characters or a leading dash.');
  }
  return model;
}

function checkEffort(effort) {
  if (effort === undefined || effort === null || effort === '') return null;
  const clean = String(effort).trim().toLowerCase();
  if (!VALID_EFFORTS.has(clean)) {
    throw new Error('Invalid reasoning effort: choose low, medium, high, or xhigh.');
  }
  return clean;
}

export function resolveAgentStepLaunch({
  agent = 'codex',
  definition = null,
  step = null,
  model = null,
  reasoningEffort = null,
  tiering = null,
  env = process.env,
} = {}) {
  const rawKind = definition?.kind ?? agent;
  const normalizedAgent = typeof rawKind === 'string' && Object.hasOwn(TIER_PROFILES, rawKind.trim().toLowerCase())
    ? rawKind.trim().toLowerCase()
    : 'codex';
  const command = definition?.command ?? rawKind;
  const explicitModel = checkModel(model);
  const explicitEffort = checkEffort(reasoningEffort);
  const cleanStep = typeof step === 'string' ? step.trim().toLowerCase() : '';
  const tier = WORKER_STEPS.has(cleanStep) ? 'worker' : (REVIEWER_STEPS.has(cleanStep) ? 'reviewer' : null);
  const cfg = tiering && typeof tiering === 'object' && !Array.isArray(tiering) ? tiering : null;
  const flag = String(env?.PDD_MODEL_TIERING ?? '').trim().toLowerCase();
  const tieringOn = tiering === true || cfg?.enabled === true
    ? true
    : (tiering === false || cfg?.enabled === false ? false : (flag === '1' || flag === 'true'));
  if (!tieringOn || !tier) {
    return {
      agent: normalizedAgent,
      command,
      tier,
      model: explicitModel,
      reasoningEffort: explicitEffort,
      args: explicitModel ? ['--model', explicitModel] : [],
      tieringEnabled: false,
    };
  }
  const defaults = TIER_PROFILES[normalizedAgent]?.[tier] ?? TIER_PROFILES.codex[tier];
  const envModel = tier === 'worker' ? env?.PDD_WORKER_MODEL : env?.PDD_REVIEWER_MODEL;
  const envEffort = tier === 'worker' ? env?.PDD_WORKER_EFFORT : env?.PDD_REVIEWER_EFFORT;
  const resolvedModel = explicitModel && cfg?.overrideExplicitModel !== true
    ? explicitModel
    : checkModel(cfg?.models?.[normalizedAgent]?.[tier] ?? cfg?.[tier]?.model ?? envModel ?? defaults.model);
  const resolvedEffort = explicitEffort
    ?? checkEffort(cfg?.efforts?.[normalizedAgent]?.[tier] ?? cfg?.[tier]?.reasoningEffort ?? envEffort ?? defaults.reasoningEffort);
  const args = [];
  if (resolvedModel) args.push('--model', resolvedModel);
  if (resolvedEffort) {
    if (normalizedAgent === 'codex') args.push('-c', `model_reasoning_effort="${resolvedEffort}"`);
    else if (normalizedAgent === 'claude') args.push('--effort', resolvedEffort);
  }
  return {
    agent: normalizedAgent,
    command,
    tier,
    model: resolvedModel,
    reasoningEffort: resolvedEffort,
    args,
    tieringEnabled: true,
  };
}

function inspectCallerArgs(rawArgs, overrideExplicitModel) {
  const list = Array.isArray(rawArgs) ? rawArgs : [];
  const cleaned = [];
  let callerModel = null;
  let hasModelFlag = false;
  let hasEffortFlag = false;
  for (let i = 0; i < list.length; i += 1) {
    const arg = String(list[i] ?? '');
    if (arg === '--') {
      cleaned.push(...list.slice(i));
      break;
    }
    if (arg === '--model' || arg === '-m') {
      hasModelFlag = true;
      if (i + 1 < list.length) callerModel = list[i + 1];
      if (!overrideExplicitModel) cleaned.push(list[i], ...(i + 1 < list.length ? [list[i + 1]] : []));
      i += 1;
      continue;
    }
    if (arg.startsWith('--model=') || arg.startsWith('-m=')) {
      hasModelFlag = true;
      callerModel = arg.slice(arg.indexOf('=') + 1);
      if (!overrideExplicitModel) cleaned.push(list[i]);
      continue;
    }
    if (arg === '--effort' || arg.startsWith('--effort=')) hasEffortFlag = true;
    if ((arg === '-c' || arg === '--config') && typeof list[i + 1] === 'string' && /^\s*model_reasoning_effort\s*=/.test(list[i + 1])) {
      hasEffortFlag = true;
    }
    cleaned.push(list[i]);
  }
  return { callerModel, hasModelFlag, hasEffortFlag, cleaned };
}

function composeStepChildArgs(launch, caller, hasExplicitEffortOption) {
  const injected = [];
  for (let i = 0; i < launch.args.length; i += 1) {
    const item = launch.args[i];
    if (item === '--model') {
      if (!caller.hasModelFlag) injected.push(item, launch.args[i + 1]);
      i += 1;
      continue;
    }
    if (item === '-c' && typeof launch.args[i + 1] === 'string' && launch.args[i + 1].startsWith('model_reasoning_effort=')) {
      if (!caller.hasEffortFlag || hasExplicitEffortOption) injected.push(item, launch.args[i + 1]);
      i += 1;
      continue;
    }
    if (item === '--effort') {
      if (!caller.hasEffortFlag || hasExplicitEffortOption) injected.push(item, launch.args[i + 1]);
      i += 1;
      continue;
    }
    injected.push(item);
  }
  const rest = caller.cleaned;
  if (launch.agent === 'codex' && rest.length) {
    const prefixLen = (rest[0] === 'exec' || rest[0] === 'e')
      ? (['resume', 'fork', 'review'].includes(rest[1]) ? 2 : 1)
      : (['resume', 'review', 'fork'].includes(rest[0]) ? 1 : 0);
    if (prefixLen > 0) return [...rest.slice(0, prefixLen), ...injected, ...rest.slice(prefixLen)];
  }
  return [...injected, ...rest];
}

export async function runStepAgentProcess({
  agent = 'codex',
  definition = null,
  step = null,
  args = [],
  model = null,
  reasoningEffort = null,
  tiering = null,
  cwd,
  env = process.env,
  input = '',
  signal,
  timeoutMs = 120_000,
  maxBytes = 131_072,
  run = runAgentProcess,
  now = Date.now,
  allowCredits = false,
  accountsPorts = {},
} = {}) {
  const childEnv = { ...env, ...definition?.env };
  const overrideExplicitModel = Boolean(tiering && typeof tiering === 'object' && tiering.overrideExplicitModel === true);
  const hasModelOpt = model !== null && model !== undefined;
  const caller = inspectCallerArgs(args, overrideExplicitModel || hasModelOpt);
  const effectiveCallerModel = hasModelOpt ? model : (!overrideExplicitModel && caller.hasModelFlag ? caller.callerModel : null);
  const launch = resolveAgentStepLaunch({ agent, definition, step, model: effectiveCallerModel, reasoningEffort, tiering, env: childEnv });
  const childArgs = composeStepChildArgs(
    launch,
    { ...caller, hasModelFlag: caller.hasModelFlag && !overrideExplicitModel && !hasModelOpt },
    reasoningEffort !== null && reasoningEffort !== undefined,
  );
  const { extractHarnessTokens, normalizeAutopilotPhase } = await import('../autopilot-telemetry.mjs');
  const phase = normalizeAutopilotPhase(step);
  const startedAt = now();
  let cloudMod = null;
  if ((launch.agent === 'codex' || launch.agent === 'claude') && childEnv.PDD_CLOUD_STEP_ISOLATED !== '1') {
    const loaded = await import('../login-pool.mjs');
    if (loaded.isCloudAccountsActive({ env: childEnv, provider: launch.agent }, accountsPorts)) cloudMod = loaded;
  }
  let result;
  let activeAccount = null;
  try {
    if (!cloudMod) {
      result = await run(launch.command, childArgs, { cwd, env: childEnv, input, signal, timeoutMs, maxBytes });
    } else {
      const triedIds = [];
      let burstRetried = false;
      let prevAccountId = null;
      for (let round = 0; ; round += 1) {
        if (round >= 24) {
          throw Object.assign(new Error(`All ${launch.agent} Cloud accounts are paused or cooling.`), { code: 'all_cooling', wakeAt: null });
        }
        let leaseReply = null;
        try {
          leaseReply = await cloudMod.leaseCloudAccount(
            { provider: launch.agent, skipAccountIds: triedIds, holderId: `step-${phase || 'cli'}` },
            { cwd, env: childEnv, timeoutMs: accountsPorts?.leaseTimeoutMs ?? 15_000 },
            accountsPorts,
          );
        } catch (leaseErr) {
          if (!triedIds.length && (leaseErr?.code === 'timeout' || leaseErr?.code === 'network_error' || leaseErr?.code === 'missing_auth_token')) {
            result = await run(launch.command, childArgs, { cwd, env: childEnv, input, signal, timeoutMs, maxBytes });
            break;
          }
          throw leaseErr;
        }
        if (leaseReply?.state === 'all_cooling') {
          if (!triedIds.length && !leaseReply.wake_at) {
            let fallBackLocal = false;
            try {
              const listed = await cloudMod.cloudAccountsRequest('GET', '/v1/accounts', { cwd, env: childEnv, timeoutMs: accountsPorts?.leaseTimeoutMs ?? 1500 }, accountsPorts);
              const accessible = (Array.isArray(listed?.accounts) ? listed.accounts : []).filter(a => a && !a.revoked);
              if (!accessible.some(a => a.provider === launch.agent)) {
                const saved = cloudMod.readCloudAccountsState({ env: childEnv }, accountsPorts);
                const nextProviders = [...new Set(accessible.map(a => a.provider).filter(Boolean))];
                const nextActive = Object.fromEntries(Object.entries(saved.active ?? {}).filter(([p]) => nextProviders.includes(p)));
                const prevCodex = saved.active?.codex;
                if (prevCodex && (!nextActive.codex || (prevCodex.managed_codex_gateway === true && !nextActive.codex?.managed_codex_gateway))) {
                  try {
                    cloudMod.restoreLocalCodexGatewayConfig({ env: childEnv, previousModelProvider: prevCodex.previous_codex_model_provider ?? null, removeAuthFile: !nextActive.codex }, accountsPorts);
                  } catch {}
                }
                const prevClaude = saved.active?.claude;
                if (prevClaude && !nextActive.claude) {
                  try { cloudMod.restoreLocalClaudeGatewayConfig?.({ env: childEnv }, accountsPorts); } catch {}
                }
                const nextCooling = Object.fromEntries(Object.entries(saved.cooling ?? {}).filter(([p]) => nextProviders.includes(p)));
                cloudMod.writeCloudAccountsState({ enrolled: accessible.length > 0, providers: nextProviders, active: nextActive, cooling: nextCooling }, { env: childEnv }, accountsPorts);
                fallBackLocal = true;
              }
            } catch {
              if (!cloudMod.readCloudAccountsState({ env: childEnv }, accountsPorts).active?.[launch.agent]) fallBackLocal = true;
            }
            if (fallBackLocal) {
              result = await run(launch.command, childArgs, { cwd, env: childEnv, input, signal, timeoutMs, maxBytes });
              break;
            }
          }
          const msg = leaseReply.wake_at ? `Waiting on AI quota until ${leaseReply.wake_at}` : `All ${launch.agent} Cloud accounts are paused or cooling.`;
          throw Object.assign(new Error(msg), { code: 'all_cooling', wakeAt: leaseReply.wake_at ?? null });
        }
        const acc = leaseReply?.account;
        if (acc && cloudMod.isReauthRequiredAccount?.(acc)) {
          cloudMod.markLocalAccountReauthRequired?.(acc.account_id, { env: childEnv }, accountsPorts);
          if (!acc.account_id || triedIds.includes(acc.account_id) || triedIds.length >= 24) {
            throw Object.assign(new Error(`All ${launch.agent} Cloud accounts require re-authentication or are cooling.`), { code: 'reauth_required', wakeAt: null });
          }
          triedIds.push(acc.account_id);
          continue;
        }
        if (!allowCredits && acc && cloudMod.isCreditOrResetAccount?.(acc)) {
          if (!acc.account_id || triedIds.includes(acc.account_id) || triedIds.length >= 24) {
            throw Object.assign(new Error(`All non-credit ${launch.agent} Cloud accounts are paused or cooling.`), { code: 'all_cooling', wakeAt: null });
          }
          triedIds.push(acc.account_id);
          continue;
        }
        if (burstRetried && prevAccountId && acc?.account_id && acc.account_id !== prevAccountId) {
          if (!triedIds.includes(prevAccountId)) triedIds.push(prevAccountId);
          burstRetried = false;
        }
        prevAccountId = acc?.account_id ?? null;
        if ((typeof acc?.five_hour_used_percent === 'number' && acc.five_hour_used_percent >= 100)
          || (typeof acc?.weekly_used_percent === 'number' && acc.weekly_used_percent >= 100)) {
          await cloudMod.reportCloudAccountUsage(acc.account_id, { ...acc, limit_reached: true }, { cwd, env: childEnv, timeoutMs: 1500 }, accountsPorts).catch(() => {});
          triedIds.push(acc.account_id);
          if (triedIds.length < 12) continue;
        }
        activeAccount = acc ? { account_id: acc.account_id, label: acc.label, provider: acc.provider } : null;
        let stepBaseArgs = childArgs;
        let stepUserSettings = null;
        let spliceExtra = null;
        if (launch.agent === 'claude') {
          const claudeHelper = await import('../accounts/claude-args.mjs');
          spliceExtra = claudeHelper.spliceClaudeExtraArgs;
          const extracted = claudeHelper.extractAndParseUserClaudeSettings(childArgs, { cwd, fs: accountsPorts?.fs });
          stepBaseArgs = extracted.strippedArgs;
          stepUserSettings = extracted.userSettings;
        }
        const stepExec = cloudMod.prepareCloudStepExecution(
          leaseReply,
          childEnv,
          accountsPorts,
          stepUserSettings ? { userSettings: stepUserSettings } : {},
        );
        const stepArgs = Array.isArray(stepExec.extraArgs) && stepExec.extraArgs.length
          ? (spliceExtra ? spliceExtra(stepBaseArgs, stepExec.extraArgs) : (() => {
              const dd = stepBaseArgs.indexOf('--');
              if (dd === -1) return [...stepBaseArgs, ...stepExec.extraArgs];
              return [...stepBaseArgs.slice(0, dd), ...stepExec.extraArgs, ...stepBaseArgs.slice(dd)];
            })())
          : stepBaseArgs;
        try {
          result = await run(launch.command, stepArgs, { cwd, env: stepExec.env, input, signal, timeoutMs, maxBytes });
        } finally {
          stepExec.cleanup();
        }
        const combined = `${result?.stderr ?? ''}\n${result?.stdout ?? ''}`;
        if (result?.code !== 0 && acc?.account_id && triedIds.length < 12 && !triedIds.includes(acc.account_id)) {
          if (cloudMod.isExplicitReauthCodeFailure?.(combined)) {
            cloudMod.markLocalAccountReauthRequired?.(acc.account_id, { env: childEnv }, accountsPorts);
            triedIds.push(acc.account_id);
            burstRetried = false;
            continue;
          }
          if (cloudMod.isGatewayGrantRevokedFailure?.(combined) && !cloudMod.isQuotaExhaustionMessage?.(combined)) {
            triedIds.push(acc.account_id);
            burstRetried = false;
            continue;
          }
          if (cloudMod.isReauthRequiredFailure?.(combined)) {
            const isBorrowed = acc.is_owner === false || (acc.is_owner == null && acc.shared === true);
            if (!isBorrowed) {
              cloudMod.markLocalAccountReauthRequired?.(acc.account_id, { env: childEnv }, accountsPorts);
            }
            triedIds.push(acc.account_id);
            burstRetried = false;
            continue;
          }
        }
        const rateClass = result?.code !== 0 ? cloudMod.classifyRateLimitFailure(combined, acc) : null;
        if (rateClass === 'burst_rate_limit' && !burstRetried) {
          burstRetried = true;
          await (accountsPorts?.sleep ?? (ms => new Promise(r => setTimeout(r, ms))))(accountsPorts?.burstRetryMs ?? 150);
          continue;
        }
        if ((rateClass === 'quota_exhausted' || (rateClass === 'burst_rate_limit' && burstRetried)) && acc?.account_id && triedIds.length < 12) {
          let windows = acc;
          if (launch.agent === 'codex' && leaseReply?.lease?.delivery_mode !== 'gateway_grant' && typeof accountsPorts?.readCodexUsageWindows === 'function') {
            const probeExec = cloudMod.prepareCloudStepExecution(leaseReply, childEnv, accountsPorts);
            try {
              windows = await accountsPorts.readCodexUsageWindows({ command: launch.command, cwd, env: probeExec.env, weeklyStopPercent: 100, timeoutMs: 800 });
            } catch {} finally {
              probeExec.cleanup();
            }
          }
          const report = cloudMod.extractRateLimitReport(combined, windows, now());
          await cloudMod.reportCloudAccountUsage(acc.account_id, report, { cwd, env: childEnv, timeoutMs: 1500 }, accountsPorts).catch(() => {});
          triedIds.push(acc.account_id);
          burstRetried = false;
          continue;
        }
        break;
      }
    }
  } catch (error) {
    const endedAt = now();
    const durationMs = Math.max(0, endedAt - startedAt);
    const tokens = extractHarnessTokens(typeof error?.stdout === 'string' ? error.stdout : '', { agent: launch.agent });
    if (error && typeof error === 'object') {
      error.launch = launch;
      error.telemetry = { phase, step: step ?? null, startedAt, endedAt, durationMs, tokens };
    }
    throw error;
  }
  const endedAt = now();
  const durationMs = Math.max(0, endedAt - startedAt);
  const stdout = typeof result?.stdout === 'string' ? result.stdout : '';
  const tokens = extractHarnessTokens(stdout, { agent: launch.agent });
  return {
    ...(result && typeof result === 'object' ? result : {}),
    stdout,
    launch,
    ...(activeAccount ? { account: activeAccount } : {}),
    telemetry: { phase, step: step ?? null, startedAt, endedAt, durationMs, tokens },
  };
}
