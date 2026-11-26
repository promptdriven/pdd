// Generated from prompts/cli/accounts-cli.prompt.md.
// Sync, auto on/off/status, listed-state reconciliation, status report, and removal cleanup.
import * as nativeFs from 'node:fs';
import {
  isCloudAccountsActive,
  isLocalReauthUnresolved,
  isReauthRequiredAccount,
  isReauthRequiredFailure,
  leaseCloudAccount,
  managedCodexAuthPath,
  managedCodexConfigPath,
  markLocalAccountReauthRequired,
  pddManagedCodexHome,
  readCloudAccountsState,
  restoreLocalClaudeGatewayConfig,
  restoreLocalCodexGatewayConfig,
  writeCloudAccountsState,
} from '../login-pool.mjs';
import { redactSecrets } from '../secret-redaction.mjs';
import { writeAtomicPreservingSymlinkAndMode } from '../shared/atomic-fs.mjs';
import {
  AUTO_BEGIN,
  applyAutoSwitchBlock,
  removeAutoSwitchBlock,
  shellProfileEntries,
} from './auto-switch.mjs';
import {
  accountDisplayState,
  formatExpiryRemaining,
  formatSeatAccess,
  formatStatusQuota,
  sanitizeStatusText,
  withLeftPercentActiveMap,
  withLeftPercentFields,
} from './cli-format.mjs';
import { summarizeCodexRuntimeStatus } from './codex-seat-visibility.mjs';
import { applyMaterializedLease, hasLocalMaterializedFile } from './enroll-login.mjs';
import { readLiveCodexRuntimeLeases } from './runtime-session.mjs';
import { fetchAccountsList } from './share-helpers.mjs';

export async function runSyncCommand({ provider: requestedProvider, quiet = false, printCodexHome = false, timeoutMs = 1200, cwd, env }, ports = {}) {
  const fs = ports.fs ?? nativeFs, now = (ports.now ?? Date.now)();
  const saved = readCloudAccountsState({ env }, ports);
  let providers = requestedProvider ? [requestedProvider] : (saved.providers.length ? saved.providers : ['codex']);
  if (quiet || printCodexHome) {
    providers = (requestedProvider ? [requestedProvider] : saved.providers).filter(p => isCloudAccountsActive({ env, provider: p }, ports));
    if (!providers.length) return { exitCode: 0, message: '' };
  }
  const messages = [];
  let codexHealthyHome = '';
  for (const provider of providers) {
    const cached = saved.active?.[provider];
    const expiresMs = cached?.expires_at ? Date.parse(cached.expires_at) : NaN;
    const tokenExpiresMs = cached?.access_token_expires_at ? Date.parse(cached.access_token_expires_at) : NaN;
    const tokenFreshEnough = !Number.isFinite(tokenExpiresMs) || (tokenExpiresMs - now) > 5 * 60 * 1000;
    const fiveH = cached?.five_hour_used_percent ?? 0, sevenD = cached?.weekly_used_percent ?? 0;
    const cachedState = cached?.state ?? 'ready';
    const isRevokedCached = cachedState === 'reauth_required' || Boolean(cached?.account_id && saved.reauth?.[cached.account_id]);
    const validCache = Boolean(
      cached?.account_id && cached?.materialized_local === true && cachedState === 'ready' && !isRevokedCached && !saved.cooling?.[provider]
      && Number.isFinite(expiresMs) && (expiresMs - now) > 15 * 60 * 1000 && tokenFreshEnough && fiveH < 100 && sevenD < 100
      && hasLocalMaterializedFile(fs, provider, env),
    );
    if (validCache) {
      if (provider === 'codex') codexHealthyHome = pddManagedCodexHome(env);
      if (!quiet && !printCodexHome) messages.push(`Active ${provider} account "${cached.label}" is fresh.`);
      continue;
    }
    try {
      const shouldSkipCached = Boolean((fiveH >= 100 || sevenD >= 100 || isRevokedCached) && cached?.account_id);
      const reply = await leaseCloudAccount({
        provider,
        currentAccountId: shouldSkipCached ? null : (cached?.account_id ?? null),
        skipAccountIds: shouldSkipCached ? [cached.account_id] : [],
        holderId: 'terminal-sync',
        updateState: false,
      }, { cwd, env, timeoutMs, ...(quiet || printCodexHome ? { maxRetries: 0 } : {}) }, ports);
      if (reply?.state === 'leased' && !isReauthRequiredAccount(reply.account)) {
        applyMaterializedLease(reply, { env }, ports);
        if (provider === 'codex' && hasLocalMaterializedFile(fs, 'codex', env)) codexHealthyHome = pddManagedCodexHome(env);
        if (!quiet && !printCodexHome) messages.push(`Synced ${provider} account "${reply.account?.label ?? reply.account?.account_id}".`);
      } else if (reply?.state === 'leased' && isReauthRequiredAccount(reply.account)) {
        markLocalAccountReauthRequired(reply.account?.account_id, { env }, ports);
        if (!quiet && !printCodexHome) messages.push(`Account "${reply.account?.label ?? reply.account?.account_id}" requires re-authentication.`);
      } else if (reply?.state === 'all_cooling') {
        const latestSaved = readCloudAccountsState({ env }, ports);
        if (latestSaved.enrolled && latestSaved.providers.includes(provider)) {
          writeCloudAccountsState({ ...latestSaved, cooling: { ...latestSaved.cooling, [provider]: { wake_at: reply.wake_at ?? null } } }, { env }, ports);
        }
        if (!quiet && !printCodexHome) messages.push(`All ${provider} accounts are cooling${reply.wake_at ? ` until ${reply.wake_at}` : ''}; keeping current local credentials.`);
      }
    } catch (error) {
      let cachedMarkedReauth = false;
      if (isReauthRequiredFailure(error)) {
        const explicitId = error?.payload?.account_id ?? error?.payload?.detail?.account_id ?? error?.payload?.account?.account_id ?? null;
        if (typeof explicitId === 'string' && explicitId) {
          markLocalAccountReauthRequired(explicitId, { env }, ports);
          if (explicitId === cached?.account_id) cachedMarkedReauth = true;
        }
      }
      if (provider === 'codex' && !codexHealthyHome && cached?.account_id && !isRevokedCached && !cachedMarkedReauth && !isReauthRequiredFailure(error) && Number.isFinite(expiresMs) && expiresMs > now) {
        try { if (fs.statSync(managedCodexAuthPath(env))?.isFile()) codexHealthyHome = pddManagedCodexHome(env); } catch {}
      }
      if (!quiet && !printCodexHome) messages.push(`Cloud sync skipped for ${provider}; keeping current local credentials.`);
    }
  }
  return printCodexHome ? { exitCode: 0, message: codexHealthyHome } : { exitCode: 0, message: quiet ? '' : messages.join('\n') };
}

export function runAutoCommand(mode, { env }, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const targets = shellProfileEntries(env);
  if (mode === 'status') {
    const activeFiles = targets.filter(e => { try { return fs.readFileSync(e.path, 'utf8').includes(AUTO_BEGIN); } catch { return false; } }).map(e => e.path);
    return { exitCode: 0, message: activeFiles.length ? `Terminal auto-switch: on (${activeFiles.join(', ')}).` : 'Terminal auto-switch: off (default).' };
  }
  if (mode === 'on') {
    for (const entry of targets) {
      let current = '';
      try { current = fs.readFileSync(entry.path, 'utf8'); } catch (err) { if (err?.code !== 'ENOENT') throw err; }
      const updated = applyAutoSwitchBlock(current, entry.shell);
      if (updated !== current) writeAtomicPreservingSymlinkAndMode(fs, entry.path, updated, { defaultMode: 0o644 });
    }
    return { exitCode: 0, message: 'Enabled opt-in terminal auto-switch in ~/.zshrc, ~/.bashrc, and ~/.config/fish/config.fish. Open a new shell or source your profile.' };
  }
  if (mode === 'off') {
    for (const entry of targets) {
      let current;
      try { current = fs.readFileSync(entry.path, 'utf8'); } catch (err) { if (err?.code === 'ENOENT') continue; throw err; }
      const updated = removeAutoSwitchBlock(current);
      if (updated !== current) writeAtomicPreservingSymlinkAndMode(fs, entry.path, updated, { defaultMode: 0o644 });
    }
    restoreLocalClaudeGatewayConfig({ env }, ports);
    return { exitCode: 0, message: 'Removed terminal auto-switch wrapper from ~/.zshrc, ~/.bashrc, and ~/.config/fish/config.fish.' };
  }
  return { exitCode: 2, message: 'Use pdd accounts auto on|off|status.' };
}

export function reconcileListedState(accounts, current, { env }, ports = {}) {
  const nowIso = new Date((ports.now ?? Date.now)()).toISOString();
  const accessible = accounts.filter(a => !a.revoked);
  const validIds = new Set(accessible.map(a => a.account_id).filter(Boolean));
  const nextProviders = [...new Set(accessible.map(a => a.provider).filter(Boolean))];
  const nextReauth = {};
  for (const [accId, meta] of Object.entries(current.reauth ?? {})) {
    if (!validIds.has(accId)) continue;
    const acc = accessible.find(a => a.account_id === accId);
    const refreshedIso = acc?.last_refresh_at ?? acc?.refreshed_at ?? null;
    if (!acc || isReauthRequiredAccount(acc) || isLocalReauthUnresolved(accId, refreshedIso, current.reauth)) nextReauth[accId] = meta;
  }
  for (const acc of accessible) if (acc?.account_id && isReauthRequiredAccount(acc) && !nextReauth[acc.account_id]) nextReauth[acc.account_id] = { marked_at: nowIso };
  const nextActive = {};
  for (const [prov, entry] of Object.entries(current.active ?? {})) {
    if (!validIds.has(entry?.account_id)) continue;
    const acc = accessible.find(a => a.account_id === entry.account_id);
    const wasClearedByNewRefresh = Boolean(current.reauth?.[entry.account_id] && !nextReauth[entry.account_id]);
    const effectiveEntry = wasClearedByNewRefresh && entry.state === 'reauth_required' ? { ...entry, state: 'ready' } : entry;
    nextActive[prov] = acc ? {
      ...entry,
      label: acc.label ?? acc.account_id,
      state: accountDisplayState(acc, effectiveEntry, nextReauth),
      last_refresh_at: acc.last_refresh_at ?? acc.refreshed_at ?? entry.last_refresh_at ?? null,
      access_token_expires_at: entry.access_token_expires_at ?? null,
      materialized_local: wasClearedByNewRefresh ? false : (entry.materialized_local === true),
      five_hour_used_percent: typeof acc.five_hour_used_percent === 'number' ? acc.five_hour_used_percent : entry.five_hour_used_percent,
      five_hour_reset_at: acc.five_hour_reset_at ?? entry.five_hour_reset_at,
      weekly_used_percent: typeof acc.weekly_used_percent === 'number' ? acc.weekly_used_percent : entry.weekly_used_percent,
      weekly_reset_at: acc.weekly_reset_at ?? entry.weekly_reset_at,
    } : entry;
  }
  const prevCodex = current.active?.codex;
  if (prevCodex && (!nextActive.codex || (prevCodex.managed_codex_gateway === true && !nextActive.codex?.managed_codex_gateway))) {
    restoreLocalCodexGatewayConfig({ env, previousModelProvider: prevCodex.previous_codex_model_provider ?? null, removeAuthFile: !nextActive.codex }, ports);
  }
  restoreLocalClaudeGatewayConfig({ env, removeManagedFile: !nextActive.claude }, ports);
  const nextCooling = Object.fromEntries(Object.entries(current.cooling ?? {}).filter(([prov]) => nextProviders.includes(prov)));
  const updatedState = writeCloudAccountsState({ enrolled: accessible.length > 0, providers: nextProviders, active: nextActive, cooling: nextCooling, reauth: nextReauth }, { env }, ports);
  return { accessible, updatedState };
}

function renderStatusSections({
  current,
  accessible,
  pendingInvites,
  cloudReachable,
  activeAutoProfiles,
  codexRuntimeLines,
  reauthRequired,
  nowMs,
}) {
  const accessibleIds = new Set(accessible.map(a => a?.account_id).filter(Boolean));
  const visiblePendingInvites = Array.isArray(pendingInvites)
    ? pendingInvites.filter(inv => !(inv?.account_id && accessibleIds.has(inv.account_id)))
    : [];

  let statusValue;
  if (current.enrolled) {
    if (cloudReachable) {
      const countPart = `${accessible.length} account${accessible.length === 1 ? '' : 's'}`;
      const invitePart = visiblePendingInvites.length > 0
        ? `, ${visiblePendingInvites.length} pending invite${visiblePendingInvites.length === 1 ? '' : 's'}`
        : '';
      statusValue = `enrolled (${countPart}${invitePart})`;
    } else {
      statusValue = 'enrolled (offline — cached local state)';
    }
  } else if (cloudReachable) {
    statusValue = visiblePendingInvites.length > 0
      ? `not enrolled (${visiblePendingInvites.length} pending invite${visiblePendingInvites.length === 1 ? '' : 's'})`
      : 'not enrolled';
  } else {
    statusValue = 'not enrolled (offline — cached local state)';
  }

  const autoSwitchValue = activeAutoProfiles.length > 0 ? 'on' : 'off';

  const sections = [[
    'PDD Cloud Accounts',
    `  ${'Status:'.padEnd(12)}  ${statusValue}`,
    `  ${'Auto-switch:'.padEnd(12)}  ${autoSwitchValue}`,
  ]];

  if (codexRuntimeLines.length > 0) {
    sections.push(['Running pdd-codex', ...codexRuntimeLines]);
  }

  const activeEntries = Object.entries(current.active ?? {}).filter(([, entry]) => entry && typeof entry === 'object');
  if (activeEntries.length > 0) {
    const activeRows = activeEntries.map(([prov, entry]) => {
      const liveAcc = accessible.find(a => a.account_id === entry.account_id) ?? null;
      const rawState = liveAcc ? accountDisplayState(liveAcc, entry, current.reauth) : (entry.state || 'ready');
      const dispState = sanitizeStatusText(rawState) || 'ready';
      const access = formatSeatAccess(liveAcc) || formatSeatAccess(entry);
      const quota = formatStatusQuota(
        liveAcc?.five_hour_used_percent ?? entry.five_hour_used_percent,
        liveAcc?.five_hour_reset_at ?? entry.five_hour_reset_at,
        liveAcc?.weekly_used_percent ?? entry.weekly_used_percent,
        liveAcc?.weekly_reset_at ?? entry.weekly_reset_at,
      );
      const leaseLine = formatExpiryRemaining(
        liveAcc?.access_token_expires_at ?? entry.access_token_expires_at ?? entry.expires_at,
        nowMs,
      );
      return {
        prov: sanitizeStatusText(prov) || 'unknown',
        label: sanitizeStatusText(entry.label) || sanitizeStatusText(entry.account_id) || '-',
        stateTag: `[${dispState}]`,
        access,
        quota,
        leaseLine,
      };
    });
    const provW = Math.max(...activeRows.map(r => r.prov.length));
    const labelW = Math.max(...activeRows.map(r => r.label.length));
    const stateW = Math.max(...activeRows.map(r => r.stateTag.length));
    const seatLines = ['Active Seats'];
    activeRows.forEach((row, idx) => {
      if (idx > 0) seatLines.push('');
      const headerParts = [row.prov.padEnd(provW), row.label.padEnd(labelW), row.stateTag.padEnd(stateW)];
      if (row.access) headerParts.push(row.access);
      seatLines.push(`  ${headerParts.join('  ')}`.trimEnd());
      seatLines.push(`    ${'Quota:'.padEnd(10)}  ${row.quota}`);
      seatLines.push(`    ${'Lease:'.padEnd(10)}  ${row.leaseLine}`);
    });
    sections.push(seatLines);
  } else if (current.enrolled) {
    sections.push(['Active Seats', '  None']);
  }

  if (reauthRequired.length > 0) {
    const actionLines = ['Action Required'];
    for (const item of reauthRequired) {
      const prov = sanitizeStatusText(item.provider) || 'codex';
      const label = sanitizeStatusText(item.label) || sanitizeStatusText(item.account_id) || '-';
      actionLines.push(`  Re-authenticate "${label}" (${prov}):`);
      actionLines.push(`    pdd accounts add --provider ${prov} --label ${label}`);
    }
    sections.push(actionLines);
  }

  return sections.map(s => s.join('\n')).join('\n\n');
}

export async function runStatusCommand({ json = false, cwd, env }, ports = {}) {
  const fs = ports.fs ?? nativeFs, nowMs = (ports.now ?? Date.now)();
  let current = readCloudAccountsState({ env }, ports), accessible = [], pendingInvites = [], cloudReachable = false;
  try {
    const listed = await fetchAccountsList({ cwd, env, refresh: true }, ports);
    cloudReachable = true; pendingInvites = listed.pendingInvites;
    const reconciled = reconcileListedState(listed.accounts, current, { env }, ports);
    accessible = reconciled.accessible; current = reconciled.updatedState;
  } catch { cloudReachable = false; }

  const codexHomePath = pddManagedCodexHome(env);
  let codexAuthPresent = false, codexConfigPresent = false;
  try { codexAuthPresent = Boolean(fs.statSync(managedCodexAuthPath(env))?.isFile()); } catch {}
  try { codexConfigPresent = Boolean(fs.statSync(managedCodexConfigPath(env))?.isFile()); } catch {}
  const activeAutoProfiles = shellProfileEntries(env).filter(e => { try { return fs.readFileSync(e.path, 'utf8').includes(AUTO_BEGIN); } catch { return false; } }).map(e => e.path);
  const runtimeLeases = readLiveCodexRuntimeLeases({ env, tmpRoot: ports.tmpRoot, uid: ports.uid }, ports);
  const { codex_runtime: codexRuntime, lines: codexRuntimeLines } = summarizeCodexRuntimeStatus({
    runtimeLeases,
    accounts: accessible,
    cachedActiveCodex: current.active?.codex ?? null,
  });

  const reauthRequired = accessible
    .filter(a => accountDisplayState(a, current.active?.[a.provider], current.reauth) === 'reauth_required')
    .map(a => ({ account_id: a.account_id, label: a.label ?? a.account_id, provider: a.provider }));
  for (const [prov, entry] of Object.entries(current.active ?? {})) {
    if (entry?.state === 'reauth_required' && !reauthRequired.some(r => r.account_id === entry.account_id)) {
      reauthRequired.push({ account_id: entry.account_id, label: entry.label ?? entry.account_id, provider: prov });
    }
  }

  if (json) {
    return {
      exitCode: 0,
      message: redactSecrets(JSON.stringify({
        enrolled: current.enrolled, cloud_reachable: cloudReachable, providers: current.providers,
        codex_home: { path: codexHomePath, materialized: codexAuthPresent && codexConfigPresent, auth_present: codexAuthPresent, config_present: codexConfigPresent },
        auto_switch: { enabled: activeAutoProfiles.length > 0, profiles: activeAutoProfiles },
        codex_runtime: codexRuntime,
        active: withLeftPercentActiveMap(current.active), cooling: current.cooling, reauth_required: reauthRequired,
        accounts: accessible.map(a => withLeftPercentFields({ ...a, state: accountDisplayState(a, current.active?.[a.provider], current.reauth) })),
        pending_invites: pendingInvites,
      }, null, 2)),
    };
  }

  const message = renderStatusSections({
    current,
    accessible,
    pendingInvites,
    cloudReachable,
    activeAutoProfiles,
    codexRuntimeLines,
    reauthRequired,
    nowMs,
  });
  return { exitCode: 0, message: redactSecrets(message) };
}

export function syncStateAfterAccountRemoval(account, accounts, { env }, ports = {}) {
  const current = readCloudAccountsState({ env }, ports);
  const remaining = accounts.filter(a => a.account_id !== account.account_id && !a.revoked);
  const remainingIds = new Set(remaining.map(a => a.account_id));
  const nextProviders = [...new Set(remaining.map(a => a.provider).filter(Boolean))];
  const nextActive = {};
  for (const [prov, entry] of Object.entries(current.active ?? {})) {
    if (entry?.account_id && entry.account_id !== account.account_id && remainingIds.has(entry.account_id)) nextActive[prov] = entry;
  }
  const prevCodex = current.active?.codex;
  if (prevCodex && (!nextActive.codex || (prevCodex.managed_codex_gateway === true && !nextActive.codex?.managed_codex_gateway))) {
    restoreLocalCodexGatewayConfig({ env, previousModelProvider: prevCodex.previous_codex_model_provider ?? null, removeAuthFile: !nextActive.codex }, ports);
  }
  restoreLocalClaudeGatewayConfig({ env, removeManagedFile: !nextActive.claude }, ports);
  const nextCooling = Object.fromEntries(Object.entries(current.cooling ?? {}).filter(([prov]) => nextProviders.includes(prov)));
  const nextReauth = Object.fromEntries(Object.entries(current.reauth ?? {}).filter(([accId]) => accId !== account.account_id && remainingIds.has(accId)));
  writeCloudAccountsState({ enrolled: remaining.length > 0, providers: nextProviders, active: nextActive, cooling: nextCooling, reauth: nextReauth }, { env }, ports);
}
