// Generated from prompts/cli/accounts-cli.prompt.md.
// Top-level `pdd accounts ...` subcommand dispatch.
import * as nativeFs from 'node:fs';
import {
  CloudAccountsError,
  cloudAccountsRequest,
  isLocalReauthUnresolved,
  isReauthRequiredAccount,
  isReauthRequiredFailure,
  leaseCloudAccount,
  markLocalAccountReauthRequired,
  readCloudAccountsState,
  restoreLocalClaudeGatewayConfig,
  restoreLocalCodexGatewayConfig,
  writeCloudAccountsState,
} from '../login-pool.mjs';
import { redactSecrets } from '../secret-redaction.mjs';
import { refreshInstalledAutoSwitchBlocks } from './auto-switch.mjs';
import {
  accountDisplayState,
  formatAccountQuotaSummary,
  renderAccountsTable,
  sanitizeLabel,
  withLeftPercentActiveMap,
  withLeftPercentFields,
} from './cli-format.mjs';
import {
  reconcileListedState,
  runAutoCommand,
  runStatusCommand,
  runSyncCommand,
  syncStateAfterAccountRemoval,
} from './cli-status-sync.mjs';
import { enrollOrImportAccount } from './enroll-iteration.mjs';
import { applyMaterializedLease, hasLocalMaterializedFile } from './enroll-login.mjs';
import { runInteractiveCodexWithAutoRotate } from './legacy-pty-rotate.mjs';
import {
  applySharePayloadsToAccounts,
  buildUnsharePayloads,
  fetchAccountsList,
  isOwnedAccount,
  parseWithTargets,
  resolveAccount,
  resolveSharePayloads,
} from './share-helpers.mjs';

const AUTO_REFRESH_SUBCOMMANDS = new Set(['list', 'status', 'add', 'import', 'use', 'next', 'codex', 'sync', 'accept']);

async function handleUse(operands, options, { cwd, env }, ports) {
  const { account, accounts } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
  const reauthMsg = `Account "${account.label}" requires re-authentication (state: reauth_required). Run pdd accounts add --provider ${account.provider} --label ${account.label}.`;
  if (isReauthRequiredAccount(account)) { markLocalAccountReauthRequired(account.account_id, { env }, ports); return { exitCode: 1, message: reauthMsg }; }
  let reply;
  try {
    reply = await leaseCloudAccount({
      provider: account.provider, preferredLabel: account.label, currentAccountId: account.account_id, holderId: 'local-cli', updateState: false,
    }, { cwd, env }, ports);
  } catch (err) {
    const attributedId = err?.payload?.account_id ?? err?.payload?.detail?.account_id ?? err?.payload?.account?.account_id ?? null;
    if (isReauthRequiredFailure(err) && attributedId) { markLocalAccountReauthRequired(attributedId, { env }, ports); return { exitCode: 1, message: reauthMsg }; }
    throw err;
  }
  if (reply?.state === 'all_cooling') return { exitCode: 1, message: `All ${account.provider} accounts are cooling${reply.wake_at ? ` until ${reply.wake_at}` : ''}.` };
  const currentBeforeUse = readCloudAccountsState({ env }, ports);
  const replyRefreshIso = reply?.account?.last_refresh_at ?? reply?.account?.refreshed_at ?? reply?.lease?.last_refresh_at ?? null;
  if (isReauthRequiredAccount(reply?.account) || isLocalReauthUnresolved(reply?.account?.account_id ?? account.account_id, replyRefreshIso, currentBeforeUse.reauth)) {
    markLocalAccountReauthRequired(account.account_id, { env }, ports);
    return { exitCode: 1, message: reauthMsg };
  }
  applyMaterializedLease(reply, { env }, ports);
  const synced = readCloudAccountsState({ env }, ports);
  const allProviders = [...new Set(accounts.filter(a => !a.revoked).map(a => a.provider).filter(Boolean))];
  writeCloudAccountsState({ ...synced, enrolled: allProviders.length > 0, providers: allProviders }, { env }, ports);
  return { exitCode: 0, message: `Active ${account.provider} account set to "${reply.account?.label ?? account.label}"${formatAccountQuotaSummary(reply.account ?? account)}.` };
}

async function handleNext(options, { cwd, env }, ports) {
  const saved = readCloudAccountsState({ env }, ports);
  const provider = options['--provider'] || (saved.providers.length === 1 ? saved.providers[0] : 'codex');
  const currentId = saved.active?.[provider]?.account_id ?? null;
  const skipIds = currentId ? [currentId] : [];
  let reply = null;
  for (let attempt = 0; attempt < 8; attempt += 1) {
    try {
      reply = await leaseCloudAccount({ provider, currentAccountId: null, skipAccountIds: skipIds, holderId: 'local-cli', updateState: false }, { cwd, env }, ports);
    } catch (err) {
      if (isReauthRequiredFailure(err)) {
        const failedId = err?.payload?.account_id ?? err?.payload?.detail?.account_id ?? null;
        if (failedId) markLocalAccountReauthRequired(failedId, { env }, ports);
        return { exitCode: 1, message: `All remaining ${provider} accounts require re-authentication (state: reauth_required). Run pdd accounts add --provider ${provider}.` };
      }
      throw err;
    }
    if (reply?.state === 'leased' && isReauthRequiredAccount(reply.account) && reply.account?.account_id && !skipIds.includes(reply.account.account_id)) {
      markLocalAccountReauthRequired(reply.account.account_id, { env }, ports);
      skipIds.push(reply.account.account_id);
      continue;
    }
    break;
  }
  if (reply?.state === 'all_cooling') {
    const latestSaved = readCloudAccountsState({ env }, ports);
    if (latestSaved.enrolled && latestSaved.providers.includes(provider)) {
      writeCloudAccountsState({ ...latestSaved, cooling: { ...latestSaved.cooling, [provider]: { wake_at: reply.wake_at ?? null } } }, { env }, ports);
    }
    return { exitCode: 1, message: `All ${provider} accounts are cooling${reply.wake_at ? ` until ${reply.wake_at}` : ''}.` };
  }
  if (!reply || reply.state !== 'leased' || isReauthRequiredAccount(reply.account)) {
    if (reply?.account?.account_id) markLocalAccountReauthRequired(reply.account.account_id, { env }, ports);
    return { exitCode: 1, message: `All remaining ${provider} accounts require re-authentication (state: reauth_required). Run pdd accounts add --provider ${provider}.` };
  }
  applyMaterializedLease(reply, { env }, ports);
  return { exitCode: 0, message: `Switched ${provider} account to "${reply.account?.label ?? reply.account?.account_id}"${formatAccountQuotaSummary(reply.account)}.` };
}

async function handleShare(operands, options, { cwd, env }, ports) {
  const labelArg = typeof operands[0] === 'string' ? operands[0].trim() : '', allFlag = options['--all'] === true, providerFilter = options['--provider'] || null;
  if (Boolean(labelArg) === allFlag) return { exitCode: 2, message: 'Specify either LABEL or --all on pdd accounts share, not both.' };
  const parsedWith = parseWithTargets(typeof options['--with'] === 'string' ? options['--with'] : '');
  if (parsedWith.error) return { exitCode: 2, message: parsedWith.error };
  if (!parsedWith.targets.length) return { exitCode: 2, message: 'Use pdd accounts share LABEL --with USER|ORG/TEAM[,...] or pdd accounts share --all --with USER|ORG/TEAM[,...].' };
  const sharePayloads = await resolveSharePayloads(parsedWith.targets, { cwd, env }, ports);
  let targetAccounts, pendingInvites = [];
  if (allFlag) {
    const listed = await fetchAccountsList({ cwd, env, refresh: false }, ports);
    pendingInvites = listed.pendingInvites;
    targetAccounts = listed.accounts.filter(acc => isOwnedAccount(acc) && (!providerFilter || acc.provider === providerFilter));
    if (!targetAccounts.length) return { exitCode: 1, message: providerFilter ? `No owned ${providerFilter} Cloud accounts found.` : 'No owned Cloud accounts found.' };
  } else {
    const resolved = await resolveAccount(labelArg, { cwd, env, provider: providerFilter }, ports);
    targetAccounts = [resolved.account]; pendingInvites = resolved.pendingInvites ?? [];
  }
  const notes = await applySharePayloadsToAccounts(targetAccounts, sharePayloads, { cwd, env, pendingInvites }, ports);
  if (targetAccounts.length === 1 && sharePayloads.length === 1) {
    if (notes[0]?.alreadyShared) return { exitCode: 0, message: `Account "${targetAccounts[0].label}" is already shared with ${notes[0].display}.` };
    return { exitCode: 0, message: `Shared "${targetAccounts[0].label}" with ${notes[0].display}${notes[0]?.inviteId ? ` (invite ${notes[0].inviteId})` : ''}.` };
  }
  const acctNames = targetAccounts.map(a => `"${a.label}"`).join(', ');
  const targetNames = sharePayloads.map(payload => {
    const matching = notes.filter(row => row.display === payload.display);
    const invitesForTarget = matching.filter(row => row.inviteId).map(row => row.inviteId);
    if (invitesForTarget.length) return `${payload.display} (invite ${invitesForTarget.join(', ')})`;
    if (matching.length && matching.every(row => row.alreadyShared)) return `${payload.display} (already shared)`;
    return payload.display;
  }).join(', ');
  return { exitCode: 0, message: `Shared ${acctNames} with ${targetNames}.` };
}

async function handleAccept(operands, { cwd, env }, ports) {
  const rawInvite = String(operands[0] ?? '').trim();
  let inviteId = rawInvite;
  if (!rawInvite.startsWith('inv_')) {
    const { pendingInvites } = await fetchAccountsList({ cwd, env }, ports);
    const sanitizedInvite = sanitizeLabel(rawInvite, '');
    const match = pendingInvites.find(inv => inv.invite_id === rawInvite || inv.label === rawInvite || inv.account_id === rawInvite || (sanitizedInvite && sanitizeLabel(inv.label, '') === sanitizedInvite));
    if (match?.invite_id) inviteId = match.invite_id;
  }
  const res = await cloudAccountsRequest('POST', `/v1/accounts/invites/${encodeURIComponent(inviteId)}/accept`, { body: {}, cwd, env }, ports);
  const current = readCloudAccountsState({ env }, ports);
  const acceptedAcc = res?.account ?? null;
  const provider = acceptedAcc?.provider ?? res?.provider ?? null;
  let nextProviders = provider ? [...new Set([...current.providers, provider])] : current.providers;
  if (!provider) {
    const listed = await fetchAccountsList({ cwd, env }, ports).catch(() => null);
    if (listed?.accounts) nextProviders = [...new Set(listed.accounts.filter(a => !a.revoked).map(a => a.provider).filter(Boolean))];
  }
  writeCloudAccountsState({ ...current, enrolled: true, providers: nextProviders }, { env }, ports);
  const fs = ports.fs ?? nativeFs, nowMs = (ports.now ?? Date.now)();
  const existingActive = provider ? current.active?.[provider] : null;
  const existingExpMs = existingActive?.expires_at ? Date.parse(existingActive.expires_at) : NaN;
  const needsActivation = Boolean(provider && (!existingActive?.account_id || existingActive.state === 'reauth_required' || Boolean(current.reauth?.[existingActive.account_id]) || !Number.isFinite(existingExpMs) || existingExpMs <= nowMs || !hasLocalMaterializedFile(fs, provider, env)));
  let syncWarning = '';
  if (needsActivation) {
    try {
      const leased = await leaseCloudAccount({
        provider, preferredLabel: acceptedAcc?.label ?? null, currentAccountId: acceptedAcc?.account_id ?? null, holderId: 'local-cli', updateState: false,
      }, { cwd, env }, ports);
      if (leased?.state === 'leased' && !isReauthRequiredAccount(leased.account)) {
        applyMaterializedLease(leased, { env }, ports);
        const refreshed = readCloudAccountsState({ env }, ports);
        writeCloudAccountsState({ ...refreshed, enrolled: true, providers: [...new Set([...refreshed.providers, ...nextProviders])] }, { env }, ports);
      } else if (leased?.state === 'leased' && isReauthRequiredAccount(leased.account)) {
        markLocalAccountReauthRequired(leased.account?.account_id, { env }, ports);
        syncWarning = ' Warning: account requires re-authentication before local sync.';
      } else if (leased?.state === 'all_cooling') {
        syncWarning = ` Warning: all ${provider} accounts are currently cooling${leased.wake_at ? ` until ${leased.wake_at}` : ''}; run pdd accounts sync once quota resets.`;
      }
    } catch (err) {
      const reason = redactSecrets(String(err?.message ?? 'lease failed')).trim();
      syncWarning = ` Warning: initial local sync failed (${reason}) — run ${acceptedAcc?.label ? `pdd accounts use ${acceptedAcc.label}` : 'pdd accounts sync'}.`;
    }
  }
  return { exitCode: 0, message: redactSecrets(`Accepted shared account${acceptedAcc?.label ? ` "${acceptedAcc.label}"` : ` invite ${inviteId}`}.${syncWarning}`) };
}

export async function runAccountsCli({
  commandId = 'accounts',
  operands = [],
  options = {},
  cwd = process.cwd(),
  env = process.env,
  stdin = process.stdin,
} = {}, ports = {}) {
  const sub = commandId === 'accounts' ? 'list' : commandId.slice('accounts.'.length);
  if (AUTO_REFRESH_SUBCOMMANDS.has(sub)) refreshInstalledAutoSwitchBlocks({ env }, ports);
  try {
    switch (sub) {
      case 'list': {
        const nowMs = (ports.now ?? Date.now)();
        const { accounts, pendingInvites } = await fetchAccountsList({ cwd, env, refresh: true }, ports);
        const { accessible, updatedState } = reconcileListedState(accounts, readCloudAccountsState({ env }, ports), { env }, ports);
        const normalizedAccounts = accessible.map(acc => withLeftPercentFields({ ...acc, state: accountDisplayState(acc, updatedState.active?.[acc.provider], updatedState.reauth) }));
        return {
          exitCode: 0,
          message: redactSecrets(options['--json'] === true
            ? JSON.stringify({ accounts: normalizedAccounts, pending_invites: pendingInvites, active: withLeftPercentActiveMap(updatedState.active) }, null, 2)
            : renderAccountsTable(normalizedAccounts, pendingInvites, updatedState.active, nowMs)),
        };
      }
      case 'status':
        return await runStatusCommand({ json: options['--json'] === true, cwd, env }, ports);
      case 'add':
        return await enrollOrImportAccount('add', {
          provider: options['--provider'], label: options['--label'], replace: options['--replace'] === true,
          loop: options['--loop'] === true, deviceAuth: options['--device-auth'] === true, withTargets: options['--with'] ?? '',
          cwd, env, stdin,
        }, ports);
      case 'import':
        return await enrollOrImportAccount('import', {
          provider: options['--provider'], from: options['--from'] ?? null, label: options['--label'],
          replace: options['--replace'] === true, withTargets: options['--with'] ?? '', cwd, env, stdin,
        }, ports);
      case 'use':
        return await handleUse(operands, options, { cwd, env }, ports);
      case 'next':
        return await handleNext(options, { cwd, env }, ports);
      case 'codex':
        return await runInteractiveCodexWithAutoRotate({ args: operands, cwd, env, stdin }, ports);
      case 'sync':
        return await runSyncCommand({
          provider: options['--provider'], quiet: options['--quiet'] === true,
          printCodexHome: options['--print-codex-home'] === true || env?.PDD_PRINT_CODEX_HOME === '1',
          timeoutMs: options['--timeout-ms'] !== undefined ? Number(options['--timeout-ms']) : 1200,
          cwd, env,
        }, ports);
      case 'auto':
        return runAutoCommand(operands[0], { env }, ports);
      case 'pause': {
        const { account } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/pause`, { body: {}, cwd, env }, ports);
        const saved = readCloudAccountsState({ env }, ports), prov = account.provider;
        if (prov && saved.active?.[prov]?.account_id === account.account_id) {
          const prevEntry = saved.active[prov], nextActive = { ...saved.active };
          delete nextActive[prov];
          writeCloudAccountsState({ ...saved, active: nextActive }, { env }, ports);
          if (prov === 'claude') restoreLocalClaudeGatewayConfig({ env }, ports);
          else if (prov === 'codex') restoreLocalCodexGatewayConfig({ env, previousModelProvider: prevEntry.previous_codex_model_provider ?? null, removeAuthFile: true }, ports);
        } else if (prov === 'claude') {
          restoreLocalClaudeGatewayConfig({ env, removeManagedFile: false }, ports);
        }
        return { exitCode: 0, message: `Paused account "${account.label}".` };
      }
      case 'unpause': {
        const { account } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/unpause`, { body: {}, cwd, env }, ports);
        return { exitCode: 0, message: `Unpaused account "${account.label}".` };
      }
      case 'share':
        return await handleShare(operands, options, { cwd, env }, ports);
      case 'accept':
        return await handleAccept(operands, { cwd, env }, ports);
      case 'unshare': {
        const labelArg = typeof operands[0] === 'string' ? operands[0].trim() : '', allFlag = options['--all'] === true, providerFilter = options['--provider'] || null;
        if (Boolean(labelArg) === allFlag) return { exitCode: 2, message: 'Specify either LABEL or --all on pdd accounts unshare, not both.' };
        const built = buildUnsharePayloads({ userOption: options['--user'], withOption: options['--with'] });
        if (built.error) return { exitCode: 2, message: built.error };
        if (!built.payloads.length) return { exitCode: 2, message: 'Use pdd accounts unshare LABEL --user USER or pass --with USER|ORG/TEAM[,...].' };
        let targetAccounts;
        if (allFlag) {
          const { accounts } = await fetchAccountsList({ cwd, env, refresh: false }, ports);
          targetAccounts = accounts.filter(acc => isOwnedAccount(acc) && (!providerFilter || acc.provider === providerFilter));
          if (!targetAccounts.length) return { exitCode: 1, message: providerFilter ? `No owned ${providerFilter} Cloud accounts found.` : 'No owned Cloud accounts found.' };
        } else {
          targetAccounts = [(await resolveAccount(labelArg, { cwd, env, provider: providerFilter }, ports)).account];
        }
        for (const account of targetAccounts) {
          for (const item of built.payloads) await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/unshare`, { body: item.body, cwd, env }, ports);
        }
        if (targetAccounts.length === 1 && built.payloads.length === 1) return { exitCode: 0, message: `Revoked "${targetAccounts[0].label}" access for ${built.payloads[0].display}.` };
        return { exitCode: 0, message: `Revoked ${targetAccounts.map(a => `"${a.label}"`).join(', ')} access for ${built.payloads.map(p => p.display).join(', ')}.` };
      }
      case 'leave': {
        const { account, accounts } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
        await cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(account.account_id)}/leave`, { body: {}, cwd, env }, ports);
        syncStateAfterAccountRemoval(account, accounts, { env }, ports);
        return { exitCode: 0, message: `Left shared account "${account.label}".` };
      }
      case 'remove': {
        const { account, accounts } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
        await cloudAccountsRequest('DELETE', `/v1/accounts/${encodeURIComponent(account.account_id)}`, { cwd, env }, ports);
        syncStateAfterAccountRemoval(account, accounts, { env }, ports);
        return { exitCode: 0, message: `Removed account "${account.label}".` };
      }
      case 'log': {
        const { account } = await resolveAccount(operands[0], { cwd, env, provider: options['--provider'] || null }, ports);
        const data = await cloudAccountsRequest('GET', `/v1/accounts/${encodeURIComponent(account.account_id)}/log`, { cwd, env }, ports);
        const entries = Array.isArray(data?.entries) ? data.entries : Array.isArray(data?.events) ? data.events : Array.isArray(data?.log) ? data.log : [];
        if (options['--json'] === true) return { exitCode: 0, message: redactSecrets(JSON.stringify({ account_id: account.account_id, label: account.label, entries }, null, 2)) };
        if (!entries.length) return { exitCode: 0, message: `No audit events recorded for "${account.label}".` };
        return {
          exitCode: 0,
          message: redactSecrets(entries.map(r => `${r.created_at ?? r.at ?? r.timestamp ?? '-'}  ${r.event ?? r.action ?? 'event'}${(r.actor_login ?? r.actor ?? r.machine_label) ? `  (${r.actor_login ?? r.actor ?? r.machine_label})` : ''}${(r.detail ?? r.note) ? `  ${r.detail ?? r.note}` : ''}`).join('\n')),
        };
      }
      default:
        return { exitCode: 2, message: 'Unsupported accounts command. Run pdd accounts --help.' };
    }
  } catch (error) {
    const exitCode = (error instanceof CloudAccountsError && Number.isInteger(error.exitCode)) ? error.exitCode : 1;
    const safeMsg = redactSecrets(error instanceof CloudAccountsError ? error.message : `Accounts command failed: ${error?.message ?? 'unknown error'}`);
    return { exitCode, message: safeMsg };
  }
}
