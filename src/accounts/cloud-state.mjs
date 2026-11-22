// Generated from prompts/cli/login-pool.prompt.md.
// Local accounts-state.json persistence, managed/user path helpers, and auth bundle sanitization.
import { scryptSync } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { homedir } from 'node:os';
import { join } from 'node:path';
import { knownSecretValues, rememberSecrets } from '../secret-redaction.mjs';
import { isPathAtOrInside, readJsonObjectQuiet as readJsonObject, writeAtomicPrivate } from '../shared/atomic-fs.mjs';
import { resolvePddStateBase } from '../shared/state-dir.mjs';
import { isLocalReauthUnresolved, isReauthRequiredAccount } from './cloud-client.mjs';
import { CLOUD_PROVIDERS } from './pool-env.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

export const accountsStatePath = (env = process.env) => join(resolvePddStateBase(env), 'accounts-state.json');
export const pddManagedCodexHome = (env = process.env) => join(resolvePddStateBase(env), 'codex-home');
export const managedCodexAuthPath = (env = process.env) => join(pddManagedCodexHome(env), 'auth.json');
export const managedCodexConfigPath = (env = process.env) => join(pddManagedCodexHome(env), 'config.toml');
export const pddManagedClaudeHome = (env = process.env) => join(resolvePddStateBase(env), 'claude-home');
export const managedClaudeSettingsPath = (env = process.env) => join(pddManagedClaudeHome(env), 'settings.json');

export function claudeTokenFingerprint(token) {
  const clean = typeof token === 'string' ? token.trim() : '';
  return clean ? scryptSync(clean, 'pdd-managed-claude-token-v1', 32).toString('hex') : '';
}

export function normalizeTokenHashes(list) {
  if (!Array.isArray(list)) return [];
  const seen = new Set();
  for (const item of list) {
    if (typeof item === 'string' && /^[a-f0-9]{64}$/i.test(item.trim())) seen.add(item.trim().toLowerCase());
  }
  return [...seen];
}

function normalizeActiveEntry(provider, entry) {
  return {
    account_id: entry.account_id,
    label: typeof entry.label === 'string' ? entry.label : String(entry.label ?? entry.account_id),
    provider,
    is_owner: typeof entry.is_owner === 'boolean' ? entry.is_owner : null,
    state: typeof entry.state === 'string' && entry.state ? entry.state : 'ready',
    lease_id: typeof entry.lease_id === 'string' ? entry.lease_id : null,
    leased_at: typeof entry.leased_at === 'string' ? entry.leased_at : null,
    expires_at: typeof entry.expires_at === 'string' ? entry.expires_at : null,
    last_refresh_at: typeof entry.last_refresh_at === 'string' ? entry.last_refresh_at : null,
    access_token_expires_at: typeof entry.access_token_expires_at === 'string' ? entry.access_token_expires_at : null,
    materialized_local: entry.materialized_local === true,
    delivery_mode: typeof entry.delivery_mode === 'string' ? entry.delivery_mode : null,
    anthropic_base_url: typeof entry.anthropic_base_url === 'string' ? entry.anthropic_base_url : null,
    managed_anthropic_base_url: entry.managed_anthropic_base_url === true,
    codex_gateway_url: typeof entry.codex_gateway_url === 'string' ? entry.codex_gateway_url : null,
    codex_backend_api_url: typeof entry.codex_backend_api_url === 'string' ? entry.codex_backend_api_url : null,
    auto_rotate: typeof entry.auto_rotate === 'boolean' ? entry.auto_rotate : null,
    managed_codex_gateway: entry.managed_codex_gateway === true,
    previous_codex_model_provider: typeof entry.previous_codex_model_provider === 'string' && entry.previous_codex_model_provider ? entry.previous_codex_model_provider : null,
    five_hour_used_percent: typeof entry.five_hour_used_percent === 'number' && Number.isFinite(entry.five_hour_used_percent) ? entry.five_hour_used_percent : null,
    five_hour_reset_at: typeof entry.five_hour_reset_at === 'string' ? entry.five_hour_reset_at : null,
    weekly_used_percent: typeof entry.weekly_used_percent === 'number' && Number.isFinite(entry.weekly_used_percent) ? entry.weekly_used_percent : null,
    weekly_reset_at: typeof entry.weekly_reset_at === 'string' ? entry.weekly_reset_at : null,
  };
}

function normalizeReauthMap(source) {
  const reauth = {};
  if (object(source)) {
    for (const [accId, meta] of Object.entries(source)) {
      if (accId && object(meta)) reauth[accId] = { marked_at: typeof meta.marked_at === 'string' ? meta.marked_at : null };
    }
  }
  return reauth;
}

export function readCloudAccountsState({ env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const raw = readJsonObject(fs, accountsStatePath(env));
  if (!raw) return { enrolled: false, providers: [], active: {}, cooling: {}, reauth: {} };
  const active = {};
  if (object(raw.active)) {
    for (const provider of CLOUD_PROVIDERS) {
      const entry = raw.active[provider];
      if (object(entry) && typeof entry.account_id === 'string' && entry.account_id) {
        active[provider] = normalizeActiveEntry(provider, entry);
      }
    }
  }
  const providers = Array.isArray(raw.providers) ? raw.providers.filter(p => CLOUD_PROVIDERS.includes(p)) : Object.keys(active);
  const managedClaudeTokenHashes = normalizeTokenHashes(raw.managed_claude_token_hashes);
  return {
    enrolled: raw.enrolled === true,
    providers: [...new Set([...providers, ...Object.keys(active)])],
    active,
    cooling: object(raw.cooling) ? raw.cooling : {},
    reauth: normalizeReauthMap(raw.reauth),
    ...(managedClaudeTokenHashes.length > 0 ? { managed_claude_token_hashes: managedClaudeTokenHashes } : {}),
  };
}

export function writeCloudAccountsState(state, { env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const active = {};
  for (const provider of CLOUD_PROVIDERS) {
    const entry = state?.active?.[provider];
    if (object(entry) && typeof entry.account_id === 'string' && entry.account_id) {
      active[provider] = normalizeActiveEntry(provider, entry);
    }
  }
  const providers = [...new Set([...(Array.isArray(state?.providers) ? state.providers.filter(p => CLOUD_PROVIDERS.includes(p)) : []), ...Object.keys(active)])];
  const enrolled = state?.enrolled === true;
  const existingState = (state?.reauth === undefined || state?.managed_claude_token_hashes === undefined)
    ? readCloudAccountsState({ env }, ports)
    : null;
  const sourceReauth = state?.reauth !== undefined ? state.reauth : (enrolled || providers.length > 0 ? existingState?.reauth : {});
  const reauth = normalizeReauthMap(sourceReauth);
  const managedClaudeTokenHashes = normalizeTokenHashes(
    state?.managed_claude_token_hashes !== undefined ? state.managed_claude_token_hashes : existingState?.managed_claude_token_hashes,
  );
  const payload = {
    enrolled,
    updated_at: new Date((ports.now ?? Date.now)()).toISOString(),
    providers,
    active,
    cooling: object(state?.cooling) ? state.cooling : {},
    ...(Object.keys(reauth).length > 0 ? { reauth } : {}),
    ...(managedClaudeTokenHashes.length > 0 ? { managed_claude_token_hashes: managedClaudeTokenHashes } : {}),
  };
  writeAtomicPrivate(fs, accountsStatePath(env), `${JSON.stringify(payload, null, 2)}\n`);
  return payload;
}

export function markLocalAccountReauthRequired(accountId, { env = process.env } = {}, ports = {}) {
  if (!accountId) return null;
  const nowIso = new Date((ports.now ?? Date.now)()).toISOString();
  const saved = readCloudAccountsState({ env }, ports);
  const nextActive = { ...saved.active };
  for (const [prov, entry] of Object.entries(nextActive)) {
    if (entry?.account_id === accountId && entry.state !== 'reauth_required') {
      nextActive[prov] = { ...entry, state: 'reauth_required' };
    }
  }
  return writeCloudAccountsState({ ...saved, active: nextActive, reauth: { ...(saved.reauth ?? {}), [accountId]: { marked_at: nowIso } } }, { env }, ports);
}

export function isCloudAccountsActive({ env = process.env, poolPath, provider } = {}, ports = {}) {
  if (typeof poolPath === 'string' && poolPath.trim()) return false;
  if (provider !== undefined && provider !== null && !CLOUD_PROVIDERS.includes(provider)) return false;
  const saved = readCloudAccountsState({ env }, ports);
  if (!saved.enrolled) return false;
  if (provider !== undefined && provider !== null && Array.isArray(saved.providers)) return saved.providers.includes(provider);
  return saved.providers.length > 0 || Object.keys(saved.active ?? {}).length > 0;
}

export function stripCodexAuthBundle(authJson) {
  const tokens = object(authJson?.tokens) ? authJson.tokens : {};
  rememberSecrets(...knownSecretValues(authJson));
  for (const val of Object.values(tokens)) if (typeof val === 'string' && val.length >= 8) rememberSecrets(val);
  const hasOauth = Boolean((typeof tokens.access_token === 'string' && tokens.access_token.trim()) || (typeof tokens.id_token === 'string' && tokens.id_token.trim()));
  const authMode = typeof authJson?.auth_mode === 'string' && authJson.auth_mode.trim() ? authJson.auth_mode.trim() : (hasOauth ? 'chatgpt' : undefined);
  return {
    ...(authMode ? { auth_mode: authMode } : {}),
    OPENAI_API_KEY: authJson?.OPENAI_API_KEY ?? null,
    tokens: {
      ...tokens,
      access_token: typeof tokens.access_token === 'string' ? tokens.access_token : '',
      refresh_token: '',
      id_token: typeof tokens.id_token === 'string' ? tokens.id_token : '',
      account_id: typeof tokens.account_id === 'string' ? tokens.account_id : '',
    },
    ...(typeof authJson?.last_refresh === 'string' ? { last_refresh: authJson.last_refresh } : {}),
  };
}

export function localCodexHome(env = process.env) {
  const home = env?.HOME || homedir();
  const defaultHome = join(home, '.codex');
  const explicit = typeof env?.CODEX_HOME === 'string' ? env.CODEX_HOME.trim() : '';
  if (!explicit) return defaultHome;
  const managedRoots = [pddManagedCodexHome(env), join(resolvePddStateBase(env), 'codex-runtime')];
  if (typeof env?.PDD_CODEX_RUNTIME_ROOT === 'string' && env.PDD_CODEX_RUNTIME_ROOT.trim()) managedRoots.push(env.PDD_CODEX_RUNTIME_ROOT.trim());
  return managedRoots.some(root => isPathAtOrInside(explicit, root)) ? defaultHome : explicit;
}

export const localCodexAuthPath = (env = process.env) => join(localCodexHome(env), 'auth.json');
export const localCodexConfigPath = (env = process.env) => join(localCodexHome(env), 'config.toml');

export function localClaudePaths(env = process.env) {
  const home = env?.HOME || homedir();
  const claudeDir = (typeof env?.CLAUDE_CONFIG_DIR === 'string' && env.CLAUDE_CONFIG_DIR.trim()) ? env.CLAUDE_CONFIG_DIR.trim() : join(home, '.claude');
  return { settingsPath: join(claudeDir, 'settings.json'), onboardingPath: join(home, '.claude.json') };
}

function extractJwtExpiresAtIso(jwt) {
  if (typeof jwt !== 'string' || !jwt.trim()) return null;
  const parts = jwt.split('.');
  if (parts.length < 2) return null;
  try {
    const payload = JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8'));
    if (typeof payload?.exp === 'number' && Number.isFinite(payload.exp) && payload.exp > 0) return new Date(payload.exp * 1000).toISOString();
  } catch {}
  return null;
}

export function saveActiveLeaseMetadata(leaseReply, {
  env = process.env,
  materializedLocal,
  managedBaseUrl,
  managedCodexGateway,
  codexGatewayUrl,
  previousCodexModelProvider,
} = {}, ports = {}) {
  if (!object(leaseReply?.account) || !object(leaseReply?.lease)) return null;
  const current = readCloudAccountsState({ env }, ports);
  const acc = leaseReply.account, lease = leaseReply.lease;
  const prev = current.active?.[acc.provider];
  const nowIso = new Date((ports.now ?? Date.now)()).toISOString();
  const explicitRefreshAt = acc.last_refresh_at ?? acc.refreshed_at ?? lease.last_refresh_at ?? lease.codex_auth_json?.last_refresh ?? null;
  const lastRefreshAt = explicitRefreshAt ?? (prev?.account_id === acc.account_id ? prev?.last_refresh_at : null) ?? null;
  const accessTokenExpiresAt = acc.access_token_expires_at ?? lease.access_token_expires_at ?? extractJwtExpiresAtIso(lease.codex_auth_json?.tokens?.access_token) ?? null;
  const stillLocallyRevoked = isLocalReauthUnresolved(acc.account_id, explicitRefreshAt, current.reauth);
  const accountState = (isReauthRequiredAccount(acc) || stillLocallyRevoked) ? 'reauth_required' : (typeof acc.state === 'string' && acc.state ? acc.state : 'ready');
  const isMaterializedLocal = materializedLocal !== undefined
    ? Boolean(materializedLocal)
    : Boolean(prev?.account_id === acc.account_id && prev?.lease_id && prev.lease_id === lease.lease_id && prev.materialized_local === true);
  const nextActive = {
    ...current.active,
    [acc.provider]: {
      account_id: acc.account_id,
      label: acc.label ?? acc.account_id,
      provider: acc.provider,
      is_owner: typeof acc.is_owner === 'boolean' ? acc.is_owner : (acc.shared === true ? false : (prev?.account_id === acc.account_id ? (prev?.is_owner ?? null) : null)),
      state: accountState,
      lease_id: lease.lease_id ?? null,
      leased_at: lease.leased_at ?? nowIso,
      expires_at: lease.expires_at ?? null,
      last_refresh_at: typeof lastRefreshAt === 'string' ? lastRefreshAt : null,
      access_token_expires_at: typeof accessTokenExpiresAt === 'string' ? accessTokenExpiresAt : null,
      materialized_local: isMaterializedLocal,
      delivery_mode: lease.delivery_mode ?? null,
      anthropic_base_url: lease.anthropic_base_url ?? null,
      managed_anthropic_base_url: managedBaseUrl !== undefined ? Boolean(managedBaseUrl) : Boolean(prev?.managed_anthropic_base_url),
      codex_gateway_url: codexGatewayUrl !== undefined ? codexGatewayUrl : (lease.codex_gateway_url ?? prev?.codex_gateway_url ?? null),
      codex_backend_api_url: lease.codex_backend_api_url ?? prev?.codex_backend_api_url ?? null,
      auto_rotate: typeof lease.auto_rotate === 'boolean' ? lease.auto_rotate : (prev?.auto_rotate ?? null),
      managed_codex_gateway: managedCodexGateway !== undefined ? Boolean(managedCodexGateway) : Boolean(prev?.managed_codex_gateway),
      previous_codex_model_provider: previousCodexModelProvider !== undefined ? previousCodexModelProvider : (prev?.previous_codex_model_provider ?? null),
      five_hour_used_percent: typeof acc.five_hour_used_percent === 'number' ? acc.five_hour_used_percent : null,
      five_hour_reset_at: acc.five_hour_reset_at ?? null,
      weekly_used_percent: typeof acc.weekly_used_percent === 'number' ? acc.weekly_used_percent : null,
      weekly_reset_at: acc.weekly_reset_at ?? null,
    },
  };
  const nextCooling = { ...current.cooling };
  delete nextCooling[acc.provider];
  const nextReauth = { ...(current.reauth ?? {}) };
  if (accountState !== 'reauth_required' && acc.account_id) delete nextReauth[acc.account_id];
  return writeCloudAccountsState({
    enrolled: true,
    providers: [...new Set([...current.providers, acc.provider])],
    active: nextActive,
    cooling: nextCooling,
    reauth: nextReauth,
  }, { env }, ports);
}
