// Generated from prompts/cli/login-pool.prompt.md (sha256: bf30fa34fabafa4c20edf0b286208194cb36df386538849510cce56a2239e46c).
import * as nativeFs from 'node:fs';
import { hostname as osHostname, homedir, tmpdir } from 'node:os';
import { dirname, isAbsolute, join, resolve } from 'node:path';
import { randomBytes, randomUUID } from 'node:crypto';
import { parseAgentAuthStatus, runAgentProcess } from './agent-adapters.mjs';
import * as codexLimitsModule from './codex-limits.mjs';
import { knownSecretValues, redactSecrets, rememberSecrets } from './secret-redaction.mjs';
import { parse as parseToml } from './vendor/smol-toml/parse.js';
import { checkWorkflowAgents } from './workflow-agents.mjs';

const readCodexLimits = (...args) => codexLimitsModule.readCodexLimits(...args);
export const readCodexUsageWindows = (...args) => (codexLimitsModule.readCodexUsageWindows ?? codexLimitsModule.readCodexLimits)(...args);

const KINDS = ['codex', 'claude', 'gemini', 'agy'];
const CLOUD_PROVIDERS = ['codex', 'claude'];
const CONFIG_VAR = Object.freeze({
  codex: 'CODEX_HOME',
  claude: 'CLAUDE_CONFIG_DIR',
  gemini: 'GEMINI_CLI_HOME',
  agy: 'ANTIGRAVITY_APP_DATA_DIR',
});
const FOLDER_KEY = Object.freeze({
  codex: 'codexHome',
  claude: 'claudeConfigDir',
  gemini: 'geminiCliHome',
  agy: 'appDataDir',
});
const ALL_CONFIG_VARS = Object.values(CONFIG_VAR);
const ALL_FOLDER_KEYS = [...Object.values(FOLDER_KEY), 'configHome'];
const ENTRY_KEYS = new Set(['id', 'kind', 'command', 'model', 'plan', 'credits', 'allowReset', 'allow_reset', 'paused', ...ALL_FOLDER_KEYS, 'env']);
const TOP_KEYS = new Set(['reset', 'weeklyStopPercent', 'logins']);
const CONTROLS = /[\u0000-\u001f\u007f-\u009f]/;
const SECRET_ENV_KEY = /(?:_TOKEN|_SECRET|_API_KEY|_PASSWORD|_CREDENTIAL|^SECRET_|API_KEY$|^OPENAI_API_KEY$|^ANTHROPIC_API_KEY$|^GEMINI_API_KEY$|^GOOGLE_API_KEY$|^CLAUDE_CODE_OAUTH_TOKEN$|^CODEX_ACCESS_TOKEN$)/i;
const CODEX_OVERLAY_LINKS = ['config.toml', 'skills', 'memories', 'sessions', 'rules'];
const CODEX_GATEWAY_OVERLAY_LINKS = ['skills', 'memories', 'sessions', 'rules'];
const MANAGED_CODEX_HOME_LINKS = ['skills', 'memories', 'sessions', 'archived_sessions', 'history.jsonl', 'session_index.jsonl', 'rules'];
const CODEX_GATEWAY_PROVIDER_ID = 'pdd_codex_gateway';
const INLINE_TOML_TABLE_KEYS = new Set(['http_headers', 'env_http_headers', 'filters', 'set']);
const MANAGED_CLAUDE_GATEWAY_RE = /\/v1\/(?:accounts\/)?claude-gateway(?:\/|$)/;
const REAUTH_CODE_RE = /\b(?:reauth_required|needs_reauth|token_revoked|invalid_grant|refresh_token_reused|refresh_token_expired|oauth_token_revoked)\b/i;
const REAUTH_TEXT_RE = /\b(?:reauth_required|needs_reauth|token_revoked|invalid_grant|refresh_token_reused|refresh_token_expired|oauth_token_revoked)\b|(?:status|http|error)[:=\s]+401\b|\b401\s+unauthorized\b/i;
export const DEFAULT_CLOUD_URL = 'https://pdd-byok-api-c437voydwa-uc.a.run.app';
export const POOL_FALLBACK_COOLDOWN_MS = 30 * 60 * 1000;

const activeOverlayCleanups = new Set();
let overlayHooksAttached = false;

export function sweepActiveCodexOverlays() {
  for (const fn of [...activeOverlayCleanups]) {
    try { fn(); } catch {}
  }
}

function onOverlaySignal(signal) {
  const otherListeners = process.listenerCount(signal) > 1;
  sweepActiveCodexOverlays();
  if (!otherListeners) {
    process.exit(signal === 'SIGINT' ? 130 : 143);
  }
}
const onOverlaySigint = () => onOverlaySignal('SIGINT');
const onOverlaySigterm = () => onOverlaySignal('SIGTERM');

function syncOverlayHooks() {
  if (activeOverlayCleanups.size > 0 && !overlayHooksAttached) {
    overlayHooksAttached = true;
    process.on('exit', sweepActiveCodexOverlays);
    process.on('SIGINT', onOverlaySigint);
    process.on('SIGTERM', onOverlaySigterm);
  } else if (activeOverlayCleanups.size === 0 && overlayHooksAttached) {
    overlayHooksAttached = false;
    process.off('exit', sweepActiveCodexOverlays);
    process.off('SIGINT', onOverlaySigint);
    process.off('SIGTERM', onOverlaySigterm);
  }
}

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);
const bad = message => { throw new Error(`Invalid login pool: ${message}`); };

export class CloudAccountsError extends Error {
  constructor(message, { status = 0, code = 'cloud_accounts_error', payload = null } = {}) {
    super(redactSecrets(String(message ?? 'Cloud accounts request failed.')));
    this.name = 'CloudAccountsError';
    this.status = status;
    this.code = code;
    this.payload = payload;
  }
}

function writeAtomicPrivate(fs, target, text, dirMode = 0o700) {
  fs.mkdirSync(dirname(target), { recursive: true, mode: dirMode });
  const tmp = `${target}.${process.pid}.${randomUUID()}.tmp`;
  fs.writeFileSync(tmp, text, { mode: 0o600 });
  try { fs.chmodSync?.(tmp, 0o600); } catch {}
  fs.renameSync(tmp, target);
  try { fs.chmodSync?.(target, 0o600); } catch {}
}

function readJsonObject(fs, file) {
  try {
    const parsed = JSON.parse(fs.readFileSync(file, 'utf8'));
    return object(parsed) ? parsed : null;
  } catch {
    return null;
  }
}

function extractJwtExpiresAtIso(jwt) {
  if (typeof jwt !== 'string' || !jwt.trim()) return null;
  const parts = jwt.split('.');
  if (parts.length < 2) return null;
  try {
    const payload = JSON.parse(Buffer.from(parts[1], 'base64url').toString('utf8'));
    if (typeof payload?.exp === 'number' && Number.isFinite(payload.exp) && payload.exp > 0) {
      return new Date(payload.exp * 1000).toISOString();
    }
  } catch {}
  return null;
}

export function isReauthRequiredAccount(entry) {
  if (!object(entry)) return false;
  const state = String(entry.state ?? '').trim().toLowerCase();
  if (state === 'reauth_required' || state === 'needs_reauth' || entry.needs_reauth === true) return true;
  const errFields = [entry.last_refresh_error, entry.auth_error, entry.error_code, entry.reason]
    .filter(v => typeof v === 'string' && v.trim())
    .join(' ');
  return Boolean(errFields && (REAUTH_CODE_RE.test(errFields) || /\b401\b|unauthorized/i.test(errFields)));
}

export function isLocalReauthUnresolved(accountId, refreshedAtIso, reauthMap) {
  if (!accountId || !object(reauthMap) || !object(reauthMap[accountId])) return false;
  const mark = reauthMap[accountId];
  const markedMs = mark.marked_at ? Date.parse(mark.marked_at) : NaN;
  const refreshedMs = refreshedAtIso ? Date.parse(refreshedAtIso) : NaN;
  return !Number.isFinite(markedMs) || !Number.isFinite(refreshedMs) || refreshedMs <= markedMs;
}

export function isReauthRequiredFailure(errorOrText) {
  if (!errorOrText) return false;
  if (typeof errorOrText === 'string') {
    return REAUTH_TEXT_RE.test(errorOrText);
  }
  if (typeof errorOrText === 'object') {
    if (errorOrText.code === 'missing_auth_token') return false;
    const code = String(errorOrText.code ?? '');
    if (REAUTH_CODE_RE.test(code)) return true;
    const reason = String(errorOrText.payload?.reason ?? errorOrText.payload?.state ?? errorOrText.reason ?? '');
    if (REAUTH_CODE_RE.test(reason)) return true;
    const msg = String(errorOrText.message ?? '');
    if (REAUTH_CODE_RE.test(msg)) return true;
    if (object(errorOrText.payload) && REAUTH_CODE_RE.test(JSON.stringify(errorOrText.payload))) {
      return true;
    }
    const hasAccountContext = Boolean(
      errorOrText.payload?.account_id
      || errorOrText.payload?.detail?.account_id
      || errorOrText.payload?.account?.account_id,
    );
    if (errorOrText.status === 401 && hasAccountContext) {
      return true;
    }
  }
  return false;
}

export function resolveCloudAccountsEndpoint(env = process.env) {
  const raw = String(env?.PDD_ACCOUNTS_URL || env?.PDD_CLOUD_URL || DEFAULT_CLOUD_URL).trim().replace(/\/+$/, '');
  let parsed;
  try { parsed = new URL(raw); } catch { throw new CloudAccountsError('Invalid Cloud Accounts URL.', { code: 'invalid_url' }); }
  if (parsed.username || parsed.password) {
    throw new CloudAccountsError('Cloud Accounts URL must not include embedded credentials.', { code: 'invalid_url' });
  }
  const loopback = ['127.0.0.1', 'localhost', '[::1]', '::1'].includes(parsed.hostname.toLowerCase());
  if (parsed.protocol !== 'https:' && !(parsed.protocol === 'http:' && loopback)) {
    throw new CloudAccountsError('Cloud Accounts requires an https:// endpoint.', { code: 'insecure_url' });
  }
  return raw;
}

export async function resolveCloudAccountsToken({ cwd = process.cwd(), env = process.env, timeoutMs = 10_000 } = {}, ports = {}) {
  for (const key of ['PDD_TOKEN', 'PDD_ACCOUNTS_TOKEN', 'GH_TOKEN', 'GITHUB_TOKEN']) {
    const val = typeof env?.[key] === 'string' ? env[key].trim() : '';
    if (val) {
      rememberSecrets(val);
      return val;
    }
  }
  if (typeof ports.authToken === 'function') {
    const tok = String((await ports.authToken({ cwd, env })) ?? '').trim();
    if (tok) { rememberSecrets(tok); return tok; }
  }
  try {
    const run = ports.run ?? runAgentProcess;
    const res = await run('gh', ['auth', 'token'], { cwd, env, input: '', timeoutMs: Math.min(timeoutMs, 10_000), maxBytes: 4096 });
    const tok = res?.code === 0 && typeof res.stdout === 'string' ? res.stdout.trim() : '';
    if (tok) {
      rememberSecrets(tok);
      return tok;
    }
  } catch {}
  throw new CloudAccountsError('Sign in with gh auth login or set PDD_TOKEN before using Cloud Accounts.', { code: 'missing_auth_token' });
}

function resolveMachineIdentity(env = process.env, ports = {}) {
  const rawHost = typeof ports.hostname === 'function' ? ports.hostname() : osHostname();
  const clean = value => String(value ?? '').replace(/[^\x21-\x7e]/g, '-').slice(0, 80) || 'local';
  return {
    machineId: clean(env?.PDD_MACHINE_ID || rawHost),
    machineLabel: clean(env?.PDD_MACHINE_LABEL || rawHost),
  };
}

function rememberLeaseSecrets(payload) {
  if (!object(payload)) return;
  rememberSecrets(...knownSecretValues(payload));
  const lease = payload.lease;
  if (object(lease)) {
    for (const key of ['claude_oauth_token', 'codex_gateway_token', 'gateway_bearer_token']) {
      if (typeof lease[key] === 'string' && lease[key]) rememberSecrets(lease[key]);
    }
    if (object(lease.codex_auth_json?.tokens)) {
      for (const val of Object.values(lease.codex_auth_json.tokens)) {
        if (typeof val === 'string' && val.length >= 8) rememberSecrets(val);
      }
    }
  }
}

function extractCloudErrorInfo(parsed, status) {
  if (!object(parsed)) return { code: `http_${status}`, message: `HTTP ${status}`, payload: parsed };
  const detail = parsed.detail;
  let code = '';
  let message = '';
  if (object(detail)) {
    code = String(detail.error?.code || (typeof detail.error === 'string' ? detail.error : '') || detail.code || '');
    message = String(detail.message || detail.error?.message || (typeof detail.error === 'string' ? detail.error : '') || '');
  } else if (typeof detail === 'string' && detail.trim()) {
    message = detail.trim();
  } else if (Array.isArray(detail) && detail.length) {
    const msgs = detail.map(item => (object(item) && typeof item.msg === 'string' ? item.msg : '')).filter(Boolean);
    if (msgs.length) {
      code = 'validation_error';
      message = msgs.join('; ');
    }
  }
  if (!code) {
    code = String(parsed.error?.code || (typeof parsed.error === 'string' ? parsed.error : '') || parsed.code || '');
  }
  if (!message) {
    message = String(parsed.error?.message || parsed.message || (typeof parsed.error === 'string' ? parsed.error : '') || '');
  }
  const payload = object(detail) ? { ...parsed, ...detail } : parsed;
  return {
    code: code || `http_${status}`,
    message: message || `HTTP ${status}`,
    payload,
  };
}

export async function cloudAccountsRequest(method, path, { body, cwd = process.cwd(), env = process.env, timeoutMs = 20_000, maxRetries, deadlineMs } = {}, ports = {}) {
  const nowFn = ports.now ?? Date.now;
  const upperMethod = String(method ?? 'GET').toUpperCase();
  const normalizedPath = path.startsWith('/') ? path : `/${path}`;
  const pathnameOnly = normalizedPath.split('?')[0];
  const isIdempotentRetryable = upperMethod === 'GET' || (upperMethod === 'POST' && pathnameOnly === '/v1/accounts/lease');
  const retries = maxRetries !== undefined
    ? Math.max(0, Math.trunc(Number(maxRetries) || 0))
    : (isIdempotentRetryable ? 1 : 0);

  const totalLimit = typeof timeoutMs === 'number' && Number.isFinite(timeoutMs) && timeoutMs > 0 ? timeoutMs : 20_000;
  const effectiveDeadline = typeof deadlineMs === 'number' && Number.isFinite(deadlineMs)
    ? deadlineMs
    : (nowFn() + totalLimit);

  const baseUrl = resolveCloudAccountsEndpoint(env);
  const tokenBudget = effectiveDeadline - nowFn();
  if (tokenBudget <= 0) throw new CloudAccountsError('Cloud Accounts request timed out.', { code: 'timeout' });
  const token = await resolveCloudAccountsToken({ cwd, env, timeoutMs: Math.min(tokenBudget, 10_000) }, ports);
  const { machineId } = resolveMachineIdentity(env, ports);
  const fetchImpl = ports.fetch ?? globalThis.fetch;
  if (typeof fetchImpl !== 'function') throw new CloudAccountsError('HTTP fetch is unavailable.', { code: 'fetch_unavailable' });
  if (body !== undefined) rememberSecrets(...knownSecretValues(body));
  const serializedBody = body !== undefined ? JSON.stringify(body) : undefined;
  const headers = {
    Authorization: `Bearer ${token}`,
    'X-PDD-Machine-Id': machineId,
    Accept: 'application/json',
    ...(serializedBody !== undefined ? { 'Content-Type': 'application/json' } : {}),
  };

  for (let attempt = 0; attempt <= retries; attempt += 1) {
    const remainingMs = effectiveDeadline - nowFn();
    if (remainingMs <= 0) {
      throw new CloudAccountsError('Cloud Accounts request timed out.', { code: 'timeout' });
    }
    const attemptLimit = attempt < retries
      ? Math.max(1, Math.ceil(remainingMs * 0.65))
      : Math.max(1, remainingMs);
    const controller = new AbortController();
    const timer = setTimeout(() => controller.abort(new Error('timeout')), attemptLimit);
    try {
      const response = await fetchImpl(`${baseUrl}${normalizedPath}`, {
        method: upperMethod,
        headers,
        ...(serializedBody !== undefined ? { body: serializedBody } : {}),
        signal: controller.signal,
      });
      const rawText = await response.text();
      let parsed = null;
      if (rawText.trim()) {
        try { parsed = JSON.parse(rawText); } catch { parsed = null; }
      }
      if (parsed) rememberLeaseSecrets(parsed);
      if (!response.ok) {
        const info = extractCloudErrorInfo(parsed, response.status);
        throw new CloudAccountsError(`Cloud Accounts ${upperMethod} ${path} failed (${response.status}): ${info.message}`, {
          status: response.status,
          code: String(info.code),
          payload: info.payload,
        });
      }
      return parsed ?? {};
    } catch (error) {
      if (error instanceof CloudAccountsError) throw error;
      const timedOut = error?.name === 'AbortError' || error?.name === 'TimeoutError' || /timed?\s*out|aborted/i.test(String(error?.message ?? ''));
      if (timedOut && isIdempotentRetryable && attempt < retries && (effectiveDeadline - nowFn()) > 0) {
        continue;
      }
      throw new CloudAccountsError(timedOut ? 'Cloud Accounts request timed out.' : `Cloud Accounts unreachable: ${error?.message ?? 'network error'}`, {
        code: timedOut ? 'timeout' : 'network_error',
      });
    } finally {
      clearTimeout(timer);
    }
  }
  throw new CloudAccountsError('Cloud Accounts request timed out.', { code: 'timeout' });
}

export async function listCloudAccounts({ refresh = false, cwd = process.cwd(), env = process.env, timeoutMs = 30_000, maxRetries } = {}, ports = {}) {
  const path = refresh === true ? '/v1/accounts?refresh=true' : '/v1/accounts';
  return cloudAccountsRequest('GET', path, { cwd, env, timeoutMs, maxRetries }, ports);
}

function resolvePddStateBase(env = process.env) {
  const home = env?.HOME || homedir();
  return (typeof env?.PDD_STATE_DIR === 'string' && env.PDD_STATE_DIR.trim())
    ? env.PDD_STATE_DIR.trim()
    : (typeof env?.XDG_STATE_HOME === 'string' && env.XDG_STATE_HOME.trim())
      ? join(env.XDG_STATE_HOME.trim(), 'pdd')
      : join(home, '.local', 'state', 'pdd');
}

export function accountsStatePath(env = process.env) {
  return join(resolvePddStateBase(env), 'accounts-state.json');
}

export function pddManagedCodexHome(env = process.env) {
  return join(resolvePddStateBase(env), 'codex-home');
}

export function managedCodexAuthPath(env = process.env) {
  return join(pddManagedCodexHome(env), 'auth.json');
}

export function managedCodexConfigPath(env = process.env) {
  return join(pddManagedCodexHome(env), 'config.toml');
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
        active[provider] = {
          account_id: entry.account_id,
          label: typeof entry.label === 'string' ? entry.label : entry.account_id,
          provider,
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
          managed_codex_gateway: entry.managed_codex_gateway === true,
          previous_codex_model_provider: typeof entry.previous_codex_model_provider === 'string' && entry.previous_codex_model_provider ? entry.previous_codex_model_provider : null,
          five_hour_used_percent: typeof entry.five_hour_used_percent === 'number' && Number.isFinite(entry.five_hour_used_percent) ? entry.five_hour_used_percent : null,
          five_hour_reset_at: typeof entry.five_hour_reset_at === 'string' ? entry.five_hour_reset_at : null,
          weekly_used_percent: typeof entry.weekly_used_percent === 'number' && Number.isFinite(entry.weekly_used_percent) ? entry.weekly_used_percent : null,
          weekly_reset_at: typeof entry.weekly_reset_at === 'string' ? entry.weekly_reset_at : null,
        };
      }
    }
  }
  const providers = Array.isArray(raw.providers) ? raw.providers.filter(p => CLOUD_PROVIDERS.includes(p)) : Object.keys(active);
  const cooling = object(raw.cooling) ? raw.cooling : {};
  const reauth = {};
  if (object(raw.reauth)) {
    for (const [accId, meta] of Object.entries(raw.reauth)) {
      if (accId && object(meta)) {
        reauth[accId] = { marked_at: typeof meta.marked_at === 'string' ? meta.marked_at : null };
      }
    }
  }
  return {
    enrolled: raw.enrolled === true,
    providers: [...new Set([...providers, ...Object.keys(active)])],
    active,
    cooling,
    reauth,
  };
}

export function writeCloudAccountsState(state, { env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const active = {};
  for (const provider of CLOUD_PROVIDERS) {
    const entry = state?.active?.[provider];
    if (object(entry) && typeof entry.account_id === 'string' && entry.account_id) {
      active[provider] = {
        account_id: entry.account_id,
        label: String(entry.label ?? entry.account_id),
        provider,
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
        managed_codex_gateway: entry.managed_codex_gateway === true,
        previous_codex_model_provider: typeof entry.previous_codex_model_provider === 'string' && entry.previous_codex_model_provider ? entry.previous_codex_model_provider : null,
        five_hour_used_percent: typeof entry.five_hour_used_percent === 'number' && Number.isFinite(entry.five_hour_used_percent) ? entry.five_hour_used_percent : null,
        five_hour_reset_at: typeof entry.five_hour_reset_at === 'string' ? entry.five_hour_reset_at : null,
        weekly_used_percent: typeof entry.weekly_used_percent === 'number' && Number.isFinite(entry.weekly_used_percent) ? entry.weekly_used_percent : null,
        weekly_reset_at: typeof entry.weekly_reset_at === 'string' ? entry.weekly_reset_at : null,
      };
    }
  }
  const providers = [...new Set([...(Array.isArray(state?.providers) ? state.providers.filter(p => CLOUD_PROVIDERS.includes(p)) : []), ...Object.keys(active)])];
  const enrolled = state?.enrolled === true;
  const sourceReauth = state?.reauth !== undefined
    ? state.reauth
    : (enrolled || providers.length > 0 ? readCloudAccountsState({ env }, ports).reauth : {});
  const reauth = {};
  if (object(sourceReauth)) {
    for (const [accId, meta] of Object.entries(sourceReauth)) {
      if (accId && object(meta)) {
        reauth[accId] = { marked_at: typeof meta.marked_at === 'string' ? meta.marked_at : null };
      }
    }
  }
  const payload = {
    enrolled: state?.enrolled === true,
    updated_at: new Date((ports.now ?? Date.now)()).toISOString(),
    providers,
    active,
    cooling: object(state?.cooling) ? state.cooling : {},
    ...(Object.keys(reauth).length > 0 ? { reauth } : {}),
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
  const nextReauth = { ...(saved.reauth ?? {}), [accountId]: { marked_at: nowIso } };
  return writeCloudAccountsState({ ...saved, active: nextActive, reauth: nextReauth }, { env }, ports);
}

export function isCloudAccountsActive({ env = process.env, poolPath, provider } = {}, ports = {}) {
  if (typeof poolPath === 'string' && poolPath.trim()) return false;
  if (provider !== undefined && provider !== null && !CLOUD_PROVIDERS.includes(provider)) return false;
  const saved = readCloudAccountsState({ env }, ports);
  if (!saved.enrolled) return false;
  if (provider !== undefined && provider !== null && Array.isArray(saved.providers)) {
    return saved.providers.includes(provider);
  }
  return saved.providers.length > 0 || Object.keys(saved.active ?? {}).length > 0;
}

export function stripCodexAuthBundle(authJson) {
  const tokens = object(authJson?.tokens) ? authJson.tokens : {};
  rememberSecrets(...knownSecretValues(authJson));
  for (const val of Object.values(tokens)) {
    if (typeof val === 'string' && val.length >= 8) rememberSecrets(val);
  }
  const hasOauth = Boolean(
    (typeof tokens.access_token === 'string' && tokens.access_token.trim())
    || (typeof tokens.id_token === 'string' && tokens.id_token.trim()),
  );
  const authMode = typeof authJson?.auth_mode === 'string' && authJson.auth_mode.trim()
    ? authJson.auth_mode.trim()
    : (hasOauth ? 'chatgpt' : undefined);
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
  const managed = pddManagedCodexHome(env);
  if (resolve(explicit) === resolve(managed)) return defaultHome;
  try {
    if (nativeFs.realpathSync(explicit) === nativeFs.realpathSync(managed)) return defaultHome;
  } catch {}
  return explicit;
}

export function localCodexAuthPath(env = process.env) {
  return join(localCodexHome(env), 'auth.json');
}

export function localCodexConfigPath(env = process.env) {
  return join(localCodexHome(env), 'config.toml');
}

function assertNoSymlinkCodexPath(fs, targetPath) {
  const lstat = typeof fs?.lstatSync === 'function' ? fs.lstatSync.bind(fs) : (fs === nativeFs ? nativeFs.lstatSync : null);
  if (!lstat) return;
  const parentDir = dirname(targetPath);
  try {
    const dirStat = lstat(parentDir);
    if (dirStat.isSymbolicLink() || !dirStat.isDirectory()) {
      throw new CloudAccountsError(`Refusing symlink or non-directory Codex folder at ${parentDir}.`, { code: 'symlink_refused' });
    }
  } catch (error) {
    if (error instanceof CloudAccountsError) throw error;
    if (error?.code !== 'ENOENT') throw error;
  }
  try {
    const fileStat = lstat(targetPath);
    if (fileStat.isSymbolicLink() || !fileStat.isFile()) {
      throw new CloudAccountsError(`Refusing symlink or non-regular Codex file at ${targetPath}.`, { code: 'symlink_refused' });
    }
  } catch (error) {
    if (error instanceof CloudAccountsError) throw error;
    if (error?.code !== 'ENOENT') throw error;
  }
}

function validateCodexGatewayUrl(rawUrl) {
  const raw = String(rawUrl ?? '').trim().replace(/\/+$/, '');
  if (!raw) throw new CloudAccountsError('Cloud lease returned no Codex gateway URL.', { code: 'invalid_lease' });
  let parsed;
  try { parsed = new URL(raw); } catch { throw new CloudAccountsError('Invalid Codex gateway URL in Cloud lease.', { code: 'invalid_lease' }); }
  if (parsed.username || parsed.password) {
    throw new CloudAccountsError('Codex gateway URL must not include embedded credentials.', { code: 'invalid_lease' });
  }
  const loopback = ['127.0.0.1', 'localhost', '[::1]', '::1'].includes(parsed.hostname.toLowerCase());
  if (parsed.protocol !== 'https:' && !(parsed.protocol === 'http:' && loopback)) {
    throw new CloudAccountsError('Codex gateway URL requires https://.', { code: 'invalid_lease' });
  }
  return raw;
}

function resolveCodexGatewayGrant(lease) {
  const token = String(lease?.codex_gateway_token || lease?.gateway_bearer_token || '').trim();
  if (!token) throw new CloudAccountsError('Cloud lease returned no Codex gateway token.', { code: 'invalid_lease' });
  rememberSecrets(token);
  if (!token.startsWith('pddg_')) {
    throw new CloudAccountsError('Codex gateway token must start with pddg_.', { code: 'invalid_lease' });
  }
  return token;
}

const isTomlTable = value => value !== null && typeof value === 'object' && !Array.isArray(value) && !(value instanceof Date) && typeof value.toISOString !== 'function';
const formatTomlKey = key => (/^[A-Za-z0-9_-]+$/.test(key) ? key : JSON.stringify(key));

function formatTomlValue(value) {
  if (typeof value === 'string') return JSON.stringify(value);
  if (typeof value === 'boolean') return value ? 'true' : 'false';
  if (typeof value === 'bigint') return String(value);
  if (typeof value === 'number') {
    if (Number.isFinite(value)) return String(value);
    if (Number.isNaN(value)) return 'nan';
    return value > 0 ? 'inf' : '-inf';
  }
  if (value instanceof Date || typeof value?.toISOString === 'function') return value.toISOString();
  if (Array.isArray(value)) return `[${value.map(formatTomlValue).join(', ')}]`;
  if (isTomlTable(value)) {
    const pairs = Object.entries(value)
      .filter(([, v]) => v !== undefined && v !== null)
      .map(([k, v]) => `${formatTomlKey(k)} = ${formatTomlValue(v)}`);
    return pairs.length ? `{ ${pairs.join(', ')} }` : '{}';
  }
  return JSON.stringify(String(value));
}

function isInlineLeafMap(key, value, depth) {
  return depth >= 1
    && INLINE_TOML_TABLE_KEYS.has(key)
    && isTomlTable(value)
    && Object.values(value).every(v => v === undefined || v === null || (!isTomlTable(v) && !Array.isArray(v)));
}

function serializeTomlConfig(root, fileLabel = 'config.toml') {
  const blocks = [];
  const visit = (table, path) => {
    const scalars = [];
    const subtables = [];
    const tableArrays = [];
    for (const [key, val] of Object.entries(table)) {
      if (val === undefined || val === null) continue;
      if (Array.isArray(val) && val.length > 0 && val.every(isTomlTable)) {
        tableArrays.push([key, val]);
      } else if (isTomlTable(val) && !isInlineLeafMap(key, val, path.length)) {
        subtables.push([key, val]);
      } else {
        scalars.push([key, val]);
      }
    }
    if (path.length === 0) {
      if (scalars.length > 0) {
        blocks.push(scalars.map(([k, v]) => `${formatTomlKey(k)} = ${formatTomlValue(v)}`).join('\n'));
      }
    } else if (scalars.length > 0 || (subtables.length === 0 && tableArrays.length === 0)) {
      const header = `[${path.map(formatTomlKey).join('.')}]`;
      const lines = scalars.map(([k, v]) => `${formatTomlKey(k)} = ${formatTomlValue(v)}`);
      blocks.push([header, ...lines].join('\n'));
    }
    for (const [key, sub] of subtables) {
      visit(sub, [...path, key]);
    }
    for (const [key, list] of tableArrays) {
      const arrPath = [...path, key];
      const header = `[[${arrPath.map(formatTomlKey).join('.')}]]`;
      for (const item of list) {
        const itemScalars = [];
        const itemSubs = [];
        for (const [ik, iv] of Object.entries(item)) {
          if (iv === undefined || iv === null) continue;
          if (isTomlTable(iv) && !isInlineLeafMap(ik, iv, arrPath.length)) itemSubs.push([ik, iv]);
          else itemScalars.push([ik, iv]);
        }
        blocks.push([header, ...itemScalars.map(([k, v]) => `${formatTomlKey(k)} = ${formatTomlValue(v)}`)].join('\n'));
        for (const [sk, sv] of itemSubs) visit(sv, [...arrPath, sk]);
      }
    }
  };
  visit(root, []);
  const text = blocks.length ? `${blocks.join('\n\n')}\n` : '';
  try {
    parseToml(text);
  } catch {
    throw new CloudAccountsError(`Failed to serialize valid TOML for ${fileLabel}.`, { code: 'invalid_codex_config' });
  }
  return text;
}

function readCodexTomlObject(fs, configPath, { strict = true } = {}) {
  let raw;
  try {
    raw = fs.readFileSync(configPath, 'utf8');
  } catch (error) {
    if (error?.code === 'ENOENT') return { exists: false, data: {} };
    if (!strict) return { exists: false, data: {} };
    throw error;
  }
  try {
    const parsed = parseToml(raw);
    return { exists: true, data: isTomlTable(parsed) ? parsed : {} };
  } catch {
    if (!strict) return { exists: true, data: {} };
    throw new CloudAccountsError(`${configPath} contains malformed TOML; fix it before updating Codex Cloud accounts.`, { code: 'invalid_codex_config' });
  }
}

export function localClaudePaths(env = process.env) {
  const home = env?.HOME || homedir();
  const claudeDir = (typeof env?.CLAUDE_CONFIG_DIR === 'string' && env.CLAUDE_CONFIG_DIR.trim()) ? env.CLAUDE_CONFIG_DIR.trim() : join(home, '.claude');
  return {
    settingsPath: join(claudeDir, 'settings.json'),
    onboardingPath: join(home, '.claude.json'),
  };
}

function stripGatewayFromTomlObject(configData, previousModelProvider = null) {
  const hasGatewaySection = isTomlTable(configData?.model_providers) && Object.hasOwn(configData.model_providers, CODEX_GATEWAY_PROVIDER_ID);
  const hasGatewayProvider = configData?.model_provider === CODEX_GATEWAY_PROVIDER_ID;
  const nextData = { ...(isTomlTable(configData) ? configData : {}) };
  if (isTomlTable(nextData.model_providers)) {
    const nextProviders = { ...nextData.model_providers };
    delete nextProviders[CODEX_GATEWAY_PROVIDER_ID];
    if (Object.keys(nextProviders).length > 0) nextData.model_providers = nextProviders;
    else delete nextData.model_providers;
  }
  if (nextData.model_provider === CODEX_GATEWAY_PROVIDER_ID) {
    if (typeof previousModelProvider === 'string' && previousModelProvider.trim() && previousModelProvider.trim() !== CODEX_GATEWAY_PROVIDER_ID) {
      nextData.model_provider = previousModelProvider.trim();
    } else {
      delete nextData.model_provider;
    }
  }
  return { changed: hasGatewaySection || hasGatewayProvider, nextData };
}

function syncManagedCodexHomeLinks(fs, sourceHome, managedHome) {
  fs.mkdirSync(managedHome, { recursive: true, mode: 0o700 });
  try { (fs.chmodSync ?? nativeFs.chmodSync)?.(managedHome, 0o700); } catch {}
  if (resolve(sourceHome) === resolve(managedHome)) return;
  const lstat = typeof fs?.lstatSync === 'function' ? fs.lstatSync.bind(fs) : (fs === nativeFs ? nativeFs.lstatSync : null);
  const symlink = typeof fs?.symlinkSync === 'function' ? fs.symlinkSync.bind(fs) : null;
  if (!lstat || !symlink) return;
  const removeLink = dst => {
    try {
      if (typeof fs.unlinkSync === 'function') fs.unlinkSync(dst);
      else fs.rmSync?.(dst, { force: true });
    } catch {}
  };
  for (const name of MANAGED_CODEX_HOME_LINKS) {
    const src = join(sourceHome, name);
    const dst = join(managedHome, name);
    let srcValid = false;
    try {
      const srcStat = lstat(src);
      srcValid = !srcStat.isSymbolicLink();
    } catch {}
    if (srcValid) {
      let dstStat = null;
      try { dstStat = lstat(dst); } catch {}
      if (!dstStat) {
        try { symlink(src, dst); } catch {}
      } else if (dstStat.isSymbolicLink()) {
        let currentTarget = null;
        try { currentTarget = fs.readlinkSync?.(dst) ?? null; } catch {}
        if (currentTarget !== src) {
          removeLink(dst);
          try { symlink(src, dst); } catch {}
        }
      }
    } else {
      try {
        const dstStat = lstat(dst);
        if (dstStat.isSymbolicLink()) removeLink(dst);
      } catch {}
    }
  }
}

export function restoreLocalCodexGatewayConfig({ env = process.env, previousModelProvider = null, removeAuthFile = false } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const managedHome = pddManagedCodexHome(env);
  const configPath = managedCodexConfigPath(env);
  const authPath = managedCodexAuthPath(env);
  const userConfigPath = localCodexConfigPath(env);
  let restoredConfig = false;
  let removedAuth = false;

  assertNoSymlinkCodexPath(fs, configPath);
  assertNoSymlinkCodexPath(fs, userConfigPath);

  // Clean up any legacy PDD-managed gateway section in user ~/.codex/config.toml without touching ~/.codex/auth.json.
  const { exists: hasUserConfig, data: userConfigData } = readCodexTomlObject(fs, userConfigPath);
  if (hasUserConfig) {
    const strippedUser = stripGatewayFromTomlObject(userConfigData, previousModelProvider);
    if (strippedUser.changed) {
      const nextUserText = serializeTomlConfig(strippedUser.nextData, userConfigPath);
      writeAtomicPrivate(fs, userConfigPath, nextUserText);
      restoredConfig = true;
    }
  }

  // Update managed PDD CODEX_HOME/config.toml if present.
  const { exists: hasManagedConfig, data: managedConfigData } = readCodexTomlObject(fs, configPath);
  if (hasManagedConfig) {
    const strippedManaged = stripGatewayFromTomlObject(managedConfigData, previousModelProvider);
    if (strippedManaged.changed) {
      const nextManagedData = {
        ...strippedManaged.nextData,
        cli_auth_credentials_store: 'file',
      };
      const nextManagedText = serializeTomlConfig(nextManagedData, configPath);
      writeAtomicPrivate(fs, configPath, nextManagedText);
      restoredConfig = true;
    }
  }

  // Never touch ~/.codex/auth.json; only remove PDD-managed auth.json inside pddManagedCodexHome(env).
  if (removeAuthFile) {
    assertNoSymlinkCodexPath(fs, authPath);
    try {
      const hasManagedAuth = Boolean(fs.statSync?.(authPath)?.isFile());
      if (hasManagedAuth) {
        if (typeof fs.rmSync === 'function') fs.rmSync(authPath, { force: true });
        else fs.unlinkSync?.(authPath);
        removedAuth = true;
      }
    } catch {}
  }

  return { codexHome: managedHome, configPath, authPath, userConfigPath, restoredConfig, removedAuth };
}

function writeAtomicCodexPair(fs, authPath, authText, configPath, configText) {
  let prevAuth = null;
  let prevConfig = null;
  try { prevAuth = fs.readFileSync(authPath, 'utf8'); } catch {}
  try { prevConfig = fs.readFileSync(configPath, 'utf8'); } catch {}
  try {
    writeAtomicPrivate(fs, configPath, configText);
    writeAtomicPrivate(fs, authPath, authText);
  } catch (err) {
    try {
      if (prevConfig !== null) writeAtomicPrivate(fs, configPath, prevConfig);
      else (fs.rmSync ?? nativeFs.rmSync)(configPath, { force: true });
    } catch {}
    try {
      if (prevAuth !== null) writeAtomicPrivate(fs, authPath, prevAuth);
      else (fs.rmSync ?? nativeFs.rmSync)(authPath, { force: true });
    } catch {}
    throw err;
  }
}

export function materializeLocalCodexAuth(authOrLease, { env = process.env, previousManagedCodexGateway = false, previousCodexModelProvider = null } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const managedHome = pddManagedCodexHome(env);
  const authPath = managedCodexAuthPath(env);
  const configPath = managedCodexConfigPath(env);
  const userHome = localCodexHome(env);
  const userConfigPath = localCodexConfigPath(env);

  const isGateway = object(authOrLease) && authOrLease.delivery_mode === 'gateway_grant';
  const gatewayUrl = isGateway ? validateCodexGatewayUrl(authOrLease.codex_gateway_url) : null;
  const grantToken = isGateway ? resolveCodexGatewayGrant(authOrLease) : null;
  const stripped = isGateway ? null : stripCodexAuthBundle(authOrLease);

  assertNoSymlinkCodexPath(fs, authPath);
  assertNoSymlinkCodexPath(fs, configPath);
  assertNoSymlinkCodexPath(fs, userConfigPath);

  const { exists: hasUserConfig, data: rawUserConfig } = readCodexTomlObject(fs, userConfigPath);
  const userCurrentProvider = typeof rawUserConfig.model_provider === 'string' ? rawUserConfig.model_provider.trim() : '';
  const { exists: hasManagedConfig, data: rawManagedConfig } = readCodexTomlObject(fs, configPath, { strict: false });
  const managedCurrentProvider = typeof rawManagedConfig.model_provider === 'string' ? rawManagedConfig.model_provider.trim() : '';

  const fallbackPriorProvider = (userCurrentProvider && userCurrentProvider !== CODEX_GATEWAY_PROVIDER_ID)
    ? userCurrentProvider
    : (managedCurrentProvider && managedCurrentProvider !== CODEX_GATEWAY_PROVIDER_ID)
      ? managedCurrentProvider
      : (typeof previousCodexModelProvider === 'string' && previousCodexModelProvider.trim() && previousCodexModelProvider.trim() !== CODEX_GATEWAY_PROVIDER_ID
          ? previousCodexModelProvider.trim()
          : null);

  // Clean up any legacy PDD-managed gateway section in ~/.codex/config.toml safely (never touching ~/.codex/auth.json).
  const cleanedUser = stripGatewayFromTomlObject(rawUserConfig, fallbackPriorProvider);
  if (hasUserConfig && (cleanedUser.changed || previousManagedCodexGateway)) {
    if (cleanedUser.changed) {
      writeAtomicPrivate(fs, userConfigPath, serializeTomlConfig(cleanedUser.nextData, userConfigPath));
    }
  }

  syncManagedCodexHomeLinks(fs, userHome, managedHome);

  if (isGateway) {
    const prevProviders = isTomlTable(cleanedUser.nextData.model_providers) ? { ...cleanedUser.nextData.model_providers } : {};
    const nextConfig = {
      ...cleanedUser.nextData,
      cli_auth_credentials_store: 'file',
      model_provider: CODEX_GATEWAY_PROVIDER_ID,
      model_providers: {
        ...prevProviders,
        [CODEX_GATEWAY_PROVIDER_ID]: {
          name: 'PDD Codex Gateway',
          base_url: gatewayUrl,
          wire_api: 'responses',
          requires_openai_auth: false,
          supports_websockets: false,
          http_headers: { 'x-pdd-gateway-grant': grantToken },
        },
      },
    };
    const serializedConfig = serializeTomlConfig(nextConfig, configPath);
    const gatewayAuth = {
      auth_mode: 'apikey',
      OPENAI_API_KEY: grantToken,
    };
    writeAtomicCodexPair(fs, authPath, `${JSON.stringify(gatewayAuth, null, 2)}\n`, configPath, serializedConfig);
    return {
      codexHome: managedHome,
      authPath,
      configPath,
      managedCodexGateway: true,
      codexGatewayUrl: gatewayUrl,
      previousCodexModelProvider: fallbackPriorProvider,
    };
  }

  const nextOwnerConfig = {
    ...cleanedUser.nextData,
    cli_auth_credentials_store: 'file',
  };
  const serializedOwnerConfig = serializeTomlConfig(nextOwnerConfig, configPath);
  writeAtomicCodexPair(fs, authPath, `${JSON.stringify(stripped, null, 2)}\n`, configPath, serializedOwnerConfig);
  return {
    codexHome: managedHome,
    authPath,
    configPath,
    stripped,
    managedCodexGateway: false,
    codexGatewayUrl: null,
    previousCodexModelProvider: null,
  };
}

export function materializeLocalClaudeAuth(lease, { env = process.env, previousManagedBaseUrl = false } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const token = String(lease?.claude_oauth_token || lease?.gateway_bearer_token || '').trim();
  if (!token) throw new CloudAccountsError('Cloud lease returned no Claude OAuth token.', { code: 'invalid_lease' });
  rememberSecrets(token);
  const { settingsPath, onboardingPath } = localClaudePaths(env);
  const settings = readJsonObject(fs, settingsPath) ?? {};
  const settingsEnv = object(settings.env) ? { ...settings.env } : {};
  settingsEnv.CLAUDE_CODE_OAUTH_TOKEN = token;
  let managedBaseUrl = false;
  if (lease?.delivery_mode === 'gateway_grant' && typeof lease.anthropic_base_url === 'string' && lease.anthropic_base_url.trim()) {
    settingsEnv.ANTHROPIC_BASE_URL = lease.anthropic_base_url.trim();
    managedBaseUrl = true;
  } else if (previousManagedBaseUrl || MANAGED_CLAUDE_GATEWAY_RE.test(String(settingsEnv.ANTHROPIC_BASE_URL ?? ''))) {
    delete settingsEnv.ANTHROPIC_BASE_URL;
  }
  settings.env = settingsEnv;
  writeAtomicPrivate(fs, settingsPath, `${JSON.stringify(settings, null, 2)}\n`);

  const onboarding = readJsonObject(fs, onboardingPath) ?? {};
  onboarding.hasCompletedOnboarding = true;
  writeAtomicPrivate(fs, onboardingPath, `${JSON.stringify(onboarding, null, 2)}\n`);
  return { settingsPath, onboardingPath, managedBaseUrl };
}

export function createCodexStepOverlay(authOrLease, { env = process.env, tmpRoot, detached = false } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const sourceCodexHome = localCodexHome(env);
  const isGateway = object(authOrLease) && authOrLease.delivery_mode === 'gateway_grant';
  const gatewayUrl = isGateway ? validateCodexGatewayUrl(authOrLease.codex_gateway_url) : null;
  const gatewayToken = isGateway ? resolveCodexGatewayGrant(authOrLease) : null;
  const rootDir = tmpRoot || (fs.existsSync?.('/tmp') !== false ? '/tmp' : tmpdir());
  let overlayDir;
  if (typeof fs.mkdtempSync === 'function') {
    overlayDir = fs.mkdtempSync(join(rootDir, 'pdd-cx-'));
  } else if (fs === nativeFs) {
    overlayDir = nativeFs.mkdtempSync(join(rootDir, 'pdd-cx-'));
  } else {
    overlayDir = join(rootDir, `pdd-cx-${randomBytes(8).toString('hex')}`);
    fs.mkdirSync(overlayDir, { recursive: false, mode: 0o700 });
  }
  try { (fs.chmodSync ?? nativeFs.chmodSync)(overlayDir, 0o700); } catch {}
  let cleaned = false;
  const cleanup = () => {
    if (cleaned) return;
    cleaned = true;
    if (activeOverlayCleanups.delete(cleanup)) syncOverlayHooks();
    try { (fs.rmSync ?? nativeFs.rmSync)(overlayDir, { recursive: true, force: true }); } catch {}
  };
  if (!detached) {
    activeOverlayCleanups.add(cleanup);
    syncOverlayHooks();
  }
  const lstat = fs.lstatSync ?? nativeFs.lstatSync;
  try {
    const linkNames = isGateway ? CODEX_GATEWAY_OVERLAY_LINKS : CODEX_OVERLAY_LINKS;
    for (const name of linkNames) {
      const src = join(sourceCodexHome, name);
      try {
        const st = lstat(src);
        if (!st.isSymbolicLink()) {
          fs.symlinkSync(src, join(overlayDir, name));
        }
      } catch {}
    }
    if (isGateway) {
      let baseConfig = {};
      const srcConfigPath = join(sourceCodexHome, 'config.toml');
      try {
        const cfgStat = lstat(srcConfigPath);
        if (cfgStat.isFile() && !cfgStat.isSymbolicLink()) {
          baseConfig = readCodexTomlObject(fs, srcConfigPath, { strict: false }).data;
        }
      } catch {}
      const prevFeatures = isTomlTable(baseConfig.features) ? { ...baseConfig.features } : {};
      const prevPolicy = isTomlTable(baseConfig.shell_environment_policy) ? { ...baseConfig.shell_environment_policy } : {};
      const prevFilters = isTomlTable(prevPolicy.filters) ? { ...prevPolicy.filters } : {};
      const hasFilterIgnoreCase = key => {
        const lower = key.toLowerCase();
        return Object.keys(prevFilters).some(k => k.toLowerCase() === lower);
      };
      if (Array.isArray(prevPolicy.exclude)) {
        for (const item of prevPolicy.exclude) {
          if (typeof item === 'string' && item.trim() && !hasFilterIgnoreCase(item.trim())) {
            prevFilters[item.trim()] = 'exclude';
          }
        }
      }
      if (Array.isArray(prevPolicy.include_only)) {
        for (const item of prevPolicy.include_only) {
          if (typeof item === 'string' && item.trim() && !hasFilterIgnoreCase(item.trim())) {
            prevFilters[item.trim()] = 'include';
          }
        }
      }
      delete prevPolicy.exclude;
      delete prevPolicy.include_only;
      for (const k of Object.keys(prevFilters)) {
        if (k.toLowerCase() === 'pdd_codex_gateway_grant') {
          delete prevFilters[k];
        }
      }
      if (isTomlTable(prevPolicy.set)) {
        const nextSet = { ...prevPolicy.set };
        for (const k of Object.keys(nextSet)) {
          if (k.toLowerCase() === 'pdd_codex_gateway_grant') {
            delete nextSet[k];
          }
        }
        if (Object.keys(nextSet).length > 0) prevPolicy.set = nextSet;
        else delete prevPolicy.set;
      }
      prevFilters.PDD_CODEX_GATEWAY_GRANT = 'exclude';
      prevPolicy.filters = prevFilters;
      const prevProviders = isTomlTable(baseConfig.model_providers) ? { ...baseConfig.model_providers } : {};
      delete prevProviders[CODEX_GATEWAY_PROVIDER_ID];
      const overlayConfig = {
        ...baseConfig,
        model_provider: CODEX_GATEWAY_PROVIDER_ID,
        features: {
          ...prevFeatures,
          shell_snapshot: false,
        },
        shell_environment_policy: prevPolicy,
        model_providers: {
          ...prevProviders,
          [CODEX_GATEWAY_PROVIDER_ID]: {
            name: 'PDD Codex Gateway',
            base_url: gatewayUrl,
            wire_api: 'responses',
            requires_openai_auth: false,
            supports_websockets: false,
            env_http_headers: { 'x-pdd-gateway-grant': 'PDD_CODEX_GATEWAY_GRANT' },
          },
        },
      };
      const configPath = join(overlayDir, 'config.toml');
      writeAtomicPrivate(fs, configPath, serializeTomlConfig(overlayConfig, configPath));
      return { overlayDir, authPath: null, configPath, gatewayToken, gatewayUrl, cleanup };
    }
    const stripped = stripCodexAuthBundle(authOrLease);
    const authPath = join(overlayDir, 'auth.json');
    writeAtomicPrivate(fs, authPath, `${JSON.stringify(stripped, null, 2)}\n`);
    return { overlayDir, authPath, cleanup };
  } catch (error) {
    cleanup();
    throw error;
  }
}

export function buildClaudeStepEnv(baseEnv = process.env, lease) {
  const out = {};
  for (const [k, v] of Object.entries(baseEnv ?? {})) {
    if (typeof v === 'string') out[k] = v;
  }
  delete out.CLAUDE_CODE_OAUTH_TOKEN;
  const token = String(lease?.claude_oauth_token || lease?.gateway_bearer_token || '').trim();
  if (token) {
    rememberSecrets(token);
    out.CLAUDE_CODE_OAUTH_TOKEN = token;
  }
  if (lease?.delivery_mode === 'gateway_grant' && typeof lease.anthropic_base_url === 'string' && lease.anthropic_base_url.trim()) {
    out.ANTHROPIC_BASE_URL = lease.anthropic_base_url.trim();
  } else if (MANAGED_CLAUDE_GATEWAY_RE.test(String(out.ANTHROPIC_BASE_URL ?? ''))) {
    delete out.ANTHROPIC_BASE_URL;
  }
  return out;
}

export function prepareCloudStepExecution(leaseReply, baseEnv = process.env, ports = {}, { detached = false } = {}) {
  const provider = leaseReply?.account?.provider;
  const lease = leaseReply?.lease;
  const cleanBase = loginEnvironment(baseEnv, { kind: provider || 'codex' });
  if (provider === 'codex') {
    if (lease?.delivery_mode === 'gateway_grant') {
      const overlay = createCodexStepOverlay(lease, { env: baseEnv, tmpRoot: ports.tmpRoot, detached }, ports);
      const env = {
        ...cleanBase,
        CODEX_HOME: overlay.overlayDir,
        PDD_CODEX_GATEWAY_GRANT: overlay.gatewayToken,
        PDD_CLOUD_STEP_ISOLATED: '1',
      };
      delete env.OPENAI_API_KEY;
      delete env.CODEX_API_KEY;
      delete env.CODEX_ACCESS_TOKEN;
      delete env.OPENAI_BASE_URL;
      return { env, cleanupDirs: [overlay.overlayDir], cleanup: overlay.cleanup, overlayDir: overlay.overlayDir };
    }
    if (!object(lease?.codex_auth_json)) {
      throw new CloudAccountsError('Cloud lease returned no Codex auth bundle.', { code: 'invalid_lease' });
    }
    const overlay = createCodexStepOverlay(lease.codex_auth_json, { env: baseEnv, tmpRoot: ports.tmpRoot, detached }, ports);
    const env = { ...cleanBase, CODEX_HOME: overlay.overlayDir, PDD_CLOUD_STEP_ISOLATED: '1' };
    return { env, cleanupDirs: [overlay.overlayDir], cleanup: overlay.cleanup, overlayDir: overlay.overlayDir };
  }
  if (provider === 'claude') {
    const env = { ...buildClaudeStepEnv(cleanBase, lease), PDD_CLOUD_STEP_ISOLATED: '1' };
    return { env, cleanupDirs: [], cleanup: () => {}, overlayDir: null };
  }
  return { env: cleanBase, cleanupDirs: [], cleanup: () => {}, overlayDir: null };
}

const HARD_QUOTA_RE = /out of credits|credit balance is too low|insufficient[_ ]quota|exceeded your current quota|quota (?:exceeded|has been exhausted|exhausted)|hit your usage limit|usage[_ ]limit(?:_reached)?|weekly limit|daily limit|monthly limit|5-?hour limit|five[ _-]hour|spend[_ ]control|spending limit/i;

export function classifyRateLimitFailure(text, usageWindows = null) {
  if (!isQuotaExhaustionMessage(text)) return null;
  const fiveH = usageWindows?.five_hour_used_percent;
  const sevenD = usageWindows?.weekly_used_percent;
  if ((typeof fiveH === 'number' && fiveH >= 100) || (typeof sevenD === 'number' && sevenD >= 100)) {
    return 'quota_exhausted';
  }
  if (HARD_QUOTA_RE.test(String(text ?? ''))) return 'quota_exhausted';
  return 'burst_rate_limit';
}

export function normalizeUsagePercentInt(value) {
  if (typeof value !== 'number' || !Number.isFinite(value)) return null;
  return value >= 100 ? 100 : Math.max(0, Math.floor(value));
}

export function extractRateLimitReport(text, accountOrWindows = null, now = Date.now()) {
  const s = String(text ?? '');
  let fiveH = typeof accountOrWindows?.five_hour_used_percent === 'number' ? accountOrWindows.five_hour_used_percent : null;
  let fiveReset = typeof accountOrWindows?.five_hour_reset_at === 'string' ? accountOrWindows.five_hour_reset_at : null;
  let sevenD = typeof accountOrWindows?.weekly_used_percent === 'number' ? accountOrWindows.weekly_used_percent : null;
  let sevenReset = typeof accountOrWindows?.weekly_reset_at === 'string' ? accountOrWindows.weekly_reset_at : null;

  const isoMatch = /\b(20\d{2}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:\.\d+)?Z)\b/.exec(s);
  const resetsSec = /"resets[_A-Za-z]*":\s*(\d{9,12})/.exec(s);
  const parsedIso = isoMatch?.[1] ?? (resetsSec ? new Date(Number(resetsSec[1]) * 1000).toISOString() : null);

  const mentionsWeekly = /weekly|7[ -]?day|seven[ -]?day/i.test(s);
  if (mentionsWeekly) {
    sevenD = Math.max(sevenD ?? 0, 100);
    if (parsedIso && !sevenReset) sevenReset = parsedIso;
  } else if ((fiveH == null || fiveH < 100) && (sevenD == null || sevenD < 100)) {
    fiveH = 100;
    if (parsedIso && !fiveReset) fiveReset = parsedIso;
  }
  if (!fiveReset && (fiveH ?? 0) >= 100) fiveReset = parsedIso ?? new Date(now + 5 * 3600 * 1000).toISOString();
  if (!sevenReset && (sevenD ?? 0) >= 100) sevenReset = parsedIso ?? new Date(now + 24 * 3600 * 1000).toISOString();

  return {
    five_hour_used_percent: normalizeUsagePercentInt(fiveH ?? 100),
    five_hour_reset_at: fiveReset,
    weekly_used_percent: normalizeUsagePercentInt(sevenD ?? 0),
    weekly_reset_at: sevenReset,
    limit_reached: true,
  };
}

export async function reportCloudAccountUsage(accountId, report, { cwd = process.cwd(), env = process.env, timeoutMs = 4000 } = {}, ports = {}) {
  if (!accountId) return null;
  const body = {
    five_hour_used_percent: normalizeUsagePercentInt(report?.five_hour_used_percent),
    five_hour_reset_at: report?.five_hour_reset_at ?? null,
    weekly_used_percent: normalizeUsagePercentInt(report?.weekly_used_percent),
    weekly_reset_at: report?.weekly_reset_at ?? null,
    limit_reached: report?.limit_reached !== false,
  };
  return cloudAccountsRequest('POST', `/v1/accounts/${encodeURIComponent(accountId)}/usage-report`, { body, cwd, env, timeoutMs }, ports);
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
  const acc = leaseReply.account;
  const lease = leaseReply.lease;
  const prev = current.active?.[acc.provider];
  const nowIso = new Date((ports.now ?? Date.now)()).toISOString();
  const explicitRefreshAt = acc.last_refresh_at
    ?? acc.refreshed_at
    ?? lease.last_refresh_at
    ?? lease.codex_auth_json?.last_refresh
    ?? null;
  const lastRefreshAt = explicitRefreshAt
    ?? (prev?.account_id === acc.account_id ? prev?.last_refresh_at : null)
    ?? null;
  const accessTokenExpiresAt = acc.access_token_expires_at
    ?? lease.access_token_expires_at
    ?? extractJwtExpiresAtIso(lease.codex_auth_json?.tokens?.access_token)
    ?? null;
  const stillLocallyRevoked = isLocalReauthUnresolved(acc.account_id, explicitRefreshAt, current.reauth);
  const accountState = (isReauthRequiredAccount(acc) || stillLocallyRevoked)
    ? 'reauth_required'
    : (typeof acc.state === 'string' && acc.state ? acc.state : 'ready');
  const isMaterializedLocal = materializedLocal !== undefined
    ? Boolean(materializedLocal)
    : Boolean(prev?.account_id === acc.account_id && prev?.lease_id && prev.lease_id === lease.lease_id && prev.materialized_local === true);
  const nextActive = {
    ...current.active,
    [acc.provider]: {
      account_id: acc.account_id,
      label: acc.label ?? acc.account_id,
      provider: acc.provider,
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
  if (accountState !== 'reauth_required' && acc.account_id) {
    delete nextReauth[acc.account_id];
  }
  return writeCloudAccountsState({
    enrolled: true,
    providers: [...new Set([...current.providers, acc.provider])],
    active: nextActive,
    cooling: nextCooling,
    reauth: nextReauth,
  }, { env }, ports);
}

export async function leaseCloudAccount({
  provider = 'codex',
  currentAccountId = undefined,
  preferredLabel = null,
  skipAccountIds = [],
  holderId = 'pdd-step',
  updateState = true,
} = {}, { cwd = process.cwd(), env = process.env, timeoutMs = 15_000, maxRetries, now } = {}, ports = {}) {
  const nowFn = now ?? ports.now ?? Date.now;
  const effectivePorts = ports.now ? ports : { ...ports, now: nowFn };
  const { machineLabel } = resolveMachineIdentity(env, effectivePorts);
  const saved = readCloudAccountsState({ env }, effectivePorts);
  const savedActive = saved.active?.[provider];
  const locallyRevokedIds = Object.keys(saved.reauth ?? {});
  const savedStickyRevoked = currentAccountId === undefined
    && savedActive?.account_id
    && (savedActive?.state === 'reauth_required' || locallyRevokedIds.includes(savedActive.account_id));
  const stickyId = currentAccountId !== undefined
    ? currentAccountId
    : (savedStickyRevoked ? null : (savedActive?.account_id ?? null));
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
    if (remainingMs <= 0) {
      throw new CloudAccountsError('Cloud Accounts request timed out.', { code: 'timeout' });
    }
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
        },
        cwd,
        env,
        timeoutMs: remainingMs,
        deadlineMs,
        maxRetries,
      }, effectivePorts);
    } catch (error) {
      if (attempt < maxReauthSkips && isReauthRequiredFailure(error) && (deadlineMs - nowFn()) > 0) {
        const explicitAccountId = error?.payload?.account_id
          ?? error?.payload?.detail?.account_id
          ?? error?.payload?.account?.account_id
          ?? null;
        if (typeof explicitAccountId === 'string' && explicitAccountId) {
          markLocalAccountReauthRequired(explicitAccountId, { env }, effectivePorts);
        }
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
      writeCloudAccountsState({
        ...latestSaved,
        cooling: { ...latestSaved.cooling, [provider]: { wake_at: reply.wake_at ?? null } },
      }, { env }, effectivePorts);
    }
  }
  return reply;
}

function candidateCloudProviders({ fallbackAgent, allowedKinds, savedState }) {
  const allowed = Array.isArray(allowedKinds) ? CLOUD_PROVIDERS.filter(p => allowedKinds.includes(p)) : [...CLOUD_PROVIDERS];
  const enrolledAllowed = allowed.filter(p => Array.isArray(savedState?.providers) && savedState.providers.includes(p));
  if (!enrolledAllowed.length) return [];
  const preferred = CLOUD_PROVIDERS.includes(fallbackAgent?.kind) ? fallbackAgent.kind : null;
  if (preferred && enrolledAllowed.includes(preferred)) {
    return [preferred, ...enrolledAllowed.filter(p => p !== preferred)];
  }
  return enrolledAllowed;
}

export function isCreditOrResetAccount(entry) {
  return Boolean(entry?.credits === true || entry?.allowReset === true || entry?.allow_reset === true);
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
  const cooling = [];
  const unavailable = [];
  let earliestWakeAt = null;
  let earliestResetMs = null;

  for (const provider of providers) {
    const tried = new Set(Array.isArray(skipAccountIds) ? skipAccountIds.filter(Boolean) : []);
    for (let round = 0; round < 12; round++) {
      const roundCurrentId = round === 0 && preferredAccountId !== undefined
        ? preferredAccountId
        : (round === 0 ? (saved.active?.[provider]?.account_id ?? undefined) : undefined);
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
        if (validMs != null && (earliestResetMs == null || validMs < earliestResetMs)) {
          earliestResetMs = validMs;
          earliestWakeAt = wakeAt;
        } else if (!earliestWakeAt && wakeAt) {
          earliestWakeAt = wakeAt;
        }
        break;
      }

      if (reply?.state !== 'leased' || !object(reply.account) || !object(reply.lease)) {
        unavailable.push({ id: provider, reason: 'invalid_lease' });
        break;
      }

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
      // Stick-Until-100%: never rotate early at 97%; rotate only at >= 100%.
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

      // Optional live Codex window probe when explicitly supplied via ports (weeklyStopPercent = 100, never 97).
      if (provider === 'codex' && reply.lease?.delivery_mode !== 'gateway_grant' && (ports.readCodexUsageWindows || ports.readCodexLimits)) {
        const probeStep = prepareCloudStepExecution(reply, env, ports);
        let probeLimits;
        try {
          const cmd = (fallbackAgent?.kind === 'codex' && fallbackAgent?.command) ? fallbackAgent.command : 'codex';
          probeLimits = ports.readCodexUsageWindows
            ? await ports.readCodexUsageWindows({ command: cmd, cwd, env: probeStep.env, weeklyStopPercent: 100 }, ports.codexLimitPorts)
            : await ports.readCodexLimits({ command: cmd, cwd, env: probeStep.env, weeklyStopPercent: 100 }, ports.codexLimitPorts);
        } finally {
          probeStep.cleanup();
        }
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

      const command = (fallbackAgent?.kind === provider && typeof fallbackAgent?.command === 'string' && fallbackAgent.command.trim())
        ? fallbackAgent.command.trim()
        : provider;
      const model = fallbackAgent?.kind === provider && typeof fallbackAgent?.model === 'string' && fallbackAgent.model.trim()
        ? fallbackAgent.model.trim()
        : null;
      const login = {
        id: acc.account_id,
        label: acc.label ?? acc.account_id,
        kind: provider,
        command,
        model,
        plan: acc.plan ?? null,
        credits: acc.credits === true,
        allowReset: acc.allowReset === true || acc.allow_reset === true,
        paused: false,
        configVar: CONFIG_VAR[provider],
        configDir: null,
        env: {},
      };
      return {
        state: 'ready',
        cloud: true,
        configured: true,
        poolPath: null,
        poolSize: Math.max(8, Number.isSafeInteger(reply.pool_size) ? reply.pool_size : 8),
        login,
        agent: agentSpecOf(login),
        env: loginEnvironment(env, login),
        account: acc,
        lease: reply.lease,
        prepareStep: (stepBaseEnv = env, stepOpts = {}) => prepareCloudStepExecution(reply, stepBaseEnv, ports, stepOpts),
      };
    }
  }

  return {
    state: 'exhausted',
    cloud: true,
    configured: true,
    poolPath: null,
    poolSize: 1,
    resetAt: earliestResetMs,
    wakeAt: earliestWakeAt ?? (earliestResetMs != null ? new Date(earliestResetMs).toISOString() : null),
    cooling,
    unavailable,
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
    if (isAuthFailureMessage(reason) && !isQuotaExhaustionMessage(reason)) {
      markLocalAccountReauthRequired(loginId, { env }, ports);
    } else {
      const report = extractRateLimitReport(reason, accountWindows, now);
      await reportCloudAccountUsage(loginId, report, { cwd, env }, ports).catch(() => {});
    }
  }
  const skip = [...new Set([...(Array.isArray(skipAccountIds) ? skipAccountIds : []), ...(loginId ? [loginId] : [])])];
  return selectCloudPoolLogin({ cwd, env, fallbackAgent, allowedKinds, skipAccountIds: skip, holderId, allowCredits }, ports);
}

// ---- Internal local-folder pool fallback ----------------------------------------------------------------

function expandHome(value, home) {
  if (value === '~' || value.startsWith('~/')) {
    if (typeof home !== 'string' || !home) bad('HOME is required for tilde paths.');
    return value === '~' ? home : join(home, value.slice(2));
  }
  return value;
}

function statNoFollow(fs, path) {
  try { return (fs.lstatSync ?? nativeFs.lstatSync)(path); }
  catch (error) { if (error?.code === 'ENOENT') return null; bad('cannot inspect pool file.'); }
}

function readPoolJson(fs, path) {
  const info = statNoFollow(fs, path);
  if (!info) bad(`file not found at ${path}.`);
  if (!info.isFile() || info.isSymbolicLink()) bad('pool file must be a regular file and not a symlink.');
  if (info.size > 65_536) bad('pool file exceeds 65536 bytes.');
  if (fs.openSync && fs.fstatSync && fs.readSync && fs.closeSync || fs === nativeFs) {
    const f = fs.openSync ? fs : nativeFs;
    const flags = (f.constants?.O_RDONLY ?? 0) | (f.constants?.O_NOFOLLOW ?? 0) | (f.constants?.O_NONBLOCK ?? 0);
    let fd;
    try {
      fd = f.openSync(path, flags);
      const actual = f.fstatSync(fd);
      if (!actual.isFile() || actual.size > 65_536) bad('pool file must be regular and at most 65536 bytes.');
      const buf = Buffer.alloc(65_537);
      let len = 0;
      while (len < buf.length) {
        const n = f.readSync(fd, buf, len, buf.length - len, null);
        if (!n) break;
        len += n;
      }
      if (len > 65_536) bad('pool file exceeds 65536 bytes.');
      try { return JSON.parse(buf.subarray(0, len).toString('utf8')); }
      catch { bad('pool file must contain valid JSON.'); }
    } catch (error) {
      if (error?.message?.startsWith('Invalid login pool:')) throw error;
      bad('cannot read pool file.');
    } finally {
      if (fd !== undefined) try { f.closeSync(fd); } catch {}
    }
  }
  let raw;
  try { raw = fs.readFileSync(path, 'utf8'); } catch { bad('cannot read pool file.'); }
  if (Buffer.byteLength(raw, 'utf8') > 65_536) bad('pool file exceeds 65536 bytes.');
  try { return JSON.parse(raw); } catch { bad('pool file must contain valid JSON.'); }
}

export function resolvePoolPath({ cwd = process.cwd(), env = process.env, poolPath } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  if (poolPath !== undefined && poolPath !== null) {
    if (typeof poolPath !== 'string' || !poolPath.trim() || CONTROLS.test(poolPath)) bad('pool path must be a nonblank path or off.');
    const trimmed = poolPath.trim();
    if (trimmed === 'off' || trimmed === 'none') return null;
    return resolve(cwd, expandHome(trimmed, env.HOME));
  }
  const candidates = [];
  const xdg = typeof env.XDG_CONFIG_HOME === 'string' && env.XDG_CONFIG_HOME.trim() ? env.XDG_CONFIG_HOME.trim()
    : typeof env.HOME === 'string' && env.HOME ? join(env.HOME, '.config') : '';
  if (xdg) candidates.push(join(xdg, 'pdd', 'pool.json'));
  if (typeof env.HOME === 'string' && env.HOME) candidates.push(join(env.HOME, '.pdd', 'pool.json'));
  for (const candidate of candidates) {
    if (statNoFollow(fs, candidate)) return candidate;
  }
  return null;
}

function normalizeFallback(fallbackAgent, env) {
  const kind = KINDS.includes(fallbackAgent?.kind) ? fallbackAgent.kind : 'codex';
  const id = typeof fallbackAgent?.id === 'string' && /^[A-Za-z0-9._-]{1,80}$/.test(fallbackAgent.id) ? fallbackAgent.id : kind;
  const command = typeof fallbackAgent?.command === 'string' && fallbackAgent.command.trim() ? fallbackAgent.command.trim() : kind;
  const model = typeof fallbackAgent?.model === 'string' && fallbackAgent.model.trim() ? fallbackAgent.model.trim() : null;
  const configVar = CONFIG_VAR[kind];
  const configDir = typeof env?.[configVar] === 'string' && env[configVar].trim() ? env[configVar].trim() : null;
  return {
    id,
    kind,
    command,
    model,
    plan: null,
    credits: fallbackAgent?.credits === true,
    allowReset: fallbackAgent?.allowReset === true || fallbackAgent?.allow_reset === true,
    paused: false,
    configVar,
    configDir,
    env: object(fallbackAgent?.env) ? { ...fallbackAgent.env } : {},
  };
}

export function loadLoginPool({ cwd = process.cwd(), env = process.env, poolPath, fallbackAgent } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const resolved = resolvePoolPath({ cwd, env, poolPath }, { fs });
  if (!resolved) {
    return {
      configured: false,
      poolPath: null,
      reset: 'never',
      weeklyStopPercent: 97,
      logins: [normalizeFallback(fallbackAgent, env)],
    };
  }
  const config = readPoolJson(fs, resolved);
  if (!object(config) || Object.keys(config).some(k => !TOP_KEYS.has(k))) bad('expected an object with logins, optional weeklyStopPercent and optional reset.');
  if ('reset' in config && config.reset !== 'never') bad('reset must be "never"; Autopilot never spends reset credits.');
  let weeklyStopPercent = 97;
  if ('weeklyStopPercent' in config) {
    if (typeof config.weeklyStopPercent !== 'number' || !Number.isFinite(config.weeklyStopPercent) || config.weeklyStopPercent <= 0 || config.weeklyStopPercent > 100) {
      bad('weeklyStopPercent must be a finite number in (0, 100].');
    }
    weeklyStopPercent = config.weeklyStopPercent;
  }
  if (!Array.isArray(config.logins) || config.logins.length < 1 || config.logins.length > 24) {
    bad('logins must be a non-empty array of at most 24 entries.');
  }
  const seenIds = new Set();
  const baseDir = dirname(resolved);
  const logins = config.logins.map(item => {
    if (!object(item) || Object.keys(item).some(k => !ENTRY_KEYS.has(k))) bad('invalid login entry.');
    if (!KINDS.includes(item.kind)) bad(`unknown login kind ${JSON.stringify(item.kind)} (expected codex, claude, gemini or agy).`);
    const id = item.id === undefined ? item.kind : item.id;
    if (typeof id !== 'string' || !/^[A-Za-z0-9._-]{1,80}$/.test(id)) bad('login id must match [A-Za-z0-9._-]{1,80}.');
    if (seenIds.has(id)) bad(`duplicate login id ${JSON.stringify(id)}.`);
    seenIds.add(id);
    const rawCmd = item.command === undefined ? item.kind : item.command;
    if (typeof rawCmd !== 'string' || !rawCmd.trim() || rawCmd.length > 4096 || CONTROLS.test(rawCmd)) bad(`invalid command for login ${id}.`);
    let command = expandHome(rawCmd.trim(), env.HOME);
    if (!isAbsolute(command) && command.includes('/')) command = resolve(baseDir, command);
    let model = null;
    if (item.model !== undefined) {
      if (typeof item.model !== 'string' || !item.model.trim() || item.model.length > 200 || CONTROLS.test(item.model)) bad(`invalid model for login ${id}.`);
      model = item.model.trim();
    }
    let plan = null;
    if (item.plan !== undefined) {
      if (typeof item.plan !== 'string' || !item.plan.trim() || item.plan.length > 64 || CONTROLS.test(item.plan)) bad(`invalid plan for login ${id}.`);
      plan = item.plan.trim().toLowerCase();
    }
    if (item.credits !== undefined && typeof item.credits !== 'boolean') bad(`credits must be boolean for login ${id}.`);
    if (item.allowReset !== undefined && typeof item.allowReset !== 'boolean') bad(`allowReset must be boolean for login ${id}.`);
    if (item.allow_reset !== undefined && typeof item.allow_reset !== 'boolean') bad(`allow_reset must be boolean for login ${id}.`);
    if (item.paused !== undefined && typeof item.paused !== 'boolean') bad(`paused must be boolean for login ${id}.`);
    const ownFolderKey = FOLDER_KEY[item.kind];
    for (const key of Object.values(FOLDER_KEY)) {
      if (key !== ownFolderKey && item[key] !== undefined) bad(`${key} cannot be set on ${item.kind} login ${id}.`);
    }
    if (item[ownFolderKey] !== undefined && item.configHome !== undefined) bad(`set either ${ownFolderKey} or configHome on login ${id}, not both.`);
    const rawFolder = item[ownFolderKey] ?? item.configHome;
    let configDir = null;
    if (rawFolder !== undefined) {
      if (typeof rawFolder !== 'string' || !rawFolder.trim() || rawFolder.length > 4096 || CONTROLS.test(rawFolder)) bad(`invalid profile folder for login ${id}.`);
      configDir = resolve(baseDir, expandHome(rawFolder.trim(), env.HOME));
    }
    const rawEnv = item.env === undefined ? {} : item.env;
    if (!object(rawEnv) || Object.keys(rawEnv).length > 32) bad(`invalid env map for login ${id}.`);
    const childEnv = {};
    for (const [k, v] of Object.entries(rawEnv)) {
      if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(k) || typeof v !== 'string' || v.length > 4096 || v.includes('\0')) bad(`invalid env entry ${k} on login ${id}.`);
      if (SECRET_ENV_KEY.test(k) || ALL_CONFIG_VARS.includes(k)) {
        bad(`env key ${k} is not permitted in pool.json; keep credentials in local CLI profile folders.`);
      }
      childEnv[k] = expandHome(v, env.HOME);
    }
    return {
      id,
      kind: item.kind,
      command,
      model,
      plan,
      credits: item.credits === true,
      allowReset: item.allowReset === true || item.allow_reset === true,
      paused: item.paused === true,
      configVar: CONFIG_VAR[item.kind],
      configDir,
      env: childEnv,
    };
  });
  return { configured: true, poolPath: resolved, reset: 'never', weeklyStopPercent, logins };
}

export function loginEnvironment(baseEnv = process.env, login) {
  const out = {};
  for (const [k, v] of Object.entries(baseEnv ?? {})) {
    if (typeof v === 'string') out[k] = v;
  }
  for (const key of [...ALL_CONFIG_VARS, 'CLAUDECODE', 'CLAUDE_CODE_OAUTH_TOKEN', 'PDD_CODEX_GATEWAY_GRANT']) delete out[key];
  if (MANAGED_CLAUDE_GATEWAY_RE.test(String(out.ANTHROPIC_BASE_URL ?? ''))) {
    delete out.ANTHROPIC_BASE_URL;
  }
  if (login?.configVar && login?.configDir) out[login.configVar] = login.configDir;
  for (const [k, v] of Object.entries(login?.env ?? {})) {
    if (typeof v === 'string') out[k] = v;
  }
  return out;
}

function looksLikeTestDiagnostic(s) {
  return /\b(?:test|tests|spec|specs|assert|assertion|expected|fixture|fixtures)\b/i.test(s)
    && /\b(?:fail|failed|expected|got|fixture|spec)\b/i.test(s);
}

export function isAuthFailureMessage(text) {
  if (typeof text !== 'string') return false;
  const s = text.trim();
  if (!s || looksLikeTestDiagnostic(s)) return false;
  return /\b(?:failed to authenticate|oauth access token is invalid|failed to refresh token|authentication_error|invalid[_ ]api[_ ]key|not logged in|please (?:run \/login|log ?in|sign ?in))\b|\b(?:api error|http|status(?: code)?)\W{0,3}401\b|\b401\s+unauthorized\b/i.test(s)
    || REAUTH_TEXT_RE.test(s);
}

export function isQuotaExhaustionMessage(text) {
  if (typeof text !== 'string') return false;
  const s = text.trim();
  if (!s || looksLikeTestDiagnostic(s)) return false;
  return /out of credits|credit balance is too low|insufficient[_ ]quota|exceeded your current quota|quota (?:exceeded|has been exhausted|exhausted)|resource_exhausted|hit your usage limit|usage[_ ]limit|weekly limit|daily limit|monthly limit|spend[_ ]control|spending limit|rate[_ ]limit|too many requests|\b(?:status|http|error|code)[:\s]+429\b|\b429\s+too many requests\b/i.test(s);
}

const poolStatePath = stateRoot => join(stateRoot, 'login-pool.json');

export function readPoolCooldowns({ stateRoot, now = Date.now() } = {}, ports = {}) {
  if (!stateRoot) return {};
  const fs = ports.fs ?? nativeFs;
  try {
    const raw = JSON.parse(fs.readFileSync(poolStatePath(stateRoot), 'utf8'));
    if (!object(raw) || !object(raw.logins)) return {};
    const active = {};
    for (const [id, row] of Object.entries(raw.logins)) {
      if (object(row) && typeof row.until === 'number' && Number.isFinite(row.until) && row.until > now) {
        active[id] = {
          until: row.until,
          resetAt: typeof row.resetAt === 'number' && Number.isFinite(row.resetAt) ? row.resetAt : null,
          reason: typeof row.reason === 'string' ? row.reason.slice(0, 200) : 'quota',
          at: typeof row.at === 'number' && Number.isFinite(row.at) ? row.at : now,
        };
      }
    }
    return active;
  } catch {
    return {};
  }
}

function writePoolCooldowns(fs, stateRoot, logins) {
  if (!stateRoot) return;
  fs.mkdirSync(stateRoot, { recursive: true, mode: 0o700 });
  const target = poolStatePath(stateRoot);
  const tmp = `${target}.${process.pid}.${randomUUID()}.tmp`;
  fs.writeFileSync(tmp, `${JSON.stringify({ logins }, null, 2)}\n`, { mode: 0o600 });
  try { fs.chmodSync?.(tmp, 0o600); } catch {}
  fs.renameSync(tmp, target);
}

export function markLoginExhausted({ stateRoot, loginId, resetAt = null, reason = 'quota', now = Date.now() } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const validReset = typeof resetAt === 'number' && Number.isFinite(resetAt) && resetAt > now ? Math.ceil(resetAt) : null;
  const until = validReset ?? (now + POOL_FALLBACK_COOLDOWN_MS);
  const entry = {
    until,
    resetAt: validReset,
    reason: typeof reason === 'string' && reason.trim() ? reason.trim().slice(0, 200) : 'quota',
    at: now,
  };
  if (stateRoot && typeof loginId === 'string' && loginId) {
    const logins = readPoolCooldowns({ stateRoot, now }, { fs });
    logins[loginId] = entry;
    writePoolCooldowns(fs, stateRoot, logins);
  }
  return { id: loginId, ...entry };
}

export function clearPoolCooldowns({ stateRoot } = {}, ports = {}) {
  if (!stateRoot) return;
  const fs = ports.fs ?? nativeFs;
  try { (fs.rmSync ?? fs.unlinkSync)?.(poolStatePath(stateRoot), { force: true }); } catch {}
}

function hasExpiredClaudeCredentialsFile(fs, env, now) {
  if (env.CLAUDE_CODE_OAUTH_TOKEN || env.ANTHROPIC_API_KEY) return false;
  const base = env.CLAUDE_CONFIG_DIR || (env.HOME ? join(env.HOME, '.claude') : '');
  if (!base) return false;
  try {
    const settings = JSON.parse(fs.readFileSync(join(base, 'settings.json'), 'utf8'));
    rememberSecrets(...knownSecretValues(settings));
    if (settings?.env?.CLAUDE_CODE_OAUTH_TOKEN || settings?.env?.ANTHROPIC_API_KEY || settings?.apiKeyHelper) return false;
  } catch {}
  try {
    const creds = JSON.parse(fs.readFileSync(join(base, '.credentials.json'), 'utf8'));
    rememberSecrets(...knownSecretValues(creds));
    const oauth = object(creds?.claudeAiOauth) ? creds.claudeAiOauth : creds;
    const rawExp = oauth?.expiresAt ?? oauth?.expires_at;
    const expNum = typeof rawExp === 'number' ? rawExp : (typeof rawExp === 'string' && rawExp.trim() ? Number(rawExp) : NaN);
    const expMs = Number.isFinite(expNum) && expNum > 0
      ? (expNum > 1e11 ? expNum : expNum * 1000)
      : (typeof rawExp === 'string' ? Date.parse(rawExp) : NaN);
    const refresh = oauth?.refreshToken ?? oauth?.refresh_token;
    const hasRefresh = typeof refresh === 'string' && Boolean(refresh.trim());
    if (Number.isFinite(expMs) && expMs <= now && !hasRefresh) return true;
  } catch {}
  return false;
}

async function defaultProbeLogin(login, { cwd, env, fs = nativeFs, now = Date.now(), run = runAgentProcess }) {
  const exec = (args, opts = {}) => run(login.command, args, { cwd, env, input: '', timeoutMs: 10_000, maxBytes: 16_384, ...opts });
  try {
    if (login.kind === 'claude' && hasExpiredClaudeCredentialsFile(fs, env, now)) {
      return { ok: false, reason: 'expired' };
    }
    if (login.kind === 'codex' || login.kind === 'claude') {
      const status = await exec(login.kind === 'codex' ? ['login', 'status'] : ['auth', 'status', '--json']);
      return parseAgentAuthStatus({ agent: login.kind, result: status }) === 'ready' ? { ok: true } : { ok: false, reason: 'signed_out' };
    }
    if (login.kind === 'agy') {
      const result = await checkWorkflowAgents({ cwd, env, requested: 'agy' }, { run: (_file, args, opts) => exec(args, opts) });
      return result.ok ? { ok: true } : { ok: false, reason: 'signed_out' };
    }
    if (login.kind === 'gemini') {
      const info = await exec(['--version']);
      if (info?.code !== 0) return { ok: false, reason: 'missing' };
      if (Boolean(env.GEMINI_API_KEY || env.GOOGLE_API_KEY) || env.GOOGLE_GENAI_USE_VERTEXAI === 'true' || env.GOOGLE_GENAI_USE_GCA === 'true') return { ok: true };
      const base = env.GEMINI_CLI_HOME || env.HOME || '';
      for (const candidate of [join(base, '.gemini', 'oauth_creds.json'), join(base, 'oauth_creds.json')]) {
        try {
          const creds = JSON.parse(fs.readFileSync(candidate, 'utf8'));
          rememberSecrets(...knownSecretValues(creds));
          if (typeof creds?.refresh_token === 'string' && creds.refresh_token) return { ok: true };
        } catch {}
      }
      return { ok: false, reason: 'signed_out' };
    }
  } catch {
    return { ok: false, reason: 'unavailable' };
  }
  return { ok: false, reason: 'unavailable' };
}

function agentSpecOf(login) {
  return {
    id: login.id,
    kind: login.kind,
    command: login.command,
    ...(login.model ? { model: login.model } : {}),
  };
}

export async function selectPoolLogin({ cwd = process.cwd(), env = process.env, poolPath, pool: preloadedPool, fallbackAgent, stateRoot, allowLimited = false, allowCredits = false, allowedKinds } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const pool = preloadedPool ?? loadLoginPool({ cwd, env, poolPath, fallbackAgent }, { fs });
  const kindFilter = Array.isArray(allowedKinds) ? new Set(allowedKinds) : null;
  const active = pool.logins.filter(login => !login.paused && (!kindFilter || kindFilter.has(login.kind)));
  const eligible = active.filter(login => allowCredits || !isCreditOrResetAccount(login));
  if (kindFilter && eligible.length === 0) {
    return {
      state: 'unavailable',
      configured: pool.configured,
      poolPath: pool.poolPath,
      poolSize: 0,
      resetAt: null,
      cooling: [],
      unavailable: active.filter(login => !allowCredits && isCreditOrResetAccount(login)).map(login => ({ id: login.id, reason: 'credit_or_reset_guarded' })),
    };
  }
  const cooldowns = stateRoot ? readPoolCooldowns({ stateRoot, now }, { fs }) : {};
  const cooling = [];
  const unavailable = [];
  let fallbackLimited = null;

  for (const login of active) {
    if (!allowCredits && isCreditOrResetAccount(login)) {
      unavailable.push({ id: login.id, reason: 'credit_or_reset_guarded' });
      continue;
    }
    const cd = cooldowns[login.id];
    if (cd && cd.until > now) {
      cooling.push({ id: login.id, until: cd.until, resetAt: cd.resetAt ?? cd.until, reason: cd.reason });
      if (!allowLimited) continue;
    }
    const childEnv = loginEnvironment(env, login);
    const probe = ports.probeLogin
      ? await ports.probeLogin(login, childEnv)
      : await defaultProbeLogin(login, { cwd, env: childEnv, fs, now, run: ports.run });
    const probeOk = probe === true || probe?.ok === true;
    if (!probeOk) {
      unavailable.push({ id: login.id, reason: probe?.reason ?? 'unavailable' });
      continue;
    }
    if (login.kind === 'codex') {
      const limits = await (ports.readCodexLimits ?? readCodexLimits)(
        { command: login.command, cwd, env: childEnv, weeklyStopPercent: pool.weeklyStopPercent },
        ports.codexLimitPorts,
      );
      if (limits.state === 'limited') {
        const entry = markLoginExhausted({
          stateRoot,
          loginId: login.id,
          resetAt: limits.resetAt,
          reason: limits.usedPercent != null ? `usage-limit (${limits.usedPercent}%)` : 'usage-limit',
          now,
        }, { fs });
        if (!cooling.some(row => row.id === login.id)) cooling.push({ id: login.id, until: entry.until, resetAt: entry.resetAt ?? entry.until, reason: entry.reason });
        if (allowLimited && !fallbackLimited) fallbackLimited = { login, env: childEnv };
        continue;
      }
      if (limits.state === 'unknown' && (login.plan === 'pro' || isCreditOrResetAccount(login))) {
        const entry = markLoginExhausted({
          stateRoot,
          loginId: login.id,
          resetAt: null,
          reason: 'pro-limits-unverified',
          now,
        }, { fs });
        if (!cooling.some(row => row.id === login.id)) cooling.push({ id: login.id, until: entry.until, resetAt: entry.until, reason: entry.reason });
        continue;
      }
    }
    if (cd && cd.until > now && allowLimited) {
      if (!fallbackLimited) fallbackLimited = { login, env: childEnv };
      continue;
    }
    return {
      state: 'ready',
      configured: pool.configured,
      poolPath: pool.poolPath,
      poolSize: eligible.length,
      login,
      agent: agentSpecOf(login),
      env: childEnv,
    };
  }

  if (allowLimited && fallbackLimited) {
    return {
      state: 'ready',
      limited: true,
      configured: pool.configured,
      poolPath: pool.poolPath,
      poolSize: eligible.length,
      login: fallbackLimited.login,
      agent: agentSpecOf(fallbackLimited.login),
      env: fallbackLimited.env,
    };
  }

  const resetTimes = cooling.map(row => row.until).filter(v => typeof v === 'number' && Number.isFinite(v));
  return {
    state: 'exhausted',
    configured: pool.configured,
    poolPath: pool.poolPath,
    poolSize: eligible.length,
    resetAt: resetTimes.length ? Math.min(...resetTimes) : null,
    cooling,
    unavailable,
  };
}
