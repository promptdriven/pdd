// Generated from prompts/cli/login-pool.prompt.md.
// PDD Cloud Accounts HTTP client, token/endpoint resolution, and auth/quota classifiers.
import { hostname as osHostname } from 'node:os';
import { knownSecretValues, rememberSecrets } from '../secret-redaction.mjs';
import { runProcess } from '../shared/subprocess.mjs';
import { CloudAccountsError } from './cloud-error.mjs';

export const DEFAULT_CLOUD_URL = 'https://pdd-byok-api-c437voydwa-uc.a.run.app';

const REAUTH_CODE_RE = /\b(?:reauth_required|needs_reauth|token_revoked|invalid_grant|refresh_token_reused|refresh_token_expired|oauth_token_revoked|oauth_not_allowed_for_organization|oauth_org_not_allowed)\b|disabled\s+claude\s+subscription\s+access\s+for\s+claude\s+code/i;
const REAUTH_TEXT_RE = /\b(?:reauth_required|needs_reauth|token_revoked|invalid_grant|refresh_token_reused|refresh_token_expired|oauth_token_revoked|oauth_not_allowed_for_organization|oauth_org_not_allowed)\b|disabled\s+claude\s+subscription\s+access\s+for\s+claude\s+code|(?:status|http|error)[:=\s]+401\b|\b401\s+unauthorized\b/i;
const GATEWAY_GRANT_REVOKED_RE = /\b(?:gateway_grant_revoked|share_revoked)\b|gateway\s+grant\s+(?:was\s+revoked|expired|request\s+limit\s+reached|principal\s+mismatch)|shared\s+account\s+(?:is\s+not\s+active|no\s+longer\s+exists|authorization\s+epoch\s+changed)/i;
const HARD_QUOTA_RE = /out of credits|credit balance is too low|insufficient[_ ]quota|exceeded your current quota|quota (?:exceeded|has been exhausted|exhausted)|hit your usage limit|usage[_ ]limit(?:_reached)?|weekly limit|daily limit|monthly limit|5-?hour limit|five[ _-]hour|spend[_ ]control|spending limit/i;

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

function looksLikeTestDiagnostic(s) {
  return /\b(?:test|tests|spec|specs|assert|assertion|expected|fixture|fixtures)\b/i.test(s)
    && /\b(?:fail|failed|expected|got|fixture|spec)\b/i.test(s);
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

export function isGatewayGrantRevokedFailure(errorOrText) {
  if (!errorOrText) return false;
  if (typeof errorOrText === 'string') {
    const s = errorOrText.trim();
    return Boolean(s && !looksLikeTestDiagnostic(s) && GATEWAY_GRANT_REVOKED_RE.test(s));
  }
  if (typeof errorOrText === 'object') {
    const fields = [errorOrText.code, errorOrText.reason, errorOrText.message, errorOrText.payload?.reason, errorOrText.payload?.state, errorOrText.payload?.error]
      .filter(v => typeof v === 'string' && v);
    if (fields.some(v => GATEWAY_GRANT_REVOKED_RE.test(v))) return true;
    if (object(errorOrText.payload) && GATEWAY_GRANT_REVOKED_RE.test(JSON.stringify(errorOrText.payload))) return true;
  }
  return false;
}

export function isExplicitReauthCodeFailure(errorOrText) {
  if (!errorOrText) return false;
  if (typeof errorOrText === 'string') {
    const s = errorOrText.trim();
    return Boolean(s && !looksLikeTestDiagnostic(s) && REAUTH_CODE_RE.test(s));
  }
  if (typeof errorOrText === 'object') {
    if (errorOrText.code === 'missing_auth_token') return false;
    const fields = [errorOrText.code, errorOrText.reason, errorOrText.message, errorOrText.payload?.reason, errorOrText.payload?.state]
      .filter(v => typeof v === 'string' && v);
    if (fields.some(v => REAUTH_CODE_RE.test(v))) return true;
    if (object(errorOrText.payload) && REAUTH_CODE_RE.test(JSON.stringify(errorOrText.payload))) return true;
  }
  return false;
}

export function isReauthRequiredFailure(errorOrText) {
  if (!errorOrText) return false;
  if (isExplicitReauthCodeFailure(errorOrText)) return true;
  if (isGatewayGrantRevokedFailure(errorOrText)) return false;
  if (typeof errorOrText === 'string') {
    const s = errorOrText.trim();
    return Boolean(s && !looksLikeTestDiagnostic(s) && REAUTH_TEXT_RE.test(s));
  }
  if (typeof errorOrText === 'object') {
    if (errorOrText.code === 'missing_auth_token') return false;
    const hasAccountContext = Boolean(errorOrText.payload?.account_id || errorOrText.payload?.detail?.account_id || errorOrText.payload?.account?.account_id);
    if (errorOrText.status === 401 && hasAccountContext) return true;
  }
  return false;
}

export function isAuthFailureMessage(text) {
  if (typeof text !== 'string') return false;
  const s = text.trim();
  if (!s || looksLikeTestDiagnostic(s)) return false;
  return /\b(?:failed to authenticate|oauth access token is invalid|failed to refresh token|authentication_error|invalid[_ ]api[_ ]key|not logged in|please (?:run \/login|log ?in|sign ?in)|oauth_not_allowed_for_organization|oauth_org_not_allowed)\b|disabled\s+claude\s+subscription\s+access\s+for\s+claude\s+code|\b(?:api error|http|status(?: code)?)\W{0,3}401\b|\b401\s+unauthorized\b/i.test(s)
    || REAUTH_TEXT_RE.test(s)
    || GATEWAY_GRANT_REVOKED_RE.test(s);
}

export function isQuotaExhaustionMessage(text) {
  if (typeof text !== 'string') return false;
  const s = text.trim();
  if (!s || looksLikeTestDiagnostic(s)) return false;
  return /out of credits|credit balance is too low|insufficient[_ ]quota|exceeded your current quota|quota (?:exceeded|has been exhausted|exhausted)|resource_exhausted|hit your usage limit|usage[_ ]limit|weekly limit|daily limit|monthly limit|spend[_ ]control|spending limit|rate[_ ]limit|too many requests|\b(?:status|http|error|code)[:\s]+429\b|\b429\s+too many requests\b/i.test(s);
}

export function classifyRateLimitFailure(text, usageWindows = null) {
  if (!isQuotaExhaustionMessage(text)) return null;
  const fiveH = usageWindows?.five_hour_used_percent;
  const sevenD = usageWindows?.weekly_used_percent;
  if ((typeof fiveH === 'number' && fiveH >= 100) || (typeof sevenD === 'number' && sevenD >= 100)) return 'quota_exhausted';
  return HARD_QUOTA_RE.test(String(text ?? '')) ? 'quota_exhausted' : 'burst_rate_limit';
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

  if (/weekly|7[ -]?day|seven[ -]?day/i.test(s)) {
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
    if (val) { rememberSecrets(val); return val; }
  }
  if (typeof ports.authToken === 'function') {
    const tok = String((await ports.authToken({ cwd, env })) ?? '').trim();
    if (tok) { rememberSecrets(tok); return tok; }
  }
  try {
    const run = ports.run ?? runProcess;
    const res = await run('gh', ['auth', 'token'], { cwd, env, input: '', timeoutMs: Math.min(timeoutMs, 10_000), maxBytes: 4096 });
    const tok = res?.code === 0 && typeof res.stdout === 'string' ? res.stdout.trim() : '';
    if (tok) { rememberSecrets(tok); return tok; }
  } catch {}
  throw new CloudAccountsError('Sign in with gh auth login or set PDD_TOKEN before using Cloud Accounts.', { code: 'missing_auth_token' });
}

export function resolveMachineIdentity(env = process.env, ports = {}) {
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
  let code = '', message = '';
  if (object(detail)) {
    code = String(detail.error?.code || (typeof detail.error === 'string' ? detail.error : '') || detail.code || '');
    message = String(detail.message || detail.error?.message || (typeof detail.error === 'string' ? detail.error : '') || '');
  } else if (typeof detail === 'string' && detail.trim()) {
    message = detail.trim();
  } else if (Array.isArray(detail) && detail.length) {
    const msgs = detail.map(item => (object(item) && typeof item.msg === 'string' ? item.msg : '')).filter(Boolean);
    if (msgs.length) { code = 'validation_error'; message = msgs.join('; '); }
  }
  if (!code) code = String(parsed.error?.code || (typeof parsed.error === 'string' ? parsed.error : '') || parsed.code || '');
  if (!message) message = String(parsed.error?.message || parsed.message || (typeof parsed.error === 'string' ? parsed.error : '') || '');
  const payload = object(detail) ? { ...parsed, ...detail } : parsed;
  return { code: code || `http_${status}`, message: message || `HTTP ${status}`, payload };
}

export async function cloudAccountsRequest(method, path, { body, cwd = process.cwd(), env = process.env, timeoutMs = 20_000, maxRetries, deadlineMs } = {}, ports = {}) {
  const nowFn = ports.now ?? Date.now;
  const upperMethod = String(method ?? 'GET').toUpperCase();
  const normalizedPath = path.startsWith('/') ? path : `/${path}`;
  const pathnameOnly = normalizedPath.split('?')[0];
  const isIdempotentRetryable = upperMethod === 'GET' || (upperMethod === 'POST' && pathnameOnly === '/v1/accounts/lease');
  const retries = maxRetries !== undefined ? Math.max(0, Math.trunc(Number(maxRetries) || 0)) : (isIdempotentRetryable ? 1 : 0);

  const totalLimit = typeof timeoutMs === 'number' && Number.isFinite(timeoutMs) && timeoutMs > 0 ? timeoutMs : 20_000;
  const effectiveDeadline = typeof deadlineMs === 'number' && Number.isFinite(deadlineMs) ? deadlineMs : (nowFn() + totalLimit);

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
    if (remainingMs <= 0) throw new CloudAccountsError('Cloud Accounts request timed out.', { code: 'timeout' });
    const attemptLimit = attempt < retries ? Math.max(1, Math.ceil(remainingMs * 0.65)) : Math.max(1, remainingMs);
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
      if (rawText.trim()) { try { parsed = JSON.parse(rawText); } catch { parsed = null; } }
      if (parsed) rememberLeaseSecrets(parsed);
      if (!response.ok) {
        const info = extractCloudErrorInfo(parsed, response.status);
        throw new CloudAccountsError(`Cloud Accounts ${upperMethod} ${path} failed (${response.status}): ${info.message}`, {
          status: response.status, code: String(info.code), payload: info.payload,
        });
      }
      return parsed ?? {};
    } catch (error) {
      if (error instanceof CloudAccountsError) throw error;
      const timedOut = error?.name === 'AbortError' || error?.name === 'TimeoutError' || /timed?\s*out|aborted/i.test(String(error?.message ?? ''));
      if (timedOut && isIdempotentRetryable && attempt < retries && (effectiveDeadline - nowFn()) > 0) continue;
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
  return cloudAccountsRequest('GET', refresh === true ? '/v1/accounts?refresh=true' : '/v1/accounts', { cwd, env, timeoutMs, maxRetries }, ports);
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

export async function releaseCloudLease(leaseId, { cwd = process.cwd(), env = process.env, timeoutMs = 2500 } = {}, ports = {}) {
  if (typeof leaseId !== 'string' || !leaseId.trim()) return null;
  return cloudAccountsRequest('POST', `/v1/accounts/leases/${encodeURIComponent(leaseId.trim())}/release`, { cwd, env, timeoutMs, maxRetries: 0 }, ports);
}

export async function heartbeatCloudLease(leaseId, { cwd = process.cwd(), env = process.env, timeoutMs = 5000 } = {}, ports = {}) {
  if (typeof leaseId !== 'string' || !leaseId.trim()) return null;
  return cloudAccountsRequest('POST', `/v1/accounts/leases/${encodeURIComponent(leaseId.trim())}/heartbeat`, { cwd, env, timeoutMs, maxRetries: 0 }, ports);
}
