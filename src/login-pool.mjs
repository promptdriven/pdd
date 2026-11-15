// Generated from prompts/cli/login-pool.prompt.md (sha256: 66fb21eec250e3857a60b1030d27d9c02535523e4d05874dfc989c3d03539bd1).
import * as nativeFs from 'node:fs';
import { hostname as osHostname, homedir, tmpdir } from 'node:os';
import { dirname, isAbsolute, join, resolve } from 'node:path';
import { randomBytes, randomUUID } from 'node:crypto';
import { parseAgentAuthStatus, runAgentProcess } from './agent-adapters.mjs';
import * as codexLimitsModule from './codex-limits.mjs';
import { knownSecretValues, redactSecrets, rememberSecrets } from './secret-redaction.mjs';
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
const ENTRY_KEYS = new Set(['id', 'kind', 'command', 'model', 'plan', 'credits', 'paused', ...ALL_FOLDER_KEYS, 'env']);
const TOP_KEYS = new Set(['reset', 'weeklyStopPercent', 'logins']);
const CONTROLS = /[\u0000-\u001f\u007f-\u009f]/;
const SECRET_ENV_KEY = /(?:_TOKEN|_SECRET|_API_KEY|_PASSWORD|_CREDENTIAL|^SECRET_|API_KEY$|^OPENAI_API_KEY$|^ANTHROPIC_API_KEY$|^GEMINI_API_KEY$|^GOOGLE_API_KEY$|^CLAUDE_CODE_OAUTH_TOKEN$|^CODEX_ACCESS_TOKEN$)/i;
const CODEX_OVERLAY_LINKS = ['config.toml', 'skills', 'memories', 'sessions', 'rules'];
const MANAGED_CLAUDE_GATEWAY_RE = /\/v1\/(?:accounts\/)?claude-gateway(?:\/|$)/;
export const DEFAULT_CLOUD_URL = 'https://api.promptdriven.ai';
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

export async function resolveCloudAccountsToken({ cwd = process.cwd(), env = process.env, timeoutMs = 4000 } = {}, ports = {}) {
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
    const res = await run('gh', ['auth', 'token'], { cwd, env, input: '', timeoutMs: Math.min(timeoutMs, 4000), maxBytes: 4096 });
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
    for (const key of ['claude_oauth_token', 'gateway_bearer_token']) {
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

export async function cloudAccountsRequest(method, path, { body, cwd = process.cwd(), env = process.env, timeoutMs = 10_000 } = {}, ports = {}) {
  const baseUrl = resolveCloudAccountsEndpoint(env);
  const token = await resolveCloudAccountsToken({ cwd, env, timeoutMs }, ports);
  const { machineId } = resolveMachineIdentity(env, ports);
  const fetchImpl = ports.fetch ?? globalThis.fetch;
  if (typeof fetchImpl !== 'function') throw new CloudAccountsError('HTTP fetch is unavailable.', { code: 'fetch_unavailable' });
  const controller = new AbortController();
  const limit = typeof timeoutMs === 'number' && Number.isFinite(timeoutMs) && timeoutMs > 0 ? timeoutMs : 10_000;
  const timer = setTimeout(() => controller.abort(new Error('timeout')), limit);
  timer.unref?.();
  if (body !== undefined) rememberSecrets(...knownSecretValues(body));
  try {
    const headers = {
      Authorization: `Bearer ${token}`,
      'X-PDD-Machine-Id': machineId,
      Accept: 'application/json',
      ...(body !== undefined ? { 'Content-Type': 'application/json' } : {}),
    };
    const response = await fetchImpl(`${baseUrl}${path.startsWith('/') ? path : `/${path}`}`, {
      method,
      headers,
      ...(body !== undefined ? { body: JSON.stringify(body) } : {}),
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
      throw new CloudAccountsError(`Cloud Accounts ${method} ${path} failed (${response.status}): ${info.message}`, {
        status: response.status,
        code: String(info.code),
        payload: info.payload,
      });
    }
    return parsed ?? {};
  } catch (error) {
    if (error instanceof CloudAccountsError) throw error;
    const timedOut = error?.name === 'AbortError' || /timeout|aborted/i.test(String(error?.message ?? ''));
    throw new CloudAccountsError(timedOut ? 'Cloud Accounts request timed out.' : `Cloud Accounts unreachable: ${error?.message ?? 'network error'}`, {
      code: timedOut ? 'timeout' : 'network_error',
    });
  } finally {
    clearTimeout(timer);
  }
}

export function accountsStatePath(env = process.env) {
  const home = env?.HOME || homedir();
  const base = (typeof env?.PDD_STATE_DIR === 'string' && env.PDD_STATE_DIR.trim())
    ? env.PDD_STATE_DIR.trim()
    : (typeof env?.XDG_STATE_HOME === 'string' && env.XDG_STATE_HOME.trim())
      ? join(env.XDG_STATE_HOME.trim(), 'pdd')
      : join(home, '.local', 'state', 'pdd');
  return join(base, 'accounts-state.json');
}

export function readCloudAccountsState({ env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const raw = readJsonObject(fs, accountsStatePath(env));
  if (!raw) return { enrolled: false, providers: [], active: {}, cooling: {} };
  const active = {};
  if (object(raw.active)) {
    for (const provider of CLOUD_PROVIDERS) {
      const entry = raw.active[provider];
      if (object(entry) && typeof entry.account_id === 'string' && entry.account_id) {
        active[provider] = {
          account_id: entry.account_id,
          label: typeof entry.label === 'string' ? entry.label : entry.account_id,
          provider,
          lease_id: typeof entry.lease_id === 'string' ? entry.lease_id : null,
          expires_at: typeof entry.expires_at === 'string' ? entry.expires_at : null,
          delivery_mode: typeof entry.delivery_mode === 'string' ? entry.delivery_mode : null,
          anthropic_base_url: typeof entry.anthropic_base_url === 'string' ? entry.anthropic_base_url : null,
          managed_anthropic_base_url: entry.managed_anthropic_base_url === true,
          five_hour_used_percent: typeof entry.five_hour_used_percent === 'number' && Number.isFinite(entry.five_hour_used_percent) ? entry.five_hour_used_percent : null,
          five_hour_reset_at: typeof entry.five_hour_reset_at === 'string' ? entry.five_hour_reset_at : null,
          weekly_used_percent: typeof entry.weekly_used_percent === 'number' && Number.isFinite(entry.weekly_used_percent) ? entry.weekly_used_percent : null,
          weekly_reset_at: typeof entry.weekly_reset_at === 'string' ? entry.weekly_reset_at : null,
        };
      }
    }
  }
  const providers = Array.isArray(raw.providers) ? raw.providers.filter(p => CLOUD_PROVIDERS.includes(p)) : Object.keys(active);
  const cooling = object(raw.cooling) ? { ...raw.cooling } : {};
  return {
    enrolled: raw.enrolled === true || Object.keys(active).length > 0,
    providers: [...new Set([...providers, ...Object.keys(active)])],
    active,
    cooling,
  };
}

export function writeCloudAccountsState(state, { env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const active = {};
  if (object(state?.active)) {
    for (const provider of CLOUD_PROVIDERS) {
      const entry = state.active[provider];
      if (!object(entry) || typeof entry.account_id !== 'string' || !entry.account_id) continue;
      // Never persist tokens or credentials in accounts-state.json.
      active[provider] = {
        account_id: entry.account_id,
        label: typeof entry.label === 'string' ? entry.label : entry.account_id,
        provider,
        lease_id: typeof entry.lease_id === 'string' ? entry.lease_id : null,
        expires_at: typeof entry.expires_at === 'string' ? entry.expires_at : null,
        delivery_mode: typeof entry.delivery_mode === 'string' ? entry.delivery_mode : null,
        anthropic_base_url: typeof entry.anthropic_base_url === 'string' ? entry.anthropic_base_url : null,
        managed_anthropic_base_url: entry.managed_anthropic_base_url === true,
        five_hour_used_percent: typeof entry.five_hour_used_percent === 'number' && Number.isFinite(entry.five_hour_used_percent) ? entry.five_hour_used_percent : null,
        five_hour_reset_at: typeof entry.five_hour_reset_at === 'string' ? entry.five_hour_reset_at : null,
        weekly_used_percent: typeof entry.weekly_used_percent === 'number' && Number.isFinite(entry.weekly_used_percent) ? entry.weekly_used_percent : null,
        weekly_reset_at: typeof entry.weekly_reset_at === 'string' ? entry.weekly_reset_at : null,
      };
    }
  }
  const providers = [...new Set([...(Array.isArray(state?.providers) ? state.providers.filter(p => CLOUD_PROVIDERS.includes(p)) : []), ...Object.keys(active)])];
  const payload = {
    enrolled: state?.enrolled === true,
    updated_at: new Date((ports.now ?? Date.now)()).toISOString(),
    providers,
    active,
    cooling: object(state?.cooling) ? state.cooling : {},
  };
  writeAtomicPrivate(fs, accountsStatePath(env), `${JSON.stringify(payload, null, 2)}\n`);
  return payload;
}

export function isCloudAccountsActive({ env = process.env, poolPath } = {}, ports = {}) {
  if (typeof poolPath === 'string' && poolPath.trim()) return false;
  if (typeof env?.PDD_ACCOUNTS_URL === 'string' && env.PDD_ACCOUNTS_URL.trim()) return true;
  const saved = readCloudAccountsState({ env }, ports);
  return saved.enrolled === true;
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

export function localCodexAuthPath(env = process.env) {
  const home = env?.HOME || homedir();
  const codexHome = (typeof env?.CODEX_HOME === 'string' && env.CODEX_HOME.trim()) ? env.CODEX_HOME.trim() : join(home, '.codex');
  return join(codexHome, 'auth.json');
}

export function localClaudePaths(env = process.env) {
  const home = env?.HOME || homedir();
  const claudeDir = (typeof env?.CLAUDE_CONFIG_DIR === 'string' && env.CLAUDE_CONFIG_DIR.trim()) ? env.CLAUDE_CONFIG_DIR.trim() : join(home, '.claude');
  return {
    settingsPath: join(claudeDir, 'settings.json'),
    onboardingPath: join(home, '.claude.json'),
  };
}

export function materializeLocalCodexAuth(authJson, { env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const stripped = stripCodexAuthBundle(authJson);
  const target = localCodexAuthPath(env);
  writeAtomicPrivate(fs, target, `${JSON.stringify(stripped, null, 2)}\n`);
  return { authPath: target, stripped };
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

export function createCodexStepOverlay(authJson, { env = process.env, tmpRoot, detached = false } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const home = env?.HOME || homedir();
  const sourceCodexHome = (typeof env?.CODEX_HOME === 'string' && env.CODEX_HOME.trim()) ? env.CODEX_HOME.trim() : join(home, '.codex');
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
  try {
    for (const name of CODEX_OVERLAY_LINKS) {
      const src = join(sourceCodexHome, name);
      try {
        (fs.lstatSync ?? nativeFs.lstatSync)(src);
        fs.symlinkSync(src, join(overlayDir, name));
      } catch {}
    }
    const stripped = stripCodexAuthBundle(authJson);
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

export function saveActiveLeaseMetadata(leaseReply, { env = process.env, managedBaseUrl } = {}, ports = {}) {
  if (!object(leaseReply?.account) || !object(leaseReply?.lease)) return null;
  const current = readCloudAccountsState({ env }, ports);
  const acc = leaseReply.account;
  const lease = leaseReply.lease;
  const prev = current.active?.[acc.provider];
  const nextActive = {
    ...current.active,
    [acc.provider]: {
      account_id: acc.account_id,
      label: acc.label ?? acc.account_id,
      provider: acc.provider,
      lease_id: lease.lease_id ?? null,
      expires_at: lease.expires_at ?? null,
      delivery_mode: lease.delivery_mode ?? null,
      anthropic_base_url: lease.anthropic_base_url ?? null,
      managed_anthropic_base_url: managedBaseUrl !== undefined ? Boolean(managedBaseUrl) : Boolean(prev?.managed_anthropic_base_url),
      five_hour_used_percent: typeof acc.five_hour_used_percent === 'number' ? acc.five_hour_used_percent : null,
      five_hour_reset_at: acc.five_hour_reset_at ?? null,
      weekly_used_percent: typeof acc.weekly_used_percent === 'number' ? acc.weekly_used_percent : null,
      weekly_reset_at: acc.weekly_reset_at ?? null,
    },
  };
  const nextCooling = { ...current.cooling };
  delete nextCooling[acc.provider];
  return writeCloudAccountsState({
    enrolled: true,
    providers: [...new Set([...current.providers, acc.provider])],
    active: nextActive,
    cooling: nextCooling,
  }, { env }, ports);
}

export async function leaseCloudAccount({
  provider = 'codex',
  currentAccountId = undefined,
  preferredLabel = null,
  skipAccountIds = [],
  holderId = 'pdd-step',
  updateState = true,
} = {}, { cwd = process.cwd(), env = process.env, timeoutMs = 5000 } = {}, ports = {}) {
  const { machineLabel } = resolveMachineIdentity(env, ports);
  const saved = readCloudAccountsState({ env }, ports);
  const stickyId = currentAccountId !== undefined ? currentAccountId : (saved.active?.[provider]?.account_id ?? null);
  const skip = [...new Set((Array.isArray(skipAccountIds) ? skipAccountIds : []).filter(Boolean))];
  const reply = await cloudAccountsRequest('POST', '/v1/accounts/lease', {
    body: {
      provider,
      current_account_id: skip.includes(stickyId) ? null : stickyId,
      preferred_label: preferredLabel ?? null,
      skip_account_ids: skip,
      machine_label: machineLabel,
      holder_id: holderId,
    },
    cwd,
    env,
    timeoutMs,
  }, ports);
  if (reply?.state === 'leased' && updateState) {
    saveActiveLeaseMetadata(reply, { env }, ports);
  } else if (reply?.state === 'all_cooling' && updateState) {
    writeCloudAccountsState({
      ...saved,
      enrolled: true,
      cooling: { ...saved.cooling, [provider]: { wake_at: reply.wake_at ?? null } },
    }, { env }, ports);
  }
  return reply;
}

function candidateCloudProviders({ fallbackAgent, allowedKinds, savedState }) {
  const allowed = Array.isArray(allowedKinds) ? CLOUD_PROVIDERS.filter(p => allowedKinds.includes(p)) : [...CLOUD_PROVIDERS];
  if (!allowed.length) return [];
  const preferred = CLOUD_PROVIDERS.includes(fallbackAgent?.kind) ? fallbackAgent.kind : null;
  if (preferred && allowed.includes(preferred)) {
    const others = allowed.filter(p => p !== preferred && savedState.providers.includes(p));
    return [preferred, ...others];
  }
  const enrolledAllowed = allowed.filter(p => savedState.providers.includes(p));
  return enrolledAllowed.length ? enrolledAllowed : [allowed[0]];
}

export async function selectCloudPoolLogin({
  cwd = process.cwd(),
  env = process.env,
  fallbackAgent,
  allowedKinds,
  skipAccountIds = [],
  preferredAccountId = undefined,
  holderId = 'autopilot-step',
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
      let reply;
      try {
        reply = await leaseCloudAccount({
          provider,
          currentAccountId: round === 0 && preferredAccountId !== undefined ? preferredAccountId : undefined,
          skipAccountIds: [...tried],
          holderId,
        }, { cwd, env, timeoutMs: ports.timeoutMs ?? 5000 }, ports);
      } catch (error) {
        unavailable.push({ id: provider, reason: error.code ?? 'unavailable' });
        break;
      }

      if (reply?.state === 'all_cooling') {
        const wakeAt = typeof reply.wake_at === 'string' ? reply.wake_at : null;
        const wakeMs = wakeAt ? Date.parse(wakeAt) : NaN;
        const validMs = Number.isFinite(wakeMs) ? wakeMs : null;
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
      if (provider === 'codex' && (ports.readCodexUsageWindows || ports.readCodexLimits)) {
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
        credits: false,
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
} = {}, ports = {}) {
  const now = (ports.now ?? Date.now)();
  if (loginId) {
    const report = extractRateLimitReport(reason, accountWindows, now);
    await reportCloudAccountUsage(loginId, report, { cwd, env }, ports).catch(() => {});
  }
  const skip = [...new Set([...(Array.isArray(skipAccountIds) ? skipAccountIds : []), ...(loginId ? [loginId] : [])])];
  return selectCloudPoolLogin({ cwd, env, fallbackAgent, allowedKinds, skipAccountIds: skip, holderId }, ports);
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
    credits: false,
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
  for (const key of [...ALL_CONFIG_VARS, 'CLAUDECODE', 'CLAUDE_CODE_OAUTH_TOKEN']) delete out[key];
  if (MANAGED_CLAUDE_GATEWAY_RE.test(String(out.ANTHROPIC_BASE_URL ?? ''))) {
    delete out.ANTHROPIC_BASE_URL;
  }
  if (login?.configVar && login?.configDir) out[login.configVar] = login.configDir;
  for (const [k, v] of Object.entries(login?.env ?? {})) {
    if (typeof v === 'string') out[k] = v;
  }
  return out;
}

export function isQuotaExhaustionMessage(text) {
  if (typeof text !== 'string') return false;
  const s = text.trim();
  if (!s) return false;
  if (/\b(?:test|tests|spec|specs|assert|assertion|expected|fixture|fixtures)\b/i.test(s)
    && /\b(?:fail|failed|expected|got|fixture|spec)\b/i.test(s)) return false;
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

async function defaultProbeLogin(login, { cwd, env, fs = nativeFs, run = runAgentProcess }) {
  const exec = (args, opts = {}) => run(login.command, args, { cwd, env, input: '', timeoutMs: 10_000, maxBytes: 16_384, ...opts });
  try {
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

export async function selectPoolLogin({ cwd = process.cwd(), env = process.env, poolPath, pool: preloadedPool, fallbackAgent, stateRoot, allowLimited = false, allowedKinds } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const now = (ports.now ?? Date.now)();
  const pool = preloadedPool ?? loadLoginPool({ cwd, env, poolPath, fallbackAgent }, { fs });
  const kindFilter = Array.isArray(allowedKinds) ? new Set(allowedKinds) : null;
  const active = pool.logins.filter(login => !login.paused && (!kindFilter || kindFilter.has(login.kind)));
  if (kindFilter && active.length === 0) {
    return {
      state: 'unavailable',
      configured: pool.configured,
      poolPath: pool.poolPath,
      poolSize: 0,
      resetAt: null,
      cooling: [],
      unavailable: [],
    };
  }
  const cooldowns = stateRoot ? readPoolCooldowns({ stateRoot, now }, { fs }) : {};
  const cooling = [];
  const unavailable = [];
  let fallbackLimited = null;

  for (const login of active) {
    const cd = cooldowns[login.id];
    if (cd && cd.until > now) {
      cooling.push({ id: login.id, until: cd.until, resetAt: cd.resetAt ?? cd.until, reason: cd.reason });
      if (!allowLimited) continue;
    }
    const childEnv = loginEnvironment(env, login);
    const probe = ports.probeLogin
      ? await ports.probeLogin(login, childEnv)
      : await defaultProbeLogin(login, { cwd, env: childEnv, fs, run: ports.run });
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
      if (limits.state === 'unknown' && (login.plan === 'pro' || login.credits === true)) {
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
      poolSize: active.length,
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
      poolSize: active.length,
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
    poolSize: active.length,
    resetAt: resetTimes.length ? Math.min(...resetTimes) : null,
    cooling,
    unavailable,
  };
}
