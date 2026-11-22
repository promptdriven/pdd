// Generated from prompts/cli/login-pool.prompt.md.
// Claude gateway settings overlay, local cleanup, step environment, and overlay cleanup registry.
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { rememberSecrets } from '../secret-redaction.mjs';
import { isPathAtOrInside, readJsonObjectQuiet as readJsonObject, writeAtomicPrivate } from '../shared/atomic-fs.mjs';
import { CloudAccountsError } from './cloud-error.mjs';
import {
  claudeTokenFingerprint,
  localClaudePaths,
  managedClaudeSettingsPath,
  normalizeTokenHashes,
  pddManagedClaudeHome,
  readCloudAccountsState,
} from './cloud-state.mjs';
import { MANAGED_CLAUDE_GATEWAY_RE } from './pool-env.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

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
  if (!otherListeners) process.exit(signal === 'SIGINT' ? 130 : 143);
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

export function registerOverlayCleanup(fn) {
  activeOverlayCleanups.add(fn);
  syncOverlayHooks();
}

export function unregisterOverlayCleanup(fn) {
  if (activeOverlayCleanups.delete(fn)) syncOverlayHooks();
}

function validateClaudeGatewayUrl(rawUrl) {
  const raw = String(rawUrl ?? '').trim().replace(/\/+$/, '');
  if (!raw) throw new CloudAccountsError('Cloud lease returned no Claude gateway URL.', { code: 'invalid_lease' });
  let parsed;
  try { parsed = new URL(raw); } catch { throw new CloudAccountsError('Invalid Claude gateway URL in Cloud lease.', { code: 'invalid_lease' }); }
  if (parsed.username || parsed.password) {
    throw new CloudAccountsError('Claude gateway URL must not include embedded credentials.', { code: 'invalid_lease' });
  }
  const loopback = ['127.0.0.1', 'localhost', '[::1]', '::1'].includes(parsed.hostname.toLowerCase());
  if (parsed.protocol !== 'https:' && !(parsed.protocol === 'http:' && loopback)) {
    throw new CloudAccountsError('Claude gateway URL requires https://.', { code: 'invalid_lease' });
  }
  return raw;
}

export function buildClaudeGatewaySettingsOverlay(lease, { env = process.env, userSettings = null } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const token = String(lease?.claude_oauth_token || lease?.gateway_bearer_token || '').trim();
  if (!token) throw new CloudAccountsError('Cloud lease returned no Claude OAuth token.', { code: 'invalid_lease' });
  rememberSecrets(token);

  const base = object(userSettings) ? { ...userSettings } : {};
  const mergedEnv = object(base.env) ? { ...base.env } : {};
  mergedEnv.CLAUDE_CODE_OAUTH_TOKEN = token;
  mergedEnv.ANTHROPIC_API_KEY = '';
  mergedEnv.ANTHROPIC_AUTH_TOKEN = '';
  mergedEnv.CLAUDE_CODE_USE_BEDROCK = '0';
  mergedEnv.CLAUDE_CODE_USE_VERTEX = '0';
  mergedEnv.CLAUDE_CODE_USE_FOUNDRY = '0';

  let managedBaseUrl = false;
  if (lease?.delivery_mode === 'gateway_grant') {
    mergedEnv.ANTHROPIC_BASE_URL = validateClaudeGatewayUrl(lease.anthropic_base_url);
    managedBaseUrl = true;
  } else {
    delete mergedEnv.ANTHROPIC_BASE_URL;
    const userGlobal = readJsonObject(fs, localClaudePaths(env).settingsPath);
    if (String(userGlobal?.env?.ANTHROPIC_BASE_URL ?? '').trim()) mergedEnv.ANTHROPIC_BASE_URL = 'https://api.anthropic.com';
  }
  return { settings: { ...base, apiKeyHelper: '', env: mergedEnv }, managedBaseUrl };
}

export function createClaudeStepSettingsOverlay(lease, { env = process.env, tmpRoot, userSettings = null, detached = false } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const { settings, managedBaseUrl } = buildClaudeGatewaySettingsOverlay(lease, { env, userSettings }, ports);
  const rootDir = tmpRoot ?? tmpdir();
  fs.mkdirSync(rootDir, { recursive: true, mode: 0o700 });
  let overlayDir;
  if (typeof fs.mkdtempSync === 'function') overlayDir = fs.mkdtempSync(join(rootDir, 'pdd-cl-'));
  else if (fs === nativeFs) overlayDir = nativeFs.mkdtempSync(join(rootDir, 'pdd-cl-'));
  else { overlayDir = join(rootDir, `pdd-cl-${randomBytes(8).toString('hex')}`); fs.mkdirSync(overlayDir, { recursive: true, mode: 0o700 }); }
  try { fs.chmodSync?.(overlayDir, 0o700); } catch {}

  let cleaned = false;
  const cleanup = () => {
    if (cleaned) return;
    cleaned = true;
    unregisterOverlayCleanup(cleanup);
    try { fs.rmSync(overlayDir, { recursive: true, force: true }); } catch {}
  };
  if (!detached) registerOverlayCleanup(cleanup);

  try {
    const settingsPath = join(overlayDir, 'settings.json');
    writeAtomicPrivate(fs, settingsPath, `${JSON.stringify(settings, null, 2)}\n`);
    return { overlayDir, settingsPath, managedBaseUrl, cleanup };
  } catch (error) {
    cleanup();
    throw error;
  }
}

export function materializeLocalClaudeAuth(lease, { env = process.env } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const { settings, managedBaseUrl } = buildClaudeGatewaySettingsOverlay(lease, { env }, ports);
  const claudeHome = pddManagedClaudeHome(env), settingsPath = managedClaudeSettingsPath(env);
  fs.mkdirSync(claudeHome, { recursive: true, mode: 0o700 });
  try { fs.chmodSync?.(claudeHome, 0o700); } catch {}
  writeAtomicPrivate(fs, settingsPath, `${JSON.stringify(settings, null, 2)}\n`);
  return { claudeHome, settingsPath, onboardingPath: null, managedBaseUrl };
}

export function restoreLocalClaudeGatewayConfig({ env = process.env, managedTokenHashes = null, removeManagedFile = true } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const managedPath = managedClaudeSettingsPath(env);
  let removedManagedSettings = false;
  if (removeManagedFile) {
    try { fs.unlinkSync(managedPath); removedManagedSettings = true; } catch {}
  }
  const { settingsPath } = localClaudePaths(env);
  const settings = readJsonObject(fs, settingsPath);
  if (!object(settings) || !object(settings.env)) {
    return { settingsPath, managedPath, removedManagedSettings, restoredSettings: false };
  }
  const hashSet = new Set(normalizeTokenHashes(managedTokenHashes));
  try {
    const saved = readCloudAccountsState({ env }, ports);
    for (const h of normalizeTokenHashes(saved.managed_claude_token_hashes)) hashSet.add(h);
  } catch {}
  const settingsEnv = { ...settings.env };
  let changed = false;
  if (typeof settingsEnv.CLAUDE_CODE_OAUTH_TOKEN === 'string') {
    const tok = settingsEnv.CLAUDE_CODE_OAUTH_TOKEN.trim();
    if (tok.startsWith('pddg_') || Boolean(tok && hashSet.size > 0 && hashSet.has(claudeTokenFingerprint(tok)))) {
      rememberSecrets(tok);
      delete settingsEnv.CLAUDE_CODE_OAUTH_TOKEN;
      changed = true;
    }
  }
  if (MANAGED_CLAUDE_GATEWAY_RE.test(String(settingsEnv.ANTHROPIC_BASE_URL ?? '').trim())) {
    delete settingsEnv.ANTHROPIC_BASE_URL;
    changed = true;
  }
  let restoredSettings = false;
  if (changed) {
    const nextSettings = { ...settings };
    if (Object.keys(settingsEnv).length === 0) delete nextSettings.env;
    else nextSettings.env = settingsEnv;
    let writeTarget = settingsPath, targetSafe = true;
    const claudeManagedHome = pddManagedClaudeHome(env);
    try {
      if (fs.lstatSync?.(settingsPath)?.isSymbolicLink?.()) {
        const realFn = fs.realpathSync?.native ?? fs.realpathSync, statFn = fs.statSync;
        if (typeof realFn !== 'function' || typeof statFn !== 'function') targetSafe = false;
        else {
          const resolved = String(realFn.call(fs, settingsPath));
          if (!statFn.call(fs, resolved)?.isFile?.() || isPathAtOrInside(resolved, claudeManagedHome, fs)) targetSafe = false;
          else writeTarget = resolved;
        }
      }
    } catch { targetSafe = false; }
    if (!targetSafe) {
      throw new CloudAccountsError(
        `Refusing unsafe symlinked Claude settings path "${settingsPath}". Ensure ~/.claude/settings.json is a regular file (or a symlink to a regular file outside PDD-managed directories), then rerun.`,
        { code: 'symlink_refused' },
      );
    }
    try {
      writeAtomicPrivate(fs, writeTarget, `${JSON.stringify(nextSettings, null, 2)}\n`);
      restoredSettings = true;
    } catch (err) {
      if (err?.code !== 'EACCES' && err?.code !== 'EROFS' && err?.code !== 'EPERM') throw err;
    }
  }
  return { settingsPath, managedPath, removedManagedSettings, restoredSettings };
}

export function buildClaudeStepEnv(baseEnv = process.env, lease, ports = {}) {
  const fs = ports?.fs ?? nativeFs;
  const out = {};
  for (const [k, v] of Object.entries(baseEnv ?? {})) if (typeof v === 'string') out[k] = v;
  for (const k of ['CLAUDE_CODE_OAUTH_TOKEN', 'ANTHROPIC_API_KEY', 'ANTHROPIC_AUTH_TOKEN', 'CLAUDE_CODE_USE_BEDROCK', 'CLAUDE_CODE_USE_VERTEX', 'CLAUDE_CODE_USE_FOUNDRY']) delete out[k];
  const token = String(lease?.claude_oauth_token || lease?.gateway_bearer_token || '').trim();
  if (token) { rememberSecrets(token); out.CLAUDE_CODE_OAUTH_TOKEN = token; }
  if (lease?.delivery_mode === 'gateway_grant') {
    out.ANTHROPIC_BASE_URL = validateClaudeGatewayUrl(lease.anthropic_base_url);
  } else {
    delete out.ANTHROPIC_BASE_URL;
    const settings = readJsonObject(fs, localClaudePaths(baseEnv).settingsPath);
    if (String(settings?.env?.ANTHROPIC_BASE_URL ?? '').trim()) out.ANTHROPIC_BASE_URL = 'https://api.anthropic.com';
  }
  return out;
}
