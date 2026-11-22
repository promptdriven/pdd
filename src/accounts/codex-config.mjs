// Generated from prompts/cli/login-pool.prompt.md.
// Single canonical builder (#3531) for Codex gateway URLs, WebSocket feature flags,
// provider blocks, CLI `-c` overrides, subshell excludes, and gateway auth payloads.
import * as nativeFs from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { rememberSecrets } from '../secret-redaction.mjs';
import { CloudAccountsError } from './cloud-error.mjs';
import { buildCodexHomeMirrorCliArgs, canonicalizeCodexPath } from './codex-mirror.mjs';
import { formatTomlKey, formatTomlValue, isTomlTable, parseCodexTomlQuiet, readCodexTomlQuiet } from './toml-codec.mjs';

export const REQUIRED_CODEX_SUBSHELL_EXCLUDES = Object.freeze([
  'PDD_*',
  'PDD_TOKEN',
  'PDD_ACCOUNTS_TOKEN',
  'PDD_CODEX_GATEWAY_GRANT',
  'OPENAI_API_KEY',
  'CODEX_API_KEY',
  'CODEX_ACCESS_TOKEN',
  'CODEX_CONNECTORS_TOKEN',
  'CODEX_HOME',
]);

export function validateCodexGatewayUrl(rawUrl) {
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

export function resolveCodexGatewayGrant(lease) {
  const token = String(lease?.codex_gateway_token || lease?.gateway_bearer_token || '').trim();
  if (!token) throw new CloudAccountsError('Cloud lease returned no Codex gateway token.', { code: 'invalid_lease' });
  rememberSecrets(token);
  if (!token.startsWith('pddg_')) {
    throw new CloudAccountsError('Codex gateway token must start with pddg_.', { code: 'invalid_lease' });
  }
  return token;
}

export function isEmbeddedLeaseGatewayGrant(grantToken) {
  return typeof grantToken === 'string' && grantToken.startsWith('pddg_lse_');
}

export function normalizeCodexGatewayBaseUrl(validatedUrl, grantToken) {
  if (!validatedUrl) return null;
  return isEmbeddedLeaseGatewayGrant(grantToken)
    ? validatedUrl.replace(/(\/codex-gateway)\/lse_[^/]+$/i, '$1')
    : validatedUrl;
}

/**
 * Resolve the canonical `/v1/codex-gateway/backend-api` URL for a Codex Cloud lease.
 */
export function resolveCodexBackendApiUrl(authOrLease, fallbackGatewayUrl = null, { preserveLegacyBase = false } = {}) {
  const explicit = typeof authOrLease?.codex_backend_api_url === 'string' && authOrLease.codex_backend_api_url.trim()
    ? validateCodexGatewayUrl(authOrLease.codex_backend_api_url)
    : null;
  if (explicit) return explicit;
  const base = fallbackGatewayUrl
    || (typeof authOrLease?.codex_gateway_url === 'string' && authOrLease.codex_gateway_url.trim()
      ? normalizeCodexGatewayBaseUrl(validateCodexGatewayUrl(authOrLease.codex_gateway_url), resolveCodexGatewayGrant(authOrLease))
      : null);
  if (!base) return null;
  if (preserveLegacyBase) return base;
  if (/\/backend-api$/i.test(base)) return base;
  if (/\/codex-gateway$/i.test(base)) return `${base}/backend-api`;
  return base;
}

/**
 * Resolve the Codex responses/models base URL (`.../backend-api/codex`) from the backend-api root.
 */
export function resolveCodexResponsesBaseUrl(backendApiUrl) {
  if (!backendApiUrl) return null;
  return /\/backend-api$/i.test(backendApiUrl) ? `${backendApiUrl}/codex` : backendApiUrl;
}

/**
 * Single canonical #3531 Codex gateway endpoint + WebSocket mode resolver shared by
 * pdd-codex, materializeLocalCodexAuth, and createCodexStepOverlay.
 */
export function resolveCodexGatewayEndpoints(authOrLease, { fallbackGatewayUrl = null, requireGatewayUrl = false } = {}) {
  const grantToken = resolveCodexGatewayGrant(authOrLease);
  const embeddedLeaseGrant = isEmbeddedLeaseGatewayGrant(grantToken);
  const hasRawGatewayUrl = typeof authOrLease?.codex_gateway_url === 'string' && authOrLease.codex_gateway_url.trim().length > 0;
  const rawGatewayUrl = (requireGatewayUrl || hasRawGatewayUrl)
    ? validateCodexGatewayUrl(authOrLease?.codex_gateway_url)
    : null;
  const gatewayUrl = rawGatewayUrl ? normalizeCodexGatewayBaseUrl(rawGatewayUrl, grantToken) : fallbackGatewayUrl;
  const nativeBackendApi = typeof authOrLease?.codex_backend_api_url === 'string'
    && authOrLease.codex_backend_api_url.trim().length > 0;
  const backendApiUrl = nativeBackendApi
    ? resolveCodexBackendApiUrl(authOrLease, gatewayUrl)
    : resolveCodexBackendApiUrl(authOrLease, gatewayUrl, { preserveLegacyBase: true });
  const codexApiUrl = nativeBackendApi ? resolveCodexResponsesBaseUrl(backendApiUrl) : backendApiUrl;
  return { grantToken, gatewayUrl, backendApiUrl, codexApiUrl, nativeBackendApi, embeddedLeaseGrant };
}

/**
 * Build the `model_providers.pdd_codex_gateway` TOML table block with unified #3531 WebSocket policy.
 */
export function buildCodexGatewayProviderBlock({
  codexApiUrl,
  nativeBackendApi,
  embeddedLeaseGrant,
  grantToken = null,
  headerMode = 'inline',
}) {
  const base = {
    name: 'PDD Codex Gateway',
    base_url: codexApiUrl,
    model_catalog_url: `${codexApiUrl}/models`,
    wire_api: 'responses',
    requires_openai_auth: Boolean(embeddedLeaseGrant),
    ...(nativeBackendApi ? {} : { supports_websockets: false }),
  };
  if (embeddedLeaseGrant) return base;
  return headerMode === 'env'
    ? { ...base, env_http_headers: { 'x-pdd-gateway-grant': 'PDD_CODEX_GATEWAY_GRANT' } }
    : { ...base, http_headers: { 'x-pdd-gateway-grant': grantToken } };
}

/**
 * Build the `[features]` table patch with unified #3531 WebSocket/daemon flags.
 */
export function buildCodexGatewayFeaturePatch(prevFeatures = {}, { nativeBackendApi, includeShellSnapshot = false } = {}) {
  const next = isTomlTable(prevFeatures) ? { ...prevFeatures } : {};
  if (nativeBackendApi) delete next.responses_websockets;
  return {
    ...next,
    ...(includeShellSnapshot ? { shell_snapshot: false } : {}),
    ...(nativeBackendApi ? { daemon_auto_start: false } : { responses_websockets: false }),
  };
}

function parseCliConfigExcludeValue(expr) {
  const excludeMatch = /^shell_environment_policy\.exclude\s*=(.+)$/s.exec(expr);
  if (excludeMatch) {
    const parsed = parseCodexTomlQuiet(`v = ${excludeMatch[1].trim()}`);
    return { matched: true, patterns: Array.isArray(parsed?.v) ? parsed.v : [] };
  }
  const tableMatch = /^shell_environment_policy\s*=(.+)$/s.exec(expr);
  if (tableMatch) {
    const parsed = parseCodexTomlQuiet(`v = ${tableMatch[1].trim()}`);
    if (isTomlTable(parsed?.v) && Array.isArray(parsed.v.exclude)) return { matched: true, patterns: parsed.v.exclude };
  }
  return { matched: false, patterns: [] };
}

function stripExcludeFromCliEnvPolicyExpr(expr) {
  const trimmed = String(expr ?? '').trim();
  if (/^shell_environment_policy\.exclude\s*=/.test(trimmed)) return { stripped: true, replacement: null };
  const tableMatch = /^shell_environment_policy\s*=(.+)$/s.exec(trimmed);
  if (tableMatch) {
    const parsed = parseCodexTomlQuiet(`v = ${tableMatch[1].trim()}`);
    if (isTomlTable(parsed?.v) && Array.isArray(parsed.v.exclude)) {
      const rest = Object.entries(parsed.v).filter(([k]) => k !== 'exclude');
      if (rest.length === 0) return { stripped: true, replacement: null };
      return { stripped: true, replacement: `shell_environment_policy={ ${rest.map(([k, v]) => `${formatTomlKey(k)} = ${formatTomlValue(v)}`).join(', ')} }` };
    }
  }
  return { stripped: false, replacement: null };
}

export function stripCodexCliEnvExcludeArgs(codexArgs = []) {
  const args = Array.isArray(codexArgs) ? codexArgs.map(String) : [];
  const out = [];
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '--') { out.push(...args.slice(i)); break; }
    if ((arg === '-c' || arg === '--config') && typeof args[i + 1] === 'string') {
      const rewritten = stripExcludeFromCliEnvPolicyExpr(args[i + 1]);
      if (rewritten.stripped) { if (rewritten.replacement) out.push(arg, rewritten.replacement); i += 1; continue; }
      out.push(arg, args[i + 1]);
      i += 1;
      continue;
    }
    if (arg.startsWith('--config=')) {
      const rewritten = stripExcludeFromCliEnvPolicyExpr(arg.slice('--config='.length));
      if (rewritten.stripped) { if (rewritten.replacement) out.push(`--config=${rewritten.replacement}`); continue; }
    }
    out.push(arg);
  }
  return out;
}

function extractCodexCliProfileAndFlags(codexArgs = []) {
  const args = Array.isArray(codexArgs) ? codexArgs.map(String) : [];
  let profile = null, cdDir = null, hasOssFlag = false, hasLegacyCliEnvPolicy = false, cliExcludePatterns = [];
  const inspectConfigExpr = expr => {
    const parsedExclude = parseCliConfigExcludeValue(expr);
    if (parsedExclude.matched) { hasLegacyCliEnvPolicy = true; cliExcludePatterns = parsedExclude.patterns; }
    else if (/^shell_environment_policy\.include_only\s*=/.test(expr)) hasLegacyCliEnvPolicy = true;
  };
  for (let i = 0; i < args.length; i += 1) {
    const arg = args[i];
    if (arg === '--') break;
    if (arg === '--oss' || arg === '--local-provider' || arg.startsWith('--local-provider=')) hasOssFlag = true;
    if ((arg === '-C' || arg === '--cd') && typeof args[i + 1] === 'string') { cdDir = args[++i].trim() || cdDir; continue; }
    if (arg.startsWith('--cd=')) { cdDir = arg.slice('--cd='.length).trim() || cdDir; continue; }
    if ((arg === '-p' || arg === '--profile') && typeof args[i + 1] === 'string') { profile = args[++i].trim() || profile; continue; }
    if (arg.startsWith('--profile=')) { profile = arg.slice('--profile='.length).trim() || profile; continue; }
    if ((arg === '-c' || arg === '--config') && typeof args[i + 1] === 'string') { inspectConfigExpr(args[++i].trim()); continue; }
    if (arg.startsWith('--config=')) inspectConfigExpr(arg.slice('--config='.length).trim());
  }
  return { profile, cdDir, hasOssFlag, hasLegacyCliEnvPolicy, cliExcludePatterns };
}

function collectProjectCodexConfigDocs(fs, startDir, userCodexHome = null) {
  if (typeof startDir !== 'string' || !startDir.trim()) return [];
  const canonicalUserHome = typeof userCodexHome === 'string' && userCodexHome.trim() ? canonicalizeCodexPath(fs, resolve(userCodexHome.trim())) : null;
  const chain = [];
  let dir = resolve(startDir.trim());
  for (let depth = 0; depth < 64; depth += 1) {
    chain.push(dir);
    let hasGitMarker = false;
    try { (fs?.lstatSync ?? nativeFs.lstatSync).call(fs, join(dir, '.git')); hasGitMarker = true; } catch {}
    if (hasGitMarker) break;
    const parent = dirname(dir);
    if (!parent || parent === dir) break;
    dir = parent;
  }
  const docs = [];
  for (const candidateDir of chain.reverse()) {
    const dotCodexDir = join(candidateDir, '.codex');
    if (canonicalUserHome && canonicalizeCodexPath(fs, dotCodexDir) === canonicalUserHome) continue;
    const doc = readCodexTomlQuiet(fs, join(dotCodexDir, 'config.toml'));
    if (doc) docs.push(doc);
  }
  return docs;
}

export function resolveEffectiveSqliteHome({ userCodexHome = null, userConfigText = null, parsedConfig = null, env = process.env } = {}) {
  if (typeof env?.CODEX_SQLITE_HOME === 'string' && env.CODEX_SQLITE_HOME.trim()) return null;
  const parsed = isTomlTable(parsedConfig) ? parsedConfig : parseCodexTomlQuiet(userConfigText);
  if (typeof parsed?.sqlite_home === 'string' && parsed.sqlite_home.trim()) return null;
  return typeof userCodexHome === 'string' && userCodexHome.trim() ? userCodexHome.trim() : null;
}

function buildCodexSubshellExcludeCliArgs(userConfigText = null, { includeCodexHome = false, userCodexHome = null, codexArgs = [], cwd = null, fs = nativeFs } = {}) {
  const requiredExcludes = includeCodexHome ? REQUIRED_CODEX_SUBSHELL_EXCLUDES : REQUIRED_CODEX_SUBSHELL_EXCLUDES.filter(k => k !== 'CODEX_HOME');
  const parsedUser = parseCodexTomlQuiet(userConfigText);
  const { profile: cliProfile, cdDir, hasLegacyCliEnvPolicy, cliExcludePatterns } = extractCodexCliProfileAndFlags(codexArgs);
  const activeProfile = cliProfile || (typeof parsedUser?.profile === 'string' ? parsedUser.profile.trim() : null);
  const policyLayers = [];
  if (isTomlTable(parsedUser?.shell_environment_policy)) policyLayers.push(parsedUser.shell_environment_policy);
  if (activeProfile) {
    if (isTomlTable(parsedUser?.profiles?.[activeProfile]?.shell_environment_policy)) policyLayers.push(parsedUser.profiles[activeProfile].shell_environment_policy);
    if (typeof userCodexHome === 'string' && userCodexHome.trim()) {
      const profileDoc = readCodexTomlQuiet(fs, join(resolve(userCodexHome.trim()), `${activeProfile}.config.toml`));
      if (isTomlTable(profileDoc?.shell_environment_policy)) policyLayers.push(profileDoc.shell_environment_policy);
    }
  }
  const effectiveStartDir = cdDir
    ? resolve(typeof cwd === 'string' && cwd.trim() ? cwd.trim() : process.cwd(), cdDir)
    : (typeof cwd === 'string' && cwd.trim() ? resolve(cwd.trim()) : null);
  if (effectiveStartDir) {
    for (const repoDoc of collectProjectCodexConfigDocs(fs, effectiveStartDir, userCodexHome)) {
      if (isTomlTable(repoDoc?.shell_environment_policy)) policyLayers.push(repoDoc.shell_environment_policy);
    }
  }
  const hasFiltersLayer = policyLayers.some(p => isTomlTable(p.filters));
  const hasLegacyArray = hasLegacyCliEnvPolicy || (!hasFiltersLayer && policyLayers.some(p => Array.isArray(p.exclude) || Array.isArray(p.include_only)));
  if (hasLegacyArray) {
    const merged = [], seen = new Set();
    const existingExcludes = [...policyLayers.flatMap(p => (Array.isArray(p.exclude) ? p.exclude : [])), ...cliExcludePatterns];
    for (const item of [...existingExcludes, ...requiredExcludes]) {
      const trimmed = typeof item === 'string' ? item.trim() : '';
      if (!trimmed || seen.has(trimmed.toLowerCase())) continue;
      seen.add(trimmed.toLowerCase());
      merged.push(trimmed);
    }
    return ['-c', `shell_environment_policy.exclude=${JSON.stringify(merged)}`];
  }
  const entries = requiredExcludes.map(pattern => `${formatTomlKey(pattern)} = "exclude"`);
  return ['-c', `shell_environment_policy.filters={ ${entries.join(', ')} }`];
}

export function buildCodexGatewayCliArgs({
  backendApiUrl,
  userCodexHome = null,
  runtimeCodexHome = null,
  emptySubshellCodexHome = null,
  userConfigText = null,
  nativeBackendApi = true,
  codexArgs = [],
  cwd = null,
  env = process.env,
  fs = nativeFs,
} = {}) {
  const codexApiUrl = nativeBackendApi ? resolveCodexResponsesBaseUrl(backendApiUrl) : backendApiUrl;
  const parsedUser = parseCodexTomlQuiet(userConfigText);
  const { profile: cliProfile, hasOssFlag } = extractCodexCliProfileAndFlags(codexArgs);
  const activeProfile = cliProfile || (typeof parsedUser?.profile === 'string' ? parsedUser.profile.trim() : null);
  let effectiveConfiguredProvider = typeof parsedUser?.model_provider === 'string' ? parsedUser.model_provider.trim() : '';
  if (activeProfile) {
    const inlineProfProvider = parsedUser?.profiles?.[activeProfile]?.model_provider;
    if (typeof inlineProfProvider === 'string' && inlineProfProvider.trim()) {
      effectiveConfiguredProvider = inlineProfProvider.trim();
    } else if (typeof userCodexHome === 'string' && userCodexHome.trim()) {
      const profileDoc = readCodexTomlQuiet(fs, join(resolve(userCodexHome.trim()), `${activeProfile}.config.toml`));
      if (typeof profileDoc?.model_provider === 'string' && profileDoc.model_provider.trim()) effectiveConfiguredProvider = profileDoc.model_provider.trim();
    }
  }
  const args = [
    '-c', 'cli_auth_credentials_store="file"',
    '-c', `chatgpt_base_url=${JSON.stringify(backendApiUrl)}`,
    '-c', `openai_base_url=${JSON.stringify(codexApiUrl)}`,
  ];
  if (!hasOssFlag && effectiveConfiguredProvider && effectiveConfiguredProvider !== 'openai') args.push('-c', 'model_provider="openai"');
  const effectiveSqliteHome = resolveEffectiveSqliteHome({ userCodexHome, parsedConfig: parsedUser, env });
  if (effectiveSqliteHome) args.push('-c', `sqlite_home=${JSON.stringify(effectiveSqliteHome)}`);
  args.push('-c', 'features.daemon_auto_start=false', '-c', 'features.shell_snapshot=false');
  if (!nativeBackendApi) args.push('-c', 'features.responses_websockets=false');
  const hideCodexHomeInSubshell = Boolean((typeof runtimeCodexHome === 'string' && runtimeCodexHome.trim()) || (typeof emptySubshellCodexHome === 'string' && emptySubshellCodexHome.trim()));
  args.push(
    ...buildCodexSubshellExcludeCliArgs(userConfigText, { includeCodexHome: hideCodexHomeInSubshell, userCodexHome, codexArgs, cwd, fs }),
    ...buildCodexHomeMirrorCliArgs({ userCodexHome, runtimeCodexHome, userConfigText, env, fs }),
    '-c', 'model_providers.pdd_pool.name="PDD Pool"',
    '-c', `model_providers.pdd_pool.base_url=${JSON.stringify(codexApiUrl)}`,
    '-c', 'model_providers.pdd_pool.wire_api="responses"',
    '-c', 'model_providers.pdd_pool.requires_openai_auth=true',
    '-c', 'model_providers.pdd_codex_gateway.name="PDD Codex Gateway"',
    '-c', `model_providers.pdd_codex_gateway.base_url=${JSON.stringify(codexApiUrl)}`,
    '-c', 'model_providers.pdd_codex_gateway.wire_api="responses"',
    '-c', 'model_providers.pdd_codex_gateway.requires_openai_auth=true',
  );
  if (!nativeBackendApi) {
    args.push('-c', 'model_providers.pdd_pool.supports_websockets=false', '-c', 'model_providers.pdd_codex_gateway.supports_websockets=false');
  }
  return args;
}

export function buildSyntheticGatewayIdToken({ planType } = {}) {
  const normalizedPlanType = typeof planType === 'string' && /^[A-Za-z0-9._-]{1,32}$/.test(planType.trim()) ? planType.trim().toLowerCase() : '';
  const header = Buffer.from(JSON.stringify({ alg: 'none', typ: 'JWT' }), 'utf8').toString('base64url');
  const payload = Buffer.from(JSON.stringify({
    exp: 4102444800,
    iat: 1700000000,
    'https://api.openai.com/auth': { chatgpt_account_id: 'acct_pdd_gateway', chatgpt_plan_type: normalizedPlanType || 'pro', chatgpt_user_id: 'user_pdd_gateway' },
  }), 'utf8').toString('base64url');
  return `${header}.${payload}.sig`;
}

export function buildGatewayAuthJson({ grantToken, planType = null, now = Date.now } = {}) {
  const nowFn = typeof now === 'function' ? now : Date.now;
  return {
    auth_mode: 'chatgpt',
    OPENAI_API_KEY: null,
    tokens: { id_token: buildSyntheticGatewayIdToken({ planType }), access_token: grantToken, refresh_token: '', account_id: 'acct_pdd_gateway' },
    last_refresh: new Date(nowFn()).toISOString(),
  };
}
