// Generated from prompts/cli/login-pool.prompt.md.
// Isolated per-step Codex/Claude overlays and prepareCloudStepExecution.
import { randomBytes } from 'node:crypto';
import * as nativeFs from 'node:fs';
import { join, resolve } from 'node:path';
import { writeAtomicPrivate } from '../shared/atomic-fs.mjs';
import { resolvePddStateBase } from '../shared/state-dir.mjs';
import {
  buildClaudeStepEnv,
  createClaudeStepSettingsOverlay,
  registerOverlayCleanup,
  unregisterOverlayCleanup,
} from './claude-config.mjs';
import { CloudAccountsError } from './cloud-error.mjs';
import { localCodexHome, pddManagedCodexHome, stripCodexAuthBundle } from './cloud-state.mjs';
import {
  buildCodexGatewayFeaturePatch,
  buildCodexGatewayProviderBlock,
  buildGatewayAuthJson,
  isEmbeddedLeaseGatewayGrant,
  REQUIRED_CODEX_SUBSHELL_EXCLUDES,
  resolveCodexGatewayEndpoints,
  resolveEffectiveSqliteHome,
} from './codex-config.mjs';
import { syncManagedCodexHomeLinks } from './codex-home.mjs';
import { remapCodexHomeConfigObject, resolveUserCodexConfigTarget } from './codex-mirror.mjs';
import { loginEnvironment } from './pool-env.mjs';
import {
  CODEX_GATEWAY_PROVIDER_ID,
  isTomlTable,
  readCodexTomlObject,
  serializeTomlConfig,
  stripGatewayFromTomlObject,
} from './toml-codec.mjs';

const object = x => x !== null && typeof x === 'object' && !Array.isArray(x);

function buildOverlayShellEnvPolicy(baseConfig) {
  const prevPolicy = isTomlTable(baseConfig.shell_environment_policy) ? { ...baseConfig.shell_environment_policy } : {};
  const hadExistingFilters = isTomlTable(prevPolicy.filters);
  const prevFilters = hadExistingFilters ? { ...prevPolicy.filters } : {};
  const hasFilterIgnoreCase = key => Object.keys(prevFilters).some(k => k.toLowerCase() === key.toLowerCase());
  if (Array.isArray(prevPolicy.exclude)) {
    for (const item of prevPolicy.exclude) {
      if (typeof item === 'string' && item.trim() && !hasFilterIgnoreCase(item.trim())) prevFilters[item.trim()] = 'exclude';
    }
  }
  if (Array.isArray(prevPolicy.include_only)) {
    if (!hadExistingFilters && !prevPolicy.inherit) prevPolicy.inherit = 'none';
    for (const item of prevPolicy.include_only) {
      if (typeof item === 'string' && item.trim() && !hasFilterIgnoreCase(item.trim())) prevFilters[item.trim()] = 'include';
    }
  }
  delete prevPolicy.exclude;
  delete prevPolicy.include_only;
  const requiredLowerSet = new Set(REQUIRED_CODEX_SUBSHELL_EXCLUDES.map(k => k.toLowerCase()));
  for (const k of Object.keys(prevFilters)) if (requiredLowerSet.has(k.toLowerCase())) delete prevFilters[k];
  if (isTomlTable(prevPolicy.set)) {
    const nextSet = { ...prevPolicy.set };
    for (const k of Object.keys(nextSet)) if (requiredLowerSet.has(k.toLowerCase())) delete nextSet[k];
    if (Object.keys(nextSet).length > 0) prevPolicy.set = nextSet;
    else delete prevPolicy.set;
  }
  for (const key of REQUIRED_CODEX_SUBSHELL_EXCLUDES) prevFilters[key] = 'exclude';
  prevPolicy.filters = prevFilters;
  return prevPolicy;
}

export function createCodexStepOverlay(authOrLease, { env = process.env, tmpRoot, detached = false } = {}, ports = {}) {
  const fs = ports.fs ?? nativeFs;
  const sourceCodexHome = localCodexHome(env), managedHome = pddManagedCodexHome(env);
  const isGateway = object(authOrLease) && authOrLease.delivery_mode === 'gateway_grant';
  const endpoints = isGateway ? resolveCodexGatewayEndpoints(authOrLease, { requireGatewayUrl: true }) : null;
  const rootDir = tmpRoot
    || (typeof env?.PDD_CODEX_RUNTIME_ROOT === 'string' && env.PDD_CODEX_RUNTIME_ROOT.trim())
    || join(resolvePddStateBase(env), 'codex-runtime');
  fs.mkdirSync(rootDir, { recursive: true, mode: 0o700 });
  try { (fs.chmodSync ?? nativeFs.chmodSync)(rootDir, 0o700); } catch {}
  let overlayDir;
  if (typeof fs.mkdtempSync === 'function') overlayDir = fs.mkdtempSync(join(rootDir, 'pdd-cx-'));
  else if (fs === nativeFs) overlayDir = nativeFs.mkdtempSync(join(rootDir, 'pdd-cx-'));
  else { overlayDir = join(rootDir, `pdd-cx-${randomBytes(8).toString('hex')}`); fs.mkdirSync(overlayDir, { recursive: false, mode: 0o700 }); }
  try { (fs.chmodSync ?? nativeFs.chmodSync)(overlayDir, 0o700); } catch {}

  let cleaned = false;
  const cleanup = () => {
    if (cleaned) return;
    cleaned = true;
    unregisterOverlayCleanup(cleanup);
    try { (fs.rmSync ?? nativeFs.rmSync)(overlayDir, { recursive: true, force: true }); } catch {}
  };
  if (!detached) registerOverlayCleanup(cleanup);

  const resolvedSourceCodexHome = resolve(sourceCodexHome);
  try {
    syncManagedCodexHomeLinks(fs, sourceCodexHome, overlayDir, [managedHome]);
    const srcConfigPath = join(resolvedSourceCodexHome, 'config.toml');
    const resolvedSrcCfg = resolveUserCodexConfigTarget(fs, srcConfigPath, [overlayDir, managedHome], { strict: false });
    if (isGateway) {
      const { grantToken: gatewayToken, gatewayUrl, backendApiUrl, codexApiUrl, nativeBackendApi, embeddedLeaseGrant } = endpoints;
      const rawBaseConfig = resolvedSrcCfg.exists && resolvedSrcCfg.readPath ? readCodexTomlObject(fs, resolvedSrcCfg.readPath, { strict: false }).data : {};
      const baseConfig = remapCodexHomeConfigObject(
        stripGatewayFromTomlObject(rawBaseConfig).nextData,
        { userCodexHome: resolvedSourceCodexHome, runtimeCodexHome: overlayDir, env, fs },
      );
      const prevPolicy = buildOverlayShellEnvPolicy(baseConfig);
      const prevProviders = isTomlTable(baseConfig.model_providers) ? { ...baseConfig.model_providers } : {};
      delete prevProviders[CODEX_GATEWAY_PROVIDER_ID];
      const configPath = join(overlayDir, 'config.toml');
      const effectiveOverlaySqliteHome = resolveEffectiveSqliteHome({ userCodexHome: resolvedSourceCodexHome, parsedConfig: baseConfig, env });
      const features = buildCodexGatewayFeaturePatch(baseConfig.features, { nativeBackendApi, includeShellSnapshot: true });
      const providerBlock = buildCodexGatewayProviderBlock({
        codexApiUrl,
        nativeBackendApi,
        embeddedLeaseGrant,
        grantToken: gatewayToken,
        headerMode: 'env',
      });
      if (embeddedLeaseGrant) {
        const overlayConfig = {
          ...baseConfig,
          cli_auth_credentials_store: 'file',
          openai_base_url: codexApiUrl,
          chatgpt_base_url: backendApiUrl,
          ...(effectiveOverlaySqliteHome ? { sqlite_home: effectiveOverlaySqliteHome } : {}),
          features,
          shell_environment_policy: prevPolicy,
          model_providers: { ...prevProviders, [CODEX_GATEWAY_PROVIDER_ID]: providerBlock },
        };
        delete overlayConfig.model_provider;
        const authPath = join(overlayDir, 'auth.json');
        writeAtomicPrivate(fs, configPath, serializeTomlConfig(overlayConfig, configPath));
        writeAtomicPrivate(fs, authPath, `${JSON.stringify(buildGatewayAuthJson({ grantToken: gatewayToken, planType: authOrLease?.plan_type ?? authOrLease?.plan, now: ports.now ?? Date.now }), null, 2)}\n`);
        return { overlayDir, authPath, configPath, gatewayToken, gatewayUrl, backendApiUrl, cleanup };
      }
      const overlayConfig = {
        ...baseConfig,
        model_provider: CODEX_GATEWAY_PROVIDER_ID,
        ...(effectiveOverlaySqliteHome ? { sqlite_home: effectiveOverlaySqliteHome } : {}),
        features,
        shell_environment_policy: prevPolicy,
        model_providers: { ...prevProviders, [CODEX_GATEWAY_PROVIDER_ID]: providerBlock },
      };
      writeAtomicPrivate(fs, configPath, serializeTomlConfig(overlayConfig, configPath));
      return { overlayDir, authPath: null, configPath, gatewayToken, gatewayUrl, backendApiUrl, cleanup };
    }
    if (resolvedSrcCfg.exists) { try { fs.symlinkSync(srcConfigPath, join(overlayDir, 'config.toml')); } catch {} }
    const authPath = join(overlayDir, 'auth.json');
    writeAtomicPrivate(fs, authPath, `${JSON.stringify(stripCodexAuthBundle(authOrLease), null, 2)}\n`);
    return { overlayDir, authPath, cleanup };
  } catch (error) {
    cleanup();
    throw error;
  }
}

export function prepareCloudStepExecution(leaseReply, baseEnv = process.env, ports = {}, { detached = false, userSettings = null } = {}) {
  const provider = leaseReply?.account?.provider, lease = leaseReply?.lease;
  const cleanBase = loginEnvironment(baseEnv, { kind: provider || 'codex' });
  if (provider === 'codex') {
    const scrubCodexAmbientEnv = targetEnv => {
      for (const k of ['OPENAI_API_KEY', 'CODEX_API_KEY', 'CODEX_ACCESS_TOKEN', 'CODEX_CONNECTORS_TOKEN', 'OPENAI_BASE_URL', 'PDD_CODEX_GATEWAY_GRANT']) delete targetEnv[k];
      return targetEnv;
    };
    if (lease?.delivery_mode === 'gateway_grant') {
      const overlay = createCodexStepOverlay({
        ...lease,
        plan_type: lease?.plan_type ?? leaseReply?.account?.plan_type ?? leaseReply?.account?.plan,
      }, { env: baseEnv, tmpRoot: ports.tmpRoot, detached }, ports);
      const env = scrubCodexAmbientEnv({ ...cleanBase, CODEX_HOME: overlay.overlayDir, PDD_CLOUD_STEP_ISOLATED: '1' });
      if (!isEmbeddedLeaseGatewayGrant(overlay.gatewayToken)) env.PDD_CODEX_GATEWAY_GRANT = overlay.gatewayToken;
      return { env, cleanupDirs: [overlay.overlayDir], cleanup: overlay.cleanup, overlayDir: overlay.overlayDir };
    }
    if (!object(lease?.codex_auth_json)) throw new CloudAccountsError('Cloud lease returned no Codex auth bundle.', { code: 'invalid_lease' });
    const overlay = createCodexStepOverlay(lease.codex_auth_json, { env: baseEnv, tmpRoot: ports.tmpRoot, detached }, ports);
    return { env: scrubCodexAmbientEnv({ ...cleanBase, CODEX_HOME: overlay.overlayDir, PDD_CLOUD_STEP_ISOLATED: '1' }), cleanupDirs: [overlay.overlayDir], cleanup: overlay.cleanup, overlayDir: overlay.overlayDir };
  }
  if (provider === 'claude') {
    const env = { ...buildClaudeStepEnv(cleanBase, lease, ports), PDD_CLOUD_STEP_ISOLATED: '1' };
    if (Boolean(String(lease?.claude_oauth_token || lease?.gateway_bearer_token || '').trim())) {
      const overlay = createClaudeStepSettingsOverlay(lease, { env: baseEnv, tmpRoot: ports.tmpRoot, userSettings, detached }, ports);
      return { env, extraArgs: ['--settings', overlay.settingsPath], settingsPath: overlay.settingsPath, cleanupDirs: [overlay.overlayDir], cleanup: overlay.cleanup, overlayDir: overlay.overlayDir };
    }
    return { env, extraArgs: [], settingsPath: null, cleanupDirs: [], cleanup: () => {}, overlayDir: null };
  }
  return { env: cleanBase, extraArgs: [], settingsPath: null, cleanupDirs: [], cleanup: () => {}, overlayDir: null };
}
