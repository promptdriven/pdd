// Generated from prompts/cli/login-pool.prompt.md.
// Thin compatibility facade for the accounts & cloud login pool subsystem under src/accounts/.
import * as codexLimitsModule from './codex-limits.mjs';
import { parse as parseToml } from './vendor/smol-toml/parse.js';
import { registerTomlParser } from './accounts/toml-codec.mjs';

registerTomlParser(parseToml);

export { CloudAccountsError } from './accounts/cloud-error.mjs';
export { POOL_FALLBACK_COOLDOWN_MS, isCreditOrResetAccount, loginEnvironment } from './accounts/pool-env.mjs';
export { resolvePddStateBase } from './shared/state-dir.mjs';

export const readCodexUsageWindows = (...args) => (codexLimitsModule.readCodexUsageWindows ?? codexLimitsModule.readCodexLimits)(...args);

export {
  DEFAULT_CLOUD_URL,
  classifyRateLimitFailure,
  cloudAccountsRequest,
  extractRateLimitReport,
  heartbeatCloudLease,
  isAuthFailureMessage,
  isExplicitReauthCodeFailure,
  isGatewayGrantRevokedFailure,
  isLocalReauthUnresolved,
  isQuotaExhaustionMessage,
  isReauthRequiredAccount,
  isReauthRequiredFailure,
  listCloudAccounts,
  normalizeUsagePercentInt,
  releaseCloudLease,
  reportCloudAccountUsage,
  resolveCloudAccountsEndpoint,
  resolveCloudAccountsToken,
} from './accounts/cloud-client.mjs';

export {
  accountsStatePath,
  claudeTokenFingerprint,
  isCloudAccountsActive,
  localClaudePaths,
  localCodexAuthPath,
  localCodexHome,
  localCodexConfigPath,
  managedClaudeSettingsPath,
  managedCodexAuthPath,
  managedCodexConfigPath,
  markLocalAccountReauthRequired,
  pddManagedClaudeHome,
  pddManagedCodexHome,
  readCloudAccountsState,
  saveActiveLeaseMetadata,
  stripCodexAuthBundle,
  writeCloudAccountsState,
} from './accounts/cloud-state.mjs';

export {
  REQUIRED_CODEX_SUBSHELL_EXCLUDES,
  buildCodexGatewayCliArgs,
  buildCodexGatewayFeaturePatch,
  buildCodexGatewayProviderBlock,
  buildGatewayAuthJson,
  buildSyntheticGatewayIdToken,
  resolveCodexBackendApiUrl,
  resolveCodexGatewayEndpoints,
  resolveCodexResponsesBaseUrl,
  resolveEffectiveSqliteHome,
  stripCodexCliEnvExcludeArgs,
} from './accounts/codex-config.mjs';

export {
  buildCodexHomeMirrorCliArgs,
  ensureUserCodexHomeBaseline,
  isIsolatedCodexHomeEntry,
  needsCodexConfigWritebackNormalization,
  normalizeCodexConfigWriteback,
} from './accounts/codex-mirror.mjs';

export {
  isSafeCodexSourceEntry,
  materializeLocalCodexAuth,
  restoreLocalCodexGatewayConfig,
  stopCodexAppServerDaemon,
  syncManagedCodexHomeLinks,
} from './accounts/codex-home.mjs';

export {
  buildClaudeGatewaySettingsOverlay,
  buildClaudeStepEnv,
  createClaudeStepSettingsOverlay,
  materializeLocalClaudeAuth,
  restoreLocalClaudeGatewayConfig,
  sweepActiveCodexOverlays,
} from './accounts/claude-config.mjs';

export {
  createCodexStepOverlay,
  prepareCloudStepExecution,
} from './accounts/step-overlay.mjs';

export {
  exhaustCloudPoolLogin,
  leaseCloudAccount,
  selectCloudPoolLogin,
} from './accounts/cloud-leases.mjs';
