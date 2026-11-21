// Generated from prompts/cli/login-pool.prompt.md.
// Layer-1 pure pool environment isolation constants and classifiers shared by Cloud and local pools.

export const KINDS = Object.freeze(['codex', 'claude', 'gemini', 'agy']);
export const CLOUD_PROVIDERS = Object.freeze(['codex', 'claude']);
export const CONFIG_VAR = Object.freeze({
  codex: 'CODEX_HOME',
  claude: 'CLAUDE_CONFIG_DIR',
  gemini: 'GEMINI_CLI_HOME',
  agy: 'ANTIGRAVITY_APP_DATA_DIR',
});
export const FOLDER_KEY = Object.freeze({
  codex: 'codexHome',
  claude: 'claudeConfigDir',
  gemini: 'geminiCliHome',
  agy: 'appDataDir',
});
export const ALL_CONFIG_VARS = Object.freeze(Object.values(CONFIG_VAR));
export const ALL_FOLDER_KEYS = Object.freeze([...Object.values(FOLDER_KEY), 'configHome']);
export const MANAGED_CLAUDE_GATEWAY_RE = /\/v1\/(?:accounts\/)?claude-gateway(?:\/|$)/i;
export const POOL_FALLBACK_COOLDOWN_MS = 30 * 60 * 1000;

/**
 * Return `true` when an account or local pool entry is flagged as credit-spending or reset-spending.
 */
export function isCreditOrResetAccount(entry) {
  return Boolean(entry?.credits === true || entry?.allowReset === true || entry?.allow_reset === true);
}

/**
 * Build an isolated child environment for one login entry, stripping cross-provider config vars,
 * ambient gateway grants, and PDD-managed Claude gateway URLs before applying login overrides.
 */
export function loginEnvironment(baseEnv = process.env, login) {
  const out = {};
  for (const [k, v] of Object.entries(baseEnv ?? {})) {
    if (typeof v === 'string') out[k] = v;
  }
  for (const key of [...ALL_CONFIG_VARS, 'CLAUDECODE', 'CLAUDE_CODE_OAUTH_TOKEN', 'PDD_CODEX_GATEWAY_GRANT']) {
    delete out[key];
  }
  if (MANAGED_CLAUDE_GATEWAY_RE.test(String(out.ANTHROPIC_BASE_URL ?? ''))) {
    delete out.ANTHROPIC_BASE_URL;
  }
  if (login?.configVar && login?.configDir) out[login.configVar] = login.configDir;
  for (const [k, v] of Object.entries(login?.env ?? {})) {
    if (typeof v === 'string') out[k] = v;
  }
  return out;
}
