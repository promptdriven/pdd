# Cloud accounts and login pool

Own `src/login-pool.mjs`. Export the Cloud Accounts client, local `0600` lease
materializers, disposable `0700` Codex step overlay, Stick-Until-100% and
burst-`429` classifiers, and internal multi-harness fallback helpers:
`resolveCloudAccountsEndpoint(env)`,
`resolveCloudAccountsToken({cwd, env}, ports)`,
`cloudAccountsRequest(method, path, options, ports)`,
`listCloudAccounts({refresh, cwd, env, timeoutMs}, ports)`,
`accountsStatePath(env)`,
`readCloudAccountsState({env}, ports)`,
`writeCloudAccountsState(state, {env}, ports)`,
`isCloudAccountsActive({env, poolPath, provider}, ports)`,
`stripCodexAuthBundle(authJson)`,
`localCodexConfigPath(env)`,
`materializeLocalCodexAuth(authOrLease, {env, previousManagedCodexGateway, previousCodexModelProvider}, ports)`,
`restoreLocalCodexGatewayConfig({env, previousModelProvider, removeAuthFile}, ports)`,
`materializeLocalClaudeAuth(lease, {env, previousManagedBaseUrl}, ports)`,
`createCodexStepOverlay(authOrLease, {env, tmpRoot}, ports)`,
`buildClaudeStepEnv(baseEnv, lease)`,
`prepareCloudStepExecution(lease, baseEnv, ports)`,
`classifyRateLimitFailure(text, usageWindows)`,
`extractRateLimitReport(text, accountOrWindows)`,
`reportCloudAccountUsage(accountId, report, {cwd, env, timeoutMs}, ports)`,
`leaseCloudAccount(request, {cwd, env, timeoutMs}, ports)`,
`isCreditOrResetAccount(entry)`,
`selectCloudPoolLogin(options, ports)`,
`exhaustCloudPoolLogin(options, ports)`,
`resolvePoolPath({env, poolPath})`,
`loadLoginPool({cwd, env, poolPath, fallbackAgent}, ports)`,
`loginEnvironment(baseEnv, login)`, `isQuotaExhaustionMessage(text)`,
`readPoolCooldowns({stateRoot, now}, ports)`,
`markLoginExhausted({stateRoot, loginId, resetAt, reason, now}, ports)`,
`clearPoolCooldowns({stateRoot}, ports)` and
`selectPoolLogin({cwd, env, poolPath, pool, fallbackAgent, stateRoot, allowLimited, allowCredits, allowedKinds}, ports)`.

## Domain decisions

- **Zero borrower credentials for shared Codex (`gateway_grant`):** Shared Codex leases never deliver OpenAI `access_token`, `id_token` or `refresh_token` to borrower machines. Step overlays route Codex through `pdd_codex_gateway` using an environment header (`PDD_CODEX_GATEWAY_GRANT`) with zero `auth.json` inside `/tmp/pdd-cx-*`, while local `~/.codex/` materialization writes only the short-lived revocable `pddg_*` grant as an API-key stub alongside `[model_providers.pdd_codex_gateway]` so `codex login status`, terminal `codex`, Herdr chats and workflows succeed and revoke immediately on `unshare`, `pause` or `remove`.
- **Single-refresh invariant for owner passes (`direct_stripped`):** Owner Codex leases deliver short-lived `access_token` and `id_token` with `tokens.refresh_token: ""` so only PDD Cloud refreshes single-use OpenAI refresh tokens. Switching from a shared Codex gateway lease back to an owner pass or leaving/removing the active shared account restores `~/.codex/config.toml` without losing user settings such as `[mcp_servers.pdd]`.
- **Opt-in live usage refresh (`listCloudAccounts`):** `listCloudAccounts({refresh = false, cwd, env, timeoutMs}, ports)` requests `GET /v1/accounts?refresh=true` only when `refresh === true` (human `pdd accounts` / `pdd accounts list`), keeping `GET /v1/accounts` fast for internal health and step checks.

## Cloud Accounts transport and single-refresh invariant

Cloud Accounts uses `PDD_ACCOUNTS_URL || PDD_CLOUD_URL ||
"https://pdd-byok-api-c437voydwa-uc.a.run.app"` (`https:` required except loopback `127.0.0.1`,
`localhost`, `[::1]`; never falls back to `PDD_RUNTIME_URL`),
`Authorization: Bearer <token>` (`PDD_TOKEN`, `PDD_ACCOUNTS_TOKEN`, `GH_TOKEN`,
`GITHUB_TOKEN`, or `gh auth token`), and `X-PDD-Machine-Id`. Unwrap FastAPI
`HTTPException` `detail` envelopes (`{"detail": {"error": ..., "message": ...}}`,
string `detail`, and validation-error arrays) alongside top-level `error`/`message`.
Every credential read or leased (including `codex_gateway_token` and `gateway_bearer_token`)
is registered with `rememberSecrets` from `src/secret-redaction.mjs` and is never printed or
logged. Zero usage-reset credit fields, endpoints or calls exist.

- Local cache (`${PDD_STATE_DIR || XDG_STATE_HOME || ~/.local/state}/pdd/accounts-state.json`,
  mode `0600`, atomic rename) stores only non-secret active lease metadata
  (`enrolled`, `providers`, per-provider `account_id`, `label`, `lease_id`, `expires_at`,
  `delivery_mode`, `anthropic_base_url`, `managed_anthropic_base_url`,
  `codex_gateway_url`, `managed_codex_gateway`, `previous_codex_model_provider`,
  `five_hour_used_percent`, `five_hour_reset_at`, `weekly_used_percent`,
  `weekly_reset_at`) — never `refresh_token`, `access_token`, OAuth tokens or `pddg_*` grants.
  `isCloudAccountsActive({env, poolPath, provider})` returns `false` when an explicit
  `poolPath` is supplied, when `provider` is neither `"codex"` nor `"claude"`, when
  `!saved.enrolled`, or when `provider` is passed and absent from `saved.providers`;
  `selectCloudPoolLogin` only leases providers present in `saved.providers`.
- `stripCodexAuthBundle`, `materializeLocalCodexAuth` and `restoreLocalCodexGatewayConfig`
  refuse symlinks on `~/.codex` (or `$CODEX_HOME`), `auth.json` and `config.toml`:
  - When `authOrLease.delivery_mode === "gateway_grant"`, `materializeLocalCodexAuth` validates
    `codex_gateway_url` (`https:` or loopback `http:`) and `codex_gateway_token || gateway_bearer_token`,
    atomically writes `0600` `auth.json` with `{"auth_mode": "apikey", "OPENAI_API_KEY": "<pddg_grant>"}`,
    and atomically updates `0600` `config.toml` (parsed and round-trip verified with
    `./vendor/smol-toml/parse.js`, preserving `[mcp_servers.pdd]` and all other user keys/tables)
    to set `model_provider = "pdd_codex_gateway"` (recording any prior non-`pdd_codex_gateway`
    `model_provider`) and `[model_providers.pdd_codex_gateway]` (`name = "PDD Codex Gateway"`,
    `base_url = "<codex_gateway_url>"`, `wire_api = "responses"`, `requires_openai_auth = false`,
    `supports_websockets = false`, `http_headers = {"x-pdd-gateway-grant": "<pddg_grant>"}`).
  - For owner `direct_stripped` bundles, `materializeLocalCodexAuth` writes `0600` `auth.json`
    with `tokens.refresh_token: ""` and, when `previousManagedCodexGateway` is true or
    `config.toml` carries `pdd_codex_gateway`, calls `restoreLocalCodexGatewayConfig` to remove
    `[model_providers.pdd_codex_gateway]` and restore `previousCodexModelProvider` (or remove
    `model_provider = "pdd_codex_gateway"`). `restoreLocalCodexGatewayConfig` with
    `removeAuthFile: true` also removes a `pddg_*` API-key `auth.json` when leaving or removing
    the active shared Codex account with no replacement.
- `materializeLocalClaudeAuth` atomically merges `env.CLAUDE_CODE_OAUTH_TOKEN`
  into `~/.claude/settings.json` (or `$CLAUDE_CONFIG_DIR/settings.json`, mode `0600`),
  sets `env.ANTHROPIC_BASE_URL` when `delivery_mode === "gateway_grant"`, removes a
  previously managed `/v1/accounts/claude-gateway` (or `/v1/claude-gateway`)
  `ANTHROPIC_BASE_URL` when switching back to `direct_oauth`, and writes
  `hasCompletedOnboarding: true` in `~/.claude.json` (mode `0600`).

## Disposable step isolation and Stick-Until-100%

- **Codex step overlay (`createCodexStepOverlay` & `prepareCloudStepExecution`):** Allocates a
  disposable `0700` directory atomically via `mkdtempSync(join(rootDir, 'pdd-cx-'))`,
  registers in-process overlays in an `exit`/`SIGINT`/`SIGTERM` cleanup `Set`, and removes
  `<overlay>` on step exit (`0` tokens in `ps`, never clobbering concurrent terminal sessions):
  - For owner `direct_stripped` passes, symlinks existing non-symlink
    `~/.codex/{config.toml,skills,memories,sessions,rules}`, writes leased stripped
    `auth.json` (`0600`, `refresh_token: ""`), and sets `CODEX_HOME=<overlay>`.
  - For shared `gateway_grant` leases, writes **no `auth.json`** in `<overlay>`, symlinks only
    existing non-symlink `~/.codex/{skills,memories,sessions,rules}` (never `auth.json` or
    `config.toml`), parses `~/.codex/config.toml` when it is a regular non-symlink file to
    preserve user settings such as `[mcp_servers.pdd]`, writes `0600` `<overlay>/config.toml`
    with `model_provider = "pdd_codex_gateway"`, `[features]` merged with `shell_snapshot = false`,
    `[shell_environment_policy]` merged with `filters = {"PDD_CODEX_GATEWAY_GRANT": "exclude"}`,
    and `[model_providers.pdd_codex_gateway]` (`name = "PDD Codex Gateway"`,
    `base_url = "<codex_gateway_url>"`, `wire_api = "responses"`, `requires_openai_auth = false`,
    `supports_websockets = false`, `env_http_headers = {"x-pdd-gateway-grant": "PDD_CODEX_GATEWAY_GRANT"}`
    with no static `http_headers`), sets `CODEX_HOME=<overlay>` and
    `PDD_CODEX_GATEWAY_GRANT=<grant>` in `step.env`, and deletes `OPENAI_API_KEY`,
    `CODEX_API_KEY`, `CODEX_ACCESS_TOKEN` and `OPENAI_BASE_URL`.
- **Claude step env (`buildClaudeStepEnv` & `loginEnvironment`):** `loginEnvironment`
  strips ambient `CLAUDE_CODE_OAUTH_TOKEN`, `PDD_CODEX_GATEWAY_GRANT` and managed
  `/v1/accounts/claude-gateway` `ANTHROPIC_BASE_URL` before applying profile settings so
  other profiles never inherit ambient grants; `buildClaudeStepEnv` injects leased
  `CLAUDE_CODE_OAUTH_TOKEN` (and `ANTHROPIC_BASE_URL` when `delivery_mode === "gateway_grant"`).
- **Stick-Until-100% (`selectCloudPoolLogin`, `exhaustCloudPoolLogin`, `reportCloudAccountUsage`):**
  Cloud accounts never stop at `97%`. They stay on `current_account_id` (`0` switches)
  until `five_hour_used_percent >= 100` or `weekly_used_percent >= 100` (or a quota
  exhaustion error), skip local `readCodexUsageWindows` / `readCodexLimits` probes when
  `lease.delivery_mode === "gateway_grant"`, normalize reported usage percents to integers `0..100`
  (`v >= 100 ? 100 : Math.max(0, Math.floor(v))`), POST `/v1/accounts/{account_id}/usage-report`
  with `limit_reached: true`, and lease the next ready account (`soonest weekly_reset_at`)
  with `0` issue strikes.
- **Burst `429` vs quota exhaustion (`classifyRateLimitFailure`):** A transient
  burst rate limit (`429 Too Many Requests`, `rate_limit_exceeded`, RPM/TPM) with no
  hard quota-exhaustion marker while known `5h < 100%` and `7d < 100%` returns
  `"burst_rate_limit"` so callers retry briefly on the same account to keep the
  prompt cache warm before rotating. Hard window/quota exhaustion returns
  `"quota_exhausted"`.
- **`all_cooling`:** When `/v1/accounts/lease` returns `{state: "all_cooling", wake_at}`,
  `selectCloudPoolLogin` returns `{state: "exhausted", cloud: true, resetAt, wakeAt: wake_at}`
  so Autopilot reports `Waiting on AI quota until <wake_at>` and auto-wakes at `wake_at`.
- **Credit and reset-flagged account guard (`isCreditOrResetAccount`):** Both
  `selectCloudPoolLogin` and `selectPoolLogin` default `allowCredits = false` for
  automated Autopilot steps and skip any account or `pool.json` login entry explicitly
  flagged `credits: true`, `allowReset: true` or `allow_reset: true` (recording reason
  `"credit_or_reset_guarded"` in `unavailable`), unless a human CLI command explicitly
  passes `allowCredits: true`.

## Internal local-folder pool fallback

For internal test fixtures and explicit local `pool.json` configurations, preserve
`resolvePoolPath`, `loadLoginPool` (`reset: "never"`, `weeklyStopPercent` default `97`,
optional boolean `credits`, `allowReset` / `allow_reset`),
`loginEnvironment`, `readPoolCooldowns`, `markLoginExhausted`, `clearPoolCooldowns`
and `selectPoolLogin`.

## Dependencies

- [Read Codex account limits](codex-limits.prompt.md) supplies the read-only
  primary/weekly rate-limit and usage-window checks.
- [Agent adapters](agent-adapters.prompt.md) and
  [workflow agents](workflow-agents.prompt.md) supply local CLI sign-in probes.
- [Secret redaction](secret-redaction.prompt.md) supplies `rememberSecrets` and
  `knownSecretValues`.
