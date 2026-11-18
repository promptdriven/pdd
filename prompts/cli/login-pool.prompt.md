# Cloud accounts and login pool

Own `src/login-pool.mjs`. Export the Cloud Accounts client, isolated `0700`
local Codex home and `0600` lease materializers, disposable `0700` Codex step
overlay, Stick-Until-100% and burst-`429` / `reauth_required` classifiers, and
internal multi-harness fallback helpers:
`resolveCloudAccountsEndpoint(env)`,
`resolveCloudAccountsToken({cwd, env}, ports)`,
`cloudAccountsRequest(method, path, options, ports)`,
`listCloudAccounts({refresh, cwd, env, timeoutMs}, ports)`,
`accountsStatePath(env)`,
`pddManagedCodexHome(env)`,
`managedCodexAuthPath(env)`,
`managedCodexConfigPath(env)`,
`readCloudAccountsState({env}, ports)`,
`writeCloudAccountsState(state, {env}, ports)`,
`isCloudAccountsActive({env, poolPath, provider}, ports)`,
`isReauthRequiredAccount(entry)`,
`isReauthRequiredFailure(errorOrText)`,
`markLocalAccountReauthRequired(accountId, {env}, ports)`,
`stripCodexAuthBundle(authJson)`,
`localCodexHome(env)`,
`localCodexAuthPath(env)`,
`localCodexConfigPath(env)`,
`buildSyntheticGatewayIdToken({planType})`,
`stopCodexAppServerDaemon(codexHome, options)`,
`materializeLocalCodexAuth(authOrLease, {env, previousManagedCodexGateway, previousCodexModelProvider}, ports)`,
`restoreLocalCodexGatewayConfig({env, previousModelProvider, removeAuthFile}, ports)`,
`materializeLocalClaudeAuth(lease, {env, previousManagedBaseUrl}, ports)`,
`createCodexStepOverlay(authOrLease, {env, tmpRoot}, ports)`,
`buildClaudeStepEnv(baseEnv, lease)`,
`prepareCloudStepExecution(lease, baseEnv, ports)`,
`classifyRateLimitFailure(text, usageWindows)`,
`extractRateLimitReport(text, accountOrWindows)`,
`reportCloudAccountUsage(accountId, report, {cwd, env, timeoutMs}, ports)`,
`leaseCloudAccount(request, {cwd, env, timeoutMs, maxRetries}, ports)`,
`isCreditOrResetAccount(entry)`,
`selectCloudPoolLogin(options, ports)`,
`exhaustCloudPoolLogin(options, ports)`,
`resolvePoolPath({env, poolPath})`,
`loadLoginPool({cwd, env, poolPath, fallbackAgent}, ports)`,
`loginEnvironment(baseEnv, login)`, `isQuotaExhaustionMessage(text)`, `isAuthFailureMessage(text)`,
`readPoolCooldowns({stateRoot, now}, ports)`,
`markLoginExhausted({stateRoot, loginId, resetAt, reason, now}, ports)`,
`clearPoolCooldowns({stateRoot}, ports)` and
`selectPoolLogin({cwd, env, poolPath, pool, fallbackAgent, stateRoot, allowLimited, allowCredits, allowedKinds}, ports)`.

## Domain decisions

- **Isolated PDD-managed Codex home (`pddManagedCodexHome`):** Local Codex lease materialization writes exclusively inside `${PDD_STATE_DIR || join(XDG_STATE_HOME, "pdd") || ~/.local/state/pdd}/codex-home` (mode `0700`), never reading from or writing to `~/.codex/auth.json`. Plain `codex logout` or `codex login` against `~/.codex` cannot revoke PDD Cloud tokens or mutate credentials under running `codex app-server` processes, and legacy `[model_providers.pdd_codex_gateway]` entries in `~/.codex/config.toml` are cleaned up safely without touching `~/.codex/auth.json`.
- **Zero-plaintext local Codex keys (`gateway_grant` + native `"openai"` provider routing):** Both owner and shared Codex leases materialize `gateway_grant` passes (`delivery_mode: "gateway_grant"`) with zero real OpenAI `access_token`, `id_token` or `refresh_token` written to disk. Step overlays route Codex through `pdd_codex_gateway` using `PDD_CODEX_GATEWAY_GRANT` with zero `auth.json` inside `/tmp/pdd-cx-*`, while `pddManagedCodexHome(env)` keeps Codex on its native `"openai"` provider (`openai_base_url` and `chatgpt_base_url` pointed at the gateway, no top-level `model_provider`, and `[model_providers.pdd_codex_gateway]` retained solely as a compatibility alias for older saved sessions) alongside a native `chatgpt`-mode `auth.json` (`tokens.access_token` set to the short-lived revocable `pddg_*` grant, `tokens.refresh_token: ""`, `tokens.account_id: "acct_pdd_gateway"`, and a deterministic unsigned `id_token` from `buildSyntheticGatewayIdToken`). Keeping local sessions on native `"openai"` with `chatgpt` auth lets `codex resume` and `codex fork` resume sessions saved under `"openai"` (as well as older `"pdd_codex_gateway"` sessions) without sending `pddg_*` grants to `api.openai.com`, and lets `codex app-server` `account/rateLimits/read` (`/status`) read usage windows through the gateway. When the grant token embeds its lease ID (`pddg_lse_<hex>_<secret>`), normalize `codex_gateway_url` by stripping any trailing `/lse_<id>` segment to the constant `<origin>/v1/codex-gateway` base URL and omit static `http_headers` in `managedCodexConfigPath(env)` so `config.toml` stays constant across syncs and account switches. Whenever local Codex credentials in a `CODEX_HOME` are mutated or cleaned up, `stopCodexAppServerDaemon` stops any stale background `app-server-daemon` caching prior OAuth state in memory. Preserve backward compatibility for legacy non-`pddg_lse_` `pddg_*` grants and legacy `direct_stripped` responses (`tokens.refresh_token: ""` so only PDD Cloud refreshes single-use OpenAI refresh tokens).
- **Cold-start resilience and opt-in live refresh:** `cloudAccountsRequest` defaults `timeoutMs` to `20_000` ms (`gh auth token` budget up to `10_000` ms) and `listCloudAccounts` defaults `timeoutMs` to `30_000` ms, `leaseCloudAccount` defaults `timeoutMs` to `15_000` ms (enforcing `timeoutMs` as an overall wall-clock deadline across bounded `reauth_required` skip retries and `maxRetries: 0` on `--quiet` shell-hook sync), and `cloudAccountsRequest` performs `1` bounded retry on timeout/abort for idempotent `GET` and `POST /v1/accounts/lease` requests. `listCloudAccounts({refresh = false})` appends `?refresh=true` only when `refresh === true`.

## Cloud Accounts transport and isolated local materialization

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

- Local cache (`${PDD_STATE_DIR || join(XDG_STATE_HOME, "pdd") || ~/.local/state/pdd}/accounts-state.json`,
  mode `0600`, atomic rename) stores only non-secret active lease metadata
  (`enrolled`, `providers`, per-provider `account_id`, `label`, `state`, `lease_id`,
  `leased_at`, `expires_at`, `last_refresh_at`, `access_token_expires_at`,
  `delivery_mode`, `anthropic_base_url`, `managed_anthropic_base_url`,
  `codex_gateway_url`, `managed_codex_gateway`, `previous_codex_model_provider`,
  `five_hour_used_percent`, `five_hour_reset_at`, `weekly_used_percent`,
  `weekly_reset_at`) — never `refresh_token`, `access_token`, OAuth tokens or `pddg_*` grants.
  `isCloudAccountsActive({env, poolPath, provider})` returns `false` when an explicit
  `poolPath` is supplied, when `provider` is neither `"codex"` nor `"claude"`, when
  `!saved.enrolled`, or when `provider` is passed and absent from `saved.providers`;
  `selectCloudPoolLogin` only leases providers present in `saved.providers`.
- `localCodexHome(env)` resolves `~/.codex` (or custom `$CODEX_HOME` when distinct from
  `pddManagedCodexHome(env)`). `pddManagedCodexHome(env)` resolves
  `join(dirname(accountsStatePath(env)), "codex-home")` (`0700`), with
  `managedCodexAuthPath(env)` and `managedCodexConfigPath(env)`.
  `materializeLocalCodexAuth` and `restoreLocalCodexGatewayConfig` refuse symlinks on
  `pddManagedCodexHome(env)`, its `auth.json` and `config.toml`, and `~/.codex/config.toml`:
  - `materializeLocalCodexAuth` creates `pddManagedCodexHome(env)` (`0700`), symlinks existing
    non-symlink `~/.codex/{skills,memories,sessions,archived_sessions,history.jsonl,session_index.jsonl,rules}`
    into `pddManagedCodexHome(env)`, merges user settings (such as `[mcp_servers.pdd]`) from
    regular non-symlink `~/.codex/config.toml` while stripping any legacy PDD gateway keys
    (`[model_providers.pdd_codex_gateway]`, `model_provider = "pdd_codex_gateway"`, and PDD-managed
    `/v1/codex-gateway` `openai_base_url` / `chatgpt_base_url`) from `~/.codex/config.toml` without
    ever reading or writing `~/.codex/auth.json`, and always sets `cli_auth_credentials_store = "file"`
    in `managedCodexConfigPath(env)` (`0600`, round-trip verified with `./vendor/smol-toml/parse.js`).
  - `buildSyntheticGatewayIdToken({planType})` builds a deterministic non-secret unsigned JWT
    (`<base64url({alg:"none",typ:"JWT"})>.<base64url(payload)>.sig`) with `exp: 4102444800`,
    `iat: 1700000000`, and `"https://api.openai.com/auth": {chatgpt_account_id: "acct_pdd_gateway", chatgpt_plan_type: normalizedPlanType || "pro", chatgpt_user_id: "user_pdd_gateway"}`.
    `stopCodexAppServerDaemon(codexHome, {env, fs, spawnSync})` is a bounded fail-open helper that skips
    subprocess execution when `fs !== nativeFs` and `spawnSync` is not a function (keeping virtual-fs
    tests hermetic), and otherwise invokes `codex app-server daemon stop` with
    `{env: {...env, CODEX_HOME: codexHome}, stdio: "ignore", timeout: 2500}` inside `try/catch`.
  - When `authOrLease` has delivery mode `"gateway_grant"`, `materializeLocalCodexAuth` validates
    `codex_gateway_url` (`https:` or loopback `http:`) and `codex_gateway_token` (or `gateway_bearer_token`,
    requiring the `"pddg_"` prefix and throwing `code: "invalid_lease"` otherwise), normalizes `<gateway_url>`
    by stripping any trailing `/lse_[^/]+` segment when `<pddg_grant>` starts with `"pddg_lse_"`, writes `0600`
    `managedCodexAuthPath(env)` in native `chatgpt` shape (`{"auth_mode": "chatgpt", "OPENAI_API_KEY": null, "tokens": {"id_token": buildSyntheticGatewayIdToken({planType}), "access_token": "<pddg_grant>", "refresh_token": "", "account_id": "acct_pdd_gateway"}, "last_refresh": "<iso>"}`),
    and writes `0600` `managedCodexConfigPath(env)` with `cli_auth_credentials_store = "file"`,
    `openai_base_url = "<gateway_url>"`, `chatgpt_base_url = "<gateway_url>"`, no top-level
    `model_provider` (recording any prior non-gateway user/managed `model_provider` in
    `previousCodexModelProvider`), and backward-compatibility `[model_providers.pdd_codex_gateway]`:
    when `<pddg_grant>` starts with `"pddg_lse_"`, set `base_url = "<origin>/v1/codex-gateway"`,
    `model_catalog_url = "<origin>/v1/codex-gateway/models"`, `wire_api = "responses"`,
    `requires_openai_auth = true`, `supports_websockets = false`, and omit `http_headers` so
    `config.toml` remains constant across account rotations; for legacy non-`"pddg_lse_"` grants,
    preserve `base_url = "<codex_gateway_url>"`, set `model_catalog_url = "<codex_gateway_url>/models"`,
    `requires_openai_auth = false`, `supports_websockets = false`, and
    `http_headers = {"x-pdd-gateway-grant": "<pddg_grant>"}`.
  - For legacy `direct_stripped` bundles, `materializeLocalCodexAuth` writes `0600`
    `managedCodexAuthPath(env)` with `tokens.refresh_token: ""` and `0600`
    `managedCodexConfigPath(env)` with `cli_auth_credentials_store = "file"` and user settings
    without PDD gateway `openai_base_url`, `chatgpt_base_url`, or `pdd_codex_gateway` (preserving
    any non-PDD user `openai_base_url` / `chatgpt_base_url`). `restoreLocalCodexGatewayConfig` strips
    PDD-managed `openai_base_url` and `chatgpt_base_url` (matching `/\/v1\/(?:accounts\/)?codex-gateway(?:\/|$)/i`),
    `[model_providers.pdd_codex_gateway]`, and `model_provider = "pdd_codex_gateway"` from
    `managedCodexConfigPath(env)` and legacy `~/.codex/config.toml` while preserving non-PDD URLs
    and restoring `previousModelProvider`, removes `managedCodexAuthPath(env)` when
    `removeAuthFile: true` without ever touching `~/.codex/auth.json`, and calls
    `stopCodexAppServerDaemon` on `pddManagedCodexHome(env)` whenever `restoredConfig || removedAuth`.
- `materializeLocalClaudeAuth` atomically merges `env.CLAUDE_CODE_OAUTH_TOKEN`
  into `~/.claude/settings.json` (or `$CLAUDE_CONFIG_DIR/settings.json`, mode `0600`),
  sets `env.ANTHROPIC_BASE_URL` when `delivery_mode === "gateway_grant"`, removes a
  previously managed `/v1/accounts/claude-gateway` (or `/v1/claude-gateway`)
  `ANTHROPIC_BASE_URL` when switching back to `direct_oauth`, and writes
  `hasCompletedOnboarding: true` in `~/.claude.json` (mode `0600`).

## Disposable step isolation, `reauth_required` rotation and Stick-Until-100%

- **Codex step overlay (`createCodexStepOverlay` & `prepareCloudStepExecution`):** Allocates a
  disposable `0700` directory atomically via `mkdtempSync(join(rootDir, 'pdd-cx-'))`,
  registers in-process overlays in an `exit`/`SIGINT`/`SIGTERM` cleanup `Set`, and removes
  `<overlay>` on step exit (`0` tokens in `ps`, never clobbering concurrent terminal sessions):
  - For owner `direct_stripped` passes, symlinks existing non-symlink
    `~/.codex/{config.toml,skills,memories,sessions,rules}`, writes leased stripped
    `auth.json` (`0600`, `refresh_token: ""`), and sets `CODEX_HOME=<overlay>`.
  - For `gateway_grant` leases, validates the `"pddg_"` grant prefix (`code: "invalid_lease"`),
    normalizes `base_url` by stripping any trailing `/lse_[^/]+` segment when the grant starts with
    `"pddg_lse_"`, writes **no `auth.json`** in `<overlay>`, symlinks only existing non-symlink
    `~/.codex/{skills,memories,sessions,rules}` (never `auth.json` or `config.toml`), parses
    `~/.codex/config.toml` when it is a regular non-symlink file to preserve user settings such as
    `[mcp_servers.pdd]`, writes `0600` `<overlay>/config.toml` with
    `model_provider = "pdd_codex_gateway"`, `[features]` merged with `shell_snapshot = false`,
    `[shell_environment_policy]` migrating string entries from legacy `exclude` (`"exclude"`) and
    `include_only` (`"include"`) arrays into `filters` when absent, deleting `exclude` and
    `include_only`, removing any case-insensitive `PDD_CODEX_GATEWAY_GRANT` entry from `filters` and
    `set`, and setting `filters.PDD_CODEX_GATEWAY_GRANT = "exclude"`,
    and `[model_providers.pdd_codex_gateway]` (`name = "PDD Codex Gateway"`,
    `base_url = "<normalized_codex_gateway_url>"`, `model_catalog_url = "<normalized_codex_gateway_url>/models"`,
    `wire_api = "responses"`, `requires_openai_auth = false`,
    `supports_websockets = false`, `env_http_headers = {"x-pdd-gateway-grant": "PDD_CODEX_GATEWAY_GRANT"}`
    with no static `http_headers`), sets `CODEX_HOME=<overlay>` and
    `PDD_CODEX_GATEWAY_GRANT=<grant>` in `step.env`, and deletes `OPENAI_API_KEY`,
    `CODEX_API_KEY`, `CODEX_ACCESS_TOKEN` and `OPENAI_BASE_URL`.
- **Claude step env (`buildClaudeStepEnv` & `loginEnvironment`):** `loginEnvironment`
  strips ambient `CLAUDE_CODE_OAUTH_TOKEN`, `PDD_CODEX_GATEWAY_GRANT` and managed
  `/v1/accounts/claude-gateway` `ANTHROPIC_BASE_URL` before applying profile settings so
  other profiles never inherit ambient grants; `buildClaudeStepEnv` injects leased
  `CLAUDE_CODE_OAUTH_TOKEN` (and `ANTHROPIC_BASE_URL` when `delivery_mode === "gateway_grant"`).
- **Stick-Until-100% and `reauth_required` skip (`selectCloudPoolLogin`, `leaseCloudAccount`, `exhaustCloudPoolLogin`, `reportCloudAccountUsage`):**
  Cloud accounts never stop at `97%`. They stay on `current_account_id` (`0` switches)
  until `five_hour_used_percent >= 100` or `weekly_used_percent >= 100` (or a quota
  exhaustion error), skip local `readCodexUsageWindows` / `readCodexLimits` probes when
  `lease.delivery_mode === "gateway_grant"`, normalize reported usage percents to integers `0..100`
  (`v >= 100 ? 100 : Math.max(0, Math.floor(v))`), POST `/v1/accounts/{account_id}/usage-report`
  with `limit_reached: true`, and lease the next ready account (`soonest weekly_reset_at`)
  with `0` issue strikes. Accounts or account-attributed lease/refresh failures matching `reauth_required`
  (`token_revoked`, `invalid_grant`, `refresh_token_reused`, `state === "reauth_required"`, or account-attributed `401`, while unattributed Cloud bearer `401` errors never taint provider accounts)
  are classified as `"reauth_required"`, persisted in `accounts-state.json` `reauth` across state reconciliations until a newer `last_refresh_at` succeeds or the account is re-enrolled/removed, added to `skip_account_ids`,
  and skipped automatically during pool rotation without masking `reauth_required` as `ready`. `active[provider]` also tracks `materialized_local` so step-only overlay leases never masquerade as locally materialized `codex-home` / `.claude` credentials, and `cloudAccountsRequest` / `leaseCloudAccount` share a single wall-clock `deadlineMs` across token resolution, cold-start transport retry, and reauth skips.
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
`loginEnvironment`, `isAuthFailureMessage` (matching `401`, `OAuth access token is invalid`,
`Failed to authenticate`, `Failed to refresh token`, `authentication_error`, `invalid_api_key`,
and signed-out prompts while ignoring test assertion diagnostics), `readPoolCooldowns`,
`markLoginExhausted`, `clearPoolCooldowns` and `selectPoolLogin` (whose default Claude probe
rejects on-disk `.credentials.json` files with an expired `expiresAt` and no `refreshToken`
as `reason: "expired"` even if `claude auth status --json` reports `loggedIn: true`).

## Dependencies

- [Read Codex account limits](codex-limits.prompt.md) supplies the read-only
  primary/weekly rate-limit and usage-window checks.
- [Agent adapters](agent-adapters.prompt.md) and
  [workflow agents](workflow-agents.prompt.md) supply local CLI sign-in probes.
- [Secret redaction](secret-redaction.prompt.md) supplies `rememberSecrets` and
  `knownSecretValues`.
