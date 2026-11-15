# Cloud accounts and login pool

Own `src/login-pool.mjs`. Export the Cloud Accounts client, local `0600` lease
materializers, disposable `0700` Codex step overlay, Stick-Until-100% and
burst-`429` classifiers, and internal multi-harness fallback helpers:
`resolveCloudAccountsEndpoint(env)`,
`resolveCloudAccountsToken({cwd, env}, ports)`,
`cloudAccountsRequest(method, path, options, ports)`,
`accountsStatePath(env)`,
`readCloudAccountsState({env}, ports)`,
`writeCloudAccountsState(state, {env}, ports)`,
`isCloudAccountsActive({env, poolPath, provider}, ports)`,
`stripCodexAuthBundle(authJson)`,
`materializeLocalCodexAuth(authJson, {env}, ports)`,
`materializeLocalClaudeAuth(lease, {env, previousManagedBaseUrl}, ports)`,
`createCodexStepOverlay(authJson, {env, tmpRoot}, ports)`,
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

## Cloud Accounts transport and single-refresh invariant

Cloud Accounts uses `PDD_ACCOUNTS_URL || PDD_CLOUD_URL ||
"https://pdd-byok-api-c437voydwa-uc.a.run.app"` (`https:` required except loopback `127.0.0.1`,
`localhost`, `[::1]`; never falls back to `PDD_RUNTIME_URL`),
`Authorization: Bearer <token>` (`PDD_TOKEN`, `PDD_ACCOUNTS_TOKEN`, `GH_TOKEN`,
`GITHUB_TOKEN`, or `gh auth token`), and `X-PDD-Machine-Id`. Unwrap FastAPI
`HTTPException` `detail` envelopes (`{"detail": {"error": ..., "message": ...}}`,
string `detail`, and validation-error arrays) alongside top-level `error`/`message`.
Every credential read or leased is registered with `rememberSecrets` from
`src/secret-redaction.mjs` and is never printed or logged. Zero usage-reset credit
fields, endpoints or calls exist.

- Local cache (`${PDD_STATE_DIR || XDG_STATE_HOME || ~/.local/state}/pdd/accounts-state.json`,
  mode `0600`, atomic rename) stores only non-secret active lease metadata
  (`enrolled`, `providers`, per-provider `account_id`, `label`, `lease_id`, `expires_at`,
  `delivery_mode`, `anthropic_base_url`, `managed_anthropic_base_url`,
  `five_hour_used_percent`, `five_hour_reset_at`, `weekly_used_percent`,
  `weekly_reset_at`) — never `refresh_token`, `access_token` or OAuth tokens.
  `isCloudAccountsActive({env, poolPath, provider})` returns `false` when an explicit
  `poolPath` is supplied, when `provider` is neither `"codex"` nor `"claude"`, when
  `!saved.enrolled`, or when `provider` is passed and absent from `saved.providers`;
  `selectCloudPoolLogin` only leases providers present in `saved.providers`.
- `stripCodexAuthBundle` and `materializeLocalCodexAuth` write `~/.codex/auth.json`
  (or `$CODEX_HOME/auth.json`) atomically with mode `0600` and `tokens.refresh_token: ""`
  so only PDD Cloud refreshes the single-use OpenAI refresh token.
- `materializeLocalClaudeAuth` atomically merges `env.CLAUDE_CODE_OAUTH_TOKEN`
  into `~/.claude/settings.json` (or `$CLAUDE_CONFIG_DIR/settings.json`, mode `0600`),
  sets `env.ANTHROPIC_BASE_URL` when `delivery_mode === "gateway_grant"`, removes a
  previously managed `/v1/accounts/claude-gateway` (or `/v1/claude-gateway`)
  `ANTHROPIC_BASE_URL` when switching back to `direct_oauth`, and writes
  `hasCompletedOnboarding: true` in `~/.claude.json` (mode `0600`).

## Disposable step isolation and Stick-Until-100%

- **Codex step overlay (`createCodexStepOverlay`):** Allocates a disposable `0700`
  directory atomically via `mkdtempSync(join(rootDir, 'pdd-cx-'))`, symlinks
  existing `~/.codex/{config.toml,skills,memories,sessions,rules}`, writes leased
  stripped `auth.json` (`0600`, `refresh_token: ""`), passes `CODEX_HOME=<overlay>`,
  registers in-process overlays in an `exit`/`SIGINT`/`SIGTERM` cleanup `Set`, and
  removes `<overlay>` on step exit (`0` tokens in `ps`, never clobbering concurrent
  terminal sessions).
- **Claude step env (`buildClaudeStepEnv` & `loginEnvironment`):** `loginEnvironment`
  strips ambient `CLAUDE_CODE_OAUTH_TOKEN` and managed `/v1/accounts/claude-gateway`
  `ANTHROPIC_BASE_URL` before applying profile settings so Codex and other profiles
  never inherit ambient Claude grants; `buildClaudeStepEnv` injects leased
  `CLAUDE_CODE_OAUTH_TOKEN` (and `ANTHROPIC_BASE_URL` when `delivery_mode === "gateway_grant"`).
- **Stick-Until-100% (`selectCloudPoolLogin`, `exhaustCloudPoolLogin`, `reportCloudAccountUsage`):**
  Cloud accounts never stop at `97%`. They stay on `current_account_id` (`0` switches)
  until `five_hour_used_percent >= 100` or `weekly_used_percent >= 100` (or a quota
  exhaustion error), normalize reported usage percents to integers `0..100`
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
