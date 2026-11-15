# Cloud accounts CLI

Own `src/accounts-cli.mjs`. Export `runAccountsCli(input, ports)`,
`readCodexFullAuthBundle(fs, env)`, and shell-wrapper helpers
`renderAutoSwitchBlock()`, `applyAutoSwitchBlock(text)` and
`removeAutoSwitchBlock(text)` for the `pdd accounts` command family. Zero
usage-reset credit commands, options or calls exist.

## Domain decisions

- **Isolated Codex sign-in (`pdd accounts add`):** Codex enrollment runs `codex login -c 'cli_auth_credentials_store="file"'` (plus `--device-auth` when requested) inside a disposable `0700` temporary `CODEX_HOME` removed in `finally`, so cancelled or duplicate sign-ins never mutate `~/.codex/auth.json` or the OS keychain before PDD Cloud accepts the bundle. `--device-auth` with `--provider claude` exits `2` before launching `claude`.
- **Tokenless shared Codex local materialization & clean restore:** Shared Codex `gateway_grant` leases (`use`, `accept`, `next`, `sync`) write only the short-lived `pddg_*` grant into `~/.codex/auth.json` (`auth_mode: "apikey"`) and `[model_providers.pdd_codex_gateway]` in `~/.codex/config.toml` while preserving `[mcp_servers.pdd]` and user keys. Switching back to an owner `direct_stripped` account or leaving/removing the active shared Codex account with no shared replacement restores `~/.codex/config.toml` and removes the `pddg_*` `auth.json` when no replacement account remains.
- **Upfront target validation for comma-separated and bulk sharing:** Because CLI flags do not repeat, `--with` accepts comma-separated `USER`, `ORG/TEAM` and `@ORG` targets (trimmed and deduplicated) and validates `LABEL` XOR `--all` plus every target before making network mutations.
- **Fresh usage on `list` and initial Codex enrollment:** `pdd accounts` and `pdd accounts list` request `GET /v1/accounts?refresh=true` via `listCloudAccounts({refresh: true})`. During Codex `add` and `import`, when the server's returned account still has `five_hour_used_percent === 0`, `weekly_used_percent === 0` and null reset timestamps, run a bounded fail-open local `readCodexUsageWindows` probe against the temporary or imported `CODEX_HOME` before wiping/stripping it and report finite windows through `reportCloudAccountUsage`.

## Commands

- `pdd accounts` / `pdd accounts list [--json]`: Call `listCloudAccounts({refresh: true})` (`GET /v1/accounts?refresh=true`), reconcile
  `accounts-state.json` (`enrolled: accounts.length > 0` and `providers` from
  accessible accounts, pruning removed/revoked `active` and `cooling` entries), mark
  the locally active account per provider with `*`, and render an aligned table
  (`*`, `LABEL`, `PROVIDER`, `ACCESS`, `5H`, `7D`, `STATE`: `ready | cooling | paused`)
  followed by any `pending_invites`. `--json` prints structured JSON with zero
  secret fields.
- `pdd accounts add [--provider codex|claude] [--label NAME] [--loop] [--device-auth] [--with USER|ORG/TEAM[,...]]`:
  Reject `--device-auth` for Claude with `exitCode: 2` before starting `claude`, and validate
  `--with` targets before sign-in. Run `codex login -c 'cli_auth_credentials_store="file"'`
  (with `--device-auth` when passed) inside a disposable `0700` temporary `CODEX_HOME` wiped in
  `finally` or `claude setup-token`, validate all four Codex OAuth token fields (`access_token`,
  `refresh_token`, `id_token`, `account_id`) locally before uploading to `POST /v1/accounts`,
  probe local Codex usage fail-open before cleanup if server windows are unpopulated, lease and
  materialize the active pass locally (recording `enrolled: true` and the provider even on
  `all_cooling`), and share with any `--with` targets. With `--loop`, require an interactive TTY
  (`stdin.isTTY && stdout.isTTY` or injected prompt port, else `exitCode: 2`), auto-generate
  collision-free labels `<prefix>-1`, `<prefix>-2`, ... (`--label` prefix or `provider`, skipping
  numbers already present on the server), detect duplicate enrollments via `already_enrolled === true`
  and enrolled `account_id`s within the loop session (`Already enrolled as <label> — refreshed credentials.`
  without advancing the label counter while still applying `--with` shares, with zero local token hashing), and prompt
  `Enroll another <provider> account? [Y/n] ` after each iteration (`""`/`y`/`yes` continues;
  `n`/`no`/EOF/`SIGINT` exits `0` with a concise summary).
- `pdd accounts import [--provider codex|claude] [--from PATH] [--label NAME] [--with USER|ORG/TEAM[,...]]`:
  Validate `--with` targets upfront, read `~/.codex/auth.json` (or `PATH` / `PATH/auth.json` when
  `--from PATH` is given) or a Claude OAuth token, validate all four Codex OAuth token fields,
  upload to `POST /v1/accounts`, probe local Codex usage fail-open before stripping if server
  windows are unpopulated, strip local `~/.codex/auth.json` (`refresh_token: ""`) when importing
  the default local path and materialize the leased pass (`enrolled: true` even on `all_cooling`),
  then apply any `--with` shares.
- `pdd accounts use LABEL`: Pin and materialize `LABEL` locally via
  `POST /v1/accounts/lease` (`preferred_label: LABEL`), handling both owner passes and shared
  `gateway_grant` leases (with clean `~/.codex/config.toml` restore when switching from a shared
  Codex gateway account to an owner pass).
- `pdd accounts next [--provider codex|claude]`: Skip the current active account
  and switch the local install to the next ready account (`soonest weekly_reset_at`)
  via `POST /v1/accounts/lease`.
- `pdd accounts sync [--provider codex|claude] [--quiet] [--timeout-ms MS]`:
  When `--quiet` is passed and `isCloudAccountsActive({env, provider})` is false,
  return `exitCode: 0` immediately without making any network call. Otherwise check
  local `accounts-state.json` first: return a `0ms` no-op when the cached active
  lease has `five_hour_used_percent < 100`, `weekly_used_percent < 100`,
  more than 15 minutes until `expires_at`, and present local materialized files
  (`auth.json`, plus `config.toml` when `managed_codex_gateway` is true).
  Otherwise call `POST /v1/accounts/lease` bounded by `--timeout-ms` (default `1200`)
  and atomically materialize the leased local credentials. Always fail-open (`exitCode: 0`,
  untouched local files) on timeout, offline or error.
- `pdd accounts auto on|off|status`: Off by default. `on` idempotently installs
  one marked fail-open shell wrapper block (`# >>> pdd accounts auto >>>` ...
  `# <<< pdd accounts auto <<<`) in `~/.zshrc` and `~/.bashrc` starting with
  `unalias codex claude 2>/dev/null || true` and running
  `command -v pdd >/dev/null 2>&1 && pdd accounts sync --provider <p> --quiet --timeout-ms 1200 2>/dev/null || true`
  before `command <p> "$@"` so Turn 1 in plain terminal `codex` or `claude` swaps
  before opening `auth.json` without colliding with user aliases. `off` removes the
  marked block cleanly leaving zero trace. `status` reports `on` or `off`.
- `pdd accounts pause LABEL`, `unpause LABEL`,
  `share [LABEL] [--all] [--provider codex|claude] --with USER|ORG/TEAM[,...]`,
  `accept INVITE`,
  `unshare [LABEL] [--all] [--provider codex|claude] [--user USER] [--with USER|ORG/TEAM[,...]]`,
  `leave LABEL`, `remove LABEL`, `log LABEL [--json]`:
  For `share` and `unshare`, require `LABEL` XOR `--all` (`exitCode: 2` otherwise), filter `--all`
  to owned accounts (`is_owner !== false`, excluding borrowed accounts, optionally filtered by
  `--provider`), and parse/validate all comma-separated targets (`USER` -> `{github_login}`,
  `ORG/TEAM` -> `{org, team}`, `@ORG` -> `{org}`, plus `--user USER` on `unshare`) before making
  network mutations. For `share` `USER` targets,
  verify `gh api users/USER` resolves `type === "User"` (rejecting `Organization` with a hint to
  pass `--with ORG/<team>`) and read `res.invite.invite_id` (falling back to `res.invite_id`).
  `accept` accepts the invite and leases/materializes the shared account when no active account is
  pinned for that provider. Both `remove` and `leave` reconcile `accounts-state.json`
  (`enrolled: remaining.length > 0`, `providers`, `active`, `cooling`) and restore local
  `~/.codex/{config.toml,auth.json}` when leaving or removing the active shared Codex gateway account.

## Dependencies

- [Cloud accounts and login pool](login-pool.prompt.md) supplies `/v1/accounts*`
  transport, `accounts-state.json` persistence, and `0600` local auth materializers.
- [Secret redaction](secret-redaction.prompt.md) supplies `redactSecrets` and
  `rememberSecrets`.
