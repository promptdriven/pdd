# Cloud accounts CLI

Own `src/accounts-cli.mjs`. Export `runAccountsCli(input, ports)`,
`readCodexFullAuthBundle(fs, env, explicitAuthPath)`,
`readClaudeTokenFromPath(fs, fromPath, options)`,
`readLocalClaudeToken(fs, env, extraText, options)`,
`detectImportProvider(fs, env, options)`, and shell-wrapper helpers
`renderAutoSwitchBlock(shell)`, `applyAutoSwitchBlock(text, shell)` and
`removeAutoSwitchBlock(text)` for the `pdd accounts` command family. Zero
usage-reset credit commands, options or calls exist.

## Domain decisions

- **Isolated PDD-managed Codex home (never touch `~/.codex/auth.json`):** `pdd accounts add` runs `codex login -c 'cli_auth_credentials_store="file"'` inside a disposable `0700` temporary `CODEX_HOME` wiped in `finally`, and post-enroll sync, `import`, `use`, `next`, `sync` and `accept` materialize leased Codex `auth.json` (`0600`) and `config.toml` (`0600`, `cli_auth_credentials_store = "file"`, symlinking `~/.codex/{skills,memories,sessions,archived_sessions,history.jsonl,session_index.jsonl,rules}` and merging `~/.codex/config.toml`) exclusively inside `pddManagedCodexHome(env)` (`${stateDir}/codex-home`), never writing to or deleting `~/.codex/auth.json`.
- **Shell auto-switch across `zsh`, `bash`, and `fish` with logout guard and fail-safe fallback:** `pdd accounts auto on|off|status` manages `~/.zshrc`, `~/.bashrc`, and `${XDG_CONFIG_HOME || ~/.config}/fish/config.fish`. For `codex`, the wrapper runs `pdd accounts sync --provider codex --quiet --timeout-ms 1200` and sets `CODEX_HOME` to `pddManagedCodexHome(env)` only when a healthy active lease is materialized and the command is neither `codex logout` nor `codex login`. On `codex logout` or `codex login`, it leaves normal `~/.codex` untouched (or refuses with guidance to run `pdd accounts pause`, `remove` or `use` if `CODEX_HOME` was manually exported to `pddManagedCodexHome(env)`). When PDD Cloud is unreachable or no valid active lease exists, `CODEX_HOME` stays unset so `codex` falls back to `~/.codex/auth.json`.
- **Symmetric `+`/`-` label lookup, `reauth_required` surfacing, and refresh visibility:** `resolveAccount` falls back to `sanitizeLabel(target, "")` (case-insensitive) when exact and lowercase matches miss so `glt+oai2` resolves `glt-oai2`. `pdd accounts list` and `pdd accounts status` surface `reauth_required` clearly (never as `ready`) alongside `last_refresh_at` and lease/token expiry status.
- **Upfront target validation and initial usage probe:** `--with` accepts comma-separated `USER`, `ORG/TEAM` and `@ORG` targets validated before network mutations, and initial Codex `add`/`import` probes local usage fail-open when server windows are unpopulated.
- **Claude `.credentials.json` fallback and expired short-lived token guard:** Standard `claude auth login` stores OAuth credentials in `<configDir>/.credentials.json` under `claudeAiOauth` (`accessToken`, `refreshToken`, `expiresAt`) without setting `env.CLAUDE_CODE_OAUTH_TOKEN` in `<configDir>/settings.json`. When `--from <dir>` or default local discovery (`CLAUDE_CONFIG_DIR` or `~/.claude`) finds no `CLAUDE_CODE_OAUTH_TOKEN` in `settings.json`, `readClaudeTokenFromPath`, `readLocalClaudeToken` and `detectImportProvider` inspect `<dir>/.credentials.json`. Whenever `claudeAiOauth` is present (including when `--from` targets a `.credentials.json` file directly, checked before regex token extraction), register its secret fields in `rememberSecrets` and check `expiresAt` (numeric epoch ms or ISO timestamp): if `expiresAt` is present and invalid or expired (`expiresAt <= now + 60_000`), throw `CloudAccountsError` (`code: "expired_local_login"`) naming `<target>` and instructing the user to run `pdd accounts add --provider claude` or `claude setup-token` before uploading to PDD Cloud or modifying `~/.claude/settings.json`; otherwise accept a non-empty `claudeAiOauth.accessToken`.

## Commands

- `pdd accounts` / `pdd accounts list [--json]`: Call `listCloudAccounts({refresh: true})` (`GET /v1/accounts?refresh=true`), reconcile
  `accounts-state.json` (`enrolled: accounts.length > 0` and `providers` from
  accessible accounts, pruning removed/revoked `active` and `cooling` entries and calling
  `restoreLocalCodexGatewayConfig` with `removeAuthFile: !nextActive.codex` when pruning an
  active Codex account), mark the locally active account per provider with `*`, and render an
  aligned table (`*`, `LABEL`, `PROVIDER`, `ACCESS`, `5H`, `7D`, `STATE`:
  `ready | cooling | draining | paused | reauth_required`, `REFRESH`: last refresh and expiry summary)
  followed by any `reauth_required` re-auth hints and `pending_invites`. `--json` prints structured JSON with zero secrets.
- `pdd accounts status [--json]`: Inspect live or cached Cloud accounts state (failing open to
  local `accounts-state.json` when offline), reporting enrollment count, `pddManagedCodexHome(env)`
  isolation status, `zsh`/`bash`/`fish` `auto` wrapper status, per-provider active account
  (`label`, `delivery_mode`, `state`, `5h`/`7d` usage, `last_refresh_at`, token/lease
  `expires_at` remaining time), and any `reauth_required` accounts.
- `pdd accounts add [--provider codex|claude] [--label NAME] [--loop] [--device-auth] [--with USER|ORG/TEAM[,...]]`:
  Reject `--device-auth` for Claude with `exitCode: 2` before starting `claude`, and validate
  `--with` targets before sign-in. Run `codex login -c 'cli_auth_credentials_store="file"'`
  (with `--device-auth` when passed) inside a disposable `0700` temporary `CODEX_HOME` wiped in
  `finally` (never reading `~/.codex/auth.json`) or `claude setup-token`, validate all four Codex
  OAuth token fields (`access_token`, `refresh_token`, `id_token`, `account_id`) locally before
  uploading to `POST /v1/accounts`, probe local Codex usage fail-open before cleanup if server
  windows are unpopulated, lease and materialize the active pass into `pddManagedCodexHome(env)`
  or `~/.claude/settings.json` (`enrolled: true` even on `all_cooling`), and share with any
  `--with` targets. With `--loop`, require an interactive TTY or injected prompt port (`exitCode: 2`
  otherwise), auto-generate collision-free labels `<prefix>-1`, `<prefix>-2`, ..., detect
  `already_enrolled === true` and session duplicate `account_id`s without advancing the counter,
  treat `SIGINT` (`code === 130` or `signal === "SIGINT"`) as a clean loop exit (`exitCode: 0`),
  and prompt `Enroll another <provider> account? [Y/n] `.
- `pdd accounts import [--provider codex|claude] [--from PATH] [--label NAME] [--with USER|ORG/TEAM[,...]]`:
  Validate `--with` targets upfront, read `~/.codex/auth.json` (or `PATH` / `PATH/auth.json` when
  `--from PATH` is given, refusing bundles with a stripped refresh token) or a validated Claude OAuth token from `settings.json`, `.credentials.json` or `PATH`,
  validate all four Codex OAuth token fields, upload to `POST /v1/accounts`, probe local Codex usage
  fail-open if server windows are unpopulated, materialize the leased pass into `pddManagedCodexHome(env)`
  without writing to `~/.codex/auth.json`, and apply any `--with` shares.
- `pdd accounts use LABEL`: Resolve `LABEL` (exact, case-insensitive, then `sanitizeLabel` `+`/`-`
  fallback), refuse `reauth_required` accounts with a clear re-authentication command, and pin/materialize
  `LABEL` in `pddManagedCodexHome(env)` or `~/.claude/settings.json` via `POST /v1/accounts/lease`.
- `pdd accounts next [--provider codex|claude]`: Skip the current active account
  and switch `pddManagedCodexHome(env)` or `~/.claude/settings.json` to the next ready account
  (`soonest weekly_reset_at`) via `POST /v1/accounts/lease`.
- `pdd accounts sync [--provider codex|claude] [--quiet] [--timeout-ms MS]`:
  When `--quiet` is passed and `isCloudAccountsActive({env, provider})` is false,
  return `exitCode: 0` immediately without making any network call. Check local
  `accounts-state.json` first: return a `0ms` no-op when the cached active lease has
  `materialized_local === true`, `state === "ready"` (never `paused`, `cooling`, or `reauth_required`),
  `five_hour_used_percent < 100`, `weekly_used_percent < 100`, more than 15 minutes
  until `expires_at` (and more than 5 minutes until `access_token_expires_at` when known),
  and present materialized files in `pddManagedCodexHome(env)` or `~/.claude/settings.json`. Otherwise call `POST /v1/accounts/lease`
  bounded by `--timeout-ms` (default `1200`, `maxRetries: 0` when `--quiet`). With
  `--print-codex-home` or `PDD_PRINT_CODEX_HOME=1`, print `pddManagedCodexHome(env)` only when a
  healthy active Codex lease is confirmed and materialized, else print nothing so the shell wrapper
  falls back to `~/.codex`. Always fail-open (`exitCode: 0`).
- `pdd accounts auto on|off|status`: Off by default. `on` idempotently installs
  marked fail-open shell wrapper blocks (`# >>> pdd accounts auto >>>` ...
  `# <<< pdd accounts auto <<<`) in `~/.zshrc`, `~/.bashrc`, and
  `${XDG_CONFIG_HOME || ~/.config}/fish/config.fish` (creating `~/.config/fish` when needed).
  `off` removes the marked block cleanly. `status` reports `on` or `off`.
- `pdd accounts pause LABEL`, `unpause LABEL`,
  `share [LABEL] [--all] [--provider codex|claude] --with USER|ORG/TEAM[,...]`,
  `accept INVITE`,
  `unshare [LABEL] [--all] [--provider codex|claude] [--user USER] [--with USER|ORG/TEAM[,...]]`,
  `leave LABEL`, `remove LABEL`, `log LABEL [--json]`:
  Require `LABEL` XOR `--all` on `share`/`unshare` (`exitCode: 2` otherwise), filter `--all`
  to owned accounts, verify `gh api users/USER` resolves `type === "User"` on `share`, materialize
  into `pddManagedCodexHome(env)` or `~/.claude/settings.json` on `accept`, and reconcile
  `accounts-state.json` plus clean up `pddManagedCodexHome(env)` and any legacy `~/.codex/config.toml`
  gateway block on `remove` and `leave` without touching `~/.codex/auth.json`.

## Dependencies

- [Cloud accounts and login pool](login-pool.prompt.md) supplies `/v1/accounts*`
  transport, `accounts-state.json` persistence, `pddManagedCodexHome(env)`, and `0600` auth materializers.
- [Secret redaction](secret-redaction.prompt.md) supplies `redactSecrets` and
  `rememberSecrets`.
