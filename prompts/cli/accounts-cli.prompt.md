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

- **Isolated PDD-managed Codex home and zero-plaintext temporary OAuth cleanup (never touch `~/.codex/auth.json`):** `pdd accounts add` runs `codex login -c 'cli_auth_credentials_store="file"'` inside a disposable `0700` temporary `CODEX_HOME`, deletes the temporary plaintext `auth.json` immediately once uploaded to PDD Cloud (as well as wiping the temp directory in `finally`), and never falls back to writing raw OAuth tokens onto disk if post-enroll `/v1/accounts/lease` returns `all_cooling` or fails. Post-enroll sync, `import`, `use`, `next`, `sync`, `codex` and `accept` materialize leased Codex `auth.json` (`0600`) and `config.toml` (`0600`, `cli_auth_credentials_store = "file"`, symlinking `~/.codex/{skills,memories,sessions,archived_sessions,history.jsonl,session_index.jsonl,rules}` and merging `~/.codex/config.toml`) exclusively inside `pddManagedCodexHome(env)` (`${stateDir}/codex-home`), never writing to or deleting `~/.codex/auth.json`. Both owner and shared `gateway_grant` leases materialize zero OpenAI OAuth tokens on disk with constant `<origin>/v1/codex-gateway` in `config.toml` when the grant token is `pddg_lse_...`.
- **Interactive Claude `setup-token` enrollment and isolated extraction:** `pdd accounts add --provider claude` runs `claude setup-token` inside an isolated `0700` temporary `CLAUDE_CONFIG_DIR` (cleaned up immediately after reading and in `finally`) with `COLUMNS=500` so Ink does not wrap ~108-character `sk-ant-oat01-...` tokens. In interactive TTY sessions (`stdin?.isTTY && stdout?.isTTY`, when no custom login runner is injected), spawn `claude setup-token` with inherited `stdin` (`stdio: ['inherit', 'pipe', 'pipe']`) and stream `stdout`/`stderr` live to the terminal so the user can view the OAuth URL and paste the authorization code without closing `stdin`; when `stdin` is non-interactive (`!stdin?.isTTY`) and no login runner stub is injected, fail fast with a clear actionable message explaining how to run `pdd accounts add --provider claude` in an interactive terminal or `pdd accounts import --provider claude`. Strip ANSI CSI/OSC sequences and unwrap soft-wrapped `sk-ant-oat...` token continuations before extracting the token, and in `add` mode extract strictly from `setup-token` output (or files inside the isolated temp `CLAUDE_CONFIG_DIR`), never falling back to pre-existing `~/.claude/settings.json`, `~/.claude/.credentials.json` or ambient `CLAUDE_CODE_OAUTH_TOKEN`.
- **Shell auto-switch and live PTY mid-session auto-rotation across `zsh`, `bash`, and `fish`:** `pdd accounts auto on|off|status` manages `~/.zshrc`, `~/.bashrc`, and `${XDG_CONFIG_HOME || ~/.config}/fish/config.fish`. For `codex`, the wrapper runs `pdd accounts sync --provider codex --quiet --timeout-ms 1200` and sets `CODEX_HOME` to `pddManagedCodexHome(env)` only when a healthy active lease is materialized and the command is neither `codex logout` nor `codex login`; for interactive terminal sessions (`[ -t 0 ] && [ -t 1 ]` / `isatty stdin; and isatty stdout`) launching interactive `codex` (default chat, `resume`, or `fork`), it delegates to `pdd accounts codex -- "$@"` so mid-session quota exhaustion rotates accounts and resumes automatically. On `codex logout` or `codex login`, it leaves normal `~/.codex` untouched (or refuses with guidance to run `pdd accounts pause`, `remove` or `use` if `CODEX_HOME` was manually exported to `pddManagedCodexHome(env)`). When PDD Cloud is unreachable or no valid active lease exists, `CODEX_HOME` stays unset so `codex` falls back to `~/.codex/auth.json`.
- **Provider-scoped `+`/`-` label lookup, `reauth_required` surfacing, and refresh visibility:** `resolveAccount` accepts optional `provider` (`codex` or `claude`), matches exact `account_id`, exact `label`, case-insensitive `label`, then `sanitizeLabel(target, "")` (`glt+oai2` resolves `glt-oai2`), and throws an `exitCode: 2` disambiguation error naming `--provider codex` or `--provider claude` whenever `--provider` is omitted and `LABEL` matches accounts across multiple providers. `pdd accounts list` and `pdd accounts status` surface `reauth_required` clearly (never as `ready`) alongside `last_refresh_at` and lease/token expiry status.
- **Post-login email labels, `--replace`, duplicate-share avoidance, and initial usage probe:** When `--label` is omitted on `add` or `import` (including `--loop`), derive the base label from the authenticated `id_token` `email` local-part (`sanitizeLabel(emailLocalPart, "")` without a `codex-` prefix), disambiguating collisions within the same provider as `<base>-2`, `<base>-3`, ... unless `--replace` is set, and falling back to `<provider>-main` (single) or `<provider>-1`, `<provider>-2`, ... (`--loop`) only when no email claim is present; explicit `--label PREFIX` with `--loop` preserves `<prefix>-1`, `<prefix>-2`, ... numbering. `--with` accepts comma-separated `USER`, `ORG/TEAM` and `@ORG` targets validated before network mutations, skips creating duplicate invites when an account already has an active or pending share for that target, and initial Codex `add`/`import` probes local usage fail-open when server windows are unpopulated.
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
- `pdd accounts add [--provider codex|claude] [--label NAME] [--loop] [--replace] [--device-auth] [--with USER|ORG/TEAM[,...]]`:
  Reject `--device-auth` for Claude with `exitCode: 2` before starting `claude`, and validate
  `--with` targets before sign-in. Run `codex login -c 'cli_auth_credentials_store="file"'`
  (with `--device-auth` when passed) inside a disposable `0700` temporary `CODEX_HOME` (deleting
  `auth.json` immediately after Cloud upload and wiping the temp directory in `finally`, never reading
  `~/.codex/auth.json`) or interactive `claude setup-token` inside an isolated `0700` temporary
  `CLAUDE_CONFIG_DIR`, validate all four Codex OAuth token fields (`access_token`, `refresh_token`,
  `id_token`, `account_id`) locally before uploading to `POST /v1/accounts`, support `--replace` to
  replace an existing owned `(provider, label)` entry cleanly (preserving/re-applying shares) and prompt
  interactively (`[r]eplace` / disambiguated `<label>-2` / `[s]kip`) on `409` label conflicts when
  `--replace` is omitted, probe local Codex usage fail-open before cleanup if server windows are
  unpopulated, lease and materialize the active pass into `pddManagedCodexHome(env)` or
  `~/.claude/settings.json` (`enrolled: true` even on `all_cooling`, without writing raw fallback
  OAuth tokens to disk), and share with any `--with` targets not already shared on that account.
  With `--loop`, require an interactive TTY or injected prompt port (`exitCode: 2` otherwise), print
  numbered iteration banners and `<email> -> "<label>"` confirmation, derive default labels from the
  authenticated email local-part when `--label` is omitted (or `<prefix>-1`, `<prefix>-2`, ... when
  `--label PREFIX` is supplied), offer `[R]etry` / `[s]kip` on transient `POST /v1/accounts` upload
  errors without repeating OAuth login, detect `already_enrolled === true` and session duplicate
  `account_id`s without advancing the counter, treat `SIGINT` (`code === 130` or `signal === "SIGINT"`)
  as a clean loop exit (`exitCode: 0`), and prompt `Enroll another <provider> account? [Y/n] `.
- `pdd accounts import [--provider codex|claude] [--from PATH] [--label NAME] [--replace] [--with USER|ORG/TEAM[,...]]`:
  Validate `--with` targets upfront, read `~/.codex/auth.json` (or `PATH` / `PATH/auth.json` when
  `--from PATH` is given, refusing bundles with a stripped refresh token) or a validated Claude OAuth token from `settings.json`, `.credentials.json` or `PATH`,
  validate all four Codex OAuth token fields, upload to `POST /v1/accounts` (supporting `--replace` and interactive `409` label conflict recovery), probe local Codex usage
  fail-open if server windows are unpopulated, materialize the leased pass into `pddManagedCodexHome(env)`
  without writing to `~/.codex/auth.json`, and apply any non-duplicate `--with` shares.
- `pdd accounts use LABEL [--provider codex|claude]`: Resolve `LABEL` (scoped to `--provider` when passed, or exiting `2` when `LABEL` is ambiguous across providers), refuse `reauth_required` accounts with a clear re-authentication command, and pin/materialize
  `LABEL` in `pddManagedCodexHome(env)` or `~/.claude/settings.json` via `POST /v1/accounts/lease`.
- `pdd accounts next [--provider codex|claude]`: Skip the current active account
  and switch `pddManagedCodexHome(env)` or `~/.claude/settings.json` to the next ready account
  (`soonest weekly_reset_at`) via `POST /v1/accounts/lease`.
- `pdd accounts codex [-- ARGS...]`: Sync/lease a healthy Codex account into `pddManagedCodexHome(env)`
  (failing open to plain `codex` when Cloud accounts are unenrolled or offline without an active lease),
  launch interactive `codex` under a live PTY/session supervisor that captures the active session ID and
  monitors output for hard quota exhaustion (`usage_limit_reached`, `You've hit your usage limit`,
  `quota_exceeded`), report usage fail-open, atomically rotate `pddManagedCodexHome(env)/auth.json` to the
  next ready Codex lease, and automatically relaunch `codex resume <session-id>` (or `codex resume --last`)
  so the interactive session continues seamlessly.
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
- `pdd accounts pause LABEL [--provider codex|claude]`, `unpause LABEL [--provider codex|claude]`,
  `share [LABEL] [--all] [--provider codex|claude] --with USER|ORG/TEAM[,...]`,
  `accept INVITE`,
  `unshare [LABEL] [--all] [--provider codex|claude] [--user USER] [--with USER|ORG/TEAM[,...]]`,
  `leave LABEL [--provider codex|claude]`, `remove LABEL [--provider codex|claude]`, `log LABEL [--provider codex|claude] [--json]`:
  Require `LABEL` XOR `--all` on `share`/`unshare` (`exitCode: 2` otherwise), allow `--provider` on both
  single-`LABEL` and `--all` operations, filter `--all` to owned accounts, skip duplicate share invites when
  a target already has an active or pending share on that account, verify `gh api users/USER` resolves
  `type === "User"` on `share`, materialize into `pddManagedCodexHome(env)` or `~/.claude/settings.json` on
  `accept`, and reconcile `accounts-state.json` plus clean up `pddManagedCodexHome(env)` and any legacy
  `~/.codex/config.toml` gateway block on `remove` and `leave` without touching `~/.codex/auth.json`.

## Dependencies

- [Cloud accounts and login pool](login-pool.prompt.md) supplies `/v1/accounts*`
  transport, `accounts-state.json` persistence, `pddManagedCodexHome(env)`, and `0600` auth materializers.
- [Secret redaction](secret-redaction.prompt.md) supplies `redactSecrets` and
  `rememberSecrets`.
