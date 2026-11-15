# Cloud accounts CLI

Own `src/accounts-cli.mjs`. Export `runAccountsCli(input, ports)`,
`readCodexFullAuthBundle(fs, env)`, and shell-wrapper helpers
`renderAutoSwitchBlock()`, `applyAutoSwitchBlock(text)` and
`removeAutoSwitchBlock(text)` for the `pdd accounts` command family. Zero
usage-reset credit commands, options or calls exist.

## Commands

- `pdd accounts` / `pdd accounts list [--json]`: Call `GET /v1/accounts`, reconcile
  `accounts-state.json` (`enrolled: accounts.length > 0` and `providers` from
  accessible accounts, pruning removed/revoked `active` and `cooling` entries), mark
  the locally active account per provider with `*`, and render an aligned table
  (`*`, `LABEL`, `PROVIDER`, `ACCESS`, `5H`, `7D`, `STATE`: `ready | cooling | paused`)
  followed by any `pending_invites`. `--json` prints structured JSON with zero
  secret fields.
- `pdd accounts add [--provider codex|claude] [--label NAME]`: Run `codex login`
  or `claude setup-token` to obtain a fresh sign-in, validate all four Codex OAuth
  token fields (`access_token`, `refresh_token`, `id_token`, `account_id`) locally
  before uploading the bundle to `POST /v1/accounts`, and immediately overwrite local
  `~/.codex/auth.json` (`0600`, `tokens.refresh_token: ""`) or
  `~/.claude/settings.json` + `~/.claude.json` (`0600`, `hasCompletedOnboarding: true`)
  so only PDD Cloud refreshes credentials, recording `enrolled: true` and the provider
  in `accounts-state.json` even when the initial `/v1/accounts/lease` reply is
  `all_cooling`.
- `pdd accounts import [--provider codex|claude] [--label NAME]`: Validate all four
  Codex OAuth token fields in `~/.codex/auth.json` (or read a Claude OAuth token) and
  upload to `POST /v1/accounts`, then replace local `~/.codex/auth.json` with a
  stripped `0600` pass (`refresh_token: ""`) or materialize `~/.claude/settings.json` +
  `~/.claude.json`, recording `enrolled: true` and the provider in
  `accounts-state.json` even when the initial `/v1/accounts/lease` reply is
  `all_cooling`.
- `pdd accounts use LABEL`: Pin and materialize `LABEL` locally via
  `POST /v1/accounts/lease` (`preferred_label: LABEL`).
- `pdd accounts next [--provider codex|claude]`: Skip the current active account
  and switch the local install to the next ready account (`soonest weekly_reset_at`)
  via `POST /v1/accounts/lease`.
- `pdd accounts sync [--provider codex|claude] [--quiet] [--timeout-ms MS]`:
  When `--quiet` is passed and `isCloudAccountsActive({env, provider})` is false,
  return `exitCode: 0` immediately without making any network call. Otherwise check
  local `accounts-state.json` first: return a `0ms` no-op when the cached active
  lease has `five_hour_used_percent < 100`, `weekly_used_percent < 100`,
  more than 15 minutes until `expires_at`, and a present local auth file.
  Otherwise call `POST /v1/accounts/lease` bounded by `--timeout-ms` (default `1200`)
  and atomically materialize `0600` `~/.codex/auth.json` or `~/.claude/settings.json` +
  `~/.claude.json`. Always fail-open (`exitCode: 0`, untouched local files) on
  timeout, offline or error.
- `pdd accounts auto on|off|status`: Off by default. `on` idempotently installs
  one marked fail-open shell wrapper block (`# >>> pdd accounts auto >>>` ...
  `# <<< pdd accounts auto <<<`) in `~/.zshrc` and `~/.bashrc` starting with
  `unalias codex claude 2>/dev/null || true` and running
  `command -v pdd >/dev/null 2>&1 && pdd accounts sync --provider <p> --quiet --timeout-ms 1200 2>/dev/null || true`
  before `command <p> "$@"` so Turn 1 in plain terminal `codex` or `claude` swaps
  before opening `auth.json` without colliding with user aliases. `off` removes the
  marked block cleanly leaving zero trace. `status` reports `on` or `off`.
- `pdd accounts pause LABEL`, `unpause LABEL`, `share LABEL --with USER|ORG/TEAM`,
  `accept INVITE`, `unshare LABEL --user USER`, `leave LABEL`, `remove LABEL`,
  `log LABEL [--json]`: Resolve `LABEL` (or account/invite ID) and call the
  corresponding `/v1/accounts` lifecycle, sharing or audit endpoint. For `--with USER`,
  verify `gh api users/USER` resolves `type === "User"` (rejecting `Organization` with
  a hint to pass `--with ORG/TEAM`), read `res.invite.invite_id` (falling back to
  `res.invite_id`) when printing invite confirmation, and reconcile `accounts-state.json`
  (`enrolled: remaining.length > 0`, `providers`, `active`, `cooling`) on both `remove`
  and `leave`.

## Dependencies

- [Cloud accounts and login pool](login-pool.prompt.md) supplies `/v1/accounts*`
  transport, `accounts-state.json` persistence, and `0600` local auth materializers.
- [Secret redaction](secret-redaction.prompt.md) supplies `redactSecrets` and
  `rememberSecrets`.
