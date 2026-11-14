# Cloud accounts CLI

Own `src/accounts-cli.mjs`. Export `runAccountsCli(input, ports)` and shell-wrapper
helpers `renderAutoSwitchBlock()`, `applyAutoSwitchBlock(text)` and
`removeAutoSwitchBlock(text)` for the `pdd accounts` command family. Zero
usage-reset credit commands, options or calls exist.

## Commands

- `pdd accounts` / `pdd accounts list [--json]`: Call `GET /v1/accounts`, mark
  the locally active account per provider with `*`, and render an aligned table
  (`*`, `LABEL`, `PROVIDER`, `ACCESS`, `5H`, `7D`, `STATE`: `ready | cooling | paused`)
  followed by any `pending_invites`. `--json` prints structured JSON with zero
  secret fields.
- `pdd accounts add [--provider codex|claude] [--label NAME]`: Run `codex login`
  or `claude setup-token` to obtain a fresh sign-in, upload the bundle to
  `POST /v1/accounts`, and immediately overwrite local `~/.codex/auth.json` (`0600`,
  `tokens.refresh_token: ""`) or `~/.claude/settings.json` + `~/.claude.json` (`0600`,
  `hasCompletedOnboarding: true`) so only PDD Cloud refreshes credentials.
- `pdd accounts import [--provider codex|claude] [--label NAME]`: Upload an
  existing local `~/.codex/auth.json` or Claude OAuth token to `POST /v1/accounts`,
  then replace local `~/.codex/auth.json` with a stripped `0600` pass
  (`refresh_token: ""`) or materialize `~/.claude/settings.json` + `~/.claude.json`.
- `pdd accounts use LABEL`: Pin and materialize `LABEL` locally via
  `POST /v1/accounts/lease` (`preferred_label: LABEL`).
- `pdd accounts next [--provider codex|claude]`: Skip the current active account
  and switch the local install to the next ready account (`soonest weekly_reset_at`)
  via `POST /v1/accounts/lease`.
- `pdd accounts sync [--provider codex|claude] [--quiet] [--timeout-ms MS]`:
  Check local `accounts-state.json` first: return a `0ms` no-op when the cached
  active lease has `five_hour_used_percent < 100`, `weekly_used_percent < 100`,
  more than 15 minutes until `expires_at`, and a present local auth file.
  Otherwise call `POST /v1/accounts/lease` bounded by `--timeout-ms` (default `1200`)
  and atomically materialize `0600` `~/.codex/auth.json` or `~/.claude/settings.json` +
  `~/.claude.json`. Always fail-open (`exitCode: 0`, untouched local files) on
  timeout, offline or error.
- `pdd accounts auto on|off|status`: Off by default. `on` idempotently installs
  one marked fail-open shell wrapper block (`# >>> pdd accounts auto >>>` ...
  `# <<< pdd accounts auto <<<`) in `~/.zshrc` and `~/.bashrc` running
  `command -v pdd >/dev/null 2>&1 && pdd accounts sync --provider <p> --quiet --timeout-ms 1200 2>/dev/null || true`
  before `command <p> "$@"` so Turn 1 in plain terminal `codex` or `claude` swaps
  before opening `auth.json`. `off` removes the marked block cleanly leaving zero
  trace. `status` reports `on` or `off`.
- `pdd accounts pause LABEL`, `unpause LABEL`, `share LABEL --with USER|ORG/TEAM`,
  `accept INVITE`, `unshare LABEL --user USER`, `leave LABEL`, `remove LABEL`,
  `log LABEL [--json]`: Resolve `LABEL` (or account/invite ID) and call the
  corresponding `/v1/accounts` lifecycle, sharing or audit endpoint.

## Dependencies

- [Cloud accounts and login pool](login-pool.prompt.md) supplies `/v1/accounts*`
  transport, `accounts-state.json` persistence, and `0600` local auth materializers.
- [Secret redaction](secret-redaction.prompt.md) supplies `redactSecrets` and
  `rememberSecrets`.
