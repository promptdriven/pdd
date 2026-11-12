# Login usage read and usage cache

Own `src/accounts-usage.mjs`. The login pool picks the next login from each
login's usage (week and 5-hour windows, limits). This module
reads that usage for one login or many, read only, and keeps the last result
per login in a local cache. A usage read must never renew or spend anything:
it runs Codex in an [access-only home](accounts-login.prompt.md#access-only-home)
that has no refresh token, and it asks Codex for nothing but the rate-limit
read. Nothing that it returns or saves holds a token, an account id or an email.

## Exports

- async `readLoginUsage(login, {env, now, command} = {}, ports = {})` returns
  one [usage row](#usage-row).
- async `readAllUsage(logins, {env, now, command, save = true} = {}, ports = {})`
  returns `{[name]: usage row}` for every login, in the input order.
- async `loadUsage({env} = {}, ports = {})` returns `{[name]: usage row}`.
- async `saveUsage({env} = {}, rows, ports = {})` returns the saved
  `{[name]: usage row}` for the names in `rows`.
- async `markLimited({env} = {}, name, untilMs, reason, ports = {})` returns the
  saved usage row for `name`.

Options: `env` defaults to `process.env`. `now` is a function that returns epoch
milliseconds, or a fixed epoch-milliseconds number; default `Date.now`.
`command` is the Codex program, default `codex`. A login is a pool row with at
least `name` (non-empty string), `provider` and `home`. A name is only data:
every returned map has each name as its own key, and a name such as
`__proto__` or `constructor` never reaches an inherited member of any object.

Ports (each optional): `spawn` (passed to the transport), `fs` and `tmpdir`
(passed to the [login facts module](accounts-login.prompt.md)), `fs` also for
the cache files, and `sleep(ms)` (a promise; default a timer) for the cache lock.

## Usage row

Every row is a fresh object with exactly these fields. Times are epoch
milliseconds.

| Field | Value |
|---|---|
| `state` | `ok`, `expired`, `no-login`, `needs-sign-in` or `unknown`. A read writes all but `needs-sign-in`, which other callers (Autopilot) record. |
| `kind` | `full` or `access` from the login facts state, else null. A `full` login renews itself on this machine at its next step, so a pick can use a `full` login in state `expired`; an `access` copy cannot renew. |
| `plan` | The bucket's `planType` when it is a non-empty string, else null. |
| `week` | `{usedPercent, resetsAt}` of the 10080-minute window, or null. |
| `fiveHour` | `{usedPercent, resetsAt}` of the 300-minute window, or null. |
| `accessExpiresAt` | From the login facts, or null. |
| `readAt` | When this row was made, or null for a row that no read made. |
| `limitedUntil` | When the limit ends, or null. |
| `limitReason` | `limit`, `credits`, `needs-sign-in`, `stale-copy` or null. A read sets only `limit` and `credits`; Autopilot marks the others after a step. `limitReason` set with `limitedUntil` null means limited with an unknown end: only a later read clears it. |
| `resets` | Always null from a read (see [read the reply](#read-the-reply)). A cached `{left, expiresAt}` passes the row filter. |
| `note` | `""` for `ok`; else a few safe words that say why. |

A row that is not `ok` has `plan`, `week`, `fiveHour` and `resets` null.
`kind` is set on every row whose facts state is `full` or `access`, also when
the row is not `ok` (for example `expired` without a read).

## Read one login

`readLoginUsage` never throws or rejects for any login, file, program or reply;
every failure is a row. It decides in this order, first match wins:

| Check | Row |
|---|---|
| `provider` is not `codex` | `unknown`, note `usage read is only for codex logins` |
| `home` is not a non-empty absolute path | `unknown`, note `login folder is not an absolute path` |
| Facts state `none` | `no-login`, note `no Codex login in this folder` |
| Facts state `unreadable` | `unknown`, note `login file is unreadable` |
| `accessExpiresAt` is null | `unknown`, note `access end is unknown; not read` |
| `accessExpiresAt` ≤ now + 10 minutes | `expired`, note `access ended; this read never refreshes` |
| Otherwise | Read it (below). |

The 10-minute margin keeps Codex away from its own refresh point (5 minutes
before the end). The read runs inside `withAccessOnlyHome(home, ...)`. The file
can change between the two reads, so it checks the access end of the copied
file again with the last three rows of the table and uses that
`accessExpiresAt`. Then it calls
[`readCodexRateLimitsReply`](codex-limits.prompt.md#transport) with:

- `command`; `cwd` = the temporary home (so no project config loads);
- `env` = a copy of `env` with `CODEX_HOME` = the temporary home and without
  `OPENAI_API_KEY`, `CODEX_API_KEY` and `CODEX_ACCESS_TOKEN` (so Codex reads
  this login and no other credential);
- `clientInfo` = name `pdd_accounts`, title `PDD accounts`, version `1`.

The transport sends only `initialize`, `initialized` and
`account/rateLimits/read`. A failed read is `unknown` with the note for its
reason:

| Reason | Note |
|---|---|
| `spawn` | `codex did not start` |
| `exit` | `codex app-server ended early` |
| `timeout` | `usage read timed out` |
| `output` | `codex app-server sent too much output` |
| `protocol` | `bad reply from codex app-server` |
| `error` | `codex app-server refused the read` |

A `PDD_NO_LOGIN` rejection (the file went away or broke between the two reads)
gives the table row for the error's `state`. A `PDD_TEMP_HOME_LEFT` rejection is
`unknown` with the note `temporary login folder not removed: <path>` (the
error's `path`); any other rejection is `unknown` with the note
`temporary login folder failed`. `readAt` is `now` after the read.

## Read the reply

The bucket is `reply.rateLimitsByLimitId.codex` when it is present and not null,
else `reply.rateLimits`. The reply must be a non-array object and the bucket a
non-array object, else `unknown` with the note `bad usage reply`.

The windows are the bucket's `primary` and `secondary` that are not null. Each
one must be valid by the [Codex limits window rule](codex-limits.prompt.md#health-state)
(finite `usedPercent` ≥ 0; `resetsAt` null or a finite non-negative Unix-seconds
value within Date range); one invalid window makes the row `unknown` with the
note `bad usage reply`. No window and no non-blank `rateLimitReachedType` is
`unknown` with the note `no usage windows in reply`.

- `windowDurationMins` 10080 gives `week`; 300 gives `fiveHour`; other values
  give neither. When both windows have one duration, keep the one with the higher
  `usedPercent` (on a tie, `primary`). `resetsAt` is Unix seconds × 1000, or null.
- Limited when any window is at 100% or more, or `rateLimitReachedType` is a
  non-blank string, or the reply's `ordinaryUsageAllowed` is `false` (the
  protocol says that a client must not infer recovery while it is false).
  `limitReason` is `credits` for `workspace_owner_credits_depleted` and
  `workspace_member_credits_depleted`, else `limit`. `limitedUntil` is the
  latest `resetsAt` of the windows at 100% or more; when no window is at 100%,
  of all windows; null when that set is empty or any member has no `resetsAt`.
  Not limited: both are null.
- Every other field is ignored. `accountId` and credit balances are never kept.
- `resets` is always null: this module keeps no data about resets from the
  reply. The field stays in the row so that the cache shape does not change.

## Read many logins

`readAllUsage` rejects with `TypeError('logins must be an array of pool logins.')`
before any read unless `logins` is an array of objects with non-empty string
names. It runs at most 4 reads at a time, started in input order. With `save`
true (the default) it then saves all rows with `saveUsage` and returns the saved
rows; with `save` false it returns the read rows and writes nothing. A failed
save rejects with its error.

## Usage cache

The cache file is `<state>/usage.json`, where `<state>` is
`$XDG_STATE_HOME/pdd/accounts` when `env.XDG_STATE_HOME` is an absolute path,
else `<home>/.local/state/pdd/accounts` with `<home>` = `env.HOME` when it is
absolute, else `os.homedir()`. This is the pool's shared state-folder rule.

The file is `{"version": 1, "rows": {"<name>": usage row}}`, mode 0600, in a
folder with mode 0700. It is derived data: no login and no decision lives in it,
and a read rebuilds it.

- `loadUsage`: the file is opened read-only and non-blocking, like the login
  file. A missing file, a path that is not a regular file, a file over 1 MiB,
  text that is not JSON, or a
  value without `version` 1 and an object `rows` gives `{}`. Each row that is a
  non-array object passes through the row filter; other rows are dropped.
- Row filter (for every load and every write): keep only the usage row fields.
  A field with a wrong type becomes its empty value (`state` `unknown`, `note`
  `""`, others null). So a token in a field that a caller added never reaches
  the file.
- `saveUsage(rows)` writes the given rows over the rows with the same names and
  keeps all other rows. A filtered row that is not `ok` keeps the cached row's
  `limitedUntil` and `limitReason` when the cached `limitReason` is set and its
  `limitedUntil` is null or later than the new `readAt` (or the new `readAt` is
  null). A failed read is no proof that a limit ended. An `ok` row replaces
  them, except an active `needs-sign-in` mark (same time test): a good usage
  read proves only that the access token works, not the refresh token that
  failed in the step, so the mark stays until its time ends. `rows` that is not a non-array object rejects with
  `TypeError('rows must be an object of usage rows by login name.')` before any
  file access.
- `markLimited` rejects with a `TypeError` unless `name` is a non-empty string,
  `untilMs` a finite non-negative number or null, and `reason` one of `limit`,
  `credits`, `needs-sign-in` and `stale-copy` (the caller picks the time). It
  sets `limitedUntil` and `limitReason` on the cached row, or on a new row
  (`unknown`, `kind` null, `readAt` null, note `not read yet`) when there is none.

Every write runs under the lock file `<state>/usage.json.lock` (exclusive
create). A lock whose modification time is more than 30 seconds old is stale and
is removed. The writer tries 100 times, 50 ms apart; then it rejects with an
`Error` with `code` `PDD_USAGE_LOCKED` and the message
`The usage cache is locked by another pdd process.` Under the lock it reads the
current file, applies the change, writes a temporary file in the same folder
(mode 0600), syncs it and renames it over `usage.json`; then it removes the
lock. A failed write rejects with its error and leaves the old file.

## Dependencies

- [Codex login facts](accounts-login.prompt.md): `codexLoginFacts` and
  `withAccessOnlyHome`; required context for the read.
- [Codex limits](codex-limits.prompt.md): `readCodexRateLimitsReply` (the
  transport) and the window rule; required context for the read.
- Node `node:fs/promises`, `node:os` and `node:path`.
