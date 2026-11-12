# Autopilot on the login pool

Own `src/autopilot-pool.mjs`: the Autopilot side of the login pool (#3252). It
gives each agent step one login from the person's pool, sorts the end of a step
into account state or normal work, pauses new steps when every login is out, and
makes the status lines that name the login. It fixes the account part of #3229
(a limit end is never a strike of the issue) and of #3230 (Autopilot saves a pool
binding, not one fixed `CODEX_HOME`).

This module never changes a login. It never refreshes a login, never signs in or
out, never spends a usage reset or credits, and never opens an `auth.json`. It
reads usage only through the [usage read](accounts-usage.prompt.md), which uses
an access-only copy that cannot refresh. It never prints, logs or returns a
token, a key, an account id or an email. Its lines name only the login name,
percentages, times and folder paths.

The Autopilot core and launcher call this module only after the 0.1.29 freeze.
The hook design is outside this repository (P3-HOOKS.md of the pool group).

## Words

- **Provider variable**: `CODEX_HOME` for `codex`, `CLAUDE_CONFIG_DIR` for
  `claude`. Another provider has no pool.
- **Pool logins**: `orderedLogins(pool)` of the [store](accounts-store.prompt.md),
  only the rows of the step's provider, in that order.
- **Readiness**: `loginReadiness(login, usageRow, now)` of the
  [pick rules](accounts-pick.prompt.md). This module never decides stop lines,
  staleness or the pick order itself; the pick rules own them.
- **Time words**: a time is `HH:MM ZONE` (24-hour clock and the short zone name,
  for example `14:41 PST`) when it is on the same day as `now` in the time zone,
  else `Mon D HH:MM ZONE` (`Nov 17 12:49 PST`). The time zone is
  `ports.timeZone`, else the machine's own zone.
- **Pool record**: this module's own file `<stateDir>/autopilot-pool.json`
  (`stateDir` from `poolPaths(env)` of the store), mode 0600, folder 0700. It
  holds `{"version":1,"providers":{"codex":{"last":…,"pause":…,"error":…}}}`.
  `last` is `{name, at}` of the latest step login. `pause` is the current
  all-out event `{reason:"all-out", since, wakeAt, checkedAt, stamp, line,
  earliest}`. `error` is `{since, line}` of a pool file that cannot be read. The
  record is machine-wide: two repositories on one machine share one pool, so an
  all-out event gives one alert per machine. A record that is missing, does not
  parse or has another version reads as empty and is replaced at the next write.
  Each write makes the folder, writes a temp file in it with mode 0600 and
  renames it. No token is ever in the record.
- **Pool stamp**: a sha256 hex of the pool's `order` and `logins` (as JSON) and,
  for each pool login, the size and change time of `<home>/auth.json` (from
  `stat`; the file is never opened). A changed pool file, a new login, a resumed
  login or a new sign-in changes the stamp.

## A step's login (`stepLogin`)

Autopilot asks before each agent start (build, review, repair, conflict). A
running step keeps its login until it ends. The first matching row decides:

| Case | Result |
|---|---|
| No provider variable for `provider` | pinned, reason `no-pool`: "Agent login: PROVIDER is not in the login pool; the step uses its own environment." |
| `env[variable]` is a nonblank string | pinned, reason `env`: "Agent login: pinned: VARIABLE=HOME is set for this Autopilot; pdd does not rotate it." When HOME is the `home` of a pool login, `login` is that row and the line names it: "Agent login: pinned to codex cx5: …". The pool read for this name is best effort; its failure changes nothing. |
| The store, usage or pick module is missing in this pdd | pinned, reason `no-pool`: "Agent login: this pdd has no login pool; the step uses its own environment." |
| `readPool` fails | pause, reason `pool-error`, `wakeAt` null: "Paused: Autopilot cannot read the login pool file (REASON). Fix it, then the next tick goes on; no step starts until then." Each call reads the pool again. The alert goes out once per error event (no saved `error` before). |
| No pool login for the provider | pinned, reason `no-pool`: "Agent login: no PROVIDER login in the pool; the step uses its own environment." Autopilot then works as before the pool. |
| A saved all-out `pause` and `shouldWake` says no | the saved pause, `alert` null. No usage read: a waiting tick costs only local file reads. |
| Otherwise | the pick below. |

**The pick.** Load the usage cache. Walk the pool logins in order and skip the
names in `skip` and the rows with `paused: true` (they are never read). For each
other login, compute its readiness. When the provider is `codex` (the only one
with a usage read) and the login has no usage row, or its readiness reason is
`stale`, read its usage now (`readLoginUsage`), put the new row in the cache and
compute the readiness again. Stop at the first ready login. So a pick reads at
most the logins before the first ready one, one at a time, in order. A read that
throws keeps the old row. When a read happened, save once, with only the rows
read in this call: `saveUsage` merges them into the cache, so a newer mark that
another process wrote on another login stays. Then `pickLogin({logins, usage, now, skip})` decides. `skip` is a
preference of one step, never a pause: when it leaves no login but a skipped
login is ready, `pickLogin` runs again with no skip and the step takes that
login.

REASON (in every line about a pool file error) is "the file does not parse" for a
JSON syntax error, else the store's message on one line (at most 400
characters), with each quoted part longer than 40 characters shortened to `…`
and token-like words (`eyJ…`, `sk-…`, `gh?_…`, `Bearer …`) replaced by
`[redacted]`, so no file text reaches a line, an alert or the pool record.

- A picked login: the result is `{login, env: {VARIABLE: login.home}, line,
  logLine, recovered}`. `line` is "Agent login: codex cx2 (week 63%, 5h 42%).
  Pool: R of T ready. Next free: cx5 at 14:41 PST." R, T and next free come from
  `poolSummary`; "Next free" is left out when it is null. When S pool logins
  that are not paused have no row or a `stale` readiness, "Pool: R of T ready (S not read in the last
  10 minutes)." The percentages are the rounded `usedPercent` of the `week` and
  `fiveHour` windows; a missing window shows `?`. A login whose readiness reason
  is `renews` (a full local login whose access ended; its own Codex renews it)
  shows "(access ended; Codex renews it at this step)" instead of the
  percentages. `logLine` is the job log line
  "pdd-account: cx2 (local pool)". Save `last` in the pool record. When a saved
  all-out pause or pool error existed, remove it; `recovered` is then "Autopilot
  has a PROVIDER login again: cx2. The pause ended." (else null).
- All out: `wakeAt` is `earliest.at` of the pick when it is after `now`;
  `now` + 10 minutes when it is not (the login should be back but is not: check
  again after one tick, not on every tick); `now` + 60 minutes with no earliest
  (no login has a known reset). `line` is "Paused: no Codex
  login has quota now (COUNTS). Earliest reset: cx1 at Nov 11 14:41 PST. Add a
  login (pdd accounts add NAME) and the pause ends at the next tick. Resets:
  WORD." COUNTS lists each readiness reason with its count, in this order and
  only when not zero: "N at a limit" (`week`, `five-hour`, `limited`), "1 needs a
  sign-in" or "N need a sign-in" (`needs-sign-in`, `expired`, `no-login`, and
  `limited` when the cached row has `limitReason: "needs-sign-in"`), "N
  paused" (`paused: true` or reason `paused`), "N not readable" (`unknown`,
  `stale` and every other reason). With no earliest: "Earliest reset: unknown;
  Autopilot checks again at TIME." WORD is "off" when every pool login has
  `reset: "never"`, else "on for NAMES (setting ask or auto; the reset rule
  decides)". A new all-out event (no saved pause) gets `since` = now and one
  `alert`; a pause that is still all out after a wake keeps its `since` and gets
  `alert` null. Save the pause with `checkedAt` = now and the current stamp.

**Alerts.** An alert is `{kind:"usage-limit", text, tried, need}` for the
Autopilot alert port (a machine incident). The all-out alert has `text` = the
pause line, `tried` "Autopilot started no new agent step. Running steps go on.",
and `need` "Add a login (pdd accounts add NAME), wait for the reset, or resume a
paused login (pdd accounts resume NAME)." The pool-error alert has the same
`text` and `tried`, and `need` "Fix the login pool file; pdd accounts list shows
the problem." An alert goes out only after the pool
record with this event is saved, so a record that cannot be written gives no
alert (no alert on every tick). A record path that cannot be made (`poolPaths`
fails, for example with no absolute HOME) means no record: reads give an empty
record and writes fail.

## Waking a pause (`shouldWake`)

`shouldWake(pause, {now, stamp, usage})` is pure. It answers, in this order:

| Condition | Answer |
|---|---|
| `pause` is null or not an object | `{wake: true, reason: "no-pause"}` |
| `now >= pause.wakeAt` (a finite number) | `{wake: true, reason: "time"}` |
| `stamp` differs from `pause.stamp` | `{wake: true, reason: "pool"}` |
| A usage row has a finite `readAt` > `pause.checkedAt` (another read, for example `pdd accounts list`, saw the logins after the last check) | `{wake: true, reason: "read"}` |
| Otherwise | `{wake: false, reason: "waiting"}` |

A wake is only a new pick. When the pick still finds no login, the pause goes on
as the same event.

## Sorting the end of a step (`classifyAgentEnd`)

`classifyAgentEnd({provider, output, exitCode, now, timeZone})` is pure. `output`
is the end of the step's job log (stdout and stderr of `codex exec --json` or
`claude -p --output-format stream-json`). Only the agent's own error events and
the last plain lines count. Tool output is inside other events and never counts,
so an agent that works on limit texts (tests, fixtures) cannot fake a limit.

Read at most the last 256 KiB and its last 200 lines, newest first. Skip blank
lines and this module's own `pdd-account:` lines.

- A JSON object line is an event. A success ends the search with `other`:
  `type: "turn.completed"`, or `type: "result"` with `is_error` not true. These
  events give a message: `type: "error"` (`message`), `type: "turn.failed"`
  (`error.message`), `type: "result"` with `is_error: true` (`result`, else
  `error`). An event with `error: "rate_limit"`, `apiError:
  "usage_limit_reached"` or `codex_error_info: "usage_limit_exceeded"` is a
  limit; `error: "authentication_failed"` is a sign-in. All other events are
  skipped.
- A plain line counts only among the last 5 plain lines, and only when it does
  not read like a test diagnostic (the words test, assert, assertion, expected,
  fixture or spec).

`exitCode` does not change the kind: the events decide. The newest error event
with a message decides, also when its message has no kind (then `other`): an
older retry or capacity message never overrides the real end. Only when no error
event gives a message, the newest of the last 5 plain lines that has a kind
decides. A message gets the first kind that matches, in this order:

| Kind | Matches |
|---|---|
| `limit` | `usage_limit_reached`, `usage_limit_exceeded`; "hit your limit", "hit your usage limit", "hit your weekly limit", "hit your weekly usage limit" (also daily, monthly, 5-hour, session); "usage limit reached", "usage limit exceeded", "usage limit has been reached"; "weekly limit reached", "5-hour limit reached"; "Claude AI usage limit reached" |
| `credits` | `credits_depleted`; "out of credits"; "credit balance is too low"; "insufficient credits", "insufficient_quota", "insufficient funds"; "exceeded your current quota" |
| `needs-sign-in` | `refresh_token_expired`, `_reused`, `_invalidated`, `_revoked`; "refresh token has expired", "was already used", "was revoked", "is invalid"; "sign in again", "log in again"; "please run /login", "please log in", "please sign in"; "not logged in", "not signed in"; "login required", "authentication required"; `authentication_failed`; "invalid api key"; "OAuth token has expired" |
| `stale-copy` | a 401 status ("status 401", "HTTP 401", "error 401", "401 Unauthorized"; a bare 401, such as a line number, is no status); "unauthorized"; "access token expired", "access token is invalid", "access token was rejected" |
| `capacity` | "at capacity", "over capacity", "overloaded"; a 429 or 5xx status, "too many requests", "internal server error", "bad gateway", "service unavailable", "gateway timeout"; "rate limit" or `rate_limit_exceeded` without the word usage; `server_error`; "stream disconnected"; "connection reset", "connection refused" |
| `other` | nothing above, no message, or a success first |

A limit text that offers to "purchase more credits" is a `limit`: the limit row
comes first. A refresh-token text that also says "access token" is
`needs-sign-in`.

`until` is the epoch milliseconds when a `limit` or `credits` end comes back by
itself, else null. The first source that gives a time wins:

1. A number after `resets_at` or `resetsAt` in the message or event JSON (9 to
   13 digits; under 1e12 means seconds).
2. `resets_in_seconds` plus `now` (needs `now`).
3. "usage limit reached|SECONDS" (the older Claude form).
4. Codex words "try again at Nov 3rd, 2026 10:35 PM" (a full date) or "try again
   at 4:17 PM" (the same day as `now`, needs `now`), in `timeZone` (default: the
   machine's own zone; Codex writes its local time).
5. Claude words "resets 3pm (America/Los_Angeles)" (the next such time: today,
   or tomorrow when that time today is before `now`) or
   "resets Nov 6 at 3:30pm (America/Los_Angeles)", in the named zone (needs
   `now`). A date with no year is in the year of `now`, or in the next year when
   that date is more than 32 days before `now`.

A time that is not finite, not positive, outside the Date range, or more than 32
days after `now` (when `now` is given) is null. `message` is a fixed safe phrase
for the kind, never the agent's words: `usage limit`, `out of credits`, `sign-in
ended`, `401 on the login copy`, `service busy`, or null for `other`.

Result: `{kind, until, message}`.

## After a step (`afterStep`)

`afterStep({login, end, env, now, command}, ports)` acts on one
`classifyAgentEnd` result. `login` is the pool login row of the step, its name,
or null (a step pinned outside the pool). It returns `{strike, line, mark,
alert}`:

- `strike` false: the end is never a strike of the issue, never a 24-hour
  cooldown and never a count toward the machine pause (#3229). The next step
  takes the next login. `strike` true: normal step rules apply (the core
  decides).
- `mark`: `{name, until, reason}` when a login was marked, else null.
- `line`: one job log and status line, else null. `alert`: as above, else null.

| Kind | What happens |
|---|---|
| `other` | Nothing. `{strike: true, line: null, mark: null, alert: null}`. |
| `capacity` | No login change and no mark (the core waits a short time). `line` "pdd-account: NAME: the AI service is busy (service busy); no login change." `strike` false. |
| `limit`, `credits` | `until` = `end.until` when it is after now; else, when `login` is the pool row (the read needs its folder), one usage read of this login (`readLoginUsage`; only this row is saved in the cache) and its readiness `until` when it is not ready and after now; else now + 30 minutes. `markLimited({env}, name, until, kind)`. One local log row `{at, action: "limited", login: name, detail: "KIND until ISO"}`. `line` "pdd-account: cx2 limited until 14:41 PST (usage limit). The next step takes the next login." |
| `needs-sign-in` | `markLimited({env}, name, now + 60 minutes, "needs-sign-in")`, one log row (action `needs-sign-in`), `line` "pdd-account: cx3 needs a new sign-in (sign-in ended). The next step takes the next login." One `alert` with `text` "Codex login cx3 needs a new sign-in. Autopilot skips it. Run: pdd accounts add cx3" ("Pool login" when `login` is only a name), `tried` "Autopilot uses the other logins of the pool.", `need` "Sign in to this login again." No alert when the cached row already has `limitReason: "needs-sign-in"` with `limitedUntil` after now (one alert per event), and no alert when the mark failed (the next step would alert again). |
| `stale-copy` | `markLimited({env}, name, now + 10 minutes, "stale-copy")`, one log row (action `limited`), `line` "pdd-account: cx2 got 401 on its login copy; it waits 10 minutes. The next step takes the next login." |

With `login` null, an account kind still returns `strike` false and marks
nothing; its line is "pdd-account: the pinned login ended with: MESSAGE. pdd
does not rotate a pinned login." (`capacity` says "the pinned login" instead of
a name). When the store, usage or pick module is missing, an account kind
returns `strike` false, no mark and "pdd-account: NAME ended with: MESSAGE (the
pool could not save this: this pdd has no login pool)." A port failure is
caught and `strike` stays as in the table. A failed read only gives the 30-minute
time. A failed cache save after a read keeps the read's time. A failed cache
save, mark or log row adds " (the pool could not save this: MESSAGE)" to the
line, and `mark` is null when the mark failed.

## The start binding (`startBinding`, #3230)

`startBinding({provider, env, saved, pool}, ports)` decides what `pdd autopilot
start` saves. `saved` is null for a new state, else `{agentPool, home}` from the old state
(`agentPool` a provider or null; `home` the saved provider variable, or null).
An old state has no `agentPool`; it keeps working as a pin of its saved folder,
or with the provider's default folder when it saved none. `pool` is true
when the person asks for the pool at this start (`--pool`). The first matching
row decides; the result is `{agentPool, home, line}`:

| Case | Result |
|---|---|
| `env[variable]` is nonblank | a pin: `{agentPool: null, home: env[variable]}`. Line "Agent login: pinned to VARIABLE=HOME." plus " It was the PROVIDER pool." or " It was VARIABLE=OLD." when the saved binding differs. |
| `pool` is true and the pool has a login for the provider | the pool: `{agentPool: provider, home: null}`. Line "Agent login: the PROVIDER pool (N logins); each step takes the first login with quota." plus " It was VARIABLE=OLD." when the saved binding was a pin. |
| `pool` is true and the pool has none | the saved binding. Line "Agent login: the PROVIDER pool has no login (pdd accounts add NAME); kept: WHAT." |
| `saved.agentPool` is the provider | the pool, line "Agent login: the PROVIDER pool (N logins, saved)." |
| `saved.home` is set | the pin, line "Agent login: pinned to VARIABLE=HOME (saved). Run pdd autopilot start --pool to rotate the pool's logins." The second sentence only when the pool has a login for the provider. |
| A new state and the pool has a login for the provider | the pool, as in row 2 with no "It was". |
| Otherwise | `{agentPool: null, home: null}`, line "Agent login: no login pool; steps use PROVIDER's own default folder." plus the `--pool` sentence of the row above when the pool has a login for the provider. |

WHAT is "the PROVIDER pool", "VARIABLE=OLD" or "no saved login". A pool that
cannot be read counts as no login, and the line says "(the pool file cannot be
read: REASON)" instead of "(pdd accounts add NAME)".

## Status lines (`poolStatusLines`)

`poolStatusLines({provider, env, now}, ports)` returns a list of lines for
`pdd autopilot status`. It reads only local files (pool, usage cache, pool
record) and never reads usage or starts a process. `env` is the Autopilot's step
environment, not the person's shell.

- Pinned (`env[variable]` nonblank): the pinned line of `stepLogin`.
- No pool module, or no pool login for the provider: no line.
- A pool that cannot be read: "Agent login: the login pool file cannot be read
  (REASON)."
- A saved all-out pause: its line, then the sign-in lines below.
- Else: "Agent login: codex cx2 (week 63%, 5h 42%) since 14:05 PST. Pool: R of T
  ready (S not read in the last 10 minutes). Next free: cx5 at 14:41 PST." The
  first sentence is "Agent login: PROVIDER pool; no step used it yet." with no
  `last`. Then, in both cases, one line for each pool login whose readiness reason is
  `needs-sign-in`, or whose cached row has `limitReason: "needs-sign-in"` with
  `limitedUntil` after now: "cx3 needs a sign-in: run pdd accounts add cx3."

## Public contract

```js
stepLogin({provider, env = {}, now, command = provider, skip = []}, ports = {})
  // -> {login, env, line, logLine, recovered}
  //  | {pinned: true, reason: 'env'|'no-pool', login: row|null, line}
  //  | {pause: {reason: 'all-out'|'pool-error', since, wakeAt, line, alert, earliest}}
classifyAgentEnd({provider, output, exitCode, now, timeZone})
  // -> {kind: 'limit'|'credits'|'needs-sign-in'|'stale-copy'|'capacity'|'other', until, message}
afterStep({login, end, env = {}, now, command}, ports = {})
  // -> {strike, line, mark: {name, until, reason}|null, alert}
startBinding({provider, env = {}, saved = null, pool = false}, ports = {})
  // -> {agentPool, home, line}
poolStatusLines({provider, env = {}, now}, ports = {})   // -> string[]
shouldWake(pause, {now, stamp, usage})                    // -> {wake, reason}
```

- `now` is epoch milliseconds. `earliest` is `{name, at}` or null. `since`,
  `wakeAt` and `until` are epoch milliseconds or null.
- `stepLogin`, `afterStep`, `startBinding` and `poolStatusLines` are async.
- Ports: `store` (`readPool`, `orderedLogins`, `appendLog`, `poolPaths`),
  `usage` (`loadUsage`, `saveUsage`, `readLoginUsage`, `markLimited`), `pick`
  (`loginReadiness`, `pickLogin`, `poolSummary`), `fs` (node:fs functions for the
  pool record and the stamp), `timeZone`, `modulePorts` (passed as the second
  argument to every store, usage and pick call), `importModule` (default:
  dynamic `import`). A missing `store`, `usage` or `pick` port loads its module
  (`./accounts-store.mjs`, `./accounts-usage.mjs`, `./accounts-pick.mjs`). Only a
  module that is not installed (`ERR_MODULE_NOT_FOUND` whose missing file, the
  first quoted path of the message, is that module) means "no pool"; a missing
  file that the module itself imports is a broken install; any other load error is thrown, so a broken install is visible.
- `loadUsage` may return the cache file object (`{version, rows}`) or the rows
  map; this module uses the rows map keyed by login name, passes the full map to
  the pick rules, and passes only new rows to `saveUsage`. `poolPaths` gets
  `modulePorts` too.

## Dependencies

- [Pool store](accounts-store.prompt.md): `poolPaths`, `readPool`,
  `orderedLogins`, `appendLog`; required for the pool file, the order and the
  local log.
- [Usage read and cache](accounts-usage.prompt.md): `loadUsage`, `saveUsage`,
  `readLoginUsage`, `markLimited`; required for usage rows and limit marks.
- [Pick rules](accounts-pick.prompt.md): `loginReadiness`, `pickLogin`,
  `poolSummary`; required for readiness, the pick and the summary.
- The shared shapes are in the pool group's DESIGN.md sections 3 to 5 (outside
  this repository). Native tests check this module with fakes of these ports,
  and with the real modules, a temp HOME, fake logins and a fake `codex
  app-server` (the usage read's `spawn` port).
- Node built-ins only: `node:fs`, `node:path`, `node:crypto`, `Intl`.

<details><summary>Runtime interface</summary>

```json
{"status":"draft","prose_sha256":"","kind":"partial","entries":[{"operation":"classifyAgentEnd","input_schema":{"type":"object","properties":{"provider":{"type":"string","enum":["codex","claude"]},"output":{"type":"string","maxLength":262144},"exitCode":{"oneOf":[{"type":"integer"},{"type":"null"}]},"now":{"type":"integer","minimum":0},"timeZone":{"type":"string","minLength":1}},"required":["provider","output","exitCode"],"additionalProperties":false},"result_schema":{"type":"object","properties":{"kind":{"type":"string","enum":["limit","credits","needs-sign-in","stale-copy","capacity","other"]},"until":{"oneOf":[{"type":"integer"},{"type":"null"}]},"message":{"oneOf":[{"type":"string","enum":["usage limit","out of credits","sign-in ended","401 on the login copy","service busy"]},{"type":"null"}]}},"required":["kind","until","message"],"additionalProperties":false},"errors":[]}],"calls":[],"resources":[],"limits":{"max_steps":4,"max_model_calls":2},"conventions":[]}
```
</details>
