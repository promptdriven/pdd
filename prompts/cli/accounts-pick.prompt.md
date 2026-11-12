# Login pool: pick a login and decide on a reset

Own `src/accounts-pick.mjs`. This module answers four questions for the login
pool of issue #3252: is a login ready, which login does the next agent step use,
what does the pool look like, and may pdd use a Codex usage reset now. This is
new work. The login pool plan (the "Final plan v2" comment on issue #3252,
sections 5 and 6) and the pool's shared design of rows and function shapes
authorize its interface.

The module is pure. It reads no file, no network, no program, no clock and no
random value. The caller gives `now` (epoch milliseconds) and every row. It never
changes its inputs. It never spends a reset: it only returns a decision and the
text for it. `pdd accounts list`, `pdd accounts reset` and Autopilot's pool code
call it.

## Inputs

- **Login row**: a row of the pool file. This module reads only `name`,
  `paused`, `reset` and `stop` (`stop.week`, `stop.fiveHour`). It ignores other
  fields. A list entry that is not an object with a string `name` is not a login:
  every function leaves it out (also from counts).
- **Stop line**: `stop.week` and `stop.fiveHour` in percent. A finite number
  above 0 and at most 100 is used. Any other value (absent, null, text, 0, 150)
  is 97.
- **Usage rows**: `usage` is an object keyed by login name. Use only own
  properties (a login can be named `constructor`). A missing or non-object
  `usage` is `{}`. A usage row has `state`, `week`, `fiveHour`, `readAt` and
  `limitedUntil` (epoch milliseconds). A row that is absent, null or not an
  object is a missing row.
- **Fresh**: `readAt` is a finite number and `now - readAt` is at most 600000
  (10 minutes). A row read exactly 10 minutes ago is fresh.
- **Window**: `week` or `fiveHour`. An absent or null window has no limit (some
  plans have no 5-hour window). A present window needs a finite number
  `usedPercent`; otherwise the row is malformed. Its `resetsAt` is a finite
  number (epoch milliseconds) or else unknown (null).
- **Blocked window**: `usedPercent` at or above that window's stop line.
- **Limited until**: `limitedUntil` is a finite number above `now`. Autopilot
  sets it after a limit error in a step; a read sets it when it sees 100%.

## Readiness

`loginReadiness(login, usageRow, now)` returns a new object
`{ ready, reason, until }`. `ready` is true only for reason `ready`. `until` is
the epoch milliseconds when the login comes back by itself, or null. The first
row that matches wins:

| # | When | reason | until |
|---|---|---|---|
| 1 | `login.paused === true` | `paused` | null |
| 2 | missing usage row | `stale` | null |
| 3 | row not fresh, limited until is set | `limited` | `limitedUntil` |
| 4 | row not fresh | `stale` | null |
| 5 | `state` is `no-login`, `needs-sign-in` or `expired` | the same word | null |
| 6 | `state` is not `ok`, or a present window is malformed | `limited` when limited until is set, else `unknown` | `limitedUntil` or null |
| 7 | a blocked window has a known `resetsAt` at or before `now` | `limited` when limited until is set, else `stale` | `limitedUntil` or null |
| 8 | the week window is blocked | `week` | see below |
| 9 | the 5-hour window is blocked | `five-hour` | see below |
| 10 | limited until is set | `limited` | `limitedUntil` |
| 11 | otherwise | `ready` | null |

For rows 8 and 9, `until` is the latest of the blocked windows' `resetsAt` and,
when set, `limitedUntil`. It is null when a blocked window has an unknown
`resetsAt`. When both windows are blocked, the reason is `week`.

Why this order:
- A stale row is not trusted (row 4): the caller reads the login again and
  then asks again. pdd never guesses from old numbers.
- A limit that a step or a read saw holds until its time, even when the row is
  old (row 3). A new read cannot make that login usable sooner.
- A blocked window whose reset time has passed (row 7) has probably reset. A
  past reset time alone never proves that, so the caller reads again.
- `no-login`, `needs-sign-in` and `expired` need a person or a refresh. They
  never come back by themselves, so `until` is null.

## Pick and summary

`pickLogin({ logins, usage, now, skip = [] })`:

- `logins` are login rows in the person's effective order (the caller sorts and
  filters them by provider). A non-array is an empty list. `skip` is a list of
  login names that this pick does not look at; a non-array is empty.
- Return `{ login, readiness }` for the first login in order (not in `skip`)
  whose readiness is ready. `login` is the same object that the caller gave.
- Otherwise return `{ login: null, allOut: true, earliest, rows }`.
  - `rows`: one `{ name, ready, reason, until }` per login not in `skip`, in
    order.
  - `earliest`: `{ name, at }` of the row with the smallest non-null `until`
    (the first in order on a tie), or null when no row has one.
- A stale login is not ready, so a later ready login can win. The caller reads
  stale rows again before it trusts a pick.

`poolSummary({ logins, usage, now })` returns `{ ready, total, next, nextFree }`:
`total` is the number of logins; `ready` is the number of ready logins; `next` is
the name of the first ready login in order, or null; `nextFree` is `{ name, at }`
of the not-ready login with the smallest non-null `until` (the first in order on
a tie), or null. `nextFree` is set also when some logins are ready.

## Resets: the decision

Each login has a `reset` setting: `never`, `ask` or `auto`. Only `ask` and
`auto` allow a reset. Any other value (absent, `never`, an unknown word) allows
none. pdd never changes this setting.

`resetDecision({ logins, usage, now, workWaiting, resets, usedToday, timeZone })`
returns a new object `{ action, login, until, reason, text }`.

- `workWaiting`: the number of issues that wait for an agent (ready issues and
  steps held for quota). Only a safe integer of 1 or more is work.
- `resets`: an object keyed by login name (own properties only).
  `resets[name]` is `{ left, expiresAt }`: `left` is the number of resets the
  account has; `expiresAt` is the epoch milliseconds when the first of them
  ends, or null. A login without this entry, or with `left` that is not a safe
  integer of 1 or more, has no reset.
- `usedToday`: a list of login names that used a reset in the last 24 hours
  (see `usedTodayFromLog`). A non-array is empty.
- `timeZone`: an IANA zone name for the clock time in the notice. An absent or
  invalid zone uses the runtime's default zone.

Output fields:

- `action`: `none` (nothing for the reset rule to do), `wait` (every login is
  out and work waits, but pdd uses no reset), `ask` (send the alert in `text`
  to the owner), or `reset` (use one reset on `login` now; after a reset that
  succeeds, send the owner notice in `text`).
- `login`: a login row (the same object that the caller gave) or null. For
  `none` with `quota`, `stale` or `unknown` it is the first login in order with
  that readiness; for `no-work` it is null. For `wait` it is back first (below),
  or null. For `ask` and `reset` it is the chosen login.
- `until`: epoch milliseconds or null. For `none` it is null. For `wait` it is
  back first's `until`, or null. For `ask` and `reset` it is the chosen login's
  natural reset.
- `reason`: one code from the table below.
- `text`: the alert for `ask`, the owner notice for `reset`, else the empty
  string.

Facts for the rule: readiness is `loginReadiness` above. A login **comes back by
itself** when its reason is `week`, `five-hour` or `limited` and its `until` is
not null. **Back first** is the login with the smallest such `until` (the first
in order on a tie). A login's **5-hour window is free** when its usage row has no
5-hour window, or that window is valid and under its stop line. Its **natural
reset** is its readiness `until`.

pdd uses a reset only when all six rules of plan section 6 are true. The checks
run in this order. The first one that stops gives the result:

| Step | Plan rule | Check | Result when it stops |
|---|---|---|---|
| 1 | 1. work waits | `workWaiting` is work | `none`, `no-work` |
| 2 | 2. no other quota | no login is ready | `none`, `quota` |
| 3 | 2 | no login is `stale` (read it again first) | `none`, `stale` |
| 4 | 2 | no login is `unknown` (it may have quota) | `none`, `unknown` |
| 5 | setting | some login allows a reset | `wait`, `not-allowed` |
| 6 | setting | of those, some have a reset left | `wait`, `no-resets` |
| 7 | one per day | of those, some are not in `usedToday` | `wait`, `used-today` |
| 8 | 3. not for a 5-hour limit | of those, some have reason `week` | `wait`, `not-weekly` |
| 9 | 3. the week wait is long | of those, some have a natural reset more than 86400000 ms (24 hours) after `now` | `wait`, `week-soon` |
| 10 | 6. 5-hour window free | of those, some have a free 5-hour window | `wait`, `five-hour-busy` |
| 11 | 6. no login back soon | back first is null, or its `until` is more than 7200000 ms (2 hours) after `now` | `wait`, `back-soon` |
| 12 | 5 and 4 | choose one of the logins left after step 10 | `ask` or `reset` |

Paused logins and logins with `no-login`, `needs-sign-in` or `expired` count as
out in steps 2 to 4: a step cannot use them, and they do not come back by
themselves. A login with reason `limited` (a limit from a step, kind not known)
is never a candidate: pdd does not know which window a reset would clear.

Step 10 and step 11 hold for every decision, not only when a 5-hour limit is
present. When no login is at a 5-hour limit, step 10 passes for every candidate,
so this is the same as plan rule 6. Step 11 applies plan rule 6's sentence "only
when the earliest login that comes back by itself is more than 2 hours away" to
every login: a reset gains little when any login comes back within 2 hours.

Step 12 (plan rules 5 and 4):

1. A candidate's reset **would expire unused** when its `expiresAt` is not null
   and is at or before its natural reset: after the natural reset the login has
   quota again, so that reset would end before it can help.
2. When some candidates would expire unused, choose among them the smallest
   `expiresAt`, then the latest natural reset, then the first in order. Reason
   `expiring`.
3. Otherwise choose the latest natural reset (it gains the most wait), then the
   first in order. Reason `furthest`.
4. The chosen login's setting gives the action: `auto` is `reset`, `ask` is
   `ask`.

## Reset texts

Durations: take whole hours, rounded down. Days are hours / 24 (rounded down),
hours are the rest. Write `1 day` or `N days`, then `1 hour` or `N hours`, joined
by one space; leave out a part that is 0. Under one hour write `1 minute` or
`N minutes` (whole minutes rounded down, at least 1). Example: 54 hours 3 minutes
is `2 days 6 hours`; 48 hours is `2 days`.

Clock time: 24-hour `HH:MM`, one space, and the zone's short generic name from
`Intl.DateTimeFormat` (`timeZoneName: 'shortGeneric'`), for example `14:05 PT`.

Counts: `1 reset` or `N resets`; `1 issue waits` or `N issues wait`.

- `ask` text, with N = `left`:
  `Reset NAME now? Its week resets in DURATION; N resets left; W issues wait. Run: pdd accounts reset NAME`
  Example: `Reset work3 now? Its week resets in 2 days 6 hours; 3 resets left; 4 issues wait. Run: pdd accounts reset work3`
- `reset` text (the owner notice), with N = `left - 1`:
  `Autopilot used a reset on NAME at CLOCK: its week would reset in DURATION; N resets left`
  Example: `Autopilot used a reset on work3 at 14:05 PT: its week would reset in 2 days 6 hours; 2 resets left`

DURATION is the natural reset minus `now`. Neither text ends with a period.

`resetNoticeText({ actor, name, now, until, left, timeZone })` makes the notice
for any actor (`Autopilot`, or `A person at a terminal` for
`pdd accounts reset`): `ACTOR used a reset on NAME at CLOCK`, then `: ` and the
known parts joined by `; `: `its week would reset in DURATION` when `until` is a
finite number after `now`, and `N resets left` (N = `left - 1`) when `left` is a
safe integer of 1 or more. With no known part the text ends after CLOCK.
`resetDecision` uses it with actor `Autopilot`.

## One reset per login per day

`usedTodayFromLog(rows, now)` returns the names (each once, in first-seen order)
of log rows with `action` `reset`, a string `login`, and `at` (an ISO time text
or epoch milliseconds) later than `now - 86400000`. A row with a time after `now`
counts too (another clock can run ahead). A non-array is empty; a row with a time
that does not parse is not counted. "Per day" means the last 24 hours, not the
calendar day, so two resets can never come at 23:59 and 00:01.

## Exports

```js
export function loginReadiness(login, usageRow, now) // -> { ready, reason, until }
export function pickLogin({ logins, usage, now, skip = [] }) // -> { login, readiness } | { login: null, allOut: true, earliest, rows }
export function poolSummary({ logins, usage, now }) // -> { ready, total, next, nextFree }
export function resetDecision({ logins, usage, now, workWaiting, resets, usedToday, timeZone }) // -> { action, login, until, reason, text }
export function resetNoticeText({ actor, name, now, until, left, timeZone }) // -> string
export function usedTodayFromLog(rows, now) // -> [name]
export const STALE_MS = 600000, DAY_MS = 86400000, BACK_SOON_MS = 7200000
```

## Dependencies

- Login pool plan, sections 5 and 6: the "Final plan v2" comment on
  https://github.com/promptdriven/pdd/issues/3252. It owns the six reset rules.
  This prompt states each rule above, so a reader needs no other file.
- Node `Intl.DateTimeFormat` gives the clock time and zone name.
