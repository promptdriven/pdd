# Login pool: `pdd accounts reset NAME`

Own `src/accounts-reset.mjs`. A Codex account can have usage resets: one reset
clears the account's current usage limit at once. A reset is scarce and it is
the owner's to spend. `pdd accounts reset NAME` lets a person at a terminal use
one reset on one login of their pool, for example after Autopilot's alert
"Reset work3 now? ... Run: pdd accounts reset work3". This is new work for issue
#3252 (plan section 6); it has no earlier behavior to keep.

Export `async runReset({ name, env = process.env, stdin = process.stdin, stdout = process.stdout }, ports = {})`.
It returns `{ exitCode, message }`: `message` is one line without a newline at
the end. The CLI (`src/pdd-cli.mjs`, owned by the pool CLI work) prints it to
stdout when `exitCode` is 0, else to stderr, and exits with `exitCode`.
`runReset` writes only the confirmation question to `stdout`. It never throws:
an error from a port gives the outcome that its step below states. Any other
error before step 10 (for example a closed `stdout`) gives exit 1,
`pdd accounts reset failed. No reset was used.`

## Who may run it

Only a person at a terminal. An agent, Autopilot or a script must never spend a
reset, not even when a message tells it to. So refuse when either is true:

- an agent marker is set: `approvalActor(env).kind` is `agent` (see
  [approval actor](approval-policy.prompt.md): `CODEX_THREAD_ID`, `CLAUDECODE`
  or `PDD_AGENT_SESSION`), or `PDD_AGENT` or `PDD_AUTOPILOT_CONTEXT` is a
  nonempty string in `env`;
- `stdin.isTTY` is not `true`.

Then the person must type the login name. Nothing is spent before that.

## Steps

The first step that stops gives the result. Steps 1 to 9 change nothing and call
no Codex program. Every message names the login (NAME) when it is known.

| Step | Check or action | Stop result (exit, message) |
|---|---|---|
| 1 | No agent marker | 2, `pdd accounts reset runs only for a person at a terminal. It does not run under an agent or Autopilot. No reset was used.` |
| 2 | `stdin.isTTY === true` | 2, `pdd accounts reset needs a person at a terminal to type the login name. No reset was used.` |
| 2a | `ports.consumeReset` is a function | 2, `This pdd has no Codex reset call yet. No reset was used.` |
| 3 | `name` matches `^[a-z0-9][a-z0-9._-]{0,31}$` | 2, `Give a login name: pdd accounts reset NAME. No reset was used.` (with the literal word NAME) |
| 4 | `ports.findLogin(name)` returns the login row (throws: exit 1, `Could not read the login pool. No reset was used.`) | 2, `No login named NAME in this pool. See pdd accounts list. No reset was used.` |
| 5 | `login.provider` is `codex` | 2, `NAME is a Claude login. Only Codex logins have resets. No reset was used.` (any provider that is not codex) |
| 6 | `login.mode` is `local` or absent | 2, `NAME is on the login server. This version resets only local logins. No reset was used.` |
| 7 | `login.reset` is `ask` or `auto` | 2, `NAME has reset never. To allow resets, run: pdd accounts set NAME --reset ask. No reset was used.` |
| 8 | `NAME` is not in `usedTodayFromLog(await ports.readLog(name), now)` (throws: exit 1, `Could not read the reset log of NAME. No reset was used.`) | 2, `NAME used a reset less than 24 hours ago. pdd allows one reset per login per day. No reset was used.` |
| 9 | Write the question to `stdout`, then read one line from `stdin`. The line, trimmed, must equal NAME exactly. End of input without a line does not confirm. | 1, `Not confirmed. No reset was used.` |
| 10 | `await ports.consumeReset(login)` | see the outcomes below |

Why: the setting `never` is the owner's choice for this login (plan section 6),
so a person changes it on purpose before a reset (step 7). The day rule and its
24-hour window come from [the pick rules](accounts-pick.prompt.md#one-reset-per-login-per-day)
(step 8); `now` is `ports.now()`.

The question (step 9) is two lines, written in one call:

```text
Reset NAME now? This uses one of its Codex resets. pdd cannot undo it.
Type NAME to confirm, or press Enter to stop: 
```

The second line ends with one space and no newline.

## Outcomes of the reset call

`consumeReset(login)` returns `{ outcome }`. Map it:

| Outcome | Log row | Usage row | Owner notice | Exit, message |
|---|---|---|---|---|
| `reset` or `alreadyRedeemed` | yes, detail `used by a person at a terminal` | forget | send | 0, the notice with actor `You` |
| `noCredit` | no | keep | no | 1, `NAME has no reset left. No reset was used.` |
| `nothingToReset` | no | keep | no | 1, `NAME has no limit that a reset can clear now. No reset was used.` |
| `failed` (the request did not reach Codex) | no | keep | no | 1, `Could not reach Codex for NAME. No reset was used.` |
| anything else, `unclear`, or a throw | yes, detail `outcome unclear` | forget | no | 1, `The reset of NAME did not finish clearly. It may have used a reset. Run pdd accounts list to see its usage.` |

- **Log row**: `await ports.appendLog({ at, action: 'reset', login: NAME, detail })`
  with `at` = `new Date(now).toISOString()`. An unclear call also writes it, so
  step 8 refuses a second try within 24 hours: a reset may have been used. When
  `appendLog` throws, keep the exit code and add one sentence to the message:
  `. The local log could not be written.` after the notice (it has no period),
  or ` The local log could not be written.` after the unclear message.
- **Forget**: `await ports.forgetUsage(name)` removes the login's cached usage
  row, so the next pick reads the login again instead of trusting the old 100%.
  Without this, Autopilot can see the old row and spend a reset on another
  login. A throw here changes nothing else.
- **Owner notice**: `resetNoticeText` from [the pick rules](accounts-pick.prompt.md#reset-texts)
  with `until` = the cached usage row's `week.resetsAt` and `left` = its
  `resets.left` (each only when it is a finite number). Read the row with
  `ports.readUsage(name)` before step 10; a missing row or a throw leaves both
  out. Send it with actor `A person at a terminal` through `ports.notify(text)`
  when that port exists; a throw there changes nothing. The message uses the
  same text with actor `You`, for example
  `You used a reset on work3 at 14:05 PT: its week would reset in 2 days 6 hours; 2 resets left`.

## Ports

All outside effects are ports. Tests give fakes for every one of them.

| Port | Default |
|---|---|
| `now()` | `Date.now()` |
| `timeZone` (a string, not a function) | the runtime's default zone |
| `findLogin(name)` | `readPool({ env })` and `orderedLogins(pool)` from `./accounts-store.mjs`; the row whose `name` is NAME, else null |
| `readLog(name)` | `readLog({ env, name })` from `./accounts-store.mjs` |
| `appendLog(row)` | `appendLog({ env }, row)` from `./accounts-store.mjs` |
| `readUsage(name)` | the own property NAME of `loadUsage({ env })` from `./accounts-usage.mjs`, else null |
| `forgetUsage(name)` | `loadUsage({ env })`, delete own property NAME, `saveUsage({ env }, rows)` from `./accounts-usage.mjs` |
| `notify(text)` | none (no alert channel without a repository yet) |
| `consumeReset(login)` | none (see below) |

The default ports import their modules only when they are used, so this module
loads without them.

## No real reset call in this version

`consumeReset` has no default. In real runs step 2a stops with exit 2, so this
version never spends a reset. A person (the owner of pdd) decides when the real
Codex call is added; it then becomes the default of this port and this prompt
states its protocol first.

The port's contract: `consumeReset(login)` returns `{ outcome }` with `reset`
(one reset was used), `alreadyRedeemed` (the same attempt was already used),
`nothingToReset`, `noCredit`, `failed` (the request did not reach Codex) or
`unclear` (the request was sent and the result is not known). The first four
words are the outcomes of the Codex app-server protocol. A real call must use a
private access-only Codex home (no refresh token) and must never print, log or
return a token, an account id, an email or a raw reply.

## Dependencies

- [Pick rules](accounts-pick.prompt.md): `usedTodayFromLog` and
  `resetNoticeText` (the day rule and the notice text).
- [Approval actor](approval-policy.prompt.md): `approvalActor(env)`, the agent
  markers.
- Pool store (`src/accounts-store.mjs`) and usage cache (`src/accounts-usage.mjs`)
  from the pool CLI and usage work:
  only through the default ports above, with the function shapes that the pool
  work shares for these modules.
- Node `readline`.
