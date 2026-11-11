# Login pool file and local log

Own `src/accounts-store.mjs`. It keeps the person's login pool on this machine:
the pool file (which logins exist, their order and settings) and a local log of
changes. `pdd accounts`, Autopilot and the login server client read and change
the pool only through this module, so one place owns the file format, the lock
and the safe write. The pool file never holds a token: a login stays in its own
folder (`home`), and pdd never copies, moves or opens that folder's login here.

## Paths

`poolPaths(env = process.env, ports = {})` returns
`{ configDir, stateDir, poolFile, logFile, usageFile, machineFile }`, all absolute:

| Key | Path |
|---|---|
| `configDir` | `$XDG_CONFIG_HOME/pdd` when `XDG_CONFIG_HOME` is an absolute path, else `HOME/.config/pdd` |
| `stateDir` | `$XDG_STATE_HOME/pdd/accounts` when `XDG_STATE_HOME` is an absolute path, else `HOME/.local/state/pdd/accounts` |
| `poolFile` | `configDir/accounts.json` |
| `logFile` | `stateDir/log.jsonl` |
| `usageFile` | `stateDir/usage.json` (the usage module owns its content) |
| `machineFile` | `configDir/machine.json` (the login server client owns its content) |

HOME counts only when `env.HOME` is an absolute path; else use
`ports.userInfo().homedir` (default `os.userInfo`) when it is absolute. Without
an absolute home and without the matching absolute XDG folder, throw a
`PoolError` with code `no-home` and the message
`pdd accounts needs an absolute home folder; set HOME to an absolute path.`
This keeps the pool and the log out of a checkout.

## Pool file (version 1)

The file is one JSON object:

| Field | Meaning |
|---|---|
| `version` | Always `1`. |
| `order` | Array of strings: the person's order of login names. A shared login from a server later appears as `OWNER/NAME`. |
| `logins` | Array of login rows (below). |
| `server` | `null` (local mode), or an object with string `url`. |
| `homesDir` | Optional absolute path; the base folder for new logins that `pdd accounts add` makes. |

A login row:

| Field | Meaning | Default when missing |
|---|---|---|
| `name` | Matches `^[a-z0-9][a-z0-9._-]{0,31}$`; unique in the file. | required |
| `provider` | `codex` or `claude`. | required |
| `home` | Absolute path of the login folder (`CODEX_HOME` or `CLAUDE_CONFIG_DIR` for a step). | required |
| `source` | `import` (an existing folder) or `add` (pdd made the folder). | `import` |
| `mode` | `local` or `cloud`. Version 1 writes only `local`. | `local` |
| `paused` | Boolean. True takes the login out of the pick; it keeps its place in `order`. | `false` |
| `reset` | `never`, `ask` or `auto`. Only a person at a terminal changes it. | `never` |
| `stop` | `{ week, fiveHour }`: stop lines in percent, each a finite number from 1 to 100. A missing part takes its default. | `{ week: 97, fiveHour: 97 }` |
| `addedAt` | ISO 8601 time when the row was added, or absent. | absent |

Keep every unknown field, at the top level and in each row, unchanged on
every write: a newer pdd may add fields. A missing `order` is `[]`; a missing
`server` is `null`.

A file that is not valid JSON, has a `version` other than 1, or breaks a rule in
the tables above is never overwritten. `readPool` and `updatePool` throw a
`PoolError` with code `invalid` and the message
`The pool file PATH is not valid: PROBLEM. pdd did not change it. Fix or move the file, then try again.`
PROBLEM names the first broken rule in a few words, for example
`login 2 has no valid name` or `the name cx5 is used twice`. The message never
quotes file content beyond a login name that passes the name rule.

`PoolError` is an exported `Error` subclass with name `PoolError` and a string
`code`.

## Read

`readPool({ env } = {}, ports = {})` returns the pool. A missing file gives the
empty pool `{ version: 1, order: [], logins: [], server: null }` and writes
nothing. A present file is checked as above and returned with the defaults of
missing optional fields filled in. Other read errors propagate.

## Change

`updatePool({ env } = {}, change, ports = {})` changes the pool safely and
returns the pool that it wrote. In this order:

1. Make the config folder when it is missing (mode 0700; a folder that exists keeps its mode).
2. Take the lock (below).
3. Read the pool as `readPool` does. An invalid file stops here (the lock is released).
4. Call `change(pool)` (it may be async) and use the pool it returns. When `change` throws, write nothing and throw the same error.
5. Check the returned pool with the same rules. A broken pool throws `PoolError` code `invalid-change` with message `pdd did not save the pool: PROBLEM.` and writes nothing.
6. Write it: a new temp file in the same folder (exclusive create, mode 0600), the JSON with two-space indent and a final newline, fsync, close, then rename over `accounts.json`. A failed step removes the temp file and leaves the old pool file as it was.
7. Release the lock in every case.

The lock is the file `accounts.json.lock` next to the pool file, made with
exclusive create (mode 0600). When the lock exists, wait and try again every
50 ms. A lock whose modification time is more than 30 s before now is stale:
remove it and try again. After 5 s of waiting, throw `PoolError` code `busy`
with message `Another pdd process is changing the pool (LOCKPATH). Try again.`
Only the process that made the lock removes it at release. Never hold the lock
while a person or another program works (for example a sign-in): callers do
slow work first, then call `updatePool`.

`ports` may supply `fs` (the `node:fs/promises` functions `open`, `readFile`,
`rename`, `unlink`, `stat`, `mkdir`, `appendFile`), `now()` (epoch ms, default
`Date.now`) and `sleep(ms)` (default a timer). Tests use them for clock and
failure cases; ordinary callers pass nothing.

## Order

`orderedLogins(pool)` returns new login row objects in effective order, each
with an added `position` (1-based place in that order). Effective order: first
the logins named in `order`, in that order (an unknown name or a repeat is
skipped); then every other login by `addedAt` (oldest first; rows without
`addedAt` after the dated ones; ties keep file order). Paused logins keep their
place and their `position`. The function does not read files and does not
change its input.

## Local log

`appendLog({ env } = {}, row, ports = {})` adds one line of JSON to the log file
and returns the saved row `{ at, action, login, detail }`:

- `at`: ISO 8601 time; default now.
- `action`: a short word, `^[a-z][a-z-]{0,31}$` (for example `import`, `add`, `order`, `pause`, `resume`, `set`, `remove`, `limit`). Else throw `PoolError` code `invalid-log`.
- `login`: a login name (the name rule, or `OWNER/NAME`), or `null` for a change to the whole pool.
- `detail`: one short line of text, at most 300 characters (longer text is cut), newlines replaced by spaces; default `''`.

The log never holds a token or an email. Before it saves `detail`, the store
replaces each email-like text (`x@y.z`) and each JWT-like text (three
base64url parts that start with `eyJ`) with `[removed]`. Callers still never
pass a secret. Make the state folder when it is missing (mode 0700) and append
with mode 0600 for a new file. One line per call: concurrent appends do not
mix lines.

`readLog({ env, name, limit = 100 } = {}, ports = {})` returns saved rows, oldest
first: the last `limit` rows, only the rows of login `name` when it is given.
A missing log gives `[]`. A line that does not parse as a row object is
skipped.

## Dependencies

Node built-ins only: `node:fs/promises` for files, `node:path`, `node:os`
(`userInfo`) and `node:crypto` (random temp names). This module is native-only
for now: its files, modes, lock, fsync, rename and clock have no complete
executable Runtime interface. Native tests own those boundaries: the file
format, modes 0600 and 0700, the lock and a stale lock, the atomic write after a
failed rename, unknown fields kept, a bad file never overwritten, and no lost
change when many changes run at once.
