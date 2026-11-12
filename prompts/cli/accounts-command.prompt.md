# pdd accounts: the login pool command

Own `src/accounts-command.mjs`. Export async module function
`runAccounts({ action, operands, options, cwd, env, stdin, stdout, stderr }, ports = {})`
that returns the exit code. The PDD CLI calls it for every `pdd accounts` route
(see [command catalog](command-catalog.prompt.md#login-pool-pdd-accounts)).
`action` is the route word after `accounts` (`group create` is `group-create`);
`operands` and `options` are the parsed words, with the catalog's option names
as keys. The pool file, its lock and the local log belong to the
[pool store](accounts-store.prompt.md); this module never writes them in
another way.

A person uses this command to see which Codex logins this machine has, how much
of each login's usage is left, and in which order agent steps use them. It
replaces hand-made folder lists and usage scripts. It must never cost the person
anything or break a login:

- It never refreshes a login, never signs out (`logout` revokes a shared login for everyone), never uses a usage reset or credits, and never prints, logs or saves a token, an account id or an email.
- It never opens a login file. Only the login facts module reads `auth.json`; this module may look at file names, kinds and links only.
- It never copies, moves or changes a login file. It deletes only a folder that `add` made, after a person types `y` at a terminal.
- Only a person at a terminal runs a sign-in or changes the reset setting.

Exit codes: 0 done; 1 refused or failed (one clear line on stderr); 2 wrong use
(a bad option combination, a needed terminal is missing, or a needed module is
missing). A `PoolError` from the store prints its message on stderr and exits 1.
Other errors propagate to the CLI.

## Modules from other packages

These ports are loaded only when a command needs them. A port given in `ports`
wins; `null` means missing; else import the module next to this one.

| Port | Module | Functions used |
|---|---|---|
| `accountsLogin` | `accounts-login.mjs` | `codexLoginFacts(home)` -> `{ state: 'full'\|'access'\|'none'\|'unreadable', accessExpiresAt, accountKey }` |
| `accountsUsage` | `accounts-usage.mjs` | `readAllUsage(logins, { env, now })` (fresh read, saves the cache), `loadUsage({ env })` (cache only) |
| `accountsPick` | `accounts-pick.mjs` | `loginReadiness(login, usageRow, now)` -> `{ ready, reason, until }`, `poolSummary({ logins, usage, now })` -> `{ ready, total, next, nextFree }` |
| `accountsCloud` | `accounts-cloud.mjs` | `runCloudAccounts(action, input)` -> `{ exitCode, message }` |
| `accountsReset` | `accounts-reset.mjs` | `runReset({ name, env, stdin, stdout })` -> exit code or `{ exitCode, message }` |

Usage results may be an array (in login order, or rows with `name`) or an object
keyed by login name, optionally under `rows`; use them as a map from name to
usage row. `next` may be a name or a login row. A module that is missing, or that
lacks the function, gives one line on stderr and exit 2, before any change:
`pdd accounts ACTION needs src/MODULE, which this pdd does not have yet.`
An import error other than "this module file is missing" propagates.

Other ports: `spawn` (default `node:child_process` `spawn`), `codexCommand`
(default `codex`), `now()` (epoch ms, default `Date.now`), `timeZone` (default
the machine zone from `Intl`), and the store ports (`fs`, `sleep`, `userInfo`),
which pass through to the store.

The login server is set when `env.PDD_ACCOUNTS_URL` is nonblank or the pool's
`server.url` is set.

## Rules shared by the commands

- A login NAME matches the store's name rule. An unknown NAME gives `No login named NAME.` and exit 1.
- A person at a terminal means `stdin.isTTY` and `stdout.isTTY` are both true.
- Every change writes one local log row (`appendLog`) with the action word of the command and the login name (or `null` for the order). Read-only commands write no row.
- Slow work (a sign-in, an editor) happens before `updatePool`, never under its lock. Inside the change, check the names again against the pool read under the lock.

## list

`pdd accounts list [--json] [--no-read]` shows every login in effective order
(`orderedLogins`). With no logins it prints
`No logins on this machine yet. Run pdd accounts import PATH or pdd accounts add NAME.`
(with `--json`, the JSON below with empty `logins`) and exits 0.

1. Login facts: `codexLoginFacts(home)` for each Codex login.
2. Usage: without `--no-read`, `readAllUsage(rows, { env, now })`; with `--no-read`, `loadUsage({ env })` only. This read is read-only: it never refreshes and spends nothing.
3. Readiness: `loginReadiness(row, usage[name] ?? null, now)` for each row (with `--no-read`, an old cache row gives `stale`), and `poolSummary({ logins: rows, usage, now })`.

The text output (times in the `timeZone`):

```text
Logins on this machine (local mode, no login server). Usage read 14:58 PST. Read only: no refresh, nothing spent.

#   NAME   KIND         PLAN  WEEK  WEEK RESETS   5H    5H RESETS     ACCESS ENDS   STATE
1   cx5    login        team  39%   Nov 17 12:49  31%   Nov 11 18:53  Nov 21 14:33  ready
2   cx6    login        team  16%   Nov 18 11:48  100%  Nov 11 16:48  Nov 21 08:56  limited (5h) until Nov 11 16:48
3   work3  access copy  pro   100%  Nov 13 15:28  -     -             Nov 21 10:02  limited (week) until Nov 13 15:28
4   work2  access copy  pro   32%   Nov 16 17:34  -     -             Nov 21 10:02  ready
-   cx2    login        team  37%   Nov 17 12:49  0%    Nov 11 19:42  Nov 15 17:50  paused
-   work1  access copy  -     -     -             -     -             Oct 27 23:02  access ended (this read never refreshes)

Next step uses cx5. Ready: 2 of 6. Next free: cx6 at Nov 11 16:48 PST.
Resets: never for every login.
```

- Header: `Logins on this machine (MODE). READ Read only: no refresh, nothing spent.` MODE is `local mode, no login server`, or `local logins only; this pdd does not list login server logins` when a server is set. READ is `Usage read TIME.` (or `Usage from the cache, read TIME.` with `--no-read`), where TIME is the newest `readAt` of the shown usage rows: `HH:MM ZONE` on the same local day as now, else `Mon D HH:MM ZONE`. With no usage row, READ is `No usage read yet.`
- Columns, separated by at least two spaces, each as wide as its widest cell (`#` at least 2 wide), trailing spaces removed. `-` is an empty cell.
  - `#`: the login's `position`, or `-` when the reason is `paused`, `no-login`, `expired` or `needs-sign-in` (the pick cannot use it until a person acts).
  - `KIND`: `login` (facts `full`), `access copy` (facts `access`), `claude folder` (Claude), else `-`.
  - `PLAN`: the usage `plan`. `WEEK` and `5H`: `usedPercent` rounded down, with `%`. `WEEK RESETS`, `5H RESETS` and `ACCESS ENDS` (usage `accessExpiresAt`, else the facts): `Mon D HH:MM` (24-hour clock, no zone).
  - `STATE` by reason: `ready`; `paused`; `no login`; `access ended (this read never refreshes)` (`expired`); `needs sign-in`; `limited (week)` and `limited (5h)` (`week`, `five-hour`); `limited` (`limited`; `limited (credits)` when the usage `limitReason` is `credits`); `stale`; `unknown`, plus ` (NOTE)` when the usage row has a nonblank `note`. A limit reason with a known `until` adds ` until Mon D HH:MM`.
- Footer line 1: `Next step uses NAME.` (or `No login is ready now.`), then `Ready: R of T.`, then `Next free: NAME at Mon D HH:MM ZONE.` when `nextFree` is set.
- Footer line 2: `Resets: SETTING for every login.` when all logins share one setting; else `Resets: ask for A, B; auto for C; never for the others.` (only the settings in use, in the order ask, auto; names in effective order).

`--json` prints one JSON object (two-space indent):
`{ mode, readAt, logins, next, ready, total, nextFree }` with `mode` `local`,
`readAt` the newest usage `readAt` (epoch ms) or `null`, `next` a name or `null`,
`ready` and `total` numbers, `nextFree` `{ name, at }` or `null`. Each `logins`
item is `{ position, name, provider, kind, plan, week, fiveHour, accessExpiresAt, state, reason, until, paused, reset }`:
`position` is the place in the order (a number, also for paused logins); `kind`
is the KIND text or `null`; `plan` a string or `null`; `week` and `fiveHour`
`{ usedPercent, resetsAt }` (epoch ms) or `null`; `accessExpiresAt` epoch ms or
`null`; `state` the STATE text; `reason` and `until` from readiness.

## import

`pdd accounts import PATH... [--name NAME] [--provider codex|claude] [--local]`
registers existing login folders. It never copies, moves or changes a login file.
`--provider claude` is refused (exit 2): `pdd accounts import takes Codex folders only for now.`
`--name` with more than one PATH is refused (exit 2): `Use --name with one PATH only.`

For each PATH (made absolute from `cwd`), in this order, the first refusal wins:

| Check | Refusal line |
|---|---|
| No folder at PATH | `No folder at PATH.` |
| PATH is a link | `PATH is a link (to TARGET). pdd imports only a folder with its own login file.` |
| PATH is not a folder | `PATH is not a folder.` |
| `PATH/auth.json` is a link | `PATH/auth.json is a link (to TARGET). pdd imports only a folder with its own login file.` |
| No `auth.json`, or facts `none` | `No Codex login in PATH. Use pdd accounts add NAME to sign in.` |
| Facts `unreadable` | `pdd cannot read the Codex login in PATH.` |
| The name (`--name`, else the folder's base name) breaks the name rule | `NAME is not a valid login name. Use --name NAME with a-z, 0-9, ., _ or - (at most 32).` |
| The name is in the pool or used by an earlier PATH | `The name NAME is in use. Use --name NAME.` |
| The same folder is in the pool | `PATH is already in the pool as NAME.` |
| The same `accountKey` as a pool login or an earlier PATH | `PATH has the same Codex account as NAME. pdd keeps one name for each account.` |

The links matter because a linked folder or file (for example
`~/.pdd-codex/interactive` -> `~/.codex`) would put one login under two names,
and two refreshers of one login break it. The account check uses the facts of
the pool's Codex logins.

The accepted folders are added in one `updatePool` as rows
`{ name, provider: 'codex', home, source: 'import', mode: 'local', paused: false, reset: 'never', stop: { week: 97, fiveHour: 97 }, addedAt }`;
`order` does not change. Each prints `Imported NAME from PATH (KIND).` on stdout
and logs `import` with detail `folder PATH`. Refusals print on stderr; the
others are still imported. Exit 0 when all PATHs are imported, else 1.

## add

`pdd accounts add NAME [--provider codex|claude] [--group GROUP] [--local]` makes
a new login folder and runs Codex's own device sign-in in it. Refusals, in
order, before any change:

1. `--provider claude`: exit 2, `pdd accounts add takes Codex logins only for now.`
2. `--group` without a login server: exit 2, `--group needs the PDD login server. It is not set up on this machine.`
3. Not a person at a terminal: exit 2, `pdd accounts add needs a person at a terminal: it runs the Codex sign-in.`
4. A bad name: exit 1, `NAME is not a valid login name. Use a-z, 0-9, ., _ or - (at most 32).` A name in use: exit 1, `The name NAME is in use.`
5. The folder exists: exit 1, `FOLDER exists. Use pdd accounts import FOLDER, or move it away first.`

The folder is `HOMES/codex/NAME`, where HOMES is the pool's `homesDir`, else
`HOME/.pdd`. Make the parents (0700) and the folder (0700, exclusive), and
write `config.toml` (0600) with the one line
`cli_auth_credentials_store = "file"`, so Codex keeps the login in this folder
and never in the system key store. Print
`Signing in to Codex for NAME in FOLDER. Follow the Codex steps below.`
Then run `codexCommand login --device-auth` with `CODEX_HOME` = FOLDER in the
given environment, with the terminal inherited, and wait for it to end.

The sign-in counts only when the command exits 0 and the facts of FOLDER are
`full`. Else, and when the new login has the same `accountKey` as a pool login,
remove FOLDER (pdd made it in this command) and exit 1 with
`The Codex sign-in did not finish. pdd removed FOLDER; nothing was added.` or
`This Codex account is in the pool as NAME. pdd removed FOLDER; nothing was added.`
On success add the row (as import, with `source: 'add'`), log `add` with detail
`folder FOLDER`, print `Added NAME (FOLDER).` and exit 0.

## Upload to a login server

After `import` or `add` saves its rows, when a login server is set and
`--local` is not given, call `runCloudAccounts('upload', { name, provider, home, group, env })`
for each new login, print its message (stdout for exit 0, else stderr) and
return the first nonzero exit code. When the cloud module is missing, print the
missing-module line and exit 2; the local rows stay. Without a server nothing
is uploaded.

## order

`pdd accounts order [NAME...] [--first NAME | --last NAME | --after NAME NAME | --edit]`

- With nothing else, print the order and exit 0: `Pool order (steps use the first ready login):`, then one line per login: `POSITION  NAME`, plus `  paused` for a paused login.
- Use at most one of: NAMEs, `--first`, `--last`, `--after`, `--edit`. Else exit 2: `Use one of NAME..., --first NAME, --last NAME, --after NAME OTHER or --edit.` `--after` takes exactly two names, the login to move and the login it goes after, and they differ; else exit 2: `Use --after NAME OTHER: it moves NAME right after OTHER.`
- `NAME...` puts these logins first, in this order; the others follow in their current order. A name given twice: exit 2, `NAME is named twice.`
- `--first NAME` and `--last NAME` move one login to the start or the end; `--after NAME OTHER` moves NAME right after OTHER.
- `--edit` needs a person at a terminal (else exit 2, `pdd accounts order --edit needs a person at a terminal.`) and `VISUAL`, else `EDITOR` (else exit 2, `Set VISUAL or EDITOR, or use pdd accounts order NAME...`). Write the current order, one name per line under two `#` comment lines that explain the file, to a new private temp folder (0700, file 0600). Run the editor through `/bin/sh -c 'EDITOR "$1"'` with the file as `$1` and the terminal inherited, then read the names back (skip blank and `#` lines) and use them as `NAME...`. A nonzero editor exit: exit 1, `The editor stopped with code N. The order did not change.` Always remove the temp folder.
- An unknown name: exit 1, `No login named NAME.`

The saved `order` is the new effective order of all logins, then any old
`order` entries that are not local logins (kept, so a shared login keeps its
entry). When it equals the current effective order, print `Order unchanged.`
and write nothing. Else save, log `order` (login `null`, detail the names joined
by `, `), print `New pool order:` and the order lines, and exit 0.

## pause, resume

`pdd accounts pause NAME` sets `paused` true: the pick skips the login, and it
keeps its place in the order. Print `Paused NAME. Steps skip it; it keeps its place in the order.`
`pdd accounts resume NAME` sets it false and prints `Resumed NAME.` When nothing
changes, print `NAME is already paused.` or `NAME is not paused.`, write nothing
and exit 0.

## set

`pdd accounts set NAME [--stop-week N] [--stop-5h N] [--reset never|ask|auto]`.
Without options print `NAME: stop lines week W%, 5h F%; reset R.` and exit 0.
The stop lines (1 to 100, checked by the catalog) set `stop.week` and
`stop.fiveHour`.

`--reset` changes whether pdd may use a Codex usage reset on this login. Only a
person changes it, because a reset is the person's resource and our agents
never spend one. When it is given and the value differs from the saved one:
refuse unless a person is at a terminal and `PDD_AGENT` is unset or blank (exit
2, before any change):
`Only a person at a terminal can change the reset setting. Run pdd accounts set NAME --reset VALUE in your own terminal.`
At the terminal, write one line that says what the value does (`never`: pdd
never uses a reset on NAME; `ask`: pdd asks you before it uses a reset on NAME;
`auto`: Autopilot may use a reset on NAME by itself when every login is out, at
most one a day, and tells you), then `Type yes to set reset to VALUE for NAME: `,
and read one line from stdin. Only the trimmed answer `yes` goes on; else print
`The reset setting did not change.` and exit 1 with no change.

Save, log `set` with detail naming the changed values, print
`Saved NAME: stop lines week W%, 5h F%; reset R.` and exit 0.

## remove

`pdd accounts remove NAME` forgets the row and removes NAME from `order`. It
never signs out and never deletes a folder that pdd did not make.

- `source: 'import'`: keep the folder; print `pdd kept FOLDER (pdd did not make it).`
- `source: 'add'` and FOLDER is `HOMES/codex/NAME` (the folder that `add` makes): at a terminal, ask `Delete FOLDER too? It holds the Codex login of NAME. [y/N] ` before the change; only `y` or `yes` (any case) deletes, and only when FOLDER is a real folder, not a link. Without a terminal, for any other answer, or for an `add` row with another folder, keep it: `pdd kept FOLDER.`

Print `Removed NAME from the pool. pdd did not sign out.` first. Log `remove` with
detail `kept folder` or `deleted folder`. A failed delete prints
`pdd could not delete FOLDER.` and exits 1; the row stays removed.

## home

`pdd accounts home NAME` prints the login's folder, one line, for wrappers that
start Codex with `CODEX_HOME`. No log row.

## log

`pdd accounts log [NAME] [--json]` shows the local log (`readLog`, the last 100
rows; only NAME's rows when given, also for a login that is gone). Text: one
line per row, `Mon D HH:MM ZONE  ACTION  LOGIN  DETAIL` (`-` for no login); no
rows: `No changes in the local log yet.` `--json` prints `{ rows }`. When a
login server is set, then call `runCloudAccounts('log', { name, json, env })` for
the server's log and print its message.

## Login server forms and reset

These forms call the other packages and own no rule here:

| Form | Call |
|---|---|
| `share NAME --with USER,...`, `unshare NAME --with USER,...` | `runCloudAccounts('share' \| 'unshare', { name, with, env })` |
| `accept NAME`, `leave NAME` | `runCloudAccounts('accept' \| 'leave', { name, env })` |
| `group create GROUP (--with USER,... \| --github ORG[/TEAM])` | `runCloudAccounts('group-create', { name: GROUP, with, github, env })` |
| `reset NAME` | `runReset({ name, env, stdin, stdout })` |

`with` is the `--with` text split at commas, trimmed, blanks dropped. `share`
and `unshare` without names in `--with`: exit 2, `Use pdd accounts ACTION NAME --with USER,...`
`group create` needs exactly one of `--with` and `--github`: else exit 2,
`Use pdd accounts group create GROUP --with USER,... or --github ORG[/TEAM].`
Print the reply message (stdout for exit 0, else stderr) and return its exit
code.

## Dependencies

- [Pool store](accounts-store.prompt.md): required generation and test context for the pool file, order, lock and local log.
- [Command catalog](command-catalog.prompt.md#login-pool-pdd-accounts): the routes, options and value checks.
- The other modules in the table above are loaded at run time; their shapes are in the table. Tests inject fakes with these shapes.

Node built-ins only: `node:child_process` (`spawn`), `node:fs/promises`,
`node:path`, `node:os` (`tmpdir`) and `Intl` for times. This command is
native-only for now: the terminal, the sign-in program, the editor, files and
the clock have no complete executable Runtime interface. Native tests own the
list output from fake usage rows, every order form, the import refusals, the
kept folders on remove, and the reset refusal without a terminal.
