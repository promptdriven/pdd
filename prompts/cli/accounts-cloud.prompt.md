# Login server client (pdd accounts, cloud side)

Own `src/accounts-cloud.mjs`: the HTTP client for the PDD login server (#3252).
It shares a login, accepts and leaves a shared login, makes groups, shows the
server audit log, gives `pdd accounts list` the server rows and invites, asks the
copy desk for a login at an agent step and writes the access-only run home for
it. The `pdd accounts` routes and the local pool belong to
`src/accounts-command.mjs` and `src/accounts-store.mjs`; they call this module.

Why: a full Codex login has a refresh token that rotates. Two places that renew
the same login break it, and a copy that can renew itself can be stolen for
good. So the server is the only place that renews a pooled login, and a machine
only ever holds an access-only copy (`refresh_token` = ""). The person's GitHub
login (the `gh` token) is the only credential this module sends; it never
reaches a message, an error, a file or a log.

## Server address and local mode

`cloudUrl(env, pool)` returns the server base URL as a string that ends in `/`,
or `null` (local mode). `env.PDD_ACCOUNTS_URL`, when it is a nonempty string,
wins over `pool.server.url`; `pool` may be `null` or `undefined`. A value must
parse as a URL with protocol `https:`, or `http:` only for the hosts
`127.0.0.1`, `localhost` or `[::1]`, with no user name, password, query or
fragment. A path is allowed (requests go below it). Any other value throws an
`Error` with `exitCode` 2 and the message `PDD_ACCOUNTS_URL must be an HTTPS
address, for example https://accounts.example.` (when the value came from the
environment) or `The server address in accounts.json must be an HTTPS address,
for example https://accounts.example.` (when it came from the pool file).

Local mode text (exact): `This needs the PDD login server. It is not set up on
this machine.` Every server action returns exit 2 with this line in local mode,
before it reads the gh token or the input names. (Only an unknown action is
refused before it.)

## Public contract

```ts
cloudUrl(env: object, pool?: object | null): string | null
runCloudAccounts(action: string, input?: object, ports?: object): Promise<{ exitCode: number, message: string }>
cloudList(input?: { env?, pool? }, ports?): Promise<ListResult | Failure>
cloudCopy(input?: { env?, pool?, provider?: 'codex', skip?: string[], pin?: string }, ports?): Promise<CopyResult | Failure>
writeCopyHome(input: { env?, name: string, auth: string }, ports?): HomeResult | Failure
```

- `input.env` defaults to `process.env`. `input.pool` is the pool object of
  `accounts-store.mjs`. When it is `undefined` and `PDD_ACCOUNTS_URL` is not
  set, the module reads it with `ports.readPool({ env })`, else with `readPool({ env })`
  from `./accounts-store.mjs` (dynamic import); a missing store module means no
  pool (the environment alone decides). An error from the pool read gives
  `input` (exit 2) with its message as a safe text.
- The module also exports `LOCAL_MODE_TEXT` (the local mode line). The error
  that `cloudUrl` throws has `exitCode` 2 and `code` `input`.
- `Failure` = `{ ok: false, code, exitCode, message }`. `message` is one safe
  line. Codes and exit codes:

| code | exitCode | When |
|---|---|---|
| `local` | 2 | No server address (local-mode text). |
| `input` | 2 | A bad name, user list, group, team or provider; a bad server address. |
| `sign-in` | 5 | No `gh`, no gh token, `gh api user` failed, or the server answered 401. |
| `not_found`, `forbidden`, `conflict`, `invalid`, `needs_sign_in`, `all_out`, `refused` | 1 | The server said no (its error code; `refused` for any other 4xx), or the listing has no such login. |
| `unavailable` | 3 | No answer, a network error, a timeout, HTTP 408, 429 or 5xx, or error code `unavailable`. |
| `bad_reply` | 3 | A reply that is not the documented JSON shape, or a redirect. |
| `unsafe_copy`, `bad_copy`, `not_copy_home`, `home_error` | 1 | `writeCopyHome` refused or failed (below). |

- `runCloudAccounts` returns the Failure's `exitCode` and `message`, or
  `{ exitCode: 0, message }` on success. It never throws for these cases.

### Actions and input

All names are checked before gh is read and before any request (a bad one:
`input`, `NAME is not a login name. Use lower-case letters, digits, dots,
dashes or underscores (at most 32), or OWNER/NAME.`, NAME shown as a safe text
of at most 60 characters). A login name is
`^[a-z0-9][a-z0-9._-]{0,31}$`, or `OWNER/NAME` for a login of another person
(OWNER is a GitHub login, `^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})$`). A group name
uses the login name rule. `with` is an array of strings or one string; each item
may hold commas; items are trimmed, empty items dropped, duplicates (ignoring
case) dropped, first spelling kept; each must be a GitHub login. `github` is
`ORG` or `ORG/TEAM` (TEAM: `^[A-Za-z0-9._-]{1,100}$`).

| action | input | Request(s) | Success message |
|---|---|---|---|
| `share` | `name`, `with` and/or `group` (at least one) | resolve own login; `POST /v1/accounts/{id}/share` `{ with, group? }` (`with` may be empty when `group` is set) | `Shared NAME with ali, mehtab. Each person accepts it with: pdd accounts accept NAME`; with a group the list ends ` and group friends`; a group alone: `Shared NAME with group friends. Each member accepts it once.` |
| `unshare` | `name`, `with` (not empty) | resolve own login; `POST /v1/accounts/{id}/unshare` `{ with }` | `ali gets no new copies of NAME. A copy that is already on a machine works until its access ends (TIME).` (`get` for two or more people; `TIME` with its zone from the reply `accessExpiresAt`; without it the sentence ends at `ends.`) |
| `accept` | `name` | resolve an invite; `POST /v1/accounts/{id}/accept` | `You accepted OWNER/NAME. Your steps use it after your own logins.` |
| `leave` | `name` | resolve a shared login, else an invite; `POST /v1/accounts/{id}/leave` | `You left OWNER/NAME. You get no new copies of it.` |
| `group-create` | `name`, exactly one of `with` or `github` | `POST /v1/groups` `{ name, with }` or `{ name, github }` | `Made group NAME with ali, mehtab. Each member accepts it once.` or `Made group NAME. It follows GitHub team ORG/TEAM. Each member accepts it once.` (`GitHub org ORG` for an org) |
| `log` | `name?`, `json?` | resolve own login(s); `GET /v1/accounts/{id}/log` for the one login, or for each own login when no name | the audit table below, or with `json` the text `JSON.stringify({ rows }, null, 2)` (rows sorted as in the table, each with exactly the six Audit fields `at, action, login, actor, machine, detail`; a string is a safe text, a finite number stays, anything else is null; a missing `login` is the login's name) |
| `upload` | (not built: waits for the group lead's decision on how an upload moves a full login) | none | exit 2: `pdd accounts upload is not ready yet. Use --local.` |

Any other action: exit 2, `Unknown pdd accounts server action: ACTION.`

Resolving uses one `GET /v1/accounts`. "Me" is the GitHub user of the gh token
(below). A row is own when `owner.id` equals my numeric id (as strings), or,
when the id is absent, `owner.login` equals my login ignoring case. The display
name of an own row is `name`; of another person's row `OWNER/NAME` with the
server's owner spelling.
- Own login: a bare `NAME`, or `OWNER/NAME` where OWNER is me. Not found:
  `not_found`, `You have no login named NAME on the PDD login server. Run pdd accounts list.`
- Invite (accept): matches `invites` by `NAME` or `OWNER/NAME` (owner ignoring
  case). No match: `not_found`, `No invite for NAME. Run pdd accounts list.`
  Two or more for a bare name: `input`, `Two people share a login named NAME
  with you. Use OWNER/NAME: A/NAME, B/NAME.`
- Shared login (leave): first rows that are not own, then invites, by the same
  matching. No match: `not_found`, `You have no shared login named NAME. Run pdd accounts list.`

Audit table (log): a header line `Server log for NAME (newest last). Times in ZONE.`
(`for your logins` when no name; ZONE is the short zone name), a blank line, then
columns `TIME`, `ACTION`, `LOGIN`, `BY`, `MACHINE`, `DETAIL` padded to the widest
cell with two spaces, rows sorted by time, oldest first. No rows:
`No server log rows for NAME.` Each cell is a safe text (below); a missing value is `-`.

### List, copy and the run home

`cloudList` returns `{ ok: true, url, me: { login, id }, logins, invites, order, groups, inviteLines }`:
- `logins`: each server Row with `display` (display name), `shared` (true when
  not own) and `kind` (`cloud login` own, `shared by OWNER` otherwise), plus the
  Row fields `id, name, owner, provider, plan, reset, stop, paused, state, week,
  fiveHour, accessExpiresAt, refreshOkAt, sharedWith, group` as sent (absent stay
  absent), with every string in them as a safe text. Other Row fields are dropped.
- `invites`: each Invite (strings as safe text) with `display` (`OWNER/NAME`); `inviteLines`: one line each,
  `OWNER shares NAME with you. Accept it with: pdd accounts accept NAME`
  (`... accept OWNER/NAME` when two invites share the name; `via` a group adds
  ` (group GROUP)` after `with you`).
- `order`: the server `order` ids mapped to display names (unknown ids dropped).
- `groups`: the server Groups as sent.

`cloudCopy` sends `POST /v1/copy` `{ provider, skip?, pin? }` (`skip` and `pin`
are server login ids; empty `skip` and absent `pin` are not sent). Only
`provider` `codex` is allowed; `claude` gives `input`, `Claude logins stay on
this machine. The PDD login server does not hold them.` Error code `all_out`
gives `{ ok: false, code: 'all_out', exitCode: 1, message, earliest }` with
`earliest` = `{ id, name, at }` (name = display name when the id is in the
listing, else null) from `error.earliest` or the top-level `earliest`, or null;
message `No login on the PDD login server has quota now.` plus ` Next free: NAME at TIME.`
when known. A good reply `{ login: Row, auth, expiresAt, copyId }` is written
with `writeCopyHome` under the display name; the result is
`{ ok: true, name, login, home, expiresAt, copyId }`. The auth text is never in
the result, a message or a file other than the run home's `auth.json`.

`writeCopyHome({ env, name, auth })` writes an access-only Codex home:
1. `name` must be a login name or `OWNER/NAME`, else `input`. The folder is
   `<state>/homes/NAME` for an own name and `<state>/homes/@owner/NAME` (owner
   in lower case) for `OWNER/NAME`; an own name never starts with `@`, so they
   never collide.
2. `auth` must be a string of at most 64 KiB that parses as a JSON object with
   an object `tokens` whose `access_token` is a nonempty string and whose
   `refresh_token` is exactly `""`; else `bad_copy`, `The login server sent a
   copy of NAME that pdd can not read. pdd did not save it.` A
   `refresh_token` that is a nonempty string, or any key named
   `refresh_token` at any depth with a value other than `""`, `null` or absent,
   gives `unsafe_copy`, `The login server sent a copy of NAME that can renew
   itself. pdd did not save it. Tell the server owner.` These checks run before
   any file is touched.
3. `<state>/homes`, `<state>/homes/@owner` and the login folder are made with
   mode 0700 (and set to 0700). None of them may be a symbolic link. A login
   folder that exists, is not empty and has no marker file `.pdd-copy-home`
   gives `not_copy_home`, `FOLDER is not a folder that pdd made for copies.
   pdd did not write there.` (FOLDER relative to the home folder as `~/...`
   when inside it). pdd writes the marker into a new or empty folder; a
   marker that another step made at the same moment counts as its own.
4. `config.toml`: written (0600) as `cli_auth_credentials_store = "file"\n`
   when it is missing or has no top-level line that sets that key to `"file"`.
5. `auth.json`: `JSON.stringify(parsed, null, 2) + "\n"` (the parsed object,
   never the raw text, so a duplicate key can not hide a refresh token), into a
   new temp file in the same folder (exclusive create, 0600), fsync, then
   rename over `auth.json` (a link there is replaced, never followed), then
   0600. A temp file is removed on any failure.
6. Any file error: `home_error`, `pdd could not write the copy of NAME (CODE).`
   Success: `{ ok: true, home }` (absolute folder path).

## The gh token, identity and requests

- Token: `ports.gh(['auth', 'token'])` returns `{ status, stdout, stderr, error }`.
  The default runs the first `gh` on `env.PATH` (else `process.env.PATH`) that
  is a file or link and is not a PDD Try launcher (its first 64 bytes contain
  `PDD Try launcher v1`), with `spawnSync`, stdin ignored, a 60 s limit, as
  `src/runtime-client.mjs` does. No program, or `error.code` `ENOENT`:
  `sign-in`, `Install the GitHub CLI, then run gh auth login.` A nonzero
  status or an empty trimmed stdout: `sign-in`, `Run gh auth login.`
  The token is passed to `rememberSecrets` at once.
- Me: `ports.gh(['api', 'user', '--jq', '.login + " " + (.id|tostring)'])`;
  stdout `LOGIN ID` with a GitHub login and a decimal id. Else `sign-in`,
  `pdd could not read your GitHub login (gh api user). Run gh auth status.`
  It is read only when an action needs it (share, unshare, leave, log, list,
  copy), once per token per process (keyed by a sha256 of the token).
- Every request: `ports.fetch(url, { method, headers, body, redirect: 'manual', signal })`
  with `Authorization: Bearer TOKEN`, `Accept: application/json`,
  `User-Agent: pdd/VERSION`, `X-PDD-Machine: ID`, `X-PDD-Machine-Name: NAME`
  and `Content-Type: application/json` when there is a body. Time limit
  `ports.timeoutMs` (default 15 000 ms). Paths are relative to the base URL
  (`v1/accounts`, ...); ids are encoded with `encodeURIComponent`.
- Machine: `<config>/machine.json` `{ "id": "m_<16 hex>", "name": "<short host name>" }`.
  Read it when it holds a valid id (`^m_[0-9a-f]{16}$`) and a name of 1 to 63
  of `[A-Za-z0-9._-]`; else make it: config folder 0700, exclusive create
  0600, `ports.randomHex(8)` for the id, the first label of `ports.hostname()`
  cleaned to those characters (`machine` when empty). When another process
  made it first, read that file. A bad existing file is not overwritten: its
  values are not used and the request sends a fresh in-memory id.
- Config folder: `$XDG_CONFIG_HOME/pdd` when `XDG_CONFIG_HOME` is absolute,
  else `HOME/.config/pdd`. State folder:
  `$XDG_STATE_HOME/pdd/accounts` when absolute, else `HOME/.local/state/pdd/accounts`.
  HOME is `env.HOME`, else the OS home.
- Replies:

| Reply | Result |
|---|---|
| fetch throws (refused, not found, timeout, TLS) | `unavailable`: `pdd could not reach the PDD login server at HOST (REASON). Check your network and PDD_ACCOUNTS_URL.` |
| 3xx | `bad_reply`: `The PDD login server at HOST sent a redirect. pdd does not follow it with your GitHub login. Check PDD_ACCOUNTS_URL.` |
| 401 | `sign-in`: `The PDD login server did not accept your GitHub login (HTTP 401). Run gh auth login, then run the command again.` |
| other 4xx/5xx | the error code (table above); message = the server's `error.message` as a safe text, else `The PDD login server refused this (HTTP STATUS, CODE).` (`unavailable` codes: `The PDD login server is not available now (HTTP STATUS). Try again later.` when it sent no message) |
| 2xx, not a JSON object | `bad_reply`: `The PDD login server sent a reply that pdd can not read (HTTP STATUS). Nothing was saved.` |

- A reply body larger than 1 MiB is a `bad_reply`. Each Row and Invite of a
  listing, and the Row of a copy reply, must have a string `id` of 1 to 128
  `[A-Za-z0-9_-]`, a `name` by the login name rule and an `owner` object whose
  `login` is a GitHub login; a listing must have `logins`, `invites`, `order`
  (strings) and `groups` (objects) arrays; a copy reply needs a string `auth`.
  Else `bad_reply`. The reply of share, unshare, accept, leave and group
  create only needs to be a JSON object. A copy reply's `expiresAt` is epoch
  milliseconds (an ISO string is converted) or null; `copyId` is kept when it
  has the id form, else null. One `GET /v1/accounts` is made at most once per call.
- Safe text: the value as a string with each known secret (the token) replaced
  by `[secret]`, then `redactSecrets` of `src/secret-redaction.mjs`, runs of
  white space as one space, trimmed, at most 300 characters. Every server
  string that reaches a message or the audit table is a safe text.
- Times: `MMM D HH:MM` in `ports.timeZone` (default the machine zone),
  24-hour, with the short zone name in the header only. A time is epoch
  milliseconds or an ISO string; anything else is `-`.

## Ports

`{ fetch, gh, readPool, hostname, randomHex, timeZone, timeoutMs }`, all
optional. Defaults: `globalThis.fetch`, the gh program above, the store's
`readPool`, `os.hostname`, `crypto.randomBytes(n).toString('hex')`, the machine
zone, 15 000 ms.

## Dependencies

- [Secret redaction](secret-redaction.prompt.md): `rememberSecrets` and
  `redactSecrets`, required for the safe text rule (generation and tests).
- The login server API v1 and the pool file are the shared design of #3252
  (DESIGN.md sections 2, 3, 5 and 7 of the pool group). The store module
  (`src/accounts-store.mjs`) supplies `readPool` when it is present.
- Node 22 built-ins: `fetch`, `node:child_process`, `node:crypto`, `node:fs`,
  `node:os`, `node:path`. No npm package.
- Tests use `test/helpers/fake-accounts-server.mjs`: an in-process `node:http`
  server with the API v1 in memory, fake gh tokens and fake logins only.
