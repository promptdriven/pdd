# Login facts

Own `src/accounts-login.mjs`. This is the only pdd module that opens a Codex
`auth.json`. The login pool needs a few facts about a login folder (is there a
login, can it renew itself, when does its access end, is it the same account as
another folder) and a safe place to run a usage read. A login file is a
password: a refresh token that leaks or gets used twice can end the login for
every machine that has it. So this module answers with facts only, and the one
copy that it writes holds no refresh token. For a Claude folder it reads
file names only (see [Claude folders](#claude-folders)).

It never logs or saves a token, an account id or an email, and it returns one
only from `readLoginForUpload` (below). It changes the login folder only in
`makeAccessOnly`, and only when the caller proves that the file is still the
one that it uploaded. It never refreshes a login, signs in or signs out, and it
starts no program.

## Exports

- async `codexLoginFacts(home, ports = {})` returns a fresh object with exactly
  `{state, accessExpiresAt, accountKey}`.
- async `withAccessOnlyHome(home, fn, ports = {})` returns what `fn` returns.
- async `readLoginForUpload(home, ports = {})` returns exactly
  `{text, sha256, facts}`.
- async `makeAccessOnly(home, expectedSha256, ports = {})` returns exactly
  `{changed, reason}`.
- async `claudeFolderFacts(dir, ports = {})` returns exactly `{state}` (see
  [Claude folders](#claude-folders)).

`home` is the login folder (`CODEX_HOME`); for Claude, `dir` is the
`CLAUDE_CONFIG_DIR` folder. It must be a non-empty absolute path
string; otherwise every export rejects with `TypeError('A login folder must be
an absolute path.')` before any file access, so a relative path never reads an
`auth.json` from the working folder.

Ports (each optional): `fs` overrides single functions of `node:fs/promises`
(`open`, `lstat`, `mkdtemp`, `chmod`, `writeFile`, `rename`, `rm`, `readdir`); `tmpdir`
is the base folder for the temporary home (default `os.tmpdir()`).

## Reading the login file

Every export reads `<home>/auth.json` the same way:

1. Open it read-only and non-blocking (`O_RDONLY | O_NONBLOCK`), so that a
   named pipe in its place cannot hang the read. A missing file or folder
   (`ENOENT`, `ENOTDIR`) is `none`. Any other open failure is `unreadable`.
2. It must be a regular file, else `unreadable`. A symbolic link is followed:
   the caller judges links from names.
3. Read at most 64 KiB. A file larger than 64 KiB is `unreadable`, because no
   real login file is that large and the read must stay bounded. The file is
   closed on every route.
4. Parse it as UTF-8 JSON. Text that is not JSON, or JSON that is not a
   non-array object, is `unreadable`.
5. `tokens` absent or null is `none`: the file has no ChatGPT login (for
   example an API-key file).
6. `tokens` must be a non-array object with `access_token` a non-empty string
   and `refresh_token` a string (it may be empty). Anything else is
   `unreadable`.

## Facts

| Field | Value |
|---|---|
| `state` | `full` when `refresh_token` is non-empty (the login renews itself); `access` when it is empty (an access-only copy that something else renews); `none`; or `unreadable`. |
| `accessExpiresAt` | Epoch milliseconds: the `exp` claim (Unix seconds) of the access token × 1000. Null when the state is `none` or `unreadable`, or the token's payload (its second dot-separated part, base64url JSON) does not decode to an object with a finite, non-negative numeric `exp` whose milliseconds fit a Date (at most 8.64e15). |
| `accountKey` | The first 16 lower-case hex characters of a SHA-256 (UTF-8) that names one person in one ChatGPT account (see below). It lets the caller refuse the same login twice without keeping the ids. Null when `tokens.account_id` is not a string with non-blank text, or the state is `none` or `unreadable`. |

The account id alone is not enough: every member of a Team or Business
workspace has the same `account_id`, so two people's logins would look like one.
The user id tells them apart. It comes from the `id_token` payload (decoded like
the access token): the first of `["https://api.openai.com/auth"].chatgpt_user_id`,
`["https://api.openai.com/auth"].user_id` and the top-level `sub` that is a string
with non-blank text. This is the claim order of the PDD login server. Both ids
are trimmed. The hashed text is `account_id + "\n" + user id`, or `account_id`
alone when there is no user id (an `id_token` that is missing or does not
decode has none).

`codexLoginFacts` never rejects for any file content or read failure; only the
`home` check rejects.

## Access-only home

`withAccessOnlyHome` gives `fn` a private folder where Codex can use the login
but can never refresh it:

1. Read the login file (above). For `none` or `unreadable`, reject with an
   `Error` whose message is `No readable Codex login in this folder.`, whose
   `code` is `PDD_NO_LOGIN` and whose `state` is that state. It makes no folder
   and does not call `fn`.
2. Make a new folder `mkdtemp(<tmpdir>/pdd-codex-read-)` and set its mode to
   0700.
3. Write `auth.json` in it with mode 0600 (exclusive create). It holds only
   these fields of the source, each kept only when the source has it as a
   string: `auth_mode`, `tokens.id_token`, `tokens.access_token`,
   `tokens.account_id`; and always `tokens.refresh_token` = "" and
   `last_refresh` = the time of the copy (ISO 8601, `Date#toISOString`), so
   that no age rule in Codex starts a renewal. Every other field (for example
   `OPENAI_API_KEY`) is left out, so no other secret enters the folder.
4. Write `config.toml` with mode 0600 and exactly the text
   `cli_auth_credentials_store = "file"` and a newline, so Codex uses this file
   and not the OS credential store.
5. Call `await fn(tempHome, facts)`. `tempHome` is the folder path. `facts` are
   the facts of the file that was copied, the same shape as `codexLoginFacts`.
6. Once `mkdtemp` has made the folder, always remove it (`rm` recursive and
   force): after `fn` returns, after `fn` throws or rejects, and after a
   failure in steps 2 to 4.

Outcome precedence, first match wins:

| Case | Result |
|---|---|
| The folder could not be removed | Reject with an `Error` with `code` `PDD_TEMP_HOME_LEFT`, `path` = the folder and the message `Could not remove the temporary login folder <path>.` A folder that holds a token on disk matters more than any other outcome. |
| Step 2, 3 or 4 failed | Reject with an `Error` with `code` `PDD_TEMP_HOME_FAILED` and the message `Could not make the temporary login folder.` `fn` is not called. |
| `fn` threw or rejected | Reject with that same error. |
| Otherwise | Resolve with `fn`'s value. |

A process that is killed while `fn` runs can leave the folder; it is 0700 and
holds no refresh token.

## Login text for an upload

`readLoginForUpload` is the only function that returns a login's text. The
caller sends it once as the upload body to the login server and never logs,
saves or shows it. It reads the file as above. For `none` or `unreadable` it
rejects with the same `PDD_NO_LOGIN` error as `withAccessOnlyHome`. Otherwise
`text` is the file's bytes as UTF-8, `sha256` the lower-case hex SHA-256 of those
bytes, and `facts` the facts of that text.

## Make the local file access-only

After a confirmed upload the server is the login's only refresher, so the local
file must stop renewing. `makeAccessOnly` rewrites `<home>/auth.json` with
`tokens.refresh_token` = "" and every other field unchanged, but only when the
file still has the bytes that the caller uploaded. If Codex renewed the file in
between, the uploaded refresh token is already spent and the local file must
stay as it is. `expectedSha256` must be 64 lower-case hex characters, else it
rejects with `TypeError('expectedSha256 must be a SHA-256 hex digest.')` before
any file access.

First match wins:

| Case | Result |
|---|---|
| `auth.json` is a symbolic link (`lstat`) | `{changed: false, reason: 'link'}`. A rename would cut the link from its target. |
| The read gives `none` or `unreadable` | `{changed: false, reason: 'no-login'}` |
| The bytes' SHA-256 differs from `expectedSha256` | `{changed: false, reason: 'bytes-changed'}` |
| `refresh_token` is already "" | `{changed: false, reason: 'already-access'}` |
| Otherwise | Rewrite (below), then `{changed: true, reason: 'rewritten'}`. |

Rewrite: write the new JSON (2-space indent and a newline) to a new file
`<home>/.auth.json.pdd-<16 random hex>.tmp` (exclusive create, mode 0600) and
sync it. Then read `auth.json` again; when its SHA-256 no longer matches, remove
the temporary file and return `{changed: false, reason: 'bytes-changed'}`. Else
rename the temporary file over `auth.json`. The rename is atomic, so a reader
sees the old file or the new one, never a part. A failure in these steps removes
the temporary file, leaves `auth.json` as it was and rejects with an `Error`
with `code` `PDD_ACCESS_ONLY_FAILED` and the message
`Could not make the login file access-only.` A renewal that lands between the
second read and the rename can still be lost; the window is a few milliseconds.

## Claude folders

A Claude login is a `CLAUDE_CONFIG_DIR` folder that a person signed into with
the normal `claude` sign-in. Its credential is `.credentials.json` in that
folder (Linux) or a macOS Keychain item. Anthropic's terms forbid a third party
to collect or store Claude.ai credentials, so pdd only chooses which folder a
step uses and never reads the credential.

`claudeFolderFacts` decides from names only. It makes exactly one file-system
call, `readdir(dir)` (names, no file types), and no other: it never opens,
stats or reads `.credentials.json`, `.claude.json` or any other file in the
folder, and it starts no program (so never `security`, the Keychain tool).

| Case | `state` |
|---|---|
| `readdir` lists `.credentials.json` or `.claude.json` | `present` |
| `readdir` fails (missing, not a folder, no access) or lists neither name | `none` |

`present` means that Claude Code has used the folder. It does not prove a live
sign-in; the step's own output shows that (a limit or sign-in message). It never
rejects except for the `dir` check.

## Dependencies

- Node `node:fs/promises`, `node:os`, `node:path` and `node:crypto` (SHA-256).
- Navigation only: the [login usage read](accounts-usage.prompt.md) runs Codex
  in the access-only home.
