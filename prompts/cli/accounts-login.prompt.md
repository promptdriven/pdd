# Codex login facts

Own `src/accounts-login.mjs`. This is the only pdd module that opens a Codex
`auth.json`. The login pool needs a few facts about a login folder (is there a
login, can it renew itself, when does its access end, is it the same account as
another folder) and a safe place to run a usage read. A login file is a
password: a refresh token that leaks or gets used twice can end the login for
every machine that has it. So this module answers with facts only, and the one
copy that it writes holds no refresh token.

It never returns, logs or saves a token, an account id or an email. It never
writes into, moves, renames or deletes anything in the login folder. It never
refreshes a login, signs in or signs out, and it starts no program.

## Exports

- async `codexLoginFacts(home, ports = {})` returns a fresh object with exactly
  `{state, accessExpiresAt, accountKey}`.
- async `withAccessOnlyHome(home, fn, ports = {})` returns what `fn` returns.

`home` is the login folder (`CODEX_HOME`). It must be a non-empty absolute path
string; otherwise both exports reject with `TypeError('A login folder must be an
absolute path.')` before any file access, so a relative path never reads an
`auth.json` from the working folder.

Ports (each optional): `fs` overrides single functions of `node:fs/promises`
(`open`, `mkdtemp`, `chmod`, `writeFile`, `rm`); `tmpdir` is the base folder
for the temporary home (default `os.tmpdir()`).

## Reading the login file

Both exports read `<home>/auth.json` the same way:

1. Open it read-only. A missing file or folder (`ENOENT`, `ENOTDIR`) is
   `none`. Any other open failure is `unreadable`.
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
| `accountKey` | The first 16 lower-case hex characters of the SHA-256 of `tokens.account_id` (UTF-8). It lets the caller refuse the same account twice without keeping the id. Null when `account_id` is not a non-empty string, or the state is `none` or `unreadable`. |

`codexLoginFacts` never rejects for any file content or read failure; only the
`home` check rejects.

## Access-only home

`withAccessOnlyHome` gives `fn` a private folder where Codex can use the login
but can never refresh it:

1. Read the login file (above). For `none` or `unreadable`, reject with an
   `Error` whose message is `No readable Codex login in this folder.` and whose
   `code` is `PDD_NO_LOGIN`. It makes no folder and does not call `fn`.
2. Make a new folder `mkdtemp(<tmpdir>/pdd-codex-read-)` and set its mode to
   0700.
3. Write `auth.json` in it with mode 0600 (exclusive create). It holds only
   these fields of the source, each kept only when the source has it as a
   string: `auth_mode`, `tokens.id_token`, `tokens.access_token`,
   `tokens.account_id`, `last_refresh`; and always `tokens.refresh_token` = "".
   Every other field (for example `OPENAI_API_KEY`) is left out, so no other
   secret enters the folder.
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

## Dependencies

- Node `node:fs/promises`, `node:os`, `node:path` and `node:crypto` (SHA-256).
- Navigation only: the [login usage read](accounts-usage.prompt.md) runs Codex
  in the access-only home.
