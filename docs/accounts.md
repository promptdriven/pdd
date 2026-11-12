# How pdd keeps your logins safe

`pdd accounts` keeps a list of your Codex logins in the order that agent steps use them: the login pool.
This page tells you what pdd stores, what it reads, what it sends and how you can check the code.
In this version, every login stays on your machine. The login server is not on (see [Not in this version](#not-in-this-version)).

## What pdd never does

- pdd never puts a token in its pool file, its usage cache, its log or its output.
- pdd never refreshes a login. Codex refreshes its own login, as it does without pdd.
- pdd never moves a login folder and never copies a full login.
- pdd never signs a login out. A sign-out ends the login on every machine that uses it.
- pdd runs a sign-in only when you run `pdd accounts add` at a terminal.

## What pdd stores on your machine

| File | What it holds |
|---|---|
| `~/.config/pdd/accounts.json` | The pool: the name and folder of each login, the order, pause, stop lines and settings. No token. |
| `~/.local/state/pdd/accounts/usage.json` | The last usage read: plan, percent used, reset times and when access ends. No token. |
| `~/.local/state/pdd/accounts/log.jsonl` | One line for each change: time, action, login name and a short detail. pdd removes text that looks like an email address or an access token before it writes a line. |
| `~/.config/pdd/machine.json` | Only when you use a login server: a random id and the short name of this machine. |
| Each login folder, for example `~/.pdd/codex/NAME` | Codex's own `auth.json`. This file is the real login. Codex writes it. |

When `XDG_CONFIG_HOME` or `XDG_STATE_HOME` is set, pdd uses those folders.
pdd writes its files with mode 0600, so only your user can read them.

## How pdd reads a login

- One file, `src/accounts-login.mjs`, reads a Codex `auth.json`. It reads at most 64 KiB.
  It gives the rest of pdd only facts: a full login or an access copy, when access ends, and a short hash that tells two logins apart.
- For the usage read, pdd makes a private temporary folder (mode 0700). It puts an access copy of the login there: the refresh token is empty.
  It starts `codex app-server` in that folder and sends only `initialize`, `initialized` and `account/rateLimits/read`. Then it deletes the folder.
  Without a refresh token, this read cannot refresh the login.
- pdd does not read a login whose access ends within 10 minutes.
- `pdd accounts list` shows the result. Its first line says "Read only: no refresh, nothing spent."

## One refresher for each login

Codex keeps a login alive with its refresh token. Each refresh gives a new refresh token, and the old one stops working.
When two machines hold the same full login, one machine refreshes it. Then the other machine sends a spent token, and OpenAI can end the login.
So each login must have exactly one refresher.

- In this version, the refresher is Codex on the machine that has the full login. It refreshes the login when it runs.
- Keep each full login on one machine. pdd refuses the same login twice in one pool. It cannot see your other machines.
- A login with an empty refresh token is an access copy. It cannot refresh itself, and it works until its access ends.
  `pdd accounts list` shows it as `access copy`.

## Add, import and remove

- `pdd accounts import PATH` adds a folder that has a Codex login. pdd does not change the login file.
  It refuses a folder whose `auth.json` is a link, a folder that is in the pool, and a login that is in the pool under another name.
- `pdd accounts add NAME` needs a person at a terminal. pdd makes `~/.pdd/codex/NAME` (mode 0700).
  It tells Codex to keep the login in a file in that folder, not in the system key store. Then it runs Codex's own sign-in (`codex login --device-auth`).
  When the sign-in does not finish, pdd deletes the folder.
- `pdd accounts remove NAME` takes the login out of the pool. It does not sign out. It keeps every folder that pdd did not make.
  For a folder that `add` made, it asks you first. The default is to keep the folder.
- Each login has a reset setting. It is `never` by default, and only a person at a terminal can change it.

## Local only

`--local` on `add` and `import` keeps a login on this machine, also when a login server is set.
In this version, every login is local.

## Claude Code

The pool takes Codex logins only. pdd never reads a Claude Code credential file or the system key store.
The login server does not take Claude logins.

## The login server

The PDD login server keeps logins in one central place, so that a new machine needs only your GitHub sign-in.
It is not on. It has no address, and pdd sends it no login.
pdd talks to a login server only when `PDD_ACCOUNTS_URL` or the pool file gives its address.
Without an address, `share`, `unshare`, `accept`, `leave` and `group create` stop with "This needs the PDD login server. It is not set up on this machine."
This section tells you what the server code does.

- **Your identity.** pdd sends your GitHub token (from `gh auth token`) only in a request header.
  It sends it only over HTTPS, or over plain HTTP to localhost. It does not follow redirects.
  The server uses the token only for GitHub reads: who you are, your orgs and teams, and the users that you name.
  It keys your data by your numeric GitHub id. It keeps only a hash of the token, for 5 minutes.
- **Storage.** The server seals each full login before it stores it: AES-256-GCM with a new 256-bit key for each write.
  A Cloud KMS key of the owner wraps that key. Each person and each group has its own KMS key.
  Each sealed login is bound to its owner, its login id and its version. It does not open as another login or as an older version.
  The rest of the row (name, owner, plan, usage, times, settings) has no token.
- **Who opens a login.** Only two parts of the server open a sealed login: the copy desk and the refresher (not built).
  Nobody gets the full login back, not a member and not the owner.
- **What a machine gets.** The copy desk gives a machine an access copy: the refresh token is empty and there is no API key. The copy cannot refresh itself.
  The copy desk gives a login only when its access lasts 6 more hours or more. It writes an audit row before the copy leaves.
  pdd saves the copy under `~/.local/state/pdd/accounts/homes/` (mode 0600) and refuses a copy that could refresh.
- **Order.** Your own logins come first, then the shared logins that you accepted. The copy desk skips paused logins and logins at their limit.
- **Sharing.** `pdd accounts share NAME --with USER,...` shares a login with GitHub users. Nothing is shared until each person runs `pdd accounts accept NAME`.
  A member stops with `pdd accounts leave NAME`.
- **Groups.** `pdd accounts group create GROUP --with USER,...` makes a group of GitHub users. To take a person out, run the same command with the new list.
  `--github ORG[/TEAM]` makes a group that follows a GitHub org or team. The server checks each member with the member's own GitHub token, again after 10 minutes.
  The owner puts a login in a group with `pdd accounts add NAME --group GROUP`. Each member accepts a group once.
- **Audit log.** The server writes one row for each add, copy, usage report, share, unshare, accept, leave, pause, resume, settings change and remove.
  A row has the time, the action, the login, the GitHub user and the machine. Only the owner reads it, with `pdd accounts log NAME`.

What a removal ends, and when:

| You do | Ends at once | Ends later |
|---|---|---|
| The owner removes the login from the server | The server deletes the sealed login. It gives no new copies. | Copies that machines have work until their access ends, about 10 days. |
| The owner unshares a person, or a member leaves | That person gets no new copies. | The same. |
| A person leaves the GitHub org or team of a group | That person gets no new copies, at the latest after 10 minutes. | The same. |

To end every copy at once, sign the Codex account out at OpenAI.

## Check the code yourself

pdd is open source. These files hold the login pool code of pdd.
Each file has its prompt in `prompts/cli/` and its tests in `test/`. Ask your own agent to read them and check this page.

| File | What it does |
|---|---|
| `src/accounts-login.mjs` | The only file that reads a Codex `auth.json`. It gives facts, never a token, and makes the temporary folder for the usage read. |
| `src/accounts-usage.mjs` | The read-only usage read and the usage cache. |
| `src/codex-limits.mjs` | Starts `codex app-server` and sends the usage read. |
| `src/accounts-store.mjs` | The pool file and the local log. |
| `src/accounts-pick.mjs` | Which login is ready and which one comes next. It reads no files. |
| `src/accounts-command.mjs` | The `pdd accounts` commands. |
| `src/accounts-cloud.mjs` | The login server client, and the folder for an access copy. |
| `src/autopilot-pool.mjs` | The Autopilot side of the pool. Autopilot does not call it in this version. |

`grep -n "auth.json" src/*.mjs` shows each line of the pdd source that names a login file.
The login server is part of PDD Cloud. Its code is not public.

## Not in this version

- The login server is not on, and it has no address.
- pdd does not upload a login. With a server address set, `add` and `import` without `--local` keep the login on this machine and say "pdd accounts upload is not ready yet. Use --local."
- `order`, `pause`, `resume`, `set` and `remove` change only the pool on this machine, not the server.
- The server refresher. The server code that refreshes a stored login is not built.
- Autopilot does not pick logins from the pool.
- No pdd command lists or removes your machines on the server. The server knows a machine only by the id that pdd sends.
- Claude Code folders in the pool.
- How long a removed login stays in server backups is not set.
