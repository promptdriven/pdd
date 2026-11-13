# CLI reference

This page lists every command of pdd 0.1.29, as `pdd --help` shows it. A test (`test/docs-commands.test.mjs`) checks that each command form of the help is on this page.

You need the pdd command only for runs with PRs, for `pdd test`, `pdd lint`, `pdd simulate` and `pdd approve`. Install the skills with `npx skills add promptdriven/pdd` (add `-g` for all your projects), and set up a repo with the `pdd-setup` skill in your agent. For simulations that your agent drives, use the Try tools in `pdd mcp`. Then use a PDD skill: `pdd-feature`, `pdd-bug`, `pdd-small-change`, `pdd-product` or `pdd-prompting`. Call a skill with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code (or ask for it by name). See [Install](USAGE.md#2-install).

Typing `pdd check` or `pdd try` runs nothing and prints the name of the command to use.

## Set up a repo

| Command | What it does |
|---|---|
| `pdd setup [--yes]` | Check for a ready agent, install the seven [PDD skills](USAGE.md#4-the-pdd-skills) when they are missing, and say where. Then add or update the short PDD block (7 lines, between `<!-- pdd:start -->` and `<!-- pdd:end -->`) in `CLAUDE.md` of this folder, else in `AGENTS.md`. If neither exists, make `AGENTS.md`. In a Git repository, add the line `.pdd/` at the end of the root `.gitignore` when no line there is `.pdd`, `.pdd/`, `/.pdd` or `/.pdd/`; `pdd test` keeps its local cache there. Setup only appends: all other bytes stay the same. When the last such line starts with `!`, or no such line exists but a `!` line names `.pdd` or a path in it (such as `!.pdd/config.json`), setup changes nothing and says so. Repeat setup keeps an existing Autopilot mode |

`pdd setup` copies the skills to `~/.agents/skills` (Codex and Gemini) and `~/.claude/skills`, or `$CLAUDE_CONFIG_DIR/skills` when it is an absolute path (Claude Code). If `npx skills` already installed them, it copies nothing. When the skills it finds are older than this pdd, or differ from its skills, it says so and prints the command that updates them: `npx skills add promptdriven/pdd -g -a codex -a claude-code -y`, without `-g` for a copy in the project. After an update of the pdd command, it replaces an older or same-version differing copy with the `.pdd-skill.json` marker, including an invalid marker. It never touches a copy without the marker, or a symlink. When `pdd --version` or `pdd setup` reports older skills, it names each affected skill and its installed version, for example `pdd-feature is 0.1.20`. Run `pdd setup` to update copies installed by pdd in user folders. For copies from another installer, use the shown `npx skills add` command. No other pdd command copies skills. The `pdd-setup` skill adds the project block and ignore rule in a chat; it installs nothing and does not register MCP tools. Run it in the top folder of the repo.

Setup previews the exact MCP configuration changes for the Codex, Claude Code and Gemini agents it finds, then asks once (y/N). Only `y` writes those changes, including the approval setting for this Codex server. Registrations pin this running pdd executable, so another installation earlier on PATH cannot receive its tools. Other configuration is preserved. Codex uses `$CODEX_HOME/config.toml` (default `~/.codex/config.toml`) and the `mcp_servers.pdd` entry with `default_tools_approval_mode = "approve"`. Claude Code uses the `mcpServers.pdd` entry in its configuration; Gemini uses `mcpServers.pdd` in `~/.gemini/settings.json` with server trust. Each entry runs `pdd mcp`. A conflicting existing entry is preserved and reported.

Setup also reports the running pdd executable and version, the `pdd` paths in order, and which path and version a plain `pdd` selects. A PATH conflict report includes the absolute command for this pdd and explains that environment activation, such as conda, must come before correcting PATH. It keeps other installations. `--version` preserves its version-only stdout; PATH diagnostics go to stderr. `workflow run` gives a one-line warning when another pdd comes first.

## Repository Autopilot settings

`pdd setup` asks for `off`, `observe` or `auto` once in a Git repository with a terminal. An empty answer selects `off`. It shows the owner and available write-access people, warns when lookup is incomplete, and optionally asks for additional GitHub names. Repeat setup keeps the saved mode and can add names. Without a terminal on both stdin and stdout, with `--yes`, or outside Git, it asks no Autopilot questions and saves no Autopilot settings. Without both terminals or with `--yes`, setup also declines interface drafting and MCP registration without asking, even when called by an agent. The normal skills, project block and ignore-file actions still run. A symlinked agent config is skipped with a warning and exit 0; incomplete GitHub owner lookup also warns without failing setup. Required write failures and malformed configs still return an error.

| Command | What it does |
| --- | --- |
| `pdd autopilot off` | Save mode `off` |
| `pdd autopilot observe` | Save mode `observe` |
| `pdd autopilot auto` | Save mode `auto` |
| `pdd autopilot trust NAME...` | Add one or more explicitly trusted GitHub names |
| `pdd autopilot untrust NAME` | Remove one explicitly trusted GitHub name |

Settings live in the repository's `pdd.json`, for example `{"autopilot":{"mode":"off","trust":[]}}`. Other settings are preserved. Autopilot on this machine reads `pdd.json` of this checkout. Its job worktrees, other machines and other people read `pdd.json` of the default branch on GitHub. So `pdd autopilot off`, `observe`, `auto`, `trust` and `untrust` also update `pdd.json` on the default branch, through the GitHub API with your `gh` sign-in. Each command makes only its own change on GitHub: a mode command sets `autopilot.mode`, `trust` adds its names to `autopilot.trust`, and `untrust` removes its name. All other keys and fields keep the GitHub values, also when your checkout is behind. The commit message says what changed, and the commit changes only those bytes of `pdd.json`: the indent and the key order of the file stay. They do not touch your current branch or your uncommitted work. More lines tell the result:

- GitHub is already up to date.
- The commit URL, then `pdd.json on GitHub is updated. To update your local copy, run git restore pdd.json, then git pull.` `git restore pdd.json` drops your local change of `pdd.json`, which GitHub now has. Run `git pull` on the default branch.
- When the default branch accepts changes only through a PR: the URL of a PR from a `pdd/autopilot-settings-…` branch, which you must merge before the GitHub copy has the new setting. While that PR is open, the next command adds its change to the same PR. When the new setting is the same as on the default branch, pdd closes the PR with a short comment.
- When the copy on GitHub then has other settings than your checkout, one more line shows both.

When another change of `pdd.json` on GitHub comes between pdd's read and its write, pdd reads the file again and tries once more. When GitHub cannot be reached or `gh` is not signed in, the local setting stays, the exit code is 0, and the line tells you to run the same command again. `pdd autopilot start` and `pdd autopilot status` print a warning when the copy on GitHub has another mode or trust list, with the commands that change it, or when a settings PR is still open, with its URL. The warning says that Autopilot on this machine uses this checkout's settings (and this machine's `--mode` and `--label`, when set), and that other machines and people read the GitHub copy. `pdd setup` saves a first mode only in your checkout and never writes to GitHub; it prints the command that puts the mode there. Invalid saved modes count as `off` with a notice; setup leaves them unchanged, and a mode command replaces them. Names match ignoring case. The repository owner, people with write access (including access through an organization team), and explicitly added names are trusted independently. An incomplete lookup never establishes trust for an unknown person.

These commands store settings and determine trust. Selecting a mode starts no run and makes no interpreter call. Approval policy, including `strict_approvals`, stays independent. Code replay reads `replay.base_scenarios` (`"linked"` or `"all"`) from `pdd.json` on each run's base commit; see [add all approved base scenarios](replay-evidence.md#add-all-approved-base-scenarios).

## Inspect authored files

`pdd files [--json]` lists prompts, Runtime interfaces, Stories, tests and refusal
reasons. It reads working files only. It does not sign in, call the interpreter,
fill hashes or approve prompts. It works from any folder in a Git repository.

The reader expands `$contract` references and preserves numeric JSON tokens for
lint, test and approval. Approval shows resolved fields and constraints. It keeps
the references in the authored file when it records a person's approval.

The JSON result has `schema_version: "pdd.files.v1"` and arrays `prompts`,
`stories`, `tests`, `orphans`, `refusals` and `warnings`. Paths are relative to the
repository root. Prompt rows include `has_interface`, resolved `references`,
paired `stories` and `tests`, and `refusals`. `has_interface` is null when a
source/reference failure prevents reading the interface. Story rows list their tests. Test
rows list every conflict member in `files`, their name-matched `stories`, reached
`prompts` and preflight `refusals`. Each refusal gives `path`, `code`, `section`
and `message`, plus a fix `hint` when available. No interface kind is inferred.

The list uses the same workspace limits, fixture exclusions and Story/test name
rule as an all-Story check. Missing tests and orphan JSON files are visible.
Inspection returns exit 0 when it can produce the list, including when files
have refusals. Exit 0 is not a lint or test pass. Root/configuration failures
return an error. `pdd test --files` remains the exact upload-file preview for a
selected check.

## Find the prompt that owns a file

`pdd owner PATH... [--json]` shows which prompt owns each file. It reads local
working files only. It does not sign in, call the interpreter or change a file.
PATH is relative to the current folder and must be inside the repository. The
file does not need to exist: a prompt is written before its code.

pdd reads three records, in this order:

| Source | Record | Certain |
|---|---|---|
| `binding` | An entry of the root `pdd-bindings.json` with `module` PATH and a `prompt` | yes |
| `header` | A `Generated from PROMPT` line in the first 4 KiB of the file ([header form](replay-evidence.md#approved-scenarios-on-the-base)) | yes |
| `prose` | The first sentence of a prompt's opening paragraph names PATH, for example ``Own `src/x.mjs`.`` | no |

The prose record is used only when no binding or header names a prompt. A prose
answer is not certain. Treat a file with `certain: false` as owned. The answer is
also not certain when a binding or header names a prompt that does not exist,
when `pdd-bindings.json` cannot be read and no owner is found, or when the file
cannot be read and no binding names a prompt. A short note tells you what to add.

```text
src/runner.mjs: prompts/cli/runner.prompt.md (header)
src/queue.mjs: prompts/cli/queue.prompt.md (prose, not certain: treat as owned)
  named only in the opening sentence of prompts/cli/queue.prompt.md; add a Generated from header or a pdd-bindings.json entry
src/rules.mjs: prompts/cli/rules.prompt.md (header)
  prompts/cli/rules.prompt.md header hash is stale (OLD); current is NEW
docs/guide.md: no owner
```

With `--json`, pdd prints `{"schema_version":"pdd.owner.v1","files":[...]}`. Each
row has `path`, `owner` (the first owner or null), `owners` (every owner: binding
first, then headers in line order; or the sorted prose owners), `source`
(`binding`, `header`, `prose` or null), `certain`, `note` (empty when there is
nothing to add) and `headers`.

`headers` has one row for each `Generated from` header of the file: `prompt`,
`sha256` (the header's hash or null), `expected` (the prompt's header hash, or
null when the prompt is not available), `state` and `legacy`. The header hash
is the SHA-256 of the prompt's behavior text: the prompt with the `status` and
`prose_sha256` fields taken out of its Runtime interface JSON, and that JSON
written without white space. It covers the prose and every interface
declaration. `pdd approve` and `pdd test --fill-hash` do not change it, so an
approval keeps the headers of the prompt current.

| `state` | Meaning |
|---|---|
| `current` | The hash is the prompt's header hash. |
| `current` with `legacy: true` | The hash is the SHA-256 of the whole prompt file. pdd accepts this form for compatibility and marks it `legacy: true`. Write the expected hash for a canonical header. |
| `stale` | The prompt changed after the header was written. Check that the file follows the prompt, then write the expected hash. |
| `none` | The header has no hash. |
| `unknown` | The named prompt is not available. |

The text form adds one line for each header that is not plain current, with
the expected hash. pdd never rewrites a header: a hash in a header says that
the file follows that prompt version. The command returns 0 when it can answer, also for an uncertain
or missing owner. It returns 2 outside a Git repository or for a PATH outside it.
Code replay and the `pdd test` check plan use the binding and header records
only.

## Autopilot on this machine

`pdd autopilot doctor` checks the pdd selected by PATH, Node 22.20 or newer,
Git, gh sign-in, write access, merge methods and effective branch rules, the Git
name and email, agent sign-in and read-only usage, setup instructions and skills,
mode and trust, the `pdd.json` on GitHub, draft prompts, authenticated interpreter
capacity access, and the platform's user scheduler. Linux lingering and macOS
sleep are advisory. Doctor needs no Herdr: Autopilot jobs run headless.
Codex usage uses a read-only account request. Claude usage remains unproved;
run `claude` and `/usage` to inspect it. No agent prompt is sent.
Unreadable branch rules are advisory; repository reviews and checks still apply.
A PASS line shows the check and its result only. A WARN or FAIL line also shows a
repair or inspection command after `fix:`. PATH repairs name this installation,
including source checkouts. A required failure refuses start with the same
report before state files, locks, timers or claims change.
Draft and unreadable prompt paths are warnings. Doctor never approves them.
A successful interpreter access read sends no source and proves no prompt behavior.
See [the first-start path](../README.md#autopilot-on-your-own-repository).

Autopilot jobs make commits, so Git needs `user.name` and `user.email`. Doctor
reads both in the repository. `GIT_AUTHOR_NAME` with `GIT_COMMITTER_NAME`, and
`GIT_AUTHOR_EMAIL` with `GIT_COMMITTER_EMAIL` (or `EMAIL`), also count. A missing
value is a warning. Its fix sets the value with `git config --global`.

Autopilot jobs and other machines read `pdd.json` of the default branch on
GitHub, not the copy in this checkout. Doctor reads that file and compares the
mode and the trust names; case and order do not count. When GitHub has no
`pdd.json`, the warning gives the commit and push that adds it, or
`pdd autopilot MODE`. When the settings differ, the warning shows both and gives
the `pdd autopilot` commands that publish the settings of this checkout. Doctor
itself writes nothing to GitHub.

Doctor uses the saved agent profile on restart.
A selected agent's HOME, CODEX_HOME, CLAUDE_CONFIG_DIR and other environment
settings apply to its checks. A repair command sets only the environment names
whose values differ from your shell, so most repair commands are plain. A
secret value is never printed.
A malformed agents.json report names the file to edit. An invalid
PDD_RUNTIME_URL report gives the HTTPS-origin or unset repair.
Interpreter health and agent usage limits are warnings with fix commands. They
never refuse start at preflight.
Interpreter readiness uses the runtime client's health check, including a JSON
404 from an interpreter without the optional capacity endpoint.

Run Autopilot commands inside the repo folder. Each repo has its own Autopilot on
each machine. Autopilot has one engine, the [core engine](#core-engine). Its tick
makes no AI call. Each issue gets one headless Codex or Claude job with a log file.
Autopilot opens no chat and needs no Herdr.

| Command | What it does |
|---|---|
| `pdd autopilot doctor` | Read-only prerequisite checks, one line per item. A WARN or FAIL line also gives a fix command. No GitHub writes or AI calls. Exit 1 for a required failure, 0 when only warnings remain |
| `pdd autopilot start [--runs N] [--checks N] [--label NAME] [--mode auto\|observe\|off] [--report file\|draft\|off] [--decisions ask\|decide] [--intake off\|shadow] [--share PERCENT]` | Run doctor, check the sign-ins, start the user timer and run the first tick now. The timer runs a tick every 10 minutes. `--label NAME` sets the opt-in label, for example `pdd:autopilot`: Autopilot takes only the issues with this label. `--mode`, `--report`, `--decisions` and `--intake` set this machine's mode, report mode, [decision mode](#core-engine) and [intake mode](#intake-cards-shadow) for this repo. These machine values win over `pdd.json`, and a later start without them keeps them. The report mode is `draft` unless you choose `--report file`. `--share PERCENT` (1 to 100, default 50) saves the part of this machine's CPU and memory that Autopilot may use; a later start without it keeps it (see [the machine guard](#core-engine)). `--runs N` and `--checks N` save this machine's run and heavy-check limits; a start without them removes them |
| `pdd autopilot stop` | Save this repo as disabled on this machine, stop its timer and its intake card jobs, and let the current step finish |
| `pdd autopilot audit RUN PR` | Audit a confirmed automatic merge once with a fresh configured agent. Save OK, CONCERN or BAD and the separate revert recommendation with the run. Post the evidence once on the issue. BAD opens a revert PR only when recommended; otherwise it keeps the merge and reopens the issue with the missing parts. One decision alert states the recommendation and choices. Unknown external outcomes require inspection before any retry. |
| `pdd autopilot check-base RUN PR` | Check the saved automatic base, PR target, current default branch and newest release before a merge or after it. This command reads only. |
| `pdd autopilot status [--all] [--json]` | Show this machine's Autopilot for this repo: enabled or disabled, the timer, the next tick, the jobs, an [alert](#alerts) that was not delivered and the last tick. `--all` lists every repository with Autopilot on this machine, from any folder. `--json` prints the [local cost report](#local-issue-costs) |
| `pdd autopilot add N...` | Create the `pdd:autopilot` label when it is missing and add it to each named issue of this repository. Use it to choose the issues that Autopilot may take |
| `pdd autopilot release ISSUE` | Release this machine's claim and remove `pdd:working` and `pdd:stuck`; keep the run folder, branch and PRs |
| `pdd autopilot regressions [--json] [--file PATH]` | Read core merge history and GitHub CI, parent checks, revert, reopen and issue-link evidence. Classify each merge as ok, suspect or proven; count distinct proven PRs per UTC evidence day. Issue-body attribution uses issue creation time even if added in a later edit; these buckets require a consumer confirmation policy before use as daily scorecard counts. At most 100 GitHub requests per scan; rate exhaustion or Retry-After stops further reads, preserving collected evidence and marking missing evidence incomplete. --json prints structured results; --file exclusively creates a local report without overwriting existing files. No GitHub writes or reverts. Incomplete reads exit 1; complete scans exit 0 even when they detect regressions |
| `pdd autopilot report` | List this machine's local Autopilot report drafts. No GitHub call |
| `pdd autopilot report send FINGERPRINT` | File one local report draft to promptdriven/pdd, or count it on the matching open report |
| `pdd autopilot intake [--json]` | Print this machine's [intake cards](#intake-cards-shadow) for this repo, the would-pick list and today's changes. Local files only: no AI call and no GitHub call |
| `pdd autopilot alerts set [--destination autopilot\|infrastructure]` | Read your Discord or Slack incoming webhook URL from stdin and save it for this machine |
| `pdd autopilot alerts set --discord-channel ID [--token-command CMD] [--destination autopilot\|infrastructure]` | Use a Discord bot in one channel: read its token from stdin, or save CMD and run it at each send to get the token |
| `pdd autopilot alerts test [--destination autopilot\|infrastructure]` | Send one test message and confirm that it was posted; for a bot, first check and show the bot name and channel name |
| `pdd autopilot alerts clear [--destination autopilot\|infrastructure]` | Remove the alert destination from this machine |
| `pdd autopilot alert --issue N --kind usage-limit\|resource\|interpreter\|interpreter-access\|access\|decision\|stuck\|test-suite\|long-running\|recovered --input - [--update]` | Record one alert and send it to this machine's destination. See [Alerts](#alerts) |

Outside a Git repository, `start`, `stop`, `status`, `add`, `off`, `observe`,
`auto`, `trust` and `untrust` stop with exit code 1 and say: `This folder is not a
Git repository. cd into the repo you want Autopilot to work on, then run the
command again.` `status --all` works from any folder.

Autopilot works only on the issues that you mark with an opt-in label. Set the
label with `--label NAME`, or with `autopilot.label` in `pdd.json`. A start with no
label starts nothing and says: `Autopilot did not start: it works only on the
issues that you mark with an opt-in label. Run pdd autopilot start --label
pdd:autopilot, then mark issues with pdd autopilot add N (or add the label on
GitHub). Nothing was started or claimed.` `add` always uses `pdd:autopilot`; for
another label, add it on GitHub. When a tick has no label, it claims no issue (`intake held: no opt-in
label; …`), and status says `No opt-in label: Autopilot takes no issue.`

A start also stops when the repository mode is `off`, or when
`autopilot.quietMinutes` is below 20 (2 times the 10-minute timer). `--mode off`
saves mode `off` for this machine and stops the timer. To turn it on again, run
`pdd autopilot start --mode auto` or `--mode observe`. A successful start prints
one line, for example `Autopilot started for OWNER/NAME in /path/to/checkout. Base
main. Mode auto · issues with pdd:autopilot · agent ID · pdd VERSION · next tick:
TIME. See: pdd autopilot status.`

The first start of a repo on this machine selects the agent. It tries the agent of
the session that runs the command first: Claude Code when you run it from Claude
Code, Codex when you run it from Codex. Then it tries Codex, Claude Code, agy and
Gemini, in that order, and takes the first one that is signed in. This check makes
no model call. Later starts on this machine keep that agent, also after
`pdd autopilot stop`. The core needs a Codex or Claude agent. With another agent,
the tick claims no issue. To select Codex, sign in to Codex and run the first
`pdd autopilot start` from Codex or from a plain terminal. From a Claude Code
session, run `env -u CLAUDECODE pdd autopilot start`.

Linux uses a systemd user timer; macOS uses a LaunchAgent. No process runs between
ticks. On Linux, start warns when user-session lingering is off or unavailable:
`loginctl enable-linger` keeps the timer after logout. A tick never changes its own
timer; only start and stop change it. When the installed timer has another
interval, status says `(run pdd autopilot start to use 10 minutes)`.

Each tick runs the [core tick](#core-engine). It reads the settings from this
checkout's `pdd.json`, and this machine's label, mode and report mode win over
them. Empty ticks make no AI call. The issue list uses ETags. When the open issue
list has more than one page, the tick reads it in full every 6 hours. Between, it
reads only the issues that changed since then (`since=`).

Autopilot uses `autopilot.base` in `pdd.json` when it is set; else it uses the
repository default branch. Start and status show the selection. Each start reads
the default branch from GitHub again. Repository documents do not select the
base. A manual workflow still accepts `--base`.

`pdd autopilot status` reads local files and the timer, with no Herdr or AI call.
It shows `Autopilot enabled; timer active, every 10 minutes; next tick: TIME`. Then
come the core lines: mode, repository, folder, base and agent; the busy slots, the
no-progress limit, repairs, the report mode and the opt-in label, each with its
source (`this machine` or `pdd.json`); the pause; one line for each job; the last
results and the count of local report drafts. Then come the move line, when there
is one, and the last tick. After start and status, one warning follows when
`pdd.json` on GitHub has other Autopilot settings than this checkout (see
[Repository Autopilot settings](#repository-autopilot-settings)). This warning is
the only GitHub read of status.

`pdd autopilot status --all` prints one line for each saved state on this machine:
repository, folder, base, mode, enabled or disabled, and the timer. The mode is the
machine mode with `(this machine)`, else the mode of that folder's `pdd.json`. A
folder that is gone shows `mode unknown (folder missing)`. A folder that is not a
Git repository shows `mode unknown (not a Git repository)`. A timer that cannot be
read shows `timer unknown`, and a broken state file shows `FILE: saved state
unreadable`. One bad line changes no other line. Without saved state it prints
`No Autopilot on this machine.` The local cost lines come last. It makes no GitHub
call.

A machine state that ran the full engine moves to the core engine at its next
tick. A start runs a tick, so a start moves it too. No new work starts before the
move is complete. While old work is busy (a live run with a merged PR, or a working
old Autopilot chat), the move waits, for at most 6 ticks. Then it closes the old
Autopilot chat pane when the pane is Autopilot's own. It cancels this machine's
live old runs and closes their worker chats. It releases this machine's claims: it
deletes their claim comments, and it removes `pdd:working` only when the claim is
this machine's. All other labels stay, also `pdd:stuck` and `pdd:needs-decision`.
Each open PR of an old run gets one note: `Autopilot moved this machine to the core
engine; this PR is not worked on. A person can merge or close it.` PRs and branches
stay. Last, the move releases the check slots and stops the old completion workers
of this repository (TERM, then KILL). It prints one line with the counts. A failed
step goes on at the next tick. The move does not change the timer: the next
`pdd autopilot start` sets the 10-minute interval, and status says so until then.
Before the move, status says `This machine moves from the full engine to the core
engine at its next tick`, and `status --all` adds the same words. For 7 days after
the move, status shows `Moved from the full engine at TIME:` and the line.
`pdd autopilot start --engine full` stops with exit code 2 and says `The full
Autopilot engine is removed; Autopilot runs only the core engine. Run pdd autopilot
start without --engine.` `--engine core` changes nothing.

## Machine and account health

Before the tick claims an issue for a Codex agent, it reads the usage of the saved
Codex profile. The read starts a short app-server connection and uses only
`initialize`, `initialized` and `account/rateLimits/read`. It makes no model call.
It does not spend, request credits, consume a usage reset, change sign-in or log
out an account. A reached limit holds intake: the tick claims no issue and says
`intake held: the agent is not ready (sign-in or usage limit); no issue was
claimed`. Jobs that run go on. Unknown usage does not hold intake. Other agent
kinds have no usage read.

Malformed protocol frames stop the connection and report unknown usage. The read
waits at most one second for cleanup after it selects its result. It sends SIGTERM
first and SIGKILL after 500 milliseconds. A descendant that holds an inherited pipe
cannot block the read.

When jobs end with no result again and again, the core pauses new jobs on this
machine and sends one alert; see [Core engine](#core-engine).

## GitHub API budget

Autopilot uses your own `gh` sign-in, so its GitHub calls use your hourly limit
(5,000 REST calls for a person). pdd counts each `gh` call of the Autopilot tick,
and of `pdd` commands in a repository where Autopilot runs on this machine, with
its purpose and the limit that GitHub reports in the reply headers:

| Purpose | Calls |
|---|---|
| `dependencies` | Issue dependency, timeline and sub-issue reads |
| `claims` | Claim checks and the `lastSeen` heartbeat |
| `issues` | The tick's issue list, comments and permission lookups |
| `pulls` | PR, review and check reads |
| `writes` | Other writes, such as a PR or a reply |
| `setup` | Sign-in, repository and settings calls |
| `other` | Everything else, such as `pdd metrics` |

pdd does not count the `gh` calls that the agent jobs make themselves. It also does
not count other machines or your own work on the same login. All of them use the
same limit. The counts stay on this machine, one file for each repository in
`~/.local/state/pdd/autopilot/github/`. Each tick keeps the last 2 hours.

A conditional read sends the ETag of the last reply. A `304` reply means that
nothing changed, and GitHub does not count it against the limit. The tick,
`pdd dependencies prepare` and `complete` use conditional reads for an Autopilot
repository. They share one file of ETags and reply bodies in the same folder. A
full page (100 items) that has no next page is read without its ETag: a `304`
reply does not show that a next page came.

pdd keeps one saved dependency snapshot for each repository in the same folder
(`*.snapshot.json`, private to you). `pdd dependencies complete` uses it. A read
asks GitHub only for the issues that changed since the last read (`since`, in
update order). It reads the comments, links and history of an issue again when its
update time, comment count or link identities changed. It checks the open index
with conditional requests and compares native link identities in batches. Equal
link counts can still mean different blockers. Incomplete batch connections fall
back to complete REST link pages. Once a day it rebuilds the open list, so a
deleted or moved issue leaves it. Safety reads always ask GitHub (a `304` is
fine): claim checks, heartbeats, trust, and the readback after each write.

The budget acts on the tick, and its floor on the dependency commands too. It
has two settings in `pdd.json`, a share (default 30%) and a floor (default 1,000
calls):

```json
{"autopilot":{"mode":"auto","trust":[],"github":{"share":30,"floor":1000}}}
```

`share` is a whole percent from 1 to 100; `floor` is a whole number of calls. A
missing or invalid value uses the default.

- **Low.** The counted REST calls of all Autopilot repositories on this machine
  in the last hour reach the share. A 304 reply does not count. When several
  machines hold live claims on one repository, each machine gets the share
  divided by their number. Then no new job starts, and the tick says
  `intake held: the GitHub budget is low (…)`. Jobs go on.
- **Reserve.** GitHub reports fewer calls left than the floor, for REST or
  GraphQL. Then the tick reads no issue list until the reset. It refreshes only
  the heartbeat of each live claim of this machine, so a claim does not expire
  while its job works. Native dependency observations for an Autopilot
  repository also stop non-safety reads. This includes `pdd dependencies
  prepare`, `complete` and direct snapshot reads. A reply that shows fewer calls
  than the floor stops the reads after it. A stopped `complete` keeps its request
  and analysis. Reviews that were already saved are never saved twice.

The agent jobs' own `gh` calls are not counted and do not wait for the floor.
Safety reads (claim checks, trust, permissions and write readbacks) and writes can
use the reserve. Other `pdd` operations are counted but do not wait for this
floor. The budget does not keep 70% of the limit for you. To give Autopilot a
limit of its own, see the design note
[A GitHub App token for Autopilot](autopilot-github-app-token.md).

The dependency snapshot is saved beside the repository's GitHub call ledger as
`github/H.snapshot.json` in the Autopilot state folder. Its temporary lock is
`github/H.snapshot.json.lock`, with the same repository hash `H` as the ledger.
If a writer exits while holding this lock, later saves refuse to replace the
snapshot. To recover, stop local PDD operations for that repository and confirm
that no snapshot writer is still running. Then remove only that empty lock
directory. Keep the snapshot and ledger files. The next observation can save again.

### Alerts

Autopilot can tell you about an incident or a decision that needs you. Set your
own destination once on each machine:

```sh
pdd autopilot alerts set    # paste the URL, press Enter, then Ctrl-D
pdd autopilot alerts test
```

The URL comes only from stdin, never from an argument, so it stays out of your
shell history. You can also pipe it from a password manager. pdd saves it in
`~/.config/pdd/autopilot-alerts.json` (`$XDG_CONFIG_HOME/pdd` when it is set),
outside every repository, with mode 0600. When `HOME` is empty or not an
absolute path, pdd uses your account's home folder; without one it saves
nothing. pdd never prints it, also not in errors. A Discord webhook gets `?wait=true`, so the reply is the posted message.
A Slack incoming webhook must reply `ok`. Only these replies count as delivered.

A team with a Discord bot can use it instead of a webhook. Give the channel ID and
the bot token. The token comes from stdin and is saved like the URL, or from your
own command, which pdd saves and runs at each send, so the token is never written
to disk:

```sh
pdd autopilot alerts set --discord-channel 123456789012345678 \
  --token-command 'gcloud secrets versions access latest --secret=NAME --project=PROJECT'
pdd autopilot alerts test
```

The bot posts with the Discord API v10, with link previews off, and reads the
message back. Only a matching readback counts as delivered. A change of line
ends or of spaces at a line end is not a mismatch. `test` first checks
the bot and the channel, read-only, and shows the bot name and the channel name.
pdd never prints the token or the command output. The bot needs permission to
view the channel, send messages and read message history.

The core sends an alert only for a real need. It sends `stuck` when a job process
reaches its backstop, when a PR waits too long for the merge lane, or when an END
cannot finish. It sends one informational `long-running` note when a job process
runs for 3 hours; work goes on. It sends `usage-limit` when it pauses new jobs
after jobs end with no result. Each alert gives the cause, what Autopilot tried and
what it needs. To record one alert yourself, give that JSON on stdin:

```sh
pdd autopilot alert --issue 12 --kind usage-limit --input - <<'PDD_ALERT'
{"cause":"Codex usage limit; resets 2026-11-06T18:00Z","tried":"Paused issue 12 and continued other work","need":"More quota or another signed-in account"}
PDD_ALERT
```

Each message names the repository, the issue link, the cause, what Autopilot tried
and what it needs. Answer on the GitHub issue, so the answer stays with the issue.
A usage limit, a resource failure, an interpreter outage or an interpreter access problem
(`interpreter-access`: this machine cannot read the interpreter health check) is one incident for the
repository and machine, so a limit that blocks 5 issues sends one alert. A call for another
blocked issue adds that issue to the incident and sends nothing. The machine is
the name that Autopilot saved at its first start (this checkout's start first),
else the host name, so a host rename does not open a new incident. An access or spending decision, a product
decision, a stuck issue or a long-running issue is one incident per issue. A repeat call sends
nothing for a delivered or unconfirmed alert, and sends again an alert that
failed or had no destination. `--update` sends a new cause, a changed decision needed or the new
issue list. Changing only what was tried sends nothing. `--kind recovered` sends one recovery and closes the matching
alerts; give `"kind"` in the JSON to close only that incident. Every call and
its delivery result are recorded in
`~/.local/state/pdd/autopilot/alerts/`. Without a destination, the alert stays in
that record. Work continues in both cases. Each repository's alert record has a
shared lock, so parallel calls cannot overwrite incidents.

To send infrastructure incidents to another channel, set a second destination:

```sh
pdd autopilot alerts set --destination infrastructure
pdd autopilot alerts test --destination infrastructure
pdd autopilot alerts clear --destination infrastructure
```

The bot options also accept `--destination infrastructure`. Its secret is saved
in `autopilot-infrastructure-alerts.json` beside the ordinary destination with
the same private permissions. Set, test and clear affect only the selected
destination. The default is `--destination autopilot`. Machine incidents
(`usage-limit`, `resource`, `interpreter`, `interpreter-access`) and their
recoveries use the infrastructure destination when it is set. Without it they
use the ordinary destination. Issue decisions and stuck alerts use the
Autopilot destination. A test clears only that route's older delivery failure. An open undelivered incident still
needs attention. Configure external credential-maintenance and machine-health
senders at their own source; PDD does not change those programs.

## Runs on a GitHub issue

| Command | What it does |
|---|---|
| `pdd workflow prove ISSUE --test COMMAND --expect TEXT [--timeout MIN]` | Fetch the selected base branch and run the supplied command on its merge-base with committed changed test files overlaid, then on committed head, in disposable snapshots. Both quoted text options are required; each phase has a limit of 10 minutes by default (`--timeout MIN` sets 1 to 120 minutes), 2-second termination grace and 1 MiB output cap. Save `old-code-proof.json` in the run folder. A successful comparison exits 0; failed or unavailable evidence exits 1 and never blocks publication. |
| `pdd workflow run NAME ISSUE [--agent codex\|claude\|gemini\|agy\|ENTRY] [--base BRANCH] [--draft] [--model MODEL] [--herdr-agent-name NAME] [--codex-threads N]` | Make a branch and a worktree for the issue, open the first chat in Herdr and return at once. `--agent ENTRY` uses an entry name from `~/.config/pdd/agents.json` (quote spaces); see [Many accounts](USAGE.md#many-accounts). `--through prompt-pr\|code` saves where a normal run goes after PR 1: stop there (the default) or go on to the code PR. `--origin`, `--decision-id` and `--outcome` supply optional metrics metadata. `--base BRANCH` selects an existing branch on origin; omitted means the repository default. An explicit base must fetch successfully before startup. PRs target the saved base, with PR 2 stacked on an open PR 1. Startup saves this terminal's `CODEX_HOME` (Codex), `CLAUDE_CONFIG_DIR` (Claude Code) or `GEMINI_CLI_HOME` (Gemini) for later chats. A leading `~` in it means your home folder. If that folder does not exist, `workflow run` stops before it starts anything |
| `pdd workflow list [--json]` | List the workflows that pdd finds, with their areas and gates: the PDD ones and [your own](workflows.md#make-your-own-workflow) |
| `pdd workflow status [ISSUE] [--all] [--cancelled] [--json]` | Show the area, the step, what the run waits for, and the PRs with their CI state. For a run with many Stories, also `Stories: N of M Stories pass`, counted only from pdd's own `pdd test` results that `pdd workflow done` recorded (and `pdd workflow evidence` receipts); with none, `Stories: no pdd result (pdd:no-verdict)`. Without ISSUE, show all runs in this repo. In a run's worktree, show that run. With `--all`, or outside a Git repo, show every run on this machine: waiting for you first, then working, PR open, done. `--cancelled` also shows the hidden cancelled runs. `--json` gives the same list as data. It says "the chat stopped" only with evidence: Herdr sees no agent in the chat's tab, and the agent was seen running there or its own native session exists. Run `pdd workflow open ISSUE` to start it again. When the agent runs but every turn fails on its login or its usage limit, it says "the chat cannot work: the agent's login failed" or "the chat cannot work: usage limit until TIME", says how to start a new chat (`pdd workflow open ISSUE --new`), and lists the run as waiting for you. To find this, pdd reads only the chat screen and the end of the agent's own session file. It never types into the chat. While a launch is not confirmed, it says "the chat is starting, not confirmed". Failed or unconfirmed startup/open and unavailable Herdr status show waiting with recovery advice. At a gate it says that the agent writes the gate message until the chat has asked you |
| `pdd workflow evidence ISSUE --summary FILE` | Record saved check JSON after verifying its selected source hash. Keeps completed steps, gates, approvals, chats and open PRs unchanged; no tests or external calls |
| `pdd workflow evidence-associate ISSUE --workspace PATH --stage current\|pr1\|before [--commit SHA] --test PATH...` | Register the producer workspace, evidence stage and selected tests for this run. Run it from the owned run worktree. Give one or more test paths after `--test`. `--stage before --commit SHA` registers the source of an earlier saved check, for example the failing check before a bug fix: the selection at that local commit must hash to the saved check's source. Registration runs no checks and changes no workflow progress. See the [association contract](../prompts/cli/workflow-runner.prompt.md#workspace-evidence-association) |
| `pdd workflow view ISSUE` | Read-only review of the saved state, current gate, recorded approvals, pending decisions, PRs, check reports, Simulator links and current gate files. Never starts or resumes a chat, approves, or refreshes external state |
| `pdd workflow open ISSUE [AREA] [--new] [--model MODEL] [--herdr-agent-name NAME] [--codex-threads N]` | Focus or resume the current chat, or the saved chat of a recorded earlier AREA. A chat that is still starting gets up to 30 seconds to show its agent; pdd sends no second launch or resume meanwhile, and then says "starting, not confirmed". `--new` closes and archives the current area's owned chat and starts one fresh session with the same run and agent setup, keeping progress and approvals. For a two-PR run in code, selecting `prompt-pr` or `story` returns work to the open PR 1 branch and clears old code checks. `--new` can replace that returned chat. Other earlier-area replacement and requests to replace a chat from an agent session or the pane being closed refuse. Repeat `--new` to resolve a pending replacement; status names its phase and resolving command, and cancel remains available |
| `pdd workflow card [ISSUE]` | Print the run's Story card from its real files: the issue and what the reporter asked, the verdict line, each Story's acceptance criteria, what must not change and rules to check, the test cases (case, input, expected), the prompts that change with their changed lines, the full paths and the next step. After the Story approval it also shows what changed since then. Read-only: no GitHub, Herdr or interpreter call |
| `pdd workflow approve [ISSUE] [--said WORDS] [--draft] [--model MODEL] [--herdr-agent-name NAME] [--codex-threads N]` | Approve the ready gate and its draft prompts together with your chat words. In a normal run, `--through prompt-pr\|code` records the code-or-stop choice from the Story card. Without ISSUE, select the current worktree or sole waiting run. Without --said use person terminal y/N; agent callers must ask then use --said. Strict mode requires a person terminal. |
| `pdd workflow resend ISSUE... [--said WORDS]` | Record one person decision and resend each lost check once. `--said -` reads exact words from stdin. Strict mode requires a person terminal. |
| `pdd workflow changes ISSUE TEXT` | Send the text to the same chat. The chat revises. The gate stays open. Also use it to answer a question that the chat asked. At a gate, a plain approval such as "I approve" is not sent: pdd tells you to run `pdd workflow approve ISSUE` |
| `pdd workflow tidy [--dry-run]` | Close safely finished chat tabs across runs on this machine. `--dry-run` lists the eligible count without changes. Keep the current chat of each live run, busy chats and chats whose pane identity cannot be verified. A finished chat without a native session requires a saved screen. Show retained counts by reason. |
| `pdd workflow cancel ISSUE` | Close the run's chat tabs. Keep the worktree and the branch. A new `pdd workflow run` on the issue then starts fresh |

Finished chats close after a 15-minute grace period when they are idle and have
a saved native session or a saved screen. Each new start tries cleanup.
`pdd workflow tidy` also retries cleanup. It refreshes restart terminal IDs for matching area tabs and the saved run shell, with confirmed agent absence and idle foreground shells. Done runs release their workspace after verified chat cleanup. Workspace closure requires a saved creation record for that exact workspace. If the creation field is missing, pdd can save it only when the workspace has the run worktree path, clone identity and run label. Other workspaces remain open with a cleanup reason. Saved native sessions, run folders and Git worktrees remain available. Missing or foreign workspaces stay protected. List status suggests tidy only when its read-only eligibility check finds a chat it can close. Status shows pane counts for working, parked, done and unowned panes. It warns at 90 percent of the configured pane budget and lists unowned workspaces with commands for manual closure. These observations do not authorize automatic closure. Status and view close nothing. A manual
start on a completed issue keeps its history and starts a fresh run. A replaced
run remains discoverable from its retained worktree; its agent sees the old and
replacement run IDs and must stop. Run `pdd workflow cancel ISSUE` from that old
worktree to close a retained busy chat.

`PDD_HERDR_PANE_BUDGET` sets the session `pdd` pane budget (default `56`; `0`
disables it). The count includes personal panes. Before making a new run, pdd
checks capacity and can close safely finished chats without the grace period.
If there is no room, `herdr_pane_budget` reports the count, required capacity and retained counts by reason;
no new branch or worktree is made. Raise the budget or close unused tabs.

For an ended run, `pdd workflow open ISSUE [AREA]` prints saved screen paths and
native resume commands with its saved account folder. It changes nothing in
Herdr. For a live run it can resume a closed historical chat immediately.
Screens are private files in the run folder's `chats` directory.

`pdd workflow open ISSUE` focuses or resumes the current area chat of a live run. If its Herdr workspace was closed, status says so and gives this command. Both ordinary open and `--new` rebuild that workspace and area tab from the verified saved worktree. A live saved layout workspace ID that belongs to another checkout or repository stops recovery, even when a matching workspace exists. A saved ID absent from live inventory permits recovery. They resume the saved native session when available, or start a fresh chat with the area start message when no saved session can be resumed. A later `--new` on the open workspace starts a fresh session as usual. After a Herdr restart, matching tabs and panes keep their identity and pdd saves their new terminal IDs. If the root layout changed, pdd rebuilds the verified workspace when no live or unconfirmed chat can be lost. A live chat or unavailable inspection keeps the workspace intact. PDD saves the returned shell IDs with new workspace creation evidence before another allocation. A saved close intent stays bound to its original shell IDs on every retry. A missing worktree folder must be restored first. No new Git worktree is made.

A run saves one launch profile: agent kind, account folder, model, Herdr name prefix and Codex thread limit. Use `--model MODEL` at start to keep the same model across areas, resumes and account changes. Omission uses the account's model default. To change the model for the next fresh chat and later areas, use `pdd workflow open ISSUE --new --model MODEL`. Model, name and thread options on open require `--new` for the current area. The agent kind and agents.json command stay the same.

`--herdr-agent-name NAME` sets a name prefix of 1 to 25 lowercase letters, digits, underscores or dashes, starting with a letter. PDD appends an area suffix. Omission gives a stable name derived from the run identity. PDD binds Codex and Claude names only after it verifies the detected native session. A resumed Codex chat, including one in a rebuilt workspace, uses its saved UUID and original session time in the saved account for this check. A saved default account uses `~/.codex` for native evidence, even when the observing terminal has another `CODEX_HOME`. A naming failure shows a warning and keeps the chat's live state. Gemini and agy lack this native ownership proof, so their names stay unbound with a warning. Detailed status shows the saved name and pane. JSON status includes `launchProfile` and `chat: {herdrAgentName, paneId}`. Use `herdr --session pdd agent get NAME` to inspect it. Use `herdr --session pdd agent send-keys NAME ctrl-c` to interrupt its work through the terminal, then send the agent's normal exit command when it is ready. `pdd workflow cancel ISSUE` ends the run and closes its tabs.

`--codex-threads N` selects a whole number from 4 through 8 for Codex chats. For example, 5 allows the main thread and four helpers. PDD passes the effective limit only to this chat. A higher positive limit in the selected account's `config.toml` is kept and shown in status. Missing files keep the requested limit; malformed configuration refuses before closing a chat. New Codex runs default to 5, while runs without a saved thread setting keep the account default. Other agents reject this option. This setting cannot prove that a required check can start. If a fresh checker cannot start, report `Not checked: STEP (agent limit)`; keep the builder separate from checkers and always use a fresh reviewer.

To fix a prompt after code review, commit or keep the current code edits so the worktree is clean. Run `pdd workflow open ISSUE prompt-pr` (or `story`). PR 1 must still be open. PDD fast-forwards its owned branch from the remote and merges the fetched current commit of the run's saved base (usually main) into PR 1. Resolve and commit any base merge conflicts on PR 1. Repeating the explicit `open ISSUE prompt-pr` command in returned prompt space integrates a newer base and clears the prompt checks when the head changes. Make the correction on PR 1 and finish the prompt checks with `workflow done`. PDD updates the same PR 1. A changed Story or scenario contract returns to the Story gate for a new decision. PDD compares PR 1 with the contract covered by the last Story decision, including changes fetched during return. Missing approval coverage also returns to that gate. Story coverage includes supported `user_stories` directories at any depth. Additions, edits and deletions require fresh coverage. A reply covers only the Story and cases shown at the gate. If they change, run `workflow done` again to show the gate and obtain a later decision. Prompt-only edits rerun the prompt checks. PDD rechecks the contract and published scenario bytes after code confirmation or an explicit reply and against the exact fetched commit before code entry. PDD merges that pinned commit and checks the resulting code source before saving the code decision. A changed contract reopens Story approval. Unpublished scenario bytes keep the run in prompt space. The normal code-choice gate then resumes the existing code branch and merges the updated PR 1 without rewriting published history. Run code generation and all code checks again. PR 2 contains no prompt edits relative to its fetched PR base. PDD checks the staged tree before its automatic commit and checks the exact candidate commit before pushing that SHA. A concurrent unsafe edit refuses publication and keeps the local work, with advice to return to prompt space. After PR 1 merges, PDD compares prompts with the fetched default or selected topic base. Normal runs keep the Story card and its saved code-or-stop choice.

The run status and PR descriptions show the return to prompt space and its reason. The ordinary replay anchor includes only scenarios changed by this run against the current merge-base of its original base branch. Unrelated scenarios merged from that base do not enter the anchor. PR 1 retains its full owned path set across publications. Later edits to already-integrated upstream prompts or scenarios do not block code entry after PR 1 merges. Owned source and anchored scenarios still require their current checks. A concurrent merge of PR 1 into the base does not remove its owned scenarios from the replay anchor during publication. Adopted runs retain their declared corpus and approval authority.



Ordinary open and exact-session resume use the chat's saved configuration folder. To select another existing account folder for one fresh current-area session, run `CODEX_HOME=/existing/work5 pdd workflow open ISSUE --new` for Codex, `CLAUDE_CONFIG_DIR=/existing/claude2 pdd workflow open ISSUE --new` for Claude, or use `GEMINI_CLI_HOME` for Gemini from another terminal outside the agent session. A nonempty account variable, including an inherited value, overrides the run's saved folder. Empty or unset values keep the saved selection. `~` expands to your home; relative paths resolve from this command's working directory. A missing folder or a regular file refuses before closing the owned chat. PDD selects the folder without checking its login or quota.

The fresh replacement keeps the run, worktree, progress, gates and approvals, and archives the original chat's session, configuration and first message. When PDD installs the replacement before launch, it saves the selected folder for later areas too; approving from another terminal does not select another account. A pending replacement stays pinned to its entire launch profile on every `--new` retry, regardless of that retry's account variable or model, name and thread options. Recovery can restore the original chat using its original profile. Plain open, historical AREA open and `changes` keep their recorded account and request target. This route starts a new native session; it does not move credentials or an existing session between profiles.

- NAME is `small-change`, `bug`, `feature`, `product` or the name of [your own workflow](workflows.md#make-your-own-workflow). pdd uses the skill `pdd-NAME`.
- ISSUE is the issue number in the current repo, worktrees included. If several repos match, use `owner/repo#N`. An issue has one active run. A second `pdd workflow run` on the same issue still starts: it marks the old active run replaced and names it (id, worktree, last activity) in one warning.
- `--base` takes a branch name such as `feature/checkout`. The branch must already be on `origin`. PDD fetches it and starts from that remote commit, preserves the repository default, and pushes only its new issue branches. A failed explicit fetch stops startup.
- `status` prints `pdd workflow view ISSUE` for passive review. The view links to the full issue, Stories and acceptance criteria, plan, prompts, test cases and Markdown gate notes. It identifies the current commit and uncommitted edits; recorded approvals cover only the saved gate and listed prompt hashes, never later edits. Missing links/files are stated plainly.
- The run folder is `.git/pdd/runs/N/` in your clone. See [workflows.md](workflows.md#the-run-folder).
- The PR description takes Stories from the run's diff against its current base branch and the run's named or approved Stories. The code PR keeps its Stories from PR 1 after PR 1 merges, even without a Story approval fingerprint. It uses PR 1's saved Story paths. For an older PR 1 record, it reads that PR's changed files from GitHub, so upstream fast-forward or merge updates do not add unrelated Stories. A failed or unavailable read supplies no recovered paths. A documentation-only small-change with no Story of its own has no User story section; Details says that no Story applies.
- In Herdr, the session is `pdd`. Each verified common Git directory has its own repository workspace. Each run has a workspace such as `my-app#42 feature`, with one tab per area.
- With Claude Code, the first chat can ask once to trust the new worktree. `workflow run` prints a hint when your clone's folder is not trusted yet.
- In a terminal, `approve` without --said asks y/N and shows the repo, the issue and its title. From an agent chat, `approve` without --said asks the agent to ask the person, then run with --said and their words.
- Without `--agent`, pdd selects the first ready agent in order: Codex, Claude Code, Gemini CLI, then Antigravity CLI (`agy`). An explicit agent or configured launcher selects that choice. The chats start in full-access mode: Codex with `--dangerously-bypass-approvals-and-sandbox`, Claude Code with `--dangerously-skip-permissions`, Gemini with `--yolo`, Antigravity CLI (`--agent agy`) with `--dangerously-skip-permissions` and the run worktree trusted for that session only. An Antigravity chat also gets pdd's runs folder and worktrees folder with `--add-dir`, so it reads its start file with its own file tools. pdd finds a signed-in Antigravity CLI with `agy models`. Gemini CLI needs a paid Gemini API key, Vertex AI or Code Assist; with a free or Google One account, use `--agent agy`. Without `--model`, the account selects the model. PDD does not change your agent's settings, sign-in or config.
- Each chat uses the sign-in of the person who runs the pdd command that starts or resumes it, not the environment of the terminal that first started the Herdr server. pdd gives the chat your own login variables and removes the ones you do not have with `env -u`. Claude Code: `ANTHROPIC_API_KEY`, `ANTHROPIC_AUTH_TOKEN`, `CLAUDE_CODE_OAUTH_TOKEN`, `ANTHROPIC_BASE_URL`, `CLAUDE_CODE_USE_BEDROCK`, `CLAUDE_CODE_USE_VERTEX`. Codex: `OPENAI_API_KEY`, `CODEX_API_KEY`, `CODEX_ACCESS_TOKEN`, `OPENAI_FEDERATION_RULE_ID`, `OPENAI_IDENTITY_TOKEN_FILE`, `OPENAI_WORKLOAD_IDENTITY_CONTEXT`, `OPENAI_BASE_URL`. Gemini: `GEMINI_API_KEY`, `GOOGLE_API_KEY`, `GOOGLE_GENAI_USE_VERTEXAI`, `GOOGLE_GENAI_USE_GCA`, `GOOGLE_APPLICATION_CREDENTIALS`, `GOOGLE_CLOUD_PROJECT`. The base URLs are in these lists because the address goes with the key. Other variables, such as `AWS_*` for Bedrock, come from the Herdr server as they are.
- pdd writes the login values to a one-time private file (mode 0600) in the run folder, inside your clone's `.git` folder. The chat deletes that file first, then reads the values and starts the agent. If it cannot delete the file, the agent does not start. So the values never show in the Herdr pane or in the shell history. When a file stays because pdd stopped before the chat ran, a start or status of the run deletes it only when it is at least five minutes old. Cancel deletes all login files, including newer ones.
- When your environment has no login variable, the chat gets none and uses the login in its config folder. An example is a Codex profile with `shell_environment_policy.inherit = "core"`. The Gemini start check runs only `gemini --version`, so it does not show whether that login works.
- The first message of each chat gives the full path of this pdd. The agent uses it, so another `pdd` on its PATH does not matter.
- A Codex chat also gets `-c shell_environment_policy.set.PDD_BIN=…` and `-c shell_environment_policy.set.PDD_AGENT_SESSION="1"` for this launch only, so its commands keep both values when the Codex profile sets `inherit = "core"` or `"none"`. pdd does not change Codex settings. Limit: a `shell_environment_policy.include_only` list that leaves out a name still removes it.
- Workflow chats have no overall time limit. `pdd workflow prove` limits each phase to 10 minutes by default; remote lint has a caller wait limit. You can close the workflow-start terminal at any time.
The pdd CLI has no merge command. In manual workflows, ask your agent to merge under [RUNBOOK §2](../RUNBOOK.md#2-the-files). In Autopilot `auto` mode, the [core engine](#core-engine) merges a PR only after its merge check passes; required human approvals still apply.

`pdd workflow run bug 2544 --draft` saves draft PR publication before starting the
chat. The saved Boolean applies to PR 1 and the separately approved code PR, or
the single small-change PR. Omission keeps ready publication. At a ready,
unpublished approval gate, `pdd workflow approve 2544 --draft --said WORDS` can
save that policy after the normal approval checks. Later omitted flags retain
it. Starting again cannot change an active nondraft run's policy. A published
stage cannot adopt it, and existing PRs are never converted. Requested draft
publication requires GitHub to confirm the exact matching PR is a draft; an
unconfirmed result requires inspection of the same PR. Draft PR publication is
separate from approval of draft prompt interfaces.

`pdd workflow run NAME ISSUE --adopt-corpus FILE` adopts an unchanged externally approved declared corpus for a fresh replay-evidence-enabled workflow; see [corpus adoption](replay-evidence.md#adopt-an-unchanged-approved-corpus). Without it, the anchor also holds the [approved scenarios on the base](replay-evidence.md#approved-scenarios-on-the-base) that link to the run's changes. The root `pdd.json` setting `{"replay":{"base_scenarios":"all"}}` on the base commit adds all of them; the default is `"linked"`. See [add all approved base scenarios](replay-evidence.md#add-all-approved-base-scenarios) for the limits and the cost.

## Tests on the PDD interpreter and prompt approval

Before a check, PDD prints one local plan. It lists target Stories, the changed
paths that affect each Story, and their dependency closures. A full batch also
lists unrelated Stories as baseline obligations. The plan shows estimated model
calls and a maximum that includes one restart replacement per test. It does not
authorize more calls. A full check with a missing interface or undefined call
bound stops with a named prerequisite and no paid check.
This is local issue work. Repair the named interface or call bound, then run a
fresh `pdd test`. A saved read or `pdd test --retry BATCH` returns the local
result and repair guidance with exit 4. It keeps the batch history and sends no
paid work. An interpreter wait cannot repair a local prerequisite.

Check JSON and saved batches include `check_plan`. Results also include
`check_scope`, with separate target and baseline states and recovery guidance.
A baseline failure stays in the failed full batch. Hand it to its owner; do not
rerun unchanged target checks to repair it. The classification does not prove
the failure's age or owner. Required repository full-pass gates still apply.
Saved reads use the original plan. Without reliable change scope, PDD marks the
selection as conservative and retains the selected Stories as targets.
Deleted generated implementations keep their owner through the comparison
revision's Generated-from header. If permitted metadata cannot prove a deleted
path's owner, the selected Stories remain conservative targets. Workspace
exclusions also apply to these historical metadata reads.

`pdd lint`, `pdd test` and `pdd test --files` report broken selected tests first,
with the file, reason and fix step. Missing or unreadable dependencies and invalid
test files do not stop other selected tests. The summary counts tests that could
not run. JSON and saved batches retain these rows. The command exits nonzero if
any selected test is broken. Broken tests are not sent for paid checks.
Local numeric-review metadata keeps the same isolation. An unreadable test
retains its refusal while valid reviews still apply to readable siblings.
This also applies when a selected test changes during source capture. Capture
checks its criterion texts and coverage against the captured Story before upload
or cached-pass reuse. Authored partial-test metadata still refuses the test.
A test with no exact criterion is refused and keeps all not-checked reasons.

A Story criterion with no check or no exact check is reported as
`not checked: <reason>`. Other criteria still run. An omitted Story item is also
not checked. The Story is not a full pass while any criterion is not checked,
and it cannot enter the complete-pass cache. PDD uses the engine's exemption
format in the uploaded scenario copy. It leaves authored files unchanged.
Changed criterion text and other malformed test rules still refuse the test.

| Command | What it does |
|---|---|
| `pdd test --target code [STORY...] [--json]` | Run the selected Story scenarios on their declared real CLI commands, with 0 AI calls. Compare arguments, optional stdin, exit code, stdout and stderr using the same cases. Save one result per Story with the commit. Unsupported steps say `not run` with a reason and cannot pass. |
| `pdd test --affected [--cache-clear] [--json] [--details] [--timeout MIN] [--max-calls N]` | Check every Story affected by local changes against the unique saved-run base or HEAD, including all variants and criteria. Uncertain scope keeps complete coverage. Read omitted baseline obligations from local original Check history in a separate historical report. Status describes selected checks only. Required full-pass gates still apply. |
| `pdd test [PATH\|STORY...] [--lf] [--cache-clear] [--json] [--details] [--timeout MIN] [--max-calls N]` | Reuse complete unchanged passes from `.pdd/cache/test/`. `--lf` selects last-known failures, or the normal scope when none are recorded. `--cache-clear` discards the cache while retaining operand scope and takes precedence over `--lf`. Check Stories on the PDD interpreter with your gh login. With no STORY, test every Story. Send your Git files and wait for the checks, with one progress line every 30 s. Then print one table with a report link for each test, one `Prompt tests` line for each Story and, with two or more Stories, the overall line |
| `pdd test --read [BATCH\|CALL_ID] [--json] [--timeout MIN]` | Read saved results; a normal Check held for lint may continue its original checks. Other reads send no work |
| `pdd test --retry BATCH [--json] [--details] [--timeout MIN]` | Retry only confirmed unstarted checks with the saved source and call caps. Keeps completed, running and unknown jobs; changed source requires a fresh selected check |
| `pdd test --fill-hash [PATH\|STORY...]` | Fill draft interface hashes and remove redundant `"kind": "full"` from drafts. With selections, fill only the selected work and required prompt dependencies; leave unrelated prompts unchanged. An explicit `.prompt.md` path works without tests. With no selection, inspect all Git-visible prompts. Approved prompts stay unchanged. No network |
| `pdd test --fill-hash --compact` | With no operands, fill draft hashes and remove interface JSON formatting whitespace. Remove redundant `"kind": "full"` from drafts; preserve other values, strings, number spellings and prose. Approved and statusless files stay unchanged. No network |
| `pdd test --explain-bindings [STORY...] [--json]` | Explain each selected resource edge, fixture candidate, mismatch cause and repair. Local reads only; no sign-in or interpreter call |
| `pdd test --files [STORY...] [--app-map PATH] [--json]` | List the exact selected upload manifest and byte sizes. No network; `--app-map` previews the Simulator's app map |
| `pdd lint [STORY...] [--json] [--timeout MIN] [--max-calls N]` | Print local SVG layout warnings, then the server checks the format of the prompts, Stories and tests only, with 0 AI calls, and requests complete diagnostics and prints the problems the server reports. Requires network access; use it before a real check |
| `pdd lint --local [STORY...] [--json]` | Compare linked `.ui.svg` parts and labels with prompt prose locally; warning advice only, 0 AI calls and no network/authentication. Without Story names, inspect all Git-visible prompts, even with no PDD tests |
| `pdd test --screen URL --drawing PATH [--json]` | Compare the real page with its `.ui.svg` layout spec in installed headless Chrome/Chromium at the SVG viewport. No AI or interpreter call; missing/hidden parts, order or region differences fail |
| `pdd interface draft [PROMPT...] [--all] [--json]` | Draft missing Runtime blocks from explicit prose or contracts and lint locally, without AI or network calls. Uncertain facts include field questions and a recovery command. |
| `pdd interface draft PROMPT [--contract FILE] [--extend \| --refresh] [--json]` | Supply schemas and effect ports, extend an existing block, or reopen a stale block as draft. |
| `pdd approve PROMPT --automatic --tests COMMAND` | Approve a complete draft of unchanged committed behavior after existing native tests and a complete current prompt check. Strict mode requires a person. |
| `pdd approve PROMPT [--said WORDS]` | Approve one prompt with your chat words, or terminal y/N without --said; strict mode requires a person terminal. |
| `pdd simulate [STORY] [--max-calls N] [--tab call\|screen\|terminal\|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent NAME]` | Automatically open a shell for command-line programs, localhost with an example request for HTTP routes, or the Simulator page for screens and typed operations. With no Story, open the whole project. |
| `pdd simulate [STORY] --page [--new]` | Open the Simulator page explicitly |
| `pdd simulate --stop [STORY]` | Stop the open Simulator link of a Story |

For `--target code`, each tested Runtime entry declares
`"implementation": {"kind": "cli", "command": "node bin/tip.mjs"}`. The command
is split into words without a shell; quoted or shell-dependent command strings
are unsupported. Cases supply string `argv` and optional UTF-8 `stdin`.
The runner supports `equals` checks on `/exit_code`, `/stdout` and `/stderr`.
Other checks, HTTP and call entries, and world or port simulations without a
native bridge report `not run` with a reason. Results are saved in
`.pdd/code-test/latest.json` with the commit and worktree dirty state; a failed
or unrun Story makes the command nonzero.

Ordinary `pdd test` reuses complete unchanged Story passes from the Git-ignored `.pdd/cache/test/` folder, showing their previous pass time and zero current AI calls. `pdd test --lf` selects the last known failures; a later attempt without a verdict keeps a failure selected until it passes. With no failures in the selected scope it uses the normal selection, including unchanged-pass reuse. Completed saved reads populate the cache after source verification, dated from the original batch start, never the later read time. `pdd test --cache-clear` discards prior local evidence and runs the normal selected scope; it takes precedence over `--lf`. It sends again and prints one stderr notice with the selected Story count; the interpreter may return a saved answer for the same key.

Reuse includes reached call targets, exact authored bytes, interpreter origin, call budget, pdd version, and the interpreter build and requested model reported by job answers. A missing identity or a pass older than seven days runs again. A different build or model observed during a run also runs the selected Stories initially skipped, with a reason; after a timeout or interrupt those rows are marked not sent. Reuse requires one clean record naming the same known build and model as the pass. A clean normal run starts after the previous sample, sees no record change during the run, and has only agreeing complete identities. Overlap, any read that writes the record (even after resending), an old or unknown writer, partial or mixed observations, or multiple stored values leaves doubt and runs. A later clean normal run can restore reuse. Before sending checks, a run saves an in-progress mark with its pid and start time. Another run's mark, live or dead, makes checks run. Live marks remain until their owners finish; dead marks are retired after forcing a run. A run can finish clean only while it still owns its mark and no other run has changed the record; it removes only its own mark. A failed sign-in removes its own mark but leaves doubt. All check sends share one ownership boundary: normal checks, saved-read continuations, retries and recovery hold their own mark from before the first send until their last send and observations finish. A retry retains ownership across its initial read. Reads and retries finish with doubt; direct callers with reuse disabled still coordinate their sends. Cache clear preserves every in-progress mark. A crash therefore costs one extra run, and overlap remains doubt until a later clean run. An all-skipped local run cannot discover an interpreter update without calls. Stories using the real clock or AI-played fakes run every time and say why; completely deterministic simulation bindings and fixed clock data permit reuse. Fixed clock values must be finite numbers or ISO 8601 date-time strings; labels such as `real 2026`, `now 1` and `1` run with the real-clock reason. Unknown resource kinds or actions run. Missing Story footprints, missing sources or malformed declarations report `runs again: resource declarations unavailable`; reuse can resume once evidence is complete; plain dependencies without an interface declare no resources. An expired pass reports `runs again: saved pass is older than seven days`. `CI` unset or set to the empty string, `0` or `false` permits ordinary reuse; every other value runs every selected Story. A saved pass at most seven days old still counts for prompt approval. Tracked cache files and caches copied without their external machine-local state are never reused. Damaged regular metadata heals after a completed run; its warning names `pdd test --cache-clear`. Dead-owner cache locks recover with one warning. Symlinked ancestors of `PDD_STATE_DIR` are accepted, but a final state-folder symlink is refused.

Run hash filling, local source preflight and the prompt check in one shell call:

```sh
pdd test --fill-hash && pdd test --files STORY && pdd test STORY
```

Replace STORY with the selected Story name. Use `pdd test --fill-hash STORY`
to fill only that Story and its required prompt dependencies; omit STORY to fill
all Git-visible prompts. Each command must succeed before the next starts. Hash
filling and `--files` are local; the final test performs interpreter lint before
sending checks. Do not run `pdd lint` immediately before `pdd test`. Use standalone
lint when you want only format/admission diagnostics without a behavioral check.

`pdd test` reuses a passing lint received within ten minutes for the exact same
captured source, test selection, interpreter endpoint, signed-in account,
package version and lint options. It retains the original receipt for saved
reads; reuse does not extend its age. Local validation and server admission
still run. Missing, incomplete, failed, expired or changed evidence runs lint
again. A reported current interpreter build must match the saved build; when
capacity does not report a build, reuse cannot detect a deployment inside that
short window. This receipt is independent of the complete Story pass cache and
never proves behavior or grants approval. Explicit lint always runs fresh.

`pdd lint --json` includes `report_url` with the interpreter's same-origin report
link, or null when no safe link is available. Text output prints `Report: <url>`
for the same link. Saved lint reads retain it.

- A new simulation defaults to 400 calls. Both `pdd test --max-calls N` and `pdd simulate --max-calls N` accept 1 through 1000. Checks default to 12 calls per step, at least 18 and at most 1000. Choose at least three times your worst-case estimate.
- `pdd test` and saved-batch `pdd test --read BATCH` wait until every Story ends in every shell. Only `--timeout MIN` sets a caller limit. Use the shell tool's longest timeout or an exit-notifying background task; if stopped, run the printed recovery read once. Never poll every minute.
- The optional profile job cap has no default limit. Set `PDD_MAX_JOBS` to a positive safe decimal integer to share that cap across repositories and worktrees among local pdd processes that set it; capped jobs wait their turn and show how many jobs are ahead. An invalid value warns once per command and uses no cap. When the interpreter is busy and confirms that your job did not start, pdd waits and tries again until your wait ends. After a saved lint passes, `--read` can start the original checks that were waiting for it, using the same files, owner and call limits. `--retry BATCH` retries checks confirmed never started, using the same files after lint passes. See [waiting for capacity](lint-capacity.md) for recovery and restart handling.
- Check source uploads use at most 8 unanswered POSTs at once per pdd process. Set `PDD_MAX_UPLOADS` to a positive safe decimal integer (leading zeros are allowed); invalid values warn once and use 8. Each answered POST or transport failure frees its place while server jobs continue running; GET reads use no upload places. This laptop upload setting protects your own connection from the 90-second POST timeout, and is not a server limit. It uses no shared job-slot queue.
- Lint and check results use `waiting`, `sent`, `passed`, `failed`, `refused`, `partial` or `not run`. Every result except `passed` includes a reason code in text, JSON, saved batches and PR evidence. Only `passed` is a full pass.
- `pdd lint --local` exits 0 after its local part and reports `partial` with code `local-only`: checked SVG layout only; prompts not checked. It cannot satisfy a PDD gate.
- For a new check, `--timeout MIN` starts after the free lint. Preliminary lint has a separate wait of MIN minutes, capped at 90 seconds in an agent shell. This bound includes maintenance, local slots and capacity waits. A timeout reports `timeout-flag` and names `--timeout`. Standalone `pdd lint --timeout MIN` bounds lint itself, including admission and capacity waits before sending. A caller stop cause takes precedence over `server-busy`; raw capacity receipts keep their server codes. A default lint wait reports `deadline`.
- Offline-only work uses `pdd lint --local`, local authoring review, `pdd test --files` and `pdd test --fill-hash`. It is not a server lint pass. Factories can bind through interface v2 instances; ports and SQL, blob and compute resources cover declared simulation. Native effects stay unbound; see [Interpreter boundaries](runtime-boundaries.md).
- Running `pdd simulate STORY` for a paused simulation explicitly reopens the same session before showing its link. Its original expiry and remaining call allowance stay in force; an unconfirmed reopen is nonzero.
- A `draft` prompt can be checked, and its result is marked DRAFT. A DRAFT pass is not an approval.
- With no test file, `pdd test` says `No tests found` and lists why, for example a Story with no `tests/<story>.json`, a `.json` file in a test folder that matches no Story, or a prompt with no Runtime interface block.
- A GitHub login that is not invited gets one line: `Your GitHub login NAME is not on the PDD interpreter invite list yet. Ask the PDD team to add you.` A GitHub account without PDD Cloud access gets the server's sign-up line (sign up at https://promptdriven.ai/login). When PDD Cloud cannot check the account, pdd says at once `PDD Cloud could not confirm your access. Try again in a minute.` A pdd that is too old gets `Please update pdd: …`. All of these exit with code 5.
- The interpreter address is set in one place in pdd. You do not need to set it.

Linked `.ui.svg` drawings specify the screen's parts, words, spatial order, ids and named state. Local lint reports unmatched controls, labels and unspecified layout regions; a generic data-field mention does not describe a score box or status bar. SVG warnings do not change the exit code. Default local lint also checks workspace interfaces. Interface findings exit 4 and name the draft command. Named Runtime Story local lint retains its SVG-only advisory; dependency prompts supply layout context. A native-only declaration needs a reason. These local checks do not certify semantic or visual agreement. `--local` belongs to `pdd lint`; it mixes only with Story names and `--json`.

An explicitly selected Story with a `Native validation` owner link is assessed from its saved native evidence by `pdd lint STORY`, including `pdd lint --local STORY`. This reads no hosted service and creates no association. Missing native proof exits 1; complete current whole-Story proof exits 0. It is separate from the SVG-only advisory for Runtime Stories.

For a built screen, serve the app in the state shown by its drawing and run, for example, `pdd test --screen http://127.0.0.1:8080/ --drawing prompts/views/active__stacked.ui.svg`. Set `PDD_CHROME_PATH` to a Chrome/Chromium executable when discovery needs help. The command checks every visible text occurrence and id, including numeric values, at the SVG viewport; metadata, hidden and context-only drawing regions are excluded. It accepts center differences of at most 15% per viewport axis and requires the same spatial order of separated parts. It prints a `Screen vs drawing` table for the code PR; retain any stricter accepted visual comparator. Exit codes are 0 for pass, 1 for mismatch, 2 for invalid input and 5 when browser/navigation execution fails. `--screen` requires `--drawing`, accepts only `--json` alongside them and takes no Story names. JSON includes the comparison rows and `exit_code`.

For a supported Simulator Screen viewer, comparison waits up to 10 seconds after
page load for readiness, app fonts and layout. It inspects only the marked
same-origin app iframe or open shadow surface, using the app's local viewport.
Shell labels and offsets do not participate. Comparison never opens the app,
clicks controls or sends an action. If the app is not open, deliberately open it
before rerunning; opening can spend AI calls.

Exit 6 means the Screen is not ready, rather than a drawing mismatch. Text gives
the state, reason and next step without a parts table. JSON contains exactly
`drawing`, `url`, `outcome` (`not-ready`), `code` (`screen-not-ready`), `state`,
`reason`, `message` and `exit_code` (6), without `rows` or `passed`. Reasons include
`timeout`, `not-open`, `state-read-failed`, `render-failed`, `action-unknown`,
`surface-unavailable` and `viewer-update-required`. An old or unsupported viewer
must be updated before comparison. An unknown action needs read-only state
reconciliation; the comparator never sends it again. Ordinary page reports and
exit codes remain as described above.

See [Check prompts on the PDD interpreter](USAGE.md#7-check-prompts-on-the-pdd-interpreter) for the exit codes, `pdd test --help`, `pdd lint --help` and `pdd simulate --help` for the options, and `RUNBOOK.md` for the file formats.

The Simulator's agent fills the fields directly when supported. It runs the action only when you explicitly ask, in your own words; otherwise you press Run. Actions use the simulation budget. Older pages keep manual Fill fields and Run.

## Try tools for your agent

| Command | What it does |
|---|---|
| `pdd mcp` | Start the stdio MCP server for the current repository; select the Story through tool input. Your agent can open a simulation, inspect its state, run input, check the result against the Story and save a case |

The tools are `try_open`, `try_state`, `try_run`, `try_check` and `try_save_case`. Use them when the person asks to try behavior. Runs count against the simulation budget and appear in the Simulator. Saved results are separate recorded cases with exact starting data. Complete missing Story coverage before `pdd test`; observations need review and are never approved expected values. MCP protocol messages use stdout; progress and diagnostics use stderr.

## Used by the agent

| Command | What it does |
|---|---|
| `pdd workflow done STEP [--summary TEXT] [--skipped REASON]` | Record a finished step. `check`, `try` and `verify` also record pdd's own latest `pdd test`, `pdd lint` and `pdd workflow prove` results, or warn that pdd has none; the summary stays an agent note. `--skipped REASON` records that the step was skipped, and why. Print the next instruction: the next step, the gate, or "pdd opens the PR now". After the last step of an area with a PR gate, push the branch and open the PR when the applicable gate is satisfied. In a normal feature or bug run, a valid Story approval and a verified full saved check pass open PR 1 without another question; strict and other routes can require a separate approval gate. The bug skill still allows only 2 defect repair rounds after review. |
| `pdd workflow ask QUESTION` | Show the person that the chat waits for an answer in the middle of a step. `status` then says "waiting for you" with the question |

The agent runs these from the run's worktree. pdd finds the run from that folder. You do not run them yourself.

## Other commands

| Command | What it does |
|---|---|
| `pdd`, `pdd --help`, `pdd -h`, `pdd help` | Show the commands and the full paths of the installed Prompting guide and RUNBOOK |
| `pdd help prompting` | Show how to write a prompt, a Story and its test, which commands check them, and the full paths of the Prompting guide and RUNBOOK |
| `pdd --version` | Print the version, `0.1.29`. When the PDD skills that your agent finds are older, also print the update command on stderr |
| `pdd -V` | Same version and local diagnostics as `pdd --version` |
| `pdd -VV` | Print the local CLI version, the interpreter's full build identifier and its supported interface, test and app-map format IDs. Use existing gh sign-in without prompting; unavailable metadata prints `PDD interpreter: unknown` and exits 0 |
| `pdd completion bash\|zsh` | Print a shell completion script. It does not change your shell files |
| `pdd jobs` | List active slots and waiting interpreter jobs on this machine, including kind, PID, age and request IDs. Local and read-only; no repository, authentication or interpreter call |

`pdd -VV` skips PATH and skill diagnostics. It reads the existing token with a
two-second limit, then sends at most one `GET /v1/version` to the configured
interpreter origin. The request and response body have one ten-second limit.
It follows no redirects, sends no source, starts no jobs and makes no AI calls.
Format IDs keep the interpreter's order; an empty list shows `none`, and a
missing or unsafe list shows `unknown`. Each version flag must be one exact
token; repeated flags, extra operands and `--verbose` are unsupported.

## Run from a source checkout

From a clone of this repository, run the CLI without a global install:

```sh
node bin/pdd.mjs --help
node bin/pdd.mjs --version
npm test
```

You need Node.js 22.16.0 or newer. The package has no dependencies and no build step. See [CONTRIBUTING.md](../CONTRIBUTING.md).

Check, remote lint and simulation setup use [local bookkeeping and capacity waiting](lint-capacity.md); they share a local slot cap when `PDD_MAX_JOBS` is set. Local waiting, maintenance and interpreter queue time all use the existing caller wait. `pdd simulate` uses one five-minute setup allowance for lint and the rest of setup in every shell; it adds no timeout flag.

A saved Simulator setup is read by its original request ID before any new setup is considered. A plain repeat keeps that ID when the setup is pending, unknown, missing, expired or ended; it does not create a replacement. Recovery diagnostics name the original UUID and its authenticated `GET /v1/runs/<UUID>` status endpoint. A known running setup reuses its existing link. Start a separate setup deliberately with `--new` after reconciling the original outcome. An unknown setup result does not prove zero AI calls or zero external effects.

`pdd simulate [STORY] --cli [--shell] [--max-calls N] [--new]`

Use the program in your own terminal. Copy the printed PATH line or run the absolute shim path.

`pdd simulate [STORY] --serve [PORT] [--max-calls N] [--new]`

Serve the Story on localhost (default 8080).

`pdd simulate --save-last`

Append the last command and its observed output to its original Story test file.

Story counts use the newest source-compatible evidence across check, verify and saved evidence records. Unknown results stay unknown. Source changes invalidate old counts. To refresh counts without rerunning workflow steps, save `pdd test --read BATCH --json` outside the repository, then run `pdd workflow evidence ISSUE --summary /path/to/check.json`. The JSON must retain its repository, selected test paths, Story lines and source SHA. This records saved evidence, not new execution or approval.

To register an earlier failing check of a bug after its prompt changed ("fails before the fix"), name a local commit whose files are exactly the checked files, then import the original saved JSON:

```sh
pdd workflow evidence-associate 18 --workspace . --stage before --commit <full commit SHA> --test tests/count-words.json
pdd test --read <BATCH> --json > /tmp/before.json
pdd workflow evidence 18 --summary /tmp/before.json
```

The selected source at that commit must have the saved check's exact `source_sha256`, and each test must be a current test of the same Story. pdd shows the result as `Before the fix (commit SHORT, batch BATCH): …`. It never counts as a current result, check or approval.

An explicit `pdd lint` that is still queued/running exits 3 and prints its saved read command; exit 0 means validation finished successfully. The all-Story cost estimate includes entry executions, declared saved-data operations and nested prompt-call allowances. Conditional operations may use fewer calls; `--max-calls` remains the hard cap.

Virtual CLI and HTTP startup print `Try AI usage` on stderr. Each virtual CLI command appends its usage line to stderr, keeping program stdout and exit status intact. It distinguishes calls for this command, total used and remaining in this simulation, and the session cap. Unknown counters stay unknown. Named HTTP routes carry `x-pdd-ai-calls`, `x-pdd-try-used`, `x-pdd-try-remaining`, `x-pdd-try-cap`, and `x-pdd-usage-source` headers; response bodies and program statuses stay intact. `runtime` identifies a confirmed call receipt; `last-known` identifies cached session allowance on a local zero-call response such as an unmatched route. Session allowance is separate from an account or tester allowance. Usage reads spend no model calls and never repeat commands.

`pdd test --read CALL_ID` reads an authenticated owner call receipt by UUID without sending the operation again. Interrupted `pdd simulate --cli` commands print the recovery command for this read. See [module binding coverage](runtime-bindings.md) for selected Story coverage and unbound reasons.

`workflow prove` leaves the saved run base unchanged. Fresh worktrees have no installed dependencies; include required installation in `--test`. The command inherits your environment and network access, and shares the repository’s Git refs and config, just like tests run by hand. Interrupting with SIGINT, SIGTERM or SIGHUP stops the process group and removes both snapshots before exit 130, 143 or 129. Only positively owned stale proof worktrees with inactive owners are recovered; unrelated worktrees are left alone.

Preliminary lint shares Check's unlimited default caller wait; standalone remote lint retains its 90-second agent default and unlimited interactive wait. `--timeout` bounds either, with no separate lint cap. A saved-batch read of a lint-held Check waits without a default limit, retains the saved interpreter origin and dispatches each original check at most once. Explicit retry retains its finite default wait. Standalone lint reads never send checks.

Before sending work, pdd asks whether the interpreter has room. During announced maintenance, it shows the end time and reason, then waits within the same deadline. If the interpreter does not offer this information, pdd uses the reply to the submission instead. A queued job keeps its ID while pdd shows its place. If the interpreter confirms that a check ended because the service restarted, pdd tries that check once more and saves both attempts and their usage. If a reply is lost or the outcome is uncertain for another reason, pdd reads the original job without sending it again.

## Shared records

| Command | What it does |
|---|---|
| `pdd contracts` | List shared records in working files, their prompt/test users, changed records and Stories needing a new check. Local; no interpreter calls |
| `pdd contracts sync [--write]` | Preview replacing inline copies with references. `--write` applies unambiguous proposals and adopts the shared shape; ambiguous matches warn and stay unchanged |

Use `{"$contract":"contracts/phone-server.md#order_in"}` in a schema of the Runtime interface.
The Markdown section has a `### order_in` heading and one JSON code block;
headings with spaces also accept their normal heading fragment. JSON records use
`{"$contract":"contracts/records.json#/defs/order"}`. Local `title` and
`description` may accompany a reference; other constraint siblings are refused.
Use `"initial_world":{"$seed":"contracts/seed-world.json","set":{"/orders":[]}}`
for a shared starting world. Paths are relative to the repository root. Set
pointers apply in written order to a fresh world and may add an object's final
key; their parents must exist. Expected values and literal inputs stay literal.

`pdd test`, `pdd lint` and `pdd simulate` use expanded schemas/worlds, including uploaded bytes. A
missing target stops before upload. Real schema `$ref` remains refused. Explicit
`pdd lint` skips inline schemas with fewer than three fields. It advises
about a differing copy only when the shared record has at least four fields and
the copy has the same fields or one extra/missing field. Equal three-field copies
can still move to references. Required-field lists and enum alternatives compare
without order; arrays inside literal values keep their order. Advice does not
fail a check. Expanded uploads keep the original JSON layout and key order.
Sync changes only selected schema values and an approved-to-draft status, using
an atomic file replacement that refuses concurrent edits and unsafe paths. Listing uses actual Check
history, never lint as a check; no baseline is shown as not checked/unavailable.
Only Stories using a changed record become stale because of that record. A
Story stays current when you check one of its tests or include it in a larger
batch without changing its files.

`pdd approve` still approves prompt prose; it does not cover shared contract
contents. Editing a contract never approves a prompt. Sync writes that edit an
approved interface set it to draft; review the preview and approve it as usual.

## Product plans

| Command | What it does |
|---|---|
| `pdd product status [--json]` | Count Stories by part and slice from current saved checks; identify stale results and remote evidence from PRs. Makes no interpreter calls |
| `pdd product next` | Show ready planned runs and their start commands; parallel starts are optional |
| `pdd product start RUN [--no-run] [--agent codex\|claude\|gemini\|agy\|ENTRY]` | Find or create the run's issue once, then start a normal feature run; `--no-run` only finds or creates the issue. ENTRY is an entry name from `~/.config/pdd/agents.json` |

See [Build a whole product](build-a-whole-product.md).

## Record a chat approval

Show the gate before you ask for approval. The person may reply in their own Claude Code or Codex conversation, or in Herdr. No Herdr area chat or terminal is needed in easy mode. The agent judges the later reply. Questions, change requests and earlier messages are not approval. No exact phrase is required.

After the person approves, record their exact words. For the ready gate and all its draft prompts, use:

```sh
pdd workflow approve N --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

For one prompt outside a workflow gate, use:

```sh
pdd approve PROMPT --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

Replace the payload line with the person's words. Choose a delimiter that does not occur as a whole line in those words. Keep the delimiter quoted. Do not put the words into shell quotes or interpolate them into a command. `--said -` reads stdin exactly, including newlines. Blank input is refused. pdd records nonblank words without a yes-word list or semantic grading.

When the gate is shown, pdd saves the selected prompt paths and prose hashes. Approval covers that snapshot. If a prompt changes, show the gate again before approval. Output lists the prompt paths and hashes. Only an explicit approve call passes a gate. Chat messages, steps and `workflow done` never approve it. A workflow with no approve gate before code gets a warning.

In a normal run (no `strict_approvals`), the Story gate prints a Story card; show it as printed, then ask. The person approves each Story with that context and may choose the code PR after PR 1 (`--through code`). After that approval, a prompt-only repair needs no new approval. When pdd verifies its own saved check results (every criterion of every scenario in the default project check scope passes, and each result belongs to its batch and matches the current files), `pdd workflow done` opens PR 1 with no question and records the route `automatic-check-pass`; PR 1 shows it as `Opened after a full check pass (no person asked):`. pdd skips the optional try step. A failed check keeps the gate for repairs. A change to a Story, the plan or an expected value shows the card again and waits for the person. The same checks apply before updating an open PR 1 and before a later said or terminal code approval, including after PR 1 merged. A revised Story must be shown and approved first. Unpublished source changes need a current full check. Default discovery excludes nested fixture projects, as `pdd test` does. With `--through code`, pdd then starts the code area and records the route `card-choice`. Strict mode keeps its person gates. A changed Story reopens Story approval and replaces any earlier check-failure guidance. Missing or unverified coverage, incomplete or stale checks, strict policy and unavailable authority keep PR 1 closed. Normal runs with missing coverage keep their person gate. Status shows the hold reason. A cancellation, new person question or changed gate during preparation or publication stops further approval, push and PR effects. This includes a blocker saved while waiting for the approval journal lock: pdd rechecks the saved run under journal custody before committing approval evidence. Saved blockers remain in place. `pdd workflow status` names the runs that wait for a Story approval.

Without `--said`, a person at a normal terminal answers y/N. The question lists the gate and its drafts; one answer approves them together. `pdd approve PROMPT` still approves only one prompt. Agent, non-TTY and current Herdr chat-pane callers must ask the person, then relay the reply with the safe form above. Native Herdr evidence never authorizes approval by itself.

Workflow approval reads `pdd.json` from the main checkout (`sourceRoot`), outside the agent's run worktree. Standalone `pdd approve` reads it from the Git root of the current checkout. `"strict_approvals": true` permits only a person at a terminal and refuses `--said`. Absent or false keeps easy mode. Agents never edit approval fields or decide expected values. Records retain the invoking actor, time, route, exact words and prompt path/hash. PRs show matching approvals safely quoted. Approval of PR 1 does not approve the later code-or-stop gate.

`pdd workflow ack REQUEST_ID --summary TEXT` records the agent’s uptake of a delivered change request from its active run worktree. The first note and time are retained on repeat calls. Delivery and this explicit agent claim do not prove the request was fully addressed. Status shows delivered requests still awaiting uptake; done warns without blocking progress.

`pdd workflow approve [ISSUE] [--said WORDS] [--draft]` records the ready approval gate. A normal Story-card choice can also use `--through prompt-pr|code`.

## Metrics

- `pdd metrics [--json] [--date YYYY-MM-DD | --snapshot ID] [--timezone IANA] [--at UTC] [--expected-source ID...]`
- `pdd metrics export FILE [--timezone IANA]`
- `pdd metrics import FILE`
- `pdd metrics record FILE`

`pdd graph` reads the saved dependency graph; `pdd graph --open` opens its viewer. Use `pdd graph --issue N` to select an issue, or `pdd graph --open --issue N --repo OWNER/REPO` to select a repository explicitly.

`pdd dependencies prepare [--issue N]` reads a scoped native review packet without AI or GitHub writes. `pdd dependencies complete --input -` reads a structured completion from stdin, saves the review and reconciles its intended effects. `pdd workflow yield N` hands off automatic capacity after the current worker has stopped.

The `pdd workflow park` forms record a stop in the run worktree. Each one keeps the run, its claim, branch, worktree and completed work, and asks no person.

`pdd workflow park --reason TEXT --step STEP` records an environment failure of
check, verify or formal in the current area. Environment parks require `--step`;
pdd does not guess the failed target from unfinished steps in an older run.

`pdd workflow park --route KIND --reason TEXT [--until FIX] [--step STEP]` records a missing supported PDD route. Use a lowercase kind such as `interface-drafting` or `native-replay`; put the agent's full question in `--reason`. The default fix is `capability:route-KIND`; `prompt-reentry` uses `#2897`. An explicit fix can name a capability, issue fix or commit. A package version alone cannot clear this wait. The command keeps gates and independent questions.

`pdd workflow park --reason TEXT --blocker KIND [--until VALUE]` names an external wait. Use `dependency --until 2897` for an issue that must merge, `pdd --until capability:prompt-reentry` for an installed capability, `pdd --until commit:SHA` for an installed ancestor commit, or `pdd --until '#2897'` for the PR 1 re-entry route, or `account` / `github` with an ISO reset time. `person` requires an existing pending question or gate and clears on its reply. `ci` and `review` use the saved PR result or review evidence. Invalid clearing values save nothing.

`pdd workflow park --reason TEXT` records an automatic stop from its existing run worktree without releasing its claim or treating the worker as done.

A lost verdict, such as `runner-stopped`, needs a person decision before another paid attempt. To authorize one resend for each listed run, relay the person's exact words:

```sh
pdd workflow resend 17 23 --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

Use a quoted delimiter absent as a whole line from the words. Without `--said`, a person can use terminal y/N. Strict mode requires a person terminal. This decision does not approve prompts or workflow gates. Automatic setup and start do not authorize it. There is no automatic resend budget setting.

pdd saves the decision, old batch and earlier cost before sending only the lost checks. It keeps the original call caps or lowers them to the smallest selected cap. Active checks, changed source and consumed attempts cannot be resent. The new batch is saved in the run's `checkResends` record. If another attempt has no verdict, the command stops the group at once and names that batch for the interpreter owner. A `service-restarted` receipt also stops this command without an automatic replacement. Later reads and retries of that batch keep this limit. An interrupted send is uncertain; it is never replayed automatically. Gates, questions, parks and completed steps stay as saved.

`pdd workflow park --interpreter --reason TEXT` records that a run waits for the PDD interpreter, the hosted service behind `pdd test`. pdd first reads the run's latest `pdd test` result. Only a check with no verdict from the AI service, a busy or not-run check, or an unknown outcome may wait. A failed check, a refusal that names a file rule or a step that took longer than the server time limit is the issue's own work (make the step smaller). A sign-in, access or interpreter address problem needs a person, and waiting does not fix it. For these, the command exits 1, names the fix and parks nothing. If pdd cannot read the result, the outcome counts as unknown. A waiting run asks no person. `pdd workflow status` shows `waiting for the interpreter: REASON`, and `pdd graph` shows the hold `Waiting for the interpreter`. The run keeps its claim, branch, worktree and progress.

## Shared full-suite queue

`pdd workflow suite --command COMMAND [--timeout MIN]` runs the repository's full
suite through one machine queue. Use the actual repository command, for example
`pdd workflow suite --command "npm test"`. Focused tests can run normally.

Each suite uses fresh temporary HOME, PDD_STATE_DIR, XDG_CONFIG_HOME and TMPDIR
folders. The runner removes them after execution. It passes PATH, locale, time
zone, terminal and CI settings, the browser path and its assigned PDD_CHECK_CPUS.
Agent settings, credentials, session variables, shell hooks and Node/npm overrides
are absent. Set extra variables explicitly in COMMAND when the suite needs them.
Queue admission still uses the caller's queue selectors. Each ticket records
`environmentPolicy: "clean-v1"`, without environment values.
If private folder setup fails before execution starts, the ticket finishes with
the failure reason and releases its slot. Any allocated private folders are removed.

The native CLI prints a receipt path in the shared queue and an output-evidence
log path under user state for each attempt. The compatibility runner keeps its lifecycle output; its
receipts are in the same queue. The receipt stores a redacted command, its SHA-256 fingerprint, cwd, starting Git head and
worktree fingerprint, matching workflow run, owned recorder and child, terminal
exit and signal, and complete TAP summary counts when available. Missing counts
stay unknown. Logs and receipts use mode 0600. Logs are under PDD_STATE_DIR, or
HOME/.local/state/pdd, in a validation folder for the selected queue.
`scripts/vm-suite-lock.sh` and `scripts/vm-suite.sh` select caller log state
explicitly: a nonempty PDD_STATE_DIR wins; otherwise they use
`PDD_SUITE_QUEUE.state`, or `LOCK.queue.state` beside the resolved compatibility
lock when no queue selector is supplied. Logs survive temporary child cleanup.
Without a state override, an external lock and queue keep both scripts' writes
outside the caller HOME.
The legacy history stays beside the lock. Factory callers select their own
private PDD_STATE_DIR; HOME fallback tests use disposable homes.
Log names
combine the queue-path hash, ticket and a random attempt ID. An existing file
causes a fresh ID to be selected. Resetting the queue or rebooting preserves
earlier logs and permits a new attempt. Commands are saved as
`[redacted]` because positional arguments can hold secrets. Execution uses the
original command. Known secret values in output and error text are redacted before any save or
forwarding. The completeness guarantee covers what the validation child can
print: secret-named values in its own environment (TOKEN, SECRET, PASSWORD,
*_KEY and similar names), and credentials pdd passes in arguments, handed-over
files or agent-definition environment overrides. A CUSTOM_API_KEY loaded from
agents.json is included before a child receives it. Credentials held only by
other processes, such as an alert bot token that the validation child cannot
read, are outside this threat model. Exact matching scans original text from
left to right and consumes the longest known match at each position, regardless
of registration order. This rule also applies to receipt strings and errors.
Each stream keeps a bounded overlap window based on the longest known value.
Exact matches can span chunks and lines, including values containing LF.
Transformed or encoded copies are outside this exact-value guarantee.
Pattern redaction for unknown headers, assignments and private keys is a
best-effort extra layer. Unknown formats, encodings and arbitrary positional
values can evade it. Do not treat pattern matching as complete secret detection.

Each log is limited to 1 MiB. Overflow keeps its beginning and end with an exact
`N bytes omitted` marker. A pending output line is limited to 256 KiB; a larger
line is omitted in full with its byte count. Bounded scanning still tracks
quoted secrets and private keys in omitted lines. Their continuation stays
redacted through its closing delimiter or end of output. A recognized credential
field stays pending across assignment whitespace, including line breaks and
omitted lines, until its quoted or unquoted value is redacted. Stdout and stderr
keep separate recognition state. Basic/Bearer schemes also stay pending across
line breaks and omitted whitespace until their credential is suppressed. Each receipt is limited
to 64 KiB, with free-text fields limited to 4 KiB. Required source and ownership metadata
that cannot fit prevents execution. The `evidence` fields report raw output
bytes, saved log bytes, omitted bytes and whether truncation occurred. Counts
and exit status use the complete process stream, including when storage is
truncated. Ordinary secret replacements do not count as omitted bytes. These
limits apply per attempt; earlier attempts remain available.

The recorder keeps the same validation running if its calling session disappears.
A later `pdd workflow status` reads its saved progress without running the command
again. Completion saves the log and terminal receipt before returning. Explicit
SIGINT/SIGTERM cancels through the recorder; unexpected caller loss leaves the
original timeout in force. If custody is lost before a terminal receipt exists,
status reports an unknown outcome. A later validation has its own ticket and
keeps earlier evidence. A receipt describes execution; it does not approve a merge.

Full suites and full builds share machine capacity across repositories and
worktrees. Run a full build through the same command. Additional
runs show "waiting for a check slot (position N)". Workflow status also shows the
queue position. For an Autopilot job, a wait for a check slot is not quiet time.
A suite failure, interruption or execution timeout has its own reason.

The execution timeout defaults to 30 minutes. `--timeout` accepts 1 to 120
minutes, or 0 for no time limit (Autopilot uses 0 and watches the suite for new
output instead). Waiting does not use that time. Output and exit status come from the
suite; timeout returns 124. The runner stops the suite process group before
releasing its slot.

The queue reads usable CPU IDs, free memory and one-minute load when it admits a
check. macOS and personal Linux machines use the first half of available
cores (round down, minimum one). Linux desktops without batteries are included.
Linux uses all available cores only when virtualization is detected and no battery
is present. Detection uses `systemd-detect-virt --quiet` with a one-second timeout.
If detection is unavailable or uncertain, Linux uses the personal-machine budget.
With U usable cores and M free bytes, calculated check slots are
`max(1, min(floor(U / 12), floor(M / 4294967296)))`.
Without Linux taskset, calculated slots are capped at one. With enough memory,
Linux VMs with taskset and 4, 8, 16, 32, 64 and 96 cores get 1, 1, 1, 2, 5
and 8 slots. A 96-core machine with 8 GiB free gets two slots.

Each check gets `max(1, floor(U / chosen slots))` cores. Linux taskset gives each
check a distinct CPU list from the parent's allowed CPUs, so tools such as
`nproc` and Node `os.availableParallelism()` see that share. Every child receives
`PDD_CHECK_CPUS` with the share. macOS and Linux without taskset use that hint;
custom test or build tools must read it to set their worker count. If affinity
slots outnumber CPUs, extra checks wait for a distinct CPU share.

When the one-minute load is above U, new checks wait in the queue. Running checks
keep their CPU lists when the machine shrinks; queued checks wait for free CPUs.

The default queue directory is `/tmp/pdd-full-suite-UID`, where UID is the local
user ID. It is independent of repository, HOME and agent profile. All launchers
on the machine must use the same queue directory. `PDD_SUITE_QUEUE` can select
an absolute shared directory. `PDD_VM_SUITE_LOCK` selects `VALUE.queue` when
`PDD_SUITE_QUEUE` is absent. `scripts/vm-suite-lock.sh` uses the same queue.
Autopilot keeps both selectors in its saved environment and timer. Workflow status
reports an unavailable queue with its cause.
Queue records stay outside the repository and contain no commands or test output.

## Local issue costs

`pdd autopilot status --json` prints `pdd.cost-report.v1`. Use `--all` to include
indexed repositories. This form reads local files only. Human status includes
day and week totals, outcomes, account token totals, and nearest-rank P50/P90
costs per merged issue. Multiple attempts for one repository/issue are combined,
including archived attempts when a run path is reused. Cost reads keep the last
workflow progress time, so polling does not delay stalled-run warnings.
Totals use the time each measurement was observed. Percentiles use cumulative
costs of issues whose latest outcome was merged in the selected period.

`pdd workflow cost ISSUE [--input -]` reads an issue cost row as JSON. With
`--input -`, it records an explicit measurement from stdin. For example:

```sh
printf '%s\n' '{"id":"suite-1","suiteMinutes":2.5,"personMinutes":1}' | pdd workflow cost 17 --input -
printf '%s\n' '{"id":"result-1","outcome":"reverted"}' | pdd workflow cost 17 --input -
```

A repeated id with equal values has no effect. Conflicting values are refused.
The accepted outcomes are merged, reverted, stuck, closed and parked. This changes
only cost data. It does not approve a prompt or change workflow progress.
Measure suite elapsed wall time, including failures. `workflow prove` records its
two native phase durations automatically; other agent-run suites need an explicit
measurement. Person active minutes are explicit measurements; waiting minutes
come from questions, answers and gates. Approval counts include every recorded
approval, including one recorded by an agent on behalf of the person. The recorder
identity does not prove active person effort. These are separate quantities.

The ledger is saved in each run's local `status.json` as `cost`. Its numeric GitHub
call journal is `github-cost.jsonl`. Calls made by pdd from that exact run worktree
are counted, including normal runs. Calls made by agents outside pdd are
excluded. Costs remain after GitHub budget compaction.

Token accounts are hashes of local config profiles, not billing identities. Codex
usage comes from cumulative rollout counts. Claude usage comes from transcript
usage, with streaming duplicates removed. Each session read is limited to 256 KiB;
Claude backlogs are consumed on later captures, including after a chat moves to
abandoned custody. Saved current, abandoned and replacement chats use their own
account and session identities; repeated custody does not add usage twice. Missing
files, backlogs and unknown minutes appear in coverage. No message text, credentials or monetary estimates
are saved. Cached input and reasoning tokens are subsets, not extra total tokens.

At PR closure, pdd reserves one Actions duration read for the saved PR branch,
including earlier heads. Without a saved branch, it reads the observed head only
and marks coverage incomplete. It reads at most 100 workflow runs, without pagination. CI minutes are elapsed
workflow wall time, not billed job minutes. Incomplete data is marked in coverage;
a failed or interrupted measurement is not retried. Status never fetches durations.


## Runtime interface kinds and coverage

Omit `kind` for a full interface; explicit kinds are `partial` or `native-only`.
A draft with `"kind": "full"` gets a warning at `/kind`, not a refusal. `pdd test --fill-hash`
reports and removes that redundant field from drafts, including current drafts.
Approved prompts stay unchanged.
Native-only requires a reason that names an effect the bound ports cannot fake
(RUNBOOK §21). A checker reviews the reason. Approval records it. Checks show
`not run: <reason>`, with no passing result. Other selected tests can run.

Test output, workflow status and saved PR evidence include prompt coverage counts. Text uses `Runtime coverage: N of M prompts checkable, K native-only` for native declarations and `Interpreter coverage` otherwise. A response with only passed and busy checks uses `Runtime coverage` and retains all coverage counts. Native-only rows retain their paths and reasons, including all-local selections. Invalid native-only scenarios retain refusal details as `not run (broken-test)` and are never uploaded.

Saved reads preserve native-only outcomes and reasons while other selected rows
wait for lint or complete it. Local lint also saves coverage and omission evidence
when another selected row is refused before upload. These local results can be
read without authentication. Repository-wide `pdd lint` preserves this evidence
when any prompt lacks an interface, including an unselected prompt. Its saved
read retains the global diagnostics and exit 4. Repositories without Story tests
still get global missing-interface diagnostics. Temporary lint failures retain local paths, reasons,
refusals and coverage in text and JSON, and return exit 5. Named lint targets
include only executable scenarios present in the uploaded archive. The files
preview uses that same selection and shows native omissions with their reasons.

M includes missing, stale and invalid blocks. Checkable means a valid current full
or partial declaration; it does not mean that all module behavior has passed.

`pdd interface draft --all` selects workspace prompts and excludes nested fixture
projects. Without extension or refresh, existing blocks stay unchanged. Each result includes local lint findings.
A clean local lint is not a server lint or a prompt check. Setup offers this command
when it finds missing blocks. It never approves them.


Locally valid authored drafts omit the redundant `kind: full` field so the strict Runtime
parser can read them; a missing kind means full. Partial local drafts retain
`kind: partial` and their questions.

The local prose drafter recognizes an explicit single-operation transport: a named
operation, a required named input field with its type, and a required named result
field with its type, in closed objects. It requires an explicit pure-behavior
statement. Its draft execution ceilings are `max_steps: 4` and `max_model_calls: 2`.
The result labels these as `command-default` draft budgets for review. A prose
draft that uses them needs a person and cannot use automatic approval. To choose
other ceilings, supply a contract with `--refresh --contract FILE`.
Numeric inputs remain numbers even if the function rejects fractions. A contract
that explicitly requests representative JSON rejection shapes can use a disjoint
`oneOf` for number, string, boolean, null, arrays of numbers and empty objects.
This transport does not cover arbitrary nested JavaScript objects.
The JSON row includes local `lint_clean` and a `prose_coverage` report. A draft
never claims completeness. Each quoted contract sentence is `mapped`, `unmapped`
or `conflicting`. Mappings name exact fields and their retained values in
`mappings` (`pointer` and `meaning`); `pointers` lists the same fields. A description
can retain prose meaning, but cannot override a contradictory schema type.
Unknown meaning stays unmapped. Each unresolved sentence has a review question
and a next step. This report is evidence for review, not proof of behavior.

The report covers prose, embedded JSON, dependency JSON, `--contract`, `--refresh`
and `--extend`, including declared context after shared `$contract` expansion.
Valid authored JSON is accepted as the author's declaration even when coverage
needs review. Coverage does not make it partial or rewrite its fields. Extension
preserves approved declaration bytes. Prose inference with unresolved meaning
stays partial. Local lint is not Runtime admission: Runtime lint must pass before
an executable draft is used. Import, refresh and extension validate expanded
schema copies and preserve authored references in the saved block.

For complex prose, each incomplete result has `questions` with `pointer` and
`question`, and `next_step`. Answer the questions in a Git-visible JSON contract
file, with complete `entries`, `calls`, `resources`, `limits` and `conventions`.
Authored `draft_gaps` and malformed inferred schemas also produce questions and a
next step on the first invocation. Repeating the command keeps those questions
stable.
Use the resource declarations in [RUNBOOK §21](../RUNBOOK.md#21-fake-the-outside-world)
for file, network and program ports. Then run:

```sh
pdd interface draft prompts/example.prompt.md --contract contracts/example.json
pdd lint example
```

If the prompt already contains an incomplete block, add `--refresh` to the draft
command. A supplied invalid schema is refused before the prompt changes, with its
JSON pointer and rule. Local drafting does not contact the Runtime. Runtime lint
must admit the draft before a check; admission alone does not prove behavior.

To add operations to an approved interface, supply an additive contract fragment:

```sh
pdd interface draft prompts/example.prompt.md --extend --contract contracts/additions.json
```

The fragment can add entries, resources or prompt calls. Existing declarations and
limits must remain equal; conflicts name their pointer and leave the prompt
unchanged. Extension preserves the exact bytes of existing declarations and appends
new array members. The Runtime format has one global status, so it cannot hold
mixed approval status. The whole interface becomes draft and requires full
re-approval. The result declares `approval_scope: "whole-interface"` and includes
`interface_diff` with before/after JSON and unchanged declaration pointers. The
approval view shows the scope and interface diff. Historical approval evidence
stays intact. To reopen a stale
block without changing its declarations, use `--refresh`. To replace declarations
for changed behavior, use `--refresh --contract FILE`. These routes keep prose
bytes and never record approval. Extension and refresh cannot use automatic
approval provenance for new behavior.

Runtime refusals retain a reported field pointer and rule. A supplied rule also
stays visible when the field is unknown, beside the field-unknown note. If the server gives
only `invalid-interface`, pdd reports any local schema findings separately. When
there is no local finding, it says that the Runtime did not identify the field.
No inferred cause is presented as a server diagnosis.

The approval view shows the current coverage report. If any sentence is unmapped
or conflicting, it asks one grouped question with the quoted sentences: amend the
prose, amend the declaration, or accept the authored contract as written. A person
must decide. Delegated approval cannot answer this question.

The automatic approval route requires a valid draft from this command with no
unmapped or conflicting contract sentence in its freshly computed report,
unchanged committed prose, code and tests, passing existing native tests, and full
prompt-check results on current source. It records `automatic-check-pass` with the
command, results and source hashes. New behavior requires a person.

Automatic native-test commands use `node --test TEST...`, `npm test` or
`npm run test:NAME`. Node files must be committed test files. The command must
finish with a TAP report, at least one test, all tests passed, and no failures.
Build scripts and commands without test results do not qualify.

## Core engine

Autopilot has one engine, the core. Each tick makes no AI call, so the timer runs a
tick every 10 minutes. Each job is a headless Codex or Claude process with a log
file. The core needs no Herdr: `pdd autopilot doctor` has no Herdr check, and
`start` opens no chat. `--label NAME` sets the opt-in label and
`--mode auto|observe|off` the mode, on this machine only (`pdd autopilot observe`
changes `pdd.json` instead). The machine values win over `pdd.json`, and
`pdd autopilot status` says where the label and the mode come from.
`--report file|draft|off` sets where this machine's problem reports go, the same
way. `--decisions ask|decide` (or `autopilot.decisions` in `pdd.json`) sets
whether a job may ask a person about a choice. Autopilot decides when at least one
reasonable fix solves the problem and breaks nothing that people use today, and lists
it in the PR under "Choices Autopilot made", with its reason and "(changes public
behavior: …)" when users see a change. A bug fix or a small change never asks about a
choice. With `ask`, routine compatible choices of command syntax, options or data
representation are agent decisions when a safe, low-surprise choice exists. Preserve
existing APIs, defaults and behavior unless the request authorizes a change. Several
valid designs alone are not a reason to ask. A job may ask one plain question with 2
or 3 options and a recommended one (you answer with one letter) only when every
reasonable fix breaks something people use today, or, in a pdd-feature run, when the
choice actually changes product direction: whether a new feature area or capability
should exist, removing a feature, an on-purpose change to a core contract, security,
privacy, data policy, or cost; `decide`, the default for now, asks no choice
question and lists big choices marked "(big)". In both modes a blocker asks: missing
access or a secret, an issue that contradicts itself, work that cannot be done, a
change against a person's answer to an earlier question, and a change of what blocks
merges (a required check, a gate, CI policy). A bug fix may change a rule of an approved
prompt without asking; the PR lists it as "(changes approved rule: OLD -> NEW)", and
the repository's approval setting still applies to that prompt. `--mode off` saves the mode and stops the timer of this machine. In
`observe` mode the core does everything except the merge (it also records the
operator approval of changed prompts, with "in observe mode" in its words; in a
`strict_approvals` repository it asks no person and lists those prompts in its note): when all checks pass, it
posts "Autopilot would merge this PR (observe mode)" with the same evidence, keeps
the PR open and ready for review, releases the issue and adds `pdd:would-merge`, so
no machine builds it again. Remove the label to have it built again. Comments
that the core posts are redacted for secrets and cut in length.

```json
{"autopilot":{"mode":"auto","trust":[],"runs":2,"label":"pdd:autopilot",
  "quietMinutes":45,"report":"draft","maxRepairs":6,"testCommand":"npm test"}}
```

| Key | Meaning | Default |
|---|---|---|
| `runs` | The most issues in progress at the same time on one machine. It can only lower the machine's automatic slots; `pdd autopilot start --runs N` on one machine wins | automatic, from the machine guard (below) |
| `label` | The opt-in label: take only issues with this label. `--label NAME` on this machine wins over it | none: Autopilot takes no issue, and start asks for a label |
| `quietMinutes` | Minutes with nothing new after which an agent process or the checks of a PR end. There is no fixed time limit: a process runs as long as it makes something new (a new commit, a new file state, a new tool call, a new output line, or CPU use in its child processes; a repeated line, a wait or a poll is not new), and a PR waits while CI, the review or the suite still runs. At least 20 (2 ticks of the core timer) | 45 |
| `ciStuckMinutes` | Minutes that CI may stay pending with no change before the job ends | 360 |
| `maxJobHours` | Backstop floor. Each agent process (build, repair, review, suite) stops at the larger of this many hours and 4 times the longest successful process of the same kind in this repository (last 30 days), counted from its own start, whatever it does (sleep time is not counted). The job ends with no result and one alert. At 3 hours a process sends one note and goes on | 24 |
| `report` | `file`, `draft` or `off` for Runtime and PDD problem reports | `draft` |
| `reports.runtimeRepo` | Repository for Runtime problem reports, for example `promptdriven/prompt-runtime`; used when this machine can read it, else `promptdriven/pdd` with label `pdd:runtime` | none |
| `reports.runtimeOwner` | GitHub login to assign Runtime problem reports filed in `reports.runtimeRepo`. Without it, reports have no assignee | none |
| `maxRepairs` | Safety cap of repair jobs for one PR (the old key `repairs` still works). Repairs go on while they make progress: see below | 6 |
| `testCommand` | Full test command that runs on the PR head, in a clean checkout. With `package-lock.json` and listed dependencies, `npm ci --ignore-scripts` runs first | `npm test` when `package.json` has a test script |

**The machine guard.** Autopilot never takes over a person's machine. It may use a
share of the machine's CPU and memory, for all repositories on the machine together:
50% by default, or `pdd autopilot start --share PERCENT` on this machine. The share
counts the real limits: the CPU list and the cgroup or container limits on Linux, the
cores and the memory of the machine.

- Slots: one job counts as 2 cores and 3 GiB (an agent is light, and a full suite
  peaks near 3 GiB). The slots are the share of the cores divided by 2 and the share of
  the memory divided by 3 GiB, the lower one, at least 1 and at most 4. So at 50% an
  8 GB Mac or a 4-core, 8 GB box gets 1 job, a 10-core, 32 GB Mac gets 2, and a 64-core,
  251 GB server gets 4. These slots are for the whole machine: two repositories on the
  64-core server share its 4 jobs. `--runs N` on this machine sets the most jobs of
  this repository; `autopilot.runs` in `pdd.json` can only lower them.
- Every Autopilot process runs at the lowest priority: nice 19, on macOS the utility
  QoS, and in the Linux timer unit `CPUWeight=1` (a weight
  counts only when the CPU is busy, so an idle machine still gives Autopilot all of it;
  at a share of 100 the normal weight) and `MemoryHigh` at the share. On Linux the
  agents run on the share of the CPUs. Every job gets `PDD_CHECK_CPUS`, the worker count
  for its tests and builds.
- Before new work, each tick checks the room for the whole machine: what all Autopilot
  jobs on this machine use now (every repository) must leave room in the share for one
  more job (its jobs, its memory and its CPU), the machine needs at least 3 GiB of
  memory free and no memory pressure, and at least 10 GiB and 5% of the disk free. With
  no room, no issue is claimed, and the tick and `pdd autopilot status` say why
  (`intake held: 4 of 4 Autopilot jobs on this machine run (all repositories, 50%
  share)`). Running work goes on.
- Each tick removes worktrees that no job uses, job logs older than 14 days, and the
  oldest logs while the log folder holds more than 500 MiB.

`pdd autopilot status` shows the share, the slot math, what Autopilot uses now and the
room in one line, for example `Machine: share 50% (default) of 10 cores and 16 GiB ·
slots min(4, 5 cores ÷ 2, 8 GiB ÷ 3 GiB) = 2 → 2 (automatic) · Autopilot on this
machine now: 1 job, 0.4 GiB, 0.3 cores · memory 6.1 GiB free, pressure normal · disk
210 GiB free · load 3.2 · priority low · new work: ok`.

Each tick, without AI calls:

1. List the open issues. An issue is ready when it has no assignee, no live
   `pdd:working` claim, no `pdd:stuck`, no open issue that blocks it (a GitHub
   issue dependency or a `blocked by #N` line in its body), a trusted author and
   the opt-in label. Without a label, the tick claims no issue. The oldest ready
   issue goes first.
2. Refresh the heartbeat of this machine's claims.
3. Check each job. A job that made no progress for `quietMinutes`, failed, died or left no
   result ends. A job with a PR goes to the merge check.
4. Merge check: the PR head is the job's head, CI is green for that head, the
   full test suite passes for that head, a fresh reviewer agent that did not write
   the change gives PASS for that head (the tick posts the verdict on the PR), every
   `Runtime:` line of the PR says `PASS` or `not run (…)`, the head contains the
   current base tip, and the base check passes. Then
   `gh pr merge --merge --match-head-commit HEAD` merges it, and the issue closes.
   A red check starts one repair job on the same branch while the repairs make
   progress: each round must fix every finding of the last round and bring back no
   finding of an earlier round (new, different findings are fine); `maxRepairs` is the
   cap. The END comment names the rule that stopped the repairs. Review findings marked
   P3 never block: they go to a follow-up section in the PR body and one follow-up note
   on the issue. A review FAIL is never a PASS unless all its items are P3, and a PASS
   that lists a P1 or P2 item is a FAIL. A full suite that waits for a check slot in
   the machine's suite queue is not quiet. A
   missing or unclear `Runtime:` line is red, unless the job says no prompt
   changed. A non-zero exit of the test command is red; a failure of the suite
   runner itself (it could not start, was killed or timed out) runs the suite again
   and never uses a repair. Merges go through one **merge lane** per repository
   (the label `pdd:merge-lane` on the PR in its final step, shared by all
   machines): other green PRs wait in claim order with their reviews, and waiting
   never ends a job. In the final step Autopilot checks for an exact conflict with
   `git merge-tree`, brings the PR up to the newest base, runs the suite and CI
   again and merges. Mechanical conflicts (derived hash headers, the same insert on
   both sides, adjacent hunks, JSON keys) are fixed in the lane; other conflicts go
   to a small agent update outside the lane that does not use a repair, and that PR
   goes first when it comes back. A PR ends after its 3rd conflict. The review stays
   when the PR's changed lines stay the same; a base change near those lines, or in a
   prompt that owns one of its files, gets a short scoped check. Each job writes its
   changed files into its claim, and the next job's brief lists them. `pdd autopilot status` shows each PR's place in the lane. When the base moved, Autopilot merges the base into the
   PR branch itself and checks the new head again: the full suite and CI run again,
   and the PASS review is kept only when the merge was clean and the PR's own change
   is the same. A merge conflict starts a repair.
5. Fill free slots: claim the oldest ready issue with `pdd:working` and a claim
   comment, make a worktree and start one headless job. The job runs the same pdd
   as the tick (it goes first on the job's `PATH`, and `PDD_CLI` names it, because a
   login shell can put an older pdd first again; when the agent's shell finds another
   pdd, the job log and `pdd autopilot status` say so). `PDD_SKILLS` names the skills
   of that same pdd, and the job reads its skills from there; when the installed skills
   (`~/.agents/skills` or `~/.claude/skills`) have another version, the job log and
   status say so too. It makes one PR with prompt,
   tests and code where the files are owned by a prompt, and changes other files
   directly: a file is owned when `pdd-bindings.json`, a `Generated from` header or the
   opening sentence of a prompt names it (`pdd owner FILE` gives the same answer). The
   job gets this owner table and writes one `Path:` line per path in the PR body.
   Autopilot takes the changed files from Git and checks the lines against the owners
   on the base: an owned file must be on a path a or b line, a file that the PR adds
   never takes path e, and a new prompt needs a binding or a `Generated from` header.
   When `pdd-bindings.json` on the base branch cannot be read, the PR is not red: its
   merge waits, and after the quiet period the run ends with one report. Existing code
   that no prompt owns changes directly with a regression test, and when the PR passed
   every check, Autopilot files one report that proposes adopting PDD for it. A config
   or metadata file (`package.json`, a lock file, CI settings) needs no prompt, and the
   review never asks for a new prompt for one. The job writes one `Runtime:` line for each changed
   Story, the verdict first and the Story file path first in the parentheses
   (`Runtime: PASS (STORY, N/N checks)`, `Runtime: FAIL (STORY, N of M checks failed:
   STEPS)` or `Runtime: not run (STORY: REASON)`), and one `Evidence:` line in the PR
   body ([RUNBOOK §15, "Autopilot core jobs"](../RUNBOOK.md#autopilot-core-jobs)). A
   single line with no Story is valid only when the PR changes one Story or none. Two
   lines for the same Story are red. It writes no review verdict: only the
   fresh reviewer gives one. In `auto` and
   `observe` mode your `pdd autopilot start` is the approval of the job's prompt
   changes: the job records it for each changed prompt with `pdd approve PROMPT --said
   -`, in the PR. The words start with "Operator action: pdd autopilot start" and
   name the real mode, the repository, the machine id and the time of the start. A changed prompt that
   still has a draft interface is red: a draft, a stale or broken interface, or an
   approval that `pdd approve` did not record. In a repository with `strict_approvals`,
   the job does not approve: in `auto` mode Autopilot asks a person
   (`pdd:needs-decision`) and keeps the PR open; in `observe` mode it asks no one and
   lists those prompts in its "would merge" note.

Only a real Runtime FAIL blocks a merge. A failed check is a FAIL, also when its check
has no verdict because another step had no answer. When Runtime cannot check a change
(a lint refusal, no interface, no verdict with no failed step, a scenario limit that pdd
gives no fix for), the job still ships its PR with native tests and `Runtime: not run
(STORY: REASON)`, and Autopilot files or counts one report for that cause. A value that is not
a safe integer is no such reason: pdd prints its exact Number spelling, and the job
applies that fix and checks again. During announced maintenance the job does not wait:
pdd has sent nothing yet, so the job stops it and writes `Runtime: not run (STORY:
maintenance until HH:MM UTC)` for each Story that pdd did not send, with the end time
that pdd printed. A job never cuts short a check that pdd has already sent, and never
sends a check again itself. Autopilot sends a check once more by itself, once for each
PR head, before the merge lane: a check that pdd never sent (maintenance, busy, or pdd
stopped before sending), and a sent check with no verdict and no failed check (an AI
provider failure). A check with a failed check is never sent again. While the
interpreter is in maintenance the PR waits: Autopilot reads the free `GET /v1/capacity`
again every 10 minutes, the job holds no slot and never counts as quiet, and other jobs
go on. Then Autopilot itself runs `pdd test` once for those Stories (no agent) and
rewrites the line of each one: a pass gives `Runtime: PASS (STORY, N/N checks)`, a real
FAIL goes to a repair, and no verdict keeps `Runtime: not run (STORY: …)` with one
report. The job's history keeps the agent's own lines. After 12 hours of maintenance
the line says `Runtime: not run (STORY: maintenance since HH:MM UTC)`, Autopilot files
one report, and the merge goes on. "Changed" means changed against the base (`git diff origin/BASE...HEAD`),
never since the previous PR head: a Story that a merge from the base brought in is not
changed. A job that merges the base into its branch checks that its fix is still
needed: when the PR's changed tests also pass on the code of the new merge base, the
base already holds the fix, and the job keeps only what the base does not hold.
The `Evidence:` line has a fixed form, for example
`Evidence: runtime=pass (11/11); vectors=pass (36/36); formal=bounded; tests=pass (42/42)`.
`vectors` counts the replay files that the PR changes or that read a changed scenario
file, in `node:test` tests (not steps or checks).
Autopilot keeps only the known parts, saves them in its local history and repeats
them in the merge comment. The claims must be true. A Runtime pass (`Runtime: PASS`,
`runtime=pass` or the result's runtime state) counts only when the saved `pdd test`
checks cover every changed prompt, Story and Story test at the PR head, compared with a
clean checkout of that head (files that are not committed never count; the latest check
of a Story decides; a PASS of other Stories does not count; write `Runtime: not run
(STORY: REASON)` for a native-only prompt; a changed Story with no Runtime test is red
until the PR adds its test, unless every changed prompt is native-only). A repair that only
runs `pdd test` again is read again. Autopilot also runs, at the PR head, every changed
replay (`*.vectors.test.*`) and formal (`*.formal.test.*`) file and every vector file
that names a changed scenario, if it is a `node:test` JavaScript file (other files are
listed as not run). It runs the replay and formal files apart, so each has its own
counts. A failure, a claim that its run contradicts (a vectors count too), or a positive
claim that it could not check, is red, and the merge comment shows its own counts. A
claim that Autopilot could not check (no result, a file it does not run, or a skipped
test) is red once per job; after that Autopilot never repeats it: the merge comment and
the history write that kind as `not-run (Autopilot could not check: reason)`, and
Autopilot files one report. For each PR head, Autopilot writes its own evidence record
(`logs/ISSUE-evidence-HEAD.json` in its state folder, kept after the run ends): the saved
`pdd test` checks it read, each replay and formal file's result, and the full suite. The
reviewer reads it, the merge comment names it, and the PR body gets a short "Autopilot
evidence" block from it.

With `--decisions ask`, a feature job asks one question instead of choosing when it
meets a product-direction decision that the issue does not settle (its brief lists the
other open issues by trusted authors, so it can see an open decision); it opens no PR
then. A bug or small-change job never asks about a choice. With `decide`, a choice
question is never posted: the job runs once more and decides it. The fresh review also
checks the PR's list of choices, and with `ask` it flags a product-direction choice of a
feature that the job made instead of asking (for example one option of an open decision
issue that the change touches). Such a finding
is not repaired: Autopilot asks the one question instead (in `observe` mode too), and
the PR waits for the answer. The next build and
review read the answer, so a settled choice is not asked again.

When a job needs a person's decision, Autopilot posts its one question on the issue,
adds `pdd:needs-decision` (not `pdd:stuck`) and frees the slot. Answer in a comment
(one letter is enough): at its next tick Autopilot reads a trusted person's reply,
removes `pdd:needs-decision` itself and goes on. A trusted person's removal of the
label works too. The next job gets Autopilot's own question and the
comments of trusted people after it.

When a job ends, the issue gets one comment with the cause and the log file name
and loses `pdd:working`. Comments show no absolute path, user name or host name. Nothing else waits on it. A job with no result (the agent
crashed, was signed out or hit a usage limit, or the machine restarted) only
releases the issue: no comment and no label, and its own open PR is closed with a
short note (the branch stays). Such an end counts against the issue only when it is
the first one after a job with a result on this machine; then the issue waits 24
hours before Autopilot takes it again. It is a strike of the issue only when the
next job on this machine has a result too. So an agent outage that ends two or
more jobs gives no strike. An issue that already has 2 strikes in 7 days ends as below at its
next counted end. An END starts the counts again, so a retry starts fresh. Before a
new job starts, Autopilot closes the issue's older open core PRs. When the agent
failed the task, the
issue gets `pdd:stuck`; to retry, remove `pdd:stuck`. When a Runtime or PDD
problem ended it and a report was filed, the issue is blocked by that report (a
GitHub issue dependency, or a hidden marker in the comment when the report is in
another repository) and is ready again when the report closes. If the same
problem comes back after its report closed, the issue gets `pdd:stuck`. An open PR
of an ended job stays open as a draft, with the cause in a PR comment. A PR whose
head has no CI check 10 minutes after it was opened merges on the full suite and
the fresh review alone (its merge comment says `CI: none`) only in a repository with
no PR CI: no workflow that runs on `pull_request`, `pull_request_target` or a push to
the PR branch, and no required status checks. A workflow that runs only on
`repository_dispatch`, a schedule or pushes to other branches is not PR CI. A new head
of a repository with PR CI always waits for its CI. To stop a running job, close the issue, assign it or add
`pdd:stuck`. After three jobs in a row end with no result, Autopilot pauses new
jobs on this machine for 1 hour and sends one alert ("Autopilot paused new jobs for
1 h: the agent ended 3 jobs with no result. Check sign-in and limits."). Jobs that
already run go on. After the pause, intake goes on as usual; if jobs still end with
no result, the next pause is twice as long (2, 4, then 8 hours at most), with a new
alert. An agent that stops because the AI service refused it ("Selected model is at
capacity", "Your workspace is out of credits", a usage limit, a sign-in error, a 5xx)
is an agent account problem, not the issue: the issue is released with no strike and
no cooldown, the end counts toward this pause, and the pause alert quotes the agent's
message. A job with a result, a review verdict or a merge sets the pause length back
to 1 hour. `pdd autopilot status` shows the jobs, the busy slots,
a pause and the time it ends, and the last results from local files.

Each stop where the time ran out has one owner, and only the issue owner blames
the issue:

| Owner | Example | What Autopilot does |
|---|---|---|
| pdd | Autopilot's own merge check step makes no progress (the base check cannot verify the releases, a refused merge) | Files one PDD report, keeps the PR and the claim, and tries the step again after 15 minutes, then 30, 60 and up to 8 hours. It never ends the issue. Repeats count toward the pause |
| service | GitHub answers 502 for the whole quiet period, CI stays pending with no change for `ciStuckMinutes`, the AI account is out of credits | Waits or releases the issue, with no report and no strike |
| service | GitHub Actions does not start a run for the PR head for 20 minutes (queued with no job), or fails it with a billing or spending-limit message | The PR waits for its CI with no repair. One alert and one status line name the cause ("Settings → Billing → Actions"), and no new job starts in this repository until a CI run starts again |
| machine | the agent stops answering | Releases the issue with no strike; the pause counts it |
| issue | the same command hangs again at the same head, or the suite hangs in a test that the PR changes | One strike and one short note on the issue (updated in place), then a repair with the hang details or a later try; the 3rd strike in 7 days ends the issue with `pdd:stuck` |

Agent jobs run with a hung-command watch: a command of the agent that prints
nothing and uses almost no CPU for 15 minutes (a stalled `npm install`, a test that
waits forever) is stopped alone, and the agent goes on. `pdd autopilot status`
shows each wait, its next try and each issue that cools down, with the owner. When
one issue has 3 stops owned by pdd or a service in 24 hours, Autopilot holds it (no
`pdd:stuck`) and files one report; it takes the issue again after a new pdd version
or a comment on the issue by a trusted person.

When the machine sleeps longer than `quietMinutes`, every job's no-progress clock
starts again at wake-up. A job whose claim expired or whose agent ended during the
sleep is only released (no comment, no `pdd:stuck`, and it does not count against
the issue). When
several machines run the core on one repository, each machine's GitHub share is the
`autopilot.github.share` divided by the number of machines with live claims, and a
machine over its share starts no new job. A machine that finishes an END or a release
after a pause writes nothing on an issue that another machine took over.

A Runtime problem (inside Runtime after the call: no verdict, an interpreter error,
server incompatibility, a server-side internal error) or a PDD problem (everything
that goes into Runtime: a lint, interface or binding refusal of our input, test
vectors such as a Runtime case, a scenario value limit or a vector replay; and CLI
errors, crashes, claim or merge-check tool errors) also gets one report for its owners: a PDD
problem in promptdriven/pdd with label `pdd:autopilot-report`; a Runtime problem in
`reports.runtimeRepo` when this machine can read it, else in promptdriven/pdd, with
label `pdd:runtime`. A report has no assignee unless you set `reports.runtimeOwner`,
which assigns Runtime reports filed in `reports.runtimeRepo`. One cause has one report: a
repeat adds at most one "seen again" comment per machine a day. There is no daily
cap on new reports. A filed report holds only fixed fields: the kind, component,
error code, step, versions, count and fingerprint. It never holds free-form text, code
or text from your repository. A short redacted detail stays in the local draft file
only. With `report` `draft` (the default) the
report stays on this machine until you run `pdd autopilot report send
FINGERPRINT`; with `file` Autopilot files it; with `off` nothing is saved. With
`draft` and `off` the ended issue gets
`pdd:stuck`, because there is no report to wait on. Report issues themselves are
never taken as work. A PR that says `Runtime: not run (reason)` can merge and files
no report by itself; a Runtime report comes only from a job that failed for a
Runtime cause.

### Intake cards (shadow)

`pdd autopilot start --intake shadow` turns on intake cards for this
repo on this machine; `--intake off` (the default) turns them off. A later start
without `--intake` keeps the saved value. In shadow mode each core tick first
checks native facts of each open issue in scope (the opt-in label, no report
issues): an assignee, an open native blocked-by link, open sub-issues, a label
`pdd:stuck`, `pdd:needs-decision`, `pdd:would-merge` or `pdd:working`, or a job of
this machine gives a native reason and no AI call. An issue whose author the core
does not trust gets `untrusted` and no AI call. For every other issue, one headless
job of this machine's agent (Codex or Claude) writes one card per issue version,
from the title, the body, the labels, the trusted person comments and the titles of
the other open issues by trusted authors. The card agent runs in an empty folder
with no tools, no write access and no GitHub token (Codex: a read-only sandbox, its
tools off and no MCP server from your Codex config; Claude: no tools, plan mode),
never with the bypass flags of build jobs. A card says ready,
improve, person, duplicate, blocked, held, fixed or elsewhere, with a reason and a
confidence. A new title, body, label, assignee, native link or comment makes a new
version. At most 2 card jobs start per tick and 2 run at once; a card job that ends
with no valid card is tried again after 6 hours, or at once for a new version.
Each card names the agent and the model. Cards live in the `intake` folder of the
core state; one file a day (UTC) lists the class changes, the "would pick" list
(ready cards, issues that unblock others first, then the oldest) and the issues
that the core really started. Shadow cards never write to GitHub and never change
which issue starts. A failure skips only that issue or that tick. After a switch to
`--intake off`, the next tick stops card jobs that still run; so do a core tick in
mode off and `pdd autopilot stop`. Trust lookups are cached for 6 hours, with at
most 40 a tick. The cards cover every
open issue in scope: unlike the core, they do not skip issues that cool down after a
no-result or whose blocker is named only in the text. `pdd autopilot intake` prints
the cards and today's changes; `--json` prints them as JSON.


## Post-merge audit settings

`pdd autopilot audit RUN PR` audits one merge of a saved workflow run. Autopilot does not
call it by itself: the core engine starts no audit after its merges. Its fixed
brief requires before/after reproduction, scope, Story quality, old-code tests,
real check evidence, unchanged checks and actual merge gates. Audit files remain
in shared durable custody under the machine workflow state root, keyed by
repository, run attempt, PR and merge commit. The run's `audits/` folder holds
evidence copies. Every clone reads shared results and effect reservations under
the repository lock. An interrupted auditor is unknown, never a pass.

Set `autopilot.audit` to `false` in this repository's `pdd.json` to disable audits.
The default is on. Codex and Claude auditors start a fresh native session using
the run's configured account and model. Unsupported agents remain pending.
Auditor sessions count in the issue cost ledger and the provider's account
limits. Optional `autopilot.auditTokenLimit` sets a nonnegative measured token
cap for this repository's last day; unavailable usage holds a capped audit. A
missing, damaged or full machine run index also holds it because cost coverage
is unknown.
Codex limit reads that are unknown or reached hold without a paid call.

The saved audit keeps `result.verdict` and Boolean `result.revert` separately.
BAD with a revert recommendation creates a unique revert branch and a PR against
the saved base. It never pushes directly to that base or merges the revert. A
revert conflict records an unknown follow-up and alerts for help. BAD without a
revert recommendation keeps the merge and reopens or keeps the original issue
open. One audit comment lists the missing parts from the saved summary and
evidence. It creates no revert PR or follow-up issue. Both BAD forms send one
decision alert that states the auditor's recommendation. When it recommends no
revert, the default choice is to keep the merge and finish the rest. The alert
also offers `git revert -m 1 MERGE_SHA` on a review branch and a PR against the
saved base as the other choice. The same command accepts a merge commit or a
single-parent squash commit. Two CONCERN verdicts of the same category
from distinct PRs create one process issue in the repository. Publication
attempts are saved before sending. An uncertain reopen, comment, PR, process issue or
alert is never blindly repeated after a restart. Audit admission and concern
records share the machine workflow state root by repository identity, including
independent local clones. Every indexed repository record must validate and appear
in run discovery before capped admission. Damaged or unreadable earlier audit
evidence, including an unreadable audit folder, holds before another auditor
launch. Unknown audit costs retain an explicit coverage marker. Separate machines
retain separate local cost ledgers.

## Explain resource bindings

Run `pdd test --explain-bindings STORY` before a check to inspect the local
binding plan. Add `--json` for `pdd.binding-plans.v1` with a `plans` array.
Each plan names the test, Story, executable closure for each step, and every
resource operation. Candidates show exact selection, wrong resource name, wrong
operation, invalid lookup, or a prompt outside the boundary or dependency
closure. Exit 4 means a binding is missing; exit 0 means the local plan has no
missing binding. This command does not establish a service compatibility pass.
It reads no token, sends no request, and saves no batch or queue ticket.

A Story can narrow its executable scope with one dedicated block:

````markdown
```pdd-boundary
prompts/cli.prompt.md
```
````

Use the exact opening and closing fence lines shown above, with blank lines or
file ends beside the block. The block must be at top level, outside every other
fence, list and HTML block. Use only LF or CRLF line ends throughout the Story.
A bare CR, vertical tab, form feed, U+001C–U+001E, NEL (U+0085), U+2028 or U+2029
anywhere in the Story keeps the full closure with reason `unsupported-line-ends`
and the note `boundary not applied: unsupported line ends`. List one
repository-relative prompt path per line,
including the entry and every executable Runtime call target. Paths use letters,
digits, underscores, hyphens, dots and slashes, with no whitespace, blank lines,
empty/dot/parent components, fragments, escapes or Markdown link syntax. Each
listed member adds its resources even when no Runtime call reaches it.

Only this block can narrow the closure. Markdown links, headings and reference
definitions elsewhere never remove an edge. A Story with no block, two blocks,
an invalid path or an unreadable member keeps its full dependency closure,
including context resource requirements. The plan includes a named
`boundary-not-applied` note with the reason. A `Runtime boundary` heading without
a valid block gives `boundary not applied: use the pdd-boundary block`. Unsupported
fences, blocks inside fenced examples and uncertain HTML contexts also keep the
full closure. No partial block is applied.

With a valid block, context outside the boundary keeps its prose in the upload
but omits its Runtime interface. Files on disk do not change. An actual call
outside an applied boundary refuses locally with `binding-boundary-invalid`;
expand the block only if the Story requires that behavior. Several Stories keep
the union of their boundaries and each Story's own plan. Adding a Story cannot
remove another Story's required edge. A Story whose boundary is not applied
prevents interface removal from the combined upload. Workspace permissions still
apply to all required reads.

Fix the smallest named cause: correct the fixture resource/operation key, add
the required binding, or declare the Story boundary. Step overrides replace
same-key scenario bindings. The plan never prints fixture arguments or replies.
If the service refuses an exact fixture selected locally, the result retains
both the service report and `binding_diagnostics` with
`server-binding-disagreement`. Ask the compatibility owner to diagnose selection
before retrying. A local match never replaces a service refusal with a pass.


## Whole-product Simulator

- `pdd simulate --product [--parts PARTS] [--journey JOURNEY] [--max-calls N] [--no-open] [--no-wait]`
- `pdd test --journeys [JOURNEY] [--max-calls N]`

Product mode combines the selected parts' maps and starting data in one upload.
Parts without screens retain their data and planned background operations.
Each part keeps separate screen state. Cross-part navigation and background
operations follow the authored maps and product plan. Shared world/seed files
are optional. Authored project files are unchanged. A product requires at least
one screen and one selected Story/scenario. Select parts with a comma-separated
list. Journey names match complete IDs: J1 does not select J10.

The interpreter must advertise product-parts-v1. Otherwise product setup stops
before upload with an upgrade explanation. Step labels use admitted product
ownership; unnamed operations remain unlabeled. Normal Story sessions keep their
existing behavior. Reopening a product retains its original selection and world;
use --new to deliberately replace it. Unknown requests must be reconciled first.
### Inspect a call cap before paid work

Run `pdd lint STORY --max-calls 25` to inspect a selected cap with 0 AI calls.
The interpreter reports each step's catalog cost and a structural test estimate.
For example, an estimate of 29 calls against cap 25 produces an advisory warning.
The cap stays 25. This does not change paid Check admission or guarantee actual
calls or completion. Resource continuations are not included in the estimate.

Text and `--json` retain source, engine and configured maximum information.
JSON rows expose the server's `call_preflight`; the result exposes
`call_preflight_context` and the separate `call_preflight_requested_cap`.
Unknown analysis stays unknown. Missing or inconsistent source, engine or cap
association cannot support a fit claim. An interpreter without
`lint-call-preflight` support refuses an explicitly selected lint cap before
submission. Ordinary lint without a cap remains available. Local lint does not
accept a call cap. Reading a saved standalone lint never starts a paid check.
