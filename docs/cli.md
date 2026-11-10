# CLI reference

This page lists every command of pdd 0.1.27, as `pdd --help` shows it. A test (`test/docs-commands.test.mjs`) checks that each command form of the help is on this page.

You need the pdd command only for runs with PRs, for `pdd test`, `pdd lint`, `pdd simulate` and `pdd approve`. Install the skills with `npx skills add promptdriven/pdd` (add `-g` for all your projects), and set up a repo with the `pdd-setup` skill in your agent. For simulations that your agent drives, use the Try tools in `pdd mcp`. Then use a PDD skill: `pdd-feature`, `pdd-bug`, `pdd-small-change` or `pdd-prompting`. Call a skill with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code (or ask for it by name). See [Install](USAGE.md#2-install).

Typing `pdd check` or `pdd try` runs nothing and prints the name of the command to use.

## Set up a repo

| Command | What it does |
|---|---|
| `pdd setup` | Check for a ready agent, install the ten [PDD skills](USAGE.md#4-the-pdd-skills) when they are missing, and say where. Then add or update the short PDD block (7 lines, between `<!-- pdd:start -->` and `<!-- pdd:end -->`) in `CLAUDE.md` of this folder, else in `AGENTS.md`. If neither exists, make `AGENTS.md`. In a Git repository, add the line `.pdd/` at the end of the root `.gitignore` when no line there is `.pdd`, `.pdd/`, `/.pdd` or `/.pdd/`; `pdd test` keeps its local cache there. Setup only appends: all other bytes stay the same. When the last such line starts with `!`, or no such line exists but a `!` line names `.pdd` or a path in it (such as `!.pdd/config.json`), setup changes nothing and says so. Repeat setup keeps an existing Autopilot mode |

`pdd setup` copies the skills to `~/.agents/skills` (Codex and Gemini) and `~/.claude/skills`, or `$CLAUDE_CONFIG_DIR/skills` when it is an absolute path (Claude Code). If `npx skills` already installed them, it copies nothing. When the skills it finds are older than this pdd, or differ from its skills, it says so and prints the command that updates them: `npx skills add promptdriven/pdd -g -a codex -a claude-code -y`, without `-g` for a copy in the project. After an update of the pdd command, it replaces an older or same-version differing copy with the `.pdd-skill.json` marker, including an invalid marker. It never touches a copy without the marker, or a symlink. When `pdd --version` or `pdd setup` reports older skills, it names each affected skill and its installed version, for example `pdd-autopilot is 0.1.20`. Run `pdd setup` to update copies installed by pdd in user folders. For copies from another installer, use the shown `npx skills add` command. No other pdd command copies skills. The `pdd-setup` skill does the same in a chat. Run it in the top folder of the repo.

Setup previews the exact MCP configuration changes for the Codex, Claude Code and Gemini agents it finds, then asks once (y/N). Only `y` writes those changes, including the approval setting for this Codex server. Registrations pin this running pdd executable, so another installation earlier on PATH cannot receive its tools. Other configuration is preserved. Codex uses `$CODEX_HOME/config.toml` (default `~/.codex/config.toml`) and the `mcp_servers.pdd` entry with `default_tools_approval_mode = "approve"`. Claude Code uses the `mcpServers.pdd` entry in its configuration; Gemini uses `mcpServers.pdd` in `~/.gemini/settings.json` with server trust. Each entry runs `pdd mcp`. A conflicting existing entry is preserved and reported.

Setup also reports the running pdd executable and version, the `pdd` paths in order, and which path and version a plain `pdd` selects. A PATH conflict report includes the absolute command for this pdd and explains that environment activation, such as conda, must come before correcting PATH. It keeps other installations. `--version` preserves its version-only stdout; PATH diagnostics go to stderr. `workflow run` gives a one-line warning when another pdd comes first.

## Repository Autopilot settings

`pdd setup` asks for `off`, `observe` or `auto` once in a Git repository with a terminal. An empty answer selects `off`. It shows the owner and available write-access people, warns when lookup is incomplete, and optionally asks for additional GitHub names. Repeat setup keeps the saved mode and can add names. Without a terminal or outside Git, it asks nothing and saves nothing.

| Command | What it does |
| --- | --- |
| `pdd autopilot off` | Save mode `off` |
| `pdd autopilot observe` | Save mode `observe` |
| `pdd autopilot auto` | Save mode `auto` |
| `pdd autopilot trust NAME...` | Add one or more explicitly trusted GitHub names |
| `pdd autopilot untrust NAME` | Remove one explicitly trusted GitHub name |
| `pdd autopilot release ISSUE` | Release this machine's claim and remove `pdd:working` and `pdd:stuck`; keep the run folder, branch and PRs |

Settings live in the repository's `pdd.json`, for example `{"autopilot":{"mode":"off","trust":[]}}`. Other settings are preserved. Autopilot workers start from the default branch on GitHub and read `pdd.json` there, not your local copy. So `pdd autopilot off`, `observe`, `auto`, `trust` and `untrust` also update `pdd.json` on the default branch, through the GitHub API with your `gh` sign-in. Each command makes only its own change on GitHub: a mode command sets `autopilot.mode`, `trust` adds its names to `autopilot.trust`, and `untrust` removes its name. All other keys and fields keep the GitHub values, also when your checkout is behind. The commit message says what changed, and the commit changes only those bytes of `pdd.json`: the indent and the key order of the file stay. They do not touch your current branch or your uncommitted work. More lines tell the result:

- GitHub is already up to date.
- The commit URL, then `pdd.json on GitHub is updated. To update your local copy, run git restore pdd.json, then git pull.` `git restore pdd.json` drops your local change of `pdd.json`, which GitHub now has. Run `git pull` on the default branch.
- When the default branch accepts changes only through a PR: the URL of a PR from a `pdd/autopilot-settings-…` branch, which you must merge before workers use the new setting. While that PR is open, the next command adds its change to the same PR. When the new setting is the same as on the default branch, pdd closes the PR with a short comment.
- When the copy on GitHub then has other settings than your checkout, one more line shows both.

When another change of `pdd.json` on GitHub comes between pdd's read and its write, pdd reads the file again and tries once more. When GitHub cannot be reached or `gh` is not signed in, the local setting stays, the exit code is 0, and the line tells you to run the same command again. `pdd autopilot start` and `pdd autopilot status` print a warning when the copy on GitHub has another mode or trust list, with the commands that change it, or when a settings PR is still open, with its URL. `pdd setup` saves a first mode only in your checkout and never writes to GitHub; it prints the command that puts the mode there. Invalid saved modes count as `off` with a notice; setup leaves them unchanged, and a mode command replaces them. Names match ignoring case. The repository owner, people with write access (including access through an organization team), and explicitly added names are trusted independently. An incomplete lookup never establishes trust for an unknown person.

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

## Autopilot on this machine

`pdd autopilot doctor` checks the pdd selected by PATH, Node 22.20 or newer,
Git, gh sign-in, write access, merge methods and effective branch rules, agent
sign-in and read-only usage, Herdr and pane room, setup instructions and skills,
mode and trust, draft prompts, authenticated interpreter capacity access, and the
platform's user scheduler. Linux lingering and macOS sleep are advisory.
Codex usage uses a read-only account request. Claude usage remains unproved;
run `claude` and `/usage` to inspect it. No agent prompt is sent.
Unreadable branch rules are advisory; repository reviews and checks still apply.
Each line includes a repair or inspection command. PATH repairs name this
installation, including source checkouts. A required failure refuses start with
the same report before state files, locks, timers, panes or claims change.
Draft and unreadable prompt paths are warnings. Doctor never approves them.
A successful interpreter access read sends no source and proves no prompt behavior.
See [the first-start path](../README.md#autopilot-on-your-own-repository).

Doctor uses the saved coordinator profile on restart.
A selected agent's HOME, CODEX_HOME, CLAUDE_CONFIG_DIR and other environment
settings apply to its checks. Repair commands carry that profile environment.
A malformed agents.json report names the file to edit. An invalid
PDD_RUNTIME_URL report gives the HTTPS-origin or unset repair.
Pane pressure, unreadable capacity, interpreter health and agent usage limits
are warnings with fix commands. They never refuse start at preflight. Start can
sweep, park and wait. It must still prove room through guarded cleanup and admission,
including cleanup of a finished run shell after its chats have closed.
Doctor closes no panes. A reused coordinator needs no extra pane.
Doctor verifies that coordinator in `pdd-autopilot`. A full `pdd` workflow
session does not block reuse. Fresh allocation uses the native workflow pane
admission rules. Unavailable saved-target evidence defers to guarded recovery.
Interpreter readiness uses the runtime client's health check, including a JSON
404 from an interpreter without the optional capacity endpoint.

Run Autopilot commands inside the repo folder. Each repo has its own Autopilot on each machine.

| Command | What it does |
|---|---|
| `pdd autopilot doctor` | Read-only prerequisite checks, one line and a command per item. No GitHub writes or AI calls. Exit 1 for a required failure, 0 when only warnings remain |
| `pdd autopilot start [--runs N] [--checks N] [--resume-custody FILE]` | Check sign-ins and the running pdd version, open a dedicated interactive Herdr session and check for work immediately. A user timer checks again every 30 minutes. `--runs` overrides the open-run cap. `--checks` overrides heavy-check slots. Omission uses machine capacity. `--resume-custody` supplies the verified original-owner projection for explicit recovery |
| `pdd autopilot stop` | Disable this repo's timer on this machine and let the current agent step finish |
| `pdd autopilot audit RUN PR` | Audit a confirmed automatic merge once with a fresh configured agent. Save OK, CONCERN or BAD and the separate revert recommendation with the run. Post the evidence once on the issue. BAD opens a revert PR only when recommended; otherwise it keeps the merge and reopens the issue with the missing parts. One decision alert states the recommendation and choices. Unknown external outcomes require inspection before any retry. |
| `pdd autopilot check-base RUN PR` | Read the saved run and exact PR target, then check that its base contains the current default branch and newest published release tag, including prereleases. A refusal explains the reason and exits 1. Use this before an automatic merge and after it for the base audit. It makes no GitHub writes |
| `pdd autopilot status [--all] [--json]` | Show this machine's repo, the folder Autopilot works in, selected base, agent, timer, coordinator health and next tick without waking an agent; an idle coordinator is healthy. It reads `pdd.json` on GitHub only to warn when its Autopilot settings differ from this checkout. Another line says when pdd workflows cannot start in this folder, and why. Other lines show a pending or held coordinator relaunch an [alert](#alerts) that was not delivered, and the [GitHub calls](#github-api-budget) of the last hour. `--all` works from any folder and lists every repository with Autopilot on this machine: repository, folder, mode, enabled or disabled, timer and coordinator state. It reads only local files, the timer and Herdr: no GitHub call |
| `pdd autopilot add N...` | Label named issues `pdd:autopilot`. Autopilot does not need this label: it considers every open issue |
| `pdd autopilot report` | List this machine's local Autopilot report drafts ([core engine](#core-engine)). No GitHub call |
| `pdd autopilot report send FINGERPRINT` | File one local report draft to promptdriven/pdd, or count it on the matching open report |
| `pdd autopilot alerts set [--destination autopilot\|infrastructure]` | Read your Discord or Slack incoming webhook URL from stdin and save it for this machine |
| `pdd autopilot alerts set --discord-channel ID [--token-command CMD] [--destination autopilot\|infrastructure]` | Use a Discord bot in one channel: read its token from stdin, or save CMD and run it at each send to get the token |
| `pdd autopilot alerts test [--destination autopilot\|infrastructure]` | Send one test message and confirm that it was posted; for a bot, first check and show the bot name and channel name |
| `pdd autopilot alerts clear [--destination autopilot\|infrastructure]` | Remove the alert destination from this machine |
| `pdd autopilot alert --issue N --kind usage-limit\|resource\|interpreter\|interpreter-access\|access\|decision\|stuck\|test-suite\|long-running\|recovered --input - [--update]` | For the coordinator: record one alert and send it to this machine's destination |

Outside a Git repository, `start`, `stop`, `status`, `add`, `off`, `observe`,
`auto`, `trust` and `untrust` stop with exit code 1 and say: `This folder is not a
Git repository. cd into the repo you want Autopilot to work on, then run the
command again.` A successful start says which repository and folder it works
in, for example `Autopilot started for OWNER/NAME in /path/to/checkout.`

Before start turns on the timer or opens a chat, it checks that `pdd workflow
run` can make an issue worktree in this checkout. The workflow worktree allocator
makes this decision, so Autopilot accepts the same Git layouts and the same
`origin` forms as `pdd workflow run`. The check reads Git only: no AI, no GitHub
call, no claim and no worktree. When the checkout cannot make issue worktrees, for
example because its `origin` remote names another repository or Git keeps its
files in a separate Git directory, start stops with exit code 1. The message names
the folder, the cause and the next step: run Autopilot from a normal clone of the
repository. When Git could not be read, the message says so and tells you to try
again. Start then changes no timer, also not the timers of other checkouts, and
claims no issue.

A tick makes the same check before it offers new issue work. Issues with
`pdd:stuck` or `pdd:code-pending` are not new work. While the check fails, the
tick offers no new issue, writes a warning to the timer log and keeps those issues
for a later tick. It still delivers the start-up recipe, dependency review, time
rules, the work of existing claims, and reviews and trusted comments on claimed
and held issues.

Starting Autopilot again keeps this machine's repository claim owner when it
replaces the coordinator chat. Open runs keep their heartbeats after a crash or
machine restart. A tick can also recover an unfinished local run whose claim
still names an earlier coordinator. The run folder, checkout, machine, claim
comment and label event must match. Another machine's claim always wins.
A claim that expired after a coordinator change can recover once. The tick
updates the run's custody, posts one short issue comment and resumes heartbeats.
Then `pdd workflow done` can publish finished work under its usual ownership
checks. Recovery makes no AI call and does not approve a prompt or a gate.

In `status --all`, each line is independent. A saved folder that is gone still
shows its real timer and coordinator state, with `mode unknown (folder missing)`.
A saved folder that is not a Git repository shows `mode unknown (not a Git
repository)`. A timer that cannot be read shows `timer unknown`, and a broken
state file shows `FILE: saved state unreadable`. One bad line changes no other
line.

The launcher uses the repository settings module to read root `pdd.json`. An
active mode is `observe` or `auto`; missing or invalid settings count as `off`. It uses an
installed, signed-in Codex, Claude Code, agy or Gemini agent. Missing dependencies
get one actionable line. Linux uses a systemd user timer; macOS uses a
LaunchAgent. On Linux, start warns when user-session lingering is off or
unavailable: `loginctl enable-linger` keeps the timer after logout. The tick
service preserves a Herdr server it starts when the tick exits. See the chat with
`herdr session attach pdd-autopilot`. The coordinator chat starts with a `cd` to the
repository, so a `cd` in your shell startup file (for example `~/.zshrc`) does not
change where the agent works.

A Codex coordinator also gets
`-c shell_environment_policy.set.PDD_AUTOPILOT_CONTEXT=…` for this launch only, so
the commands of its chat keep the Autopilot start context when the Codex profile
sets `inherit = "core"` or `"none"`. When Autopilot started with an explicit
`CODEX_HOME`, the chat also gets `-c shell_environment_policy.set.CODEX_HOME=…`,
so a `pdd workflow run` from the chat keeps that Codex profile. Autopilot does not
change Codex settings. Limit: a `shell_environment_policy.include_only` list that
leaves out one of these names still removes it.

The first start of a repo on this machine selects the agent. It tries the agent of
the session that runs the command first: Claude Code when you run it from Claude
Code, Codex when you run it from Codex. Then it tries Codex, Claude Code, agy and
Gemini, in that order, and takes the first one that is signed in. This check makes
no model call. Later starts on this machine keep that agent, also after
`pdd autopilot stop`. To select Codex, sign in to Codex and run the first
`pdd autopilot start` from Codex or from a plain terminal. From a Claude Code
session, run `env -u CLAUDECODE pdd autopilot start`.

A coordinator chat keeps the launch settings that it started with. Autopilot
saves a fingerprint of the pdd package and the launch arguments with each
coordinator launch. When a start or tick finds a chat with another or no
fingerprint, for example after you install a newer pdd, it ends that chat
when the chat is idle or done and starts a fresh chat with the current
settings. The coordinator identity stays the same, so claims, saved runs and
progress do not change. A busy chat is not interrupted: its work stays pending,
and `pdd autopilot status` shows `Coordinator relaunch pending after upgrade`
until the relaunch is done. Autopilot relaunches for the same settings only
once. If the settings change again, for example when starts from two pdd
installs alternate, the current chat stays and gets work, and status shows
`Coordinator relaunch held`. Close the coordinator pane in Herdr to start a
fresh chat with the current settings.

Autopilot saves the Herdr terminal of each coordinator chat. When the saved
pane is gone, for example after a failed relaunch, a closed pane or a Herdr
server restart, the next tick opens a fresh pane for the same coordinator and
delivers the pending work there. After `pdd autopilot stop`, also during a
relaunch, the next `pdd autopilot start` does this. A pane that now has the old
pane ID but another terminal gets no prompt, no close and no launch.

In auto mode, each tick checks the saved run agents in Herdr without an AI call.
A resumed run gets one continue request through the same delivery route as
`pdd workflow changes`. The request points to its current step brief and STEP.md.
An unfinished run whose agent stays idle gets a continue request after 10 idle
minutes. Requests are at least 10 minutes apart. After three attempts in one area
without recorded step progress, another idle interval marks the run stuck and
sends one alert. A recorded step change resets that area's allowance. A working
agent alone does not reset it. Gates, questions, deliberate chat closure, login
failures and usage limits keep their holds. Observe and off modes send no nudges.
Workflow status shows `agent idle since HH:MM` for an idle unfinished run, with
the configured status time zone or UTC. Status reads send no request.

A tick checks GitHub with ETags and wakes the coordinator only for a repo's first
start-up recipe or an unseen trusted issue, comment or related PR change.
Already-seen issues stay quiet across unchanged ticks, including stuck,
code-pending, claimed and observe-mode issues waiting for a person. Busy coordinators
receive no tick prompt; pending changes are coalesced until they are idle.
Empty ticks use no AI. This applies to Claude
Code too: the user timer keeps empty ticks out of the conversation. Paginated
queues revalidate every cached page; changed candidates may require comment and
write-permission lookups. GitHub rate limits wait until the reset time. When the
open issue list has more than one page, the tick reads it in full every 6 hours.
Between, it reads only the issues and PRs that changed since that full read
(`since=`), so an unchanged list costs no counted call.

Every open issue can enter the queue, old or new, with or without `pdd:autopilot`.
Autopilot starts fresh work only on an issue that the current dependency review
lists as eligible. That review checks dependencies, trust, the GitHub Assignees
field and the `pdd:working` claim; a missing result waits. On an outsider's issue,
a static reply says "thanks, a maintainer will look" until a trusted person comments.
The agent receives only trusted people's text, including comments. Owners, people with write access and configured trusted
names count as trusted. The `pdd-autopilot` skill owns the start-up recipe,
`pdd:working` claim and one comment across machines, capacity and progress
tracking. Only Autopilot uses `pdd:working`; a person or a manual session assigns
a person instead. Each tick writes a `lastSeen` time into its own claim comments
without an AI call; that edit is the heartbeat. A new claim record has
`"lastSeen": ""`. A claim record with a top-level `lastSeen` and no GitHub edit
for 4 hours (counted from its creation until the first heartbeat) is expired. A
claim record without `lastSeen`, as older pdd writes it, a claim without a claim
record, or a bare label is expired after 24 hours with no issue activity. For an
expired claim, `pdd graph` shows "Expired claim, last seen" and another
coordinator may take it over. The last-seen time is only the claim comment's GitHub edit or creation
time; the recorded `lastSeen` value never extends a claim. In `off` mode a tick
does nothing on this machine: it releases no claim and writes no `lastSeen`, so the claims expire after 4 hours, as
on a stopped machine; their runs then cannot open or update a PR. After 4
hours stuck, the owner tries a changed approach or asks for help, and the claim then expires. After a ceiling (the repair limit or the takeover limit), the owner does not retry and sends no second alert. After 3 takeovers of one issue, its expired claim is not taken over again: `pdd graph` shows "Taken over 3 times", a 4th start is refused, and the tick asks one coordinator once to take the stuck path. A takeover is the removal of an expired `pdd:working` whose remover adds the label again within 10 minutes for another coordinator or machine. A coordinator that takes back its own expired claim (same coordinator ID and machine) makes no takeover. To let Autopilot continue after the takeover limit, a person removes `pdd:stuck`: this resets the count. A normal release, or a person's removal of an expired `pdd:working`, also starts the count again. When people and coordinators share one GitHub login, pdd cannot tell them apart: a person's cleanup of an expired `pdd:working` followed by an Autopilot claim within 10 minutes counts as a takeover. Removing `pdd:stuck` at the limit always resets the count. 24 hours after the claim with no merge, the tick asks the owner once for an informational alert and records it in the claim comment, so that no machine sends it again; work continues. Related PRs are associated through same-repository closing references;
trusted PR discussion comments and state transitions can wake waiting work once.
Claimed issues stay identified as claimed when a trusted change needs attention.
`add` rejects foreign repository references before writing any labels. Status
reports unavailable Herdr instead of claiming a healthy running session. Stop
leaves the interactive session open.

Upgrade all coordinators of one repository at the same time, when no run is in
the middle of a step. Older pdd sends no heartbeat, so its claims follow the
24-hour rule until their owner upgrades. It still pushes at its last `done`
without a claim check and removes `pdd:working` when its run ends. A stopped
launcher or `off` mode lets its claims expire after 4 hours. The heartbeat moves
claimed issues to the top of "recently updated" every 30 minutes.

## Machine and account health

Each no-AI tick checks available memory and free disk on the checkout volume.
Available memory must be at least 10% of total. Disk must have at least 1 GiB
and 5% free. The shared machine observation port also supplies CPU count, load
and Linux pressure for validation retries and machine-sized checks.
Validation retries reuse the tick's checkout observation. They also check load,
pressure, required tools and suite capacity before offering a retry.

For the saved Codex profile, the tick starts a short app-server connection and
uses only `initialize`, `initialized` and `account/rateLimits/read`. This makes
no model call. It reads usage and the ordinary reset time. It does not spend,
request credits, consume a usage reset, change sign-in or log out an account.
Other agent kinds have no Codex usage check.
Malformed protocol frames stop the connection and report unknown usage.
The read waits at most one second for cleanup after selecting its result.
It sends SIGTERM first and sends SIGKILL after 500 milliseconds if the direct
child has not exited. If close has not arrived after another 500 milliseconds,
it releases the connection's streams and process handle and returns the selected
result. A descendant holding an inherited pipe cannot block the health read.

Low resources, reached usage limits and unreadable health observations pause new
automatic admissions. Claims, progress and heartbeats remain. One `resource` or
`usage-limit` incident covers the affected issues on this repository and machine.
The alert includes a known reset time. A later healthy read sends one recovery
and wakes the coordinator. A busy coordinator keeps that wake pending. Passing
the saved reset time alone does not establish recovery.

`pdd autopilot status` and `status --all` show the saved Health line and observation
time. Status does not probe an account or the machine. Before any observation,
health is unknown. If no issue can own an alert, health stays visible and the
next tick attaches the incident when an issue is known.

When the GitHub budget permits reads, the tick removes an ended run's worktree only after a read-only PR lookup shows
its branch closed or merged. It verifies allocator identity, a clean worktree,
and a branch equal to its tracked upstream. Dirty, unpushed, active, waiting,
locked and unverifiable worktrees stay. It does not delete branches or run
records. Cleanup makes no push or fetch. A cleanup failure keeps the worktree.

## GitHub API budget

Autopilot uses your own `gh` sign-in, so its GitHub calls use your hourly limit
(5,000 REST calls for a person). pdd counts each `gh` call of the Autopilot tick,
and of `pdd` commands in a repository where Autopilot runs on this machine, with
its purpose and the limit that GitHub reports in the reply headers:

| Purpose | Calls |
|---|---|
| `dependencies` | The dependency re-sync: open issues, comments, links, history |
| `claims` | Claim checks and the `lastSeen` heartbeat |
| `issues` | The tick's issue list, comments and permission lookups |
| `pulls` | PR, review and check reads |
| `writes` | Other writes, such as a PR or a reply |
| `setup` | Sign-in, repository and settings calls |
| `other` | Everything else, such as `pdd metrics` |

pdd does not count the `gh` calls that the coordinator and worker chats make
themselves, such as `gh pr checks` or `gh run watch`. It also does not count
other machines or your own work on the same login. All of them use the same
limit. Their use shows only in the limit that is left on the status line.

The counts stay on this machine, one file for each repository in
`~/.local/state/pdd/autopilot/github/`. `pdd autopilot status` shows one line
when there was a call in the last hour, for example:

```text
GitHub calls in the last hour: 212 (dependencies 120, claims 14, issues 60, pulls 18); 150 of 190 conditional reads were 304 (79%); REST limit 4210 of 5000 left until 17:05Z; budget normal: Autopilot on this machine used 61 of 1500 (30%).
```

"Autopilot on this machine used 61" is the counted calls of this machine: the
tick and the counted `pdd` commands, not the chats.

A conditional read sends the ETag of the last reply. A `304` reply means that
nothing changed, and GitHub does not count it against the limit. The tick, the
dependency re-sync, `pdd dependencies prepare` and `complete` and the workflow
claim checks use conditional reads for an Autopilot repository. They share one
file of ETags and reply bodies in the same folder. A full page (100 items) that
has no next page is read without its ETag: a `304` reply does not show that a
next page came.

Autopilot keeps one saved dependency snapshot for each repository in the same
folder (`*.snapshot.json`, private to you). The tick, `pdd dependencies complete`
and the claim scan use it. A read asks GitHub only for the issues that changed
since the last read (`since`, in update order), and reads the comments, links and
history of an issue again when its update time, comment count or link identities
changed. It checks the open index with conditional requests and compares native
link identities in batches. Equal link counts can still mean different blockers.
Incomplete batch connections fall back to complete REST link pages. Once a day
it rebuilds the open list, so a deleted or moved issue leaves it. Safety reads always ask GitHub (a `304` is fine): the claim
checks before a start, a push and a merge, heartbeats, trust, and the readback
after each write. A quiet tick then makes a few calls instead of hundreds, and
a batch reuses the same observations. After `pdd dependencies complete`, the next
request comes from the saved snapshot: the completion tick and the idle wake
reuse the dependency issue list for 10 minutes after its last complete read.

The budget acts on the tick, and its floor on the dependency commands too. It
has two settings in `pdd.json`, a share (default 30%) and a floor (default 1,000
calls):

```json
{"autopilot":{"mode":"auto","trust":[],"github":{"share":30,"floor":1000}}}
```

`share` is a whole percent from 1 to 100; `floor` is a whole number of calls. A
missing or invalid value uses the default.

- **Low.** The counted REST calls of all Autopilot repositories on this machine
  in the last hour reach the share. A 304 reply does not count. Then the tick
  runs the dependency re-sync at most once an hour and uses its last result
  between. All other calls of the tick go on: the issue list, comment, review
  and PR reads, heartbeats and wakes.
- **Reserve.** GitHub reports fewer calls left than the floor, for REST or
  GraphQL. Then the tick makes no GitHub call until the reset time, except the
  heartbeat of each live claim of this machine (2 REST calls each). So a claim
  does not expire while its chat works. With fewer REST calls left than these
  heartbeats need, it sends none. The tick also wakes no chat with new work
  until the reset. Native dependency observations for an Autopilot repository
  also stop non-safety reads. This includes `pdd dependencies prepare`,
  `complete`, direct snapshot reads and automatic workflow start. A reply that
  shows fewer calls than the floor stops the reads
  after it. A stopped `complete` keeps its request and analysis; the first tick
  after the reset saves the remaining reviews without a new analysis. Reviews
  that were already saved are never saved twice.

The coordinator and worker chats go on, and their own `gh` calls are not counted.
Safety reads, including workflow start's live subject and claim checks, trust,
permissions and write readbacks, can use the reserve. Writes can use it too.
Other `pdd` operations are counted but do not wait for this floor. The budget
does not keep 70% of the limit for you. The floor makes the tick and native
dependency observations read less. To
give Autopilot a limit of its own, see the design note
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

The coordinator alerts only for a real need: an AI account usage limit (with the
reset time when known), a CPU, memory or disk failure, an access or spending
decision, an unresolved product choice, or an issue stuck after its retry time.
It also sends one informational `long-running` alert when an issue was claimed 24
hours ago and has no merge yet; work goes on. It gives the cause, what it tried and what it needs as JSON on stdin:

```sh
pdd autopilot alert --issue 12 --kind usage-limit --input - <<'PDD_ALERT'
{"cause":"Codex usage limit; resets 2026-11-06T18:00Z","tried":"Paused issue 12 and continued other work","need":"More quota or another signed-in account"}
PDD_ALERT
```

Each message names the repository, the issue link, the cause, what Autopilot tried
and what it needs. Answer on the GitHub issue, so the answer stays with the run.
A usage limit, a resource failure, an interpreter outage or an interpreter access problem
(`interpreter-access`: this machine cannot read the interpreter health check) is one incident for the
repository and machine, so a limit that blocks 5 runs sends one alert. A call for another
blocked issue adds that issue to the incident and sends nothing. The machine is
the name that Autopilot saved at its first start (this checkout's start first),
else the host name, so a host rename does not open a new incident. An access or spending decision, a product
decision, a stuck issue or a long-running issue is one incident per issue. A repeat call sends
nothing for a delivered or unconfirmed alert, and sends again an alert that
failed or had no destination. `--update` sends a new cause, a changed decision needed or the new
issue list. Changing only what was tried sends nothing. Keep cause and need
stable during a review with no new facts. A 4-hour stuck review alone sends no
new message. `--kind recovered` sends one recovery and closes the matching
alerts; give `"kind"` in the JSON to close only that incident. Every call and
its delivery result are recorded in
`~/.local/state/pdd/autopilot/alerts/`. Without a destination, the alert stays in
that record. `pdd autopilot status` adds one line when an alert was not delivered.
Work continues in both cases. A delivered `pdd autopilot alerts test` ends that
line for an older failed send, such as a failed recovery. An open alert that was
not delivered stays in the line until a later call sends it.

The native tick sends one short digest per repository and machine at most every
6 hours, only while open work exists. It lists stuck issues and their causes,
parked automatic runs, and decisions waiting for a person. It reads saved runs
across parallel worktrees. It does not wake an agent or approve work. The last
digest attempt is saved across restarts. Failed or unconfirmed digest attempts
also wait 6 hours, so a delivery problem cannot cause a burst of digests. Other
work continues when delivery fails. Each repository's alert record has a shared
lock, so parallel runs cannot overwrite incidents or send concurrent digests.

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
use the ordinary destination. Issue decisions, stuck alerts and digests use the
Autopilot destination. Status identifies the failing destination; a test clears
only that route's older delivery failure. An open undelivered incident still
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
| `pdd workflow evidence-associate ISSUE --workspace PATH --stage current\|pr1 --test PATH...` | Register the producer workspace, evidence stage and selected tests for this run. Run it from the owned run worktree. Give one or more test paths after `--test`. Registration runs no checks and changes no workflow progress. See the [association contract](../prompts/cli/workflow-runner.prompt.md#workspace-evidence-association) |
| `pdd workflow view ISSUE` | Read-only review of the saved state, current gate, recorded approvals, pending decisions, PRs, check reports, Simulator links and current gate files. Never starts or resumes a chat, approves, or refreshes external state |
| `pdd workflow open ISSUE [AREA] [--new] [--model MODEL] [--herdr-agent-name NAME] [--codex-threads N]` | Focus or resume the current chat, or the saved chat of a recorded earlier AREA. A chat that is still starting gets up to 30 seconds to show its agent; pdd sends no second launch or resume meanwhile, and then says "starting, not confirmed". `--new` closes and archives the current area's owned chat and starts one fresh session with the same run and agent setup, keeping progress and approvals. For a two-PR run in code, selecting `prompt-pr` or `story` returns work to the open PR 1 branch and clears old code checks. `--new` can replace that returned chat. Other earlier-area replacement and requests to replace a chat from an agent session or the pane being closed refuse. Repeat `--new` to resolve a pending replacement; status names its phase and resolving command, and cancel remains available |
| `pdd workflow card [ISSUE]` | Print the run's Story card from its real files: the issue and what the reporter asked, the verdict line, each Story's acceptance criteria, what must not change and rules to check, the test cases (case, input, expected), the prompts that change with their changed lines, the full paths and the next step. After the Story approval it also shows what changed since then. Read-only: no GitHub, Herdr or interpreter call |
| `pdd workflow approve [ISSUE] [--said WORDS] [--draft] [--model MODEL] [--herdr-agent-name NAME] [--codex-threads N]` | Approve the ready gate and its draft prompts together with your chat words. In a normal run, `--through prompt-pr\|code` records the code-or-stop choice from the Story card. Without ISSUE, select the current worktree or sole waiting run. Without --said use person terminal y/N; agent callers must ask then use --said. Strict mode requires a person terminal. |
| `pdd workflow resend ISSUE... [--said WORDS]` | Record one person decision and resend each lost check once. `--said -` reads exact words from stdin. Strict mode requires a person terminal. |
| `pdd workflow changes ISSUE TEXT` | Send the text to the same chat. The chat revises. The gate stays open. Also use it to answer a question that the chat asked. At a gate, a plain approval such as "I approve" is not sent: pdd tells you to run `pdd workflow approve ISSUE` |
| `pdd workflow tidy [--dry-run]` | Close safely finished chat tabs across runs on this machine. `--dry-run` lists the eligible count without changes. Keep the current chat of each live run, busy chats and chats whose pane identity cannot be verified. A finished chat without a native session requires a saved screen. Show retained counts by reason. |
| `pdd workflow cancel ISSUE` | Close the run's chat tabs. Keep the worktree and the branch. A new `pdd workflow run` on the issue then starts fresh |

Finished chats close after a 15-minute grace period when they are idle and have
a saved native session or a saved screen. Each new start and each Autopilot tick tries cleanup.
`pdd workflow tidy` also retries cleanup. It refreshes restart terminal IDs for matching area tabs and the saved run shell, with confirmed agent absence and idle foreground shells. Done runs release their workspace after verified chat cleanup. Workspace closure requires a saved creation record for that exact workspace. If the creation field is missing, pdd can save it only when the workspace has the run worktree path, clone identity and run label. Other workspaces remain open with a cleanup reason. Saved native sessions, run folders and Git worktrees remain available. Missing or foreign workspaces stay protected. List status suggests tidy only when its read-only eligibility check finds a chat it can close. Status shows pane counts for working, parked, done and unowned panes. It warns at 90 percent of the configured pane budget and lists unowned workspaces with commands for manual closure. These observations do not authorize automatic closure. Status and view close nothing. A manual
start on a completed issue keeps its history and starts a fresh run. A replaced
run remains discoverable from its retained worktree; its agent sees the old and
replacement run IDs and must stop. Run `pdd workflow cancel ISSUE` from that old
worktree to close a retained busy chat.

`PDD_HERDR_PANE_BUDGET` sets the session `pdd` pane budget (default `56`; `0`
disables it). The count includes personal panes. Before making a new run, pdd
checks capacity and can close safely finished chats without the grace period.
If there is no room, `herdr_pane_budget` reports the count, required capacity and retained counts by reason;
no new branch or worktree is made. Autopilot holds fresh work with reason `panes`
and checks again on its next tick. Raise the budget or close unused tabs.

For an ended run, `pdd workflow open ISSUE [AREA]` prints saved screen paths and
native resume commands with its saved account folder. It changes nothing in
Herdr. For a live run it can resume a closed historical chat immediately.
Screens are private files in the run folder's `chats` directory.

`pdd workflow open ISSUE` focuses or resumes the current area chat of a live run. If its Herdr workspace was closed, status says so and gives this command. Both ordinary open and `--new` rebuild that workspace and area tab from the verified saved worktree. A live saved layout workspace ID that belongs to another checkout or repository stops recovery, even when a matching workspace exists. A saved ID absent from live inventory permits recovery. They resume the saved native session when available, or start a fresh chat with the area start message when no saved session can be resumed. A later `--new` on the open workspace starts a fresh session as usual. After a Herdr restart, matching tabs and panes keep their identity and pdd saves their new terminal IDs. If the root layout changed, pdd rebuilds the verified workspace when no live or unconfirmed chat can be lost. A live chat or unavailable inspection keeps the workspace intact. PDD saves the returned shell IDs with new workspace creation evidence before another allocation. A saved close intent stays bound to its original shell IDs on every retry. A missing worktree folder must be restored first. No new Git worktree is made.

A run saves one launch profile: agent kind, account folder, model, Herdr name prefix and Codex thread limit. Use `--model MODEL` at start to keep the same model across areas, resumes and account changes. Omission uses the account's model default. To change the model for the next fresh chat and later areas, use `pdd workflow open ISSUE --new --model MODEL`. Model, name and thread options on open require `--new` for the current area. The agent kind and agents.json command stay the same.

`--herdr-agent-name NAME` sets a name prefix of 1 to 25 lowercase letters, digits, underscores or dashes, starting with a letter. PDD appends an area suffix. Omission gives a stable name derived from the run identity. PDD binds Codex and Claude names only after it verifies the detected native session. A resumed Codex chat, including one in a rebuilt workspace, uses its saved UUID and original session time in the saved account for this check. A saved default account uses `~/.codex` for native evidence, even when the observing terminal has another `CODEX_HOME`. A naming failure shows a warning and keeps the chat's live state. Gemini and agy lack this native ownership proof, so their names stay unbound with a warning. Detailed status shows the saved name and pane. JSON status includes `launchProfile` and `chat: {herdrAgentName, paneId}`. Use `herdr --session pdd agent get NAME` to inspect it. Use `herdr --session pdd agent send-keys NAME ctrl-c` to interrupt its work through the terminal, then send the agent's normal exit command when it is ready. `pdd workflow cancel ISSUE` ends the run and closes its tabs.

`--codex-threads N` selects a whole number from 4 through 8 for Codex chats. For example, 5 allows the main thread and four helpers. PDD passes the effective limit only to this chat. A higher positive limit in the selected account's `config.toml` is kept and shown in status. Missing files keep the requested limit; malformed configuration refuses before closing a chat. New Codex runs default to 5, while runs without a saved thread setting keep the account default. Other agents reject this option. This setting cannot prove that a required check can start. If a fresh checker cannot start, report `Not checked: STEP (agent limit)`; keep the builder separate from checkers and always use a fresh reviewer.

Saved Autopilot chats check current claim ownership before open, replacement,
automatic resume or parked wake. If another machine owns the active claim, PDD
marks the local run as handed over and closes its identified local chats. The
worktree, branch and completed work stay available. The other machine's claim
stays unchanged. Unavailable or uncertain ownership refuses continuation and
keeps the saved run. A handover with unconfirmed cleanup lists the retained panes;
use `pdd workflow tidy` to retry safe cleanup.

To fix a prompt after code review, commit or keep the current code edits so the worktree is clean. Run `pdd workflow open ISSUE prompt-pr` (or `story`). PR 1 must still be open. PDD fast-forwards its owned branch from the remote and merges the fetched current commit of the run's saved base (usually main) into PR 1. Resolve and commit any base merge conflicts on PR 1. Repeating the explicit `open ISSUE prompt-pr` command in returned prompt space integrates a newer base and clears the prompt checks when the head changes. Make the correction on PR 1 and finish the prompt checks with `workflow done`. PDD updates the same PR 1. A changed Story or scenario contract returns to the Story gate for a new decision. PDD compares PR 1 with the contract covered by the last Story decision, including changes fetched during return. Missing approval coverage also returns to that gate. Story coverage includes supported `user_stories` directories at any depth. Additions, edits and deletions require fresh coverage. A reply covers only the Story and cases shown at the gate. If they change, run `workflow done` again to show the gate and obtain a later decision. Prompt-only edits rerun the prompt checks. PDD rechecks the contract and published scenario bytes after code confirmation or an explicit reply and against the exact fetched commit before code entry. PDD merges that pinned commit and checks the resulting code source before saving the code decision. A changed contract reopens Story approval. Unpublished scenario bytes keep the run in prompt space. The normal code-choice gate then resumes the existing code branch and merges the updated PR 1 without rewriting published history. Run code generation and all code checks again. PR 2 contains no prompt edits relative to its fetched PR base. PDD checks the staged tree before its automatic commit and checks the exact candidate commit before pushing that SHA. A concurrent unsafe edit refuses publication and keeps the local work, with advice to return to prompt space. After PR 1 merges, PDD compares prompts with the fetched default or selected topic base. Automatic runs use this same route when review finds a prompt defect. A returned automatic run with current operator delegation, unchanged Story coverage and a full current check pass updates PR 1 and resumes PR 2 without a person question. A later Story approval replaces its earlier coverage before checked continuation. The run keeps both PR identities and its claim. Strict approvals and changed Story gates still apply. Normal runs keep the Story card and its saved code-or-stop choice.

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
- When your environment has no login variable, the chat gets none and uses the login in its config folder. An example is an Autopilot Codex coordinator with `shell_environment_policy.inherit = "core"`. The Gemini start check runs only `gemini --version`, so it does not show whether that login works.
- The first message of each chat gives the full path of this pdd. The agent uses it, so another `pdd` on its PATH does not matter.
- A Codex chat also gets `-c shell_environment_policy.set.PDD_BIN=…` and `-c shell_environment_policy.set.PDD_AGENT_SESSION="1"` for this launch only, so its commands keep both values when the Codex profile sets `inherit = "core"` or `"none"`. pdd does not change Codex settings. Limit: a `shell_environment_policy.include_only` list that leaves out a name still removes it.
- Workflow chats have no overall time limit. `pdd workflow prove` limits each phase to 10 minutes by default; remote lint has a caller wait limit. You can close the workflow-start terminal at any time.
The pdd CLI has no merge command. In manual workflows, ask your agent to merge under [RUNBOOK §2](../RUNBOOK.md#2-the-files). In Autopilot `auto` mode, pdd-merge handles eligible merges after repository review and test rules pass; required human approvals still apply.

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
| `pdd test [PATH\|STORY...] [--lf] [--cache-clear] [--json] [--details] [--timeout MIN] [--max-calls N]` | Reuse complete unchanged passes from `.pdd/cache/test/`. `--lf` selects last-known failures, or the normal scope when none are recorded. `--cache-clear` discards the cache while retaining operand scope and takes precedence over `--lf`. Check Stories on the PDD interpreter with your gh login. With no STORY, test every Story. Send your Git files and wait for the checks, with one progress line every 30 s. Then print one table with a report link for each test, one `Prompt tests` line for each Story and, with two or more Stories, the overall line |
| `pdd test --read [BATCH\|CALL_ID] [--json] [--timeout MIN]` | Read saved results; a normal Check held for lint may continue its original checks. Other reads send no work |
| `pdd test --retry BATCH [--json] [--details] [--timeout MIN]` | Retry only confirmed unstarted checks with the saved source and call caps. Keeps completed, running and unknown jobs; changed source requires a fresh selected check |
| `pdd test --fill-hash` | Fill the hash of draft runtime interfaces. No network |
| `pdd test --fill-hash --compact` | Fill draft hashes and remove interface JSON formatting whitespace. Preserve values, strings, number spellings and prose. Approved and statusless files stay unchanged. No network |
| `pdd test --explain-bindings [STORY...] [--json]` | Explain each selected resource edge, fixture candidate, mismatch cause and repair. Local reads only; no sign-in or interpreter call |
| `pdd test --files [STORY...] [--app-map PATH] [--json]` | List the exact selected upload manifest and byte sizes. No network; `--app-map` previews the Simulator's app map |
| `pdd lint [STORY...] [--json] [--timeout MIN]` | Print local SVG layout warnings, then the server checks the format of the prompts, Stories and tests only, with 0 AI calls, and requests complete diagnostics and prints the problems the server reports. Requires network access; use it before a real check |
| `pdd lint --local [STORY...] [--json]` | Compare linked `.ui.svg` parts and labels with prompt prose locally; warning advice only, 0 AI calls and no network/authentication. Without Story names, inspect all Git-visible prompts, even with no PDD tests |
| `pdd test --screen URL --drawing PATH [--json]` | Compare the real page with its `.ui.svg` layout spec in installed headless Chrome/Chromium at the SVG viewport. No AI or interpreter call; missing/hidden parts, order or region differences fail |
| `pdd interface draft [PROMPT...] [--all] [--json]` | Draft missing Runtime blocks from explicit prose or contracts and lint locally, without AI or network calls. Uncertain facts include field questions and a recovery command. |
| `pdd interface draft PROMPT [--contract FILE] [--extend \| --refresh] [--json]` | Supply schemas and effect ports, extend an existing block, or reopen a stale block as draft. |
| `pdd approve PROMPT --automatic --tests COMMAND` | Approve a complete draft of unchanged committed behavior after existing native tests and a complete current prompt check. Strict mode requires a person. |
| `pdd approve PROMPT [--said WORDS]` | Approve one prompt with your chat words, or terminal y/N without --said; strict mode requires a person terminal. |
| `pdd simulate [STORY] [--max-calls N] [--tab call\|screen\|terminal\|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent NAME]` | Open the Story in the PDD Simulator: make a Simulator link and open it in your browser. It ends in 24 hours. Short form: `pdd sim`. `--agent NAME` chooses a configured display name (quote spaces), or codex, claude or gemini. With terminal stdout or explicit `--agent`, it connects your agent and waits. Without either, it reads saved cases once and returns. `--no-wait` skips the connection. In a terminal, it adds each case saved in the Simulator to the Story's test file, and asks y/n when you click Approve on the page |
| `pdd simulate --stop [STORY]` | Stop the open Simulator link of a Story |

Ordinary `pdd test` reuses complete unchanged Story passes from the Git-ignored `.pdd/cache/test/` folder, showing their previous pass time and zero current AI calls. `pdd test --lf` selects the last known failures; a later attempt without a verdict keeps a failure selected until it passes. With no failures in the selected scope it uses the normal selection, including unchanged-pass reuse. Completed saved reads populate the cache after source verification, dated from the original batch start, never the later read time. `pdd test --cache-clear` discards prior local evidence and runs the normal selected scope; it takes precedence over `--lf`. It sends again and prints one stderr notice with the selected Story count; the interpreter may return a saved answer for the same key.

Reuse includes reached call targets, exact authored bytes, interpreter origin, call budget, pdd version, and the interpreter build and requested model reported by job answers. A missing identity or a pass older than seven days runs again. A different build or model observed during a run also runs the selected Stories initially skipped, with a reason; after a timeout or interrupt those rows are marked not sent. Reuse requires one clean record naming the same known build and model as the pass. A clean normal run starts after the previous sample, sees no record change during the run, and has only agreeing complete identities. Overlap, any read that writes the record (even after resending), an old or unknown writer, partial or mixed observations, or multiple stored values leaves doubt and runs. A later clean normal run can restore reuse. Before sending checks, a run saves an in-progress mark with its pid and start time. Another run's mark, live or dead, makes checks run. Live marks remain until their owners finish; dead marks are retired after forcing a run. A run can finish clean only while it still owns its mark and no other run has changed the record; it removes only its own mark. A failed sign-in removes its own mark but leaves doubt. All check sends share one ownership boundary: normal checks, saved-read continuations, retries and recovery hold their own mark from before the first send until their last send and observations finish. A retry retains ownership across its initial read. Reads and retries finish with doubt; direct callers with reuse disabled still coordinate their sends. Cache clear preserves every in-progress mark. A crash therefore costs one extra run, and overlap remains doubt until a later clean run. An all-skipped local run cannot discover an interpreter update without calls. Stories using the real clock or AI-played fakes run every time and say why; completely deterministic simulation bindings and fixed clock data permit reuse. Fixed clock values must be finite numbers or ISO 8601 date-time strings; labels such as `real 2026`, `now 1` and `1` run with the real-clock reason. Unknown resource kinds or actions run. Missing Story footprints, missing sources or malformed declarations report `runs again: resource declarations unavailable`; reuse can resume once evidence is complete; plain dependencies without an interface declare no resources. An expired pass reports `runs again: saved pass is older than seven days`. `CI` unset or set to the empty string, `0` or `false` permits ordinary reuse; every other value runs every selected Story. A saved pass at most seven days old still counts for prompt approval. Tracked cache files and caches copied without their external machine-local state are never reused. Damaged regular metadata heals after a completed run; its warning names `pdd test --cache-clear`. Dead-owner cache locks recover with one warning. Symlinked ancestors of `PDD_STATE_DIR` are accepted, but a final state-folder symlink is refused.

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
| `pdd workflow done STEP [--summary TEXT] [--skipped REASON]` | Record a finished step. `check`, `try` and `verify` also record pdd's own latest `pdd test`, `pdd lint` and `pdd workflow prove` results, or warn that pdd has none; the summary stays an agent note. `--skipped REASON` records that the step was skipped, and why. Print the next instruction: the next step, the gate, or "pdd opens the PR now". After the last step of an area with a PR gate, push the branch and open the PR when the applicable gate is satisfied. In a normal feature or bug run, a valid Story approval and a verified full saved check pass open PR 1 without another question; strict and other routes can require a separate approval gate. In an Autopilot run, a `done` that returns to an earlier step and clears later recorded steps is a repair round; a retry of the same step (after a failed PR open, claim check or push) or a check recorded again on unchanged files is not. A clean merge of a newer saved base, with no extra issue edits, uses a separate base integration budget of 2 per area. Each new source-changing merge charges once, even when a step return clears no later records. Repeating any step on an already charged source tree consumes neither budget, including after a source-identical base advance and across mixed step returns. A base advance that leaves the source tree identical also consumes neither budget. Commit the issue work before recording the step so pdd can retain its Git snapshot. A missing snapshot, dirty tree or merge conflict gives no exemption. Each accepted integration prints its reason, retains superseded step records in history and clears later checks for fresh evidence. It also archives and clears every current step record tied to an older source tree, including steps before the returning step. PDD requests the first missing step. Record all cleared steps on the new tree before a PR opens; this does not charge the integration again. Archived snapshots remain budget baselines, so further merges and issue edits still respect their limits. A third integration stops the run and refuses later `done` calls; use the same cancel and new-run recovery route. The bug skill still allows only 2 defect repair rounds after review. After 5 native repair rounds in one area, pdd refuses another, marks the run stuck ("Repair limit reached in AREA: take the stuck path" in `status`) and refuses every later `done` of it. To let Autopilot try again, a person removes `pdd:stuck` and `pdd:working`, then runs `pdd workflow cancel N` in the checkout that holds the stuck run; the next tick starts a new run with a fresh repair count. Without the cancel, a new automatic start of the issue in that checkout waits: "Automatic start deferred: issue has an active run" |
| `pdd workflow ask QUESTION` | Show the person that the chat waits for an answer in the middle of a step. `status` then says "waiting for you" with the question |

The agent runs these from the run's worktree. pdd finds the run from that folder. You do not run them yourself.

## Other commands

| Command | What it does |
|---|---|
| `pdd`, `pdd --help`, `pdd -h`, `pdd help` | Show the commands and the full paths of the installed Prompting guide and RUNBOOK |
| `pdd help prompting` | Show how to write a prompt, a Story and its test, which commands check them, and the full paths of the Prompting guide and RUNBOOK |
| `pdd --version` | Print the version, `0.1.27`. When the PDD skills that your agent finds are older, also print the update command on stderr |
| `pdd completion bash\|zsh` | Print a shell completion script. It does not change your shell files |
| `pdd jobs` | List active slots and waiting interpreter jobs on this machine, including kind, PID, age and request IDs. Local and read-only; no repository, authentication or interpreter call |

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

In a normal run (no `strict_approvals`, not an Autopilot run), the Story gate prints a Story card; show it as printed, then ask. The person approves each Story with that context and may choose the code PR after PR 1 (`--through code`). After that approval, a prompt-only repair needs no new approval. When pdd verifies its own saved check results (every criterion of every scenario in the default project check scope passes, and each result belongs to its batch and matches the current files), `pdd workflow done` opens PR 1 with no question and records the route `automatic-check-pass`; PR 1 shows it as `Opened after a full check pass (no person asked):`. pdd skips the optional try step. A failed check keeps the gate for repairs. A change to a Story, the plan or an expected value shows the card again and waits for the person. The same checks apply before updating an open PR 1 and before a later said or terminal code approval, including after PR 1 merged. A revised Story must be shown and approved first. Unpublished source changes need a current full check. Default discovery excludes nested fixture projects, as `pdd test` does. With `--through code`, pdd then starts the code area and records the route `card-choice`. Strict mode keeps its person gates. In `auto` mode, each Autopilot tick handles waiting PR 1 gates before local parking and dependency reviews when its GitHub budget permits. This includes a gate already parked solely for that approval wait. A changed Story reopens Story approval and replaces any earlier check-failure guidance. The park follows the revised gate and keeps its age and closed sessions. Later ticks keep the Story approval reason until that gate is resolved. A successful publication keeps its saved sessions closed and binds the park to the separate code gate. A run with current operator scope, current claim custody, unchanged approved Story coverage and a full saved check pass uses the same `automatic-check-pass` route with automatic origin. It leaves the code gate for the scoped coordinator handoff. When an automatic run has no saved Story coverage, pdd can derive it once from the recorded Story approval and its matching journal evidence. A saved Story contract and file inventory bound to that approval must establish the approved files. An earlier Story-step source hash cannot establish what a later approval covered. pdd derives the contract and fingerprint from the same temporary snapshot, then compares them and the prompt list with the recorded approval and current files before saving coverage with source "derived from the recorded approval". A difference or intervening edit reopens the Story card and saves no coverage. Missing or unverified coverage, incomplete or stale checks, strict policy and unavailable authority keep PR 1 closed. Normal runs with missing coverage keep their person gate. Status shows the hold reason. A cancellation, new person question or changed gate during preparation or publication stops further approval, push and PR effects. This includes a blocker saved while waiting for the approval journal lock: pdd rechecks the saved run under journal custody before committing approval evidence. Saved blockers remain in place. Observe mode does not cross this gate. `pdd workflow status` names the runs that wait for a Story approval.

Without `--said`, a person at a normal terminal answers y/N. The question lists the gate and its drafts; one answer approves them together. `pdd approve PROMPT` still approves only one prompt. Agent, non-TTY and current Herdr chat-pane callers must ask the person, then relay the reply with the safe form above. Native Herdr evidence never authorizes approval by itself.

Workflow approval reads `pdd.json` from the main checkout (`sourceRoot`), outside the agent's run worktree. Standalone `pdd approve` reads it from the Git root of the current checkout. `"strict_approvals": true` permits only a person at a terminal and refuses `--said`. Absent or false keeps easy mode. Agents never edit approval fields or decide expected values. Records retain the invoking actor, time, route, exact words and prompt path/hash. PRs show matching approvals safely quoted. Approval of PR 1 does not approve the later code-or-stop gate.

`pdd workflow ack REQUEST_ID --summary TEXT` records the agent’s uptake of a delivered change request from its active run worktree. The first note and time are retained on repeat calls. Delivery and this explicit agent claim do not prove the request was fully addressed. Status shows delivered requests still awaiting uptake; done warns without blocking progress.

## Metrics

- `pdd metrics [--json] [--date YYYY-MM-DD | --snapshot ID] [--timezone IANA] [--at UTC] [--expected-source ID...]`
- `pdd metrics export FILE [--timezone IANA]`
- `pdd metrics import FILE`
- `pdd metrics record FILE`

`pdd graph` reads the saved dependency graph; `pdd graph --open` opens its viewer. Use `pdd graph --issue N` to select an issue, or `pdd graph --open --issue N --repo OWNER/REPO` to select a repository explicitly.

`pdd dependencies prepare [--issue N]` prepares a coordinator packet. Review batches use the stable owner of this machine’s Autopilot for the repository. A replacement coordinator chat can finish the same batch. Ownership is checked before automatic review delivery and again before saving reviews. A different owner leaves the batch pending with `owner-changed`. `pdd dependencies complete --input -` reads a structured completion from stdin. `pdd workflow yield N` hands off automatic capacity after the current worker has stopped.

`pdd workflow park --reason TEXT --step STEP` records an environment failure of
check, verify or formal in the current area. Environment parks require `--step`;
pdd does not guess the failed target from unfinished steps in an older run. Autopilot retries only that validation
after 15 minutes, 1 hour and 4 hours. It keeps the run and completed work. After
three failed retries, it stays stuck and sends one alert naming the cause.

`pdd workflow park --route KIND --reason TEXT [--until FIX] [--step STEP]` records a missing supported PDD route. Use a lowercase kind such as `interface-drafting` or `native-replay`; put the agent's full question in `--reason`. The default fix is `capability:route-KIND`; `prompt-reentry` uses `#2897`. An explicit fix can name a capability, issue fix or commit. A package version alone cannot clear this wait. The command keeps gates, independent questions, work and the claim. It asks no person.

The native tick saves route questions and counts by kind in `routeQuestions` in the coordinator state. On an automatic tick with GitHub work allowed, two distinct records of a kind create one issue in `promptdriven/pdd`. An uncertain issue write stays recorded and is not sent again. JSON Autopilot status includes this ledger. A run parks with a `missing PDD route` blocker and wakes through the saved session when the installed PDD provides the required capability or commit. An issue closing alone cannot wake it.

`pdd workflow park --reason TEXT --blocker KIND [--until VALUE]` names an external wait. Use `dependency --until 2897` for an issue that must merge, `pdd --until capability:prompt-reentry` for an installed capability, `pdd --until commit:SHA` for an installed ancestor commit, or `pdd --until '#2897'` for the PR 1 re-entry route, or `account` / `github` with an ISO reset time. `person` requires an existing pending question or gate and clears on its reply. `ci` and `review` use the saved PR result or review evidence. Invalid clearing values save nothing.

Autopilot closes a blocked run's chat and shell panes after it saves their native session identity. A live UUID supplies resume custody only for the same agent kind, pane and saved terminal, with successful naming verification when required. A current chat without proven session evidence stays open. A matching legacy workspace can be adopted for cleanup only when its creation field is absent; explicit null keeps it protected. The run keeps its claim, folder, branch and worktree. Only working runs count against `--runs`, with the same count as status. Idle stuck and parked runs use the separate parked-run limit. A deferred automatic start names `runs` when the working cap is full and `parked` when the parked-run limit is full. A queued or running check counts as working even after its chat closes. Unknown check custody retains that slot and prevents claim release. A reply to a parked question is saved in the request journal. Its chat stays closed until the coordinator admits the ready run within the working cap. A ready parked run resumes its saved session before new work, oldest first. Three consecutive no-verdict observations enable test mode. During recovery, `outage.probe` tests one waiting run at a time; the other waiting runs wake only after that check reaches a verdict. A verdict restores ordinary interpreter admission; older saved no-verdict waits cannot override it. When a verdict arrives late, failures that occurred after it still count. Code and native tests can continue.

Set `autopilot.parking.hours` in `pdd.json` to change the 48-hour park limit. `autopilot.parking.maxParked` sets the parked-run limit; the default is twice the chosen run cap. Replacing a parked run's named blocker replaces its clearing condition and keeps its saved session and original park time. A timeout or surplus park releases its claim to the existing queue, keeps its work on its branch and posts one marked comment. Release holds run custody; replies cannot resume a run while its claim is being released. An uncertain release keeps a reservation for retry. Each tick also classifies saved stuck and waiting runs, including those without a parking record. Interpreter no-verdict and unknown saved reads use the same test-mode wake rules. A replacement interpreter wait keeps its current saved batch and counts once across unchanged ticks. At a generic approval gate without an independent question, a finished check with no verdict refines an existing park to an interpreter wait bound to the current gate and saved batch. Each tick re-reads this inferred evidence. A changed gate, completed check record, batch or saved result refreshes the wait, even when the other values stay unchanged. Unchanged evidence keeps the same wait identity and original park time. A saved verdict returns the wait to its current approval gate. Another blocker retires the old interpreter evidence without changing the original park time. A saved wait for the missing PR 1 re-entry route wakes when that capability is installed. A wake consumes its saved stop cause. A later person gate or new stop uses its own blocker and keeps its pending question or gate. Package version numbers alone do not prove a fix is installed. Saved idle or resume ceilings keep their existing recovery and alert custody. A pause without a saved blocker or failure cause stays paused. Other unknown causes stay stuck with one alert. Status shows working and parked counts by blocker. A same-group issue joins the group's existing run. File overlap does not prevent independent runs; update each PR from its base before merge.

Parking waits for the current agent to be idle or done. A done chat closes without
finished-chat grace after its screen and session are saved. Complete Herdr
inventory can confirm an absent workspace or pane, including a starting chat,
as closed with reason `absent`. Every tab and pane row must name the requested
workspace and include its required IDs. An empty scoped list proves absence
only after a valid workspace list confirms that workspace exists. Malformed
or out-of-scope inventory retains the chat with `invalid_cleanup_inventory`
and supplies no close mark. Confirmed absence sends no close request and keeps
the saved session. A `closing` run holds a working slot in status and admission until all
chat and shell absence checks pass. Without a current blocker, fresh running
progress holds cleanup with `new progress since park`. An unelapsed recovery
grace holds it with `recovery grace until T`, where T is its UTC deadline.
Both holds keep saved custody and count as working. When neither progress
timestamp is newer than the park time and no grace remains, a stale or missing
blocker permits guarded cleanup to retry. Status names the retained reasons;
after 60 seconds it also shows `closing-retry`.
Busy agents and uncertain identity keep their protection during every retry.

`pdd workflow park --reason TEXT` records an automatic stop from its existing run worktree without releasing its claim or treating the worker as done.

A lost verdict, such as `runner-stopped`, needs a person decision before another paid attempt. Autopilot waits for the free health check to answer, then sends one decision alert for all such runs. The alert lists each old batch and its earlier AI calls. Unknown usage stays unknown. To authorize one resend for each listed run, relay the person's exact words:

```sh
pdd workflow resend 17 23 --said - <<'PDD_SAID'
<the person's exact words>
PDD_SAID
```

Use a quoted delimiter absent as a whole line from the words. Without `--said`, a person can use terminal y/N. Strict mode requires a person terminal. This decision does not approve prompts or workflow gates. Automatic setup and start do not authorize it. There is no automatic resend budget setting.

pdd saves the decision, old batch and earlier cost before sending only the lost checks. It keeps the original call caps or lowers them to the smallest selected cap. Active checks, changed source and consumed attempts cannot be resent. The new batch is saved in the run's `checkResends` record. If another attempt has no verdict, the command stops the group at once and names that batch for the interpreter owner. A `service-restarted` receipt also stops this command without an automatic replacement. Later reads and retries of that batch keep this limit. An interrupted send is uncertain; it is never replayed automatically. Gates, questions, parking and completed steps stay as saved.

`pdd workflow park --interpreter --reason TEXT` records that an automatic run waits for the PDD interpreter, the hosted service behind `pdd test`. pdd first reads the run's latest `pdd test` result. Only a check with no verdict from the AI service, a busy or not-run check, or an unknown outcome may wait. A failed check, a refusal that names a file rule or a step that took longer than the server time limit is the issue's own work (make the step smaller). A sign-in, access or interpreter address problem needs a person, and waiting does not fix it. For these, the command exits 1, names the fix and parks nothing. If pdd cannot read the result, the outcome counts as unknown. A waiting run asks no person. `pdd workflow status` shows `waiting for the interpreter: REASON`, and `pdd graph` shows the hold `Waiting for the interpreter`. The run keeps its claim, branch, worktree and progress, and the native tick frees its worker slot after it confirms chat and shell closure.

### Interpreter outage in Autopilot

While a run waits for the interpreter, or an outage or an interpreter access problem is open, each Autopilot tick makes one free health check: a `GET /v1/capacity` read of the interpreter with your gh login. It sends no files and makes no AI call. When nothing waits and nothing is open, a tick makes no check.

- the interpreter unavailable (no answer, HTTP 408, 429 or 5xx, or maintenance): this is an outage. Only a failed health check opens one. Autopilot sends one `interpreter` alert for the repository and machine, wakes no waiting run, and offers other work as usual. New issues can start; their workers wait only at the interpreter check.
- An answer that is neither healthy nor down (HTTP 401 or 403, a redirect, an HTML page, a 404 that is not JSON, no gh sign-in, or an invalid `PDD_RUNTIME_URL`): this is a sign-in or setup problem on this machine. Autopilot sends one `interpreter-access` alert with the fix (`gh auth status`, or check `PDD_RUNTIME_URL`) and resends nothing. This alert includes lost-verdict waits, even when no other run waits. The runs stay visibly waiting. Lost-verdict runs remain parked for a person decision. After 4 hours, other waiting runs follow the stuck rule.
- interpreter healthy and no outage open: waiting runs, from one issue or from many, are a problem of their own issues. Autopilot wakes each run once to retry. If the same step waits for the interpreter again, the coordinator follows the stuck rule.
- the interpreter back after an outage: Autopilot first wakes one waiting run as a test, the oldest. Only when that run saves a new `pdd test` result that passed or failed does Autopilot send one recovery and wake the others, oldest first, within the worker cap. A test run that waits again or goes stuck is no proof, and neither is a test with no verdict within 60 minutes of its wake, also a wake that was never delivered. Each run is the test at most once in an outage.
- A woken worker first runs `pdd test --read BATCH`. It resends only a check that surely gave no verdict: `pdd test --retry BATCH` only when pdd names it (busy or held checks), and else the Story's check once with `pdd test STORY --max-calls N`, for another check that did not run or an AI-service refusal. Lost-verdict runs remain parked for the grouped person decision above. A worker never resends a failed check. Each wake reaches the run at most once for each park. `--max-calls`, strict mode and the merge rules do not change.

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
queue position. Queue waiting and suite execution pause Autopilot's stuck clock.
A suite failure, interruption or execution timeout has its own reason and the
`test-suite` alert kind. It does not mark the issue stuck.

The execution timeout defaults to 30 minutes. `--timeout` accepts 1 to 120
minutes. Waiting does not use that time. Output and exit status come from the
suite; timeout returns 124. The runner stops the suite process group before
releasing its slot.

Autopilot samples usable CPU IDs, free memory and one-minute load at each active
tick. macOS and personal Linux machines use the first half of available
cores (round down, minimum one). Linux desktops without batteries are included.
Linux uses all available cores only when virtualization is detected and no battery
is present. Detection uses `systemd-detect-virt --quiet` with a one-second timeout.
If detection is unavailable or uncertain, Linux uses the personal-machine budget.
With U usable cores and M free bytes, calculated check slots are
`max(1, min(floor(U / 12), floor(M / 4294967296)))`.
Without Linux taskset, calculated slots are capped at one. With enough memory,
Linux VMs with taskset and 4, 8, 16, 32, 64 and 96 cores get 1, 1, 1, 2, 5
and 8 slots. A 96-core machine with 8 GiB free gets two slots.

`--checks N` replaces the calculated slots. Default open runs are twice the chosen
slots, capped at the largest safe integer. `--runs N` replaces that open-run limit. Both options require positive safe
integers and are saved for timer ticks. A start without an option selects its
machine default, except while an uncertain delivery retains saved options.
Native workflow admission enforces the current open-run cap. A resize changes
that cap without changing the coordinator identity or cancelling existing runs.

Each check gets `max(1, floor(U / chosen slots))` cores. Linux taskset gives each
check a distinct CPU list from the parent's allowed CPUs, so tools such as
`nproc` and Node `os.availableParallelism()` see that share. Every child receives
`PDD_CHECK_CPUS` with the share. macOS and Linux without taskset use that hint;
custom test or build tools must read it to set their worker count. Manual slot
overrides can permit several hint-only checks. If affinity slots outnumber CPUs,
extra checks wait for a distinct CPU share.

A tick with load above U holds new checks in the queue. The next active tick
refreshes the shared snapshot, including busy-machine state. Running checks keep
their CPU lists when the machine shrinks; queued checks wait for free CPUs.
A standalone queue without a saved snapshot reads its machine ports on admission.
The latest active tick supplies the machine-wide snapshot and any check override,
including when several repositories use the same queue. Stopping its owner
removes that snapshot, while running checks keep their tickets. A snapshot
expires after 31 minutes without a refresh. Standalone checks then probe current
machine capacity with default limits. Another active repository's snapshot is
retained when a different repository stops.

Idle automatic runs release their chat process and panes through parking. This
includes stuck runs, person waits, and stopped recovery attempts. Bare pauses and recovery
ceilings without a named blocker get a 60-second grace period. Saved sessions, worktrees and claims stay.
A continuation uses the saved session in a new pane. Before pane admission fails,
pdd tries the oldest idle automatic runs with zero grace. Active or uncertain
checks and workspaces without a saved creation record prevent cleanup. Personal
workspaces stay open and are listed for manual inspection.

`pdd autopilot status` reports calculated and chosen checks and runs, and
`check slots: B busy of S, W waiting, cores per check C`. These are the shared
admission limits, including another repository's active override. Status uses
current machine defaults only when the shared snapshot is absent or expired.
It labels this repository's saved options separately as repository overrides.
It reads shared tickets without changing queue or workflow state. An unavailable
observation reports its cause. Machine-caused check retries are separate from
capacity admission.

The default queue directory is `/tmp/pdd-full-suite-UID`, where UID is the local
user ID. It is independent of repository, HOME and agent profile. All launchers
on the machine must use the same queue directory. `PDD_SUITE_QUEUE` can select
an absolute shared directory. `PDD_VM_SUITE_LOCK` selects `VALUE.queue` when
`PDD_SUITE_QUEUE` is absent. `scripts/vm-suite-lock.sh` uses the same queue.
Autopilot keeps both selectors in its saved environment, timers and coordinator
and worker launches. Workflow status reports an unavailable queue with its cause.
While queue activity is unknown, Autopilot withholds inactivity rules for the run
and retries the read on later ticks.
Queue records stay outside the repository and contain no commands or test output.

Environment validation stops show the next attempt and UTC time in workflow status.
A person can request another try by removing the observed `pdd:stuck` label or
posting a trusted retry comment, such as `Please retry the failed validation.`
Diagnostic mentions and negative continuation instructions do not request a retry.
The next tick offers the signal through the existing coordinator packet. The
coordinator passes its exact retry text with `pdd workflow changes N`. Confirmed
worker delivery resumes only the failed step and keeps completed work, gates,
questions, branch, claim and the automatic retry count. This person request does
not wait for the automatic backoff. STOP, current ownership and repair ceilings
still apply. A failed or uncertain delivery does not resume the run.

Autopilot classifies causes as environment, interpreter or work. Real failing
assertions, review must-fixes and decisions follow the work rules. Unknown
interpreter outcomes retain saved-batch reconciliation. Mixed causes with real
work failures do not retry automatically. Missing-tool stops must name the
executable (for example `missing tool: node`); the retry checks PATH first.
The host preflight requires one-minute load per CPU below 1, at least 10% available
memory, and Linux I/O and memory PSI avg10 below 10%. Unknown host or queue facts
block retry. The optional shared suite queue is observed without changing it;
only confirmed-dead waiting owners, or dead running owners with confirmed-dead
descendant process groups, release capacity in this read. Live or unknown ownership
still blocks. Queue records stay unchanged, and the validation command must still
use normal suite admission. An environment wake
is offered by the next regular tick after its due time, as worker room permits.

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
are counted, including normal runs. Unallocated coordinator calls and calls made
by agents outside pdd are excluded. Costs remain after GitHub budget compaction.

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


## Autopilot issue sorting and areas

Before new issue work, the coordinator sorts the issue on the current release.
It supplies `analysis.sorts` in the same dependency completion. PDD validates and
saves the records. It makes no model call for sorting. The record schema and agent
steps are in [sort and route](../skills/pdd-autopilot/steps/sort.md).

Set owners in root `pdd.json`, for example:

```json
{
  "autopilot": {
    "mode": "observe",
    "areas": [
      {"name": "cli", "match": {"paths": ["src/**", "skills/**", "docs/**"]}, "owner": "autopilot"},
      {"name": "runtime", "match": {"repositories": ["promptdriven/prompt-runtime"], "keywords": ["hosted interpreter"], "labels": ["runtime"]}, "owner": "agarwal-ishaan", "mixed": "whole"}
    ]
  }
}
```

Match rules accept paths, keywords, labels and repositories. Explicit areas win
over local CODEOWNERS. Ambiguous matches need a person. Without a rule, the repo
has one Autopilot area. On the first visit without an explicit map, the coordinator
shows a draft from CODEOWNERS, folders, labels and known assignees. A person edits
and saves it once. A repository owner can use `repo:OWNER/NAME` to route work to
another repository with a link note.

Auto closes fixed, duplicate and old-code issues with evidence and a reopen hint.
Observe labels them `pdd:close-proposed` and proposes the close. Another login gets
one assignment note. An unknown owner gets `pdd:needs-owner` and one question.
Each area's optional `mixed` is `whole` or `split`. For promptdriven/pdd,
Runtime defaults to `whole`: its owner receives the complete issue, including
CLI work, with one note naming all parts. Autopilot does not start it.
`pdd:owner-whole` and `pdd:owner-split` labels from a trusted person override
comments and defaults. A trusted comment can use either directive or
`mixed: whole` / `mixed: split`. Conflicting labels or unknown label authority
need one owner question.

The sort record includes `touchedAreas`, with an `{area,evidence}` row for
every area. Split also needs `splitOrder:{first,evidence}`. Auto creates one
issue for each of the two parts, titled `<area> part of #N`, links them as
sub-issues, assigns the external part and adds native blocked-by links in the
required order. Autopilot works the local part. Each part closes independently;
the original tracker closes only after both complete. Observe retains the split
proposal. Missing area evidence, policy or work order gets `pdd:needs-owner`
and one question. More complex owner or order choices also need a person.
Person assignees and live claims prevent all issue writes. Writes are
guarded inside native admission. Closing a split tracker checks its ownership,
state and inputs again after reading both child completions. Missing split links
check both endpoints after evidence reads. Child claims are read before child
assignees, then parent ownership is checked again. An interrupted split recovers
the same completed, unassigned and unclaimed child, confirms missing links and
saves the split note without assigning completed work. Person assignments and
live claims hold recovery until released. Malformed sort
records cannot abort the snapshot read. Invalid trusted heads hold selection;
outsider records do not block it. Writes are
serial and wait at least one second between effects. Each invocation routes at
most 10 unfinished issues. Record saves, group effects and routing share a limit
of 20 write attempts. A low or reserve GitHub budget stops further effects. The
next tick resumes the remaining work. Existing route notes and labels prevent
repeat effects from holding later issues.

Grouping is continuous. New and changed sorts are compared with all open saved
sorts and groups. Equal causes join or form a group. A changed cause leaves it.
At three members, or across locally owned areas, auto creates one
`Global fix: <cause>` issue with the member links, cause and one fix statement.
Observe keeps the group proposal. Claimed issues and open-PR work finish before
they can join. A running umbrella gets one note when membership changes.

The global fix PR references its members. After that PR merges, every member
needs a fresh sort against the fix. Only members confirmed fixed close with
evidence; the others stay open. `pdd autopilot status` and the graph issue list
show group size, cause and umbrella. Umbrella creation uses a shared GitHub
reservation for each cause. This requires repository Contents write access. The
reservation is a temporary `pdd/issue-groups/` branch. While holding it, PDD checks
the current open issue index for an existing trusted umbrella. Separate machines
therefore recover the same issue. This does not claim the members or start work.
An uncertain create keeps the reservation and holds another create. A visible
trusted umbrella can still be recovered on a later tick. Without such evidence,
a person must inspect the cause before removing a retained reservation. PDD never
expires it by age. Local group state is kept in the checkout's
Git common directory. Existing dependencies, claims, trust and merge rules apply.

`pdd workflow approve [ISSUE] [--said WORDS] [--draft]` records the ready approval gate. A normal Story-card choice can also use `--through prompt-pr|code`.

Automatic runs use `autopilot.base` in `pdd.json` when set; otherwise they use the repository default branch. Start and status show the selection. Each explicit start refreshes the cached default branch from one repository read, including after stop. A changed selection reaches the coordinator even when issues are unchanged. Ordinary ticks and status use the cached value. Each run saves its base at start and keeps it for its area briefs and PRs. Repository documents do not select the automatic base. A manual workflow still accepts `--base`.

## Runtime interface kinds and coverage

A block declares `kind: full`, `partial` or `native-only`. An absent kind means full.
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

The installed interface drafting capability clears a saved Autopilot wait for
`capability:route-interface-drafting`. It wakes the saved session through the
ordinary continuation route. It does not approve a prompt or a person gate.

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

Set `autopilot.engine` to `core` in `pdd.json` to run the small native engine
instead of the coordinator chat. The default is `full`. The core engine needs no
Herdr: `pdd autopilot doctor` skips the Herdr checks, `start` opens no Herdr
session, and each job is a headless Codex or Claude process with a log file.

```json
{"autopilot":{"mode":"auto","trust":[],"engine":"core","runs":2,"label":"pdd:autopilot",
  "jobTimeoutMinutes":120,"report":"draft","repairs":2,"testCommand":"npm test"}}
```

| Key | Meaning | Default |
|---|---|---|
| `runs` | Issues in progress at the same time on this machine | 2 |
| `label` | Take only issues with this label | none: every ready issue |
| `jobTimeoutMinutes` | Time limit for one agent job, and for the checks of one PR | 120 |
| `report` | `file`, `draft` or `off` for Runtime and PDD problem reports | `draft` |
| `repairs` | Repair jobs for one PR after a red check | 2 |
| `testCommand` | Full test command that runs on the PR head | `npm test` when `package.json` has a test script |

Each tick, without AI calls:

1. List the open issues. An issue is ready when it has no assignee, no live
   `pdd:working` claim, no `pdd:stuck`, no open issue that blocks it (a GitHub
   issue dependency or a `blocked by #N` line in its body), a trusted author and,
   when `label` is set, that label. The oldest ready issue goes first.
2. Refresh the heartbeat of this machine's claims.
3. Check each job. A job that ran past its time limit, failed, died or left no
   result ends. A job with a PR goes to the merge check.
4. Merge check: the PR head is the job's head, CI is green for that head, the
   full test suite passes for that head, a fresh reviewer agent that did not write
   the change gives PASS for that head (the tick posts the verdict on the PR), the
   PR does not say `Runtime: FAIL`, and the base check passes. Then
   `gh pr merge --merge --match-head-commit HEAD` merges it, and the issue closes.
   A red check starts one repair job on the same branch, up to `repairs` times.
5. Fill free slots: claim the oldest ready issue with `pdd:working` and a claim
   comment, make a worktree and start one headless job. The job makes one PR with
   prompt, tests and code, and writes one `Runtime:` line in the PR body.

When a job ends, the issue gets one comment with the cause and the log path, the
label `pdd:stuck`, and loses `pdd:working`. Nothing else waits on it. To retry,
remove `pdd:stuck`. To stop a running job, close the issue, assign it or add
`pdd:stuck`. After three jobs in a row end with no
result, for example when the agent is signed out, intake pauses for one hour on
this machine. `pdd autopilot status` shows the jobs, the busy slots, a pause and
the last results from local files.

A Runtime problem (no verdict, lint or binding refusal, interpreter error) or a PDD
problem (CLI error, crash, claim or merge-check tool error) also gets one report
for its owners in promptdriven/pdd: label `pdd:runtime` (assigned to the Runtime
owner) or `pdd:autopilot-report`. One cause has one report: a repeat on another
day adds one "seen again" comment. Each machine files at most 3 new reports a day.
Reports hold versions, the step, the error code and a short redacted detail,
never code or text from your repository. With `report` `draft` (the default) the
report stays on this machine until you run `pdd autopilot report send
FINGERPRINT`; with `off` nothing is saved. The ended issue's comment says
`Blocked by` the report when it was filed. When a job's PR says
`Runtime: not run (reason)` for a Runtime cause, the PR still can merge; the tick
files or counts the report and rewrites the line to `Runtime: not run (#N)`.

## Post-merge audit settings

Autopilot calls `pdd autopilot audit RUN PR` after each automatic merge. Its fixed
brief requires before/after reproduction, scope, Story quality, old-code tests,
real check evidence, unchanged checks and actual merge gates. Audit files remain
in shared durable custody under the machine workflow state root, keyed by
repository, run attempt, PR and merge commit. The run's `audits/` folder holds
evidence copies. Every clone reads shared results and effect reservations under
the repository lock. An interrupted auditor is unknown, never a pass.
Pending known work is offered to the coordinator on later ticks. Discovery reads
saved runs through the tick process port. The local scan needs no GitHub read.

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
Autopilot parks a saved binding refusal with blocker `binding`. Interpreter
health alone does not wake it. Use the normal reply/retry route after repair.
