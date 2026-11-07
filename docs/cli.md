# CLI reference

This page lists every command of pdd 0.1.20, as `pdd --help` shows it. A test (`test/docs-commands.test.mjs`) checks that each command form of the help is on this page.

You need the pdd command only for runs with PRs, for `pdd test`, `pdd lint`, `pdd simulate` and `pdd approve`. Install the skills with `npx skills add promptdriven/pdd` (add `-g` for all your projects), and set up a repo with the `pdd-setup` skill in your agent. For simulations that your agent drives, use the Try tools in `pdd mcp`. Then use a PDD skill: `pdd-feature`, `pdd-bug`, `pdd-small-change` or `pdd-prompting`. Call a skill with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code (or ask for it by name). See [Install](USAGE.md#2-install).

Typing `pdd check` or `pdd try` runs nothing and prints the name of the command to use.

## Set up a repo

| Command | What it does |
|---|---|
| `pdd setup` | Install the five [PDD skills](USAGE.md#4-the-pdd-skills) when they are missing, and say where. Then add or update the short PDD block (7 lines, between `<!-- pdd:start -->` and `<!-- pdd:end -->`) in `CLAUDE.md` of this folder, else in `AGENTS.md`. If neither exists, make `AGENTS.md`. In a Git repository, add the line `.pdd/` at the end of the root `.gitignore` when no line there is `.pdd`, `.pdd/`, `/.pdd` or `/.pdd/`; `pdd test` keeps its local cache there. Setup only appends: all other bytes stay the same. When the last such line starts with `!`, or no such line exists but a `!` line names `.pdd` or a path in it (such as `!.pdd/config.json`), setup changes nothing and says so. Repeat setup keeps an existing Autopilot mode |

`pdd setup` copies the skills to `~/.agents/skills` (Codex and Gemini) and `~/.claude/skills`, or `$CLAUDE_CONFIG_DIR/skills` when it is set (Claude Code). If `npx skills` already installed them, it copies nothing. When the skills it finds are older than this pdd, or differ from its skills, it says so and prints the command that updates them: `npx skills add promptdriven/pdd -g -a codex -a claude-code -y`, without `-g` for a copy in the project. After an update of the pdd command, it replaces an older copy that has the `.pdd-skill.json` marker. It never touches a copy without the marker, or a symlink. No other pdd command copies skills. The `pdd-setup` skill does the same in a chat. Run it in the top folder of the repo.

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

Settings live in the repository's `pdd.json`, for example `{"autopilot":{"mode":"off","trust":[]}}`. Other settings are preserved. Autopilot workers start from the default branch on GitHub and read `pdd.json` there, not your local copy. So `pdd autopilot off`, `observe`, `auto`, `trust` and `untrust` also update `pdd.json` on the default branch, through the GitHub API with your `gh` sign-in. Each command makes only its own change on GitHub: a mode command sets `autopilot.mode`, `trust` adds its names to `autopilot.trust`, and `untrust` removes its name. All other keys and fields keep the GitHub values, also when your checkout is behind. The commit message says what changed, and the commit changes only those bytes of `pdd.json`: the indent and the key order of the file stay. They do not touch your current branch or your uncommitted work. More lines tell the result:

- GitHub is already up to date.
- The commit URL, then `pdd.json on GitHub is updated. To update your local copy, run git restore pdd.json, then git pull.` `git restore pdd.json` drops your local change of `pdd.json`, which GitHub now has. Run `git pull` on the default branch.
- When the default branch accepts changes only through a PR: the URL of a PR from a `pdd/autopilot-settings-…` branch, which you must merge before workers use the new setting. While that PR is open, the next command adds its change to the same PR. When the new setting is the same as on the default branch, pdd closes the PR with a short comment.
- When the copy on GitHub then has other settings than your checkout, one more line shows both.

When another change of `pdd.json` on GitHub comes between pdd's read and its write, pdd reads the file again and tries once more. When GitHub cannot be reached or `gh` is not signed in, the local setting stays, the exit code is 0, and the line tells you to run the same command again. `pdd autopilot start` and `pdd autopilot status` print a warning when the copy on GitHub has another mode or trust list, with the commands that change it, or when a settings PR is still open, with its URL. `pdd setup` saves a first mode only in your checkout and never writes to GitHub; it prints the command that puts the mode there. Invalid saved modes count as `off` with a notice; setup leaves them unchanged, and a mode command replaces them. Names match ignoring case. The repository owner, people with write access (including access through an organization team), and explicitly added names are trusted independently. An incomplete lookup never establishes trust for an unknown person.

These commands store settings and determine trust. Selecting a mode starts no run and makes no interpreter call. Approval policy, including `strict_approvals`, stays independent.

## Autopilot on this machine

| Command | What it does |
|---|---|
| `pdd autopilot start [--runs N] [--resume-custody FILE]` | Check sign-ins and the running pdd version, open a dedicated interactive Herdr session and check for work immediately. A user timer checks again every 30 minutes. `--runs` sets an optional concurrent-run cap; omission has no fixed cap. `--resume-custody` supplies the verified original-owner projection for explicit recovery |
| `pdd autopilot stop` | Disable this repo's timer on this machine and let the current agent step finish |
| `pdd autopilot status` | Show this machine's repo, agent, timer, coordinator health and next tick without waking an agent; an idle coordinator is healthy. It reads `pdd.json` on GitHub only to warn when its Autopilot settings differ from this checkout. Another line shows a pending or held coordinator relaunch, one line an [alert](#alerts) that was not delivered, and one line the [GitHub calls](#github-api-budget) of the last hour |
| `pdd autopilot add N...` | Label named issues `pdd:autopilot`. Autopilot does not need this label: it considers every open issue |
| `pdd autopilot alerts set` | Read your Discord or Slack incoming webhook URL from stdin and save it for this machine |
| `pdd autopilot alerts set --discord-channel ID [--token-command CMD]` | Use a Discord bot in one channel: read its token from stdin, or save CMD and run it at each send to get the token |
| `pdd autopilot alerts test` | Send one test message and confirm that it was posted; for a bot, first check and show the bot name and channel name |
| `pdd autopilot alerts clear` | Remove the alert destination from this machine |
| `pdd autopilot alert --issue N --kind usage-limit\|resource\|access\|decision\|stuck\|recovered --input - [--update]` | For the coordinator: record one alert and send it to this machine's destination |

The launcher uses the repository settings module to read root `pdd.json`. An
active mode is `observe` or `auto`; missing or invalid settings count as `off`. It uses an
installed, signed-in Codex, Claude Code, agy or Gemini agent. Missing dependencies
get one actionable line. Linux uses a systemd user timer; macOS uses a
LaunchAgent. On Linux, start warns when user-session lingering is off or
unavailable: `loginctl enable-linger` keeps the timer after logout. The tick
service preserves a Herdr server it starts when the tick exits. See the chat with
`herdr session attach pdd-autopilot`.

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

A tick checks GitHub with ETags and wakes the agent only for a repo's first
start-up recipe or an unseen trusted issue, comment or related PR change.
Already-seen issues stay quiet across unchanged ticks, including stuck,
code-pending, claimed and observe-mode issues waiting for a person. Busy agents
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
hours stuck, the owner tries a changed approach or asks for help, and the claim then expires. Related PRs are associated through same-repository closing references;
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

### GitHub API budget

Autopilot uses your own `gh` sign-in, so its GitHub calls use your hourly limit
(5,000 REST calls for a person). pdd counts each `gh` call that it makes, with
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

The counts stay on this machine, one file for each repository in
`~/.local/state/pdd/autopilot/github/`. `pdd autopilot status` shows one line
when there was a call in the last hour, for example:

```text
GitHub calls in the last hour: 212 (dependencies 120, claims 14, issues 60, pulls 18); 150 of 190 conditional reads were 304 (79%); REST limit 4210 of 5000 left until 17:05Z; budget normal: Autopilot on this machine used 61 of 1500 (30%).
```

A conditional read sends the ETag of the last reply. A `304` reply means that
nothing changed, and GitHub does not count it against the limit. The tick and the
dependency re-sync use conditional reads. The dependency re-sync keeps its ETags
and reply bodies in the same folder.

By default Autopilot on one machine uses at most 30% of the hourly REST limit,
and never the last 500 calls. Change this in `pdd.json`:

```json
{"autopilot":{"mode":"auto","trust":[],"github":{"share":30,"floor":500}}}
```

`share` is a whole percent from 1 to 100; `floor` is a whole number of calls. A
missing or invalid value uses the default. The budget counts the calls of all
Autopilot repositories on this machine in the last hour; a 304 reply does not
count. When Autopilot used its share, the tick runs the dependency re-sync at
most once an hour and uses its last result between. Heartbeats of live claims
continue. When GitHub reports fewer calls left than the floor, for REST or
GraphQL, the tick makes no GitHub call until the reset time; claims last 4
hours, so they do not expire in that time. Other machines and your own work on
the same login use the same limit; each machine keeps its own share. The
workflow start's claim check and other `pdd` commands do not wait for the
budget. To give Autopilot a limit of its own, see the design note
[A GitHub App token for Autopilot](autopilot-github-app-token.md).

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
It gives the cause, what it tried and what it needs as JSON on stdin:

```sh
pdd autopilot alert --issue 12 --kind usage-limit --input - <<'PDD_ALERT'
{"cause":"Codex usage limit; resets 2026-11-06T18:00Z","tried":"Paused issue 12 and continued other work","need":"More quota or another signed-in account"}
PDD_ALERT
```

Each message names the repository, the issue link, the cause, what Autopilot tried
and what it needs. Answer on the GitHub issue, so the answer stays with the run.
A usage limit or a resource failure is one incident for the repository and
machine, so a limit that blocks 5 runs sends one alert. A call for another
blocked issue adds that issue to the incident and sends nothing. The machine is
the name that Autopilot saved at its first start (this checkout's start first),
else the host name, so a host rename does not open a new incident. An access or spending decision, a product
decision or a stuck issue is one incident per issue. A repeat call sends
nothing for a delivered or unconfirmed alert, and sends again an alert that
failed or had no destination. `--update` sends a material change or the new
issue list. `--kind recovered` sends one recovery and closes the matching
alerts; give `"kind"` in the JSON to close only that incident. Every call and
its delivery result are recorded in
`~/.local/state/pdd/autopilot/alerts/`. Without a destination, the alert stays in
that record. `pdd autopilot status` adds one line when an alert was not delivered.
Work continues in both cases. A delivered `pdd autopilot alerts test` ends that
line for an older failed send, such as a failed recovery. An open alert that was
not delivered stays in the line until a later call sends it.

## Runs on a GitHub issue

| Command | What it does |
|---|---|
| `pdd workflow prove ISSUE --test COMMAND --expect TEXT [--timeout MIN]` | Fetch the selected base branch and run the supplied command on its merge-base with committed changed test files overlaid, then on committed head, in disposable snapshots. Both quoted text options are required; each phase has a limit of 10 minutes by default (`--timeout MIN` sets 1 to 120 minutes), 2-second termination grace and 1 MiB output cap. Save `old-code-proof.json` in the run folder. A successful comparison exits 0; failed or unavailable evidence exits 1 and never blocks publication. |
| `pdd workflow run NAME ISSUE [--agent codex\|claude\|gemini\|agy] [--base BRANCH] [--draft]` | Make a branch and a worktree for the issue, open the first chat in Herdr and return at once. `--origin`, `--decision-id` and `--outcome` supply optional metrics metadata. `--base BRANCH` selects an existing branch on origin; omitted means the repository default. An explicit base must fetch successfully before startup. PRs target the saved base, with PR 2 stacked on an open PR 1. Startup saves this terminal's `CODEX_HOME` (Codex), `CLAUDE_CONFIG_DIR` (Claude Code) or `GEMINI_CLI_HOME` (Gemini) for later chats. A leading `~` in it means your home folder. If that folder does not exist, `workflow run` stops before it starts anything |
| `pdd workflow list [--json]` | List the workflows that pdd finds, with their areas and gates: the PDD ones and [your own](workflows.md#make-your-own-workflow) |
| `pdd workflow status [ISSUE] [--all] [--cancelled] [--json]` | Show the area, the step, what the run waits for, and the PRs with their CI state. For a run with many Stories, also `Stories: N of M pass`, counted only from pdd's own `pdd test` results that `pdd workflow done` recorded (and `pdd workflow evidence` receipts); with none, `Stories: no pdd result (pdd:no-verdict)`. Without ISSUE, show all runs in this repo. In a run's worktree, show that run. With `--all`, or outside a Git repo, show every run on this machine: waiting for you first, then working, PR open, done. `--cancelled` also shows the hidden cancelled runs. `--json` gives the same list as data. It says "the chat stopped" only with evidence: Herdr sees no agent in the chat's tab, and the agent was seen running there or its own native session exists. Run `pdd workflow open ISSUE` to start it again. While a launch is not confirmed, it says "the chat is starting, not confirmed". Failed or unconfirmed startup/open and unavailable Herdr status show waiting with recovery advice. At a gate it says that the agent writes the gate message until the chat has asked you |
| `pdd workflow evidence ISSUE --summary FILE` | Record saved check JSON after verifying its selected source hash. Keeps completed steps, gates, approvals, chats and open PRs unchanged; no tests or external calls |
| `pdd workflow evidence-associate ISSUE --workspace PATH --stage current\|pr1 --test PATH...` | Register the producer workspace, evidence stage and selected tests for this run. Run it from the owned run worktree. Give one or more test paths after `--test`. Registration runs no checks and changes no workflow progress. See the [association contract](../prompts/cli/workflow-runner.prompt.md#workspace-evidence-association) |
| `pdd workflow view ISSUE` | Read-only review of the saved state, current gate, recorded approvals, pending decisions, PRs, check reports, Simulator links and current gate files. Never starts or resumes a chat, approves, or refreshes external state |
| `pdd workflow open ISSUE [AREA] [--new]` | Focus or resume the current chat, or the saved chat of a recorded earlier AREA. A chat that is still starting gets up to 30 seconds to show its agent; pdd sends no second launch or resume meanwhile, and then says "starting, not confirmed". `--new` closes and archives the current area's owned chat and starts one fresh session with the same run and agent setup, keeping progress and approvals. Earlier-area replacement and requests from an agent session or the pane being closed refuse. Repeat `--new` to resolve a pending replacement; status names its phase and resolving command, and cancel remains available |
| `pdd workflow approve [ISSUE] [--said WORDS] [--draft]` | Approve the ready gate and its draft prompts together with your chat words. Without ISSUE, select the current worktree or sole waiting run. Without --said use person terminal y/N; agent callers must ask then use --said. Strict mode requires a person terminal. |
| `pdd workflow changes ISSUE TEXT` | Send the text to the same chat. The chat revises. The gate stays open. Also use it to answer a question that the chat asked. At a gate, a plain approval such as "I approve" is not sent: pdd tells you to run `pdd workflow approve ISSUE` |
| `pdd workflow cancel ISSUE` | Close the run's chat tabs. Keep the worktree and the branch. A new `pdd workflow run` on the issue then starts fresh |

`pdd workflow open ISSUE` focuses or resumes the current area chat.

Ordinary open and exact-session resume use the chat's saved configuration folder. To select another existing Codex profile for one fresh current-area session, run `CODEX_HOME=/existing/work5 pdd workflow open ISSUE --new` from another terminal outside the agent session. A nonempty `CODEX_HOME`, including an inherited value, overrides the run's saved folder. Empty or unset values keep the saved selection. `~` expands to your home; relative paths resolve from this command's working directory. A missing folder or a regular file refuses before closing the owned chat. PDD selects the folder without checking its login or quota.

The fresh replacement keeps the run, worktree, progress, gates and approvals, and archives the original chat's session, configuration and first message. When PDD installs the replacement before launch, it saves the selected folder for later areas too; approving from another terminal does not select another account. A pending replacement stays pinned to its own folder on every `--new` retry, regardless of that retry's `CODEX_HOME`. Recovery can restore the original chat using its original profile. Plain open, historical AREA open and `changes` keep their recorded account and request target. This route starts a new native session; it does not move credentials or an existing session between profiles.

- NAME is `small-change`, `bug`, `feature`, `product` or the name of [your own workflow](workflows.md#make-your-own-workflow). pdd uses the skill `pdd-NAME`.
- ISSUE is the issue number in the current repo, worktrees included. If several repos match, use `owner/repo#N`. An issue has one active run. A second `pdd workflow run` on the same issue still starts: it marks the old active run replaced and names it (id, worktree, last activity) in one warning.
- `--base` takes a branch name such as `feature/checkout`. The branch must already be on `origin`. PDD fetches it and starts from that remote commit, preserves the repository default, and pushes only its new issue branches. A failed explicit fetch stops startup.
- `status` prints `pdd workflow view ISSUE` for passive review. The view links to the full issue, Stories and acceptance criteria, plan, prompts, test cases and Markdown gate notes. It identifies the current commit and uncommitted edits; recorded approvals cover only the saved gate and listed prompt hashes, never later edits. Missing links/files are stated plainly.
- The run folder is `.git/pdd/runs/N/` in your clone. See [workflows.md](workflows.md#the-run-folder).
- In Herdr, the session is `pdd`. Each verified common Git directory has its own repository workspace. Each run has a workspace such as `my-app#42 feature`, with one tab per area.
- With Claude Code, the first chat can ask once to trust the new worktree. `workflow run` prints a hint when your clone's folder is not trusted yet.
- In a terminal, `approve` without --said asks y/N and shows the repo, the issue and its title. From an agent chat, `approve` without --said asks the agent to ask the person, then run with --said and their words.
- Codex is the default agent. The chats start in full-access mode: Codex with `--dangerously-bypass-approvals-and-sandbox`, Claude Code with `--dangerously-skip-permissions`, Gemini with `--yolo`, Antigravity CLI (`--agent agy`) with `--dangerously-skip-permissions` and the run worktree trusted for that session only. An Antigravity chat also gets pdd's runs folder and worktrees folder with `--add-dir`, so it reads its start file with its own file tools. pdd finds a signed-in Antigravity CLI with `agy models`. Gemini CLI needs a paid Gemini API key, Vertex AI or Code Assist; with a free or Google One account, use `--agent agy`. PDD does not choose a model and does not change your agent's settings, sign-in or config.
- The first message of each chat gives the full path of this pdd. The agent uses it, so another `pdd` on its PATH does not matter.
- A Codex chat also gets `-c shell_environment_policy.set.PDD_BIN=…` and `-c shell_environment_policy.set.PDD_AGENT_SESSION="1"` for this launch only, so its commands keep both values when the Codex profile sets `inherit = "core"` or `"none"`. pdd does not change Codex settings. Limit: a `shell_environment_policy.include_only` list that leaves out a name still removes it.
- No command has a time limit. You can close the terminal at any time.
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

`pdd workflow run NAME ISSUE --adopt-corpus FILE` adopts an unchanged externally approved declared corpus for a fresh replay-evidence-enabled workflow; see [corpus adoption](replay-evidence.md#adopt-an-unchanged-approved-corpus).

## Tests on the PDD interpreter and prompt approval

| Command | What it does |
|---|---|
| `pdd test [PATH\|STORY...] [--lf] [--cache-clear] [--json] [--details] [--timeout MIN] [--max-calls N]` | Reuse complete unchanged passes from `.pdd/cache/test/`. `--lf` selects last-known failures, or the normal scope when none are recorded. `--cache-clear` discards the cache while retaining operand scope and takes precedence over `--lf`. Check Stories on the PDD interpreter with your gh login. With no STORY, test every Story. Send your Git files and wait for the checks, with one progress line every 30 s. Then print one table with a report link for each test, one `Prompt tests` line for each Story and, with two or more Stories, the overall line |
| `pdd test --read [BATCH\|CALL_ID] [--json] [--timeout MIN]` | Read saved results; a normal Check held for lint may continue its original checks. Other reads send no work |
| `pdd test --retry BATCH [--json] [--details] [--timeout MIN]` | Retry only confirmed unstarted checks with the saved source and call caps. Keeps completed, running and unknown jobs; changed source requires a fresh selected check |
| `pdd test --fill-hash` | Fill the hash of draft runtime interfaces. No network |
| `pdd test --fill-hash --compact` | Fill draft hashes and remove interface JSON formatting whitespace. Preserve values, strings, number spellings and prose. Approved and statusless files stay unchanged. No network |
| `pdd test --files [STORY...] [--app-map PATH]` | List the exact selected upload manifest and byte sizes. No network; `--app-map` previews the Simulator's app map |
| `pdd lint [STORY...] [--json] [--timeout MIN]` | Print local SVG layout warnings, then the server checks the format of the prompts, Stories and tests only, with 0 AI calls, and requests complete diagnostics and prints the problems the server reports. Requires network access; use it before a real check |
| `pdd lint --local [STORY...] [--json]` | Compare linked `.ui.svg` parts and labels with prompt prose locally; warning advice only, 0 AI calls and no network/authentication. Without Story names, inspect all Git-visible prompts, even with no PDD tests |
| `pdd test --screen URL --drawing PATH [--json]` | Compare the real page with its `.ui.svg` layout spec in installed headless Chrome/Chromium at the SVG viewport. No AI or interpreter call; missing/hidden parts, order or region differences fail |
| `pdd approve PROMPT [--said WORDS]` | Approve one prompt with your chat words, or terminal y/N without --said; strict mode requires a person terminal. |
| `pdd simulate [STORY] [--max-calls N] [--tab call\|screen\|terminal\|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent NAME]` | Open the Story in the PDD Simulator: make a Simulator link and open it in your browser. It ends in 24 hours. Short form: `pdd sim`. `--agent NAME` chooses a configured display name (quote spaces), or codex, claude or gemini. With terminal stdout or explicit `--agent`, it connects your agent and waits. Without either, it reads saved cases once and returns. `--no-wait` skips the connection. In a terminal, it adds each case saved in the Simulator to the Story's test file, and asks y/n when you click Approve on the page |
| `pdd simulate --stop [STORY]` | Stop the open Simulator link of a Story |

Ordinary `pdd test` reuses complete unchanged Story passes from the Git-ignored `.pdd/cache/test/` folder, showing their previous pass time and zero current AI calls. `pdd test --lf` selects the last known failures; a later attempt without a verdict keeps a failure selected until it passes. With no failures in the selected scope it uses the normal selection, including unchanged-pass reuse. Completed saved reads populate the cache after source verification, dated from the original batch start, never the later read time. `pdd test --cache-clear` discards prior local evidence and runs the normal selected scope; it takes precedence over `--lf`. It sends again and prints one stderr notice with the selected Story count; the interpreter may return a saved answer for the same key.

Reuse includes reached call targets, exact authored bytes, interpreter origin, call budget, pdd version, and the interpreter build and requested model reported by job answers. A missing identity or a pass older than seven days runs again. A different build or model observed during a run also runs the selected Stories initially skipped, with a reason; after a timeout or interrupt those rows are marked not sent. Reuse requires one clean record naming the same known build and model as the pass. A clean normal run starts after the previous sample, sees no record change during the run, and has only agreeing complete identities. Overlap, any read that writes the record (even after resending), an old or unknown writer, partial or mixed observations, or multiple stored values leaves doubt and runs. A later clean normal run can restore reuse. Before sending checks, a run saves an in-progress mark with its pid and start time. Another run's mark, live or dead, makes checks run. Live marks remain until their owners finish; dead marks are retired after forcing a run. A run can finish clean only while it still owns its mark and no other run has changed the record; it removes only its own mark. A failed sign-in removes its own mark but leaves doubt. All check sends share one ownership boundary: normal checks, saved-read continuations, retries and recovery hold their own mark from before the first send until their last send and observations finish. A retry retains ownership across its initial read. Reads and retries finish with doubt; direct callers with reuse disabled still coordinate their sends. Cache clear preserves every in-progress mark. A crash therefore costs one extra run, and overlap remains doubt until a later clean run. An all-skipped local run cannot discover an interpreter update without calls. Stories using the real clock or AI-played fakes run every time and say why; completely deterministic simulation bindings and fixed clock data permit reuse. Fixed clock values must be finite numbers or ISO 8601 date-time strings; labels such as `real 2026`, `now 1` and `1` run with the real-clock reason. Unknown resource kinds or actions run. Missing Story footprints, missing sources or malformed declarations report `runs again: resource declarations unavailable`; reuse can resume once evidence is complete; plain dependencies without an interface declare no resources. An expired pass reports `runs again: saved pass is older than seven days`. `CI` unset or set to the empty string, `0` or `false` permits ordinary reuse; every other value runs every selected Story. A saved pass at most seven days old still counts for prompt approval. Tracked cache files and caches copied without their external machine-local state are never reused. Damaged regular metadata heals after a completed run; its warning names `pdd test --cache-clear`. Dead-owner cache locks recover with one warning. Symlinked ancestors of `PDD_STATE_DIR` are accepted, but a final state-folder symlink is refused.

- A new simulation defaults to 400 calls. Both `pdd test --max-calls N` and `pdd simulate --max-calls N` accept 1 through 1000. Checks default to 12 calls per step, at least 18 and at most 1000. Choose at least three times your worst-case estimate.
- `pdd test` and saved-batch `pdd test --read BATCH` wait until every Story ends in every shell. Only `--timeout MIN` sets a caller limit. Use the shell tool's longest timeout or an exit-notifying background task; if stopped, run the printed recovery read once. Never poll every minute.
- pdd has no default local job limit: all selected checks, remote lint and simulation setup proceed without a local-slot wait. Set `PDD_MAX_JOBS` to a positive safe decimal integer to share that cap across repositories and worktrees among local pdd processes that set it; capped jobs wait their turn and show how many jobs are ahead. An invalid value warns once per command and uses no cap. When the interpreter is busy and confirms that your job did not start, pdd waits and tries again until your wait ends. After a saved lint passes, `--read` can start the original checks that were waiting for it, using the same files, owner and call limits. `--retry BATCH` retries checks confirmed never started, using the same files after lint passes. See [waiting for capacity](lint-capacity.md) for recovery and restart handling.
- Check source uploads use at most 8 unanswered POSTs at once per pdd process. Set `PDD_MAX_UPLOADS` to a positive safe decimal integer (leading zeros are allowed); invalid values warn once and use 8. Each answered POST or transport failure frees its place while server jobs continue running; GET reads use no upload places. This laptop upload setting protects your own connection from the 90-second POST timeout, and is not a server limit. It uses no shared job-slot queue.
- Offline-only work uses `pdd lint --local`, local authoring review, `pdd test --files` and `pdd test --fill-hash`. It is not a server lint pass. Factories can bind through interface v2 instances; ports and SQL, blob and compute resources cover declared simulation. Native effects stay unbound; see [Interpreter boundaries](runtime-boundaries.md).
- Running `pdd simulate STORY` for a paused simulation explicitly reopens the same session before showing its link. Its original expiry and remaining call allowance stay in force; an unconfirmed reopen is nonzero.
- A `draft` prompt can be checked, and its result is marked DRAFT. A DRAFT pass is not an approval.
- With no test file, `pdd test` says `No tests found` and lists why, for example a Story with no `tests/<story>.json`, a `.json` file in a test folder that matches no Story, or a prompt with no Runtime interface block.
- A GitHub login that is not invited gets one line: `Your GitHub login NAME is not on the PDD interpreter invite list yet. Ask the PDD team to add you.` A GitHub account without PDD Cloud access gets the server's sign-up line (sign up at https://promptdriven.ai/login). When PDD Cloud cannot check the account, pdd says at once `PDD Cloud could not confirm your access. Try again in a minute.` A pdd that is too old gets `Please update pdd: …`. All of these exit with code 5.
- The interpreter address is set in one place in pdd. You do not need to set it.

Linked `.ui.svg` drawings specify the screen's parts, words, spatial order, ids and named state. Local lint reports unmatched controls, labels and unspecified layout regions; a generic data-field mention does not describe a score box or status bar. Its warnings do not change exit 0 and do not certify semantic or visual agreement. `--local` belongs to `pdd lint`; it mixes only with Story names and `--json`.

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
| `pdd workflow done STEP [--summary TEXT] [--skipped REASON]` | Record a finished step. `check`, `try` and `verify` also record pdd's own latest `pdd test`, `pdd lint` and `pdd workflow prove` results, or warn that pdd has none; the summary stays an agent note. `--skipped REASON` records that the step was skipped, and why. Print the next instruction: the next step, the gate, or "pdd opens the PR now". After the last step of an area with a PR gate, push the branch and open the PR |
| `pdd workflow ask QUESTION` | Show the person that the chat waits for an answer in the middle of a step. `status` then says "waiting for you" with the question |

The agent runs these from the run's worktree. pdd finds the run from that folder. You do not run them yourself.

## Other commands

| Command | What it does |
|---|---|
| `pdd`, `pdd --help`, `pdd -h`, `pdd help` | Show the commands and the full paths of the installed Prompting guide and RUNBOOK |
| `pdd help prompting` | Show how to write a prompt, a Story and its test, which commands check them, and the full paths of the Prompting guide and RUNBOOK |
| `pdd --version` | Print the version, `0.1.20`. When the PDD skills that your agent finds are older, also print the update command on stderr |
| `pdd completion bash\|zsh` | Print a shell completion script. It does not change your shell files |
| `pdd jobs` | List active slots and waiting interpreter jobs on this machine, including kind, PID, age and request IDs. Local and read-only; no repository, authentication or interpreter call |

## Run from a source checkout

From a clone of this repository, run the CLI without a global install:

```sh
node bin/pdd.mjs --help
node bin/pdd.mjs --version
npm test
```

You need Node.js 22 or newer. The package has no dependencies and no build step. See [CONTRIBUTING.md](../CONTRIBUTING.md).

Check, remote lint and simulation setup use [local bookkeeping and capacity waiting](lint-capacity.md); they share a local slot cap when `PDD_MAX_JOBS` is set. Local waiting, maintenance and interpreter queue time all use the existing caller wait. `pdd simulate` uses one five-minute setup allowance for lint and the rest of setup in every shell; it adds no timeout flag.

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
| `pdd product start RUN [--no-run] [--agent codex\|claude\|gemini\|agy]` | Find or create the run's issue once, then start a normal feature run; `--no-run` only finds or creates the issue |

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

Without `--said`, a person at a normal terminal answers y/N. The question lists the gate and its drafts; one answer approves them together. `pdd approve PROMPT` still approves only one prompt. Agent, non-TTY and current Herdr chat-pane callers must ask the person, then relay the reply with the safe form above. Native Herdr evidence never authorizes approval by itself.

Workflow approval reads `pdd.json` from the main checkout (`sourceRoot`), outside the agent's run worktree. Standalone `pdd approve` reads it from the Git root of the current checkout. `"strict_approvals": true` permits only a person at a terminal and refuses `--said`. Absent or false keeps easy mode. Agents never edit approval fields or decide expected values. Records retain the invoking actor, time, route, exact words and prompt path/hash. PRs show matching approvals safely quoted. Approval of PR 1 does not approve the later code-or-stop gate.

`pdd workflow ack REQUEST_ID --summary TEXT` records the agent’s uptake of a delivered change request from its active run worktree. The first note and time are retained on repeat calls. Delivery and this explicit agent claim do not prove the request was fully addressed. Status shows delivered requests still awaiting uptake; done warns without blocking progress.

## Metrics

- `pdd metrics [--json] [--date YYYY-MM-DD | --snapshot ID] [--timezone IANA] [--at UTC] [--expected-source ID...]`
- `pdd metrics export FILE [--timezone IANA]`
- `pdd metrics import FILE`
- `pdd metrics record FILE`

`pdd graph` reads the saved dependency graph; `pdd graph --open` opens its viewer. Use `pdd graph --issue N` to select an issue, or `pdd graph --open --issue N --repo OWNER/REPO` to select a repository explicitly.

`pdd dependencies prepare [--issue N]` prepares a coordinator packet. `pdd dependencies complete --input -` reads a structured completion from stdin. `pdd workflow yield N` hands off automatic capacity after the current worker has stopped.

`pdd workflow park --reason TEXT` records an automatic stop from its existing run worktree without releasing its claim or treating the worker as done.
