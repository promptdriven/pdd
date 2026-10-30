# CLI reference

This page lists every command of pdd 0.1.10, as `pdd --help` shows it. A test (`test/docs-commands.test.mjs`) checks that each command form of the help is on this page.

You need the pdd command only for runs with PRs, for `pdd check`, `pdd try` and `pdd approve`. Install the skills with `npx skills add promptdriven/pdd` (add `-g` for all your projects), and set up a repo with the `pdd-setup` skill in your agent. For agent-driven Try runs, use `pdd mcp`. Then use a PDD skill: `pdd-feature`, `pdd-bug`, `pdd-small-change` or `pdd-prompting`. Call a skill with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code (or ask for it by name). See [Install](USAGE.md#2-install).

## Set up a repo

| Command | What it does |
|---|---|
| `pdd setup` | Install the five [PDD skills](USAGE.md#4-the-pdd-skills) when they are missing, and say where. Then add or update the short PDD block (7 lines, between `<!-- pdd:start -->` and `<!-- pdd:end -->`) in `CLAUDE.md` of this folder, else in `AGENTS.md`. If neither exists, make `AGENTS.md`. A second run changes nothing |

`pdd setup` copies the skills to `~/.agents/skills` (Codex) and `~/.claude/skills`, or `$CLAUDE_CONFIG_DIR/skills` when it is set (Claude Code). If `npx skills` already installed them, it copies nothing. When the skills it finds are older than this pdd, or differ from its skills, it says so and prints the command that updates them: `npx skills add promptdriven/pdd#alpha -g -a codex -a claude-code -y`, without `-g` for a copy in the project. After an update of the pdd command, it replaces an older copy that has the `.pdd-skill.json` marker. It never touches a copy without the marker, or a symlink. No other pdd command copies skills. The `pdd-setup` skill writes the same block in a chat. Run it in the top folder of the repo.

Setup previews the exact MCP configuration changes for the Codex, Claude Code and Gemini agents it finds, then asks once (y/N). Only `y` writes those changes, including the approval setting for this Codex server. Registrations pin this running pdd executable, so another installation earlier on PATH cannot receive its tools. Other configuration is preserved. Codex uses `$CODEX_HOME/config.toml` (default `~/.codex/config.toml`) and the `mcp_servers.pdd` entry with `default_tools_approval_mode = "approve"`. Claude Code uses the `mcpServers.pdd` entry in its configuration; Gemini uses `mcpServers.pdd` in `~/.gemini/settings.json` with server trust. Each entry runs `pdd mcp`. A conflicting existing entry is preserved and reported.

Setup also reports the running Alpha executable and version, the `pdd` paths in order, and which path and version a plain `pdd` selects. A PATH conflict report includes the absolute Alpha command and explains that environment activation, such as conda, must come before correcting PATH. It keeps other installations. `--version` preserves its version-only stdout; PATH diagnostics go to stderr. `workflow run` gives a one-line warning when another pdd comes first.

## Runs on a GitHub issue

| Command | What it does |
|---|---|
| `pdd workflow prove ISSUE --test COMMAND --expect TEXT` | Fetch the selected base branch and run the supplied command on its merge-base with committed changed test files overlaid, then on committed head, in disposable snapshots. Both quoted text options are required; each phase has a fixed 120-second limit, 2-second termination grace and 1 MiB output cap. Save `old-code-proof.json` in the run folder. A successful comparison exits 0; failed or unavailable evidence exits 1 and never blocks publication. |
| `pdd workflow run NAME ISSUE [--agent codex\|claude] [--base BRANCH]` | Make a branch and a worktree for the issue, open the first chat in Herdr and return at once. `--base BRANCH` selects an existing branch on origin; omitted means the repository default. An explicit base must fetch successfully before startup. PRs target the saved base, with PR 2 stacked on an open PR 1. Every chat of the run uses the `CODEX_HOME` (Codex) or `CLAUDE_CONFIG_DIR` (Claude Code) of this terminal. A leading `~` in it means your home folder. If that folder does not exist, `run` stops before it starts anything |
| `pdd workflow list [--json]` | List the workflows that pdd finds, with their areas and gates: the PDD ones and [your own](workflows.md#make-your-own-workflow) |
| `pdd workflow status [ISSUE] [--all] [--cancelled] [--json]` | Show the area, the step, what the run waits for, and the PRs with their CI state. For a run with many Stories, also `Stories: N of M pass`. Without ISSUE, show all runs in this repo. In a run's worktree, show that run. With `--all`, or outside a Git repo, show every run on this machine: waiting for you first, then working, PR open, done. `--cancelled` also shows the hidden cancelled runs. `--json` gives the same list as data. It says "the chat stopped" when no agent runs in the chat: run `pdd workflow open ISSUE` to start it again. Failed or unconfirmed startup/open and unavailable Herdr status show waiting with recovery advice. At a gate it says that the agent writes the gate message until the chat has asked you |
| `pdd workflow evidence ISSUE --summary FILE` | Record saved check JSON after verifying its selected source hash. Keeps completed steps, gates, approvals, chats and open PRs unchanged; no tests or external calls |
| `pdd workflow view ISSUE` | Read-only review of the saved state, current gate, recorded approvals, pending decisions, PRs, runtime reports, Try links and current gate files. Never starts or resumes a chat, approves, or refreshes external state |
| `pdd workflow open ISSUE` | Show the current chat of the run. If the chat ended, resume it in its tab |
| `pdd workflow approve [ISSUE]` | Approve the open gate. The next area starts in a new chat. Before PR 1, this approves what you tried, and pdd opens PR 1. At the code question of `feature` and `bug`, this makes the code PR, also later. Without ISSUE, approve the run of the current worktree, or else the one run in this repo that waits for a person. In a terminal that looks like an agent's (for example Claude Code's `!` prefix, which sets `CLAUDECODE=1`), pdd cannot ask y/N: run it in a normal terminal, or answer the gate question in the chat. While PR 1 has a draft prompt, pdd does not make the code PR: it prints the `pdd approve` line to run first |
| `pdd workflow changes ISSUE TEXT` | Send the text to the same chat. The chat revises. The gate stays open. Also use it to answer a question that the chat asked. At a gate, a plain approval such as "I approve" is not sent: pdd tells you to run `pdd workflow approve ISSUE` |
| `pdd workflow cancel ISSUE` | Close the run's chat tabs. Keep the worktree and the branch. A new `run` on the issue then starts fresh |

- NAME is `small-change`, `bug`, `feature`, `product` or the name of [your own workflow](workflows.md#make-your-own-workflow). pdd uses the skill `pdd-NAME`.
- ISSUE is the issue number in the current repo, worktrees included. If several repos match, use `owner/repo#N`. An issue can have only one active run. `run` refuses a second one.
- `--base` takes a branch name such as `feature/checkout`. The branch must already be on `origin`. PDD fetches it and starts from that remote commit, preserves the repository default, and pushes only its new issue branches. A failed explicit fetch stops startup.
- `status` prints `pdd workflow view ISSUE` for passive review. The view links to the full issue, Stories and acceptance criteria, plan, prompts, test cases and Markdown gate notes. It identifies the current commit and uncommitted edits; recorded gate approvals do not certify later edits or approve prompts. Missing links/files are stated plainly.
- The run folder is `.git/pdd/runs/N/` in your clone. See [workflows.md](workflows.md#the-run-folder).
- In Herdr, the session is `pdd`. Each repo has a workspace with its name. Each run has a tab such as `my-app#42 feature`.
- With Claude Code, the first chat can ask once to trust the new worktree. `run` prints a hint when your clone's folder is not trusted yet.
- In a terminal, `approve` asks y/N and shows the repo, the issue and its title. From an agent chat, `approve` works only when the person's own message after the gate is in that chat.
- Codex is the default agent. The chats start in full-access mode: Codex with `--dangerously-bypass-approvals-and-sandbox`, Claude Code with `--dangerously-skip-permissions`. PDD does not choose a model and does not change your agent's settings, sign-in or config.
- The first message of each chat gives the full path of this pdd. The agent uses it, so another `pdd` on its PATH does not matter.
- No command has a time limit. You can close the terminal at any time.
- pdd never merges.

## Runtime checks and prompt approval

| Command | What it does |
|---|---|
| `pdd check [STORY...] [--json] [--details] [--timeout MIN] [--max-calls N]` | Check Stories on the PDD runtime with your gh login. Send your Git files and wait for the checks, with one progress line every 30 s. Then print one table with a report link for each test, one `Runtime check` line for each Story and, with two or more Stories, the overall line |
| `pdd check --read [BATCH|CALL_ID] [--json] [--timeout MIN]` | Read saved results; a normal Check held for lint may continue its original checks. Other reads send no work |
| `pdd check --retry BATCH [--json] [--details] [--timeout MIN]` | Retry only confirmed unstarted checks with the saved source and call caps. Keeps completed, running and unknown jobs; changed source requires a fresh selected check |
| `pdd check --fill-hash` | Fill the hash of draft runtime interfaces. No network |
| `pdd check --files [STORY...] [--app-map PATH]` | List the exact selected upload manifest and byte sizes. No network; `--app-map` previews a Try map |
| `pdd check --lint [STORY...] [--json] [--timeout MIN]` | Print local SVG layout warnings, then the server checks the format of the prompts, Stories and tests only, with 0 AI calls, and requests complete diagnostics and prints the problems the server reports. Requires network access; use it before a real check |
| `pdd check --lint --local [STORY...] [--json]` | Compare linked `.ui.svg` parts and labels with prompt prose locally; warning advice only, 0 AI calls and no network/authentication. Without Story names, inspect all Git-visible prompts, even with no runtime tests |
| `pdd check --screen URL --drawing PATH [--json]` | Compare the real page with its `.ui.svg` layout spec in installed headless Chrome/Chromium at the SVG viewport. No AI/runtime call; missing/hidden parts, order or region differences fail |
| `pdd approve PROMPT` | Show the prompt's runtime interface in plain words and its text changes since the last approved version, then ask y/n. On `y`, set it to `approved` and fill its hash. For a person at a terminal only |
| `pdd try [STORY] [--max-calls N] [--tab call\|screen\|terminal\|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent NAME]` | Make a Try link and open it in your browser. It ends in 24 hours. `--agent NAME` chooses a configured display name (quote spaces), or codex, claude or gemini. With terminal stdout or explicit `--agent`, it connects your agent and waits. Without either, it reads saved cases once and returns. `--no-wait` skips the connection. In a terminal, it adds each case saved on the Try page to the Story's test file, and asks y/n when you click Approve on the page |
| `pdd try --stop [STORY]` | Stop the open Try link of a Story |

- A new Try defaults to 400 calls. Both `pdd check --max-calls N` and `pdd try --max-calls N` accept 1 through 1000. Checks default to 12 calls per step, at least 18 and at most 1000. Choose at least three times your worst-case estimate.
- In a terminal, `pdd check` waits until every check ends. Without a terminal (an agent), it waits at most 90 seconds, then prints the table and `Still running. Read the results later with: pdd check --read BATCH`. `--timeout MIN` sets the limit in both cases.
- Local pdd processes share a runtime job limit (`PDD_MAX_JOBS`, default 4) across repositories and worktrees. Checks, remote lint and Try setup wait their turn. When the runtime is busy and confirms that your job did not start, pdd waits and tries again until your wait ends. It shows how many jobs are ahead of you. After a saved lint passes, `--read` can start the original checks that were waiting for it, using the same files, owner and call limits. `--retry BATCH` retries checks confirmed never started, using the same files after lint passes. See [waiting for capacity](lint-capacity.md) for recovery and restart handling.
- Offline-only work uses `pdd check --lint --local`, local authoring review, `pdd check --files` and `pdd check --fill-hash`. It is not a server lint pass. Factories can bind through interface v2 instances; ports and SQL, blob and compute resources cover declared simulation. Native effects stay unbound; see [Runtime boundaries](runtime-boundaries.md).
- Running `pdd try STORY` for a paused Try explicitly reopens the same session before showing its link. Its original expiry and remaining call allowance stay in force; an unconfirmed reopen is nonzero.
- A `draft` prompt can be checked, and its result is marked DRAFT. A DRAFT pass is not an approval.
- With no test file, `pdd check` says `No tests found` and lists why, for example a `tests/*.json` file without the PDD `schema_version`, or a prompt with no Runtime interface block.
- A GitHub login that is not invited gets one line: `Your GitHub login NAME is not on the PDD runtime invite list yet. Ask the PDD team to add you.` A GitHub account without PDD Cloud access gets the server's sign-up line (sign up at https://promptdriven.ai/login). When PDD Cloud cannot check the account, pdd says at once `PDD Cloud could not confirm your access. Try again in a minute.` A pdd that is too old gets `Please update pdd: …`. All of these exit with code 5.
- The runtime address is set in one place in pdd. You do not need to set it.

Linked `.ui.svg` drawings specify the screen's parts, words, spatial order, ids and named state. Local lint reports unmatched controls, labels and unspecified layout regions; a generic data-field mention does not describe a score box or status bar. Its warnings do not change exit 0 and do not certify semantic or visual agreement. `--local` requires `--lint`; it mixes only with Story names and `--json`.

For a built screen, serve the app in the state shown by its drawing and run, for example, `pdd check --screen http://127.0.0.1:8080/ --drawing prompts/views/active__stacked.ui.svg`. Set `PDD_CHROME_PATH` to a Chrome/Chromium executable when discovery needs help. The command checks every visible text occurrence and id, including numeric values, at the SVG viewport; metadata, hidden and context-only drawing regions are excluded. It accepts center differences of at most 15% per viewport axis and requires the same spatial order of separated parts. It prints a `Screen vs drawing` table for the code PR; retain any stricter accepted visual comparator. Exit codes are 0 for pass, 1 for mismatch, 2 for invalid input and 5 when browser/navigation execution fails. `--screen` requires `--drawing`, accepts only `--json` alongside them and takes no Story names. JSON includes the comparison rows and `exit_code`.

See [Check prompts on the PDD runtime](USAGE.md#7-check-prompts-on-the-pdd-runtime) for the exit codes, `pdd check --help` and `pdd try --help` for the options, and `RUNBOOK.md` for the file formats.

The Try page's agent fills the fields directly when supported. It runs the action only when you explicitly ask, in your own words; otherwise you press Run. Actions use the Try budget. Older pages keep manual Fill fields and Run.

## Try tools for your agent

| Command | What it does |
|---|---|
| `pdd mcp` | Start the stdio MCP server for the current repository; select the Story through tool input. Your agent can open a Try, inspect its state, run input, check the result against the Story and save a case |

The tools are `try_open`, `try_state`, `try_run`, `try_check` and `try_save_case`. Use them when the person asks to try behavior. Runs count against the Try budget and appear on its page. Saved results are separate recorded cases with exact starting data. Complete missing Story coverage before `pdd check`; observations need review and are never approved expected values. MCP protocol messages use stdout; progress and diagnostics use stderr.

## Used by the agent

| Command | What it does |
|---|---|
| `pdd workflow done STEP [--summary TEXT]` | Record a finished step. Print the next instruction: the next step, the gate, or "pdd opens the PR now". After the last step of an area with a PR gate, push the branch and open the PR |
| `pdd workflow ask QUESTION` | Show the person that the chat waits for an answer in the middle of a step. `status` then says "waiting for you" with the question |

The agent runs these from the run's worktree. pdd finds the run from that folder. You do not run them yourself.

## Other commands

| Command | What it does |
|---|---|
| `pdd`, `pdd --help`, `pdd -h`, `pdd help` | Show the commands |
| `pdd --version` | Print the version, `0.1.10`. When the PDD skills that your agent finds are older, also print the update command on stderr |
| `pdd completion bash\|zsh` | Print a shell completion script. It does not change your shell files |
| `pdd jobs` | List active slots and waiting runtime jobs on this machine, including kind, PID, age and request IDs. Local and read-only; no repository, authentication or runtime call |

## Run from a source checkout

From a clone of this repository, run the CLI without a global install:

```sh
node bin/pdd.mjs --help
node bin/pdd.mjs --version
npm test
```

You need Node.js 22 or newer. The package has no dependencies and no build step. See [CONTRIBUTING.md](../CONTRIBUTING.md).

Check, remote lint and Try setup share [local slots and capacity waiting](lint-capacity.md). Local waiting, maintenance and runtime queue time all use the existing caller wait. Try keeps its five-minute setup allowance and 90-second agent lint wait; it adds no timeout flag.

`pdd try [STORY] --cli [--shell] [--max-calls N] [--new]`

Use the program in your own terminal. Copy the printed PATH line or run the absolute shim path.

`pdd try [STORY] --serve [PORT] [--max-calls N] [--new]`

Serve the Story on localhost (default 8080).

`pdd try --save-last`

Append the last command and its observed output to its original Story test file.

Story counts use the newest source-compatible evidence across check, verify and saved evidence records. Unknown results stay unknown. Source changes invalidate old counts. To refresh counts without rerunning workflow steps, save `pdd check --read BATCH --json` outside the repository, then run `pdd workflow evidence ISSUE --summary /path/to/check.json`. The JSON must retain its repository, selected test paths, Story lines and source SHA. This records saved evidence, not new execution or approval.

An explicit `pdd check --lint` that is still queued/running exits 3 and prints its saved read command; exit 0 means validation finished successfully. The all-Story cost estimate includes entry executions, declared saved-data operations and nested prompt-call allowances. Conditional operations may use fewer calls; `--max-calls` remains the hard cap.

Virtual CLI and HTTP startup print `Try AI usage` on stderr. Each virtual CLI command appends its usage line to stderr, keeping program stdout and exit status intact. It distinguishes calls for this command, total used and remaining in this Try, and the session cap. Unknown counters stay unknown. Named HTTP routes carry `x-pdd-ai-calls`, `x-pdd-try-used`, `x-pdd-try-remaining`, `x-pdd-try-cap`, and `x-pdd-usage-source` headers; response bodies and program statuses stay intact. `runtime` identifies a confirmed call receipt; `last-known` identifies cached session allowance on a local zero-call response such as an unmatched route. Session allowance is separate from an account or tester allowance. Usage reads spend no model calls and never repeat commands.

`pdd check --read CALL_ID` reads an authenticated owner call receipt by UUID without sending the operation again. Interrupted Try CLI commands print this exact recovery command. See [module binding coverage](runtime-bindings.md) for selected Story coverage and unbound reasons.

`workflow prove` leaves the saved run base unchanged. Fresh worktrees have no installed dependencies; include required installation in `--test`. The command inherits your environment and network access, and shares the repository’s Git refs and config, just like tests run by hand. Interrupting with SIGINT, SIGTERM or SIGHUP stops the process group and removes both snapshots before exit 130, 143 or 129. Only positively owned stale proof worktrees with inactive owners are recovered; unrelated worktrees are left alone.

Remote lint shares the Check caller wait, including `--timeout`, with no separate lint limit. Recovery of a saved lint-held Check has a fresh finite wait (`--timeout`, otherwise 90 seconds), retains the saved runtime origin and dispatches each original check at most once. Standalone lint reads never send checks.

Before sending work, pdd asks whether the runtime has room. During announced maintenance, it shows the end time and reason, then waits within the same deadline. If the runtime does not offer this information, pdd uses the reply to the submission instead. A queued job keeps its ID while pdd shows its place. If the runtime confirms that a check ended because the service restarted, pdd tries that check once more and saves both attempts and their usage. If a reply is lost or the outcome is uncertain for another reason, pdd reads the original job without sending it again.

## Shared records

| Command | What it does |
|---|---|
| `pdd contracts` | List shared records in working files, their prompt/test users, changed records and Stories needing a new check. Local; no runtime calls |
| `pdd contracts --check [--json]` | Check supported schemas, references, eligible copy drift, world writers and seed values locally; 0 complete, 4 definite problem, 5 unavailable validation or I/O, 2 syntax/no repository |
| `pdd contracts sync [--write]` | Preview replacing inline copies with references. `--write` applies unambiguous proposals and adopts the shared shape; ambiguous matches warn and stay unchanged |

`pdd contracts --check` writes nothing and reads no Check history. It cannot be
combined with `sync` or `--write`. Both world files may be absent; if either
`contracts/world.md` or `contracts/seed-world.json` exists, both are required.
The first Key/Writer or Path/Writer ownership table may omit Schema. Only explicit
schema links validate seed values. Key tables require every top-level seed key
to have a declaration; Path tables check exact declared ownership without inferred
seed coverage or template matching. Complete writer labels may contain commas;
parent and child paths may have different writers. Identical declarations
coalesce, while conflicting labels or explicit schema mappings for the same
exact path fail. JSON schema-map leaves validate without implicitly authorizing
copy agreement. Seed data is never mistaken for schemas. Unrelated JSON skips;
unjudged value patterns and precision that cannot be checked without rounding
report validation unavailable with a location. Ordinary finite decimal
bounds and enum values can be checked locally; uncertainty never produces a false pass.

Use `{"$contract":"contracts/phone-server.md#order_in"}` in a Runtime schema.
The Markdown section has a `### order_in` heading and one JSON code block;
headings with spaces also accept their normal heading fragment. JSON records use
`{"$contract":"contracts/records.json#/defs/order"}`. Local `title` and
`description` may accompany a reference; other constraint siblings are refused.
Use `"initial_world":{"$seed":"contracts/seed-world.json","set":{"/orders":[]}}`
for a shared starting world. Paths are relative to the repository root. Set
pointers apply in written order to a fresh world and may add an object's final
key; their parents must exist. Expected values and literal inputs stay literal.

Check, lint and Try use expanded schemas/worlds, including uploaded bytes. A
missing target stops before upload. Real schema `$ref` remains refused. Explicit
`pdd check --lint` skips inline schemas with fewer than three fields. It advises
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
| `pdd product status [--json]` | Count Stories by part and slice from current saved checks; identify stale results and remote evidence from PRs. Makes no runtime calls |
| `pdd product next` | Show ready planned runs and their start commands; parallel starts are optional |
| `pdd product start RUN [--no-run] [--agent codex\|claude]` | Find or create the run's issue once, then start a normal feature run; `--no-run` only finds or creates the issue |

See [Build a whole product](build-a-whole-product.md).

For `pdd contracts --check`, world tables accept Key or Path and Writer columns;
Schema is optional. Ownership is per exact path, with the complete Writer cell
as its label. Non-schema JSON files are skipped in one summary. Inline object
copies need at least three properties; differing copies need an eligible shared
record with at least four properties. Smaller copies are not compared. Only
declared records supply copy authorities; incidental nested schemas do not.
`--json` requires `--check` and prints counts, skipped files and diagnostics as
one JSON object with the same exit code as text output.
