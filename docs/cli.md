# CLI reference

This page lists every command of pdd 0.1.7, as `pdd --help` shows it. A test (`test/docs-commands.test.mjs`) checks that each command form of the help is on this page.

You need the pdd command only for runs with PRs, for `pdd check`, `pdd try` and `pdd approve`. Install the skills with `npx skills add promptdriven/pdd` (add `-g` for all your projects), and set up a repo with the `pdd-setup` skill in your agent. Then use a PDD skill: `pdd-feature`, `pdd-bug`, `pdd-small-change` or `pdd-prompting`. Call a skill with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code (or ask for it by name). See [Install](USAGE.md#2-install).

## Set up a repo

| Command | What it does |
|---|---|
| `pdd setup` | Install the five [PDD skills](USAGE.md#4-the-pdd-skills) when they are missing, and say where. Then add or update the short PDD block (7 lines, between `<!-- pdd:start -->` and `<!-- pdd:end -->`) in `CLAUDE.md` of this folder, else in `AGENTS.md`. If neither exists, make `AGENTS.md`. A second run changes nothing |

`pdd setup` copies the skills to `~/.agents/skills` (Codex) and `~/.claude/skills`, or `$CLAUDE_CONFIG_DIR/skills` when it is set (Claude Code). If `npx skills` already installed them, it copies nothing. When the skills it finds differ from the skills of this pdd, it says so and prints the command that updates them: `npx skills update -g`, or `npx skills update -p` for a copy in the project. After an update of the pdd command, it replaces an older copy that has the `.pdd-skill.json` marker. It never touches a copy without the marker, or a symlink. No other pdd command copies skills. The `pdd-setup` skill writes the same block in a chat. Run it in the top folder of the repo.

## Runs on a GitHub issue

| Command | What it does |
|---|---|
| `pdd workflow run NAME ISSUE [--agent codex\|claude] [--base BRANCH]` | Make a branch and a worktree for the issue, open the first chat in Herdr and return at once. `--base BRANCH` selects an existing branch on origin; omitted means the repository default. An explicit base must fetch successfully before startup. PRs target the saved base, with PR 2 stacked on an open PR 1. Every chat of the run uses the `CODEX_HOME` (Codex) or `CLAUDE_CONFIG_DIR` (Claude Code) of this terminal. A leading `~` in it means your home folder. If that folder does not exist, `run` stops before it starts anything |
| `pdd workflow list [--json]` | List the workflows that pdd finds, with their areas and gates: the PDD ones and [your own](workflows.md#make-your-own-workflow) |
| `pdd workflow status [ISSUE] [--all] [--cancelled] [--json]` | Show the area, the step, what the run waits for, and the PRs with their CI state. For a run with many Stories, also `Stories: N of M pass`. Without ISSUE, show all runs in this repo. In a run's worktree, show that run. With `--all`, or outside a Git repo, show every run on this machine: waiting for you first, then working, PR open, done. `--cancelled` also shows the hidden cancelled runs. `--json` gives the same list as data. It says "the chat stopped" when no agent runs in the chat: run `pdd workflow open ISSUE` to start it again. Failed or unconfirmed startup/open and unavailable Herdr status show waiting with recovery advice. At a gate it says that the agent writes the gate message until the chat has asked you |
| `pdd workflow open ISSUE` | Show the current chat of the run. If the chat ended, resume it in its tab |
| `pdd workflow approve [ISSUE]` | Approve the open gate. The next area starts in a new chat. Before PR 1, this approves what you tried, and pdd opens PR 1. At the code question of `feature` and `bug`, this makes the code PR, also later. Without ISSUE, approve the run of the current worktree, or else the one run in this repo that waits for a person. In a terminal that looks like an agent's (for example Claude Code's `!` prefix, which sets `CLAUDECODE=1`), pdd cannot ask y/N: run it in a normal terminal, or answer the gate question in the chat. While PR 1 has a draft prompt, pdd does not make the code PR: it prints the `pdd approve` line to run first |
| `pdd workflow changes ISSUE TEXT` | Send the text to the same chat. The chat revises. The gate stays open. Also use it to answer a question that the chat asked. At a gate, a plain approval such as "I approve" is not sent: pdd tells you to run `pdd workflow approve ISSUE` |
| `pdd workflow cancel ISSUE` | Close the run's chat tabs. Keep the worktree and the branch. A new `run` on the issue then starts fresh |

- NAME is `small-change`, `bug`, `feature` or the name of [your own workflow](workflows.md#make-your-own-workflow). pdd uses the skill `pdd-NAME`.
- ISSUE is the issue number in the current repo, worktrees included. If several repos match, use `owner/repo#N`. An issue can have only one active run. `run` refuses a second one.
- `--base` takes a branch name such as `round3/workflow-base`. The branch must already be on `origin`. PDD fetches it and starts from that remote commit, preserves the repository default, and pushes only its new issue branches. A failed explicit fetch stops startup.
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
| `pdd check --read [BATCH] [--json]` | Show saved check results again. Sends no check |
| `pdd check --fill-hash` | Fill the hash of draft runtime interfaces. No network |
| `pdd check --files [STORY...] [--app-map PATH]` | List the exact selected upload manifest and byte sizes. No network; `--app-map` previews a Try map |
| `pdd check --lint [STORY...] [--json]` | The server checks the format of the prompts, Stories and tests only, with 0 AI calls, and shows every problem at once. Use it before a real check |
| `pdd approve PROMPT` | Show the prompt's runtime interface in plain words and its text changes since the last approved version, then ask y/n. On `y`, set it to `approved` and fill its hash. For a person at a terminal only |
| `pdd try [STORY] [--tab call\|screen\|terminal\|world] [--app-map PATH] [--new] [--no-open] [--no-wait]` | Make a Try link and open it in your browser. It ends in 24 hours. In a terminal, it waits: it adds each case saved on the Try page to the Story's test file, and asks y/n when you click Approve on the page |
| `pdd try --stop [STORY]` | Stop the open Try link of a Story |

- In a terminal, `pdd check` waits until every check ends. Without a terminal (an agent), it waits at most 90 seconds, then prints the table and `Still running. Read the results later with: pdd check --read BATCH`. `--timeout MIN` sets the limit in both cases.
- A `draft` prompt can be checked, and its result is marked DRAFT. A DRAFT pass is not an approval.
- With no test file, `pdd check` says `No tests found` and lists why, for example a `tests/*.json` file without the PDD `schema_version`, or a prompt with no Runtime interface block.
- A GitHub login that is not invited gets one line: `Your GitHub login NAME is not on the PDD runtime invite list yet. Ask the PDD team to add you.` A pdd that is too old gets `Please update pdd: …`. Both exit with code 5.
- The runtime address is set in one place in pdd. You do not need to set it.

See [Check prompts on the PDD runtime](USAGE.md#7-check-prompts-on-the-pdd-runtime) for the exit codes, `pdd check --help` and `pdd try --help` for the options, and `RUNBOOK.md` for the file formats.

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
| `pdd --version` | Print the version, `0.1.7` |
| `pdd completion bash\|zsh` | Print a shell completion script. It does not change your shell files |

## Run from a source checkout

From a clone of this repository, run the CLI without a global install:

```sh
node bin/pdd.mjs --help
node bin/pdd.mjs --version
npm test
```

You need Node.js 22 or newer. The package has no dependencies and no build step. See [CONTRIBUTING.md](../CONTRIBUTING.md).
