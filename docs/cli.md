# CLI reference

`pdd --help` shows all commands. `help` and `-h` also work. Each command first checks the [PDD skills](USAGE.md#4-the-pdd-skills). It copies a skill that is missing, older, or changed in the same version.

There is no `pdd session` command. Open Codex or Claude Code as usual and call a PDD skill: `/pdd-feature`, `/pdd-bug`, `/pdd-small-change` or `/pdd-prompting`.

## Set up a repo

| Command | What it does |
|---|---|
| `pdd setup` | Add or update the short PDD block (7 lines, between `<!-- pdd:start -->` and `<!-- pdd:end -->`) in `CLAUDE.md` of this folder, else in `AGENTS.md`. If neither exists, make `AGENTS.md`. A second run changes nothing |

The skill `/pdd-setup` does the same in a chat. Run it in the top folder of the repo.

## Runs on a GitHub issue

| Command | What it does |
|---|---|
| `pdd workflow run NAME ISSUE [--agent codex\|claude]` | Make a branch and a worktree for the issue, open the first chat in Herdr and return at once |
| `pdd workflow list [--json]` | List the workflows that pdd finds, with their areas and gates: the PDD ones and [your own](workflows.md#make-your-own-workflow) |
| `pdd workflow status [N]` | Show the area, the step, what the run waits for, and the PRs with their CI state. Without N, show all runs in this repo. In a run's worktree, show that run |
| `pdd workflow open N` | Show the current chat of the run. If the chat ended, resume it in its tab |
| `pdd workflow approve [N]` | Approve the open gate. The next area starts in a new chat. At the PR 1 gate of `feature` and `bug`, this makes the code PR. Without N, approve the run of the current worktree, or else the one run in this repo that waits for a person |
| `pdd workflow changes N "text"` | Send the text to the same chat. The chat revises. The gate stays open |
| `pdd workflow cancel N` | Close the run's chat tabs. Keep the worktree and the branch. A new `run` on the issue then starts fresh |

- NAME is `small-change`, `bug`, `feature` or the name of [your own workflow](workflows.md#make-your-own-workflow). pdd uses the skill `pdd-NAME`.
- ISSUE is the issue number in the repo of your clone. An issue can have only one active run. `run` refuses a second one. After `cancel`, a new `run` on the issue starts fresh.
- The run folder is `.git/pdd/runs/N/` in your clone. See [workflows.md](workflows.md#the-run-folder).
- With Claude Code, the first chat can ask once to trust the new worktree. `run` prints a hint when your clone's folder is not trusted yet.
- N is the issue number of a run in the current repo, worktrees included. If several repos match, use `owner/repo#N`.
- In a terminal, `approve` asks y/N and shows the repo, the issue and its title. From an agent chat, `approve` works only when the person's own message after the gate is in that chat.
- Codex is the default agent. The chats start in full-access mode: Codex with `--dangerously-bypass-approvals-and-sandbox`, Claude Code with `--dangerously-skip-permissions`. PDD does not choose a model and does not change your agent's settings, sign-in or config.
- The first message of each chat gives the full path of this pdd. The agent uses it, so another `pdd` on its PATH does not matter.
- No command has a time limit. You can close the terminal at any time.
- pdd never merges.

## Runtime checks

| Command | What it does |
|---|---|
| `pdd check [STORY...]` | Check stories on the PDD runtime with your gh login. Print one table, a `Runtime check:` line and a report link for each story |
| `pdd check --read [BATCH]` | Show saved check results again. Sends no check |
| `pdd check --fill-hash` | Fill the hash of draft interfaces. No network |
| `pdd check --files` | List the files a check would send. No network |
| `pdd try [STORY]` | Make a Try link and open it in your browser. It ends in 24 hours |
| `pdd try --stop [STORY]` | Stop the open Try link of a story |

A `draft` prompt can be checked, and its result is marked DRAFT. Until the next server update, a draft check may be refused with a plain message. See [Check prompts on the PDD runtime](USAGE.md#7-check-prompts-on-the-pdd-runtime) for the exit codes, and `pdd check --help` for all options.

## Used by the agent

| Command | What it does |
|---|---|
| `pdd workflow done STEP [--summary TEXT]` | Record a finished step. Print the next instruction: the next step, the gate, or "pdd opens the PR now". After the last step of an area with a PR gate, push the branch and open the PR |

The agent runs `done` from the run's worktree. pdd finds the run from that folder. You do not run `done` yourself.

## Other commands

| Command | What it does |
|---|---|
| `pdd completion bash\|zsh` | Print a shell completion script. It does not change your shell files |
| `pdd --help`, `pdd --version` | Help and version |

## Run from a source checkout

From a clone of this repository, run the CLI without a global install:

```sh
node bin/pdd.mjs --help
node bin/pdd.mjs --version
npm test
```

You need Node.js 22 or newer. The package has no dependencies and no build step. See [CONTRIBUTING.md](../CONTRIBUTING.md).
