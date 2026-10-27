# CLI reference

`pdd --help` shows all commands. `help` and `-h` also work. Each command first checks the [PDD skills](USAGE.md#4-the-pdd-skills) and installs them when they are missing or old.

## Sessions

| Command | What it does |
|---|---|
| `pdd session [--agent codex\|claude] [request]` | Start your agent in this folder with the short PDD intro. Without a request, the agent asks what you want to work on. |
| `pdd workflow NAME [--agent codex\|claude] [request]` | The same intro, plus "Use the pdd-NAME skill for this request." The work stays in this one chat: no branch, no worktree, no PR. |

Codex is the default agent. Both commands start the agent in full-access mode: Codex with `--dangerously-bypass-approvals-and-sandbox`, Claude Code with `--dangerously-skip-permissions`. PDD does not choose a model and does not change your agent's settings, sign-in or config. Use `--` to end the PDD options before a request that starts with `-`.

The intro has the folder, the core rules of the `pdd-prompting` skill, the names of the workflow skills and the full path of this pdd. The agent uses that full path, so another `pdd` on its PATH does not matter.

## Runs on a GitHub issue

| Command | What it does |
|---|---|
| `pdd workflow run NAME ISSUE [--agent codex\|claude]` | Make a branch and a worktree for the issue, open the first chat in Herdr and return at once |
| `pdd workflow status [N]` | Show the area, the step, what the run waits for, and the PR with its CI state |
| `pdd workflow open N` | Show the current chat of the run. If the chat ended, resume it in its tab |
| `pdd workflow approve [N]` | Approve the open gate. The next area starts in a new chat, or pdd opens the PR |
| `pdd workflow changes N "text"` | Send the text to the same chat. The chat revises. The gate stays open |
| `pdd workflow cancel N` | Mark the run cancelled and close its tabs. Keep the worktree and the branch |

- NAME is `small-change`, `bug` or `feature`.
- ISSUE is the issue number in the repo of your clone.
- N is the issue number of a run in the current repo, worktrees included. If several repos match, use `owner/repo#N`.
- In a terminal, `approve` asks y/N and shows the repo, the issue and its title. From an agent chat, `approve` works only when the person's own message after the gate is in that chat.
- No command has a time limit. You can close the terminal at any time.
- pdd never merges.

## Used by the agent

| Command | What it does |
|---|---|
| `pdd workflow done STEP [--summary TEXT]` | Record a finished step. Print the next instruction: the next step, the gate, or "pdd opens the PR now". After the last build step, push the branch and open the PR |

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

The package has no dependencies and no build step. See [CONTRIBUTING.md](../CONTRIBUTING.md).
