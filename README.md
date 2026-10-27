# PDD Alpha

> Looking for the original Python PDD (`pdd-cli` 0.0.x)? It lives on the [`main` branch](https://github.com/promptdriven/pdd/tree/main) and on PyPI: `pip install pdd-cli`.

**Prompt-driven development for your coding agent.**

> **This is the `alpha` branch of `promptdriven/pdd`.** It holds PDD Alpha, a command-line tool for Node.js. The `main` branch holds the older Python `pdd-cli`. Both install a command named `pdd`. Read [If you have the old Python pdd](#if-you-have-the-old-python-pdd) before you install.

In PDD, prompts are the source of your software. You and your coding agent write the prompt, the Story and the test cases first. Then the agent writes the code.

PDD Alpha gives your agent (Codex or Claude Code) four skills:

| Skill | What it is |
|---|---|
| [`pdd-prompting`](skills/pdd-prompting/SKILL.md) | The [Prompting guide](docs/prompting-guide.md) and its core rules |
| `pdd-small-change` | A workflow for a small change that is easy to undo |
| `pdd-bug` | A workflow for something that is broken |
| `pdd-feature` | A workflow for new behavior |

pdd copies them into your agent's own skills folders (`~/.agents/skills`, `~/.claude/skills`, and `$CLAUDE_CONFIG_DIR/skills` if you set it). It never writes them into your repo. Then pdd can take a GitHub issue to a real pull request. You approve each plan. pdd opens the PR. You merge it.

> [!WARNING]
> **Agents run with full access.** PDD starts Codex and Claude Code in full-access mode, so they do not stop to ask for approval. They can read, change and delete files and run commands as your user. Use PDD only in projects and on machines where you accept this.

The full guide is in [docs/USAGE.md](docs/USAGE.md).

## Requirements

| You need | Check it with |
|---|---|
| [Node.js](https://nodejs.org) 22 or newer, and [Git](https://git-scm.com) | `node -v`, `git --version` |
| [GitHub CLI](https://cli.github.com), signed in | `gh auth status` |
| [Herdr](https://herdr.dev) (for workflow runs) | `herdr --version` |
| [Codex CLI](https://developers.openai.com/codex/cli/) or [Claude Code](https://code.claude.com/docs/en/overview), signed in | `codex login status`, or start `claude` |

The other tools work with the versions you have. Codex is the default agent. PDD Alpha is tested on macOS and Linux, not on Windows.

## Install

```sh
npm install -g github:promptdriven/pdd#alpha
pdd --version   # prints 0.2.0
which -a pdd    # the first line must be in "$(npm prefix -g)/bin"
```

Always install and update with that full `github:` line. Do not run `npm install -g pdd` or `npm update -g`. The npm registry has a different, unrelated package called `pdd`, and npm would replace PDD Alpha with it.

### If you have the old Python pdd

The Python `pdd-cli` (from the `main` branch and PyPI) also installs a `pdd` command. If `pdd --version` does not print `0.2.0`, the old one comes first on your PATH. Remove it with the tool you used to install it:

```sh
uv tool uninstall pdd-cli    # or: pipx uninstall pdd-cli   or: pip uninstall pdd-cli
hash -r                      # zsh users can also run: rehash
which -a pdd
```

If you want to keep the old one, call PDD Alpha by its full path: `"$(npm prefix -g)/bin/pdd"`. The agents that PDD starts always use the full path, so they are not affected.

## Start a session

```sh
cd your-project
pdd session                              # Codex
pdd session --agent claude "Help me write a prompt for a CSV export button."
```

The agent starts with a short intro. The intro names the Prompting guide skill, its core rules and the three workflow skills. The agent reads the full guide when it writes a prompt, a Story or test cases. You need no issue and no setup.

## Run a workflow on a GitHub issue

Run this in a clone of a GitHub repository that you can push to:

```sh
cd your-clone
git fetch origin
pdd workflow run small-change 42
```

pdd makes a branch and a worktree for issue #42. It opens the first chat in Herdr and returns at once. **You can close the terminal. There are no time limits.**

```
pdd workflow run bug 42            returns at once
  |
chat 1  solution: reproduce, prompt-story, check, try?
  |     gate: the chat shows the result and asks you
  |       changes -> the same chat revises and asks again
  |       approve -> pdd starts a new chat
chat 2  build: build, verify
  |     pdd pushes the branch and opens the PR
you     review and merge the PR on GitHub
```

Each chat gives each step to a fresh subagent. `?` marks an optional step: the chat asks you about it. At a gate, answer in the chat in your own words, or use the commands below.

| Workflow | Use it for | Areas (you act at the **bold** ones) |
|---|---|---|
| `small-change` | A small edit that is easy to undo | plan, **approve**, build, PR, **merge** |
| `bug` | Something is broken | solution, **approve**, build, PR, **merge** |
| `feature` | New behavior | solution, **approve**, story, **approve**, build, PR, **merge** |

A run always makes one PR. The agents run the tests. A fresh subagent that did not write the code does the verify step. The PR body has `Closes #N`, the step summaries and the real test commands with their output. pdd never merges.

## Commands

| Command | What it does |
|---|---|
| `pdd session [--agent codex\|claude] [request]` | Start your agent with the PDD intro |
| `pdd workflow NAME [request]` | Start your agent on one workflow, in one chat (no issue, no PR) |
| `pdd workflow run NAME ISSUE [--agent codex\|claude]` | Start a run on a GitHub issue |
| `pdd workflow list` | List the workflow skills that pdd finds |
| `pdd workflow status [N]` | Show the area, the step, what it waits for and the PR. Without N: all runs in this repo |
| `pdd workflow open N` | Show the chat of the run. It resumes an ended chat |
| `pdd workflow approve [N]` | Approve the gate. The next area starts in a new chat. Without N: this worktree's run, or the one run that waits |
| `pdd workflow changes N "text"` | Ask for changes. The same chat revises |
| `pdd workflow cancel N` | Stop the run and close its tabs. pdd keeps the worktree and the branch |

N is the issue number in the current repo. If several repos match, use `owner/repo#N`. Only the agent uses `pdd workflow done STEP`.

## Make your own workflow

A workflow is a skill folder: `SKILL.md`, `workflow.json` and one short file for each step. Copy one as `pdd-NAME`, then edit its name and steps. In your repo:

```sh
mkdir -p .agents/skills                                   # Claude Code: .claude/skills
cp -R ~/.agents/skills/pdd-bug .agents/skills/pdd-mybug
rm .agents/skills/pdd-mybug/.pdd-skill.json
pdd workflow run mybug 42
```

pdd finds `pdd-NAME` in the repo's `.agents/skills` or `.claude/skills`, or in your user skills folders. Do not edit the installed `pdd-*` folders: an update replaces them. See [docs/workflows.md](docs/workflows.md#make-your-own-workflow).

## Update and uninstall

```sh
npm install -g github:promptdriven/pdd#alpha   # update. The next pdd command updates the skills
npm uninstall -g pdd                           # remove PDD Alpha
```

The uninstall keeps the skills. To remove them, see [Update and uninstall](docs/USAGE.md#update-and-uninstall).

## Known limits of this alpha

- pdd does not run or check the tests. Read the test output in the PR body before you merge.
- pdd does not remove old worktrees or branches. See [Clean up](docs/USAGE.md#clean-up-after-a-run).
- A busy or rate-limited model can stop a chat. Open it with `pdd workflow open N` and ask it to go on.
- If your agent is not signed in, the chat stops at a sign-in screen. Check this before you start.
- Claude Code can ask once to trust a new worktree. `run` prints a hint. Answer it in the chat.
- An issue can have only one active run. After `pdd workflow cancel N`, you can run it again.
- Each step is a fresh subagent. A run uses a lot of agent quota. Many runs at once also use a lot of memory.

## Report a problem

[Open an issue](https://github.com/promptdriven/pdd/issues/new?title=%5Balpha%5D%20) with **[alpha]** at the start of the title. [The usage guide](docs/USAGE.md#13-report-a-problem) says what to add. Do not paste tokens or secrets.

## Documentation

- [Usage guide](docs/USAGE.md): install, sessions, runs, gates, clean up and fixes
- [Workflows in depth](docs/workflows.md): areas, steps, gates, tests and your own workflows
- [CLI reference](docs/cli.md)
- [Prompting guide](docs/prompting-guide.md) and the [pdd-prompting skill](skills/pdd-prompting/SKILL.md)
- [Example project](examples/ticket-status/README.md)

## Contributing and license

Open pull requests against the `alpha` branch. See [CONTRIBUTING.md](CONTRIBUTING.md). PDD Alpha uses the [MIT license](LICENSE).
