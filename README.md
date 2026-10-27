# PDD Alpha

> Looking for the original Python PDD (`pdd-cli` 0.0.x)? It lives on the [`main` branch](https://github.com/promptdriven/pdd/tree/main) and on PyPI: `pip install pdd-cli`.

**Prompt-driven development for your coding agent.**

> **This is the `alpha` branch of `promptdriven/pdd`.** It holds PDD Alpha, a command-line tool for Node.js. The `main` branch holds the older Python `pdd-cli`. Both install a command named `pdd`. Read [If you have the old Python pdd](#if-you-have-the-old-python-pdd) before you install.

In PDD, prompts are the source of your software. You and your coding agent write the prompt, the Story and the test cases first. Then the agent writes the code.

PDD Alpha gives your agent (Codex or Claude Code) five skills. You call them as slash commands:

| Skill | What it is |
|---|---|
| [`/pdd-prompting`](skills/pdd-prompting/SKILL.md) | The [Prompting guide](docs/prompting-guide.md) and its core rules |
| `/pdd-feature` | A workflow for new behavior |
| `/pdd-bug` | A workflow for something that is broken |
| `/pdd-small-change` | A workflow for a small change that is easy to undo |
| `/pdd-setup` | Set up a repo for PDD (once for each repo) |

The `pdd` command can also take a GitHub issue to real pull requests. You approve each plan. pdd opens the PRs. You merge them.

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
pdd --version   # prints 0.1.2
which -a pdd    # the first line must be in "$(npm prefix -g)/bin"
```

The pdd command also copies the skills into your agent's skills folders (`~/.agents/skills`, `~/.claude/skills`, and `$CLAUDE_CONFIG_DIR/skills` if you set it). It never writes them into your repo.

To install only the skills, without the pdd command, use the standard skills installer:

```sh
npx skills add "promptdriven/pdd#alpha"
```

Always install and update pdd with that full `github:` line. Do not run `npm install -g pdd` or `npm update -g`. The npm registry has a different, unrelated package called `pdd`, and npm would replace PDD Alpha with it.

### If you have the old Python pdd

The Python `pdd-cli` (from the `main` branch and PyPI) also installs a `pdd` command. If `pdd --version` does not print `0.1.2`, the old one comes first on your PATH. Remove it with the tool you used to install it:

```sh
uv tool uninstall pdd-cli    # or: pipx uninstall pdd-cli   or: pip uninstall pdd-cli
hash -r                      # zsh users can also run: rehash
which -a pdd
```

If you want to keep the old one, call PDD Alpha by its full path: `"$(npm prefix -g)/bin/pdd"`. The agents that PDD starts always use the full path, so they are not affected.

## Set up a repo and use the skills

Run this once in the top folder of each repo:

```sh
cd your-project
pdd setup          # or, in Codex or Claude Code: /pdd-setup
```

It adds one short PDD block (7 lines) to `CLAUDE.md`, else to `AGENTS.md`. It never pastes the guide. A second run changes nothing.

Then open Codex or Claude Code as usual and call a skill:

```
/pdd-feature Add a CSV export button to the orders page.
/pdd-bug The export button does nothing on Safari.
/pdd-small-change Fix the typo in the footer.
/pdd-prompting Review my prompts.
```

The agent reads the full Prompting guide when it writes a prompt, a Story or test cases. The work stays in your chat. To get pull requests, start a run.

## Run a workflow on a GitHub issue

Run this in a clone of a GitHub repository that you can push to:

```sh
cd your-clone
git fetch origin
pdd workflow run feature 42
```

pdd makes a branch and a worktree for issue #42. It opens the first chat in Herdr and returns at once. **You can close the terminal. There are no time limits.**

```
pdd workflow run feature 42        returns at once
  |
chat 1  story: understand, visual?, prompt-story
  |     gate: you approve (or ask for changes in the same chat)
chat 2  prompt PR: check, try?
  |     pdd opens PR 1: the prompt, the Story and the tests
  |     gate: "Do you want the code PR now, or stop here and merge PR 1 first?"
chat 3  code (only when you ask): build, verify
  |     pdd opens PR 2: the code, stacked on PR 1
you     review and merge on GitHub
```

Each chat gives each step to a fresh subagent. `?` marks an optional step: the chat asks you about it. At a gate, answer in the chat in your own words, or use the commands below.

| Workflow | Use it for | Areas (you act at the **bold** ones) |
|---|---|---|
| `feature` | New behavior | story, **approve**, prompt PR (PR 1), **code now or stop?**, code (PR 2), **merge** |
| `bug` | Something is broken | story, **approve**, prompt PR (PR 1), **code now or stop?**, code (PR 2), **merge** |
| `small-change` | A small edit that is easy to undo | plan, **approve**, build (one PR), **merge** |

If you stop at PR 1, merge it when you are ready. `pdd workflow approve N` makes the code PR at any time. If the prompts in PR 1 are still `draft`, approve them before the code PR. The agents run the tests. A fresh subagent that did not write the code does the verify step. The PR body has the step summaries and the real test commands with their output. pdd never merges.

## Commands

| Command | What it does |
|---|---|
| `pdd setup` | Add or update the PDD block in `CLAUDE.md`, else `AGENTS.md` |
| `pdd workflow run NAME ISSUE [--agent codex\|claude]` | Start a run on a GitHub issue |
| `pdd workflow list` | List the workflows that pdd finds, with their areas and gates |
| `pdd workflow status [N]` | Show the area, the step, what it waits for and the PRs. Without N: all runs in this repo |
| `pdd workflow open N` | Show the chat of the run. It resumes an ended chat |
| `pdd workflow approve [N]` | Approve the gate, or make the code PR. Without N: this worktree's run, or the one run that waits |
| `pdd workflow changes N "text"` | Ask for changes. The same chat revises |
| `pdd workflow cancel N` | Stop the run and close its tabs. pdd keeps the worktree and the branch |

N is the issue number in the current repo. If several repos match, use `owner/repo#N`. Only the agent uses `pdd workflow done STEP`.

## Check prompts on the PDD runtime

`pdd check` sends your prompts, Stories and tests to the PDD runtime. An AI model runs each prompt as the program, and the runtime checks its answer against the test. `pdd try` makes a link where a person can use the prompt by hand. Both sign in with your GitHub login (`gh auth status`) and send every file that Git shows.

| Command | What it does |
|---|---|
| `pdd check [story]` | Check every story, or one. One table, a `Runtime check:` line and a report link for each story |
| `pdd check --fill-hash` | Fill the hash of draft interfaces. Sends nothing |
| `pdd check --files` | List the files a check would send. Sends nothing |
| `pdd check --read` | Show the last results again. Sends nothing new |
| `pdd try [story]` | Make a Try link and open it in your browser. It ends in 24 hours |
| `pdd try --stop [story]` | Stop the Try link |

A prompt whose interface is still `draft` can be checked, and its result is marked DRAFT. Until the next server update, a draft check may be refused with a plain message.

Exit codes: 0 passed, 1 a check failed, 4 refused (a file breaks a rule; nothing was judged), 5 not run (sign-in, busy server, no AI room), 3 unknown (run `pdd check --read`; never send it again), 2 command error. Your agent reads [RUNBOOK.md](RUNBOOK.md) for the rules. See [Check prompts on the PDD runtime](docs/USAGE.md#7-check-prompts-on-the-pdd-runtime).

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
npx skills add "promptdriven/pdd#alpha"         # update the skills, if you installed them this way
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

[Open an issue](https://github.com/promptdriven/pdd/issues/new?title=%5Balpha%5D%20) with **[alpha]** at the start of the title. [The usage guide](docs/USAGE.md#14-report-a-problem) says what to add. Do not paste tokens or secrets.

## Documentation

- [Usage guide](docs/USAGE.md): install, setup, runs, gates, runtime checks, clean up and fixes
- [Workflows in depth](docs/workflows.md): areas, steps, gates, tests and your own workflows
- [CLI reference](docs/cli.md)
- [Prompting guide](docs/prompting-guide.md) and the [pdd-prompting skill](skills/pdd-prompting/SKILL.md)
- [Example project](examples/ticket-status/README.md)

## Contributing and license

Open pull requests against the `alpha` branch. See [CONTRIBUTING.md](CONTRIBUTING.md). PDD Alpha uses the [MIT license](LICENSE).
