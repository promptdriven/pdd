# PDD Alpha usage guide

This guide is for people who install PDD Alpha 0.2.0 from the `alpha` branch of `promptdriven/pdd`. Each section has commands that you can copy.

> [!WARNING]
> **Agents run with full access.** PDD starts Codex with `--dangerously-bypass-approvals-and-sandbox` and Claude Code with `--dangerously-skip-permissions`. The agents do not stop to ask for approval. They can read, change and delete files and run commands as your user. Use PDD only in projects and on machines where you accept this.

Contents:

1. [Before you start](#1-before-you-start)
2. [Install](#2-install)
3. [If you have the old Python pdd](#3-if-you-have-the-old-python-pdd)
4. [The PDD skills](#4-the-pdd-skills)
5. [Your first session](#5-your-first-session)
6. [Run a workflow on a GitHub issue](#6-run-a-workflow-on-a-github-issue)
7. [Make your own workflow](#7-make-your-own-workflow)
8. [Shell completion](#8-shell-completion)
9. [Clean up after a run](#clean-up-after-a-run)
10. [Update and uninstall](#update-and-uninstall)
11. [Known limits](#11-known-limits)
12. [Troubleshooting](#12-troubleshooting)
13. [Report a problem](#13-report-a-problem)

## 1. Before you start

PDD runs on your own machine, with your own agent account and your own GitHub account. It needs no PDD account and no server.

Check your tools:

```sh
node -v               # Node.js
git --version         # Git
gh auth status        # "Logged in to github.com"
herdr --version       # Herdr, for workflow runs
codex login status    # "Logged in ..."  (or use Claude Code)
```

PDD works with the versions you have. If a tool is missing:

| Tool | How to get it |
|---|---|
| Node.js | [nodejs.org](https://nodejs.org), or your Node version manager |
| Git | [git-scm.com](https://git-scm.com) |
| GitHub CLI | [cli.github.com](https://cli.github.com). Then run `gh auth login`. If `git push` asks for a password later, run `gh auth setup-git`. |
| Herdr | `curl -fsSL https://herdr.dev/install.sh \| sh`, or see [herdr.dev/docs/install](https://herdr.dev/docs/install/). You need Herdr only for workflow runs. You do not have to open it yourself. |
| Codex CLI | [developers.openai.com/codex/cli](https://developers.openai.com/codex/cli/). Then run `codex login`. |
| Claude Code (optional) | [code.claude.com](https://code.claude.com/docs/en/overview). Start `claude` once and sign in. |

Codex is the default agent. PDD Alpha is tested on macOS and Linux. Windows is not tested.

## 2. Install

```sh
npm install -g github:promptdriven/pdd#alpha
pdd --version   # prints 0.2.0
which -a pdd    # the first line must be in "$(npm prefix -g)/bin"
```

npm downloads the `alpha` branch from GitHub. The package has no dependencies and no build step.

Important:

- Always install and update with the full `github:promptdriven/pdd#alpha` line.
- Do not run `npm install -g pdd`. That installs a different, unrelated package from the npm registry.
- Do not run `npm update -g`. npm thinks that the unrelated registry package is a newer version of PDD, and it would replace PDD Alpha with it. You can see this with `npm outdated -g`.
- If npm says `EACCES` (permission denied), your global npm folder belongs to root. Use a Node version manager, or set your own npm prefix. Do not use `sudo`.

## 3. If you have the old Python pdd

The `main` branch of this repository and PyPI have the older Python `pdd-cli`. It also installs a command named `pdd`. On one machine, only the first `pdd` on your PATH runs.

See all of them:

```sh
which -a pdd
pdd --version   # PDD Alpha prints 0.2.0
```

Remove the old one with the tool you used to install it:

```sh
uv tool uninstall pdd-cli     # if you used uv
pipx uninstall pdd-cli        # if you used pipx
pip uninstall pdd-cli         # if you used pip (inside the same Python environment)
hash -r                       # forget the old path (zsh users can also run: rehash)
which -a pdd
```

If you want to keep the old one, call PDD Alpha by its full path:

```sh
"$(npm prefix -g)/bin/pdd" --version
```

The agents that PDD starts always get the full path of PDD Alpha. They are not affected by your PATH. Only the commands that you type are.

## 4. The PDD skills

PDD is four skills. A skill is a folder of plain Markdown that your agent reads when it needs it.

| Skill | What it is |
|---|---|
| `pdd-prompting` | The full [Prompting guide](prompting-guide.md) (`guide.md`), its core rules and how to review a prompt |
| `pdd-small-change` | A workflow for a small change that is easy to undo |
| `pdd-bug` | A workflow for something that is broken |
| `pdd-feature` | A workflow for new behavior |

Each pdd command checks the skills first. If they are missing or older than your pdd, pdd copies them into the skills folders of your agents:

- `~/.agents/skills/` for Codex
- `~/.claude/skills/` for Claude Code

pdd never copies them into your repo. Each copied folder has a `.pdd-skill.json` file. This file shows that pdd owns the folder and replaces it on an update. Do not edit these folders. To change a workflow, [make your own](#7-make-your-own-workflow).

The skills work in any Codex or Claude Code chat, also one that you open yourself. Ask the agent, for example: "Use the pdd-bug skill for this."

## 5. Your first session

A session starts your normal agent with a short PDD intro. It needs no issue, no Herdr and no setup.

```sh
cd your-project
pdd session
```

What happens:

1. PDD starts Codex in your project folder, in full-access mode.
2. The first message is short. It says that prompts are the source. It names the `pdd-prompting` skill and lists its core rules. It names the three workflow skills and the `pdd workflow run` command.
3. The agent asks what you want to work on.

The agent reads the full Prompting guide when it writes or changes a prompt, a Story or test cases. Nothing big is pasted into the chat.

Give the first request on the command line, or use Claude Code:

```sh
pdd session "Help me write a prompt, a Story and test cases for a CSV export button."
pdd session --agent claude
pdd session --agent claude "Review my prompts against the Prompting guide."
```

When a request fits a workflow, the agent suggests it. It can do the workflow in this chat. Or, when you ask, it can start a run on a GitHub issue for you.

To start a chat on one workflow (no issue, no worktree, no PR):

```sh
pdd workflow small-change "Fix the typo in the footer."
pdd workflow bug --agent claude "The export button does nothing on Safari."
pdd workflow feature "Add a dark mode switch."
```

Leave the session the normal way for your agent (for example `/exit`). PDD does not change your agent's settings, sign-in or config.

## 6. Run a workflow on a GitHub issue

`pdd workflow run` takes one GitHub issue to one real PR. The work happens in a few chats in Herdr. You approve at each gate. pdd opens the PR. It never merges.

### 6.1 Prepare the repository

- Use a clone of a GitHub repository that you can push to. The `origin` remote must point to it.
- The issue must be in that same repository. It must be an issue, not a PR.
- Run `git fetch origin` first. PDD starts the new branch from your last fetch of `origin`'s default branch (for example `origin/main`). PDD does not fetch for you.
- The project needs a way to test the change. The agents find and run the project's tests.
- Your own checkout can have uncommitted work. PDD does not touch it.

### 6.2 Start the run

Run this from the top folder of your clone:

```sh
cd your-clone
git fetch origin
pdd workflow run small-change 42
```

ISSUE is the issue number (`42`). Add `--agent claude` to use Claude Code for the whole run. NAME is `small-change`, `bug` or `feature`.

The command returns at once. It prints where the run is and the commands to open and approve it. **You can close the terminal now. There are no time limits.**

### 6.3 What happens

1. pdd reads the issue with `gh`. It makes a new branch (for example `pdd/small-change-42-1a2b3c4d`) and a new Git worktree in the folder `your-clone.pdd-worktrees/` next to your clone.
2. pdd opens the first chat in Herdr, in full-access mode. The Herdr session is `pdd`. Each repo has a workspace. Each run has a tab, for example `#42 small-change`. pdd does not touch your default Herdr session.
3. The chat follows the workflow skill. It gives each step to a fresh subagent. The subagent gets a short brief and file paths, not the chat history.
4. After each step, the agent tells pdd that the step is done. The step notes go into the run folder.
5. At a gate, the chat shows you the result and asks you. Then it stops and waits. It waits as long as you need.
6. When you approve, pdd starts a new chat for the next area. That chat gets the results of the area that you approved.
7. After the last step of the build area, pdd pushes the branch and opens the PR.
8. You review and merge the PR on GitHub. When `pdd workflow status` sees the merge, the run is completed.

The areas of the three workflows (you act at the **bold** ones):

| Workflow | Areas and steps |
|---|---|
| `small-change` | plan (scope), **approve**, build (change, verify), PR, **merge** |
| `bug` | solution (reproduce, prompt-story, check, try?), **approve**, build (build, verify), PR, **merge** |
| `feature` | solution (understand, visual?), **approve**, story (prompt-story, check, try?), **approve**, build (build, verify), PR, **merge** |

`?` marks an optional step. Each area is one chat. [workflows.md](workflows.md) tells what each step does.

### 6.4 See the chat

```sh
pdd workflow open 42
```

This shows the current chat of the run. You can read it and type to it. If the chat ended, for example after a restart, `open` resumes it in its tab.

### 6.5 Answer a gate

At a gate, read what the chat shows. The step notes are in the run folder, and the files are in the run's worktree. Then choose:

| You want to | In the chat | In a terminal |
|---|---|---|
| Approve | Say so in your own words, for example "Looks good, go on." | `pdd workflow approve 42` |
| Ask for changes | Say what to change | `pdd workflow changes 42 "Also cover an empty list."` |
| Stop the run | (no chat answer) | `pdd workflow cancel 42` |

Rules:

- Only you can approve. An agent never approves for you. When you approve in the chat, the agent runs `pdd workflow approve`. pdd then checks that your own message is in the chat after the gate.
- In a terminal, `approve` asks y/N. The question shows the repo, the issue and its title.
- `approve` without N works when one run in this repo waits for you.
- Changes stay in the same chat. The chat revises and asks you again.
- `cancel` marks the run cancelled and closes its tabs. pdd keeps the worktree and the branch.

### 6.6 Optional steps

`visual` and `try` are optional. The chat asks you about them. They are questions, not stops. Answer in the chat.

### 6.7 The PR and the merge

A run always makes one PR. The prompts, the Story, the tests and the code are all in it.

- The verify step runs in a fresh subagent that did not write the code.
- verify writes the exact test commands and their real output to `verify.md` in the run folder.
- The PR body has the run summary and `verify.md`.
- pdd does not run the tests itself. Read the test output in the PR before you merge.
- pdd never merges. You review and merge on GitHub.

### 6.8 Check a run

```sh
pdd workflow status 42
pdd workflow status        # the runs of this repo
```

`status` shows the area, the step, what the run waits for, and the PR with its CI state. N is the issue number in the current repo. If several repos have a run for that number, use `owner/repo#42`.

### 6.9 Close the terminal or restart

The chats run in Herdr, not in your terminal. You can close the terminal at any time. Nothing has a time limit.

After a restart, run `pdd workflow open 42`. pdd resumes the chat of the current area (`codex resume` or `claude --resume`) in its tab.

### 6.10 Many issues at once

Each issue gets its own branch, worktree and Herdr tab. You can start several runs. Each step is a full agent session on your machine. Many runs at once use a lot of memory and agent quota.

## 7. Make your own workflow

A workflow is a skill folder. Copy one of the PDD workflows under a new name, and edit it. [workflows.md](workflows.md#make-your-own-workflow) has the steps and the file format.

## 8. Shell completion

`pdd completion bash` and `pdd completion zsh` print a completion script. They do not change your shell files. To turn it on, add one line to your shell startup file:

```sh
source <(pdd completion zsh)    # in ~/.zshrc, after compinit
source <(pdd completion bash)   # in ~/.bashrc
```

<a id="clean-up-after-a-run"></a>

## 9. Clean up after a run

PDD does not remove old worktrees or branches. Clean up only runs that are completed (the PR is merged) or cancelled.

```sh
git worktree list                                   # runs show as your-clone.pdd-worktrees/FOLDER [pdd/...]
git worktree remove ../your-clone.pdd-worktrees/FOLDER
git branch -D pdd/small-change-42-1a2b3c4d          # the run's local branch
```

Removing a worktree also removes that run's records. Do not remove a worktree while its run goes on.

All runs share the Herdr session `pdd`. `cancel` closes the tabs of a run. To remove the whole session when no run uses it:

```sh
herdr session list
herdr session delete pdd
```

Do not run `herdr server stop` without a session name. That stops your default Herdr and every agent in it.

<a id="update-and-uninstall"></a>

## 10. Update and uninstall

Update to the newest alpha:

```sh
npm install -g github:promptdriven/pdd#alpha
pdd --version
```

The next pdd command replaces the installed PDD skills with the new ones. It does not touch a skill folder that has no `.pdd-skill.json` file. Such a folder belongs to you.

Uninstall:

```sh
npm uninstall -g pdd
rm -rf ~/.agents/skills/pdd-prompting ~/.agents/skills/pdd-small-change ~/.agents/skills/pdd-bug ~/.agents/skills/pdd-feature
rm -rf ~/.claude/skills/pdd-prompting ~/.claude/skills/pdd-small-change ~/.claude/skills/pdd-bug ~/.claude/skills/pdd-feature
rm -rf ~/.local/state/pdd
```

Leftovers can stay in your clones: `.git/pdd`, the `*.pdd-worktrees` folders and the `pdd/...` branches. See [Clean up after a run](#clean-up-after-a-run).

## 11. Known limits

This is an alpha. These limits are known today:

- pdd does not run or check the tests. The agents run them. Read the test output in the PR body before you merge.
- pdd does not remove old worktrees or branches. See [Clean up after a run](#clean-up-after-a-run).
- A busy or rate-limited model (HTTP 429, capacity or quota) can stop a chat. Open it with `pdd workflow open N` and ask it to go on.
- If your agent is not signed in, the chat stops at a sign-in screen. Check `codex login status` before you start.
- Each step is a fresh subagent. A run uses a lot of agent quota.
- Codex is the default agent. Claude Code works too.

## 12. Troubleshooting

| You see | What to do |
|---|---|
| `pdd --version` does not print `0.2.0` | Another `pdd` comes first. See [section 3](#3-if-you-have-the-old-python-pdd). |
| pdd says that `codex` or `claude` is not on PATH | Install the agent and sign in, or use the other one with `--agent`. |
| A message about `git rev-parse --show-toplevel` | You are not in a Git clone. `cd` into your clone. |
| A message about `refs/remotes/origin/...` or a missing base | Run `git fetch origin`. |
| A GitHub error when the run starts | Check `git remote -v` (a GitHub `origin`), `gh auth status`, and that the issue exists in this repository. |
| `approve` says that more than one run matches | Give the issue number, or `owner/repo#N`. |
| The agent cannot approve for you | pdd found no message from you after the gate. Write your approval in the chat yourself, or run `pdd workflow approve N` in a terminal. |
| The chat stopped and does nothing | Run `pdd workflow open N`. Read the last lines. It can wait for you, show a sign-in screen or hit a rate limit. Answer it, or ask it to go on. |
| The chat is gone after a restart | Run `pdd workflow open N`. It resumes the chat. |
| The agent uses an old PDD skill | Run any pdd command, for example `pdd --version`. It updates the skills. |
| `npm outdated -g` shows `pdd` 0.4.14 | That is the unrelated registry package. Ignore it. Do not run `npm update -g`. |

## 13. Report a problem

[Open an issue](https://github.com/promptdriven/pdd/issues/new?title=%5Balpha%5D%20) on `promptdriven/pdd` and put **[alpha]** at the start of the title. Please add:

- your OS, and the output of `pdd --version`, `node -v`, `git --version` and `herdr --version`;
- the agent (Codex or Claude Code) and its version;
- the command you ran and the output of `pdd workflow status N`;
- what you expected, and what happened.

Do not paste tokens, passwords or private code.
