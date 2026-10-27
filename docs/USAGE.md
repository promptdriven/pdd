# PDD Alpha usage guide

This guide is for people who install PDD Alpha 0.2.0 from the `alpha` branch of `promptdriven/pdd`. Each section has commands that you can copy.

> [!WARNING]
> **Agents run with full access.** PDD starts Codex with `--dangerously-bypass-approvals-and-sandbox` and Claude Code with `--dangerously-skip-permissions`. The agents do not stop to ask for approval. They can read, change and delete files and run commands as your user. Use PDD only in projects and on machines where you accept this.

Contents:

1. [Before you start](#1-before-you-start)
2. [Install](#2-install)
3. [If you have the old Python pdd](#3-if-you-have-the-old-python-pdd)
4. [The PDD skills](#4-the-pdd-skills)
5. [Set up a repo and use the skills](#5-set-up-a-repo-and-use-the-skills)
6. [Run a workflow on a GitHub issue](#6-run-a-workflow-on-a-github-issue)
7. [Check prompts on the PDD runtime](#7-check-prompts-on-the-pdd-runtime)
8. [Make your own workflow](#8-make-your-own-workflow)
9. [Shell completion](#9-shell-completion)
10. [Clean up after a run](#clean-up-after-a-run)
11. [Update and uninstall](#update-and-uninstall)
12. [Known limits](#12-known-limits)
13. [Troubleshooting](#13-troubleshooting)
14. [Report a problem](#14-report-a-problem)

## 1. Before you start

PDD runs on your own machine, with your own agent account and your own GitHub account. It needs no PDD account. Only `pdd check` and `pdd try` use a server, the PDD runtime, with your GitHub login.

Check your tools:

```sh
node -v               # Node.js 22 or newer
git --version         # Git
gh auth status        # "Logged in to github.com"
herdr --version       # Herdr, for workflow runs
codex login status    # "Logged in ..."  (or use Claude Code)
```

PDD needs Node.js 22 or newer. The other tools work with the versions you have. If a tool is missing:

| Tool | How to get it |
|---|---|
| Node.js 22 or newer | [nodejs.org](https://nodejs.org), or your Node version manager |
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

npm downloads the `alpha` branch from GitHub. The package has no dependencies and no build step. The pdd command also copies the PDD skills into your agent's skills folders (see [section 4](#4-the-pdd-skills)).

To install only the skills, without the pdd command, use the standard skills installer:

```sh
npx skills add "promptdriven/pdd#alpha"
```

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

PDD is five skills. A skill is a folder of plain Markdown that your agent reads when it needs it. You call a skill by its name, as a slash command.

| Skill | What it is |
|---|---|
| [`/pdd-prompting`](../skills/pdd-prompting/SKILL.md) | The full [Prompting guide](prompting-guide.md) (`guide.md`), its core rules, how to review a prompt, and `RUNBOOK.md` for runtime checks |
| `/pdd-feature` | A workflow for new behavior |
| `/pdd-bug` | A workflow for something that is broken |
| `/pdd-small-change` | A workflow for a small change that is easy to undo |
| `/pdd-setup` | Set up a repo for PDD. It does the same as `pdd setup` |

There are two ways to install the skills:

| Way | Command | Where the skills go |
|---|---|---|
| The standard skills installer | `npx skills add "promptdriven/pdd#alpha"` | Your project's `.agents/skills/` (Codex) and `.claude/skills/` (Claude Code). Add `-g` for `~/.agents/skills/` and `~/.claude/skills/`. Add `--skill NAME` to pick skills |
| The pdd command | Any pdd command, for example `pdd --version` | Your user folders, see below |

The pdd command checks the skills first and copies them into the skills folders of your agents:

- `~/.agents/skills/` for Codex
- `~/.claude/skills/` for Claude Code
- `$CLAUDE_CONFIG_DIR/skills/` too, when you set that variable

pdd never copies them into your repo. Each copied folder has a marker file, `.pdd-skill.json`. It shows that pdd owns the folder.

| The installed skill folder | What pdd does |
|---|---|
| Is missing | Copies the skill |
| Is older than your pdd | Replaces it |
| Has the same version, but its files changed | Replaces it |
| Is newer than your pdd | Keeps it |
| Is a symlink, or has no `.pdd-skill.json` file | Keeps it. It belongs to you |

So do not edit the installed folders: pdd replaces your edits. To change a workflow, [make your own](#8-make-your-own-workflow).

The skills work in any Codex or Claude Code chat.

## 5. Set up a repo and use the skills

Set up each repo once. Run this in the top folder of the repo:

```sh
cd your-project
pdd setup
```

Or, in Codex or Claude Code, call `/pdd-setup`. Both do the same:

1. They pick `CLAUDE.md` if it exists, else `AGENTS.md`. If neither exists, they make `AGENTS.md`.
2. They add one short block (7 lines) between `<!-- pdd:start -->` and `<!-- pdd:end -->`. The block says that this project uses PDD and that prompts are the source. It names the skills and `pdd workflow run`. It tells the agent to read `RUNBOOK.md` before a runtime check.
3. They keep all other text. A second run changes nothing. They never paste the guide.

Then open Codex or Claude Code as usual, in your project, and call a skill:

```
/pdd-feature Add a CSV export button to the orders page.
/pdd-bug The export button does nothing on Safari.
/pdd-small-change Fix the typo in the footer.
/pdd-prompting Review my prompts against the Prompting guide.
```

The agent can also pick a skill by itself when your request fits it. It reads the full Prompting guide when it writes or changes a prompt, a Story or test cases. Nothing big is pasted into the chat.

In a chat, the work stays in your folder: no worktree and no automatic PR. To turn a GitHub issue into PRs, start a run (next section). The agent can start it for you when you ask.

## 6. Run a workflow on a GitHub issue

`pdd workflow run` takes one GitHub issue to real PRs. The work happens in a few chats in Herdr. You approve at each gate. pdd opens the PRs. It never merges.

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

ISSUE is the issue number (`42`). Add `--agent claude` to use Claude Code for the whole run. NAME is `small-change`, `bug`, `feature` or the name of [your own workflow](#8-make-your-own-workflow).

The command returns at once. It prints where the run is and the commands to open and approve it. **You can close the terminal now. There are no time limits.**

### 6.3 What happens

1. pdd reads the issue with `gh`. It makes a new branch (for example `pdd/small-change-42-1a2b3c4d`) and a new Git worktree in the folder `your-clone.pdd-worktrees/` next to your clone. It makes the run folder `your-clone/.git/pdd/runs/42/`.
2. pdd opens the first chat in Herdr, in full-access mode. The Herdr session is `pdd`. Each repo has a workspace. Each run has a tab, for example `#42 small-change`. pdd does not touch your default Herdr session.
3. The chat follows the workflow skill. It gives each step to a fresh subagent. The subagent gets a short brief and file paths, not the chat history.
4. After each step, the agent tells pdd that the step is done. The step notes go into the run folder.
5. At a gate, the chat shows you the result and asks you. Then it stops and waits. It waits as long as you need.
6. When you approve, pdd starts a new chat for the next area. That chat gets the results of the area that you approved.
7. After the last step of an area with a PR gate, pdd pushes the branch and opens the PR.
8. You review and merge the PRs on GitHub. When `pdd workflow status` sees the merge, the run is completed.

With Claude Code, the first chat can ask you once to trust the new worktree folder. This happens when your clone's folder is not trusted in Claude Code yet. `run` prints a hint. Open the chat with `pdd workflow open 42` and answer the question.

The areas of the three workflows (you act at the **bold** ones):

| Workflow | Areas and steps |
|---|---|
| `feature` | story (understand, visual?, prompt-story), **approve**, prompt PR (check, try?) opens PR 1, **code now or stop?**, code (build, verify) opens PR 2, **merge** |
| `bug` | story (reproduce, prompt-story), **approve**, prompt PR (check, try?) opens PR 1, **code now or stop?**, code (build, verify) opens PR 2, **merge** |
| `small-change` | plan (scope), **approve**, build (change, verify) opens one PR, **merge** |

`?` marks an optional step. Each area is one chat. The code area of `feature` and `bug` runs only when you ask for it. [workflows.md](workflows.md) tells what each step does.

### 6.4 See the chat

```sh
pdd workflow open 42
```

This shows the current chat of the run. You can read it and type to it. If the chat ended, for example after a restart, `open` resumes it in its tab.

### 6.5 Answer a gate

At a gate, read what the chat shows. The step notes are in the run folder (`.git/pdd/runs/42/` in your clone), and the files are in the run's worktree. Then choose:

| You want to | In the chat | In a terminal |
|---|---|---|
| Approve | Say so in your own words, for example "Looks good, go on." | `pdd workflow approve 42` |
| Ask for changes | Say what to change | `pdd workflow changes 42 "Also cover an empty list."` |
| Stop the run | (no chat answer) | `pdd workflow cancel 42` |

Rules:

- Only you can approve. An agent never approves for you. When you approve in the chat, the agent runs `pdd workflow approve`. pdd then checks that your own message is in the chat after the gate.
- In a terminal, `approve` asks y/N. The question shows the repo, the issue and its title.
- `approve` without N: in a run's worktree, it approves that run. Elsewhere in the repo, it approves the one run that waits for you. If more than one run waits, it lists them.
- Changes stay in the same chat. The chat revises and asks you again.
- `cancel` closes the chat tabs of the run. pdd keeps the worktree and the branch. A new `pdd workflow run` on the same issue then starts fresh.

### 6.6 Optional steps

`visual` and `try` are optional. The chat asks you about them. They are questions, not stops. Answer in the chat.

### 6.7 The PRs and the merge

`small-change` makes one PR with the change and its tests. Its body says `Closes #42`.

`feature` and `bug` make up to two PRs:

| PR | What it holds | When |
|---|---|---|
| PR 1 | The prompt, the Story and the test cases | After the prompt PR area. Its body says `Part of #42` |
| PR 2 | The code | Only when you ask for it. Its body says `Closes #42` and that it builds on PR 1 |

At the PR 1 gate, the chat shows the PR 1 link, the `Runtime check:` line and the Try link, when there are any. Then it asks: "Do you want the code PR now, or stop here and merge PR 1 first?"

- **Code now:** say so in the chat in your own words, or run `pdd workflow approve 42`. The code area starts in a new chat. PR 2 is stacked on PR 1's branch. Merge PR 1 first.
- **Stop:** the run waits. `status` says that PR 1 is open. If you merge PR 1 and do not go on, the run ends as "done at PR 1". You can still run `pdd workflow approve 42` later. Then PR 2 starts from the merged prompts on the default branch.
- If the prompts in PR 1 are still `draft`, approve them before the code PR. The agent sets them to `approved` only after your OK.

For all workflows:

- The verify step runs in a fresh subagent that did not write the code.
- verify writes the exact test commands and their real output to `verify.md` in the run folder.
- The PR body has the step summaries and `verify.md`. When a runtime check ran, it also has a `Runtime check:` line and a report link. Runtime report links expire after 7 days.
- pdd does not run the tests itself. Read the test output in the PR before you merge.
- pdd never merges. You review and merge on GitHub.

### 6.8 Check a run

```sh
pdd workflow status 42
pdd workflow status        # all runs in this repo
```

`status` shows the area, the step, what the run waits for, and the PR with its CI state. Without N, it shows all runs in this repo. In a run's worktree, it shows that run. N is the issue number in the current repo. If several repos have a run for that number, use `owner/repo#42`.

### 6.9 Close the terminal or restart

The chats run in Herdr, not in your terminal. You can close the terminal at any time. Nothing has a time limit.

After a restart, run `pdd workflow open 42`. pdd resumes the chat of the current area (`codex resume` or `claude --resume`) in its tab.

### 6.10 Many issues at once

Each issue gets its own branch, worktree and Herdr tab. You can start several runs. An issue can have only one active run: a second `run` on the same issue is refused. After `pdd workflow cancel N`, you can run it again, and the new run starts fresh. Each step is a full agent session on your machine. Many runs at once use a lot of memory and agent quota.

## 7. Check prompts on the PDD runtime

The PDD runtime runs a prompt as a program: an AI model on the PDD server reads the `*.prompt.md` file and acts as the program. `pdd check` sends your prompts, Stories and tests there and checks each answer against its test. `pdd try` makes a link where a person can use the prompt by hand.

Both commands sign in with your GitHub login (`gh auth status`). They send every file that Git shows (tracked and new, not ignored), at most 10 MB, and refuse secret file names. pdd keeps run state in `~/.pdd/runtime`, never in your repo.

```sh
pdd check --fill-hash     # fill the hash of draft interfaces; sends nothing
pdd check --files         # list the files a check would send; sends nothing
pdd check                 # check every story; one table and a report link for each
pdd check place-order     # check one story
pdd check --read          # show the last results again; sends nothing new
pdd try place-order       # open a Try link in your browser; it ends in 24 hours
pdd try --stop place-order
```

After the table, `pdd check` prints one `Runtime check:` line that you can paste into a PR, for example `Runtime check: ✓ 4 of 4 criteria · 11/11 checks · 2 AI calls`.

A prompt whose interface is still `draft` can be checked, and its result is marked DRAFT. Until the next server update, a draft check may be refused with a plain message, for example `pdd: PATH is "draft". The person must approve it first.` The agent sets a prompt to `approved` only after your OK.

| Exit | Result | What to do |
|---|---|---|
| 0 | passed | Nothing. |
| 1 | a check failed | Look at the failed check. You decide: change the prompt or the expected value. |
| 4 | refused | A file breaks a rule and nothing was judged. Fix the file. |
| 5 | not run | Sign-in, a busy server or no AI room. Check `gh auth status`, or wait and run again. |
| 3 | unknown | Run `pdd check --read` later. Never send it again. |
| 2 | command error | Run `pdd check --help`. |

Your agent reads [RUNBOOK.md](../RUNBOOK.md) in the pdd package: the three files (prompt, Story, test), their rules and what to do with each result.

## 8. Make your own workflow

A workflow is a skill folder. Copy one of the PDD workflows as `pdd-NAME`, and edit it. For example, in your repo:

```sh
mkdir -p .agents/skills
cp -R ~/.agents/skills/pdd-bug .agents/skills/pdd-mybug
rm .agents/skills/pdd-mybug/.pdd-skill.json
pdd workflow list            # pdd-mybug is in the list
pdd workflow run mybug 42
```

[workflows.md](workflows.md#make-your-own-workflow) has the steps and the file format.

## 9. Shell completion

`pdd completion bash` and `pdd completion zsh` print a completion script. They do not change your shell files. To turn it on, add one line to your shell startup file:

```sh
source <(pdd completion zsh)    # in ~/.zshrc, after compinit
source <(pdd completion bash)   # in ~/.bashrc
```

<a id="clean-up-after-a-run"></a>

## 10. Clean up after a run

PDD does not remove old worktrees or branches. Clean up only runs that are completed (the PR is merged) or cancelled.

```sh
git worktree list                                   # runs show as your-clone.pdd-worktrees/FOLDER [pdd/...]
git worktree remove ../your-clone.pdd-worktrees/FOLDER
git branch -D pdd/small-change-42-1a2b3c4d          # the run's local branch
```

Do not remove a worktree while its run goes on. The run folder stays in `.git/pdd/runs/N` in your clone.

All runs share the Herdr session `pdd`. `cancel` closes the tabs of a run. To remove the whole session when no run uses it:

```sh
herdr session list
herdr session delete pdd
```

Do not run `herdr server stop` without a session name. That stops your default Herdr and every agent in it.

<a id="update-and-uninstall"></a>

## 11. Update and uninstall

Update to the newest alpha:

```sh
npm install -g github:promptdriven/pdd#alpha
pdd --version
```

The next pdd command replaces the installed PDD skills with the new ones. It does not touch a symlink or a skill folder that has no `.pdd-skill.json` file. Such a folder belongs to you.

Uninstall:

```sh
npm uninstall -g pdd
rm -rf ~/.agents/skills/pdd-prompting ~/.agents/skills/pdd-small-change ~/.agents/skills/pdd-bug ~/.agents/skills/pdd-feature
rm -rf ~/.claude/skills/pdd-prompting ~/.claude/skills/pdd-small-change ~/.claude/skills/pdd-bug ~/.claude/skills/pdd-feature
# If you set CLAUDE_CONFIG_DIR, also remove the four pdd-* folders in "$CLAUDE_CONFIG_DIR/skills"
rm -rf ~/.local/state/pdd
```

Leftovers can stay in your clones: `.git/pdd`, the `*.pdd-worktrees` folders and the `pdd/...` branches. See [Clean up after a run](#clean-up-after-a-run).

## 12. Known limits

This is an alpha. These limits are known today:

- pdd does not run or check the tests. The agents run them. Read the test output in the PR body before you merge.
- pdd does not remove old worktrees or branches. See [Clean up after a run](#clean-up-after-a-run).
- A busy or rate-limited model (HTTP 429, capacity or quota) can stop a chat. Open it with `pdd workflow open N` and ask it to go on.
- If your agent is not signed in, the chat stops at a sign-in screen. Check `codex login status` before you start.
- With Claude Code, the first chat of a run can ask once to trust the new worktree. Answer it in the chat.
- An issue can have only one active run. After `pdd workflow cancel N`, you can run it again.
- Each step is a fresh subagent. A run uses a lot of agent quota.
- Codex is the default agent. Claude Code works too.

## 13. Troubleshooting

| You see | What to do |
|---|---|
| `pdd --version` does not print `0.2.0` | Another `pdd` comes first. See [section 3](#3-if-you-have-the-old-python-pdd). |
| pdd says that `codex` or `claude` is not on PATH | Install the agent and sign in, or use the other one with `--agent`. |
| A message about `git rev-parse --show-toplevel` | You are not in a Git clone. `cd` into your clone. |
| A message about `refs/remotes/origin/...` or a missing base | Run `git fetch origin`. |
| A GitHub error when the run starts | Check `git remote -v` (a GitHub `origin`), `gh auth status`, and that the issue exists in this repository. |
| `approve` says that more than one run matches | Give the issue number, or `owner/repo#N`. |
| `run` says that the issue already has a run | Use `pdd workflow open N` or `status N`. To start again, run `pdd workflow cancel N` first. |
| `run` prints a hint about Claude Code trust | Run `pdd workflow open N` and answer the trust question in the chat. |
| The agent cannot approve for you | pdd found no message from you after the gate. Write your approval in the chat yourself, or run `pdd workflow approve N` in a terminal. |
| The chat stopped and does nothing | Run `pdd workflow open N`. Read the last lines. It can wait for you, show a sign-in screen or hit a rate limit. Answer it, or ask it to go on. |
| The chat is gone after a restart | Run `pdd workflow open N`. It resumes the chat. |
| The agent uses an old PDD skill | Run any pdd command, for example `pdd --version`. It updates the skills. |
| `npm outdated -g` shows `pdd` 0.4.14 | That is the unrelated registry package. Ignore it. Do not run `npm update -g`. |

## 14. Report a problem

[Open an issue](https://github.com/promptdriven/pdd/issues/new?title=%5Balpha%5D%20) on `promptdriven/pdd` and put **[alpha]** at the start of the title. Please add:

- your OS, and the output of `pdd --version`, `node -v`, `git --version` and `herdr --version`;
- the agent (Codex or Claude Code) and its version;
- the command you ran and the output of `pdd workflow status N`;
- what you expected, and what happened.

Do not paste tokens, passwords or private code.
