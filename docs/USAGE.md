# PDD Alpha usage guide

This guide is for people who install PDD Alpha 0.1.0 from the `alpha` branch of `promptdriven/pdd` and want to use all of it. Each section has commands that you can copy.

> [!WARNING]
> **Agents run with full access.** PDD starts Codex with `--dangerously-bypass-approvals-and-sandbox` and Claude Code with `--dangerously-skip-permissions`. The agents do not stop to ask for approval. They can read, change and delete files and run commands as your user. Use PDD only in projects and on machines where you accept this.

Contents:

1. [Before you start](#1-before-you-start)
2. [Install](#2-install)
3. [If you have the old Python pdd](#3-if-you-have-the-old-python-pdd)
4. [Your first session](#4-your-first-session)
5. [Run a workflow on a GitHub issue](#5-run-a-workflow-on-a-github-issue)
6. [Make a workflow your own](#make-a-workflow-your-own)
7. [The Prompting guide and the PDD skill](#7-the-prompting-guide-and-the-pdd-skill)
8. [Shell completion](#8-shell-completion)
9. [Clean up after a run](#clean-up-after-a-run)
10. [Update and uninstall](#10-update-and-uninstall)
11. [Known limits](#11-known-limits)
12. [Troubleshooting](#12-troubleshooting)
13. [Report a problem](#13-report-a-problem)

## 1. Before you start

PDD runs on your own machine, with your own agent account and your own GitHub account. It needs no PDD account and no server.

Check your tools:

```sh
node -v               # v22.16.0 or newer
git --version         # 2.36 or newer
gh auth status        # "Logged in to github.com"
herdr --version       # 0.9.1 is the tested version
codex login status    # "Logged in ..."  (or use Claude Code)
```

If a tool is missing:

| Tool | How to get it |
|---|---|
| Node.js 22.16+ | [nodejs.org](https://nodejs.org), or your Node version manager |
| Git 2.36+ | [git-scm.com](https://git-scm.com) |
| GitHub CLI | [cli.github.com](https://cli.github.com). Then run `gh auth login`. If `git push` asks for a password later, run `gh auth setup-git`. |
| Herdr | `curl -fsSL https://herdr.dev/install.sh \| sh`, or see [herdr.dev/docs/install](https://herdr.dev/docs/install/). Herdr is only needed for workflow runs. You do not have to open it yourself. |
| Codex CLI | [developers.openai.com/codex/cli](https://developers.openai.com/codex/cli/). Then run `codex login`. |
| Claude Code (optional) | [code.claude.com](https://code.claude.com/docs/en/overview). Start `claude` once and sign in. |

Codex is the default agent and the most tested one. PDD Alpha is tested on macOS and Linux. Windows is not tested.

## 2. Install

```sh
npm install -g github:promptdriven/pdd#alpha
pdd --version   # prints 0.1.0
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
pdd --version   # PDD Alpha prints 0.1.0
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

## 4. Your first session

A session opens your normal agent with PDD loaded. It needs no issue, no Herdr and no setup.

```sh
cd your-project
pdd session
```

What happens:

1. PDD starts Codex in your project folder, in full-access mode.
2. The first message has the full Prompting guide, the PDD skill and all three workflows (about 21,000 tokens).
3. The agent summarizes the method and asks what you want to work on.

Then talk to it as usual. For example: plan a change, draft a prompt, a Story and test cases, review them with you, and build when you ask.

Give the first request on the command line, or use Claude Code:

```sh
pdd session "Help me write a prompt, a Story and test cases for a CSV export button."
pdd session --agent claude
pdd session --agent claude "Review my prompts against the Prompting guide."
```

Leave the session the normal way for your agent (for example `/exit`). PDD does not change your agent's settings, sign-in or global config.

To follow one workflow in a single normal conversation (no stages, no worktree, no automatic PR):

```sh
pdd workflow small-change "Fix the typo in the footer."
pdd workflow bug --agent claude "The export button does nothing on Safari."
pdd workflow feature "Add a dark mode switch."
```

## 5. Run a workflow on a GitHub issue

`pdd workflow run` takes one GitHub issue to a real PR. Each agent stage is a fresh agent session in Herdr. You approve the plan. PDD runs the tests and opens the PR. It never merges.

### 5.1 Prepare the repository

- Use a clone of a GitHub repository that you can push to. The `origin` remote must point to it.
- The issue must be in that same repository. It must be an issue, not a PR.
- Run `git fetch origin` first. PDD starts the new branch from your last fetch of `origin`'s default branch (for example `origin/main`). PDD does not fetch for you.
- The project needs a way to test the change. The agent proposes test commands, and you approve them. PDD runs them.
- Your own checkout can have uncommitted work. PDD does not touch it.

### 5.2 Start the run

Run this from the top folder of your clone:

```sh
cd your-clone
git fetch origin
pdd workflow run small-change 42
```

ISSUE can be a number (`42`), `owner/repo#42` or `https://github.com/owner/repo/issues/42`. Add `--agent claude` to use Claude Code for all stages. NAME is `small-change`, `bug`, `feature` or the name of [your own workflow](#make-a-workflow-your-own).

### 5.3 What happens, step by step

1. PDD reads the issue with `gh`. It saves the workflow and the guide for this run, so later edits do not change it.
2. PDD makes a new branch, for example `pdd/small-change-42-1a2b3c4d`, and a new Git worktree for it in the folder `your-clone.pdd-worktrees/` next to your clone.
3. PDD starts the first stage: a fresh agent in a background Herdr session that belongs to this run. The agent gets the guide, the stage instructions, the issue and the results of earlier stages.
4. The `pdd workflow run` command stays busy and prints nothing while agents work. This is normal. It can take a while.
5. When a stage ends, PDD checks the agent's handoff file and the file hashes. "The agent says it is done" is not enough to pass.
6. At a gate, the command stops and prints one result line. It tells you what it waits for.
7. You approve with `pdd workflow resume RUN_ID --decision approve`. That command then drives the next stages, and stays busy the same way.
8. At the verify stage, PDD runs the approved test commands itself and records the real results.
9. At the PR stage, PDD pushes the branch and opens a PR with `gh`.
10. Then the run waits for the merge. You review and merge the PR on GitHub. PDD never merges.
11. Run `pdd workflow resume RUN_ID` once more. PDD sees the merge and marks the run completed.

The stages of the three bundled workflows (you act at the **bold** ones):

| Workflow | Stages |
|---|---|
| `small-change` | scope, **approve the scope and tests**, change, verify, open PR, **merge** |
| `bug` | reproduce, prompt and Story, check, try (optional), **approve**, prompt PR (optional), prompt merge, build, verify, code PR, **merge** |
| `feature` | understand, visual (optional), prompt and Story, check, try (optional), **approve**, prompt PR (optional), prompt merge, build, verify, code PR, **merge** |

`small-change` is the most tested workflow. Start with it.

### 5.4 Find the run ID

The run ID is a UUID. The result line shows it when the command stops:

```
waiting: run 6f1c2d3e-4a5b-4c6d-8e7f-0a1b2c3d4e5f / change. Review the independent proposal and test plan; resume with approve to advance.
```

To find it while the first stage still works, run this in a second terminal, in your clone:

```sh
ls -t .git/pdd/workflow-inputs | head -1   # newest run in this clone
```

### 5.5 Watch or talk to a stage

In a second terminal window (a normal one, not a Herdr pane), in your clone:

```sh
pdd workflow attach RUN_ID
```

You see the live agent of the current stage. You can type to it. While you are attached, PDD waits: it does not accept the stage until you leave.

- To leave and let the agent go on, use Herdr's normal detach: press `Ctrl+B`, then `Q`.
- Do not exit the agent itself. That ends the stage.
- A finished stage is closed. You cannot attach to it.

### 5.6 Review and approve the plan

At the approval gate, look at what the agent proposes before you approve:

```sh
git worktree list                         # find the run's worktree and branch
cd ../your-clone.pdd-worktrees/FOLDER     # the folder from the list
git status                                # the files that the agent wrote
ls "$(git rev-parse --git-dir)/pdd/workflows/RUN_ID/artifacts/"   # handoff files (JSON)
```

The handoff files have the agent's summary, the list of files and the proposed test commands. Read the proposed expectations and test cases. Approval fixes this exact plan and these exact test commands for the rest of the run.

```sh
pdd workflow resume RUN_ID --decision approve
```

There is no "reject" decision. Do not edit the proposal files to change the plan: PDD refuses to go on when its saved input changed. If the plan is wrong, leave the run, and open a new, clearer issue.

### 5.7 Optional stages

`bug` and `feature` have optional stages: `visual`, `try` and `prompt PR`. At each one, the run stops and asks you:

```sh
pdd workflow resume RUN_ID --decision approve   # run this optional stage
pdd workflow resume RUN_ID --decision skip      # leave it out
```

`skip` works only on optional stages. A choice stays saved, also after an interruption.

About the optional prompt PR:

- **Skip it (recommended at first).** The prompts, the Story, the tests and the code come together in one PR.
- **Approve it.** PDD opens a separate PR with only the prompts, the Story and the cases. You merge that PR first. Then, in the run's worktree, bring that merge into the run's branch with normal Git (for example `git fetch origin` and `git merge origin/main`), with a clean worktree and the approved files unchanged. Then run `pdd workflow resume RUN_ID --decision approve`. PDD does not do this Git step for you.

### 5.8 Read the result line

Each `run`, `resume` and `attach` ends with one line: `STATE: run RUN_ID / STAGE. MESSAGE`.

| State | Exit code | Meaning |
|---|---|---|
| `completed` | 0 | All steps are done, and the PR is merged |
| `waiting` | 2 | The run waits for you: an approval, an optional choice or a merge |
| `failed` | 1 | The run stopped. Read the message |
| `recovery_required` | 1 | PDD cannot prove what happened. It will not repeat an effect blindly. Read the message |

`pdd workflow resume RUN_ID` without a decision only shows where the run is. It starts no new agent, push or PR.

### 5.9 If you closed the terminal

In this alpha, the `run` or `resume` command is the controller of the run. If you close its terminal, the agent of the current stage can go on in Herdr, but PDD does not move to the next stage. The same happens when one stage takes more than 30 minutes: the command stops with `stage_wait_timeout`.

1. Open a terminal in your clone. Find the run ID (see [5.4](#54-find-the-run-id)).
2. Check the stage: `pdd workflow resume RUN_ID`. If the agent still works, PDD says that the stage is not resolved yet. Wait, or look with `pdd workflow attach RUN_ID`.
3. When the agent is done, the message says that the stage has a candidate handoff. Go on with `pdd workflow resume RUN_ID --decision approve`.

Note: in step 3, `--decision approve` also says yes to the next stage if that is an optional stage.

### 5.10 Many issues at once

Each issue gets its own branch, worktree and Herdr session. You can run several issues at the same time, each in its own terminal. Each stage is a full agent session on your machine. Many runs at once use a lot of memory and agent quota.

<a id="make-a-workflow-your-own"></a>

## 6. Make a workflow your own

A workflow is a folder with a `workflow.json` file and one Markdown file per stage. The bundled ones are in the package. Copy one into your project and edit it:

```sh
cd your-project
mkdir -p .pdd/workflows
cp -R "$(npm prefix -g)/lib/node_modules/pdd/.pdd/workflows/small-change" .pdd/workflows/
pdd workflow list
```

`pdd workflow list` now shows `small-change  project`. Rules:

- A project folder replaces the bundled workflow with the same name, as a whole. PDD does not mix in bundled files.
- To add a new workflow, give the folder a new name and set the same `name` in its `workflow.json`. Names use lowercase letters, digits and single hyphens, start with a letter and have at most 64 characters.
- Stage kinds are `agent`, `human`, `pr` and `merge`. Use a bundled `workflow.json` as your example. Unknown fields are refused.
- If a definition is not valid, `pdd workflow list` and `pdd workflow run` refuse with a message.
- Make your edits before you start a run. A running run keeps its saved copy. If you edit the workflow during a run, PDD refuses to go on.

Commit the `.pdd/workflows` folder so that your team gets the same workflows. The full format is in [workflows.md](workflows.md#edit-workflows).

## 7. The Prompting guide and the PDD skill

- [The Prompting guide](prompting-guide.md) is the method: say what and why, keep the visible behavior and edge cases, give each rule one owner, and write expected results without looking at the code.
- [The PDD skill](../skills/pdd/SKILL.md) tells an agent how to use the guide: load the whole guide first, build only when asked, and report honestly.
- `pdd session` and every workflow stage load both for you.
- In a chat that you opened yourself, have the agent read the full output of `pdd --skill` before it writes a Story:

```sh
pdd --skill | less
```

The [ticket-status example](../examples/ticket-status/README.md) shows a full prompt, Story, cases, code and tests.

## 8. Shell completion

`pdd completion bash` and `pdd completion zsh` print a completion script. They do not change your shell files. To turn it on, add one line to your shell startup file:

```sh
source <(pdd completion zsh)    # in ~/.zshrc, after compinit
source <(pdd completion bash)   # in ~/.bashrc
```

<a id="clean-up-after-a-run"></a>

## 9. Clean up after a run

PDD does not remove old worktrees, branches or Herdr sessions. Clean up only runs that are completed (the PR is merged) or that you gave up.

```sh
git worktree list                                   # runs show as your-clone.pdd-worktrees/FOLDER [pdd/...]
git worktree remove ../your-clone.pdd-worktrees/FOLDER
git branch -D pdd/small-change-42-1a2b3c4d          # the run's local branch
```

Removing a worktree also removes that run's records. Do not remove a worktree while its run goes on.

Each run has its own Herdr session. Its name starts with `pdd-`:

```sh
herdr session list
herdr session stop NAME      # only when no run uses it
herdr session delete NAME
```

Do not run `herdr server stop` without a session name. That stops your default Herdr and every agent in it.

Keep the `.git/pdd` folder in your clone. It holds the claims that stop two runs on one issue.

## 10. Update and uninstall

Update to the newest alpha:

```sh
npm install -g github:promptdriven/pdd#alpha
pdd --version
```

Uninstall:

```sh
npm uninstall -g pdd
```

PDD Alpha 0.1.0 makes no folder in your home directory. Leftovers are only in your clones: `.git/pdd`, the `*.pdd-worktrees` folders, `pdd/...` branches and the `pdd-` Herdr sessions. See [Clean up after a run](#clean-up-after-a-run).

## 11. Known limits

This is an alpha. These limits are known today:

- **Closing the terminal stops the run's progress.** See [5.9](#59-if-you-closed-the-terminal). A fix ("never lose work") is in progress: it will keep the controller running in Herdr.
- The `run` and `resume` commands keep your terminal busy until the run stops at a gate or ends. The run ID shows only when the command stops (see [5.4](#54-find-the-run-id)).
- The controller waits at most 30 minutes for one stage. Then it stops with `stage_wait_timeout`, and the agent can go on. Continue as in [5.9](#59-if-you-closed-the-terminal).
- There is no command to list your runs, to stop a run or to clean up. `pdd workflow list` lists workflows, not runs.
- One run per issue in a clone. A second `pdd workflow run` on the same issue points back to the first run and starts nothing new.
- There is no "reject" decision at the approval gate.
- A busy or rate-limited model (HTTP 429, capacity or quota) can fail a stage. `resume` may not recover it. Then open a new issue and start again.
- If your agent is not signed in, a stage can stop or hang at a sign-in screen. Check `codex login status` before you start, and look with `pdd workflow attach RUN_ID` if a stage takes very long.
- The PR step can fail when an agent left files that are not committed. You can finish by hand: in the run's worktree, commit the files, `git push -u origin HEAD` and `gh pr create`.
- The PR title is the last commit message. The PR body is short and does not link the issue. Edit both on GitHub, and add `Closes #42`, before you merge.
- PDD refuses to go on when the run's worktree or branch changed after its saved input. Do not edit files there during a run.
- `small-change` has made real PRs. `bug` has made one real PR. `feature` is tested only with stand-ins, not on real issues. Claude Code inside workflow runs is less tested than Codex.
- Every session and every stage starts with the full guide (about 21,000 tokens). This uses your agent plan's quota.
- Herdr 0.9.1 is the tested version. Other versions may work, but they are not tested.

## 12. Troubleshooting

| You see | What to do |
|---|---|
| `pdd --version` does not print `0.1.0` | Another `pdd` comes first. See [section 3](#3-if-you-have-the-old-python-pdd). |
| `The native codex CLI is not on PATH` | Install Codex and sign in, or use `--agent claude`. |
| `failed: run (not started). Command failed: git rev-parse --show-toplevel` | You are not in a Git clone. `cd` into your clone. |
| `failed: run (not started). workflow_github_command_failed` | Check `git remote -v` (a GitHub `origin`), `gh auth status`, and that the issue exists in this repository. |
| A message about `refs/remotes/origin/...` or a missing base | Run `git fetch origin`. |
| `This issue already has its original assigned run` | One run per issue. Resume that run, or open a new issue. |
| `Optional step: resume with --decision approve ... or --decision skip` | Choose: see [5.7](#57-optional-stages). |
| `Waiting for actual merge of <URL>` | Review and merge the PR on GitHub, then run `pdd workflow resume RUN_ID`. |
| `Original native stage remains unresolved` | The agent still works, or it is stuck. Look with `pdd workflow attach RUN_ID`. |
| `stage_wait_timeout` | The stage took more than 30 minutes. The agent can still work. See [5.9](#59-if-you-closed-the-terminal). |
| `prompt_activity_stalled` | The agent did not start to work. It may show a sign-in screen or a question. Look with `pdd workflow attach RUN_ID`. |
| `Workflow definition or Markdown source changed` | You edited the workflow during a run. Put it back, or start a new run on a new issue. |
| `Workflow definitions could not be read or validated` | A file in your `.pdd/workflows` folder is not valid. Fix it or remove the folder. |
| `npm outdated -g` shows `pdd` 0.4.14 | That is the unrelated registry package. Ignore it. Do not run `npm update -g`. |

## 13. Report a problem

[Open an issue](https://github.com/promptdriven/pdd/issues/new?title=%5Balpha%5D%20) on `promptdriven/pdd` and put **[alpha]** at the start of the title. Please add:

- your OS, and the output of `pdd --version`, `node -v`, `git --version` and `herdr --version`;
- the agent (Codex or Claude Code) and its version;
- the command you ran, the run ID and the last 10 lines of output;
- what you expected, and what happened.

Do not paste tokens, passwords or private code.
