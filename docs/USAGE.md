# PDD Alpha usage guide

This guide is for people who install PDD Alpha 0.1.7 from the `alpha` branch of `promptdriven/pdd`. Each section has commands that you can copy.

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

Do these steps in this order:

| Step | Command | When |
|---|---|---|
| 1. Install the skills | `npx skills add promptdriven/pdd` | Always. Add `-g` for all your projects |
| 2. Set up the repo | The `pdd-setup` skill in Codex or Claude Code | Once for each repo |
| 3. Install the pdd command | `npm install -g github:promptdriven/pdd#alpha` | Only for runs with PRs, and for `pdd check`, `pdd try` and `pdd approve` |

### 2.1 Install the skills

```sh
cd your-project
npx skills add promptdriven/pdd       # for this project
npx skills add promptdriven/pdd -g    # for all your projects
```

This is the standard skills installer. It needs only Node.js. [Section 4](#4-the-pdd-skills) tells where the skills go. Then do [step 2](#5-set-up-a-repo-and-use-the-skills).

### 2.2 Install the pdd command

You need the pdd command only for runs on GitHub issues ([section 6](#6-run-a-workflow-on-a-github-issue)) and for `pdd check`, `pdd try` and `pdd approve` ([section 7](#7-check-prompts-on-the-pdd-runtime)).

```sh
npm install -g github:promptdriven/pdd#alpha
pdd --version   # prints 0.1.7
which -a pdd    # the first line must be in "$(npm prefix -g)/bin"
```

npm downloads the `alpha` branch from GitHub. The package has no dependencies and no build step. The pdd command does not copy the skills on each command. Only `pdd setup` copies them, when they are missing.

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
pdd --version   # PDD Alpha prints 0.1.7
```

Remove the old one with the tool that installed it:

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

PDD is five skills. A skill is a folder of plain Markdown that your agent reads when it needs it. Call a skill with `$pdd-feature` in Codex or `/pdd-feature` in Claude Code (or ask for it by name).

| Skill | What it is |
|---|---|
| [`pdd-prompting`](../skills/pdd-prompting/SKILL.md) | The full [Prompting guide](prompting-guide.md) (`guide.md`), its core rules, how to review a prompt, and `RUNBOOK.md` for runtime checks |
| `pdd-feature` | A workflow for new behavior |
| `pdd-bug` | A workflow for something that is broken |
| `pdd-small-change` | A workflow for a small change that is easy to undo |
| `pdd-setup` | Set up a repo for PDD. It does the same as `pdd setup` |

Where the skills go:

| You run | Codex gets them in | Claude Code gets them in |
|---|---|---|
| `npx skills add promptdriven/pdd` | `.agents/skills/` in your project | `.claude/skills/` in your project |
| `npx skills add promptdriven/pdd -g` | `~/.agents/skills/` | `~/.claude/skills/`, or `$CLAUDE_CONFIG_DIR/skills/` when you set that variable |
| `pdd setup`, when the skills are missing | `~/.agents/skills/` | `~/.claude/skills/`, or `$CLAUDE_CONFIG_DIR/skills/` when you set that variable |

`pdd setup` copies the skills only when your agent does not have them yet, and says where. If `npx skills` already installed them, it copies nothing. When those skills differ from the skills of this pdd, `pdd setup` says so and prints the command that updates them: `npx skills update -g` (or `-p` for a copy in your project). pdd never copies the skills into your repo.

Each copy that pdd makes has a marker file, `.pdd-skill.json`. After you update the pdd command, `pdd setup` replaces an older copy that has this marker. It never touches a copy without the marker, or a symlink, for example an `npx skills` install.

`npx skills add promptdriven/pdd --skill pdd-prompting` installs one skill. `npx skills list` shows what you have.

Do not edit the installed skill folders: an update replaces your edits. To change a workflow, [make your own](#8-make-your-own-workflow).

The skills work in any Codex or Claude Code chat.

## 5. Set up a repo and use the skills

Set up each repo once. Open Codex or Claude Code in the top folder of the repo and call the `pdd-setup` skill:

```
$pdd-setup          # in Codex
/pdd-setup          # in Claude Code
```

If you installed the pdd command, `pdd setup` in the top folder of the repo does the same. It also installs the skills when they are missing. Both do this:

1. They pick `CLAUDE.md` if it exists, else `AGENTS.md`. If neither exists, they make `AGENTS.md`.
2. They add one short block (7 lines) between `<!-- pdd:start -->` and `<!-- pdd:end -->`. The block says that this project uses PDD and that prompts are the source. It names the skills and `pdd workflow run`. It tells the agent to read `RUNBOOK.md` before a runtime check.
3. They keep all other text. A second run changes nothing. They never paste the guide.

Then open Codex or Claude Code as usual, in your project, and call a skill. In Codex:

```
$pdd-feature Add a CSV export button to the orders page.
$pdd-bug The export button does nothing on Safari.
$pdd-small-change Fix the typo in the footer.
$pdd-prompting Review my prompts against the Prompting guide.
```

In Claude Code:

```
/pdd-feature Add a CSV export button to the orders page.
/pdd-bug The export button does nothing on Safari.
/pdd-small-change Fix the typo in the footer.
/pdd-prompting Review my prompts against the Prompting guide.
```

You can also ask for a skill by name, for example "Use the pdd-bug skill for this."

The agent can also pick a skill by itself when your request fits it. It reads the full Prompting guide when it writes or changes a prompt, a Story or test cases. Nothing big is pasted into the chat.

In a chat, the work stays in your folder: no worktree and no automatic PR. To turn a GitHub issue into PRs, start a run (next section). The agent can start it for you when you ask.

## 6. Run a workflow on a GitHub issue

`pdd workflow run` takes one GitHub issue to real PRs. The work happens in a few chats in Herdr. You approve at each gate. pdd opens the PRs. It never merges.

### 6.1 Prepare the repository

- Use a clone of a GitHub repository that you can push to. The `origin` remote must point to it.
- The issue must be in that same repository. It must be an issue, not a PR.
- PDD fetches `origin`'s default branch (for example `origin/main`) and starts the new issue branch there. If that default fetch fails, it warns and uses the last fetched commit. Add `--base BRANCH` to select an existing origin topic branch; an explicit base must fetch successfully before startup.
- If the default branch on GitHub changed, also run `git remote set-head origin -a`, so Git knows the new one.
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

To build on an isolated topic branch, put that base on `origin`, then name its branch (without an `origin/` or `refs/` prefix):

```sh
pdd workflow run bug 2 --base round3/tipjar-workflow-base
```

PDD fetches that exact branch and starts the issue worktree from its commit. A failed fetch or missing branch stops the run; it does not use a local or default branch instead. Startup prints the selected base. The PR targets that saved base, and PDD pushes only its new issue branches. It does not change the repository's default branch. For two PRs, PR 2 stacks on an open PR 1; after PR 1 merges, PR 2 starts from and targets the saved base.

The command returns at once. It prints where the run is and the commands to open and approve it. **You can close the terminal now. There are no time limits.**

### 6.3 What happens

1. pdd reads the issue with `gh`. It makes a new branch (for example `pdd/small-change-42-1a2b3c4d`) and a new Git worktree in the folder `your-clone.pdd-worktrees/` next to your clone. It makes the run folder `your-clone/.git/pdd/runs/42/`.
2. pdd opens the first chat in Herdr, in full-access mode. The Herdr session is `pdd`. Each repo has a workspace with the repo's name. Each run has a tab with the repo name, the issue and the workflow, for example `my-app#42 small-change`. If two repos have the same name, pdd uses `owner/repo`. pdd does not touch your default Herdr session.
3. The chat follows the workflow skill. It gives each step to a fresh subagent. The subagent gets its full brief at once, with file paths, not the chat history.
4. After each step, the agent tells pdd that the step is done. The step notes go into the run folder.
5. At a gate, the chat shows you the result and asks you. Then it stops and waits. It waits as long as you need.
6. When you approve, pdd starts a new chat for the next area. That chat gets the results of the area that you approved.
7. After the last step of an area with a PR gate, pdd pushes the branch and opens the PR.
8. You review and merge the PRs on GitHub. When `pdd workflow status` sees the merge, the run is completed.

With Claude Code, the first chat can ask you once to trust the new worktree folder. This happens when your clone's folder is not trusted in Claude Code yet. `run` prints a hint. Open the chat with `pdd workflow open 42` and answer the question.

The areas of the three workflows (you act at the **bold** ones):

| Workflow | Areas and steps |
|---|---|
| `feature` | story (understand, visual?, prompt-story), **approve**, prompt PR (check, try?), **try it and approve**, PR 1 opens, **code now or stop?**, code (build, verify, formal) opens PR 2, **merge** |
| `bug` | story (reproduce, prompt-story), **approve**, prompt PR (check, try?), **try it and approve**, PR 1 opens, **code now or stop?**, code (build, verify, formal) opens PR 2, **merge** |
| `small-change` | plan (scope), **approve**, build (change, verify, formal) opens one PR, **merge** |

`?` marks an optional step. Each area is one chat. The code area of `feature` and `bug` runs only when you ask for it. [workflows.md](workflows.md) tells what each step does.

**A big request: a plan and many Stories.** In `feature`, the understand step counts the separate behaviors in the issue. For one behavior, it writes one Story. For more, it writes a plan, `user_stories/PLAN.md`: a numbered list with one line for each Story, in build order. Each Story gets its own test file, `tests/<story>.json`. At the story gate, the chat gives the paths of the Story files and the plan, shows the plan, and ends with "Reply 'I approve' here or run `pdd workflow approve 42`, or tell me what to change." You can answer, for example:

- "Make it one Story."
- "Split part 5."
- "Change Story 5: also refuse an empty order." The chat redoes only that Story and its test file.

Before PR 1, the check shows one `Runtime check` line for each Story. `pdd workflow status` then shows, for example, `Stories: 4 of 5 pass (✗ refunds)`.

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
| Ask for changes | Say what to change | `pdd workflow changes 42 "Also cover an empty list."` (a plain "I approve" is not a change: pdd tells you to run `approve`) |
| Stop the run | (no chat answer) | `pdd workflow cancel 42` |

Rules:

- Only you can approve. An agent never approves for you. When you approve in the chat, the agent runs `pdd workflow approve`. pdd then checks that your own message is in the chat after the gate.
- In a terminal, `approve` asks y/N. The question shows the repo, the issue and its title.
- pdd asks y/N only in a normal terminal. A terminal tab of your own in Herdr is one, but the chat's own pane is not. Inside Claude Code (its `!` prefix sets `CLAUDECODE=1`) or Codex, pdd looks for your answer in the chat. If it finds none, it tells you to run `approve` in a normal terminal or to answer in the chat.
- `status` says "waiting for you" when the chat has asked you. Before that, it says that the agent writes the gate message.
- `approve` without N: in a run's worktree, it approves that run. Elsewhere in the repo, it approves the one run that waits for you. If more than one run waits, it lists them.
- Changes stay in the same chat. The chat revises and asks you again.
- `cancel` closes the chat tabs of the run. pdd keeps the worktree and the branch. A new `pdd workflow run` on the same issue then starts fresh.

### 6.6 Optional steps

`visual` and `try` are optional. Before each one, the chat asks you, for example "Do you want a visual design step? yes/no", and waits for your answer. They are not gates: answer in the chat.

For a page or a screen, the chat recommends `visual`. It writes the app map, so the Try page shows the real screen and your keys or taps work. A page with no visual step still gets an app map and a `render` operation that returns its HTML, so you can try it, and its tests check what the page shows. At the story gate, you can open a Try before the check: `pdd try <story>`, or `pdd try <story> --new` when there is an app map. The check still runs first in the prompt PR area.

### 6.7 The PRs and the merge

`small-change` makes one PR with the change and its tests. Its body says `Closes #42`.

`feature` and `bug` make up to two PRs:

| PR | What it holds | When |
|---|---|---|
| PR 1 | The prompt, the Story and the test cases. Its title ends with "(prompt, Story and tests)", or "(prompt and Story)" when it has no test file | After the prompt PR area. Its body says `Part of #42` |
| PR 2 | The code | Only when you ask for it. Its body says `Closes #42` and that it builds on PR 1. It shows the PR 1 test cases run on the real code (a table: expected, prompt result, code result) and a formal check line: Proved, Failed with a counterexample, Not run or Not applicable, each with a reason. The tables come first; long commands and output are folded in closed `<details>` blocks |

**Try before PR 1.** After the prompt PR area, the chat shows one `Runtime check` line for each Story, with its report link, and the Try links. Try it. Then approve, or ask for changes. pdd opens PR 1 only after you approve. When there is nothing to try, the chat asks you only to approve.

Then the chat shows the PR 1 link and asks: "Do you want the code PR now, or stop here and merge PR 1 first? To make the code PR later, run `pdd workflow approve 42`."

The PR 1 body is short. For a bug, it starts with the verdict line (for example "Verdict: the bug is in the PROMPT …") and the `Before ✗ … → after ✓ …` line with both report links. Then comes one `Runtime check (<story>)` line for each Story. With more than one Story, pdd adds them up in a `Runtime check (all Stories)` line. A `Report (<story>)` link follows for each Story. Then come `Part of #42`, a line that names any prompts that are still `draft`, and one short line for each step. PR 1 has no `verify.md` and no Try links.

- **Code now:** say so in the chat in your own words, or run `pdd workflow approve 42`. The code area starts in a new chat. PR 2 is stacked on PR 1's branch. Merge PR 1 first.
- **Stop:** the run waits. `status` says that PR 1 is open. If you merge PR 1 and do not go on, the run ends as "done at PR 1". You can still run `pdd workflow approve 42` later. Then PR 2 starts from the merged prompts on the run’s saved base branch.
- If PR 1 says "Draft prompts: …", approve each one with `pdd approve prompts/NAME.prompt.md` before you merge ([section 7.1](#71-approve-a-prompt)). An agent never sets `approved`. The code is built only from approved prompts, so pdd offers the code PR only after that. It prints the lines to run: `pdd approve` in the run's worktree, then `pdd workflow approve 42`. pdd then commits your approval, pushes it to PR 1, removes the "Draft prompts" line from PR 1 and starts the code area. If you committed in the worktree yourself, pdd pushes those commits to PR 1 too, so they do not end up in PR 2.
- If a test case still fails on the code after two more build rounds, PR 2 opens anyway with "✗ N vectors fail" at the top. Read it before you merge.

**When the chat asks you something in the middle of a step,** the agent first runs `pdd workflow ask` (only agents use it). Then `pdd workflow status` shows "waiting for you: <the question>". Answer in the chat, or from any terminal with `pdd workflow changes 42 "your answer"`.

For all workflows:

- The verify step runs in a fresh subagent that did not write the code.
- verify writes the exact test commands and their real output to `verify.md` in the run folder.
- The PR body has the step summaries. PR 2 and the `small-change` PR also have `verify.md`. When a runtime check ran, the body starts with its `Runtime check` lines and report links. Runtime report links expire after 7 days.
- pdd does not run the tests itself. Read the test output in the PR before you merge.
- pdd never merges. You review and merge on GitHub.

### 6.8 Check a run

```sh
pdd workflow status 42
pdd workflow status               # all runs in this repo
pdd workflow status --all         # every run on this machine, in all repos
pdd workflow status --cancelled   # also show the cancelled runs
pdd workflow status --all --json  # the same list as data
```

`status` shows the area, the step, what the run waits for, and the PRs with their CI state. For a run with many Stories, it also shows how many pass, for example `Stories: 4 of 5 pass`. Without N, it shows all runs in this repo. In a run's worktree, it shows that run. N is the issue number in the current repo. If several repos have a run for that number, use `owner/repo#42`.

`--all` lists every run on this machine, in all repos. Plain `status` outside a Git repo does the same. The list shows the runs that wait for you first, then the runs that work, then the runs with an open PR, then the runs that are done. Cancelled runs are hidden. `--cancelled` shows them. `--json` gives the same list as data.

### 6.9 Close the terminal or restart

The chats run in Herdr, not in your terminal. You can close the terminal at any time. Nothing has a time limit.

After a restart, run `pdd workflow open 42`. pdd resumes the chat of the current area (`codex resume` or `claude --resume`) in its tab.

### 6.10 Many issues at once

Each issue gets its own branch, worktree and Herdr tab. You can start several runs. An issue can have only one active run: a second `run` on the same issue is refused. After `pdd workflow cancel N`, you can run it again, and the new run starts fresh. Each step is a full agent session on your machine. Many runs at once use a lot of memory and agent quota.

## 7. Check prompts on the PDD runtime

The PDD runtime runs a prompt as a program: an AI model on the PDD server reads the `*.prompt.md` file and acts as the program. `pdd check` sends your prompts, Stories and tests there and checks each answer against its test. `pdd try` makes a link where a person can use the prompt by hand.

Both commands sign in with your GitHub login (`gh auth status`). They send the selected Stories, their authored tests and the prompts and context those tests need. Every sent file must be Git-visible (tracked or new, not ignored). The selected payload must fit 10 MB and 10,000 files; secret names, symlinks and non-regular files are refused. Unrelated source files are not sent. pdd keeps run state in `~/.pdd/runtime`, never in your repo.

The upload follows each test's entry prompts and their `calls` targets, test `context` files, and local links in each prompt's `## Dependencies`. A dependency list item may instead begin with a backticked file path, such as ``- `data/menu.json`: required runtime context``. Schema labels, code examples, installation paths and backticked names in descriptions do not declare extra files. Markdown context may declare its own Dependencies. Paths in links are relative to their declaring file; repository-root spellings also work when Git names them. A linked fragment includes the whole file. Local image links, including SVG mockups, go with their prompt. Ordinary navigation links outside Dependencies and remote URLs do not supply context. A missing declared file stops the upload and names its referrer.

Try includes a valid default `app-map.json` (else `app/app-map.json`), including screen, router, handler and after-operation prompts and stylesheets. Check and lint use no app map. To preview a Try with a custom map, run `pdd check --files place-order --app-map app/custom-map.json` before `pdd try place-order --app-map app/custom-map.json`.

For extra files, add `pdd-source.json` at the repository root:

```json
{"include": ["docs/shared-policy.md", "data/menu.json"]}
```

`include` is the only key. Entries are exact repository-relative file paths, not folders or patterns, and Git must show them. The same safety and size limits apply. Included prompts and Markdown files bring their declared dependencies too. The config is local selection metadata and is sent only when explicitly included. Try keeps the original test paths: Save as test appends cases to the authored test file.

```sh
pdd check --fill-hash     # fill the hash of draft interfaces; sends nothing
pdd check --files         # exact upload manifest and byte sizes for all Stories; offline
pdd check --files place-order  # preview only this Story; offline
pdd check --lint          # the server checks the format only, 0 AI calls
pdd check                 # check every story; one table and a report link for each
pdd check place-order     # check one story
pdd check --read          # show the last results again; sends nothing new
pdd try place-order       # open a Try link in your browser; it ends in 24 hours
pdd try --stop place-order
```

In a terminal, `pdd check` waits until every check ends. When an agent runs it (no terminal), it waits at most 90 seconds, then prints the table and `Still running. Read the results later with: pdd check --read BATCH`; the checks keep running on the server. `--timeout MIN` (1 to 120 minutes) sets the limit in both cases. While checks run, pdd prints one line every 30 s, for example `Still running: 2 of 3 Stories done · 14 AI calls so far · 4 min`. Press Ctrl-C to stop waiting, and run `pdd check --read` to see the results.

After the table, `pdd check` prints one `Runtime check` line for each Story that you can paste into a PR, for example `Runtime check (place-order): ✓ 4 of 4 criteria · 11/11 checks · 2 AI calls`. With two or more Stories, the overall `Runtime check:` line comes last.

Run `pdd check --lint` (or `pdd check --lint STORY`) before a real check. The server checks the format of the prompts, Stories and tests only. It uses 0 AI calls and shows every problem at once, so you can fix them all before you spend AI calls.

A prompt whose interface is still `draft` can be checked, and its result is marked DRAFT. A DRAFT pass is not an approval.

| Exit | Result | What to do |
|---|---|---|
| 0 | passed | Nothing. |
| 1 | a check failed | Look at the failed check. You decide: change the prompt or the expected value. |
| 4 | refused | A file breaks a rule and nothing was judged. Fix the file. |
| 5 | not run | Sign-in, a busy server, no AI room, a login that is not invited, or an old pdd. Read the one line that pdd prints. |
| 3 | unknown or still running | Run `pdd check --read` later. Never send it again. |
| 2 | command error | Run `pdd check --help`. |

Your agent reads [RUNBOOK.md](../RUNBOOK.md) in the pdd package: the three files (prompt, Story, test), their rules and what to do with each result.

The runtime address is set in one place in pdd. You do not need to set it.

### 7.1 Approve a prompt

Only a person approves a prompt. An agent never sets `"status": "approved"`.

```sh
pdd approve prompts/place_order.prompt.md
```

pdd shows the prompt's runtime interface in plain words: each input, result and error. Then it shows the text that you approve: the changes since the last approved version in Git, or the whole text when there is none, at most 40 lines. Then it asks `Approve prompts/place_order.prompt.md? y/n`. When you answer `y`, pdd sets the prompt to `approved` and fills its hash. Any other answer changes nothing.

- `pdd approve` works only for a person at a terminal. When an agent runs it, pdd tells the agent to ask you to run it.
- If the prompt has schema problems, pdd lists them and does not approve.
- If an approved prompt changes, `pdd check` refuses it as stale. The agent sets it back to `draft`, and you approve it again.

### 7.2 Try a Story

`pdd try STORY` makes a Try link and opens it in your browser. On the Try page, you use the prompt by hand. The link ends after 24 hours, or with `pdd try --stop STORY`.

In your terminal, `pdd try` keeps waiting while the page is open:

- When you save a case on the Try page, pdd adds it as a new step to the Story's test file.
- When you click **Approve** on the Try page, pdd asks `Approve PROMPT? y/n` in this terminal. Only your `y` there approves the prompt. If the prompt changed after you clicked, pdd does not approve it.

Use `--no-open` to get the link without opening a browser. Use `--no-wait` to return at once. When an agent runs `pdd try`, it reads the saved cases once and returns. Anyone with a Try link can use it, so the link never goes into a file, a PR or an issue.

### 7.3 When a check does not run

| pdd prints | What to do |
|---|---|
| `No tests found. A test is a Git-visible *.json file with "schema_version": "prompt-runtime.program-scenario.v1".` | pdd also says why for each near miss: a `tests/*.json` file without that `schema_version`, a prompt that ends in `.prompt` instead of `.prompt.md`, or a prompt with no Runtime interface block. Fix the files that it names. See RUNBOOK.md section 2. |
| `Your GitHub login NAME is not on the PDD runtime invite list yet. Ask the PDD team to add you.` | Ask the PDD team to add your GitHub login. Exit code 5. |
| `Please update pdd: npm install -g github:promptdriven/pdd#alpha` | Your pdd is too old for the runtime. Run that line, then `pdd setup`. Exit code 5. |

## 8. Make your own workflow

A workflow is a skill folder. Copy one of the PDD workflows as `pdd-NAME`, and edit it. For example, in your repo:

```sh
mkdir -p .agents/skills
cp -RL ~/.agents/skills/pdd-bug .agents/skills/pdd-mybug   # or from .agents/skills/pdd-bug
rm -f .agents/skills/pdd-mybug/.pdd-skill.json
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

Update the skills:

```sh
npx skills update        # add -g for the skills of all your projects, -p for this project only
```

Update the pdd command, then let it check the skills:

```sh
npm install -g github:promptdriven/pdd#alpha
pdd --version
pdd setup
```

Uninstall the skills that `npx skills` installed:

```sh
npx skills remove pdd-prompting pdd-setup pdd-feature pdd-bug pdd-small-change      # add -g for the global ones
```

Uninstall the pdd command, the skills that `pdd setup` copied, and its state:

```sh
npm uninstall -g pdd
rm -rf ~/.agents/skills/pdd-{prompting,setup,feature,bug,small-change}
rm -rf ~/.claude/skills/pdd-{prompting,setup,feature,bug,small-change}
# If you set CLAUDE_CONFIG_DIR, also remove the five pdd-* folders in "$CLAUDE_CONFIG_DIR/skills"
rm -rf ~/.local/state/pdd
```

Look before you run `rm -rf`: if `npx skills -g` installed these folders, use `npx skills remove -g` instead.

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
| `pdd --version` does not print `0.1.7` | Another `pdd` comes first. See [section 3](#3-if-you-have-the-old-python-pdd). |
| pdd says that `codex` or `claude` is not on PATH | Install the agent and sign in, or use the other one with `--agent`. |
| A message about `git rev-parse --show-toplevel` | You are not in a Git clone. `cd` into your clone. |
| A message about `refs/remotes/origin/...` or a missing base | Run `git fetch origin`. |
| A GitHub error when the run starts | Check `git remote -v` (a GitHub `origin`), `gh auth status`, and that the issue exists in this repository. |
| `approve` says that more than one run matches | Give the issue number, or `owner/repo#N`. |
| `run` says that the issue already has a run | Use `pdd workflow open N` or `status N`. To start again, run `pdd workflow cancel N` first. |
| `run` prints a hint about Claude Code trust | Run `pdd workflow open N` and answer the trust question in the chat. |
| `run` says that `CODEX_HOME` or `CLAUDE_CONFIG_DIR` does not exist | Set it to a folder that exists, for example `CODEX_HOME=$HOME/.codex`, and run the command again. |
| `status` says "the chat stopped" | No agent runs in the chat. Run `pdd workflow open N` to start it again. If it stops again at once, read the error in the chat. |
| `approve` says that pdd sees an agent environment | Your terminal runs inside Claude Code or Codex. Run `pdd workflow approve N` in a normal terminal, or answer the gate question in the chat. |
| The agent cannot approve for you | pdd found no message from you after the gate. Write your approval in the chat yourself, or run `pdd workflow approve N` in a terminal. |
| The chat stopped and does nothing | Run `pdd workflow open N`. Read the last lines. It can wait for you, show a sign-in screen or hit a rate limit. Answer it, or ask it to go on. |
| The chat is gone after a restart | Run `pdd workflow open N`. It resumes the chat. |
| The agent uses an old PDD skill | Run `npx skills update`. If the pdd command installed the skills, run `pdd setup`. |
| `npx skills add … -g` prints `Failed to install` for some agents | Those agents do not support global skills. Codex and Claude Code still get them. To install only for these two, add `-a codex -a claude-code`. |
| The agent does not know the `pdd-feature` skill | Install the skills: `npx skills add promptdriven/pdd`. Then start a new chat. |
| `pdd check` says `No tests found` | Read the reasons under that line, and fix the files that it names. See [section 7.3](#73-when-a-check-does-not-run). |
| `pdd check` says that your login is not on the invite list | Ask the PDD team to add your GitHub login. |
| `pdd check` or `pdd try` says `Please update pdd` | Run `npm install -g github:promptdriven/pdd#alpha`, then `pdd setup`. |
| `pdd approve is for a person at a terminal` | An agent tried to approve. Run the `pdd approve` line yourself, in a terminal. |
| PR 1 says `Draft prompts: …` | Run `pdd approve` for each prompt that it names, before you merge PR 1. |
| `npm outdated -g` shows `pdd` 0.4.14 | That is the unrelated registry package. Ignore it. Do not run `npm update -g`. |

## 14. Report a problem

[Open an issue](https://github.com/promptdriven/pdd/issues/new?title=%5Balpha%5D%20) on `promptdriven/pdd` and put **[alpha]** at the start of the title. Please add:

- your OS, and the output of `pdd --version`, `node -v`, `git --version` and `herdr --version`;
- the agent (Codex or Claude Code) and its version;
- the command you ran and the output of `pdd workflow status N`;
- what you expected, and what happened.

Do not paste tokens, passwords or private code.
