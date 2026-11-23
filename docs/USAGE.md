# PDD usage guide

This guide is for people who install pdd 0.1.50 from `promptdriven/pdd`. Each section has commands that you can copy.

> [!WARNING]
> **Autopilot agents run with full access.** When running headless Autopilot jobs, PDD starts Codex with `--dangerously-bypass-approvals-and-sandbox`, Claude Code with `--dangerously-skip-permissions`, Gemini CLI with `--yolo`, and Antigravity CLI with `--dangerously-skip-permissions`. The agents do not stop to ask for approval. They can read, change and delete files and run commands as your user. Use Autopilot only in projects and on machines where you accept this.

Contents:

1. [Before you start](#1-before-you-start)
2. [Install](#2-install)
3. [If you have the old Python pdd](#3-if-you-have-the-old-python-pdd)
4. [The PDD skill](#4-the-pdd-skills)
5. [Set up a repo and use `/pdd`](#5-set-up-a-repo-and-use-the-skills)
6. [Work on issues with `/pdd` and Autopilot](#6-work-on-issues-with-pdd-and-autopilot)
7. [Check prompts on the PDD interpreter](#7-check-prompts-on-the-pdd-interpreter)
8. [Customize project lint and verification rules](#8-customize-project-lint-and-verification-rules)
9. [Shell completion](#9-shell-completion)
10. [Clean up worktrees and state](#clean-up-after-a-run)
11. [Update and uninstall](#update-and-uninstall)
12. [Known limits](#12-known-limits)
13. [Troubleshooting](#13-troubleshooting)
14. [Report a problem](#14-report-a-problem)
15. [Use your program for real with `pdd simulate`](#15-use-your-program-for-real-with-pdd-simulate)
16. [Ask your agent in the PDD Simulator](#16-ask-your-agent-in-the-pdd-simulator)

## 1. Before you start

PDD runs on your own machine, with your own agent account and your own GitHub account. Remote `pdd test`, `pdd lint --remote`, `pdd simulate` and the Try tools in `pdd mcp` use the PDD interpreter with your GitHub login, which needs PDD Cloud approval.

Check your tools:

```sh
node -v               # Node.js 22.16.0 or newer
git --version         # Git
gh auth status        # "Logged in to github.com"
codex login status    # "Logged in ..."  (or use Claude Code)
```

PDD needs Node.js 22.16.0 or newer. The other tools work with the versions you have. If a tool is missing:

| Tool | How to get it |
|---|---|
| Node.js 22.16.0 or newer | [nodejs.org](https://nodejs.org), or your Node version manager |
| Git | [git-scm.com](https://git-scm.com) |
| GitHub CLI | [cli.github.com](https://cli.github.com). Then run `gh auth login`. If `git push` asks for a password later, run `gh auth setup-git`. |
| Codex CLI | [developers.openai.com/codex/cli](https://developers.openai.com/codex/cli/). Then run `codex login`. |
| Claude Code | [code.claude.com](https://code.claude.com/docs/en/overview). Start `claude` once and sign in. |
| Gemini CLI / Antigravity CLI | Install and sign in to the agent you choose. |

Without `--agent`, pdd selects the first ready agent in order: Codex, Claude Code, Gemini CLI, then Antigravity CLI (`agy`). An explicit agent or configured launcher selects that choice. PDD is tested on macOS and Linux.

## 2. Install

Do these steps in this order:

| Step | Command | When |
|---|---|---|
| 1. Install the pdd command | `npm install -g @promptdriven/pdd` | Once on your machine |
| 2. Set up your machine | `pdd setup` | Once on your machine: installs `/pdd` globally and previews PDD Simulator MCP registration |
| 3. Set up a repo | `pdd init` | Once in the top folder of each repository |

### 2.1 Install the pdd command

You need the pdd command for offline repo tools (`pdd init`, `pdd status`, `pdd lint`, `pdd prove`, `pdd update`, `pdd owner`, `pdd files`), interpreter commands (`pdd test`, `pdd simulate`, `pdd approve`), and headless Autopilot (`pdd autopilot`).

```sh
npm install -g @promptdriven/pdd
"$(npm prefix -g)/bin/pdd" --version  # reports PATH conflicts without changing files
pdd --version   # prints 0.1.50
which -a pdd    # the first line must be in your global npm or Volta bin folder
```

Important:

- Always install and update `@promptdriven/pdd` (or `github:promptdriven/pdd` for a Git tag/branch).
- Do not run `npm install -g pdd`. That installs a different, unrelated package from the npm registry.
- Do not run `npm update -g`. npm thinks that the unrelated registry package is a newer version of PDD, and it would replace your pdd with it. You can see this with `npm outdated -g`.
- If npm says `EEXIST` on `<prefix>/bin/pdd`, an unscoped `pdd` npm package still owns `bin/pdd` while PDD installs as `@promptdriven/pdd`. Remove the unscoped package first instead of passing `--force`: `npm uninstall -g pdd && npm install -g @promptdriven/pdd`.
- If npm says `EACCES` (permission denied), your global npm folder belongs to root. Use a Node version manager (such as Volta or nvm), or set your own npm prefix. Do not use `sudo`.

### 2.2 Set up your machine (`pdd setup`)

```sh
pdd setup
```

`pdd setup` installs the global `/pdd` skill into user folders (marked with `.pdd-skill.json`), removes retired PDD split skills and their agent-folder/dangling symlinks, and previews PDD Simulator MCP registration for detected Codex, Claude Code, Gemini, and Antigravity configs without editing any repository. Pass `--yes` to apply previewed MCP registration without prompting, `--skills-dir PATH` for a custom folder, or `--upgrade` to sync skills and silently refresh only already-registered stale PDD MCP entries.

**Alternative (skill-only installer, without MCP registration):**

```sh
npx skills add promptdriven/pdd -g --skill pdd    # for all your projects
npx skills add promptdriven/pdd --skill pdd       # for one project only
```

[Section 4](#4-the-pdd-skills) lists where the skill goes. Next, run `pdd init` inside your repository ([Section 5](#5-set-up-a-repo-and-use-the-skills)).

`pdd upgrade` updates a global npm or Volta `@promptdriven/pdd` installation and then delegates skill sync, retired-skill cleanup, and stale PDD MCP refresh to the newly installed binary (`pdd setup --upgrade`). Normal CLI commands also refresh existing PDD-managed user folders once per version without touching custom skills or local git-checkout symlinks.

### 2.3 Start Autopilot on your repository

Follow [Autopilot on your own repository](../README.md#autopilot-on-your-own-repository)
for the ordered installation, sign-in, init, doctor, start, status and stop path.
Use Node.js 22.20 or newer. Repository writes need write permission.
`pdd autopilot doctor` reads readiness without GitHub writes or AI calls.
Start runs the same checks before it changes local state or starts work.
Only missing or signed-out agent sign-in refuses preflight. All other findings
warn with fix commands in observe and auto mode. Native start keeps its own guards.
Manual gates need your later approval. Explicit auto setup and start can delegate
ordinary automatic gates and eligible merges. Strict approvals and required
human reviews still need a person. An empty trust list still trusts the owner
and write-access users. Draft prompts may need approval at the first check;
doctor lists them without approving them. Interpreter access is checked without
running a prompt, so native green CI and doctor do not prove prompt behavior.

## 3. If you have the old Python pdd

The Python pdd (0.0.x) is on the [`v1` branch](https://github.com/promptdriven/pdd/tree/v1) and on [PyPI](https://pypi.org/project/pdd-cli/) as `pdd-cli`. It also installs a command named `pdd`. On one machine, only the first `pdd` on your PATH runs.

Run this pdd by its absolute path to diagnose the selection: `"$(npm prefix -g)/bin/pdd" --version`. On a conflict it lists executable paths and reports the selected executable’s version. `pdd --version` keeps just the version on stdout and prints a conflict report to stderr. A program whose version cannot be read stays listed as version unavailable. No installation is removed or replaced.

See all of them:

```sh
which -a pdd
pdd --version   # this pdd prints 0.1.50
```

If you choose to remove the Python installation, use the tool that installed it:

```sh
uv tool uninstall pdd-cli     # if you used uv
pipx uninstall pdd-cli        # if you used pipx
pip uninstall pdd-cli         # if you used pip (inside the same Python environment)
hash -r                       # forget the old path (zsh users can also run: rehash)
which -a pdd
```

If you want to keep the old one, call this pdd by its full path:

```sh
"$(npm prefix -g)/bin/pdd" --version
```

Activating an environment later, for example `conda activate pdd`, can reorder PATH and shadow this pdd again. Activate the environment first, then prepend the directory that contains this `pdd` command and clear the shell cache:

```sh
conda activate pdd
export PATH="$(npm prefix -g)/bin:$PATH"
hash -r
```

Use the absolute Node-plus-pdd command printed by the diagnostic when the environment selects a different Node installation or pdd is running from a source checkout.

Autopilot workers always get the full path of this pdd. They are not affected by your PATH. Only the commands that you type are.

<a id="4-the-pdd-skills"></a>

## 4. The PDD skill

PDD exposes one skill: [`pdd`](../skills/pdd/SKILL.md), with co-located references in `skills/pdd/references/`. Call it with `$pdd` in Codex or `/pdd` in Claude Code (or ask for it by name); it routes product planning, features, bugs, and small changes and loads only the reference needed for the task.

| Reference | What it covers |
|---|---|
| [`skills/pdd/SKILL.md`](../skills/pdd/SKILL.md) | The single PDD workflow router (`product`, `bug`, `feature`, `small-change`), `pdd status --json` orientation, pre-code review, and real-path verification |
| [`references/prompting.md`](../skills/pdd/references/prompting.md) | How to write, split, and review module prompts (`*.prompt.md`) |
| [`references/stories.md`](../skills/pdd/references/stories.md) | How to write Stories (`user_stories/*.md`) and scenario test files (`tests/*.json`) |
| [`references/product.md`](../skills/pdd/references/product.md) | How to plan multi-part products with shared contracts |
| [`references/ports-and-cli.md`](../skills/pdd/references/ports-and-cli.md) | Ports, interfaces, CLI programs, HTTP routes, and persistence |
| [`references/ui-and-screens.md`](../skills/pdd/references/ui-and-screens.md) | Screens, HTML rendering, app maps, and interactive simulation |
| [`references/verification.md`](../skills/pdd/references/verification.md) | Real-path verification, `pdd.json` `verify.paths` Feature Map, `pdd prove`, and Deliberate-Break Probe |
| [`references/formal.md`](../skills/pdd/references/formal.md) | Code-bound formal verification (3-tier stack, Z3 isolation, mutation control; loaded only for invariant-heavy work) |

Where the skill goes:

| You run | Codex & Gemini CLI | Claude Code | Antigravity |
|---|---|---|---|
| `npx skills add promptdriven/pdd` | `.agents/skills/` in your project | `.claude/skills/` in your project | — |
| `npx skills add promptdriven/pdd -g` | `~/.agents/skills/` | `~/.claude/skills/`, or `$CLAUDE_CONFIG_DIR/skills/` | — |
| `pdd setup` | `~/.agents/skills/` | `~/.claude/skills/`, or `$CLAUDE_CONFIG_DIR/skills/` (skips copying `/pdd` when the Claude Code plugin is installed, while cleaning retired PDD split skills and symlinks) | `~/.gemini/config/skills/` |

`pdd setup` installs missing skills in user folders and says where. Pass `--skills-dir PATH` to sync a custom folder. It updates eligible PDD-managed user copies (either `.pdd-skill.json`-marked or carrying `pdd-skills:` frontmatter in `SKILL.md`) and cleans retired PDD skills. When a project copy or a symlinked/unmanaged copy is older than this pdd or differs from its skills, `pdd setup` says so and prints the command that updates it: `npx skills add promptdriven/pdd -g -a codex -a claude-code -y` (without `-g` for a copy in your project). `pdd --version` warns on stderr when your skills are older or retired PDD skills remain. pdd never copies skills into your repo.

Each copy that pdd writes carries a marker file, `.pdd-skill.json`. `pdd setup` upgrades any PDD-managed user copy (`.pdd-skill.json`-marked or `SKILL.md` with `pdd-skills:` frontmatter) when its version is older, when the same version has different files, or when its marker is invalid, and keeps a copy with a newer version. It removes PDD-managed user copies of retired skills (`pdd-autopilot`, `pdd-check`, `pdd-merge`, `pdd-setup`, `pdd-prompting`, `pdd-small-change`, `pdd-bug`, `pdd-feature`, `pdd-product`, `pdd-graph`) and unlinks retired symlinks that are dangling or target another PDD-managed agent skill folder, including when Claude Code has the PDD plugin installed. It never touches unrelated custom skills, unmarked folders without `pdd-skills:` frontmatter, or symlinks pointing into a local git checkout.

`npx skills add promptdriven/pdd --skill pdd` installs the skill directly. `npx skills list` shows what you have. The `pdd-skills:` line at the top of `SKILL.md` shows the version of that skill, for example `pdd-skills: 0.1.50`.

Do not edit the installed skill folders: an update replaces your edits. The skill works in any Codex, Claude Code, Gemini CLI, or Antigravity chat.

<a id="5-set-up-a-repo-and-use-the-skills"></a>

## 5. Set up a repo and use `/pdd`

Run `pdd setup` once on your machine to install the `/pdd` skill globally and preview PDD Simulator MCP tool registration (`--yes` applies MCP registration without prompting; non-interactive runs without `--yes` skip MCP safely). `pdd setup` edits no repository files.

Set up each repo once from its top folder:

```sh
pdd init
```

`pdd init` makes these local edits:

1. It picks `CLAUDE.md` if it exists, else `AGENTS.md`. If neither exists, it makes `AGENTS.md`.
2. It adds one short 4-line block between `<!-- pdd:start -->` and `<!-- pdd:end -->`. The block says that this project uses PDD, that prompts change before code, to run `pdd status` to orient, and to invoke `/pdd` before editing.
3. It keeps all other text and preserves existing line endings (LF or CRLF). A second run changes nothing. It never pastes the guide or edits root `.gitignore` (`.pdd/.gitignore` is written automatically when `.pdd/` is created).
4. It detects the project's language and test command so your agent can verify changes right away.

Then open Codex or Claude Code as usual, in your project, and call `/pdd` (or `$pdd` in Codex):

```text
$pdd Add a CSV export button to the orders page.
$pdd The export button does nothing on Safari.
$pdd Fix the typo in the footer.
$pdd Review my prompts against the Prompting guide.
```

In Claude Code:

```text
/pdd Add a CSV export button to the orders page.
/pdd The export button does nothing on Safari.
/pdd Fix the typo in the footer.
/pdd Review my prompts against the Prompting guide.
```

You can also inspect repository state offline at any time with `pdd status` (or `pdd status --changed --json`). The agent reads only the reference files needed for your task; nothing big is pasted into the chat.

<a id="6-work-on-issues-with-pdd-and-autopilot"></a>

## 6. Work on issues with `/pdd` and Autopilot

### 6.1 Interactive issue work in your coding agent

In Codex, Claude Code, Gemini CLI, or Antigravity, invoke `/pdd` with the issue number or description. The skill inspects the repo with `pdd status --json`, selects `feature`, `bug`, `small-change`, or `product` mode, writes prompts/Stories/tests before code, checks them with `pdd lint` and `pdd test`, waits for your approval (`pdd approve PROMPT`), builds the implementation, and proves the change with `pdd prove`:

```sh
pdd status --changed
pdd lint
pdd lint --diff origin/main
pdd prove --base origin/main
```

For bug fixes, prove that your regression test fails on the merge base with the defect text and passes on `HEAD`:

```sh
pdd prove --base origin/main --test "node --test test/regression.test.mjs" --expect "expected defect text"
```

### 6.2 Unattended background runs with Autopilot

To process opt-in GitHub issues autonomously on a 10-minute timer, configure Autopilot in your repository:

```sh
pdd autopilot doctor
pdd autopilot observe                  # or: pdd autopilot auto
pdd autopilot add 42
pdd autopilot start --label pdd:autopilot
pdd autopilot status
pdd autopilot logs 42 -f               # follow live worker progress (Ctrl-C detaches safely)
```

- Each issue runs in an isolated Git worktree and branch using a headless worker job.
- Full test suites run through the shared machine queue (`pdd autopilot suite --command "npm test"`).
- In `observe` mode, Autopilot opens the PR, runs CI, fresh review, and full tests, and posts "would merge" for a person to merge.
- In `auto` mode, Autopilot merges its own PR once CI, fresh review, and full tests pass (required GitHub branch protections and `strict_approvals` still apply).
- Run `pdd autopilot stop` to stop the timer while letting any active step finish.

<a id="7-check-prompts-on-the-pdd-runtime"></a>

## 7. Check prompts on the PDD interpreter

The PDD interpreter runs a prompt as a program: an AI model on the PDD server reads the `*.prompt.md` file and acts as the program. `pdd test` sends your prompts, Stories and tests there and checks each answer against its test. `pdd simulate` opens the PDD Simulator, where a person can use the prompt by hand.

Both commands sign in with your GitHub login (`gh auth status`). They send the selected Stories, their authored tests and the prompts and context those tests need. Every sent file must be Git-visible (tracked or new, not ignored). The selected payload must fit 10 MB and 10,000 files; safe in-repository links send their final Git-visible regular target bytes under the authored path. Secret names, outside or broken links, loops and non-regular targets are refused. Unrelated source files are not sent. pdd keeps runtime state in `~/.pdd/runtime`; the repo also holds the test cache in `.pdd/cache/test/` and CLI simulation files in `.pdd/try/`.

The upload follows each test's entry prompts and their `calls` targets, test `context` files, and local links in each prompt's `## Dependencies`. A dependency list item may instead begin with a backticked file path, such as ``- `data/menu.json`: required runtime context``. Local image links, including SVG mockups, go with their prompt. Ordinary navigation links outside Dependencies and remote URLs do not supply context. A missing declared file stops the upload and names its referrer.

A simulation includes a valid default `app-map.json` (else `app/app-map.json`), including screen, router, handler and after-operation prompts and stylesheets. Check and lint use no app map. To preview a simulation with a custom map, run `pdd test --files place-order --app-map app/custom-map.json` before `pdd simulate place-order --app-map app/custom-map.json`.

For extra files, add `pdd-source.json` at the repository root:

```json
{"include": ["docs/shared-policy.md", "data/menu.json"]}
```

`include` is the only key. Entries are exact repository-relative file paths, not folders or patterns, and Git must show them.

```sh
pdd lint                      # offline structural, SVG and project lint; 0 AI / 0 network
pdd lint --diff origin/main   # offline lint plus diff checks against origin/main
pdd lint --remote             # interpreter format and cross-prompt lint; 0 AI calls
pdd test --files              # exact upload manifest and byte sizes for all Stories; offline
pdd test --files place-order  # preview only this Story; offline
pdd test                      # check Stories, reusing unchanged passing results from the local cache
pdd test place-order          # check one story
pdd test --lf                 # check the last failures
pdd test --cache-clear        # clear cached results
pdd test --read               # read saved results; may continue original lint-held checks after lint passes
pdd simulate place-order      # open a Simulator link in your browser; it ends in 24 hours
pdd simulate --stop place-order
```

The AI-call budget is a ceiling; you are charged only for calls that run. Check defaults to 12 calls per step, with a minimum of 18 and maximum of 1000 per test. `pdd test STORY --max-calls N` overrides that ceiling. A new `pdd simulate STORY` requests 400 calls; use `pdd simulate STORY --max-calls 600` when starting a new simulation. Both `pdd test` and `pdd simulate` accept `--max-calls` from 1 through 1000, the interpreter maximum. Choose at least 3 times your worst-case estimate, including child calls and planned interactions (see [`skills/pdd/references/stories.md`](../skills/pdd/references/stories.md)).

`pdd test` and saved-batch `pdd test --read BATCH` wait until every Story ends in every shell. `--timeout MIN` (1 to 120 minutes) sets an explicit caller limit. While checks run, pdd prints one stderr line every 30 s, for example `Still running: 2 of 3 Stories done · 14 AI calls so far · 4 min`. If stopped, run the printed recovery read once to keep waiting. Never poll every minute.

After the table, `pdd test` prints one `Prompt tests` line for each Story that you can paste into a PR, for example `Prompt tests (place-order): ✓ 4 of 4 criteria · 11/11 checks · 2 AI calls`. With two or more Stories, the overall `Prompt tests:` line comes last.

A prompt whose interface is still `draft` can be checked, and its result is marked DRAFT. A DRAFT pass is not an approval.

| Exit | Result | What to do |
|---|---|---|
| 0 | passed | Nothing. |
| 1 | a check failed | Look at the failed check. Usually the prompt is wrong, and your agent fixes it. A person decides expected values. The agent may propose a change, and never makes it. |
| 4 | refused | A file rule or the AI service; nothing was judged. Read the reason under the line. |
| 5 | not run | Sign-in, a busy server, no AI room, a GitHub account that PDD Cloud has not approved, or an old pdd. Read the one line that pdd prints. |
| 3 | unknown or still running | Run `pdd test --read` later. Never send it again. |
| 2 | command error | Run `pdd test --help`. |

The optional Story scope uses one exact `pdd-boundary` fenced block with repository-relative prompt paths, one per line. See [Explain resource bindings](cli.md#explain-resource-bindings).

Your agent reads [`skills/pdd/references/stories.md`](../skills/pdd/references/stories.md) in the pdd package: the three files (prompt, Story, test), their rules and what to do with each result.

The interpreter address is set in one place in pdd. You do not need to set it.

Factories and method-bearing instances can bind through Runtime interface v2 handles and collections. Put injected I/O and callbacks behind ports, and use the declared SQL, blob and compute simulations. Preserve the public API and report native effects as unbound. See [Factories and simulated resources](runtime-boundaries.md#native-factories-and-json-operations).

### 7.1 Approve a prompt

In interactive work, a person approves a prompt. Explicit Autopilot auto setup and start can delegate ordinary approval gates through the supported commands. Strict approvals and required human reviews still need a person. An agent never edits `"status": "approved"` directly.

```sh
pdd approve prompts/place_order.prompt.md
```

pdd shows the prompt summary and the text that you approve: the changes since the last approved version in Git, or the whole text when there is none, at most 40 lines. Then it asks `Approve prompts/place_order.prompt.md? y/n`. When you answer `y`, pdd records your approval for the prompt's prose SHA-256 (keeping plain Markdown prompts unchanged on disk). Any other answer changes nothing.

- If the prompt has schema problems, pdd lists them and does not approve.
- If an approved prompt changes, ask the person to approve the updated prose again.

### 7.2 Simulate a Story

`pdd simulate STORY` automatically opens a shell for a command-line program, localhost with an example request for HTTP routes, the PDD Simulator page for screens, or its Form tab for typed operations. Omit STORY to open the whole project: all mapped screens, the unique main command-line program, or all HTTP routes. Use `--page` to choose the Simulator page. On the page, it makes a Simulator link and opens it in your browser. In the Simulator, you use the prompt by hand. The link ends after 24 hours, or with `pdd simulate --stop STORY`.

In your terminal, `pdd simulate` keeps waiting while the page is open:

- When you save a case in the Simulator, pdd adds it as a new step to the Story's test file.
- When you click **Approve** in the Simulator, pdd asks `Approve PROMPT? y/n` in this terminal. Only your `y` there approves the prompt. If the prompt changed after you clicked, pdd does not approve it.

Use `--no-open` to get the link without opening a browser. Use `--no-wait` to return at once. When an agent runs `pdd simulate`, it reads the saved cases once and returns. Anyone with a Simulator link can use it, so the link never goes into a file, a PR or an issue.

### 7.3 When a check does not run

| pdd prints | What to do |
|---|---|
| `No tests found. The test of Story user_stories/S.md is S.json in a test or tests folder.` | pdd also says why for each near miss: a Story with no test (with the path it expects), a `.json` file in a test folder that matches no Story, or a prompt that ends in `.prompt` instead of `.prompt.md`. Fix the files that it names. See [`skills/pdd/references/stories.md`](../skills/pdd/references/stories.md). |
| `Your GitHub account does not have PDD interpreter access yet. Sign up at https://promptdriven.ai/login with GitHub; you can use the interpreter when your account is approved.` | PDD Cloud has not approved your GitHub account. Sign up at [promptdriven.ai/login](https://promptdriven.ai/login) with the GitHub account that `gh` uses. After the approval, access starts within 1 minute. Exit code 5. |
| `Your GitHub login NAME is not on the PDD interpreter invite list yet. Ask the PDD team to add you.` | Ask the PDD team to add your GitHub login. Exit code 5. |
| `PDD Cloud could not confirm your access. Try again in a minute.` | PDD Cloud did not answer. Run the same command again in a minute. Exit code 5. |
| `Please update pdd: ...` | Your pdd is too old for the PDD interpreter. Run `pdd upgrade` (or `npm install -g @promptdriven/pdd && pdd setup`). Exit code 5. |

<a id="8-customize-project-lint-and-verification-rules"></a>

## 8. Customize project lint and verification rules

Configure repository-specific lint rules and real-path verification recipes in root `pdd.json`:

- `"lint"`: tune built-in rules (`"off" | "warn" | "error"`), disable rules, or add `"custom_rules"` enforced by `pdd lint`.
- `"verify": { "paths": [...] }`: declare glob-matched real-path verification recipes (CLI, API, browser, or database) that `pdd status` reports and `pdd prove` runs from merge-base trusted configuration.

See [`skills/pdd/references/verification.md`](../skills/pdd/references/verification.md) and [the CLI reference](cli.md).

## 9. Shell completion

`pdd completion bash` and `pdd completion zsh` print a completion script. They do not change your shell files. To turn it on, add one line to your shell startup file:

```sh
source <(pdd completion zsh)    # in ~/.zshrc, after compinit
source <(pdd completion bash)   # in ~/.bashrc
```

<a id="clean-up-after-a-run"></a>

## 10. Clean up worktrees and state

Autopilot ticks automatically remove unused Autopilot worktrees and prune old logs. To clean up any manual worktree or branch:

```sh
git worktree list
git worktree remove ../path/to/worktree
git branch -D pdd/branch-name
```

<a id="update-and-uninstall"></a>

## 11. Update and uninstall

Update the pdd command and its `.pdd-skill.json`-marked user skills in one step:

```sh
pdd upgrade           # latest release (npm first with GitHub fallback; Volta-safe)
pdd upgrade --main    # pinned main commit
```

Update skills installed with `npx skills`:

```sh
npx skills add promptdriven/pdd -g -a codex -a claude-code -y   # for all your projects
npx skills add promptdriven/pdd -a codex -a claude-code -y      # in a project that has its own copy
```

Start a new agent chat after updating so it loads the updated skill.

Uninstall the skill that `npx skills` installed:

```sh
npx skills remove pdd      # add -g for the global install
```

Uninstall the pdd command, the skill that `pdd setup` copied, and its state:

```sh
npm uninstall -g @promptdriven/pdd
rm -rf ~/.agents/skills/pdd
rm -rf ~/.claude/skills/pdd
rm -rf ~/.gemini/config/skills/pdd
# If you set CLAUDE_CONFIG_DIR, also remove "$CLAUDE_CONFIG_DIR/skills/pdd"
rm -rf ~/.local/state/pdd
rm -rf ~/.pdd
```

Look before you run `rm -rf`: if `npx skills -g` installed these folders, use `npx skills remove -g` instead.

If setup added MCP registration, remove only its `pdd` entry from `$CODEX_HOME/config.toml` (default `~/.codex/config.toml`), `$CLAUDE_CONFIG_DIR/.claude.json` (default `~/.claude.json`), `~/.gemini/settings.json`, and `~/.gemini/config/mcp_config.json`.

## 12. Known limits

- Read the test and `pdd prove` output before merging a PR.
- PDD is tested on macOS and Linux.
- Without `--agent`, pdd selects the first ready agent in order: Codex, Claude Code, Gemini CLI, then Antigravity CLI (`agy`). An explicit agent or configured launcher selects that choice.

## 13. Troubleshooting

| You see | What to do |
|---|---|
| `pdd --version` does not print `0.1.50` | Another `pdd` comes first. See [section 3](#3-if-you-have-the-old-python-pdd). |
| pdd says an agent is not installed or signed in | Install the agent and sign in, or use another agent with `--agent`. |
| A message about `git rev-parse --show-toplevel` | You are not in a Git clone. `cd` into your clone. |
| A message about `refs/remotes/origin/...` or a missing base | Run `git fetch origin`. |
| The agent uses an old PDD skill | Run `pdd setup` (or `npx skills add promptdriven/pdd -g -a codex -a claude-code -y` for unmarked installs), then start a new chat. `pdd --version` says when your skills are older than pdd. |
| `npx skills update -g` prints `No global skills tracked in lock file` | `npx skills add` did not install the skill (for example, `pdd setup` did). Run `npx skills add promptdriven/pdd -g -a codex -a claude-code -y` once. After that, `npx skills update -g` works too. |
| `npx skills add … -g` prints `Failed to install` for some agents | Those agents do not support global skills. Codex and Claude Code still get them. To install only for these two, add `-a codex -a claude-code`. |
| The agent does not know the `/pdd` skill | Run `pdd setup` (or `npx skills add promptdriven/pdd -g`), then start a new chat. |
| `pdd test` says `No tests found` | Read the reasons under that line, and fix the files that it names. See [section 7.3](#73-when-a-check-does-not-run). |
| `pdd test` says that your GitHub account does not have PDD interpreter access | Sign up at [promptdriven.ai/login](https://promptdriven.ai/login) with the GitHub account that `gh` uses, and wait for the approval. See [section 7.3](#73-when-a-check-does-not-run). |
| `pdd test` or `pdd simulate` says `Please update pdd` | Run `pdd upgrade` (or `npm install -g @promptdriven/pdd && pdd setup`). |
| `pdd test` says that your login is not on the invite list | Ask the PDD team to add your GitHub login. |
| `pdd approve is for a person at a terminal` | In strict mode (`"strict_approvals": true`), run the approval yourself in a normal terminal. Otherwise, your agent can record your actual chat approval with `--said -`. |
| `npm error code EEXIST` on `<prefix>/bin/pdd` | An unscoped `pdd` npm package owns `bin/pdd`. Run `npm uninstall -g pdd && npm install -g @promptdriven/pdd` (do not use `--force`). |
| `npm outdated -g` shows `pdd` 0.4.14 | That is the unrelated registry package. Ignore it. Do not run `npm update -g`. |

## 14. Report a problem

Follow [Report a problem](ISSUES.md). It is for you and for your agent. It tells how to check the version, search the open issues and write one clear issue. Fill the [issue form](https://github.com/promptdriven/pdd/issues/new?template=bug.yml), or ask your agent to file the issue with `gh`.

Do not paste tokens, passwords, Simulator links or private code.

## 15. Use your program for real with `pdd simulate`

Run `pdd simulate <story>` to open a shell with your program ready. Use `--cli` to print the PATH line instead, then type your program's commands in your
own terminal, or run the printed absolute path. For example: `tipjar split 100 --people 3 --tip 18 --round-up`.
Each command runs the prompt on the interpreter with your gh login; saved data stays in the same simulation.
`--help` also runs the prompt. `--shell` opens a shell with the PATH ready. Piped UTF-8 input is forwarded when
the prompt declares `stdin`. Program output and exit codes pass through; wrapper errors begin `pdd:`
and use reserved code 125. Calls can take a while because they run AI.

Run `pdd simulate --save-last` to append the last command and its observed answer to the original test file.
Review that recording before treating it as an expected answer. Stop the session with `pdd simulate --stop <story>`.

For HTTP, give the prompt entry an input schema title such as `HTTP GET /api/books`, then run
`pdd simulate <story> --serve 8080`. Call `curl 'http://127.0.0.1:8080/api/books?read=false'`. The prompt returns the
HTTP status, headers and body. Unknown routes return 404. The listener stays on loopback; Ctrl-C closes it.
When the Story has an app map, open `http://127.0.0.1:8080/` to use its real Screen. Click **Open the app**
if needed; opening and taps use the same simulation budget and saved data. See [`skills/pdd/references/ui-and-screens.md`](../skills/pdd/references/ui-and-screens.md) for details.

## 16. Ask your agent in the PDD Simulator

Run `pdd simulate STORY` in your own terminal and keep pdd running. Without terminal stdout, plain `pdd simulate STORY` reads saved cases once and returns without discovering or connecting a local agent. An explicit `--agent NAME` connects even in the background; `--no-wait` skips the connection. The Simulator's **Ask your agent** panel connects to your own installed Codex, Claude or Gemini through the interpreter. Ask what you can try, ask it to prepare the fields, or ask whether the last answer meets the Story. Suggested inputs are checked against the entry's schema. The agent fills directly on a supported page and runs only when it understands that you want the action to happen; otherwise you press **Run**. Actions use the simulation budget. Older pages keep manual **Fill fields** and **Run**.

```sh
pdd simulate my-story
pdd simulate my-story --agent claude
```

<a id="many-accounts"></a>
Many accounts? List your agents in `~/.config/pdd/agents.json`:

```json
{
  "agents": [
    { "name": "Claude (account-a)", "kind": "claude", "command": "claude-account-a" },
    { "name": "Codex (account-b)", "kind": "codex", "command": "codex", "env": { "CODEX_HOME": "~/.pdd-codex/account-b" } }
  ],
  "include_defaults": true
}
```

Use `pdd simulate my-story --agent "Codex (account-b)"`, or choose a name in the picker. Each launcher has its own state, and the choice is remembered for the project. Detected defaults appear after your entries; set `"include_defaults": false` to show only your list. Only your user file supplies custom launchers; repository `.pdd/agents.json` files are ignored. `kind` chooses the read-only Codex, Claude or Gemini adapter. `command` is a program name or path, launched without a shell; leading `~` is expanded in paths and env values. Env overrides apply only to that launcher. Commands and env stay on your computer; only names and states reach the picker. Invalid configuration stops with a plain error.

The same names also work with `pdd product start`:

```sh
pdd product start phone-1 --agent "Claude (account-a)"
```

`command` must be a file that can run, not a shell function or an alias, because pdd starts it without your shell startup files. A small script works. For example, `~/bin/claude-account-a` (run `chmod +x` on it):

```sh
#!/bin/sh
unset ANTHROPIC_API_KEY ANTHROPIC_AUTH_TOKEN
CLAUDE_CODE_OAUTH_TOKEN="$(cat ~/.secrets/claude-account-a.token)"
export CLAUDE_CODE_OAUTH_TOKEN
exec claude "$@"
```

The picker shows installation and sign-in state. You can switch agents; pdd remembers the choice for this project. A usage limit or sign-in error is shown in the chat without sending your message to another agent automatically. Codex and Claude use fresh read-only turns with your default model and login. Gemini Try accepts any installed version whose `--help` lists the required options. It checks `--help` for `--approval-mode`, `--admin-policy`, `--extensions`, `--allowed-mcp-server-names` and `--output-format` before applying its restricted configuration. If an option is missing, pdd prints `Gemini Try read-only mode requires <option>; update Gemini CLI.` When its sign-in cannot be checked cheaply, the picker says it will be checked on the first message.

If an agent cannot start, the chat shows its first error line with recognized secrets removed. Full sanitized diagnostics stay on your computer in `~/.pdd/runtime/agent-chat.log`; the chat shows that path when the log was saved.

Chat uses your agent account's allowance. The interpreter relays messages and invokes no model for chat. Context includes the Story, criteria, entry schemas, current fields/data and last answer; recognized credential fields and token patterns are removed. Keep secrets out of project text and chat. The agent can request a Simulator action when you ask it to run one; it cannot edit the project.

Closing pdd or pressing Ctrl-C disconnects chat and leaves the simulation open. `pdd simulate STORY --no-wait` opens an ordinary Simulator link without a chat bridge. Agent selection does not combine with `--no-wait`, `--cli`, `--serve`, `--stop` or `--save-last`. Shared Simulator links do not grant access to owner chat. If a browser cannot open automatically, pdd prints a separate private owner-chat link; do not share it. Reconnecting replaces the chat connection and clears its temporary history.
