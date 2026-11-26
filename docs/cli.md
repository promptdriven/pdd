# CLI reference

This page lists every command of pdd 0.1.53, as `pdd --help` and `pdd <command> --help` show it. The command tables below are generated from `PUBLIC_COMMAND_MANIFEST` (`src/command-catalog.mjs`) by `node scripts/generate-cli-docs.mjs` and verified by `test/docs-commands.test.mjs` (`node scripts/generate-cli-docs.mjs --check`).

You need the pdd command for local inspection (`pdd status`, `pdd files`, `pdd owner`, `pdd update`, `pdd lint`, `pdd prove`), remote checks and direct prompt execution (`pdd test`, `pdd lint --remote`, `pdd <PROMPT.md|STORY|.>`), and headless Autopilot issue runs (`pdd autopilot`). Install the single `/pdd` skill globally with `pdd setup` (or `npx skills add promptdriven/pdd -g`), and set up each repository once with `pdd init`. For sessions that your agent drives, use the Try tools in `pdd mcp`. Call the skill with `$pdd` in Codex or `/pdd` in Claude Code (or ask for it by name). See [Install](USAGE.md#2-install).

Typing `pdd check`, `pdd try`, `pdd simulate`, `pdd sim`, `pdd workflow`, or `pdd approve` runs nothing and prints what to use instead.

## Set up your machine and repo

<!-- BEGIN GENERATED: cli-commands:setup -->
| Command | What it does |
|---|---|
| `pdd setup [--yes] [--skills-dir PATH] [--upgrade]` | Install or refresh global PDD skills (~/.agents/skills, ~/.claude/skills, ~/.gemini/config/skills; plugin-aware for Claude Code; or custom PATH with --skills-dir), remove retired PDD skills, and offer Prompt Interpreter MCP registration for detected Codex, Claude Code, Gemini and Antigravity configs. Never edits repositories or Autopilot settings. Pass --yes to register previewed MCP tools without prompting, or --upgrade to sync skills and refresh only already-registered stale MCP entries silently. |
| `pdd init` | Add or refresh the 4-line PDD block in this repository's CLAUDE.md (else AGENTS.md) and report detected language and test command; never edits root .gitignore. |
| `pdd status [PATH...] [--changed] [--json]` | Show a compact offline overview of prompts, Stories, tests, file ownership and the pdd.json Feature Map; --changed inspects branch-diff and working-tree changes. No network or AI calls. |
| `pdd files [--json]` | List prompts, Stories, tests and refusal reasons; no network calls. |
| `pdd owner PATH... [--json]` | Show which prompt owns each file, from pdd-bindings.json and top-of-file Prompt / Generated from headers; reads local files only. |
| `pdd update [FILE...] [--from RANGE] [--branch] [--all] [--check] [--json]` | Inspect changed code files against their owning prompts and changed symbols using local Git and working files only (read-only, zero AI calls). Use --branch to diff from merge-base(defaultBranch, HEAD), --all for all mapped files, and --check to fail on drift. |
| `pdd upgrade [--main]` | Upgrade a user-owned global npm @promptdriven/pdd installation from npm (with GitHub tag fallback, or pinned main commit with --main) and refresh installed user PDD skills. |
| `pdd doctor [--json]` | Run read-only health checks for Node, competing pdd installs, login-shell PATH splits, agent skills, MCP configs, and gh sign-in. Exits 0 when healthy, 1 when actionable issues are found. |
<!-- END GENERATED: cli-commands:setup -->

`pdd setup` copies the bundled `/pdd` skill to `~/.agents/skills` (Codex and Gemini CLI), `~/.claude/skills` (or `$CLAUDE_CONFIG_DIR/skills` when it is an absolute path, cleaning retired PDD skills and symlinks and skipping duplicate `/pdd` copies when Claude Code already has the PDD plugin installed in `installed_plugins.json`), and `~/.gemini/config/skills` when Antigravity (`agy` on PATH, `~/.gemini/antigravity-cli`, `~/.gemini/config/mcp_config.json`, or existing PDD skills in `~/.gemini/config/skills`) is present. Pass `--skills-dir PATH` to target a custom skill folder instead of the default roots. Setup also updates existing PDD-managed folders in `~/.codex/skills` and `$CODEX_HOME/skills`. After an update of the pdd command, `pdd setup`, `pdd upgrade`, and the once-per-version automatic sync on normal `pdd` commands recognize real PDD-managed folders carrying `.pdd-skill.json` or `pdd-skills:` frontmatter, replacing older or same-version differing copies with a `.pdd-skill.json`-marked copy, adding missing bundled skills, removing PDD-managed retired skills (`pdd-autopilot`, `pdd-check`, `pdd-merge`, `pdd-setup`, `pdd-prompting`, `pdd-small-change`, `pdd-bug`, `pdd-feature`, `pdd-product`, `pdd-graph`), and unlinking retired symlinks that are dangling or point into another user agent skill directory. Do not hand-edit PDD-managed folders because updates replace managed copies; folders lacking both `.pdd-skill.json` and `pdd-skills:` frontmatter, symlinks into developer git checkouts, and unrelated custom skills are never modified. When `pdd --version` or `pdd setup` reports older or retired skills, it names each affected skill and advises `pdd setup` for user folders (or `npx skills add` for project folders). Discovery commands (`pdd files`, `pdd status`, `pdd owner`, default `pdd lint`) make no network calls and write nothing to the repository (`pdd lint --local` may still save local assessment state under `$PDD_STATE_DIR` when assessing scenario JSONs).

Setup shows a compact per-agent summary of planned PDD MCP configuration changes for the Codex, Claude Code, Gemini CLI and Antigravity (`agy`) agents it finds, then asks once (`[y/N/d]`, where `d` prints the exact raw TOML/JSON preview before confirming). Passing `--yes` applies the planned MCP configuration without asking; passing `--upgrade` refreshes only already-registered stale PDD entries silently and skips unregistered agents; without `--yes` in a non-interactive terminal, MCP registration is skipped safely. Existing empty or whitespace-only JSON agent config files are initialized cleanly as `{}` while preserving file permissions. Registrations pin this running pdd executable, so another installation earlier on PATH cannot receive its tools, and stale PDD entries are updated in place while preserving custom keys, unrelated servers and formatting. Codex uses `$CODEX_HOME/config.toml` (default `~/.codex/config.toml`) and `mcp_servers.pdd` with `default_tools_approval_mode = "approve"`. Claude Code uses `mcpServers.pdd` in its configuration; Gemini CLI uses `mcpServers.pdd` in `~/.gemini/settings.json` with server trust (detected via `settings.json` or `gemini` on PATH); Antigravity uses `mcpServers.pdd` in `~/.gemini/config/mcp_config.json` (detected via `mcp_config.json`, `~/.gemini/antigravity-cli`, or `agy` on PATH). Each entry runs `pdd mcp`. A symlinked agent config is skipped with a warning and exit 0, and a failure in one agent does not block registering healthy agents.

Setup also reports PATH conflicts, competing `pdd` installs across version managers (Volta, nvm, fnm, mise, asdf, pnpm, Homebrew, global npm, Python/conda/uv/pipx), and login-subshell (`zsh -lc` / `bash -lc`) PATH splits with single-command cleanup suggestions. When PATH and installs are clean, setup stays quiet. `--version` preserves its version-only stdout and fast local PATH check without spawning login shells; PATH diagnostics go to stderr.

`pdd doctor [--json]` runs a read-only host health check without creating or modifying any files in `$HOME` or the repository. It checks five areas:

1. **CLI & Node runtime:** running `pdd` version, install kind, binary path, and Node.js version (`>=22.16.0`).
2. **Installs & shell PATH:** all `pdd` executables across `PATH`, Volta, nvm, fnm, mise, asdf, pnpm, global npm, Homebrew, and Python/conda/uv/pipx (deduplicated by realpath, Volta shims, and pnpm wrappers), plus login-subshell (`zsh -lc` and `bash -lc`) parity with exact single-command cleanup hints.
3. **Agent skills:** checks `~/.agents/skills`, `~/.claude/skills` (or `$CLAUDE_CONFIG_DIR/skills`, respecting Claude Code plugin installs), `~/.gemini/config/skills`, and `~/.codex/skills` (plus `$CODEX_HOME/skills`) for current, missing, stale, or retired PDD skills.
4. **Agent MCP configs:** read-only inspection of detected Codex, Claude Code, Gemini CLI, and Antigravity MCP config files for missing entries, stale paths pointing to another `pdd` install, 0-byte or malformed JSON/TOML, and symlinks.
5. **GitHub CLI (`gh`):** bounded read-only sign-in check for hosted interpreter runs (advisory only so offline/local setups stay healthy).

`pdd doctor` exits `0` when all required checks pass (optional advisories such as `gh` sign-in or intentional symlinked MCP configs stay exit `0`), exits `1` when actionable issues are detected (incompatible Node, competing or shadowed installs, login-shell PATH splits, missing/stale/retired skills, or missing/stale/broken MCP configs), and exits `2` on invalid arguments. Pass `--json` for structured `pdd.doctor.v1` JSON output on stdout.

`pdd init` sets up the current repository without touching user-global skills, MCP config, or root `.gitignore` (`.pdd/.gitignore` is written automatically whenever `.pdd/` is created). It preserves existing line endings (LF or CRLF), follows in-repo symlinks such as `CLAUDE.md -> AGENTS.md` cleanly while refusing out-of-repo symlinks, and detects project stack and test commands so the agent can start immediately.

## Repository Autopilot settings

Manage Autopilot repository mode and trust directly with `pdd autopilot`:

<!-- BEGIN GENERATED: cli-commands:autopilot-settings -->
| Command | What it does |
|---|---|
| `pdd autopilot observe` | Set the repository Autopilot mode to observe. |
| `pdd autopilot auto` | Set the repository Autopilot mode to auto. |
| `pdd autopilot off` | Set the repository Autopilot mode to off. |
| `pdd autopilot trust NAME...` | Add explicitly trusted GitHub names. |
| `pdd autopilot untrust NAME` | Remove an explicitly trusted GitHub name. |
<!-- END GENERATED: cli-commands:autopilot-settings -->

Settings live in the repository's `pdd.json`, for example `{"autopilot":{"mode":"off","trust":[]}}`. Other settings are preserved. Autopilot on this machine reads `pdd.json` of this checkout. Its job worktrees, other machines and other people read `pdd.json` of the default branch on GitHub. So `pdd autopilot off`, `observe`, `auto`, `trust` and `untrust` also update `pdd.json` on the default branch, through the GitHub API with your `gh` sign-in. Each command makes only its own change on GitHub: a mode command sets `autopilot.mode`, `trust` adds its names to `autopilot.trust`, and `untrust` removes its name. All other keys and fields keep the GitHub values, also when your checkout is behind. The commit message says what changed, and the commit changes only those bytes of `pdd.json`: the indent and the key order of the file stay. They do not touch your current branch or your uncommitted work. More lines tell the result:

- GitHub is already up to date.
- The commit URL, then `pdd.json on GitHub is updated. To update your local copy, run git restore pdd.json, then git pull.` `git restore pdd.json` drops your local change of `pdd.json`, which GitHub now has. Run `git pull` on the default branch.
- When the default branch accepts changes only through a PR: the URL of a PR from a `pdd/autopilot-settings-…` branch, which you must merge before the GitHub copy has the new setting. While that PR is open, the next command adds its change to the same PR. When the new setting is the same as on the default branch, pdd closes the PR with a short comment.
- When the copy on GitHub then has other settings than your checkout, one more line shows both.

When another change of `pdd.json` on GitHub comes between pdd's read and its write, pdd reads the file again and tries once more. When GitHub cannot be reached or `gh` is not signed in, the local setting stays, the exit code is 0, and the line tells you to run the same command again. `pdd autopilot start` and `pdd autopilot status` print a warning when the copy on GitHub has another mode or trust list, with the commands that change it, or when a settings PR is still open, with its URL. The warning says that Autopilot on this machine uses this checkout's settings (and this machine's `--mode` and `--label`, when set), and that other machines and people read the GitHub copy. Invalid saved modes count as `off` with a notice; a mode command replaces them. Names match ignoring case. The repository owner, people with write access (including access through an organization team), and explicitly added names are trusted independently. An incomplete lookup never establishes trust for an unknown person.

These commands store settings and determine trust. Selecting a mode starts no run and makes no interpreter call.

## Inspect authored files

`pdd files [--json]` lists prompts, Stories, tests and refusal
reasons. It reads working files only. It does not sign in, call the interpreter,
or edit files. It works from any folder in a Git repository.

The reader expands `$contract` references and preserves numeric JSON tokens for
lint and test.

The JSON result has `schema_version: "pdd.files.v1"` and arrays `prompts`,
`stories`, `tests`, `orphans`, `refusals` and `warnings`. Paths are relative to the
repository root. Prompt rows include `has_interface`, resolved `references`,
paired `stories` and `tests`, and `refusals`. `has_interface` is null when a
source/reference failure prevents reading the interface. Story rows list their tests. Test
rows list every conflict member in `files`, their name-matched `stories`, reached
`prompts` and preflight `refusals`. Each refusal gives `path`, `code`, `section`
and `message`, plus a fix `hint` when available. No interface kind is inferred.

The list uses the same workspace limits, fixture exclusions and Story/test name
rule as an all-Story check. Missing tests and orphan JSON files are visible.
Inspection returns exit 0 when it can produce the list, including when files
have refusals. Exit 0 is not a lint or test pass. Root/configuration failures
return an error. `pdd test --files` remains the exact upload-file preview for a
selected check.

## Find the prompt that owns a file

`pdd owner PATH... [--json]` shows which prompt owns each file. It reads local
working files only. It does not sign in, call the interpreter or change a file.
PATH is relative to the current folder and must be inside the repository. The
file does not need to exist: a prompt is written before its code.

pdd reads two explicit ownership records, in this order:

| Source | Record | Certain |
|---|---|---|
| `binding` | An entry of the root `pdd-bindings.json` with `module` PATH and a `prompt` | yes |
| `header` | A `Prompt: PROMPT` or `Generated from PROMPT` comment line (`//`, `#`, `--`, `/* ... */`, `<!-- ... -->`, MDX `{/* ... */}`, or YAML frontmatter `prompt:`) in the first 4 KiB of the file ([header form](../skills/pdd/references/prompting.md#2-100-truth-rule-top-of-file-headers-and-hybrid-brownfield-prs)) | yes |

Prose mentions and filename stem matches never claim ownership: when no binding or header exists, pdd reports `owner: null`, `owners: []`, `source: null`, `certain: true`, and prints an advisory `note` suggesting an explicit `// Prompt: ...` header or `pdd-bindings.json` entry when a prompt mentions the path. The answer is `certain: false` when a binding or header names a prompt that does not exist, when `pdd-bindings.json` cannot be read and no owner is found, or when the file cannot be read and no binding names a prompt.

```text
src/runner.mjs: prompts/cli/runner.prompt.md (header)
src/queue.mjs: no owner
  hint: prompts/cli/queue.prompt.md mentions this path; add `// Prompt: prompts/cli/queue.prompt.md` or a pdd-bindings.json entry to claim ownership
src/rules.mjs: prompts/cli/rules.prompt.md (header)
  prompts/cli/rules.prompt.md header hash is stale (OLD); current is NEW
docs/guide.md: no owner
```

With `--json`, pdd prints `{"schema_version":"pdd.owner.v1","files":[...]}`. Each
row has `path`, `owner` (the first owner or null), `owners` (every owner: binding
first, then headers in line order), `source`
(`binding`, `header` or null), `certain`, `note` (empty when there is
nothing to add) and `headers`.

`headers` has one row for each provenance header of the file: `prompt`,
`sha256` (the header's hash or null), `expected` (the prompt's header hash, or
null when the prompt is not available), `state` and `legacy`. The header hash
is the SHA-256 of the prompt's behavior text: for a plain prompt, the prompt
text itself; when an embedded Runtime interface JSON block is present, the prompt
with `status` and `prose_sha256` taken out and that JSON written without white
space.

| `state` | Meaning |
|---|---|
| `current` | The hash is the prompt's header hash. |
| `current` with `legacy: true` | The hash is the SHA-256 of the whole prompt file. pdd accepts this form for compatibility and marks it `legacy: true`. Write the expected hash for a canonical header. |
| `stale` | The prompt changed after the header was written. Check that the file follows the prompt, then write the expected hash. |
| `none` | Canonical path-only header without a hash. |
| `unknown` | The named prompt is not available. |

The text form adds one line only when a header carries a `stale` or whole-file
`legacy` hash, showing the expected hash; canonical path-only headers (`none`)
add no extra line. `pdd owner` does not rewrite headers. The command returns 0 when it can answer, also for an uncertain
or missing owner. When a prompt claims ownership of a test file (`test/**`,
`tests/**`, `*.test.*`, `*_test.*` or `test_*.*`), `pdd owner` writes a
non-blocking warning on `stderr` and keeps exit code 0 and `stdout` unchanged.
It returns 2 outside a Git repository or for a PATH outside it.
Code replay and the `pdd test` check plan use the binding and header records
only.

## Inspect changed code files against owning prompts

`pdd update [FILE...] [--from RANGE] [--branch] [--all] [--check] [--json]`
inspects changed code files against their owning `.prompt.md` contracts using
local Git metadata and working-tree files only, with zero AI subprocesses, zero
network or interpreter calls, and zero file writes.

Choose one scope:

- Pass explicit repository-relative `FILE...` paths to scope strictly to those
  files.
- Pass `--from RANGE` (`<base>..<head>` or `<base>`, meaning `<base>..HEAD`) to
  scope strictly to files touched in that Git diff range.
- Pass `--branch` to diff from `merge-base(defaultBranch, HEAD)` against the
  working tree.
- Pass `--all` to inspect all prompt-mapped files in the repository.
- Omit all scope flags to inspect staged, unstaged, and untracked non-ignored
  changes in the current working tree (automatically widening to `--branch` on
  clean committed feature branches, or to `--all` during `--check` whenever no
  owned modules or prompts are in scope).

`pdd update` is strictly read-only and writes zero sidecar files or prompt
edits. It maps each touched file through `pdd owner` (`pdd-bindings.json` and
`Prompt:` / `Generated from` headers), groups owned modules by owning
`.prompt.md` with `+added/-removed` diff stats and changed exported/top-level
symbols, and lists genuine unowned product source files separately (excluding
tests, docs, user stories, prompts, dotfiles/dot-directories, configs,
manifests, lockfiles, and configured workspace ignores) without fabricating
ownership.

- Default: print each affected prompt's status (`current`, `reconciled`,
  `changed`, `prompt-stale`, or `deleted`), diff stats, changed symbols, and
  advisory reminders for code-only edits without writing files; exits 0. Use
  `pdd status --changed` for the same overview alongside the Feature Map.
- `--check`: read-only structural check that exits 1 only on broken ownership
  links (a missing or unreadable owning prompt, invalid prompt path, misplaced
  test prompt, dangling deleted binding, or a legacy `(sha256: ...)` header
  whose hash disagrees with its prompt). Path-only `Prompt:` headers,
  `pdd-bindings.json` bindings, co-changed code and prompt pairs (`reconciled`),
  and code-only edits (`changed`, printed with an advisory reminder to verify
  the owning prompt) exit 0.
- `--json`: emit machine-readable `pdd.update-sync.v1` JSON (`scope`,
  `prompts`, `modules`, `unowned`, `drifted`, `reminders`, `updated`, `ok`).

Path traversal (`..`), leading-`-` options/ranges, symlinks, secret-looking
paths (`.env`, credentials), malformed `pdd-bindings.json`, and binary owned or
explicit files exit 2 without writing any files.

## Autopilot on this machine

`pdd autopilot doctor` checks the pdd selected by PATH, Node 22.20 or newer,
Git, gh sign-in, write access, merge methods and effective branch rules, the Git
name and email, agent sign-in and read-only usage, setup instructions and skills,
mode and trust, the `pdd.json` on GitHub, draft prompts, authenticated interpreter
capacity access, and the platform's user scheduler. Linux lingering and macOS
sleep are advisory. Autopilot jobs run headless.
Codex usage uses a read-only account request. Claude usage remains unproved;
run `claude` and `/usage` to inspect it. No agent prompt is sent.
Unreadable branch rules are advisory; repository reviews and checks still apply.
A PASS line shows the check and its result only. A WARN or FAIL line also shows a
repair or inspection command after `fix:`. PATH repairs name this installation,
including source checkouts. A required failure refuses start with the same
report before state files, locks, timers or claims change.
Draft and unreadable prompt paths are warnings. Doctor never approves them.
A successful interpreter access read sends no source and proves no prompt behavior.
See [the first-start path](../README.md#autopilot-on-your-own-repository).

Autopilot jobs make commits, so Git needs `user.name` and `user.email`. Doctor
reads both in the repository. `GIT_AUTHOR_NAME` with `GIT_COMMITTER_NAME`, and
`GIT_AUTHOR_EMAIL` with `GIT_COMMITTER_EMAIL` (or `EMAIL`), also count. A missing
value is a warning. Its fix sets the value with `git config --global`.

Autopilot jobs and other machines read `pdd.json` of the default branch on
GitHub, not the copy in this checkout. Doctor reads that file and compares the
mode and the trust names; case and order do not count. When GitHub has no
`pdd.json`, the warning gives the commit and push that adds it, or
`pdd autopilot MODE`. When the settings differ, the warning shows both and gives
the `pdd autopilot` commands that publish the settings of this checkout. Doctor
itself writes nothing to GitHub.

Doctor uses the saved agent profile on restart.
A selected agent's HOME, CODEX_HOME, CLAUDE_CONFIG_DIR and other environment
settings apply to its checks. A repair command sets only the environment names
whose values differ from your shell, so most repair commands are plain. A
secret value is never printed.
A malformed agents.json report names the file to edit. An invalid
PDD_RUNTIME_URL report gives the HTTPS-origin or unset repair.
Interpreter health and agent usage limits are warnings with fix commands. They
never refuse start at preflight.
Interpreter readiness uses the runtime client's health check, including a JSON
404 from an interpreter without the optional capacity endpoint.

Run Autopilot commands inside the repo folder. Each repo has its own Autopilot on
each machine. Autopilot runs the [core engine](#core-engine). Its tick
makes no AI call. Each issue gets one headless Codex, Claude, Gemini, or Antigravity job with a log file.

<!-- BEGIN GENERATED: cli-commands:autopilot -->
| Command | What it does |
|---|---|
| `pdd autopilot doctor` | Read-only first-start checks and fix commands; no AI call or GitHub write. |
| `pdd autopilot start [--runs N] [--checks N] [--label NAME] [--issues N,M] [--issue N] [--mode auto\|observe\|off] [--report file\|draft\|off] [--decisions ask\|decide] [--intake off\|shadow\|active] [--share PERCENT] [--agent codex\|claude\|gemini\|agy] [--auto-update release\|main\|off]` | Start this repo with headless agent jobs (the core engine): check now and every 10 minutes, with no AI call on empty ticks. Autopilot works on issues with an opt-in label (--label NAME or autopilot.label in pdd.json) or on vetted ready cards when --intake active is enabled; without --intake active, a start with no label starts nothing. --issues N,M or --issue N limits this machine to those issue numbers (pass off, all or clear to clear). --runs and --checks override machine-sized run and heavy-check limits; --label, --mode and --report save this machine's opt-in label, mode and report mode for this repo, over pdd.json (--mode observe runs every check but never merges; --report draft, the default, keeps problem reports on this machine); --decisions saves this machine's decision mode (ask asks a person only for a big decision; decide, the default, never asks); --intake saves this machine's intake mode (shadow writes local intake cards that never change what starts; active selects ready cards, refines improve cards via read-only repo inspection and groups related small work; off is the default). --share saves the percent of this machine's CPU and memory that Autopilot may use (1-100, default 50; it sets the automatic slots, the room check and the timer's memory limit). --agent saves or replaces this machine's agent and sign-in profile. --auto-update saves this machine's between-tick self-update mode for a user-owned global pdd install and its skills when no job is publishing or merging (release is the default; main tracks promptdriven/pdd main; off disables self-update). |
| `pdd autopilot suite --command COMMAND [--timeout MIN]` | Run a full test suite through the shared machine queue without workflow dependencies (machine-sized check slots, 30-minute default timeout; --timeout 0 runs with no time limit). |
| `pdd autopilot status [--all] [--json]` | Show this machine's repo, folder, agent and next tick; --all lists every repository with Autopilot on this machine, from any folder. |
| `pdd autopilot logs [ISSUE] [--follow\|-f] [--lines N] [--json]` | List current headless Autopilot workers with stage, owned process state, suite queue position, blockers and saved log or evidence paths, or inspect and follow one issue worker live (--follow / -f detaches cleanly on Ctrl-C without stopping the worker or changing observe mode). Read-only; no GitHub write or approval effect. |
| `pdd autopilot logs --issue N [--follow\|-f] [--lines N] [--json]` | Select one worker explicitly with --issue N (number, #N, owner/repo#N or issue URL) to inspect saved progress or stream live updates. |
| `pdd autopilot stop` | Stop this machine's timer; let the current agent step finish. |
| `pdd autopilot add N...` | Mark named old issues with pdd:autopilot so Autopilot may take them. |
| `pdd autopilot release ISSUE` | Release this machine's claim and remove pdd:working and pdd:stuck; keep the run folder, branch and PRs. |
| `pdd autopilot intake [--json]` | Print this machine's local intake cards for this repo (shadow mode), the would-pick list and today's changes; no AI call or GitHub write. |
| `pdd autopilot graph [--open] [--issue N] [--repo OWNER/REPO]` | Read native issue dependencies or open the local graph viewer (alias: pdd graph). |
| `pdd autopilot report` | List the local Autopilot report drafts of this machine; no GitHub call. |
| `pdd autopilot report send FINGERPRINT` | File one local report draft to promptdriven/pdd, or count it on the matching open report. |
| `pdd autopilot regressions [--json] [--file PATH]` | Read core merge history and GitHub regression evidence; optionally save a local report, without GitHub writes or reverts. |
| `pdd autopilot investigate [--date YYYY-MM-DD] [--json] [--write-issues] [--max-issues N]` | Run the deterministic 4-bucket Autopilot incident investigator against local history, post-merge regressions, flakes, and report drafts (read-only by default; pass --write-issues to auto-file deduplicated strong-evidence GitHub issues up to --max-issues N). |
| `pdd autopilot alerts set [--destination autopilot\|infrastructure]` | Read a Discord or Slack incoming webhook URL from stdin and save it for this machine outside every repository, readable only by you; the URL is never printed. Post changed causes, decisions and recoveries; an unchanged stuck review sends nothing. Send one digest of open work per repository and machine at most every 6 hours. Use --destination infrastructure to separate machine incidents. |
| `pdd autopilot alerts set --discord-channel ID [--token-command CMD] [--destination autopilot\|infrastructure]` | Use a Discord bot instead: read its token from stdin and save it readable only by you, or save CMD and run it at each send so the token is never written to disk. The token and the command output are never printed. |
| `pdd autopilot alerts test [--destination autopilot\|infrastructure]` | Send one test message and confirm the posted message; for a bot, first show the bot name and channel name. |
| `pdd autopilot alerts clear [--destination autopilot\|infrastructure]` | Remove the alert destination from this machine. |
| `pdd autopilot alert --issue N --kind usage-limit\|resource\|interpreter\|interpreter-access\|access\|decision\|stuck\|test-suite\|long-running\|recovered --input - [--update]` | Record one alert for a real human need or incident and send it to this machine's destination. Reads {"cause","tried","need"} JSON from stdin. usage-limit, resource, interpreter and interpreter-access are one alert per repository and machine for all blocked issues; access, decision, stuck, test-suite and long-running are one alert per issue. A repeat sends nothing unless the last send failed; --update sends a changed cause, decision or issue list, never attempt notes alone; one digest of open work per repository and machine is sent at most every 6 hours; recovered sends one recovery and closes the matching alerts. |
| `pdd autopilot check-base RUN PR` | Check the saved automatic base, PR target, current default branch and newest release before a merge or after it. This command reads only. |
<!-- END GENERATED: cli-commands:autopilot -->

Outside a Git repository, `start`, `stop`, `status`, `logs`, `add`, `off`, `observe`,
`auto`, `trust` and `untrust` stop with exit code 1 and say: `This folder is not a
Git repository. cd into the repo you want Autopilot to work on, then run the
command again.` `status --all` works from any folder.

Autopilot works only on the issues that you mark with an opt-in label. Set the
label with `--label NAME`, or with `autopilot.label` in `pdd.json`. A start with no
label starts nothing and says: `Autopilot did not start: it works only on the
issues that you mark with an opt-in label. Run pdd autopilot start --label
pdd:autopilot, then mark issues with pdd autopilot add N (or add the label on
GitHub). Nothing was started or claimed.` `add` always uses `pdd:autopilot`; for
another label, add it on GitHub. When a tick has no label, it claims no issue (`intake held: no opt-in
label; …`), and status says `No opt-in label: Autopilot takes no issue.`

A start also stops when the repository mode is `off`, or when
`autopilot.quietMinutes` is below 20 (2 times the 10-minute timer). `--mode off`
saves mode `off` for this machine and stops the timer. To turn it on again, run
`pdd autopilot start --mode auto` or `--mode observe`. A successful start prints
one line, for example `Autopilot started for OWNER/NAME in /path/to/checkout. Base
main. Mode auto · issues with pdd:autopilot · agent ID · pdd VERSION · next tick:
TIME. See: pdd autopilot status.`

The first start of a repo on this machine selects the agent. It tries the agent of
the session that runs the command first: Claude Code when you run it from Claude
Code, Codex when you run it from Codex. Then it tries Codex, Claude Code, agy and
Gemini, in that order, and takes the first one that is signed in. This check makes
no model call. Later starts without an account flag keep that saved agent, also
after `pdd autopilot stop`. To switch the saved account or agent, use
[Cloud accounts](#cloud-accounts) (`pdd accounts use LABEL`) or pass
`--agent codex|claude|gemini|agy` or a different agent config folder
(`CODEX_HOME`, `CLAUDE_CONFIG_DIR`, `GEMINI_CLI_HOME` or `ANTIGRAVITY_APP_DATA_DIR`)
to `pdd autopilot start`. The core runs Codex, Claude, Gemini and agy headless jobs.
From a Claude Code session, run `env -u CLAUDECODE pdd autopilot start` or pass
`--agent codex` to select Codex.

Linux uses a systemd user timer; macOS uses a LaunchAgent. No process runs between
ticks. On Linux, start warns when user-session lingering is off or unavailable:
`loginctl enable-linger` keeps the timer after logout. A tick never changes its own
timer; only start and stop change it. When the installed timer has another
interval, status says `(run pdd autopilot start to use 10 minutes)`.

Each tick runs the [core tick](#core-engine). It reads the settings from this
checkout's `pdd.json`, and this machine's label, mode and report mode win over
them. Empty ticks make no AI call. The issue list uses ETags. When the open issue
list has more than one page, the tick reads it in full every 6 hours. Between, it
reads only the issues that changed since then (`since=`).

Autopilot uses `autopilot.base` in `pdd.json` when it is set; else it uses the
repository default branch. Start and status show the selection. Each start reads
the default branch from GitHub again. Repository documents do not select the
base.

`pdd autopilot status` reads local files and the timer, with no AI call.
It shows `Autopilot enabled; timer active, every 10 minutes; next tick: TIME`. Then
come the core lines: mode, repository, folder, base and agent; the busy slots, the
no-progress limit, repairs, the report mode and the opt-in label, each with its
source (`this machine` or `pdd.json`); the pause; one line for each job; the last
results and the count of local report drafts. Then come the move line, when there
is one, and the last tick. After start and status, one warning follows when
`pdd.json` on GitHub has other Autopilot settings than this checkout (see
[Repository Autopilot settings](#repository-autopilot-settings)). This warning is
the only GitHub read of status.

`pdd autopilot status --all` prints one line for each saved state on this machine:
repository, folder, base, mode, enabled or disabled, and the timer. The mode is the
machine mode with `(this machine)`, else the mode of that folder's `pdd.json`. A
folder that is gone shows `mode unknown (folder missing)`. A folder that is not a
Git repository shows `mode unknown (not a Git repository)`. A timer that cannot be
read shows `timer unknown`, and a broken state file shows `FILE: saved state
unreadable`. One bad line changes no other line. Without saved state it prints
`No Autopilot on this machine.` The local cost lines come last. It makes no GitHub
call.

`pdd autopilot logs` inspects headless Autopilot workers from local state files
without knowing internal state folders or touching running jobs. With no issue
argument, it prints the effective mode (`observe`, `auto` or `off`), active
workers sorted by issue number (stage, owned process state, suite queue position,
blockers, last activity, and saved log and evidence paths), recent finished
workers, and the follow command. With `ISSUE` or `--issue N`, it prints the
worker header and the last `--lines N` (default 40, maximum 5000) human-readable
progress lines formatted from Codex, Claude, Gemini/agy or test-suite logs, with
secrets redacted. It distinguishes waiting in the shared test-suite queue from a
running full suite, a repair pass, and a stale suite receipt. Add `--follow` or
`-f` to stream live worker and test-suite progress and stage changes; pressing
Ctrl-C detaches the viewer without stopping the worker or changing `observe`
mode. Add `--json` for structured snapshot output (`pdd.autopilot-logs.v1`).

## Machine and account health

Before the tick claims an issue for a Codex agent, it reads the usage of the saved
Codex profile. The read starts a short app-server connection and uses only
`initialize`, `initialized` and `account/rateLimits/read`. It makes no model call.
It does not spend, request credits, consume a usage reset, change sign-in or log
out an account. A primary window at 100%, a weekly window at 97% (protecting Pro
and credit-enabled accounts before paid extra credits burn), or a reached rate or
spend-control limit holds intake: with one account, the tick claims no issue and
says `intake held: the agent is not ready (sign-in or usage limit); no issue was
claimed`. Jobs that run go on. Unknown usage does not hold a standard single-account
intake.

When [Cloud accounts](#cloud-accounts) are enrolled or accepted on this machine,
`pdd` and `pdd autopilot` lease accounts automatically per step with zero switches
while both the 5-hour and weekly windows stay below 100%. When a login reaches 100%
on its 5-hour or weekly window (or returns `429 usage_limit_reached`), `pdd` reports
usage to PDD Cloud, selects the ready account with the soonest weekly reset, and
retries the step with zero issue strikes. When every account is cooling, Autopilot
pauses intake with `Waiting on AI quota until TIME`, sends one deduplicated alert,
and wakes automatically at `TIME`.

Malformed protocol frames stop the connection and report unknown usage. The read
waits at most one second for cleanup after it selects its result. It sends SIGTERM
first and SIGKILL after 500 milliseconds. A descendant that holds an inherited pipe
cannot block the read.

When jobs end with no result again and again, the core pauses new jobs on this
machine and sends one alert; see [Core engine](#core-engine).

## Cloud accounts

`pdd accounts` manages Codex and Claude logins in PDD Cloud from one local install
of `@openai/codex` (isolated in `$PDD_STATE_DIR/codex-home`, default `~/.local/state/pdd/codex-home`, leaving `~/.codex/auth.json` untouched) and `@anthropic-ai/claude-code`
(isolated in `$PDD_STATE_DIR/claude-home`, leaving `~/.claude/settings.json` and `~/.claude.json` untouched). PDD never spends or triggers usage-reset credits.

<!-- BEGIN GENERATED: cli-commands:accounts -->
| Command | What it does |
|---|---|
| `pdd accounts [--json]` | List enrolled and shared Cloud accounts, active selection, 5-hour and weekly usage windows, refresh status, and pending invites. |
| `pdd accounts list [--json]` | List enrolled and shared Cloud accounts, active selection, 5-hour and weekly usage windows, refresh status, and pending invites. |
| `pdd accounts status [--json]` | Show Cloud account enrollment, isolated Codex home, shell auto-switch status, active leases, and token refresh/expiry health. |
| `pdd accounts add [--provider codex\|claude] [--label NAME] [--loop] [--replace] [--device-auth] [--with USER\|ORG/TEAM[,...]]` | Sign in inside an isolated folder, upload the encrypted bundle to PDD Cloud, materialize in PDD's isolated Codex home or Claude home, and optionally enroll in a loop, replace an existing label, or share immediately. |
| `pdd accounts import [--provider codex\|claude] [--from PATH] [--label NAME] [--replace] [--with USER\|ORG/TEAM[,...]]` | Import a local or external Codex auth.json or Claude token into PDD Cloud, materialize in PDD's isolated Codex home or Claude home, and optionally replace an existing label or share immediately. |
| `pdd accounts use LABEL [--provider codex\|claude]` | Pin and materialize LABEL in PDD's isolated Codex home or Claude home. |
| `pdd accounts next [--provider codex\|claude]` | Skip the active login and switch to the next ready account sorted by soonest weekly reset. |
| `pdd accounts codex [ARGS...]` | Launch an interactive Codex session with live Cloud account quota monitoring and automatic mid-session resume rotation. |
| `pdd accounts sync [--provider codex\|claude] [--quiet] [--timeout-ms MS]` | Refresh the PDD-managed login from PDD Cloud when near expiry or at 100% usage; no-op when cached and healthy; fail-open when offline. |
| `pdd accounts auto on\|off\|status` | Manage the opt-in fail-open shell wrapper in ~/.zshrc, ~/.bashrc, and ~/.config/fish/config.fish for plain terminal codex and claude launches (off by default). |
| `pdd accounts pause LABEL [--provider codex\|claude]` | Pause automatic leasing for LABEL. |
| `pdd accounts unpause LABEL [--provider codex\|claude]` | Resume automatic leasing for LABEL. |
| `pdd accounts share LABEL [--provider codex\|claude] --with USER\|ORG/TEAM[,...]` | Share LABEL with GitHub users, organization teams, or @ORG targets without exposing raw credentials. |
| `pdd accounts share --all [--provider codex\|claude] --with USER\|ORG/TEAM[,...]` | Share all owned Cloud accounts (optionally filtered by provider) with GitHub users, organization teams, or @ORG targets. |
| `pdd accounts accept INVITE` | Accept a pending Cloud account share invite. |
| `pdd accounts unshare LABEL [--provider codex\|claude] --user USER` | Revoke shared access to LABEL for USER. |
| `pdd accounts unshare [LABEL] [--all] [--provider codex\|claude] [--user USER] [--with USER\|ORG/TEAM[,...]]` | Revoke shared access for users, organization teams, or @ORG targets across LABEL or all owned accounts. |
| `pdd accounts leave LABEL [--provider codex\|claude]` | Leave a shared Cloud account. |
| `pdd accounts remove LABEL [--provider codex\|claude]` | Delete LABEL from PDD Cloud and revoke active leases. |
| `pdd accounts log LABEL [--provider codex\|claude] [--json]` | Show the lease and sharing audit log for LABEL. |
<!-- END GENERATED: cli-commands:accounts -->

Standalone gateway launchers:

| Command | What it does |
|---|---|
| `pdd-codex [CODEX_ARGS...]` | Launch your installed `codex` binary through the PDD Cloud `/backend-api` gateway using your `~/.codex` chats, skills, plugins, and `config.toml` while sharing one temporary machine runtime lease and leaving personal `~/.codex/auth.json` untouched (`--account LABEL` pins a single account; `pdd-codex logout` revokes the runtime lease only) |
| `pdd-claude [CLAUDE_ARGS...]` | Launch your installed `claude` binary through the PDD Cloud `/v1/claude-gateway` gateway using a private `0600` temporary `--settings` file while keeping your `~/.claude` chats, plugins, skills, hooks, MCP servers, Claude in Chrome, and `~/.claude/settings.json` untouched (`--account LABEL` pins a single account; `pdd-claude logout` revokes the runtime lease only) |

- **Encrypted vault, zero-plaintext gateway grants, and constant gateway URLs.** PDD
  Cloud encrypts each account's refresh credential with envelope encryption bound
  to the account record. Codex and shared Claude `gateway_grant` leases
  (`delivery_mode: "gateway_grant"`) deliver only a short-lived revocable `pddg_…`
  gateway grant routed through PDD Cloud (`openai_base_url` and `chatgpt_base_url`
  pointed at the constant `<origin>/v1/codex-gateway` base URL on Codex's native
  `openai` provider with a `[model_providers.pdd_codex_gateway]` compatibility
  alias for `pddg_lse_…` grants, `ANTHROPIC_BASE_URL` for Claude), with zero real
  OpenAI or Anthropic OAuth tokens written to disk, seamless `codex resume` /
  `codex fork` session compatibility, and automatic `codex app-server` daemon
  refresh on credential switches. Legacy `direct_stripped` Codex passes write
  `refresh_token: ""` (`0600`) inside `$PDD_STATE_DIR/codex-home` so only PDD Cloud
  refreshes single-use OAuth tokens. Local state in `$PDD_STATE_DIR/accounts-state.json`
  (`0600`) stores metadata and refresh timestamps only, with zero tokens.
- **Stick-Until-100% and automatic `reauth_required` skip.** Inside `pdd` and
  `pdd autopilot`, steps stay on the active leased account with zero switches while
  both the 5-hour and weekly windows remain below 100%. Brief burst `429` responses
  below 100% retry on the same account so the prompt cache stays warm. Revoked or
  expired credentials (`reauth_required`, `401`, `token_revoked`, `invalid_grant`)
  surface as `reauth_required` in `pdd accounts list` and `pdd accounts status`
  and are skipped automatically during rotation. At 100% on either window, `pdd`
  reports the window to PDD Cloud, cools the account until `reset_at`, and switches
  to the ready account whose weekly window resets soonest.
- **Per-step isolation.** Owner Codex steps write the leased stripped `auth.json`
  (`0600`) into a disposable `0700` temporary folder (`/tmp/pdd-cx-…`) that symlinks
  `~/.codex/{config.toml,skills,memories,sessions,rules}`. Shared Codex gateway
  steps write zero `auth.json` in `/tmp/pdd-cx-…`, symlink
  `~/.codex/{skills,memories,sessions,rules}`, merge user settings such as
  `[mcp_servers.pdd]` into `/tmp/pdd-cx-…/config.toml` (`0600`), and pass
  `PDD_CODEX_GATEWAY_GRANT` via the child environment with `shell_snapshot = false`
  and `shell_environment_policy.filters`. Concurrent plain terminal chats keep their
  own `~/.codex/` untouched, and zero tokens appear in process arguments. Claude
  steps pass `CLAUDE_CODE_OAUTH_TOKEN` in the child environment, plus
  `ANTHROPIC_BASE_URL` on shared gateway grants.
- **Isolated PDD homes and opt-in terminal auto-switch.** Local Codex leases
  live inside `$PDD_STATE_DIR/codex-home` (`~/.local/state/pdd/codex-home`, mode
  `0700`, with `cli_auth_credentials_store = "file"`, merged user `~/.codex/config.toml`
  settings, and symlinked `~/.codex` skills, memories, sessions, history, and rules),
  leaving `~/.codex/auth.json` untouched. `pdd accounts auto on` writes one marked
  block in `~/.zshrc`, `~/.bashrc`, and `~/.config/fish/config.fish` that routes
  plain `codex` and `claude` invocations through `PDD_CODEX_AUTO_FAIL_OPEN=1 command pdd-codex`
  and `PDD_CLAUDE_AUTO_FAIL_OPEN=1 command pdd-claude` (passing through to stock
  `codex` / `claude` when `pdd-codex` / `pdd-claude` is absent, or failing open to
  personal credentials on transient Cloud outage while keeping `codex login` / `logout`
  on `~/.codex`). Set `PDD_LEGACY_PTY_ROTATE=1` to use the legacy `pdd accounts sync`
  and `pdd accounts codex --` PTY rotation path. `pdd accounts auto off` removes the
  marked block cleanly.

## GitHub API budget

Autopilot uses your own `gh` sign-in, so its GitHub calls use your hourly limit
(5,000 REST calls for a person). pdd counts each `gh` call of the Autopilot tick,
and of `pdd` commands in a repository where Autopilot runs on this machine, with
its purpose and the limit that GitHub reports in the reply headers:

| Purpose | Calls |
|---|---|
| `dependencies` | Issue dependency, timeline and sub-issue reads |
| `claims` | Claim checks and the `lastSeen` heartbeat |
| `issues` | The tick's issue list, comments and permission lookups |
| `pulls` | PR, review and check reads |
| `writes` | Other writes, such as a PR or a reply |
| `setup` | Sign-in, repository and settings calls |
| `other` | Everything else, such as `pdd metrics` |

pdd does not count the `gh` calls that the agent jobs make themselves. It also does
not count other machines or your own work on the same login. All of them use the
same limit. The counts stay on this machine, one file for each repository in
`~/.local/state/pdd/autopilot/github/`. Each tick keeps the last 2 hours.

A conditional read sends the ETag of the last reply. A `304` reply means that
nothing changed, and GitHub does not count it against the limit. The Autopilot
tick uses conditional reads with one shared ETag file in the same folder. A
full page (100 items) that has no next page is read without its ETag: a `304`
reply does not show that a next page came.

pdd keeps one saved dependency snapshot for each repository in the same folder
(`*.snapshot.json`, private to you). A read
asks GitHub only for the issues that changed since the last read (`since`, in
update order). It reads the comments, links and history of an issue again when its
update time, comment count or link identities changed. It checks the open index
with conditional requests and compares native link identities in batches. Equal
link counts can still mean different blockers. Incomplete batch connections fall
back to complete REST link pages. Once a day it rebuilds the open list, so a
deleted or moved issue leaves it. Safety reads always ask GitHub (a `304` is
fine): claim checks, heartbeats, trust, and the readback after each write.

The budget acts on the tick, and its floor on the dependency commands too. It
has two settings in `pdd.json`, a share (default 30%) and a floor (default 1,000
calls):

```json
{"autopilot":{"mode":"auto","trust":[],"github":{"share":30,"floor":1000}}}
```

`share` is a whole percent from 1 to 100; `floor` is a whole number of calls. A
missing or invalid value uses the default.

- **Low.** The counted REST calls of all Autopilot repositories on this machine
  in the last hour reach the share. A 304 reply does not count. When several
  machines hold live claims on one repository, each machine gets the share
  divided by their number. Then no new job starts, and the tick says
  `intake held: the GitHub budget is low (…)`. Jobs go on.
- **Reserve.** GitHub reports fewer calls left than the floor, for REST or
  GraphQL. Then the tick reads no issue list until the reset. It refreshes only
  the heartbeat of each live claim of this machine, so a claim does not expire
  while its job works. Native dependency snapshot reads for an Autopilot
  repository also stop non-safety reads. A reply that shows fewer calls than
  the floor stops the reads after it. Reviews that were already saved are never
  saved twice.

The agent jobs' own `gh` calls are not counted and do not wait for the floor.
Safety reads (claim checks, trust, permissions and write readbacks) and writes can
use the reserve. Other `pdd` operations are counted but do not wait for this
floor. The budget does not keep 70% of the limit for you.

The dependency snapshot is saved beside the repository's GitHub call ledger as
`github/H.snapshot.json` in the Autopilot state folder. Its temporary lock is
`github/H.snapshot.json.lock`, with the same repository hash `H` as the ledger.
If a writer exits while holding this lock, later saves refuse to replace the
snapshot. To recover, stop local PDD operations for that repository and confirm
that no snapshot writer is still running. Then remove only that empty lock
directory. Keep the snapshot and ledger files. The next observation can save again.

### Alerts

Autopilot can tell you about an incident or a decision that needs you. Set your
own destination once on each machine:

```sh
pdd autopilot alerts set    # paste the URL, press Enter, then Ctrl-D
pdd autopilot alerts test
```

The URL comes only from stdin, never from an argument, so it stays out of your
shell history. You can also pipe it from a password manager. pdd saves it in
`~/.config/pdd/autopilot-alerts.json` (`$XDG_CONFIG_HOME/pdd` when it is set),
outside every repository, with mode 0600. When `HOME` is empty or not an
absolute path, pdd uses your account's home folder; without one it saves
nothing. pdd never prints it, also not in errors. A Discord webhook gets `?wait=true`, so the reply is the posted message.
A Slack incoming webhook must reply `ok`. Only these replies count as delivered.

A team with a Discord bot can use it instead of a webhook. Give the channel ID and
the bot token. The token comes from stdin and is saved like the URL, or from your
own command, which pdd saves and runs at each send, so the token is never written
to disk:

```sh
pdd autopilot alerts set --discord-channel 123456789012345678 \
  --token-command 'gcloud secrets versions access latest --secret=NAME --project=PROJECT'
pdd autopilot alerts test
```

The bot posts with the Discord API v10, with link previews off, and reads the
message back. Only a matching readback counts as delivered. A change of line
ends or of spaces at a line end is not a mismatch. `set --token-command` and `test`
check the bot and the channel, read-only, and show the bot name and the channel name.
pdd never prints or saves the token or the command stdout; when a token command
fails during `set` or `test`, pdd shows only scrubbed single-line stderr. The bot needs permission to
view the channel, send messages and read message history.

The core sends an alert only for a real need. It sends `stuck` when a job process
reaches its backstop, when a PR waits too long for the merge lane, or when an END
cannot finish. It sends one informational `long-running` note when a job process
runs for 3 hours; work goes on. It sends `usage-limit` when it pauses new jobs
after jobs end with no result. Each alert gives the cause, what Autopilot tried and
what it needs. To record one alert yourself, give that JSON on stdin:

```sh
pdd autopilot alert --issue 12 --kind usage-limit --input - <<'PDD_ALERT'
{"cause":"Codex usage limit; resets 2026-11-06T18:00Z","tried":"Paused issue 12 and continued other work","need":"More quota or another signed-in account"}
PDD_ALERT
```

Each message names the repository, the issue link, the cause, what Autopilot tried
and what it needs. Answer on the GitHub issue, so the answer stays with the issue.
A usage limit, a resource failure, an interpreter outage or an interpreter access problem
(`interpreter-access`: this machine cannot read the interpreter health check) is one incident for the
repository and machine, so a limit that blocks 5 issues sends one alert. A call for another
blocked issue adds that issue to the incident and sends nothing. The machine is
the name that Autopilot saved at its first start (this checkout's start first),
else the host name, so a host rename does not open a new incident. An access or spending decision, a product
decision, a stuck issue or a long-running issue is one incident per issue. A repeat call sends
nothing for a delivered or unconfirmed alert, and sends again an alert that
failed or had no destination; a delivered `pdd autopilot alerts test` and later Autopilot ticks also retry open failed or newly configured alerts once. `--update` sends a new cause, a changed decision needed or the new
issue list. Changing only what was tried sends nothing. `--kind recovered` sends one recovery and closes the matching
alerts; give `"kind"` in the JSON to close only that incident. Every call and
its delivery result are recorded in
`~/.local/state/pdd/autopilot/alerts/`. Without a destination, the alert stays in
that record. Work continues in both cases. Each repository's alert record has a
shared lock, so parallel calls cannot overwrite incidents.

To send infrastructure incidents to another channel, set a second destination:

```sh
pdd autopilot alerts set --destination infrastructure
pdd autopilot alerts test --destination infrastructure
pdd autopilot alerts clear --destination infrastructure
```

The bot options also accept `--destination infrastructure`. Its secret is saved
in `autopilot-infrastructure-alerts.json` beside the ordinary destination with
the same private permissions. Set, test and clear affect only the selected
destination. The default is `--destination autopilot`. Machine incidents
(`usage-limit`, `resource`, `interpreter`, `interpreter-access`) and their
recoveries use the infrastructure destination when it is set. Without it they
use the ordinary destination. Issue decisions and stuck alerts use the
Autopilot destination. A test clears only that route's older delivery failure. An open undelivered incident still
needs attention. Configure external credential-maintenance and machine-health
senders at their own source; PDD does not change those programs.

## Tests on the PDD interpreter

Before a check, PDD prints one local plan. It lists target Stories, the changed
paths that affect each Story, and their dependency closures. A full batch also
lists unrelated Stories as baseline obligations. The plan shows estimated model
calls and a maximum that includes one restart replacement per test. It does not
authorize more calls. A full check with a missing interface or undefined call
bound stops with a named prerequisite and no paid check.
This is local issue work. Repair the named interface or call bound, then run a
fresh `pdd test`. A saved read or `pdd test --retry BATCH` returns the local
result and repair guidance with exit 4. It keeps the batch history and sends no
paid work. An interpreter wait cannot repair a local prerequisite.

Check JSON and saved batches include `check_plan`. Results also include
`check_scope`, with separate target and baseline states and recovery guidance.
A baseline failure stays in the failed full batch. Hand it to its owner; do not
rerun unchanged target checks to repair it. The classification does not prove
the failure's age or owner. Required repository full-pass gates still apply.
Saved reads use the original plan. Without reliable change scope, PDD marks the
selection as conservative and retains the selected Stories as targets.
Deleted generated implementations keep their owner through the comparison
revision's Generated-from header. If permitted metadata cannot prove a deleted
path's owner, the selected Stories remain conservative targets. Workspace
exclusions also apply to these historical metadata reads.

`pdd lint`, `pdd test` and `pdd test --files` report broken selected tests first,
with the file, reason and fix step. Missing or unreadable dependencies and invalid
test files do not stop other selected tests. The summary counts tests that could
not run. JSON and saved batches retain these rows. The command exits nonzero if
any selected test is broken. Broken tests are not sent for paid checks.
Local numeric-review metadata keeps the same isolation. An unreadable test
retains its refusal while valid reviews still apply to readable siblings.
This also applies when a selected test changes during source capture. Capture
checks its criterion texts and coverage against the captured Story before upload
or cached-pass reuse. Authored partial-test metadata still refuses the test.
A test with no exact criterion is refused and keeps all not-checked reasons.

A Story criterion with no check or no exact check is reported as
`not checked: <reason>`. Other criteria still run. An omitted Story item is also
not checked. The Story is not a full pass while any criterion is not checked,
and it cannot enter the complete-pass cache. PDD uses the engine's exemption
format in the uploaded scenario copy. It leaves authored files unchanged.
Changed criterion text and other malformed test rules still refuse the test.

<!-- BEGIN GENERATED: cli-commands:interpreter -->
| Command | What it does |
|---|---|
| `pdd test --target code [STORY...] [--json]` | Run Story cases against declared CLI code without AI calls. |
| `pdd test --affected [--cache-clear] [--json] [--details] [--timeout MIN] [--max-calls N]` | Check every affected Story with conservative full fallback and a separate historical baseline report; required full-pass gates still apply. Also accepts --fresh and --batch-timeout MIN. |
| `pdd test --journeys [JOURNEY] [--max-calls N]` | Check all root product journeys or one journey. Also accepts --fresh and --batch-timeout MIN. |
| `pdd test [PATH\|STORY...] [--lf] [--cache-clear] [--fresh] [--json] [--details] [--timeout MIN] [--batch-timeout MIN] [--max-calls N]` | Check stories on the PDD interpreter with your gh login: reuses unchanged passing Stories from .pdd/cache/test/; --lf selects previous failures in scope or uses the normal selection when none match, --cache-clear clears the cache and sends the selected Stories again (the interpreter may reuse saved answers), --fresh bypasses local cache reuse and server-side saved answers (fresh: true; also accepted with --affected and --journeys); sends selected PATH or STORY dependencies (every Story when you name none), waits for every check (no default limit in any shell; --timeout MIN caps each Story wait and --batch-timeout MIN caps the whole batch wait) with a progress line every 30 s, then prints one table with report links. Defaults to 12 calls per step, at least 18 and at most 1000; --max-calls accepts 1 to 1000. |
| `pdd test [PATH\|STORY...] [--max-total-calls N] [--no-restart-replacement] [--max-calls N] [--timeout MIN] [--json]` | Cap logical interpreter calls across all selected Stories and any permitted service-restarted replacement (--max-total-calls 1..999999), or decline automatic service-restarted replacement (--no-restart-replacement; saved across --read and --retry). Also accepted with --affected, --journeys and --batch-timeout MIN. |
| `pdd test --read [BATCH\|CALL_ID] [--json] [--details] [--timeout MIN]` | Read saved results (--details includes step and check detail, outputs, errors, calls and draft interfaces; also accepts --batch-timeout MIN); a normal Check held for lint may continue its original checks. Other reads send no work. |
| `pdd test --retry BATCH [--json] [--details] [--timeout MIN]` | Retry only confirmed unstarted checks from a saved batch, with the same source and call caps (also accepts --batch-timeout MIN); preserve completed and uncertain runs. |
| `pdd test --reconcile REQUEST_ID\|BATCH [--json]` | Read-only reconciliation of a historical CHECK request UUID against the PDD interpreter, or reconcile unresolved prior reservations for a saved local batch ID without replaying checks. |
| `pdd test --reconcile-stale [--json]` | Reconcile unresolved stale prior batch reservations for this repository, settling confirmed receipts or expiring reservations past TTL without replaying checks. |
| `pdd test --explain-bindings [STORY...] [--json]` | Explain local resource edges, fixture selection and repairs before any paid call. |
| `pdd test --files [STORY...] [--app-map PATH] [--json]` | List the exact selected upload files and byte sizes; no network. --app-map selects the Prompt Interpreter's app map. |
| `pdd test --screen URL --drawing PATH [--look] [--json]` | Compare a real page with its drawing at the drawing viewport in installed headless Chrome/Chromium (--look also checks main colors, painted boxes and spacing within tolerance); no AI or interpreter calls. |
| `pdd lint [STORY...] [--diff [BASE]] [--json]` | Run fast offline structural, SVG layout, and optional diff checks (0 AI, 0 network). |
| `pdd lint --local [STORY...] [--json]` | Run offline local structural, compact scenario JSON, criterion-binding, and native-evidence checks (0 AI, 0 network). |
| `pdd lint --remote [STORY...] [--json] [--timeout MIN] [--max-calls N]` | Run hosted PDD interpreter cross-prompt lint (0 AI calls) on selected Stories and dependencies; --max-calls (1..1000) previews call budgets. |
| `pdd lint --codex [STORY...] [--issue N\|FILE] [--json] [--timeout MIN]` | Run local deterministic lint plus read-only Codex readability, Story-vs-Prompt alignment, and optional issue-coverage checks. |
| `pdd lint --emit-v1 [STORY...] [--write] [--json]` | Expand compact scenario JSON files to full scenario JSON offline (--write updates each selected test file on disk). |
| `pdd lint --bind-criteria [STORY...] [--json]` | Bind matching Story acceptance criteria in selected test files to current content-hash IDs on disk; 0 AI/network calls. |
| `pdd prove [--base REF] [--timeout MIN] [--json]` | Run offline lint, diff checks, repository tests, and merge-base trusted verify.paths recipes against REF (default timeout: 10 min per step). Exits 0 Proved, 1 Failed, 2 Usage, 3 Not proved. |
| `pdd prove --base REF --test CMD --expect TEXT [--overlay GLOB] [--setup CMD] [--timeout MIN] [--json]` | Run isolated base-vs-head bug-contrast proof in temporary worktrees: proves CMD fails on base with TEXT and passes on head (default timeout: 10 min per phase; --overlay adds extra files alongside changed tests). Exits 0 Proved, 1 Failed, 2 Usage, 3 Not proved. |
| `pdd [OPTIONS] <PROMPT.md\|app-map.json> [ARGS...]` | Run a prompt program directly on the PDD interpreter (Python-style: options before the file belong to pdd; trailing args pass verbatim to CLI or typed prompts, or use -- to force passthrough). Prefix options include --fresh, --new, --data FILE, --show-data, -q/--quiet, --page, --cli, --shell, --serve [PORT], --allow-origins CSV, --trust-proxy, --serve-token TOKEN, --serve-header NAME, --max-calls N, --tab, --app-map PATH, --no-open, --no-wait, --agent NAME, and --stop. |
| `pdd <PROMPT.md\|STORY\|.> [--max-calls N] [--tab call\|screen\|terminal\|world] [--app-map PATH] [--new] [--fresh] [--no-open] [--no-wait] [--agent NAME]` | Open the prompt, Story, or whole project (.) automatically on the Prompt Interpreter: a command-line program opens a shell, HTTP routes start on localhost with an example request, screens (including single-file plain-prose UI prompts without app-map.json or Runtime interface) open the Prompt Interpreter Screen page, and typed operations open its Form tab. Make a session on the PDD interpreter with your gh login; it ends in 24 hours. A new session defaults to 400 calls; --max-calls accepts 1 to 1000. --fresh requests fresh uncached interpreter execution (fresh: true; also accepted with --page, --cli and --serve). With terminal stdout or explicit --agent, it stays running to connect your own agent; otherwise it reads saved cases once and returns. --agent selects a configured name or a default Codex, Claude or Gemini; --no-wait skips the bridge. In a terminal it adds each saved test case to the Story's test file. |
| `pdd <PROMPT.md\|STORY\|.> --page [--new] [--fresh]` | Open the Prompt Interpreter browser page explicitly. |
| `pdd <PROMPT.md\|STORY\|.> --cli [--shell] [--max-calls N] [--new] [--fresh]` | Run your program in your terminal through a Prompt Interpreter session; prints a PATH line, or opens a shell with --shell. Use --shell alone to open the shell. |
| `pdd <PROMPT.md\|STORY\|.> --serve [PORT] [--allow-origins CSV] [--trust-proxy] [--serve-token TOKEN] [--serve-header NAME] [--max-calls N] [--new] [--fresh]` | Serve real HTTP requests through your Prompt Interpreter session on 127.0.0.1 (default port 8080). Opt-in --allow-origins CSV permits listed cross-origin clients (with CORS), --trust-proxy accepts forwarded Host headers from a local tunnel while binding 127.0.0.1, and --serve-token (with optional --serve-header) gates requests behind a bearer or header token. |
| `pdd --product [--parts PARTS] [--journey JOURNEY] [--max-calls N] [--no-open] [--no-wait]` | Compose declared product maps, data and planned operations into one Prompt Interpreter session. |
| `pdd --save-last [STORY]` | Save the last terminal command and its output in the original Story test file. |
| `pdd --stop [STORY\|PROMPT.md]` | Stop the open Prompt Interpreter link of a Story, prompt, or exact Try ID. |
<!-- END GENERATED: cli-commands:interpreter -->

For `--target code`, each tested Runtime entry declares
`"implementation": {"kind": "cli", "command": "node bin/tip.mjs"}`. The command
is split into words without a shell; quoted or shell-dependent command strings
are unsupported. Cases supply string `argv` and optional UTF-8 `stdin`.
The runner supports `equals` checks on `/exit_code`, `/stdout` and `/stderr`.
Other checks, HTTP and call entries, and world or port simulations without a
native bridge report `not run` with a reason. Results are saved in
`.pdd/code-test/latest.json` with the commit and worktree dirty state; a failed
or unrun Story makes the command nonzero.

Ordinary `pdd test` reuses complete unchanged Story passes from the Git-ignored `.pdd/cache/test/` folder, showing their previous pass time and zero current AI calls. `pdd test --lf` selects the last known failures; a later attempt without a verdict keeps a failure selected until it passes. With no failures in the selected scope it uses the normal selection, including unchanged-pass reuse. Completed saved reads populate the cache after source verification, dated from the original batch start, never the later read time. `pdd test --cache-clear` discards prior local evidence and runs the normal selected scope; it takes precedence over `--lf`. It sends again and prints one stderr notice with the selected Story count; the interpreter may return a saved answer for the same key.

Reuse includes reached call targets, exact authored bytes, interpreter origin, call budget, pdd version, and the interpreter build and requested model reported by job answers. A missing identity or a pass older than seven days runs again. A different build or model observed during a run also runs the selected Stories initially skipped, with a reason; after a timeout or interrupt those rows are marked not sent. Reuse requires one clean record naming the same known build and model as the pass. A clean normal run starts after the previous sample, sees no record change during the run, and has only agreeing complete identities. Overlap, any read that writes the record (even after resending), an old or unknown writer, partial or mixed observations, or multiple stored values leaves doubt and runs. A later clean normal run can restore reuse. Before sending checks, a run saves an in-progress mark with its pid and start time. Another run's mark, live or dead, makes checks run. Live marks remain until their owners finish; dead marks are retired after forcing a run. A run can finish clean only while it still owns its mark and no other run has changed the record; it removes only its own mark. A failed sign-in removes its own mark but leaves doubt. All check sends share one ownership boundary: normal checks, saved-read continuations, retries and recovery hold their own mark from before the first send until their last send and observations finish. A retry retains ownership across its initial read. Reads and retries finish with doubt; direct callers with reuse disabled still coordinate their sends. Cache clear preserves every in-progress mark. A crash therefore costs one extra run, and overlap remains doubt until a later clean run. An all-skipped local run cannot discover an interpreter update without calls. Stories using the real clock or AI-played fakes run every time and say why; completely deterministic simulation bindings and fixed clock data permit reuse. Fixed clock values must be finite numbers or ISO 8601 date-time strings; labels such as `real 2026`, `now 1` and `1` run with the real-clock reason. Unknown resource kinds or actions run. Missing Story footprints, missing sources or malformed declarations report `runs again: resource declarations unavailable`; reuse can resume once evidence is complete; plain dependencies without an interface declare no resources. An expired pass reports `runs again: saved pass is older than seven days`. `CI` unset or set to the empty string, `0` or `false` permits ordinary reuse; every other value runs every selected Story. Tracked cache files and caches copied without their external machine-local state are never reused. Damaged regular metadata heals after a completed run; its warning names `pdd test --cache-clear`. Dead-owner cache locks recover with one warning. Symlinked ancestors of `PDD_STATE_DIR` are accepted, but a final state-folder symlink is refused.

Run local source preflight and the prompt check in one shell call:

```sh
pdd test --files STORY && pdd test STORY
```

Replace STORY with the selected Story name; omit STORY to preview and check all
Stories. Each command must succeed before the next starts. Run offline `pdd lint`
first to catch local structural, SVG, and scenario problems immediately (0 AI, 0 network).
`pdd test` performs hosted interpreter lint automatically before sending checks, so
you do not need `pdd lint --remote` immediately before `pdd test`; use `pdd lint --remote`
when you want hosted cross-prompt admission diagnostics without running AI checks.

`pdd test` reuses a passing remote lint received within ten minutes for the exact same
captured source, test selection, interpreter endpoint, signed-in account,
package version and lint options. It retains the original receipt for saved
reads; reuse does not extend its age. Local validation and server admission
still run. Missing, incomplete, failed, expired or changed evidence runs lint
again. A reported current interpreter build must match the saved build; when
capacity does not report a build, reuse cannot detect a deployment inside that
short window. This receipt is independent of the complete Story pass cache and
never proves behavior or grants approval. Explicit `pdd lint --remote` always runs fresh.

`pdd lint --remote --json` includes `report_url` with the interpreter's same-origin report
link, or null when no safe link is available. Text output prints `Report: <url>`
for the same link. Saved remote lint reads retain it. Plain `pdd lint --json` runs
locally offline (`pdd.local-lint.v1`) with zero network calls and no report URL.

- A new Prompt Interpreter session defaults to 400 calls. Both `pdd test --max-calls N` and direct `pdd <PROMPT.md|STORY|.> --max-calls N` accept 1 through 1000. Checks default to 12 calls per step, at least 18 and at most 1000. Choose at least three times your worst-case estimate.
- `pdd test` and saved-batch `pdd test --read BATCH` wait until every Story ends in every shell. Only `--timeout MIN` (per-Story wait) and `--batch-timeout MIN` (whole-batch wait) set caller limits. Use the shell tool's longest timeout or an exit-notifying background task; if stopped, run the printed recovery read once. Never poll every minute.
- The optional profile job cap has no default limit. Set `PDD_MAX_JOBS` to a positive safe decimal integer to share that cap across repositories and worktrees among local pdd processes that set it; capped jobs wait their turn and show how many jobs are ahead. An invalid value warns once per command and uses no cap. When the interpreter is busy and confirms that your job did not start, pdd waits and tries again until your wait ends. After a saved lint passes, `--read` can start the original checks that were waiting for it, using the same files, owner and call limits. `--retry BATCH` retries checks confirmed never started, using the same files after lint passes. See [waiting for capacity](lint-capacity.md) for recovery and restart handling.
- Check source uploads use at most 8 unanswered POSTs at once per pdd process. Set `PDD_MAX_UPLOADS` to a positive safe decimal integer (leading zeros are allowed); invalid values warn once and use 8. Each answered POST or transport failure frees its place while server jobs continue running; GET reads use no upload places. This laptop upload setting protects your own connection from the 90-second POST timeout, and is not a server limit. It uses no shared job-slot queue.
- Lint and check results use `waiting`, `sent`, `passed`, `failed`, `refused`, `partial` or `not run`. Every result except `passed` includes a reason code in text, JSON, saved batches and PR evidence. Only `passed` is a full pass.
- Default `pdd lint` runs fast offline structural, SVG, scenario, and optional `--diff` checks with 0 AI calls, 0 network calls, and 0 batch-state writes. `pdd lint --local` runs the offline local assessment path (including local scenario/criterion checks) and reports `partial` with code `local-only` when run through runtime assessment; it cannot substitute for hosted `pdd test`. Use `pdd lint --remote` for hosted interpreter cross-prompt lint (0 AI calls).
- For a new check, `--timeout MIN` starts after the free lint. Preliminary lint has a separate wait of MIN minutes, capped at 90 seconds in an agent shell. This bound includes maintenance, local slots and capacity waits. A timeout reports `timeout-flag` and names `--timeout`. Standalone `pdd lint --remote --timeout MIN` bounds remote lint itself, including admission and capacity waits before sending. A caller stop cause takes precedence over `server-busy`; raw capacity receipts keep their server codes. A default remote lint wait reports `deadline`.
- Offline-only work uses `pdd lint --local`, local authoring review, `pdd files` and `pdd test --files`. It is not a server lint pass. Factories can bind through opaque handles and collections (or explicit interface v2 instances); ports and SQL, blob and compute resources cover declared simulation. Native effects stay unbound; see [Interpreter boundaries](runtime-boundaries.md).
- Running `pdd STORY` for a paused Prompt Interpreter session explicitly reopens the same session before showing its link. Its original expiry and remaining call allowance stay in force; an unconfirmed reopen is nonzero.
- A `draft` prompt can be checked, and its result is marked DRAFT. A DRAFT pass is not an approval.
- With no test file, `pdd test` says `No tests found` and lists why, for example a Story with no `tests/<story>.json`, a `.json` file in a test folder that matches no Story, or a prompt that ends in `.prompt` instead of `.prompt.md`.
- A GitHub login that is not invited gets one line: `Your GitHub login NAME is not on the PDD interpreter invite list yet. Ask the PDD team to add you.` A GitHub account without PDD Cloud access gets the server's sign-up line (sign up at https://promptdriven.ai/login). When PDD Cloud cannot check the account, pdd says at once `PDD Cloud could not confirm your access. Try again in a minute.` A pdd that is too old gets `Please update pdd: …`. All of these exit with code 5.
- The interpreter address is set in one place in pdd. You do not need to set it.

Linked `.ui.svg` drawings specify the screen's parts, words, spatial order, ids and named state. Local lint (and preliminary local checks in `pdd lint` / `pdd test`) reports unmatched controls, labels, unspecified layout regions, HTML operation screens whose app map leaves `"stylesheets": []`, and HTML screen prompts that name none of their stylesheet's CSS classes, plus built-in deterministic rules in `pdd lint` (`prompt-larger-than-code` checking `prompt lines < code lines` when owned code exists, `test-private-import` and `test-private-access` checking that tests in `test/` use public module interfaces only, `prompt-missing-title`, `prompt-missing-dependencies` and `prompt-missing-diagram` checking required prompt structure and diagrams where applicable, fake-test checks, imperative or oversized fenced prompt blocks, Story criteria hygiene, misplaced prompt owners including `test/**` / `tests/**` / `*.test.*`, prompts above 500 or 1,000 prose lines, Stories above 15 scenario steps or 1,000 lines, and `TODO`/`FIXME`/`HACK`/`XXX` excuse comments in prompt-owned code); a generic data-field mention does not describe a score box or status bar. Projects can configure `"lint"` in root `pdd.json` with `"disable"`, `"rules"` (`"off" | "warn" | "error"`), and `"custom_rules"` (`{id, target, include, exclude, severity, forbid_pattern, require_pattern, require_heading, max_lines, flags, message}`) on top of the built-in defaults; default warnings do not change the exit code, while `"error"`-severity rules fail lint with exit code 1. Default local lint also checks any explicit schemas and frontmatter declarations in workspace prompts; malformed declarations exit 4. Named Runtime Story local lint stays advisory; dependency prompts supply layout and ownership context. A native-only declaration needs a reason. These local checks do not certify semantic or visual agreement. `--local` belongs to `pdd lint`; it mixes only with Story names and `--json`. `--codex` belongs to `pdd lint`; it mixes only with Story or prompt paths, `--issue N|FILE`, `--json` and `--timeout MIN` (`--issue` requires `--codex`).

An explicitly selected Story with a `Native validation` owner link is assessed from its saved native evidence by `pdd lint STORY`, including `pdd lint --local STORY`. This reads no hosted service and creates no association. Missing native proof exits 1; complete current whole-Story proof exits 0. It is separate from the SVG-only advisory for Runtime Stories.

For a built screen, serve the app in the state shown by its drawing and run, for example, `pdd test --screen http://127.0.0.1:8080/ --drawing prompts/views/active__stacked.ui.svg` (add `--look` to check main colors, painted boxes, box bounds and spacing within tolerance without pixel equality). Set `PDD_CHROME_PATH` to a Chrome/Chromium executable when discovery needs help. The command checks every visible text occurrence and id, including numeric values, at the SVG viewport; metadata, hidden and context-only drawing regions are excluded. It accepts center differences of at most 15% per viewport axis and requires the same spatial order of separated parts; `--look` appends `look` rows for the canvas color and painted card/section/control boxes so an unstyled screen fails. It prints a `Screen vs drawing` table for the code PR; retain any stricter accepted visual comparator. Exit codes are 0 for pass, 1 for mismatch, 2 for invalid input and 5 when browser/navigation execution fails. `--screen` requires `--drawing`, accepts only `--look` and `--json` alongside them and takes no Story names. JSON includes the comparison rows and `exit_code`.

For a supported Prompt Interpreter Screen viewer, comparison waits up to 10 seconds after
page load for readiness, app fonts and layout. It inspects only the marked
same-origin app iframe or open shadow surface, using the app's local viewport.
Shell labels and offsets do not participate. Comparison never opens the app,
clicks controls or sends an action. If the app is not open, deliberately open it
before rerunning; opening can spend AI calls.

Exit 6 means the Screen is not ready, rather than a drawing mismatch. Text gives
the state, reason and next step without a parts table. JSON contains exactly
`drawing`, `url`, `outcome` (`not-ready`), `code` (`screen-not-ready`), `state`,
`reason`, `message` and `exit_code` (6), without `rows` or `passed`. Reasons include
`timeout`, `not-open`, `state-read-failed`, `render-failed`, `action-unknown`,
`surface-unavailable` and `viewer-update-required`. An old or unsupported viewer
must be updated before comparison. An unknown action needs read-only state
reconciliation; the comparator never sends it again. Ordinary page reports and
exit codes remain as described above.

See [Check prompts on the PDD interpreter](USAGE.md#7-check-prompts-on-the-pdd-interpreter) for the exit codes, `pdd test --help`, `pdd lint --help` and `pdd . --help` for the options, and [`skills/pdd/references/stories.md`](../skills/pdd/references/stories.md) for the file formats.

The Prompt Interpreter's agent fills the fields directly when supported. It runs the action only when you explicitly ask, in your own words; otherwise you press Run. Actions use the session call budget. Older pages keep manual Fill fields and Run.

## Try tools for your agent

<!-- BEGIN GENERATED: cli-commands:mcp -->
| Command | What it does |
|---|---|
| `pdd mcp` | Serve the current repository’s Try tools over stdio MCP. |
<!-- END GENERATED: cli-commands:mcp -->

The tools are `try_open`, `try_state`, `try_run`, `try_observe`, `try_check` and `try_save_case`. `try_open` and `try_state` include `source_sha256`, `engine_sha` and `server_commit` for the open Try. Supply `try_id` to bind an existing running session without opening or reopening one, and use `try_observe` to read call and session state without replaying a run. Use them when the person asks to try behavior. Runs count against the session call budget and appear in the Prompt Interpreter. Saved results are separate recorded cases with exact starting data. Complete missing Story coverage before `pdd test`; observations need review and are never approved expected values. MCP protocol messages use stdout; progress and diagnostics use stderr.

## Other commands

<!-- BEGIN GENERATED: cli-commands:other -->
| Command | What it does |
|---|---|
| `pdd jobs` | List active and waiting interpreter jobs on this machine without contacting the interpreter. |
| `pdd completion bash\|zsh` | Print local shell completion. |
| `pdd` | Show local commands. |
| `pdd --help` | Show local commands. |
| `pdd -h` | Show local commands. |
| `pdd help` | Show local commands. |
| `pdd help prompting` | Show how to write prompts, Stories and tests, and where the guide is. |
| `pdd --version` | Show this package version. |
| `pdd -V` | Show this package version. |
| `pdd -VV` | Show this package version and the interpreter build and supported formats; unknown when unavailable. Uses existing gh sign-in, with no AI call. |
<!-- END GENERATED: cli-commands:other -->

`pdd -VV` skips PATH and skill diagnostics. It reads the existing token with a
two-second limit, then sends at most one `GET /v1/version` to the configured
interpreter origin. The request and response body have one ten-second limit.
It follows no redirects, sends no source, starts no jobs and makes no AI calls.
When the interpreter also reports `service_sha`, `pdd -VV` prints `PDD service: <sha|unknown>` right after `PDD interpreter:`.
Format IDs keep the interpreter's order; an empty list shows `none`, and a
missing or unsafe list shows `unknown`. Each version flag must be one exact
token; repeated flags, extra operands and `--verbose` are unsupported.

## Run from a source checkout

From a clone of this repository, run the CLI without a global install:

```sh
npm ci --ignore-scripts
node bin/pdd.mjs --help
node bin/pdd.mjs --version
npm test
```

You need Node.js 22.16.0 or newer (22.20.0+ for Autopilot). Install dependencies with `npm ci --ignore-scripts` (the only runtime dependency is `@promptdriven/runtime-client`); there is no build step. See [CONTRIBUTING.md](../CONTRIBUTING.md).

Check, remote lint and Prompt Interpreter session setup use [local bookkeeping and capacity waiting](lint-capacity.md); they share a local slot cap when `PDD_MAX_JOBS` is set. Local waiting, maintenance and interpreter queue time all use the existing caller wait. Direct `pdd <PROMPT.md|STORY|.>` execution uses one five-minute setup allowance for lint and the rest of setup in every shell; it adds no timeout flag.

A saved Prompt Interpreter setup is read by its original request ID before any new setup is considered. A plain repeat keeps that ID when the setup is pending, unknown, missing, expired or ended; it does not create a replacement. Recovery diagnostics name the original UUID and its authenticated `GET /v1/runs/<UUID>` status endpoint. A known running setup reuses its existing link. Start a separate setup deliberately with `--new` after reconciling the original outcome. An unknown setup result does not prove zero AI calls or zero external effects.

`pdd <PROMPT.md|STORY|.> --cli [--shell] [--max-calls N] [--new] [--fresh]`

Use the program in your own terminal. Copy the printed PATH line or run the absolute shim path (`--fresh` bypasses saved answer caches).

`pdd <PROMPT.md|STORY|.> --serve [PORT] [--allow-origins CSV] [--trust-proxy] [--serve-token TOKEN] [--serve-header NAME] [--max-calls N] [--new] [--fresh]`

Serve the prompt, Story, or whole project on `127.0.0.1` (default 8080; `--fresh` bypasses saved answer caches; opt-in `--allow-origins`, `--trust-proxy`, and `--serve-token` with optional `--serve-header` permit cross-origin, tunneled, or token-gated requests).

`pdd --save-last [STORY]`

Append the last command and its observed output to its original Story test file.

An explicit `pdd lint --remote` that is still queued/running exits 3 and prints its saved read command; exit 0 means validation finished successfully. The all-Story cost estimate includes entry executions, declared saved-data operations and nested prompt-call allowances. Conditional operations may use fewer calls; `--max-calls` remains the hard cap.

Virtual CLI and HTTP startup print `Try AI usage` on stderr. Each virtual CLI command appends its usage line to stderr, keeping program stdout and exit status intact. It distinguishes calls for this command, total used and remaining in this session, and the session cap. Unknown counters stay unknown. Named HTTP routes carry `x-pdd-ai-calls`, `x-pdd-try-used`, `x-pdd-try-remaining`, `x-pdd-try-cap`, and `x-pdd-usage-source` headers; response bodies and program statuses stay intact. `runtime` identifies a confirmed call receipt; `last-known` identifies cached session allowance on a local zero-call response such as an unmatched route. Session allowance is separate from an account or tester allowance. Usage reads spend no model calls and never repeat commands.

`pdd test --read CALL_ID` reads an authenticated owner call receipt by UUID without sending the operation again. Interrupted `pdd <PROMPT.md|STORY|.> --cli` commands print the recovery command for this read. See [module binding coverage](runtime-bindings.md) for selected Story coverage and unbound reasons.

`pdd prove --base REF --test CMD --expect TEXT` leaves the repository checkout unchanged and runs both base and head snapshots in isolated temporary worktrees (default `--timeout` is 10 minutes per phase; timed-out runs report `Not proved`). `--overlay GLOB` adds extra matching files alongside the changed test files overlaid onto the base worktree. `--expect TEXT` matches in the failing base run's combined output (prefer a concrete assertion message rather than a test title). Fresh worktrees have no installed dependencies; include required installation in `--setup` or `--test`. Temporary worktrees are removed cleanly when execution finishes. Reference `verify.paths` verification scripts by repository-relative path (for example `node scripts/verify.mjs`) so Check 4 protects them automatically; if `pdd.json` sets `verify.report`, add that generated report path to `.gitignore` so repeated `pdd prove` runs keep a clean `commit` proof scope.

Preliminary lint shares Check's unlimited default caller wait; standalone remote lint retains its 90-second agent default and unlimited interactive wait. `--timeout` bounds either, with no separate lint cap. A saved-batch read of a lint-held Check waits without a default limit, retains the saved interpreter origin and dispatches each original check at most once. Explicit retry retains its finite default wait. Standalone lint reads never send checks.

Before sending work, pdd asks whether the interpreter has room. During announced maintenance, it shows the end time and reason, then waits within the same deadline. If the interpreter does not offer this information, pdd uses the reply to the submission instead. A queued job keeps its ID while pdd shows its place. If the interpreter confirms that a check ended because the service restarted, pdd tries that check once more and saves both attempts and their usage. If a reply is lost or the outcome is uncertain for another reason, pdd reads the original job without sending it again.

## Shared records

<!-- BEGIN GENERATED: cli-commands:contracts -->
| Command | What it does |
|---|---|
| `pdd contracts` | List shared records, their users and Stories stale since their last check; local working files only. |
| `pdd contracts sync [--write]` | Show proposed changes for moving schema copies to references; apply only with --write. No interpreter calls. |
| `pdd product contracts` | List shared product records, their users and Stories stale since their last check (alias: pdd contracts); local working files only. |
<!-- END GENERATED: cli-commands:contracts -->

Link `contracts/*.md` under `## Dependencies` in plain Markdown prompts; in JSON schemas (such as `state_schema` or an optional explicit Runtime interface), use `{"$contract":"contracts/phone-server.md#order_in"}`.
The Markdown section has a `### order_in` heading and one JSON code block;
headings with spaces also accept their normal heading fragment. JSON records use
`{"$contract":"contracts/records.json#/defs/order"}`. Local `title` and
`description` may accompany a reference; other constraint siblings are refused.
Use `"initial_world":{"$seed":"contracts/seed-world.json","set":{"/orders":[]}}`
for a shared starting world. Paths are relative to the repository root. Set
pointers apply in written order to a fresh world and may add an object's final
key; their parents must exist. Expected values and literal inputs stay literal.

`pdd test`, `pdd lint` and direct `pdd <PROMPT.md|STORY|.>` use expanded schemas/worlds, including uploaded bytes. A
missing target stops before upload. Real schema `$ref` remains refused. Explicit
`pdd lint` skips inline schemas with fewer than three fields. It advises
about a differing copy only when the shared record has at least four fields and
the copy has the same fields or one extra/missing field. Equal three-field copies
can still move to references. Required-field lists and enum alternatives compare
without order; arrays inside literal values keep their order. Advice does not
fail a check. Expanded uploads keep the original JSON layout and key order.
Sync changes only selected schema values and an approved-to-draft status, using
an atomic file replacement that refuses concurrent edits and unsafe paths. Listing uses actual Check
history, never lint as a check; no baseline is shown as not checked/unavailable.
Only Stories using a changed record become stale because of that record. A
Story stays current when you check one of its tests or include it in a larger
batch without changing its files.

Editing a contract never approves a prompt; review the sync preview and diff as
usual.

## Product plans

<!-- BEGIN GENERATED: cli-commands:product -->
| Command | What it does |
|---|---|
| `pdd product status [--json] [--through prompt-pr\|code]` | Count Stories by part and slice from the product plan; --through prompt-pr\|code selects the completion target; no interpreter calls. |
| `pdd product next [--through prompt-pr\|code]` | Show ready planned runs and their start commands; --through prompt-pr\|code selects the completion target; no interpreter calls. |
| `pdd product start RUN [--no-run] [--agent codex\|claude\|gemini\|agy\|ENTRY] [--through prompt-pr\|code] [--base BRANCH]` | Create or reuse the scoped run issue and print a /pdd handoff prompt; --no-run only prepares the issue; --through prompt-pr\|code sets the completion target; --base selects an existing origin branch; ENTRY is a name from ~/.config/pdd/agents.json. No interpreter calls. |
| `pdd graph` | Read native dependencies and saved reviews without AI. |
| `pdd graph --open` | Open the local viewer. |
| `pdd graph --issue N` | Select a root issue. |
| `pdd graph --open --issue N --repo OWNER/REPO` | Open a selected issue in an explicit repository, including outside a checkout. |
<!-- END GENERATED: cli-commands:product -->

See [Build a whole product](build-a-whole-product.md).

## Prompt review and approvals

Show prompt and Story changes in chat or on a GitHub pull request before asking for approval. The person reviews the diff and replies in chat or in GitHub PR review. Questions, change requests, and earlier messages are not approval. Agents never invent a person's decision, decide expected values, or merge without explicit permission.

## Metrics

<!-- BEGIN GENERATED: cli-commands:metrics -->
| Command | What it does |
|---|---|
| `pdd metrics [--repos] [--repo OWNER/REPO] [--date YYYY-MM-DD] [--timezone IANA] [--standup] [--json] [--html] [--file PATH]` | Show Autopilot overview metrics (Last 24h and Week Mon-Sun, or 9am-9am standup window with --standup) across active repositories on this machine, or per repository with --repos. |
| `pdd metrics stages [--repo OWNER/REPO] [--date YYYY-MM-DD] [--timezone IANA] [--standup] [--json] [--html] [--file PATH]` | Show Autopilot gate pass rates (Prompt tests, Vectors, Formal, Suite, Review, CI), merges, reopens, and non-merged status counts. |
| `pdd metrics skills [--repo OWNER/REPO] [--date YYYY-MM-DD] [--timezone IANA] [--standup] [--json] [--html] [--file PATH]` | Show Autopilot work mix (small-change, bug, feature, Total) with merge conversion and median completion time. |
| `pdd metrics full [--repos] [--repo OWNER/REPO] [--date YYYY-MM-DD] [--timezone IANA] [--standup] [--json] [--html] [--file PATH]` | Show all three Autopilot metrics views (Overview, Stages, and Skills) together. |
| `pdd metrics on [--repo OWNER/REPO] [--json]` | Enable Autopilot metrics recording on this machine (or for one repository). |
| `pdd metrics off [--repo OWNER/REPO] [--json]` | Pause Autopilot metrics recording on this machine (or for one repository) while keeping existing history. |
<!-- END GENERATED: cli-commands:metrics -->

See [Metrics](metrics.md) for the three Autopilot views, local state layout, and recording switch.

`pdd graph` reads the saved dependency graph; `pdd graph --open` opens its viewer. Use `pdd graph --issue N` to select an issue, or `pdd graph --open --issue N --repo OWNER/REPO` to select a repository explicitly.

## Shared full-suite queue

`pdd autopilot suite --command COMMAND [--timeout MIN]` runs the repository's full
suite through one machine queue. Use the actual repository command, for example
`pdd autopilot suite --command "npm test"`. Focused tests can run normally.

Each suite uses fresh temporary HOME, PDD_STATE_DIR, XDG_CONFIG_HOME and TMPDIR
folders. The runner removes them after execution. It passes PATH, locale, time
zone, terminal and CI settings, the browser path and its assigned PDD_CHECK_CPUS.
Agent settings, credentials, session variables, shell hooks and Node/npm overrides
are absent. Set extra variables explicitly in COMMAND when the suite needs them.
Queue admission still uses the caller's queue selectors. Each ticket records
`environmentPolicy: "clean-v1"`, without environment values.
If private folder setup fails before execution starts, the ticket finishes with
the failure reason and releases its slot. Any allocated private folders are removed.

The native CLI prints a receipt path in the shared queue and an output-evidence
log path under user state for each attempt. The compatibility runner keeps its lifecycle output; its
receipts are in the same queue. The receipt stores a redacted command, its SHA-256 fingerprint, cwd, starting Git head and
worktree fingerprint, matching workflow run, owned recorder and child, terminal
exit and signal, and complete TAP summary counts when available. Missing counts
stay unknown. Logs and receipts use mode 0600. Logs are under PDD_STATE_DIR, or
HOME/.local/state/pdd, in a validation folder for the selected queue.
`scripts/vm-suite-lock.sh` and `scripts/vm-suite.sh` select caller log state
explicitly: a nonempty PDD_STATE_DIR wins; otherwise they use
`PDD_SUITE_QUEUE.state`, or `LOCK.queue.state` beside the resolved compatibility
lock when no queue selector is supplied. Logs survive temporary child cleanup.
Without a state override, an external lock and queue keep both scripts' writes
outside the caller HOME.
The legacy history stays beside the lock. Factory callers select their own
private PDD_STATE_DIR; HOME fallback tests use disposable homes.
Log names
combine the queue-path hash, ticket and a random attempt ID. An existing file
causes a fresh ID to be selected. Resetting the queue or rebooting preserves
earlier logs and permits a new attempt. Commands are saved as
`[redacted]` because positional arguments can hold secrets. Execution uses the
original command. Known secret values in output and error text are redacted before any save or
forwarding. The completeness guarantee covers what the validation child can
print: secret-named values in its own environment (TOKEN, SECRET, PASSWORD,
*_KEY and similar names), and credentials pdd passes in arguments, handed-over
files or agent-definition environment overrides. A CUSTOM_API_KEY loaded from
agents.json is included before a child receives it. Credentials held only by
other processes, such as an alert bot token that the validation child cannot
read, are outside this threat model. Exact matching scans original text from
left to right and consumes the longest known match at each position, regardless
of registration order. This rule also applies to receipt strings and errors.
Each stream keeps a bounded overlap window based on the longest known value.
Exact matches can span chunks and lines, including values containing LF.
Transformed or encoded copies are outside this exact-value guarantee.
Pattern redaction for unknown headers, assignments and private keys is a
best-effort extra layer. Unknown formats, encodings and arbitrary positional
values can evade it. Do not treat pattern matching as complete secret detection.

Each log is limited to 1 MiB. Overflow keeps its beginning and end with an exact
`N bytes omitted` marker. A pending output line is limited to 256 KiB; a larger
line is omitted in full with its byte count. Bounded scanning still tracks
quoted secrets and private keys in omitted lines. Their continuation stays
redacted through its closing delimiter or end of output. A recognized credential
field stays pending across assignment whitespace, including line breaks and
omitted lines, until its quoted or unquoted value is redacted. Stdout and stderr
keep separate recognition state. Basic/Bearer schemes also stay pending across
line breaks and omitted whitespace until their credential is suppressed. Each receipt is limited
to 64 KiB, with free-text fields limited to 4 KiB. Required source and ownership metadata
that cannot fit prevents execution. The `evidence` fields report raw output
bytes, saved log bytes, omitted bytes and whether truncation occurred. Counts
and exit status use the complete process stream, including when storage is
truncated. Ordinary secret replacements do not count as omitted bytes. These
limits apply per attempt; earlier attempts remain available.

The recorder keeps the same validation running if its calling session disappears.
A later `pdd autopilot status` or `pdd autopilot logs` reads its saved progress without running the command
again. Completion saves the log and terminal receipt before returning. Explicit
SIGINT/SIGTERM cancels through the recorder; unexpected caller loss leaves the
original timeout in force. If custody is lost before a terminal receipt exists,
status reports an unknown outcome. A later validation has its own ticket and
keeps earlier evidence. A receipt describes execution; it does not approve a merge.

Full suites and full builds share machine capacity across repositories and
worktrees. Run a full build through the same command. Additional
runs show "waiting for a check slot (position N)". Autopilot status also shows the
queue position. For an Autopilot job, a wait for a check slot is not quiet time.
A suite failure, interruption or execution timeout has its own reason.

The execution timeout defaults to 30 minutes. `--timeout` accepts 1 to 120
minutes, or 0 for no time limit (Autopilot uses 0 and watches the suite for new
output instead). Waiting does not use that time. Output and exit status come from the
suite; timeout returns 124. The runner stops the suite process group before
releasing its slot.

The queue reads usable CPU IDs, free memory and one-minute load when it admits a
check. macOS and personal Linux machines use the first half of available
cores (round down, minimum one). Linux desktops without batteries are included.
Linux uses all available cores only when virtualization is detected and no battery
is present. Detection uses `systemd-detect-virt --quiet` with a one-second timeout.
If detection is unavailable or uncertain, Linux uses the personal-machine budget.
With U usable cores and M free bytes, calculated check slots are
`max(1, min(floor(U / 12), floor(M / 4294967296)))`.
Without Linux taskset, calculated slots are capped at one. With enough memory,
Linux VMs with taskset and 4, 8, 16, 32, 64 and 96 cores get 1, 1, 1, 2, 5
and 8 slots. A 96-core machine with 8 GiB free gets two slots.

Each check gets `max(1, floor(U / chosen slots))` cores. Linux taskset gives each
check a distinct CPU list from the parent's allowed CPUs, so tools such as
`nproc` and Node `os.availableParallelism()` see that share. Every child receives
`PDD_CHECK_CPUS` with the share. macOS and Linux without taskset use that hint;
custom test or build tools must read it to set their worker count. If affinity
slots outnumber CPUs, extra checks wait for a distinct CPU share.

When the one-minute load is above U, new checks wait in the queue. Running checks
keep their CPU lists when the machine shrinks; queued checks wait for free CPUs.

The default queue directory is `/tmp/pdd-full-suite-UID`, where UID is the local
user ID. It is independent of repository, HOME and agent profile. All launchers
on the machine must use the same queue directory. `PDD_SUITE_QUEUE` can select
an absolute shared directory. `PDD_VM_SUITE_LOCK` selects `VALUE.queue` when
`PDD_SUITE_QUEUE` is absent. `scripts/vm-suite-lock.sh` uses the same queue.
Autopilot keeps both selectors in its saved environment and timer. Workflow status
reports an unavailable queue with its cause.
Queue records stay outside the repository and contain no commands or test output.

## Local issue costs

`pdd autopilot status --json` prints `pdd.cost-report.v1`. Use `--all` to include
indexed repositories. This form reads local files only. Human status includes
day and week totals, outcomes, account token totals, and nearest-rank P50/P90
costs per merged issue. Multiple attempts for one repository/issue are combined.
Totals use the time each measurement was observed. Percentiles use cumulative
costs of issues whose latest outcome was merged in the selected period.

Token accounts are hashes of local config profiles, not billing identities. Codex
usage comes from cumulative rollout counts. Claude usage comes from transcript
usage, with streaming duplicates removed. Each session read is limited to 256 KiB.
Missing files, backlogs and unknown minutes appear in coverage. No message text,
credentials or monetary estimates are saved. Cached input and reasoning tokens
are subsets, not extra total tokens.

## Prompt coverage and native-only declarations

Plain Markdown prompts are checkable by default; the interpreter synthesizes and caches their Runtime interfaces on demand. For pure OS, network, database or byte-level plumbing with `0` Runtime Stories, declare YAML frontmatter at the top of the prompt (`kind: native-only` and a nonblank `reason` naming an effect the bound ports in [Ports and CLI](../skills/pdd/references/ports-and-cli.md) cannot fake). Prompts with an embedded Runtime interface block remain supported (`partial` or `native-only`). A checker reviews a native-only reason. Checks show `not run: <reason>`, with no passing result. Other selected tests can run.

Test output and saved PR evidence include prompt coverage counts. Text uses `Runtime coverage: N of M prompts checkable, K native-only` for native declarations and `Interpreter coverage` otherwise. A response with only passed and busy checks uses `Runtime coverage` and retains all coverage counts. Native-only rows retain their paths and reasons, including all-local selections. Invalid native-only scenarios retain refusal details as `not run (broken-test)` and are never uploaded.

Saved reads preserve native-only outcomes and reasons while other selected rows wait for lint or complete it. Local lint also saves coverage and omission evidence when another selected row is refused before upload. These local results can be read without authentication. Temporary lint failures retain local paths, reasons, refusals and coverage in text and JSON, and return exit 5. Named lint targets include only executable scenarios present in the uploaded archive. The files preview uses that same selection and shows native omissions with their reasons.

M includes unreadable, stale and invalid prompts. Checkable means a valid plain Markdown prompt or a valid current full or partial declaration; it does not mean that all module behavior has passed.

Runtime refusals retain a reported field pointer and rule. A supplied rule also stays visible when the field is unknown, beside the field-unknown note. If the server gives only `invalid-interface`, pdd reports any local schema findings separately. When there is no local finding, it says that the Runtime did not identify the field. No inferred cause is presented as a server diagnosis.

## Core engine

Autopilot runs the core engine. Each tick makes no AI call, so the timer runs a
tick every 10 minutes. Each job is a headless Codex, Claude, Gemini, or Antigravity process with a log
file. `--label NAME` sets the opt-in label and
`--mode auto|observe|off` the mode, on this machine only (`pdd autopilot observe`
changes `pdd.json` instead). The machine values win over `pdd.json`, and
`pdd autopilot status` says where the label and the mode come from.
`--report file|draft|off` sets where this machine's problem reports go, the same
way. `--decisions ask|decide` (or `autopilot.decisions` in `pdd.json`) sets
whether a job may ask a person about a choice. Autopilot decides when at least one
reasonable fix solves the problem and breaks nothing that people use today, and lists
it in the PR under "Choices Autopilot made", with its reason and "(changes public
behavior: …)" when users see a change. A bug fix or a small change never asks about a
choice. With `ask`, routine compatible choices of command syntax, options or data
representation are agent decisions when a safe, low-surprise choice exists. Preserve
existing APIs, defaults and behavior unless the request authorizes a change. Several
valid designs alone are not a reason to ask. A job may ask one plain question with 2
or 3 options and a recommended one (you answer with one letter) only when every
reasonable fix breaks something people use today, or, in feature mode, when the
choice actually changes product direction: whether a new feature area or capability
should exist, removing a feature, an on-purpose change to a core contract, security,
privacy, data policy, or cost; `decide`, the default for now, asks no choice
question and lists big choices marked "(big)". In both modes a blocker asks: missing
access or a secret, an issue that contradicts itself, work that cannot be done, a
change against a person's answer to an earlier question, and a change of what blocks
merges (a required check, a gate, CI policy). A bug fix may change a rule of an approved
prompt without asking; the PR lists it as "(changes approved rule: OLD -> NEW)". `--mode off` saves the mode and stops the timer of this machine. In
`observe` mode the core does everything except the merge: when all checks pass, it
posts "Autopilot would merge this PR (observe mode)" with the same evidence, keeps
the PR open and ready for review, releases the issue and adds `pdd:would-merge`, so
no machine builds it again. Remove the label to have it built again. Comments
that the core posts are redacted for secrets and cut in length.

```json
{"autopilot":{"mode":"auto","trust":[],"runs":2,"label":"pdd:autopilot",
  "quietMinutes":45,"report":"draft","maxRepairs":6,"testCommand":"npm test"}}
```

| Key | Meaning | Default |
|---|---|---|
| `runs` | The most issues in progress at the same time on one machine. It can only lower the machine's automatic slots; `pdd autopilot start --runs N` on one machine wins | automatic, from the machine guard (below) |
| `label` | The opt-in label: take only issues with this label. `--label NAME` on this machine wins over it | none: Autopilot takes no issue, and start asks for a label |
| `quietMinutes` | Minutes with nothing new after which an agent process or the checks of a PR end. There is no fixed time limit: a process runs as long as it makes something new (a new commit, a new file state, a new tool call, a new output line, or CPU use in its child processes; a repeated line, a wait or a poll is not new), and a PR waits while CI, the review or the suite still runs. At least 20 (2 ticks of the core timer) | 45 |
| `ciStuckMinutes` | Minutes that CI may stay pending with no change before the job ends | 360 |
| `maxJobHours` | Backstop floor. Each agent process (build, repair, review, suite) stops at the larger of this many hours and 4 times the longest successful process of the same kind in this repository (last 30 days), counted from its own start, whatever it does (sleep time is not counted). The job ends with no result and one alert. At 3 hours a process sends one note and goes on | 24 |
| `report` | `file`, `draft` or `off` for Runtime and PDD problem reports | `draft` |
| `reports.runtimeRepo` | Repository for Runtime problem reports, for example `promptdriven/prompt-runtime`; used when this machine can read it, else `promptdriven/pdd` with label `pdd:runtime` | none |
| `reports.runtimeOwner` | GitHub login to assign Runtime problem reports filed in `reports.runtimeRepo`. Without it, reports have no assignee | none |
| `maxRepairs` | Safety cap of repair jobs for one PR (the old key `repairs` still works). Repairs go on while they make progress: see below | 6 |
| `testCommand` | Full test command that runs on the PR head, in a clean checkout. With `package-lock.json` and listed dependencies, `npm ci --ignore-scripts` runs first | `npm test` when `package.json` has a test script |
| `modelTiering` | Opt-in worker and reviewer model routing (`true`, `false`, or `{enabled, worker, reviewer, models, efforts, overrideExplicitModel}`). Also enabled on one machine with `PDD_MODEL_TIERING=1` (with optional `PDD_WORKER_MODEL`, `PDD_REVIEWER_MODEL`, `PDD_WORKER_EFFORT`, `PDD_REVIEWER_EFFORT` overrides). Worker roles (`intake`, `build`, `repair`, `conflict`) use the worker profile (`medium` effort by default) and `review` uses the reviewer profile (`high` effort by default). Completed jobs save per-phase wall-clock durations and harness token totals in `history.jsonl` and the head evidence record | off: default agent command with no model or effort override |

**The machine guard.** Autopilot never takes over a person's machine. It may use a
share of the machine's CPU and memory, for all repositories on the machine together:
50% by default, or `pdd autopilot start --share PERCENT` on this machine. The share
counts the real limits: the CPU list and the cgroup or container limits on Linux, the
cores and the memory of the machine.

- Slots: one job counts as 2 cores and 3 GiB (an agent is light, and a full suite
  peaks near 3 GiB). The slots are the share of the cores divided by 2 and the share of
  the memory divided by 3 GiB, the lower one, at least 1 and at most 4. So at 50% an
  8 GB Mac or a 4-core, 8 GB box gets 1 job, a 10-core, 32 GB Mac gets 2, and a 64-core,
  251 GB server gets 4. These slots are for the whole machine: two repositories on the
  64-core server share its 4 jobs. `--runs N` on this machine sets the most jobs of
  this repository; `autopilot.runs` in `pdd.json` can only lower them.
- Every Autopilot process runs at the lowest priority: nice 19, on macOS the utility
  QoS, and in the Linux timer unit `CPUWeight=1` (a weight
  counts only when the CPU is busy, so an idle machine still gives Autopilot all of it;
  at a share of 100 the normal weight) and `MemoryHigh` at the share. On Linux the
  agents run on the share of the CPUs. Every job gets `PDD_CHECK_CPUS`, the worker count
  for its tests and builds.
- Before new work, each tick checks the room for the whole machine: what all Autopilot
  jobs on this machine use now (every repository) must leave room in the share for one
  more job (its jobs, its memory and its CPU), the machine needs at least 3 GiB of
  memory free and no memory pressure, and at least 10 GiB and 5% of the disk free. With
  no room, no issue is claimed, and the tick and `pdd autopilot status` say why
  (`intake held: 4 of 4 Autopilot jobs on this machine run (all repositories, 50%
  share)`). Running work goes on.
- Each tick removes worktrees that no job uses, job logs older than 14 days, and the
  oldest logs while the log folder holds more than 500 MiB.

`pdd autopilot status` shows the share, the slot math, what Autopilot uses now and the
room in one line, for example `Machine: share 50% (default) of 10 cores and 16 GiB ·
slots min(4, 5 cores ÷ 2, 8 GiB ÷ 3 GiB) = 2 → 2 (automatic) · Autopilot on this
machine now: 1 job, 0.4 GiB, 0.3 cores · memory 6.1 GiB free, pressure normal · disk
210 GiB free · load 3.2 · priority low · new work: ok`.

Each tick, without AI calls:

1. List the open issues. An issue is ready when it has no assignee, no live
   `pdd:working` claim, no `pdd:stuck`, no open issue that blocks it (a GitHub
   issue dependency or a `blocked by #N` line in its body), a trusted author and
   the opt-in label. Without a label, the tick claims no issue. The oldest ready
   issue goes first.
2. Refresh the heartbeat of this machine's claims.
3. Check each job. A job that made no progress for `quietMinutes`, failed, died or left no
   result ends. A job with a PR goes to the merge check.
4. Merge check: the PR head is the job's head, CI is green for that head, the
   full test suite passes for that head, a fresh reviewer agent that did not write
   the change gives PASS for that head (the tick posts the verdict on the PR), every
   `Runtime:` line of the PR says `PASS` or `not run (…)`, the head contains the
   current base tip, and the base check passes. Then
   `gh pr merge --merge --match-head-commit HEAD` merges it, and the issue closes.
   A red check starts one repair job on the same branch while the repairs make
   progress: each round must fix every finding of the last round and bring back no
   finding of an earlier round (new, different findings are fine); `maxRepairs` is the
   cap. The END comment names the rule that stopped the repairs. Review findings marked
   P3 never block: they go to a follow-up section in the PR body and one follow-up note
   on the issue. A review FAIL is never a PASS unless all its items are P3, and a PASS
   that lists a P1 or P2 item is a FAIL. A full suite that waits for a check slot in
   the machine's suite queue is not quiet. A
   missing or unclear `Runtime:` line is red, unless the job says no prompt
   changed. A non-zero exit of the test command is red; a failure of the suite
   runner itself (it could not start, was killed or timed out) runs the suite again
   and never uses a repair. Merges go through one **merge lane** per repository
   (the label `pdd:merge-lane` on the PR in its final step, shared by all
   machines): other green PRs wait in claim order with their reviews, and waiting
   never ends a job. In the final step Autopilot checks for an exact conflict with
   `git merge-tree`, brings the PR up to the newest base, runs the suite and CI
   again and merges. Mechanical conflicts (derived hash headers, the same insert on
   both sides, adjacent hunks, JSON keys) are fixed in the lane; other conflicts go
   to a small agent update outside the lane that does not use a repair, and that PR
   goes first when it comes back. A PR ends after its 3rd conflict. The review stays
   when the PR's changed lines stay the same; a base change near those lines, or in a
   prompt that owns one of its files, gets a short scoped check. Each job writes its
   changed files into its claim, and the next job's brief lists them. `pdd autopilot status` shows each PR's place in the lane. When the base moved, Autopilot merges the base into the
   PR branch itself and checks the new head again: the full suite and CI run again,
   and the PASS review is kept only when the merge was clean and the PR's own change
   is the same. A merge conflict starts a repair.
5. Fill free slots: claim the oldest ready issue with `pdd:working` and a claim
   comment, make a worktree and start one headless job. The job runs the same pdd
   as the tick (it goes first on the job's `PATH`, and `PDD_CLI` names it, because a
   login shell can put an older pdd first again; when the agent's shell finds another
   pdd, the job log and `pdd autopilot status` say so). `PDD_SKILLS` names the skills
   of that same pdd, and the job reads its skills from there; when the installed skills
   (`~/.agents/skills` or `~/.claude/skills`) have another version, the job log and
   status say so too. It makes one Hybrid Brownfield PR: for files owned by a prompt,
   it updates the prompt, Story, tests, and code together; for unowned files, it edits
   code and tests directly without forcing a speculative prompt. A file is owned only
   when `pdd-bindings.json` or a top-of-file `// Prompt: <path>` header (legacy
   `Generated from` headers stay readable) names its prompt (`pdd owner FILE` gives the
   same answer; prose mentions never confer ownership). When `pdd-bindings.json` on the
   base branch cannot be read, the PR is not red: its merge waits, and after the quiet
   period the run ends with one report. Config or metadata files (`package.json`, lock
   files, CI workflows) need no prompt, and protected paths (`pdd.json`, `package.json`,
   `.github/workflows/**`, `CODEOWNERS`, gate scripts) always hold for manual human
   review and merge on GitHub — Autopilot never auto-merges edits, deletions, or renames
   of protected paths. The Autopilot harness owns verification receipts, `Runtime:`,
   and `Evidence:` reporting (builders do not fabricate receipts or review verdicts;
   only the fresh blind read-only reviewer produces a review verdict). When merge-base
   `pdd.json` defines `verify.paths` (or `autopilot.strictEvidenceContract: true`),
   Autopilot enforces the full 4-check non-compensatory Evidence Contract (clean commit
   `Proved` `pdd prove` receipt, merge-base report comparison, complete frozen Story AC
   coverage, base-owned edited-test oracle, and Check 4 protected paths). Repositories
   without `verify.paths` run path-receipt checks in compatibility advisory mode
   (emitting `Not proved` with zero forged `proved` receipts while still strictly
   enforcing protected paths, real-E2E validation, blind review, full tests, and CI).

Only a real Runtime FAIL blocks a merge. A failed check is a FAIL, also when its check
has no verdict because another step had no answer. When Runtime cannot check a change
(a lint refusal, no interface, no verdict with no failed step, a scenario limit that pdd
gives no fix for), the job still ships its PR with native tests and `Runtime: not run
(STORY: REASON)`, and Autopilot files or counts one report for that cause. A value that is not
a safe integer is no such reason: pdd prints its exact Number spelling, and the job
applies that fix and checks again. During announced maintenance the job does not wait:
pdd has sent nothing yet, so the job stops it and writes `Runtime: not run (STORY:
maintenance until HH:MM UTC)` for each Story that pdd did not send, with the end time
that pdd printed. A job never cuts short a check that pdd has already sent, and never
sends a check again itself. Autopilot sends a check once more by itself, once for each
PR head, before the merge lane: a check that pdd never sent (maintenance, busy, or pdd
stopped before sending), and a sent check with no verdict and no failed check (an AI
provider failure). A check with a failed check is never sent again. While the
interpreter is in maintenance the PR waits: Autopilot reads the free `GET /v1/capacity`
again every 10 minutes, the job holds no slot and never counts as quiet, and other jobs
go on. Then Autopilot itself runs `pdd test` once for those Stories (no agent) and
rewrites the line of each one: a pass gives `Runtime: PASS (STORY, N/N checks)`, a real
FAIL goes to a repair, and no verdict keeps `Runtime: not run (STORY: …)` with one
report. The job's history keeps the agent's own lines. After 12 hours of maintenance
the line says `Runtime: not run (STORY: maintenance since HH:MM UTC)`, Autopilot files
one report, and the merge goes on. "Changed" means changed against the base (`git diff origin/BASE...HEAD`),
never since the previous PR head: a Story that a merge from the base brought in is not
changed. A job that merges the base into its branch checks that its fix is still
needed: when the PR's changed tests also pass on the code of the new merge base, the
base already holds the fix, and the job keeps only what the base does not hold.
The `Evidence:` line has a fixed form, for example
`Evidence: runtime=pass (11/11); vectors=pass (36/36); formal=bounded; tests=pass (42/42)`.
`vectors` counts the replay files that the PR changes or that read a changed scenario
file, in `node:test` tests (not steps or checks).
Autopilot keeps only the known parts, saves them in its local history and repeats
them in the merge comment. The claims must be true. A Runtime pass (`Runtime: PASS`,
`runtime=pass` or the result's runtime state) counts only when the saved `pdd test`
checks cover every changed prompt, Story and Story test at the PR head, compared with a
clean checkout of that head (files that are not committed never count; the latest check
of a Story decides; a PASS of other Stories does not count; write `Runtime: not run
(STORY: REASON)` for a native-only prompt; a changed Story with no Runtime test is red
until the PR adds its test, unless every changed prompt is native-only). A repair that only
runs `pdd test` again is read again. Autopilot also runs, at the PR head, every changed
replay (`*.vectors.test.*`) and formal (`*.formal.test.*`) file and every vector file
that names a changed scenario, if it is a `node:test` JavaScript file (other files are
listed as not run). It runs the replay and formal files apart, so each has its own
counts. A failure, a claim that its run contradicts (a vectors count too), or a positive
claim that it could not check, is red, and the merge comment shows its own counts. A
claim that Autopilot could not check (no result, a file it does not run, or a skipped
test) is red once per job; after that Autopilot never repeats it: the merge comment and
the history write that kind as `not-run (Autopilot could not check: reason)`, and
Autopilot files one report. For each PR head, Autopilot writes its own evidence record
(`logs/ISSUE-evidence-HEAD.json` in its state folder, kept after the run ends): the saved
`pdd test` checks it read, each replay and formal file's result, and the full suite. The
reviewer reads it, the merge comment names it, and the PR body gets a short "Autopilot
evidence" block from it.

With `--decisions ask`, a feature job asks one question instead of choosing when it
meets a product-direction decision that the issue does not settle (its brief lists the
other open issues by trusted authors, so it can see an open decision); it opens no PR
then. A bug or small-change job never asks about a choice. With `decide`, a choice
question is never posted: the job runs once more and decides it. The fresh review also
checks the PR's list of choices, and with `ask` it flags a product-direction choice of a
feature that the job made instead of asking (for example one option of an open decision
issue that the change touches). Such a finding
is not repaired: Autopilot asks the one question instead (in `observe` mode too), and
the PR waits for the answer. The next build and
review read the answer, so a settled choice is not asked again.

When a job needs a person's decision, Autopilot posts its one question on the issue,
adds `pdd:needs-decision` (not `pdd:stuck`) and frees the slot. Answer in a comment
(one letter is enough): at its next tick Autopilot reads a trusted person's reply,
removes `pdd:needs-decision` itself and goes on. A trusted person's removal of the
label works too. The next job gets Autopilot's own question and the
comments of trusted people after it.

When a job ends, the issue gets one comment with the cause and the log file name
and loses `pdd:working`. Comments show no absolute path, user name or host name. Nothing else waits on it. A job with no result (the agent
crashed, was signed out or hit a usage limit, or the machine restarted) only
releases the issue: no comment and no label, and its own open PR is closed with a
short note (the branch stays). Such an end counts against the issue only when it is
the first one after a job with a result on this machine; then the issue waits 24
hours before Autopilot takes it again. It is a strike of the issue only when the
next job on this machine has a result too. So an agent outage that ends two or
more jobs gives no strike. An issue that already has 2 strikes in 7 days ends as below at its
next counted end. An END starts the counts again, so a retry starts fresh. Before a
new job starts, Autopilot closes the issue's older open core PRs. When the agent
failed the task, the
issue gets `pdd:stuck`; to retry, remove `pdd:stuck`. When a Runtime or PDD
problem ended it and a report was filed, the issue is blocked by that report (a
GitHub issue dependency, or a hidden marker in the comment when the report is in
another repository) and is ready again when the report closes. If the same
problem comes back after its report closed, the issue gets `pdd:stuck`. An open PR
of an ended job stays open as a draft, with the cause in a PR comment. A PR whose
head has no CI check 10 minutes after it was opened merges on the full suite and
the fresh review alone (its merge comment says `CI: none`) only in a repository with
no PR CI: no workflow that runs on `pull_request`, `pull_request_target` or a push to
the PR branch, and no required status checks. A workflow that runs only on
`repository_dispatch`, a schedule or pushes to other branches is not PR CI. A new head
of a repository with PR CI always waits for its CI. To stop a running job, close the issue, assign it or add
`pdd:stuck`. After three jobs in a row end with no result, Autopilot pauses new
jobs on this machine for 1 hour and sends one alert ("Autopilot paused new jobs for
1 h: the agent ended 3 jobs with no result. Check sign-in and limits."). Jobs that
already run go on. After the pause, intake goes on as usual; if jobs still end with
no result, the next pause is twice as long (2, 4, then 8 hours at most), with a new
alert. An agent that stops because the AI service refused it ("Selected model is at
capacity", "Your workspace is out of credits", a usage limit, a sign-in error, a 5xx)
is an agent account problem, not the issue: the issue is released with no strike and
no cooldown, the end counts toward this pause, and the pause alert quotes the agent's
message. A job with a result, a review verdict or a merge sets the pause length back
to 1 hour. `pdd autopilot status` shows the jobs, the busy slots,
a pause and the time it ends, and the last results from local files.

Each stop where the time ran out has one owner, and only the issue owner blames
the issue:

| Owner | Example | What Autopilot does |
|---|---|---|
| pdd | Autopilot's own merge check step makes no progress (the base check cannot verify the releases, a refused merge) | Files one PDD report, keeps the PR and the claim, and tries the step again after 15 minutes, then 30, 60 and up to 8 hours. It never ends the issue. Repeats count toward the pause |
| service | GitHub answers 502 for the whole quiet period, CI stays pending with no change for `ciStuckMinutes`, the AI account is out of credits | Waits or releases the issue, with no report and no strike |
| service | GitHub Actions does not start a run for the PR head for 20 minutes (queued with no job), or fails it with a billing or spending-limit message | The PR waits for its CI with no repair. One alert and one status line name the cause ("Settings → Billing → Actions"), and no new job starts in this repository until a CI run starts again |
| machine | the agent stops answering | Releases the issue with no strike; the pause counts it |
| issue | the same command hangs again at the same head, or the suite hangs in a test that the PR changes | One strike and one short note on the issue (updated in place), then a repair with the hang details or a later try; the 3rd strike in 7 days ends the issue with `pdd:stuck` |

Agent jobs run with a hung-command watch: a command of the agent that prints
nothing and uses almost no CPU for 15 minutes (a stalled `npm install`, a test that
waits forever) is stopped alone, and the agent goes on. `pdd autopilot status`
shows each wait, its next try and each issue that cools down, with the owner. When
one issue has 3 stops owned by pdd or a service in 24 hours, Autopilot holds it (no
`pdd:stuck`) and files one report; it takes the issue again after a new pdd version
or a comment on the issue by a trusted person.

When the machine sleeps longer than `quietMinutes`, every job's no-progress clock
starts again at wake-up. A job whose claim expired or whose agent ended during the
sleep is only released (no comment, no `pdd:stuck`, and it does not count against
the issue). When
several machines run the core on one repository, each machine's GitHub share is the
`autopilot.github.share` divided by the number of machines with live claims, and a
machine over its share starts no new job. A machine that finishes an END or a release
after a pause writes nothing on an issue that another machine took over.

A Runtime problem (inside Runtime after the call: no verdict, an interpreter error,
server incompatibility, a server-side internal error) or a PDD problem (everything
that goes into Runtime: a lint, interface or binding refusal of our input, test
vectors such as a Runtime case, a scenario value limit or a vector replay; and CLI
errors, crashes, claim or merge-check tool errors) also gets one report for its owners: a PDD
problem in promptdriven/pdd with label `pdd:autopilot-report`; a Runtime problem in
`reports.runtimeRepo` when this machine can read it, else in promptdriven/pdd, with
label `pdd:runtime`. A report has no assignee unless you set `reports.runtimeOwner`,
which assigns Runtime reports filed in `reports.runtimeRepo`. One cause has one report: a
repeat adds at most one "seen again" comment per machine a day. There is no daily
cap on new reports. A filed report holds only fixed fields: the kind, component,
error code, step, versions, count and fingerprint. It never holds free-form text, code
or text from your repository. A short redacted detail stays in the local draft file
only. With `report` `draft` (the default) the
report stays on this machine until you run `pdd autopilot report send
FINGERPRINT`; with `file` Autopilot files it; with `off` nothing is saved. With
`draft` and `off` the ended issue gets
`pdd:stuck`, because there is no report to wait on. Report issues themselves are
never taken as work. A PR that says `Runtime: not run (reason)` can merge and files
no report by itself; a Runtime report comes only from a job that failed for a
Runtime cause.

### Intake cards (shadow)

`pdd autopilot start --intake shadow` turns on shadow intake cards for this
repo on this machine; `--intake active` turns on active card selection, bounded
read-only spec refinement and small-issue grouping (no opt-in label required);
`--intake off` (the default) turns intake cards off. A later start
without `--intake` keeps the saved value. In shadow mode each core tick first
checks native facts of each open issue in scope (the opt-in label, no report
issues): an assignee, an open native blocked-by link, open sub-issues, a label
`pdd:stuck`, `pdd:needs-decision`, `pdd:would-merge` or `pdd:working`, or a job of
this machine gives a native reason and no AI call. An issue whose author the core
does not trust gets `untrusted` and no AI call. For every other issue, one headless
job of this machine's agent (Codex or Claude) writes one card per issue version,
from the title, the body, the labels, the trusted person comments and the titles of
the other open issues by trusted authors. The card agent runs in an empty folder
with no tools, no write access and no GitHub token (Codex: a read-only sandbox, its
tools off and no MCP server from your Codex config; Claude: no tools, plan mode),
never with the bypass flags of build jobs. A card says ready,
improve, person, duplicate, blocked, held, fixed or elsewhere, with a reason and a
confidence. A new title, body, label, assignee, native link or comment makes a new
version. At most 2 card jobs start per tick and 2 run at once; a card job that ends
with no valid card is tried again after 6 hours, or at once for a new version.
Each card names the agent and the model. Cards live in the `intake` folder of the
core state; one file a day (UTC) lists the class changes, the "would pick" list
(ready cards, issues that unblock others first, then the oldest) and the issues
that the core really started. Shadow cards never write to GitHub and never change
which issue starts. A failure skips only that issue or that tick. After a switch to
`--intake off`, the next tick stops card jobs that still run; so do a core tick in
mode off and `pdd autopilot stop`. Trust lookups are cached for 6 hours, with at
most 40 a tick. The cards cover every
open issue in scope: unlike the core, they do not skip issues that cool down after a
no-result or whose blocker is named only in the text. `pdd autopilot intake` prints
the cards and today's changes; `--json` prints them as JSON.
See [Autopilot issue refinement](autopilot-issue-refinement.md) for the active
refiner step and for a template of an issue that is ready at the first check.


## Explain resource bindings

Run `pdd test --explain-bindings STORY` before a check to inspect the local
binding plan. Add `--json` for `pdd.binding-plans.v1` with a `plans` array.
Each plan names the test, Story, executable closure for each step, and every
resource operation. Candidates show exact selection, wrong resource name, wrong
operation, invalid lookup, or a prompt outside the boundary or dependency
closure. Exit 4 means a binding is missing; exit 0 means the local plan has no
missing binding. This command does not establish a service compatibility pass.
It reads no token, sends no request, and saves no batch or queue ticket.

A Story can narrow its executable scope with one dedicated block:

````markdown
```pdd-boundary
prompts/cli.prompt.md
```
````

Use the exact opening and closing fence lines shown above, with blank lines or
file ends beside the block. The block must be at top level, outside every other
fence, list and HTML block. Use only LF or CRLF line ends throughout the Story.
A bare CR, vertical tab, form feed, U+001C–U+001E, NEL (U+0085), U+2028 or U+2029
anywhere in the Story keeps the full closure with reason `unsupported-line-ends`
and the note `boundary not applied: unsupported line ends`. List one
repository-relative prompt path per line,
including the entry and every executable Runtime call target. Paths use letters,
digits, underscores, hyphens, dots and slashes, with no whitespace, blank lines,
empty/dot/parent components, fragments, escapes or Markdown link syntax. Each
listed member adds its resources even when no Runtime call reaches it.

Only this block can narrow the closure. Markdown links, headings and reference
definitions elsewhere never remove an edge. A Story with no block, two blocks,
an invalid path or an unreadable member keeps its full dependency closure,
including context resource requirements. The plan includes a named
`boundary-not-applied` note with the reason. A `Runtime boundary` heading without
a valid block gives `boundary not applied: use the pdd-boundary block`. Unsupported
fences, blocks inside fenced examples and uncertain HTML contexts also keep the
full closure. No partial block is applied.

With a valid block, context outside the boundary keeps its prose in the upload
but omits its Runtime interface. Files on disk do not change. An actual call
outside an applied boundary refuses locally with `binding-boundary-invalid`;
expand the block only if the Story requires that behavior. Several Stories keep
the union of their boundaries and each Story's own plan. Adding a Story cannot
remove another Story's required edge. A Story whose boundary is not applied
prevents interface removal from the combined upload. Workspace permissions still
apply to all required reads.

Fix the smallest named cause: correct the fixture resource/operation key, add
the required binding, or declare the Story boundary. Step overrides replace
same-key scenario bindings. The plan never prints fixture arguments or replies.
If the service refuses an exact fixture selected locally, the result retains
both the service report and `binding_diagnostics` with
`server-binding-disagreement`. Ask the compatibility owner to diagnose selection
before retrying. A local match never replaces a service refusal with a pass.


## Whole-product Prompt Interpreter

- `pdd --product [--parts PARTS] [--journey JOURNEY] [--max-calls N] [--no-open] [--no-wait]`
- `pdd test --journeys [JOURNEY] [--max-calls N]`

Product mode combines the selected parts' maps and starting data in one upload.
Parts without screens retain their data and planned background operations.
Each part keeps separate screen state. Cross-part navigation and background
operations follow the authored maps and product plan. Shared world/seed files
are optional. Authored project files are unchanged. A product requires at least
one screen and one selected Story/scenario. Select parts with a comma-separated
list. Journey names match complete IDs: J1 does not select J10.

The interpreter must advertise product-parts-v1. Otherwise product setup stops
before upload with an upgrade explanation. Step labels use admitted product
ownership; unnamed operations remain unlabeled. Normal Story sessions keep their
existing behavior. Reopening a product retains its original selection and world;
use --new to deliberately replace it. Unknown requests must be reconciled first.
### Inspect a call cap before paid work

Run `pdd lint --remote STORY --max-calls 25` to inspect a selected cap with 0 AI calls.
The interpreter reports each step's catalog cost and a structural test estimate.
For example, an estimate of 29 calls against cap 25 produces an advisory warning.
The cap stays 25. This does not change paid Check admission or guarantee actual
calls or completion. Resource continuations are not included in the estimate.

Text and `--json` retain source, engine and configured maximum information.
JSON rows expose the server's `call_preflight`; the result exposes
`call_preflight_context` and the separate `call_preflight_requested_cap`.
Unknown analysis stays unknown. Missing or inconsistent source, engine or cap
association cannot support a fit claim. An interpreter without
`lint-call-preflight` support refuses an explicitly selected lint cap before
submission. Ordinary remote lint without a cap remains available. Offline `pdd lint`
(without `--remote`) does not accept `--max-calls`. Reading a saved standalone lint never starts a paid check.
