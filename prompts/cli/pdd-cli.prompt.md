# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix, packageRoot)` (packageRoot defaults to this package's root) and `runPdd(argv, dependencies)`. Help, ordinary version, completion, and local inspection operate using public local files only. pdd prints no guide text: help names the installed skill and guide files and gives a short summary ([Learn PDD](command-catalog.prompt.md#learn-pdd)); the agent loads `/pdd` and its references on demand. Parse with `parseArgv` from the required argument-parser contract before reading skills; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

Use the package-root metadata version. For the catalog's ordinary version route, print only that version followed by one newline, without the package name or any prefix. Then call [skills install](skills-install.prompt.md) `findSkills` with the same arguments as setup (plus `codexHome` when `CODEX_HOME` is set), and for each agent result whose `stale` is `'older'` or whose `staleSkills` includes an older skill print the stale line below to stderr. Then call [cached release notice](release-notice.prompt.md) `checkReleaseNotice` (or injected `releaseNotice` with `releaseNoticePorts`) and print any returned update line to stderr; on interactive non-help, non-completion, non-JSON routes (`stderr.isTTY === true` or injected `releaseNotice`, excluding `project-files`, `setup`, `init`, `status`, `lint`, `prove`, `update-sync`, and `upgrade`), emit the 24-hour cached notice on stderr after command completion without changing stdout or exit code. A failure of either check prints nothing and never changes the exit code. Preserve stdout for successful values and stderr for errors. `setup` is laptop-wide (never edits repo files, never runs `setupProject` or `ignorePddFolder`, never probes coding-agent logins, and never asks Autopilot questions): first it runs a non-blocking `gh auth token` check and prints a sign-in status/hint line; next it calls [skills install](skills-install.prompt.md) `setupSkills({packageRoot, cwd, home, claudeConfigDir, env, codexHome, skillsDir})` with `home` from `env.HOME` (else `os.homedir()`) and `CLAUDE_CONFIG_DIR`. For each agent result it prints plugin-managed skip lines (and any cleaned retired skills or cleanup error) when `pluginManaged` is true, `Updated N PDD skills in ROOT: NAMES` when it updated copies, then, when found, `PDD skills found in FOLDER`, or when `stale` is set the stale line `PDD skills in FOLDER are older than pdd VERSION. DETAILS. For copies installed by pdd in user folders, run: pdd setup. For other copies, run: npx skills add promptdriven/pdd -g -a codex -a claude-code -y` (`differ from the skills of pdd VERSION` for `'differs'`; VERSION from the package metadata; leave out ` -g` when FOLDER is `<cwd>/.agents/skills`, `<cwd>/.codex/skills` or `<cwd>/.claude/skills`). `DETAILS` names every affected skill and its installed version from `staleSkills`. Omit ` DETAILS.` when there are no details. Print `npx skills add`, never `npx skills update`. Else `Installed N PDD skills to ROOT: NAMES` when it copied any. NAMES are the skill folder names, joined by `, `, in the order of `PDD_SKILL_NAMES`. Use `skill` instead of `skills` when N is 1. An agent error prints `pdd setup: the PDD skills could not be installed in ROOT (REASON).` to stderr. Next it calls [agent MCP setup](agent-mcp-setup.prompt.md) `setupAgentMcp` with `{ yes, interactive }`. Each part runs even when the other fails; exit 1 if any part failed, else 0. Per-repository setup is `pdd init`, which calls [project setup](project-setup.prompt.md) `initProject({cwd, packageRoot})` (or injected `setupProject`) and prints `Wrote the PDD block in FILE.` or `FILE already has this PDD block. No change.` plus detected stack/test command without editing `.gitignore`. Discovery and machine-output routes never write skills; normal CLI commands sync existing marker-owned user skill folders once per CLI version, and `pdd upgrade` updates a global npm or Volta `@promptdriven/pdd` installation and its user skills via [CLI upgrade](cli-upgrade.prompt.md). pdd starts Autopilot through its launcher; `product start` creates or reuses the scoped run issue and prints a `/pdd` handoff prompt. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

For setup and version reporting, use [PATH diagnostics](path-diagnostic.prompt.md). Print the returned lines to stderr. Setup uses the full report; `--version` uses its conflict-only mode while stdout remains exactly the package version and newline. Other commands, help and invalid syntax do not discover or probe PATH. A diagnostic failure must not prevent the requested command. No installer script is part of this package; setup is the supported install check.

For a `CommandInputError`, print its message once to stderr, leave stdout empty
and return its exitCode (2). Every line written to stdout or stderr ends with
one newline. Preserve other commands and their existing dispatch and effects.

A [removed name](argument-parser.prompt.md#removed-names) (`check`, `try`, `workflow`) is a `CommandInputError`, so pdd prints its one line and runs nothing: no help, PATH probe, skill check, sign-in, file read or interpreter call.

Forward `autopilot status --json` as `json:true` to the launcher, and skip settings-on-GitHub warnings for this local JSON route.

## Detailed version dispatch

The catalog owns version syntax. Ordinary version retains every existing stdout,
PATH and stale-skill behavior, with no token or network access. For admitted
`version-detailed`, read the same package-root version first, then call
[detailed version](interpreter-version.prompt.md) operation `runDetailedVersion`
exactly once with `{version,env}`. Pass the invocation env unchanged; the helper owns its address-port projection
and passes the full native environment to its credential process.
Write the returned stdout/stderr unchanged and return its exit_code. This route
runs no PATH diagnostic, skill discovery, setup or workflow. If package metadata
cannot be read, retain the ordinary unreadable-version stderr/exit1 and do not
call the helper. A helper import/call failure prints the helper's unknown result
for the already read local version and exits 0, with no raw exception text.

The existing dependencies object may additionally inject `readPackageVersion`,
`findSkills`, `interpreterVersion` (module) and `interpreterVersionPorts`.
`readPackageVersion({packageRoot})` defaults to the existing local package.json
read and returns `{ok,version}`, with false/empty version on unreadable, malformed
or missing version metadata. The CLI still rejects a blank/nonstring version.
Runtime `package.readVersion` binds that callback. Runtime `skills.findSkills`
binds the existing read-only discovery callback, wrapping its array as `{results}`
with the same result rows as setupSkills. It is called only on ordinary version.
All existing interface declarations and transport defaults remain in force.

## Setup, init, status, and upgrade

- **Lazy loading:** `src/pdd-cli.mjs` keeps startup fast by dynamically importing command implementations per route (`runtime-seam.mjs`, `project-setup.mjs`, `skills-install.mjs`, `agent-mcp-setup.mjs`, `path-diagnostic.mjs`, `completion.mjs`, `setup/cli-upgrade.mjs`, `core/status.mjs`, etc.) and reading shared helpers (`causeText`, `gitContext`, `PACKAGE_ROOT`, `resolvePddStateBase`) from `src/shared/*`. `pdd --help` and `pdd --version` never import `runtime-seam.mjs`.
- **`setup [--yes] [--skills-dir PATH]` (laptop-only):**
  - Never edits repository files (`CLAUDE.md`, `AGENTS.md`, `.gitignore`, `pdd.json`), never probes coding-agent login CLIs, and never asks Autopilot setup questions.
  - Non-blocking `gh auth token` check: when `gh` is present and returns a non-empty token, print `GitHub CLI (gh) sign-in detected (for promptdriven.ai).`; when `gh` is missing or signed out, print `GitHub CLI (gh) is not signed in — run \`gh auth login\` or visit https://promptdriven.ai/login (continuing setup).` (never blocks exit 0 and never claims a live network check).
  - Calls [skills install](skills-install.prompt.md) `setupSkills({ packageRoot, cwd, home, claudeConfigDir, env, codexHome, skillsDir })`: installs/syncs bundled skills into user global roots (`~/.agents/skills`, `~/.claude/skills` unless Claude plugin is installed, and `~/.gemini/config/skills` when Antigravity is detected), or targets ONLY `skillsDir` when `--skills-dir PATH` is provided.
  - Calls [agent MCP setup](agent-mcp-setup.prompt.md) `setupAgentMcp({ yes, interactive, ... })`: `--yes` applies previewed PDD Simulator MCP tool registrations without prompting; without `--yes` in a non-interactive terminal, MCP registration is skipped safely; in a TTY without `--yes`, previews changes and prompts once (y/N).
  - Calls [PATH diagnostics](path-diagnostic.prompt.md) with `mode: 'setup'` (quiet when clean, conflict report on stderr when shadowed).
  - Skips post-command automatic skill sync and release-notice network checks.
- **`init` (per-repo):**
  - Calls [project setup](project-setup.prompt.md) `initProject({ cwd, packageRoot })` to upsert the canonical 4-line PDD block in `CLAUDE.md` (if present) else `AGENTS.md`, detect language/test command, and never edit root `.gitignore`. Prints concise status lines and exits 0 (or prints error to stderr and exits 1).
  - Skips post-command automatic skill sync and release-notice network checks.
- **`status [PATH...] [--changed] [--json]` (offline repo overview):**
  - Calls [repo status](status.prompt.md) `runStatus({ cwd, paths, changed, json }, { stdout, stderr })`. Zero network or AI calls; skips skill sync and release-notice checks.
- **`upgrade [--main]`:**
  - Dispatches directly to [CLI upgrade](cli-upgrade.prompt.md) `runCliUpgrade({ cwd, env, main, packageRoot }, ports)` with zero Autopilot imports.
- **Release-notice exclusions:** skip the cached release-notice check on discovery, `--json`, `update-sync`, `project-files`, `setup`, `init`, and `status` routes.

## Authoring

Read the entire [Prompting guide](../../skills/pdd/references/prompting.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for native authoring/generation scope and shared local command policy. Runtime parsing/forwarding receives no guide input; applicable concrete validation and route facts remain with the required parser/catalog contracts.

Dispatch catalog dispositions `autopilot.off`, `autopilot.observe`, `autopilot.auto`, `autopilot-trust` and `autopilot-untrust` to [Autopilot settings](autopilot.prompt.md) `runAutopilot`, with action mode and the named mode, or trust/untrust and parsed names respectively. For settings writes, supply the launcher’s native `withAutopilotModeLock({cwd,env}, action, ports)` as the settings write boundary. Preserve the settings result and non-repository behavior. Print its message once to stdout on exit 0, stderr otherwise, and return its exit code. After a `mode` action with exit 0, best-effort invoke the launcher's `resetAutopilotCircuitBreaker({cwd, env, mode}, {...autopilotPorts, ...autopilotLauncherPorts})` (#3484) so `pdd autopilot auto`, `observe` and `off` clear any tripped circuit breaker and stale machine `observe` override. Autopilot workers start from the default branch on GitHub and read `pdd.json` there. So after a mode, trust or untrust action with exit 0, call [Autopilot settings on GitHub](autopilot-github.prompt.md) `publishAutopilotSettings({cwd, action, mode, names, retry}, autopilotGithubPorts)` with the parsed names and with retry the same command (`pdd autopilot MODE`, or `pdd autopilot trust|untrust NAMES`), and print its nonempty message to stdout. Tests may inject `dependencies.autopilotGithub` (the module) and `autopilotGithubPorts`. When that call throws, print `pdd.json on GitHub was not updated. To retry, run RETRY.` This line never changes the exit code, and the local write stays. Permit injected module and ports; a thrown error yields one finite diagnostic and exit 1. No Autopilot settings route starts a workflow or interpreter.

Dispatch `issue-dependency-graph` (both `pdd graph` and `pdd autopilot graph`) to injected `issueGraph` (default `src/issue-dependency-graph.mjs`) module function `runIssueGraph({cwd,repository,issue,open}, issueGraphPorts)`, mapping repository and issue from the corresponding options and open to a Boolean. Print its message to stdout on exit 0, stderr otherwise, and return its exitCode. On a throw, print a finite diagnostic and return 1.

Dispatch `lint` offline by default (`pdd lint [STORY...] [--local] [--diff [BASE]] [--json]`) directly to `src/core/lint/run-local-lint.mjs` (`runLocalLint`) with 0 AI calls, 0 network calls, and 0 batch-state writes; forward `--codex` to [Codex lint](codex-lint.prompt.md) and `--remote`, `--emit-v1`, `--write`, or `--bind-criteria` to [Runtime seam](runtime-seam.prompt.md) `lint`. Dispatch `prove` directly to [Stateless proof](prove.prompt.md) `runProve`.

Dispatch `autopilot-suite` directly to `runTestSuite` in `src/test-suite-queue.mjs` with `cwd`, `env`, `command` from `--command`, optional integer `timeout` from `--timeout`, and `{ say }` writing live queue lines to stdout; require a nonblank `--command` (exit 2 otherwise) before importing execution. For `autopilot-start`, forward `--issues` as `allowedIssues` and `--issue` as `issue` to `runAutopilotLauncher`.

Dispatch `project-files` to `runProjectFiles({cwd,json}, {stdout,stderr})`
from the files view module, with json from --json. Return its exit code. This
local route imports no Runtime client, reads no token and installs no skills.

Dispatch `file-owner` to `runOwner({cwd,paths,json}, {stdout,stderr})` from the
file owner module, with the PATH operands and json from --json. Return its exit
code. This local route imports no Runtime client, reads no token and installs no
skills.

Dispatch `update-sync` to `(runUpdateSync ?? runUpdate)({cwd,files,from,branch,all,check,write,json}, {stdout,stderr})`
from [Changed-map wrapper](update-sync.prompt.md), with FILE operands as `files`,
`--from` as `from` (when present), and
Boolean flags `--branch`, `--all`, `--check`, `--write`, and `--json`. It stays read-only
(zero `.pdd/sync/` sidecars, refusing hidden `--write` with exit 2), returns its
exit code, catches unexpected errors with one finite stderr line and exit 1,
imports no Runtime client, spawns zero AI subprocesses, and skips post-upgrade
skill sync and the cached release notice.

Dispatch autopilot-doctor through the launcher with command doctor, the normal cwd/packageRoot/env and injected launcher ports. Preserve multi-line output and exit status. Do not run the remote settings warning for doctor. Dispatch catalog disposition `autopilot.release` to the launcher with command `release`, the single issue operand in `issues`, and the normal cwd, env and launcher ports. Preserve its reply and exit status; the launcher owns locking, custody checks, durable cleanup retries and label removal.

Dispatch `autopilot-regressions` directly to
[regression detection](autopilot-regressions.prompt.md)
`runAutopilotRegressions({cwd,env,json,file}, autopilotRegressionsPorts)`, with json
true only for --json and file from --file. Allow dependencies.autopilotRegressions
and autopilotRegressionsPorts for tests. Validate the normal {exitCode,message}
reply, print once to stdout on zero and stderr otherwise. An exception prints a
finite safe failure and exits 1. Do not load the launcher or remote settings.

## Dependencies

- [Compiled Story checker](compiled-test.prompt.md): required native generation and verification context for code-target dispatch.
- [Codex readability and quality lint](codex-lint.prompt.md): required native generation and verification context for `pdd lint --codex` dispatch.
- [Repo hygiene and extensible project lint](repo-hygiene-lint.prompt.md): required native generation and verification context for default-on deterministic structural error rules and `pdd.json` `"lint"` error-severity rule enforcement.

- [Detailed version](interpreter-version.prompt.md): required generation, runtime and verification context for the single detailed-version call and result.

- [Repo status](status.prompt.md): required generation, runtime and verification context for offline `pdd status`.
- [CLI upgrade](cli-upgrade.prompt.md): required generation, runtime and verification context for `pdd upgrade [--main]`.

- [Regression detection](autopilot-regressions.prompt.md): required native generation/verification context for regression command dispatch.

- [PDD to Runtime seam](runtime-seam.prompt.md#public-contract): required generation and verification context for Runtime command and reader dispatch (`check`, `lint`, `simulate`, `jobs`, `mcp`, `contracts`, and `causeText`).

- [Shared full-suite queue](test-suite-queue.prompt.md): required execution, status and paused inactivity contract.


- [Files view](files.prompt.md): required generation/verification/testing context for read-only file inspection and exits.

- [File owner lookup](file-owner.prompt.md): required generation/verification/testing context for the read-only owner command and its exits.
- [Code-to-prompt sync](update-sync.prompt.md): required generation/verification/testing context for the offline scoped `pdd update` command and per-module derived hash sync.

- [Metrics command](metrics-command.prompt.md): required native generation/verification context for local metrics dispatch.

- [Issue dependency graph](issue-dependency-graph.prompt.md): required generation and verification context for graph dispatch.
- [Stateless proof](prove.prompt.md): required generation and verification context for `pdd prove` dispatch.

- [Autopilot launcher](autopilot-launcher.prompt.md): required native generation/verification context for launch, tick, stop, status and backlog selection. These native effects are not bound by the existing syntax transport. Launcher ports are separate from the settings module's `autopilotPorts`.

- [Autopilot settings](autopilot.prompt.md): required authoring, generation, runtime, verification and testing context for setup, Autopilot settings and `autopilot logs` subcommand dispatch.
- [Autopilot worker logs](autopilot-logs.prompt.md): required native generation, verification and testing context for read-only worker listing and live log following (`pdd autopilot logs`).
- [Autopilot settings on GitHub](autopilot-github.prompt.md): required generation, verification and testing context for the GitHub copy of the settings after the mode, trust, untrust, start and status commands.

- [Autopilot alerts](autopilot-alerts.prompt.md): required native generation, verification and testing context for alert and destination dispatch.

- [Command catalog](command-catalog.prompt.md): required authoring/generation/runtime/verification/testing context for route facts, complete help entries and `PUBLIC_HELP_TEXT` heading, closing, Learn PDD and prompting topic templates. This module renders the common help wrapper and forwards parsed values; it does not own a second help table.

- [Argument parser](argument-parser.prompt.md) is required for authoring,
  generation, runtime, verification and testing: it owns command validation and
  exact input-error messages. The CLI owns only their stream and exit handling.

- [Skills install](skills-install.prompt.md), [CLI upgrade](cli-upgrade.prompt.md), [project setup](project-setup.prompt.md), [agent MCP setup](agent-mcp-setup.prompt.md), [PATH diagnostics](path-diagnostic.prompt.md), and [cached release notice](release-notice.prompt.md): required authoring/generation/runtime/verification/testing context for laptop `pdd setup`, per-repo `pdd init`, automatic post-upgrade sync of marker-owned user skill folders, `pdd upgrade [--main]` dispatch, their streams and consent, optional PATH reporting, and the 24-hour cached CLI update notice.

Native integration uses the public APIs linked in the route sections below. Runtime bindings cover only the declared operations and supplied replies; unrelated command effects remain native.

Dispatch `autopilot-check-base` to the launcher with command check-base and both
operands in issues. Use the same reply and stream rules; no remote settings warning.

## Autopilot dispatch

For catalog dispositions `autopilot-start`, `autopilot-stop`, `autopilot-status`, `autopilot-add`, `autopilot-release` and `autopilot-check-base`, dynamically import [Autopilot launcher](autopilot-launcher.prompt.md). Call its module function `runAutopilotLauncher({command, issues, runs, checks, share, all, cwd, packageRoot, env}, ports)`: command is the disposition suffix, issues are the operands unchanged, runs is the --runs text when present, checks is the --checks text when present, share is the --share text when present (#3231), and all is true only for `autopilot status --all`. Tests may inject `dependencies.autopilotLauncher` and `autopilotLauncherPorts`. Print its {exitCode,message} once, stdout on zero and stderr otherwise, and return that code. After `autopilot-start` or `autopilot-status` without `--all` with exit 0, call [Autopilot settings on GitHub](autopilot-github.prompt.md) `checkAutopilotSettings({cwd}, autopilotGithubPorts)` and print its nonempty warning as one stderr line; a throw prints nothing. This check never writes, never changes the exit code, and start never writes `pdd.json` to GitHub. Invalid replies or exceptions produce one finite diagnostic and exit 1 without retry. Help and parsing do not load the launcher or check sign-ins. Existing admission applies only to setup and workflow-run; the launcher owns its own startup checks.

For catalog disposition `autopilot-logs`, skip post-upgrade skill sync and GitHub settings checks on this read-only local viewer. Parse `operands[0]` and `--issue` as issue selectors (`N`, `#N`, `owner/repo#N`, or GitHub issue URL), rejecting invalid selectors, conflicting parsed issue numbers or repository qualifiers, missing issue with `--follow`/`-f`, or `--follow`/`-f` combined with `--json` with exit 2 and one finite stderr line before importing execution. Dynamically delegate `{cwd, env, issue, follow, lines, json}` to `dependencies.autopilotLogs.runAutopilotLogs` when injected, else [Autopilot settings](autopilot.prompt.md) `runAutopilotSubcommand("logs", {cwd, env, issue, follow, lines, json}, {stdout, stderr, ...autopilotLogsPorts})`. When `streamed` is true, output has already been streamed to `stdout`; otherwise print nonempty `message` once to `stdout` on exit 0 and `stderr` otherwise, and return `exitCode`. An unexpected exception prints one finite safe failure and returns 1.

For catalog dispositions `autopilot-alert` and `autopilot-alerts`, dynamically import [Autopilot alerts](autopilot-alerts.prompt.md) and call its module function `runAutopilotAlerts({action, cwd, env, text, issue, kind, update}, ports)`. The action is `alert` for `autopilot-alert`, else the `set`, `test` or `clear` operand. For `alert`, `--input` must be `-`; otherwise return 2 with one line before importing the module. Read all stdin as UTF-8 `text` for `alert` and `set` only, and not for `set` with `--token-command`; when `set` reads a terminal, first print one hint line to stderr. Pass `--issue`, `--kind` and the `--update` flag unchanged, pass `--destination` as `destination` only when given, and pass `--discord-channel` as `discordChannel` and `--token-command` as `tokenCommand` only when given. Either of these two options with `test` or `clear` returns 2 with one line. Tests may inject `dependencies.autopilotAlerts` and `autopilotAlertsPorts`. Print the reply once, stdout on zero and stderr otherwise. An invalid reply or exception prints one fixed line without the error text, so a webhook URL can never reach the output, and returns 1.

## Product commands

For product-status, product-next and product-start dynamically import
[Product](product.prompt.md). Resolve the invoking cwd with the shared
`gitContext(cwd, ports)` from run records; tests may
inject this callback as `dependencies.gitContext`. Pass its `toplevel` as cwd to
`runProduct({command, run, noRun, agent, json, cwd, packageRoot, ...}, ports)`
with the parsed command and options, forwarding `through` only when `--through`
is supplied and `base` only when `--base` is supplied. A missing repository
context or resolution error is
one finite stderr diagnostic and exit 1, before any GitHub or runtime mutation.
Tests may inject the product module and its ports. Print its returned message once to stdout on
exitCode 0, stderr otherwise; return that exitCode. A missing export, malformed
reply or thrown error is one finite diagnostic and exit 1. No PATH probes,
authentication or runtime-client import belongs to these routes.

## Help contract

The required [catalog help text](command-catalog.prompt.md#help-text) owns the heading, usage line, quick-start lines, grouped summaries, focused-help note, Learn PDD lines and closing lines. Root help (`pdd`, `pdd --help`, `pdd -h`, `pdd -help`, `pdd help`) prints the heading, one empty line, `usageLine`, one empty line, `Quick start:` followed by `quickStartLines`, one empty line, each `{title, lines}` group from `PUBLIC_HELP_TEXT.groups` separated by one empty line, one empty line, `focusedHelpLines`, `learnLines` (with `PACKAGE_ROOT` substituted), one empty line, and `closingLines`. `pdd WORDS --help` prints the heading, one empty line, only the complete `PUBLIC_COMMAND_MANIFEST` entries whose form starts with `pdd WORDS` (`  <form>  <description>`), one empty line and `closingLines`, with no learn or path lines. A [quiet name](argument-parser.prompt.md#quiet-names) gets the lines of its route: `pdd sim --help` gives the `pdd simulate` lines. A removed name gets no help, also with a help flag or after `help`. Print each scoped help entry exactly as the catalog manifest lists it, including quoted heredocs.

Render `pdd help prompting` from the catalog's heading, one empty line, prompting lines, one empty line and the two path lines. Substitute `PACKAGE_ROOT` with the absolute `packageRoot` of `runPdd`, defaulting to the parent folder of `src/`, never cwd or the person's repo. Read no file to print the paths. Help is exit 0, writes nothing to stderr and is local, with no runner, network or auth effects.

## Help forms

The required [command catalog](command-catalog.prompt.md#help-forms) owns every route form, description, order and multiline approval example. Render its complete selected help entries, including quoted heredocs. The catalog also owns the Learn PDD lines and prompting topic text. This dispatcher owns only the common wrapper, package-root path substitution and route-prefix filtering above. Do not keep a separate exact help table here.

## Local jobs

For `runtime-jobs`, dynamically import the [Runtime seam](runtime-seam.prompt.md) (or an injected slots module for native tests, calling `jobs` or `runJobs`), pass the injected env/stdout/stderr to `jobs` and return its exit code. No repository, gh, fetch, skill discovery, PATH probing or workflow runner is needed. Parsing remains catalog-owned. A listing failure prints one finite cause and returns5.

## Runtime commands

For the `prompt-approve` plan, import [prompt approve](prompt-approve.prompt.md) dynamically and return `runApprove({words, cwd, ...(options["--said"] !== undefined ? {said: options["--said"]} : {})}, {stdout, stderr, env})` unchanged.

For the `runtime-check` and `runtime-try` plans, when `--issue` is set without `--codex`, or `--codex` is set without `--lint` (`pdd test --codex`), or `--codex` is combined with `--local` or `--max-calls`, print one finite stderr usage line and return 2 before any external call; when `--lint` and `--codex` are set (`pdd lint --codex [STORY...] [--issue N|FILE] [--json] [--timeout MIN]`), dynamically import [Codex readability and quality lint](codex-lint.prompt.md) (or injected `dependencies.codexLint`) and return `runCodexLint({cwd, words, issue, timeoutMinutes, json, env}, {stdout, stderr, ...codexLintPorts})` (passing `issue` only when `--issue` is set) with no PDD interpreter call. When `plan.local === 'runtime-check'` and `--reconcile` is set (`pdd test --reconcile REQUEST_ID [--json]`), delegate through `./runtime-seam.mjs` `runCheck` (passing optional injected `dependencies.runtimeCheckReconcile` as `reconcileCheckReceipt` alongside `runtimeCheckReconcilePorts`) strictly read-only so both CLI and direct seam callers share one fail-closed handler: reject extra Story operands or any option other than `--reconcile` and `--json` with one finite stderr line and exit 2 before calling runtime code; invoke `reconcileCheckReceipt({cwd, requestId: plan.options['--reconcile']}, {env, stdout, stderr, ...runtimeCheckReconcilePorts})`, print JSON when `--json` is set or human-readable output via Workflow results `formatCheckReconciliation` otherwise, and return 0 when `result.available === true` or 3 when `result.available === false` (fail-closed unknown, missing, expired or contradictory evidence). If reconciliation throws `code === 'invalid-request-id'` or explicit `exitCode === 2`, print `causeText(error.message)` to stderr and return 2; if it throws `code === 'reconciliation-unsupported'` or explicit `exitCode === 5`, print `causeText(error.message)` to stderr and return 5; any other error prints a finite stderr diagnostic and returns 3. Otherwise import the [Runtime seam](runtime-seam.prompt.md) dynamically and call `check`, `lint` (when `--lint` is set) or `simulate` with the operands (`words`), the options (including `--fresh` and `--read --details`) and cwd, plus stdout, stderr and the injected env. Before `runtime-check` Story runs (when none of `--local`, `--files`, `--explain-bindings`, `--read`, `--retry`, `--reconcile`, `--request`, `--screen`, `--emit-v1`, `--write` or `--bind-criteria` is set), emit a non-blocking `Advisory [inverted-native-only-dependency]` warning on `stderr` whenever a selected Story enters a checkable prompt (`kind !== 'native-only'`) whose dependency closure (via preflight `row.native_only`, embedded `interface.calls`, or Markdown prompt links via `promptMarkdownTargets` for plain-Markdown prompts without embedded interfaces) reaches a `kind: native-only` adapter prompt, without adding a refusal gate. Pass `cache:true` for every `runtime-check` plan (test and lint); the runtime client decides which modes use it. When `--lint` is set (outside `--files`, `--explain-bindings`, `--read`, `--retry`, `--reconcile`, `--request`, `--screen`, `--emit-v1`, `--write`, and `--bind-criteria` inspection modes) inside a Git repository (resolving the canonical Git root with a 10-second timeout), supply `onProjectLintResult` to the Runtime seam strictly for repo-wide local lint (`--local` with no Story/test operands) so the single unfiltered `lintRepoProject` scan performed during local lint captures `errors` directly without a second full-repository scan (while hosted repo-wide lint, Story-scoped operands, or runs where the seam did not invoke an unfiltered `lintRepoProject` scan always run `lintRepoProject` on the exact selected scope so `kind: native-only` adapters outside Story captures are never skipped), even when `pdd.json` is absent or defines no `"lint"` key (while safely reading non-symlink workspace `rules/lint/*.json` rule files — verifying neither `rules` nor `rules/lint` nor any matched file is a symlink, bounded size — and regular non-symlink `pdd.json` overrides via `O_NOFOLLOW` and bounded size inside `lintRepoProject`): whenever `lintRepoProject` returns errors (default-on structural error rules such as `native-only-unknown-port` or `lint-config-invalid`, or rules promoted to `"error"` in `pdd.json` or workspace-local `rules/lint/*.json`, respecting `"off"` / `"warn"` / `"error"` overrides), append those `Error: …` problems (updating JSON `problems`, `ok: false` and `exit_code: 1` when `--json` is set, or writing each error line on `stderr`) and return exit code 1; default `"warn"` rules remain advisory and never alter the exit code. Return its exit code unchanged otherwise. The runtime seam and client also own local `lint --local`, `lint --emit-v1`, `lint --bind-criteria`, and `test --screen URL --drawing PATH`; dispatch them with the same operands, options, cwd and ports, without adding runtime authentication in this router. Help for test, lint and simulate stays local. If the client throws, write `pdd stopped with an internal error. If it sent checks, read them with pdd test --read. Do not send them again.` to stderr and return 3, because checks may have been sent.

## Progress and unexpected errors

An unexpected error in a runtime or local route keeps its fixed safe line and adds `Reason: <cleaned first line of the error>` (the [cause helper](runtime-seam.prompt.md)), so the person sees what really failed.

## Try MCP transport and registration

For local `mcp`, dynamically import the [Runtime seam](runtime-seam.prompt.md) and return `mcp({cwd, env}, {stdin, stdout, stderr})` (or `mcp` / `runMcp` on an injected `mcpServer` for tests). This route performs no PATH diagnostics, skill checks or stdout chatter; stdout belongs exclusively to MCP. A startup error prints one finite cause to stderr and returns 1.

After setup's existing skills action, dynamically import [agent MCP setup](agent-mcp-setup.prompt.md) and await `setupAgentMcp({env, packageRoot}, {stdin, stdout, stderr, confirm, interactive, yes})`. Combine its failure with the existing exit status; preserve the earlier actions even if registration is declined or fails. Accept stdin (default process.stdin) and optional confirm as ports. Only registration is covered by its consent; the existing setup actions retain their behavior.

The `runPdd` entry observes the existing public module function in
`src/pdd-cli.mjs`: supply argv and capture its stdout/stderr ports and returned
exit code as the result fields below. This transport does not change that
function's signature. Invalid syntax is resolved locally before any dependency
with external effects is invoked; no runtime resource is called for that path.

Optional fields in the existing `dependencies` object may inject `setupSkills`, `setupProject`, `initProject`, `projectStatus`, `setupAgentMcp`, `cliUpgrade`, `localLint`, `proveRunner`, and `pathDiagnostic` functions. Defaults remain the public package modules; these are dependency substitutions, not argv options or new operations.

## Local contract commands

For `contracts` and `contracts-sync`, dynamically import the [Runtime seam](runtime-seam.prompt.md), allowing an injected contracts module
for native tests. Call `contracts` (or `runContracts` on an injected test module) with words [] or ['sync'], parsed options unchanged,
cwd and env/stdout/stderr; return its exit code. Do not do runtime authentication,
slot admission, skill discovery or PATH probing here. A thrown error prints one
finite local cause and returns 5. Catalog owns all syntax.

The `autopilotLauncher` Runtime resource below models only this CLI dispatch and
its `{exitCode,message}` reply. It does not model or test the launcher's native
timer, process, state, or network behavior; that behavior remains in the child
prompt's native dependency context.

Runtime `autopilotLauncher.runAutopilotLauncher` binds the injected
`dependencies.autopilotLauncher.runAutopilotLauncher` callback or the existing
default module. It forwards the constructed dispatch input, including Runtime's
closed environment projection, unchanged and returns its `{exitCode,message}`
reply.

<details>
<summary>Runtime interface</summary>

```json
{
  "kind": "partial",
  "status": "approved",
  "prose_sha256": "0592c6613e8f42e73ac872dedee53cc1f852fda2e9637068f3a7360418f86940",
  "entries": [
    {
      "operation": "runPdd",
      "input_schema": {
        "type": "object",
        "properties": {
          "argv": {
            "type": "array",
            "items": {
              "type": "string"
            }
          },
          "cwd": {
            "type": "string"
          },
          "env": {
            "type": "object",
            "properties": {
              "HOME": {
                "type": "string"
              },
              "PATH": {
                "type": "string"
              },
              "CODEX_HOME": {
                "type": "string"
              },
              "CLAUDE_CONFIG_DIR": {
                "type": "string"
              },
              "PDD_RUNTIME_URL": {
                "type": "string"
              }
            },
            "required": [],
            "additionalProperties": false
          },
          "packageRoot": {
            "type": "string"
          }
        },
        "required": [
          "argv"
        ],
        "additionalProperties": false
      },
      "result_schema": {
        "type": "object",
        "properties": {
          "exit_code": {
            "type": "integer"
          },
          "stdout": {
            "type": "string"
          },
          "stderr": {
            "type": "string"
          }
        },
        "required": [
          "exit_code",
          "stdout",
          "stderr"
        ],
        "additionalProperties": false
      },
      "errors": []
    }
  ],
  "calls": [
    {
      "operation": "runDetailedVersion",
      "target": "prompts/cli/interpreter-version.prompt.md",
      "target_operation": "runDetailedVersion",
      "max_calls": 1
    }
  ],
  "resources": [
    {
      "name": "dispatch",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "prove",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "ref": {
                "type": "string"
              },
              "test": {
                "type": "string"
              },
              "expect": {
                "type": "string"
              },
              "cwd": {
                "type": "string"
              },
              "timeoutMinutes": {
                "type": "integer",
                "minimum": 1,
                "maximum": 120
              }
            },
            "required": [
              "ref",
              "test",
              "expect",
              "cwd"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exitCode": {
                "type": "integer"
              },
              "message": {
                "type": "string"
              }
            },
            "required": [
              "exitCode",
              "message"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "requestUptake",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "requestId": {
                "type": "string"
              },
              "summary": {
                "type": "string"
              },
              "cwd": {
                "type": "string"
              }
            },
            "required": [
              "requestId",
              "summary",
              "cwd"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exitCode": {
                "type": "integer"
              },
              "message": {
                "type": "string"
              }
            },
            "required": [
              "exitCode",
              "message"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "startRun",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "input": {
                "type": "object",
                "properties": {
                  "name": {
                    "type": "string"
                  },
                  "issue": {
                    "type": "string"
                  },
                  "agent": {
                    "type": "string",
                    "enum": [
                      "codex",
                      "claude"
                    ]
                  },
                  "cwd": {
                    "type": "string"
                  },
                  "packageRoot": {
                    "type": "string"
                  },
                  "base": {
                    "type": "string"
                  },
                  "adoptCorpus": {
                    "type": "string"
                  },
                  "draft": {
                    "type": "boolean"
                  },
                  "origin": {
                    "type": "string",
                    "enum": [
                      "manual",
                      "autopilot",
                      "unknown"
                    ]
                  },
                  "decisionId": {
                    "type": "string"
                  },
                  "outcome": {
                    "type": "string",
                    "enum": [
                      "code",
                      "prompt-only"
                    ]
                  }
                },
                "required": [
                  "name",
                  "issue",
                  "agent",
                  "cwd",
                  "packageRoot"
                ],
                "additionalProperties": false
              },
              "env": {
                "type": "object",
                "properties": {
                  "HOME": {
                    "type": "string"
                  },
                  "PATH": {
                    "type": "string"
                  },
                  "CODEX_HOME": {
                    "type": "string"
                  },
                  "CLAUDE_CONFIG_DIR": {
                    "type": "string"
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "input",
              "env"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exitCode": {
                "type": "integer"
              },
              "message": {
                "type": "string"
              }
            },
            "required": [
              "exitCode",
              "message"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "agents",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "checkWorkflowAgents",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "env": {
                "type": "object",
                "properties": {
                  "HOME": {
                    "type": "string"
                  },
                  "PATH": {
                    "type": "string"
                  },
                  "CODEX_HOME": {
                    "type": "string"
                  },
                  "CLAUDE_CONFIG_DIR": {
                    "type": "string"
                  }
                },
                "required": [],
                "additionalProperties": false
              },
              "requested": {
                "type": "string",
                "enum": [
                  "codex",
                  "claude"
                ]
              }
            },
            "required": [
              "cwd",
              "env"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": {
                "type": "boolean"
              },
              "agent": {
                "oneOf": [
                  {
                    "type": "string",
                    "enum": [
                      "codex",
                      "claude",
                      "gemini",
                      "agy"
                    ]
                  },
                  {
                    "type": "null"
                  }
                ]
              },
              "message": {
                "type": "string"
              },
              "hint": {
                "type": "string"
              }
            },
            "required": [
              "ok",
              "agent",
              "message"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "diagnostics",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "pathDiagnostic",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "packageRoot": {
                "type": "string"
              },
              "cwd": {
                "type": "string"
              },
              "env": {
                "type": "object",
                "properties": {
                  "HOME": {
                    "type": "string"
                  },
                  "PATH": {
                    "type": "string"
                  },
                  "CODEX_HOME": {
                    "type": "string"
                  },
                  "CLAUDE_CONFIG_DIR": {
                    "type": "string"
                  }
                },
                "required": [],
                "additionalProperties": false
              },
              "mode": {
                "type": "string",
                "enum": [
                  "setup",
                  "version",
                  "workflow"
                ]
              }
            },
            "required": [
              "packageRoot",
              "cwd",
              "env",
              "mode"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "lines": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              }
            },
            "required": [
              "lines"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "setup",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "setupSkills",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "packageRoot": {
                "type": "string"
              },
              "cwd": {
                "type": "string"
              },
              "home": {
                "type": "string"
              },
              "claudeConfigDir": {
                "type": "string"
              }
            },
            "required": [
              "packageRoot",
              "cwd",
              "home"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "results": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "agent": {
                      "type": "string"
                    },
                    "root": {
                      "type": "string"
                    },
                    "found": {
                      "oneOf": [
                        {
                          "type": "string"
                        },
                        {
                          "type": "null"
                        }
                      ]
                    },
                    "stale": {
                      "oneOf": [
                        {
                          "type": "string"
                        },
                        {
                          "type": "null"
                        }
                      ]
                    },
                    "staleSkills": {
                      "type": "array",
                      "items": {
                        "type": "object",
                        "properties": {
                          "name": {
                            "type": "string"
                          },
                          "version": {
                            "oneOf": [
                              {
                                "type": "string"
                              },
                              {
                                "type": "null"
                              }
                            ]
                          },
                          "state": {
                            "type": "string",
                            "enum": [
                              "older",
                              "differs"
                            ]
                          }
                        },
                        "required": [
                          "name",
                          "version",
                          "state"
                        ],
                        "additionalProperties": false
                      }
                    },
                    "installed": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    },
                    "updated": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    }
                  },
                  "required": [
                    "agent",
                    "root",
                    "found",
                    "stale",
                    "installed",
                    "updated"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "results"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "setupProject",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "cwd": {
                "type": "string"
              },
              "packageRoot": {
                "type": "string"
              }
            },
            "required": [
              "cwd",
              "packageRoot"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "file": {
                "type": "string"
              },
              "changed": {
                "type": "boolean"
              }
            },
            "required": [
              "file",
              "changed"
            ],
            "additionalProperties": false
          }
        },
        {
          "name": "setupAgentMcp",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "env": {
                "type": "object",
                "properties": {
                  "HOME": {
                    "type": "string"
                  },
                  "PATH": {
                    "type": "string"
                  },
                  "CODEX_HOME": {
                    "type": "string"
                  },
                  "CLAUDE_CONFIG_DIR": {
                    "type": "string"
                  }
                },
                "required": [],
                "additionalProperties": false
              },
              "packageRoot": {
                "type": "string"
              }
            },
            "required": [
              "env",
              "packageRoot"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exitCode": {
                "type": "integer"
              }
            },
            "required": [
              "exitCode"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "package",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "readVersion",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "packageRoot": {
                "type": "string"
              }
            },
            "required": [
              "packageRoot"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "ok": {
                "type": "boolean"
              },
              "version": {
                "type": "string"
              }
            },
            "required": [
              "ok",
              "version"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "skills",
      "kind": "port",
      "access": "read",
      "operations": [
        {
          "name": "findSkills",
          "access": "read",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "packageRoot": {
                "type": "string"
              },
              "cwd": {
                "type": "string"
              },
              "home": {
                "type": "string"
              },
              "claudeConfigDir": {
                "type": "string"
              },
              "codexHome": {
                "type": "string"
              }
            },
            "required": [
              "packageRoot",
              "cwd",
              "home"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "results": {
                "type": "array",
                "items": {
                  "type": "object",
                  "properties": {
                    "agent": {
                      "type": "string"
                    },
                    "root": {
                      "type": "string"
                    },
                    "found": {
                      "oneOf": [
                        {
                          "type": "string"
                        },
                        {
                          "type": "null"
                        }
                      ]
                    },
                    "stale": {
                      "oneOf": [
                        {
                          "type": "string"
                        },
                        {
                          "type": "null"
                        }
                      ]
                    },
                    "staleSkills": {
                      "type": "array",
                      "items": {
                        "type": "object",
                        "properties": {
                          "name": {
                            "type": "string"
                          },
                          "version": {
                            "oneOf": [
                              {
                                "type": "string"
                              },
                              {
                                "type": "null"
                              }
                            ]
                          },
                          "state": {
                            "type": "string",
                            "enum": [
                              "older",
                              "differs"
                            ]
                          }
                        },
                        "required": [
                          "name",
                          "version",
                          "state"
                        ],
                        "additionalProperties": false
                      }
                    },
                    "installed": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    },
                    "updated": {
                      "type": "array",
                      "items": {
                        "type": "string"
                      }
                    }
                  },
                  "required": [
                    "agent",
                    "root",
                    "found",
                    "stale",
                    "installed",
                    "updated"
                  ],
                  "additionalProperties": false
                }
              }
            },
            "required": [
              "results"
            ],
            "additionalProperties": false
          }
        }
      ]
    },
    {
      "name": "autopilotLauncher",
      "kind": "port",
      "access": "write",
      "operations": [
        {
          "name": "runAutopilotLauncher",
          "access": "write",
          "arguments_schema": {
            "type": "object",
            "properties": {
              "command": {
                "type": "string",
                "enum": [
                  "doctor",
                  "audit",
                  "check-base",
                  "start",
                  "stop",
                  "status",
                  "add",
                  "release",
                  "report",
                  "intake"
                ]
              },
              "issues": {
                "type": "array",
                "items": {
                  "type": "string"
                }
              },
              "runs": {
                "type": "string"
              },
              "checks": {
                "type": "string"
              },
              "engine": {
                "type": "string"
              },
              "label": {
                "type": "string"
              },
              "share": {
                "type": "string"
              },
              "agent": {
                "type": "string"
              },
              "pool": {
                "type": "string"
              },
              "autoUpdate": {
                "type": "string"
              },
              "mode": {
                "type": "string"
              },
              "report": {
                "type": "string"
              },
              "decisions": {
                "type": "string"
              },
              "intake": {
                "type": "string"
              },
              "all": {
                "type": "boolean"
              },
              "json": {
                "type": "boolean"
              },
              "cwd": {
                "type": "string"
              },
              "packageRoot": {
                "type": "string"
              },
              "env": {
                "type": "object",
                "properties": {
                  "HOME": {
                    "type": "string"
                  },
                  "PATH": {
                    "type": "string"
                  },
                  "CODEX_HOME": {
                    "type": "string"
                  },
                  "CLAUDE_CONFIG_DIR": {
                    "type": "string"
                  },
                  "GEMINI_CLI_HOME": {
                    "type": "string"
                  },
                  "ANTIGRAVITY_APP_DATA_DIR": {
                    "type": "string"
                  },
                  "PDD_RUNTIME_URL": {
                    "type": "string"
                  }
                },
                "required": [],
                "additionalProperties": false
              }
            },
            "required": [
              "command",
              "issues",
              "cwd",
              "packageRoot",
              "env"
            ],
            "additionalProperties": false
          },
          "result_schema": {
            "type": "object",
            "properties": {
              "exitCode": {
                "type": "integer"
              },
              "message": {
                "type": "string"
              }
            },
            "required": [
              "exitCode",
              "message"
            ],
            "additionalProperties": false
          }
        }
      ]
    }
  ],
  "limits": {
    "max_steps": 10,
    "max_model_calls": 12
  },
  "conventions": []
}
```

</details>

Dispatch each metrics route to [metrics command](metrics-command.prompt.md) with the selected arguments, current cwd, stdout and stderr; return its exit code without an interpreter call. Forward optional origin, decisionId and outcome metadata alongside existing base, adoptCorpus and draft fields to startRun; these observations grant no workflow authority.

Dispatch `autopilot-report` to the Autopilot launcher with command report and its operands in issues, with the same reply validation and stream rules and no remote settings warning. Dispatch `autopilot-intake` the same way with command intake and `--json` as `json`. For `autopilot-start`, also pass `--engine` as `engine` and `--label` as `label`, `--mode` as `mode`, `--report` as `report`, `--decisions` as `decisions`, `--intake` as `intake`, `--agent` as `agent`, `--pool` as `pool` and `--auto-update` as `autoUpdate` when given.

Route `pdd test --target code` to the local compiled Story checker without contacting the interpreter. Reject other test options except `--json` for this route.

Dispatch local `accounts` by dynamically importing [Cloud accounts CLI](accounts-cli.prompt.md) (`accountsCli ?? await import('./accounts-cli.mjs')`) and calling `runAccountsCli({commandId: plan.commandId, operands: [...plan.operands], options: {...plan.options}, cwd, env, stdin}, accountsPorts)`. When `result.message` is non-empty, write it to `stdout` on exit 0 or `stderr` otherwise; keep `stdout` silent when `result.message === ''` (such as `pdd accounts sync --quiet`).

Before command dispatch on normal CLI invocations (excluding `help`, `version`, `version-detailed`, `completion`, `workflow-list`, `project-files`, `file-owner`, `status`, `init`, `update-sync`, `mcp`, `setup`, `upgrade`, `autopilot-logs`, `accounts` with `--quiet`, and any command with `--json` in `plan.options` or `argv`), call [skills install](skills-install.prompt.md) `syncOwnedUserSkills({packageRoot, home: env.HOME || homedir(), claudeConfigDir: env.CLAUDE_CONFIG_DIR, codexHome: env.CODEX_HOME, stateRoot: env.PDD_STATE_DIR, env})` (or injected `syncOwnedUserSkills`) fail-open (#3424). When `updated.length > 0` and `stderr?.isTTY === true`, write `Updated PDD skills to VERSION (FOLDERS).` to `stderr`. Dispatch local `upgrade` by dynamically importing [CLI upgrade](cli-upgrade.prompt.md) (`cliUpgrade ?? await import('./setup/cli-upgrade.mjs')`) and calling `runCliUpgrade({env, stdout, stderr, main: plan.options['--main'] === true, packageRoot, home: env.HOME || homedir(), cwd}, cliUpgradePorts)`; return its `exitCode` without running the post-command release notice.
