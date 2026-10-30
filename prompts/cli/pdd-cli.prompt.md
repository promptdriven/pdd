# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, completion and recipe discovery operate using public local files only. pdd prints no guide; the agent loads the pdd-prompting skill. Parse with `parseArgv` from the required argument-parser contract before reading skills or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

Use the package-root metadata version. For `--version`, print only that version followed by one newline, without the package name or any prefix. Then call [skills install](skills-install.prompt.md) `findSkills` with the same arguments as setup, and for each agent result whose `stale` is `'older'` print the stale line below to stderr (0.1.8 tester: no command showed that the installed skills were older than pdd). A failure of that check prints nothing and never changes the exit code. `workflow list` reads the bundled workflow areas only; it does not start work. Preserve stdout for successful values and stderr for errors. `setup` does two things, in this order. First it calls [skills install](skills-install.prompt.md) `setupSkills({packageRoot, cwd, home, claudeConfigDir})` with home from the HOME environment value (else `os.homedir()`) and `CLAUDE_CONFIG_DIR`. For each agent result it prints `Updated N PDD skills in ROOT: NAMES` when it updated copies, then, when found, `PDD skills found in FOLDER`, or when `stale` is set the stale line `PDD skills in FOLDER are older than pdd VERSION. To update them, run: npx skills add promptdriven/pdd#alpha -g -a codex -a claude-code -y` (`differ from the skills of pdd VERSION` for `'differs'`; VERSION from the package metadata; leave out ` -g` when FOLDER is `<cwd>/.agents/skills` or `<cwd>/.claude/skills`). Print this `npx skills add` command, never `npx skills update`: update changes only skills that `npx skills add` recorded, and says "No global skills tracked" for copies that pdd setup or a person made (0.1.8 tester). `add` replaces any copy, and later `update` works too, else `Installed N PDD skills to ROOT: NAMES` when it copied any. NAMES are the skill folder names, joined by `, `, in the order of `PDD_SKILL_NAMES`. Use `skill` instead of `skills` when N is 1. An agent error prints `pdd setup: the PDD skills could not be installed in ROOT (REASON).` to stderr. Then it calls [project setup](project-setup.prompt.md) `setupProject({cwd, packageRoot})` and prints `Wrote the PDD block in FILE.` or `FILE already has this PDD block. No change.`; its error prints `pdd setup: ` and the message to stderr. Each part runs even when the other fails. Exit 1 if any part failed, else 0. No other command installs skills. pdd starts chats through the workflow runner; `product start` may delegate to a normal feature run. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

For setup, version reporting and workflow startup, use [PATH diagnostics](path-diagnostic.prompt.md). Print the returned lines to stderr. Setup uses the full report; `--version` uses its conflict-only mode while stdout remains exactly the package version and newline; the `workflow-run` plan uses its compact shadowing warning before dispatch. Other commands, help and invalid syntax do not discover or probe PATH. A diagnostic failure must not prevent the requested command. No installer script is part of this package; setup is the supported install check.

For a `CommandInputError`, print its message once to stderr, leave stdout empty
and return its exitCode (2). Every line written to stdout or stderr ends with
one newline. Preserve other commands and their existing dispatch and effects.

When the plan has a `notice` ([former names](argument-parser.prompt.md#former-names)), print it once to stderr before any other line, help and PATH lines included, then run the plan as usual. Never print it to stdout, so `--json` output stays exact. A `CommandInputError` has no notice.

## Authoring

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for native authoring/generation scope and shared local command policy. Runtime parsing/forwarding receives no guide input; applicable concrete validation and route facts remain with the required parser/catalog contracts.

## Dependencies

- [Contract commands](contracts.prompt.md): required generation and verification
  context for local list/sync dispatch; the syntax-only Runtime entry does not
  bind these native effects.

- [Runtime slots](runtime-slots.prompt.md): required generation/verification context for local jobs dispatch. The existing syntax-only Runtime entry does not bind its native filesystem effects.

- [Old-code proof](workflow-prove.prompt.md): required authoring/generation/runtime/verification context for the explicit prove dispatch and injected callback contract.
- [Argument parser](argument-parser.prompt.md) is required for authoring,
  generation, runtime, verification and testing: it owns command validation and
  exact input-error messages. The CLI owns only their stream and exit handling.

Native authoring/generation uses existing imported project APIs and their owner contracts linked in the route sections below. Those links are the native integration context for the existing commands; the Runtime prove transport uses only its declared callback plus the pure parser/catalog facts, and does not simulate unrelated command effects.

## Workflow dispatch

The runner routes (run, done, ask, approve, changes, cancel, status, open) call the matching export of `src/workflow-runner.mjs` (startRun, stepDone, askPerson, approveRun, changeRun, cancelRun, runStatus, openRun) with the parsed values, cwd and packageRoot. For startRun, pass `base` only when `--base` was given, using its text unchanged; the runner owns branch validation and selection. For approveRun, pass `said: options["--said"]` only when supplied, without trimming or joining. For status, pass `all`, `cancelled` and `json` only when their flag is given. Tests may inject the runner module. Print the returned message once: stdout when exitCode is 0, stderr otherwise. Return the exitCode. A missing export, an invalid reply or a thrown error prints one finite line and returns 1; never retry.

workflow list uses `listWorkflowAreas({packageRoot,cwd,home})` (home from the HOME environment value) and `formatWorkflowList` from [workflow areas](workflow-areas.prompt.md). A read failure returns 1. Local help/version/skill/completion do not import the runner.

## Product commands

For product-status, product-next and product-start dynamically import
[Product](product.prompt.md). Resolve the invoking cwd with the shared
`gitContext(cwd, ports)` from [run records](workflow-runs.prompt.md); tests may
inject this callback as `dependencies.gitContext`. Pass its `toplevel` as cwd to
`runProduct({command, run, noRun, agent, json, cwd, packageRoot}, ports)` with the
parsed command and options. A missing repository context or resolution error is
one finite stderr diagnostic and exit 1, before any GitHub or runtime mutation.
Tests may inject the product module and its ports. Print its returned message once to stdout on
exitCode 0, stderr otherwise; return that exitCode. A missing export, malformed
reply or thrown error is one finite diagnostic and exit 1. No PATH probes,
authentication or runtime-client import belongs to these routes.

## Help contract

The first help line is exactly `PDD: prompt-driven development for your coding agent.` Root help (`pdd`, `pdd --help`, `pdd -h`, `pdd help`) prints that line, one empty line, every line of the [help forms](#help-forms) below, in order, one empty line, then the three closing lines below. `pdd WORDS --help` prints the same layout with only the help-form lines whose form starts with `pdd WORDS`. For a [former name](argument-parser.prompt.md#former-names) these are the lines of its new route: `pdd check --help` gives the `pdd test` lines (not the `pdd lint` lines), `pdd check --lint --help` gives the `pdd lint` lines, `pdd try --help` the `pdd simulate` lines and `pdd workflow start --help` the `pdd workflow run` line. `pdd sim --help` gives the `pdd simulate` lines with no notice. Print each help-form line exactly as the catalog lists it, never a made-up `Usage:` line. The three closing lines are exactly:

```text
Open Codex or Claude as usual and call a PDD skill: $pdd-feature in Codex, /pdd-feature in Claude Code (also pdd-bug, pdd-small-change, pdd-prompting).
workflow run opens the first area chat in Herdr session pdd and exits. The person approves each area; after the last step pdd pushes the branch and opens a real PR.
pdd never merges.
```

(`start` is the [NAMES](command-catalog.prompt.md#names) word. Codex calls a skill with `$name`, Claude Code with `/name`.) Help is exit 0 and local, with no runner, network or auth effects.


## Help forms

Help prints exactly these lines, in this order. Each line is two spaces, the form, two spaces and its description. The [catalog](command-catalog.prompt.md) routes own them; the first words after `pdd` are the route prefix.

```text
  pdd product status [--json]  Count Stories by part and slice from the product plan; no interpreter calls.
  pdd product next  Show ready planned runs and their start commands; no interpreter calls.
  pdd product start RUN [--no-run] [--agent codex|claude]  Create or reuse the run issue and start a normal feature run; --no-run only prepares the issue. No interpreter calls.
  pdd workflow run NAME ISSUE [--agent codex|claude] [--base BRANCH]  Start the first area chat for a GitHub issue in Herdr and exit; --base selects an existing origin branch (default: repository default); pdd later pushes the issue branch and opens a real PR.
  pdd workflow prove ISSUE --test COMMAND --expect TEXT  Run committed changed tests on the fetched base branch merge-base and committed head with a 120-second limit per phase; save a non-gating report.
  pdd workflow done STEP [--summary TEXT]  For the agent in a run worktree: record a step and print what to do next.
  pdd workflow evidence ISSUE --summary FILE  Record source-verified saved check JSON without rerunning steps, gates or publication.
  pdd workflow ask QUESTION  For the agent in a run worktree: show the person that the chat waits for their answer.
  pdd workflow approve [ISSUE] [--said WORDS]  Record the person's chat approval for the gate and all its draft prompts, or use terminal/native area-chat approval; strict mode requires a person terminal.
  pdd workflow changes ISSUE TEXT  Send a change request to the same area chat; the gate stays open.
  pdd workflow cancel ISSUE  Cancel the run and close its Herdr tabs; keep the worktree and branch.
  pdd workflow status [ISSUE] [--all] [--cancelled] [--json]  Show this repo's runs, or one run with its area, gate, chat and PRs. --all (or outside a repo): every run on this machine, people-waiting first.
  pdd workflow view ISSUE  Read-only review of gates, approvals, files, PRs and Simulator links; never start or resume a chat.
  pdd workflow open ISSUE  Focus or attach the current area chat; resume it if its session ended.
  pdd  Show local commands.
  pdd --help  Show local commands.
  pdd -h  Show local commands.
  pdd help  Show local commands.
  pdd --version  Show this package version.
  pdd completion bash|zsh  Print local shell completion.
  pdd workflow list [--json]  List the bundled workflows with their areas and gates.
  pdd test [STORY...] [--json] [--details] [--timeout MIN] [--max-calls N]  Check stories on the PDD interpreter with your gh login: sends the named Stories (every Story when you name none) and their dependencies, waits for every check (no limit in a terminal, at most 90 s for an agent; --timeout MIN sets the limit) with a progress line every 30 s, then prints one table with report links. Defaults to 12 calls per step, at least 18 and at most 1000; --max-calls accepts 1 to 1000.
  pdd test --read [BATCH|CALL_ID] [--json] [--timeout MIN]  Read saved results; a normal Check held for lint may continue its original checks. Other reads send no work.
  pdd test --retry BATCH [--json] [--details] [--timeout MIN]  Retry only confirmed unstarted checks from a saved batch, with the same source and call caps; preserve completed and uncertain runs.
  pdd test --fill-hash  Fill prose_sha256 of draft runtime interfaces; no network.
  pdd test --files [STORY...] [--app-map PATH]  List the exact selected upload files and byte sizes; no network. --app-map selects the Simulator's app map.
  pdd test --screen URL --drawing PATH [--json]  Compare a real page with its drawing at the drawing viewport in installed headless Chrome/Chromium; no AI or interpreter calls.
  pdd lint [STORY...] [--json] [--timeout MIN]  Print local SVG layout warnings, then the PDD interpreter lint (0 AI calls) on selected Stories and their dependencies; sends no checks.
  pdd lint --local [STORY...] [--json]  Check linked SVG layout parts locally with warning diagnostics and 0 AI/network calls.
  pdd approve PROMPT [--said WORDS]  Approve one prompt with the person's chat words in easy mode, or show its interface/text changes and ask terminal y/N; strict mode requires a person terminal.
  pdd simulate [STORY] [--max-calls N] [--tab call|screen|terminal|world] [--app-map PATH] [--new] [--no-open] [--no-wait] [--agent NAME]  Open the Story in the PDD Simulator: make a link on the PDD interpreter with your gh login and open it in your browser; it ends in 24 hours. Short form: pdd sim. A new simulation defaults to 400 calls; --max-calls accepts 1 to 1000. With terminal stdout or explicit --agent, it stays running to connect your own agent; otherwise it reads saved cases once and returns. --agent selects a configured name or a default Codex, Claude or Gemini; --no-wait skips the bridge. In a terminal it adds each test saved in the Simulator to the story's test file.
  pdd simulate [STORY] --cli [--shell] [--max-calls N] [--new]  Run your program in your terminal through a Simulator session; prints a PATH line, or opens a shell with --shell.
  pdd simulate [STORY] --serve [PORT] [--max-calls N] [--new]  Serve real HTTP requests through your Simulator session on localhost (default port 8080).
  pdd simulate --save-last  Save the last terminal command and its output in the original Story test file.
  pdd simulate --stop [STORY]  Stop the open Simulator link of a story.
  pdd jobs  List active and waiting interpreter jobs on this machine without contacting the interpreter.
  pdd contracts  List shared records, their users and Stories stale since their last check; local working files only.
  pdd contracts sync [--write]  Show proposed changes for moving schema copies to references; apply only with --write. No interpreter calls.
  pdd mcp  Serve the current repository’s Try tools over stdio MCP.
  pdd setup  Install the PDD skills for Codex and Claude if they are missing, and add the short PDD block to CLAUDE.md, else AGENTS.md. Offer detected Codex, Claude Code and Gemini MCP registrations after showing exact config changes and one y/N question. A second run changes nothing.
```

## Local jobs

For `runtime-jobs`, dynamically import [runtime slots](runtime-slots.prompt.md), pass the injected env/stdout/stderr to runJobs and return its exit code. Permit an injected slots module for native tests. No repository, gh, fetch, skill discovery, PATH probing or workflow runner is needed. Parsing remains catalog-owned. A listing failure prints one finite cause and returns5.

## Runtime commands

For the `prompt-approve` plan, import [prompt approve](prompt-approve.prompt.md) dynamically and return `runApprove({words, cwd, ...(options["--said"] !== undefined ? {said: options["--said"]} : {})}, {stdout, stderr, env})` unchanged.

For the `runtime-check` and `runtime-try` plans, import the [runtime client](runtime-client.prompt.md) dynamically and call `runCheck` or `runTry` with the operands, the options and cwd, plus stdout, stderr and the injected env. Return its exit code unchanged. The runtime client also owns local `check --lint --local` and `check --screen URL --drawing PATH`; dispatch them with the same operands, options, cwd and ports, without adding runtime authentication in this router. Help for check and try stays local. If the client throws, write `pdd stopped with an internal error. If it sent checks, read them with pdd check --read. Do not send them again.` to stderr and return 3, because checks may have been sent.

For `workflow-view`, dynamically import [read-only review](workflow-view.prompt.md) and call `viewRun({ref: operands[0], cwd})`. Print the result once (stdout on success, stderr on failure) and return its exit code. This route must not import the workflow runner, inspect Herdr, or execute PATH version probes.

Route workflow-evidence to workflow runner recordEvidence with issue ref and required --summary file path; missing summary is a CLI input error. It records evidence only, not workflow progression.


For `workflow-prove`, require both `--test` and `--expect` before importing or invoking any effectful dependency; missing options print exactly `pdd workflow prove requires nonblank --test and --expect.` to stderr and return 2. Dynamically import `src/workflow-prove.mjs` (or injected `dependencies.workflowProve`) and call module function `proveRun({ref: operands[0], test: options.test, expect: options.expect, cwd}, provePorts)`. Preserve quoted strings unchanged. Print its `{exitCode,message}` once, stdout on zero and stderr otherwise, and return its exitCode. Reuse workflow-route safe unexpected-error handling, without retry. `provePorts` is the injected operation ports object; defaults belong to the prove module. Help/discovery never loads it. This explicit route is the sole supplied-command execution exception; it grants no hosted-runtime/auth/token authority.

## Progress and unexpected errors

Pass the runner a `say` port that writes one line to stderr, so slow workflow steps show progress while stdout keeps the result. An unexpected error in a runner, runtime or view route keeps its fixed safe line and adds `Reason: <cleaned first line of the error>` (the [cause helper](runtime-output.prompt.md#progress-and-causes)), so the person sees what really failed.

## Try MCP transport and registration

For local `mcp`, dynamically import [Try MCP](try-mcp.prompt.md) and return `runMcp({cwd, env}, {stdin, stdout, stderr})`. Accept injected `mcpServer` for tests. This route performs no PATH diagnostics, skill checks or stdout chatter; stdout belongs exclusively to MCP. A startup error prints one finite cause to stderr and returns 1.

After setup's existing skills and project-block actions, dynamically import [agent MCP setup](agent-mcp-setup.prompt.md) and await `setupAgentMcp({env, packageRoot}, {stdin, stdout, stderr, confirm})`. Combine its failure with the existing exit status; preserve the earlier actions even if registration is declined or fails. Accept stdin (default process.stdin) and optional confirm as ports. Only registration is covered by its consent; the existing setup actions retain their behavior.

Runtime resource `dispatch.prove` binds the actual injected `workflowProve.proveRun` module function; call it once only for valid prove input. Resource arguments preserve the forwarded native input; the module's operation ports remain its dependency injection. Optional Runtime input `cwd` binds existing `dependencies.cwd` (default `.` in this transport); it is not a new argv option. Other effects are not simulated by this entry.

The `runPdd` entry observes the existing public module function in
`src/pdd-cli.mjs`: supply argv and capture its stdout/stderr ports and returned
exit code as the result fields below. This transport does not change that
function's signature. Invalid syntax is resolved locally before any dependency
with external effects is invoked; no runtime resource is called for that path.

## Local contract commands

For `contracts` and `contracts-sync`, dynamically import
[contract commands](contracts.prompt.md), allowing an injected contracts module
for native tests. Call runContracts with words [] or ['sync'], parsed options unchanged,
cwd and env/stdout/stderr; return its exit code. Do not do runtime authentication,
slot admission, skill discovery or PATH probing here. A thrown error prints one
finite local cause and returns 5. Catalog owns all syntax.

<details>
<summary>Runtime interface</summary>

```json
{
  "status": "approved",
  "prose_sha256": "fb2d5a0397734c8cbc83e45917a5cde4ab80e28222ba824fb9650201ca2d0b8a",
  "entries": [{
    "operation": "runPdd",
    "input_schema": {
      "type": "object",
      "properties": {"argv": {"type": "array", "items": {"type": "string"}}, "cwd": {"type": "string"}},
      "required": ["argv"], "additionalProperties": false
    },
    "result_schema": {
      "type": "object",
      "properties": {
        "exit_code": {"type": "integer"},
        "stdout": {"type": "string"}, "stderr": {"type": "string"}
      },
      "required": ["exit_code", "stdout", "stderr"], "additionalProperties": false
    },
    "errors": []
  }],
  "calls": [],
  "resources": [{"name": "dispatch", "kind": "port", "access": "write", "operations": [{
    "name": "prove", "access": "write",
    "arguments_schema": {"type": "object", "properties": {
      "ref": {"type": "string"}, "test": {"type": "string"},
      "expect": {"type": "string"}, "cwd": {"type": "string"}},
      "required": ["ref", "test", "expect", "cwd"], "additionalProperties": false},
    "result_schema": {"type": "object", "properties": {
      "exitCode": {"type": "integer"}, "message": {"type": "string"}},
      "required": ["exitCode", "message"], "additionalProperties": false}
  }]}],
  "limits": {"max_steps": 2, "max_model_calls": 3},
  "conventions": []
}
```

</details>
