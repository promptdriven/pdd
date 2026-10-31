# Local authoring-kit CLI

Own `src/pdd-cli.mjs`; export `renderHelp(prefix)` and `runPdd(argv, dependencies)`. Help, version, completion and recipe discovery operate using public local files only. pdd prints no guide; the agent loads the pdd-prompting skill. Parse with `parseArgv` from the required argument-parser contract before reading skills or workflows; unsupported input gets a finite stderr diagnostic/exit2 and no private fallback.

Use the package-root metadata version. For `--version`, print only that version followed by one newline, without the package name or any prefix. Then call [skills install](skills-install.prompt.md) `findSkills` with the same arguments as setup, and for each agent result whose `stale` is `'older'` print the stale line below to stderr (0.1.8 tester: no command showed that the installed skills were older than pdd). A failure of that check prints nothing and never changes the exit code. `workflow list` reads the bundled workflow areas only; it does not start work. Preserve stdout for successful values and stderr for errors. `setup` does two things, in this order. First it calls [skills install](skills-install.prompt.md) `setupSkills({packageRoot, cwd, home, claudeConfigDir})` with home from the HOME environment value (else `os.homedir()`) and `CLAUDE_CONFIG_DIR`. For each agent result it prints `Updated N PDD skills in ROOT: NAMES` when it updated copies, then, when found, `PDD skills found in FOLDER`, or when `stale` is set the stale line `PDD skills in FOLDER are older than pdd VERSION. To update them, run: npx skills add promptdriven/pdd -g -a codex -a claude-code -y` (`differ from the skills of pdd VERSION` for `'differs'`; VERSION from the package metadata; leave out ` -g` when FOLDER is `<cwd>/.agents/skills` or `<cwd>/.claude/skills`). Print this `npx skills add` command, never `npx skills update`: update changes only skills that `npx skills add` recorded, and says "No global skills tracked" for copies that pdd setup or a person made (0.1.8 tester). `add` replaces any copy, and later `update` works too, else `Installed N PDD skills to ROOT: NAMES` when it copied any. NAMES are the skill folder names, joined by `, `, in the order of `PDD_SKILL_NAMES`. Use `skill` instead of `skills` when N is 1. An agent error prints `pdd setup: the PDD skills could not be installed in ROOT (REASON).` to stderr. Then it calls [project setup](project-setup.prompt.md) `setupProject({cwd, packageRoot})` and prints `Wrote the PDD block in FILE.` or `FILE already has this PDD block. No change.`; its error prints `pdd setup: ` and the message to stderr. Each part runs even when the other fails. Exit 1 if any part failed, else 0. No other command installs skills. pdd starts chats through the workflow runner; `product start` may delegate to a normal feature run. Keep imports and injection defaults self-contained, with no private transport/backend dependency.

For setup, version reporting and workflow startup, use [PATH diagnostics](path-diagnostic.prompt.md). Print the returned lines to stderr. Setup uses the full report; `--version` uses its conflict-only mode while stdout remains exactly the package version and newline; the `workflow-run` plan uses its compact shadowing warning before dispatch. Other commands, help and invalid syntax do not discover or probe PATH. A diagnostic failure must not prevent the requested command. No installer script is part of this package; setup is the supported install check.

For a `CommandInputError`, print its message once to stderr, leave stdout empty
and return its exitCode (2). Every line written to stdout or stderr ends with
one newline. Preserve other commands and their existing dispatch and effects.

A [removed name](argument-parser.prompt.md#removed-names) is a `CommandInputError`, so pdd prints its one line and runs nothing: no help, PATH probe, skill check, sign-in, file read or interpreter call.

## Authoring

Read the entire [Prompting guide](../../docs/prompting-guide.md) before authoring prompts or Stories. Follow [public alpha boundary](public-boundary.prompt.md) for native authoring/generation scope and shared local command policy. Runtime parsing/forwarding receives no guide input; applicable concrete validation and route facts remain with the required parser/catalog contracts.

## Dependencies

- [Command catalog](command-catalog.prompt.md): required authoring/generation/runtime/verification/testing context for route facts and complete help entries. This module renders the common help wrapper and forwards parsed values; it does not own a second help table.

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

The runner routes (run, done, ask, approve, changes, cancel, status, open) call the matching export of `src/workflow-runner.mjs` (startRun, stepDone, askPerson, approveRun, changeRun, cancelRun, runStatus, openRun) with the parsed values, cwd and packageRoot. For startRun, pass `base` only when `--base` was given, using its text unchanged; the runner owns branch validation and selection. For startRun, pass `adoptCorpus` only when `--adopt-corpus` was given, using its text unchanged; the runner owns adoption policy. For approveRun, pass `said: options["--said"]` only when supplied, without trimming or joining. Forward the literal `-` marker unchanged; dispatch never reads stdin or interprets person words. For status, pass `all`, `cancelled` and `json` only when their flag is given. Tests may inject the runner module. Print the returned message once: stdout when exitCode is 0, stderr otherwise. Return the exitCode. A missing export, an invalid reply or a thrown error prints one finite line and returns 1; never retry.

For catalog route `workflow.request-uptake`, require nonblank `--summary` before importing or invoking the runner; missing summary returns 2 with one finite diagnostic. Reuse normal parser validation for missing/extra operands, duplicate/blank options and help/completion. Call the actual module function `acknowledgeRequest({requestId: operands[0], summary: options['--summary'], cwd}, ports)` on the existing injectable `workflowRunner`, using the workflow stream/error handling above. Derive command hints from the catalog prefix by stable id; dispatch on the catalog's stable disposition, never a second public verb. `bin/pdd.mjs` remains a thin entry point. Interpreter resource `dispatch.requestUptake` binds this same injected module function, not native journal execution.

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

The first help line is exactly `PDD: prompt-driven development for your coding agent.` Root help (`pdd`, `pdd --help`, `pdd -h`, `pdd help`) prints that line, one empty line, every line of the [catalog help forms](command-catalog.prompt.md#help-forms), in order, one empty line, then the three closing lines below. `pdd WORDS --help` prints the same layout with only the complete catalog help entries whose form starts with `pdd WORDS`. A [quiet name](argument-parser.prompt.md#quiet-names) gets the lines of its route: `pdd sim --help` gives the `pdd simulate` lines and `pdd workflow start --help` the `pdd workflow run` line. A removed name gets no help, also with a help flag or after `help`. Print each help-form line exactly as the catalog lists it, never a made-up `Usage:` line. The three closing lines are exactly:

```text
Open Codex or Claude as usual and call a PDD skill: $pdd-feature in Codex, /pdd-feature in Claude Code (also pdd-bug, pdd-small-change, pdd-prompting).
workflow run opens the first area chat in Herdr session pdd and exits. The person approves each area; after the last step pdd pushes the branch and opens a real PR.
pdd never merges.
```

(`run` is the [NAMES](command-catalog.prompt.md#names) word. Codex calls a skill with `$name`, Claude Code with `/name`.) Help is exit 0 and local, with no runner, network or auth effects.


## Help forms

The required [command catalog](command-catalog.prompt.md#help-forms) owns every route form, description, order and multiline approval example. Render its complete selected help entries, including quoted heredocs. This dispatcher owns only the common wrapper and route-prefix filtering above. Do not keep a separate exact help table here.

## Local jobs

For `runtime-jobs`, dynamically import [runtime slots](runtime-slots.prompt.md), pass the injected env/stdout/stderr to runJobs and return its exit code. Permit an injected slots module for native tests. No repository, gh, fetch, skill discovery, PATH probing or workflow runner is needed. Parsing remains catalog-owned. A listing failure prints one finite cause and returns5.

## Runtime commands

For the `prompt-approve` plan, import [prompt approve](prompt-approve.prompt.md) dynamically and return `runApprove({words, cwd, ...(options["--said"] !== undefined ? {said: options["--said"]} : {})}, {stdout, stderr, env})` unchanged.

For the `runtime-check` and `runtime-try` plans, import the [runtime client](runtime-client.prompt.md) dynamically and call `runCheck` or `runTry` with the operands, the options and cwd, plus stdout, stderr and the injected env. Return its exit code unchanged. The runtime client also owns local `lint --local` and `test --screen URL --drawing PATH`; dispatch them with the same operands, options, cwd and ports, without adding runtime authentication in this router. Help for test, lint and simulate stays local. If the client throws, write `pdd stopped with an internal error. If it sent checks, read them with pdd test --read. Do not send them again.` to stderr and return 3, because checks may have been sent.

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
  "status": "draft",
  "prose_sha256": "74e9a7c4d2e4184e28ce04be1f7761282ef7e29e2764d956b188f1b4b85a0f34",
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
  }, {
    "name": "requestUptake", "access": "write",
    "arguments_schema": {"type": "object", "properties": {
      "requestId": {"type": "string"}, "summary": {"type": "string"}, "cwd": {"type": "string"}},
      "required": ["requestId", "summary", "cwd"], "additionalProperties": false},
    "result_schema": {"type": "object", "properties": {
      "exitCode": {"type": "integer"}, "message": {"type": "string"}},
      "required": ["exitCode", "message"], "additionalProperties": false}
  }]}],
  "limits": {"max_steps": 2, "max_model_calls": 3},
  "conventions": []
}
```

</details>
