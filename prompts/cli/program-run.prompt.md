# Direct prompt programs

Own src/program-run.mjs; export module function
`runProgram({file, args, root, env, flags}, ports)` returning an exit code. Run an entry
prompt as a CLI or typed operation with fake outside resources and no Story.
Preserve existing simulate, Try and test behavior. Screen/HTTP launches belong to
C's src/program-app.mjs. Before B's CLI or typed classification, lazily load
that module and call its exported `appKind({file,root},ports)`; it returns
`'screen'`, `'http'` or null. A non-null result delegates to its exported
`runApp({file,root,env,flags},ports)` and awaits its exit code; asynchronous rejection uses the same plain pdd error
handling as local failures, never a raw Node stack. Pass the parsed
pdd prefix flags with every file-valued option (including data) resolved to a
full path from invocation cwd; program suffix words never become pdd flags.
Null or a missing module continues B's CLI/typed classification. No entry means
context, not an executable: exit2 with `pdd: FILE has no entry, so it cannot run.`,
explain it is context for other prompts, and list actual repository prompts that
use it. Discover callers locally; never invent callers. More than one CLI entry,
or CLI plus typed entries, refuses2 before authentication. One file is one kind;
C owns screen/HTTP ambiguity and its shared lint warning. Preserve appKind FIRST
and never duplicate C's HTTP or app-map inference. C owns screen/HTTP classification; B must not duplicate it using
schema titles or app-map guesses. For deterministic tests, ports.programApp may
supply that module's public exports instead of loading it; both paths use the
same classification precedence and arguments. Never edit C's module. Messages
never tell people to add an adapter or cli convention.

## Entry and input

A CLI entry has cli conventions on both schemas; its first heading supplies a command name only for the shell. Apply Try's safe
name, reserved-name and launcher protections only when opening that shell. With ARGS,
a heading with spaces or punctuation must not prevent execution;
call once with exact argv and read piped UTF-8 only if stdin is declared. Never
consume undeclared stdin, including an enclosing shell read loop. Preserve exact
stdout/stderr and return program exit_code 0–255 except reserved 125.
With no ARGS create the safe real-command launcher locally. Only terminal stdin
opens the injected shell(shell, env) port (native interactive shell by default).
Without a terminal, print a correctly shell-quoted `export PATH="...:$PATH"`
line with `# then: NAME --help` on stdout and exit0: no child, authentication,
source lint, session or network. The shim invokes the CLI once, even with zero
words. It carries selected initial data without reapplying fresh/backup on every
command. In a terminal, pdd-owned informational lines go to stderr prefixed
`pdd:`: NAME is a command in this shell; type exit to leave, the data directory,
and prompt behavior, not tested code. On shell exit report saved world.json,
restore caller PATH and return the shell exit code. Quiet hides those lines.
Invoking that launcher with zero words calls the CLI once with empty argv; it
never opens another shell. Prefix fresh/data options select the shell's data
before its commands run, including that zero-word invocation.
Never open a browser for CLI or typed input.

For typed input, --name value fills input_schema fields. Parse integers, finite
numbers and true/false booleans by schema; strings retain exact value. Repeated
array flags append items in order with item types; repeated scalar flags refuse.
With two or more entries the first word selects an operation; with one it is
implicit, and an arbitrary word is not consumed as an operation. --input JSON or
--input @file supplies the whole object; resolve that file from the invocation
current folder, even when the repository root differs. Piped JSON supplies it only when no flags
were given. Whole-input and field flags cannot mix; stdin never merges with flags.
Whole JSON supports nested objects and nullable fields. Validate all admitted
schema constraints locally before authentication, lint, session creation or calls.
--help after FILE prints schema usage, exits0, sends nothing. Invalid input prints
that usage and a plain reason, exits2, sends nothing. With no ARGS and no nonempty piped JSON, print usage and exit2 even if the schema
accepts {}; do this before authentication. Explicit piped `{}` is supplied input.
Usage distinguishes required flags from optional bracketed flags and shows schema
types and enum alternatives. Successful result prints JSON,
one line when piped; a declared error exits1.

## Saved data and reuse

Use [program data](program-data.prompt.md) for initial and confirmed world and
last-record persistence, and [program sessions](program-session.prompt.md) for
source identity, automatic replacement and confirmed answer reuse. Show-data
prints JSON without executing a call; fresh invalidates cached answers.

## Transport, budget and failures

Use runtime-client's direct transport and runtime-preflight's entry graph capture.
No Story or synthetic scenario is uploaded. Outside resources stay fake; absent
bindings use interpreter defaults, never real files/databases/services.
Entry worst case is: 1 plus each declared call's
max_calls times (child worst case +1). Default per-call cap is min(worst case,100). Explicit --max-calls accepts1–1000
and changes only this per-call cap. Always send max_calls and boolean fresh in
the call request, including fresh:false. The interpreter enforces insufficient
caps; never refuse locally because cap is below worst case. Cycles/indeterminate estimates
refuse clearly. Do not add a local refusal merely because the default worst case
exceeds100; the interpreter enforces its limits. Above20 print `pdd: may use up to N AI calls.` before dispatch.
Session allowance must permit per-call cap and interpreter remaining admission.
After a run stderr has one `pdd: N AI calls · T s` summary; cached results say
`cached · 0 AI calls`; reached drafts add DRAFT; a new session adds
`prompt behavior, not tested code`. Every pdd-owned stderr line starts `pdd:` (traceback frames and usage/error
continuations may remain indented). Quiet hides all informational status, warnings,
accounting and fake-call summaries, never program stderr or useful failure reasons. Accounting uses receipts, never another call.
For supplied call_chain print `Traceback (prompt calls, most recent call last):`, then
ordered `prompt, operation OP` lines, appending `(call I of at most M)` for nested
frames' call_index/max_calls. Finish `Error CODE: MESSAGE`. Never invent frames.
Use the final direct-call receipt: result.output is the CLI/typed result and
result.world is the exact confirmed after-world. Never overwrite it from a later
state GET. This module validates the terminal receipt before writing its world,
acknowledging its pending request or emitting output/last-run metadata. report.verdict
is required and must be passed, failed or refused; never infer it from outer state.
Outer passed confirms transport completion and may contain any of those semantic
verdicts. An outer non-passed terminal state must not contradict the semantic
outcome or turn into success; successful output requires outer passed and semantic
passed together. A missing/invalid verdict or contradictory receipt
exits125 with a plain interpreter-failure reason and same-ID read hint: no result
stdout (including --json), no world replacement, no cacheable receipt and no pending
clear. Keep the accepted ID for GET-only recovery until a valid confirmed outcome.
A valid report.verdict passed yields CLI exit_code or typed0; failed with a
declared report.error yields1; refused yields125 even when report.error exists.
Preserve result.refusals and report.error code/message, fix/hint/field and graph
cap evidence. Render `pdd: refused, N AI calls.` with supplied evidence and Fix
advice. report.replayed:true displays cached and0 AI calls. Report accounting uses
confirmed calls/seconds and includes report_url as details. Preserve call_chain
frames in order and disclose omitted frames using call_chain_total; never fabricate
frames or lose the report link. Declared errors exit1. Interpreter refusals, exhausted calls, ten-minute limits,
invalid results, transport failures and unknown outcomes exit125 with plain reason
and recovery/fix hint. Ctrl-C exits130, retains accepted ID and prints
`pdd --read ID FILE`; this prefix option uses GET only, never resends a call.
Lost POST replies recover that same ID without duplicate execution.

## Structured output and fake calls

Prefix --json prints one JSON receipt, with output, outside_calls, call_chain,
session_id, report_url, exit_code and ai_calls, preserving provided metadata.
Never mix raw program stdout into that JSON. Normal CLI mode preserves program
stdout/stderr byte for byte; typed mode prints result.output as JSON. When supplied,
report.outside_calls is rendered on stderr as `pdd: fake calls (nothing real was
called):` and one prefixed summary/level line per call. Quiet hides these lines;
JSON and last-run.json retain complete supplied outside-call records. Metadata
never claims an outside service was really called. Retain server error code and
field, include supplied Fix or setup/size/cap recovery advice. session-busy exits125.
Confirmed session-stopped/session-unknown admission errors may replace the session
with confirmed world and execute once; uncertain POST outcomes always use same-ID
GET recovery and never repeat the uncertain operation.

## Dependencies

- [Program data](program-data.prompt.md): required native generation/verification/testing persisted-world policy.
- [Program sessions](program-session.prompt.md): required native generation/verification/testing no-Story session lifecycle.

- [Runtime client](runtime-client.prompt.md): required native generation,
  verification/testing transport, authentication, receipts and injected ports.
- [Runtime preflight](runtime-preflight.prompt.md): required native generation,
  verification/testing capture, interface/schema and privacy primitives.
- [Try doors](try-doors.prompt.md): required native generation, verification/testing
  safe launchers, names and CLI stream conventions only. Preserve Story behavior.

## Runtime interface

This native orchestrator binds filesystem, shell, streams and transport through
ports. Deterministic fake-interpreter tests invoke the existing public runPdd;
there is no model-executed Runtime operation for native process launching.
