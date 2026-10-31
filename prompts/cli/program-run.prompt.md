# Direct prompt programs

Own src/program-run.mjs; export module function
`runProgram({file, args, root, env, flags}, ports)` returning an exit code. Run an entry
prompt as a CLI or typed operation with fake outside resources and no Story.
Preserve existing simulate, Try and test behavior. Screen/HTTP launches belong to
other owners. Detect screen apps via a selected app map and named HTTP entries
via their input_schema title. Lazily import ./program-app.mjs and return
runApp({file,root,env,flags},ports). If that module is missing, print exactly
`Screen apps and HTTP entries open this way in the next release; for now run pdd simulate STORY.`
and exit2. Never treat a named HTTP or mapped screen entry as a typed operation. Messages never tell people to add an adapter or cli convention.

## Entry and input

A CLI entry has cli conventions on both schemas; its first heading supplies a safe
command name, retaining Try's reserved names and launcher protections. With ARGS,
call once with exact argv and read piped UTF-8 only if stdin is declared. Never
consume undeclared stdin, including an enclosing shell read loop. Preserve exact
stdout/stderr and return program exit_code 0–255 except reserved 125.
With no ARGS open the injected shell(shell, env) port (native interactive shell by
default) with a real command launcher on PATH, without executing the program.
First stdout line: `Answers come from prompts on the PDD interpreter, not installed code.`
Then say `NAME works only in this shell; exit removes its PATH context. Another terminal: export PATH=...`
with correctly shell-quoted launcher directory. Exit restores the caller's PATH.
Never open a browser for CLI or typed input.

For typed input, --name value fills input_schema fields. Parse integers, finite
numbers and true/false booleans by schema; strings retain exact value. Repeated
array flags append items in order with item types; repeated scalar flags refuse.
With two or more entries the first word selects an operation; with one it is
implicit, and an arbitrary word is not consumed as an operation. --input JSON or
--input @file supplies the whole object. Piped JSON supplies it only when no flags
were given. Whole-input and field flags cannot mix; stdin never merges with flags.
Whole JSON supports nested objects and nullable fields. Validate all admitted
schema constraints locally before authentication, lint, session creation or calls.
--help after FILE prints schema usage, exits0, sends nothing. Invalid input prints
that usage and a plain reason, exits2, sends nothing. Successful result prints JSON,
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
Default per-call cap is entry worst case, at most100: 1 plus each declared call's
max_calls times (child worst case +1). Explicit --max-calls accepts1–1000. A cap
below worst case refuses at0 calls before dispatch. Cycles/indeterminate estimates
refuse clearly. Above20 print `pdd: may use up to N AI calls.` before dispatch.
Session allowance must permit per-call cap and interpreter remaining admission.
After a run stderr has one `pdd: N AI calls · T s` summary; cached results say
`cached · 0 AI calls`; reached drafts add DRAFT; a new session adds
`prompt behavior, not tested code`. Quiet hides summary only, never program stderr
or failure reasons. Accounting uses receipts, never another call.
For supplied call_chain print `Traceback (prompt calls, most recent last):`, then
ordered `prompt, operation OP` lines, appending `(call I of at most M)` for nested
frames' call_index/max_calls. Finish `Error CODE: MESSAGE`. Never invent frames.
Declared errors exit1. Interpreter refusals, exhausted calls, ten-minute limits,
invalid results, transport failures and unknown outcomes exit125 with plain reason
and recovery/fix hint. Ctrl-C exits130, retains accepted ID and prints
`pdd --read ID FILE`; this prefix option uses GET only, never resends a call.
Lost POST replies recover that same ID without duplicate execution.

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
