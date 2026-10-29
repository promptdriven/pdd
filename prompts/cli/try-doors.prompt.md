# Use a Try session from a terminal or HTTP client

Own src/try-doors.mjs. Provide one generic adapter around the owner's saved Try. Preserve argv strings, program
streams and saved session identity. Do not interpret commands, execute a project binary, or generate project logic.

`openCli(context, test, sessionId, options)` selects the first distinct CLI entry used by the Story's tests; refuse
if there are multiple distinct CLI entries. Both input and result schemas carry the cli convention. A safe program
name comes from the prompt's first H1 (optionally backticked): letters/digits/dot/underscore/hyphen, starting with
a letter, up to 64 characters; pdd, node, gh and git are reserved because putting their shims first on PATH would shadow pdd’s own tools. Record schema, original test and Story criteria in the private workspace session record. Install the shared named launcher through [Try launcher](try-launcher.prompt.md); its compatibility repo-bin link points to the same executable. Never traverse a symlink
or overwrite a file not marked as a PDD Try launcher. Ignore .pdd/try/ via the repository's local Git exclude file
so future source captures contain no adapters or evidence. Before writing private command data, refuse any tracked
.pdd/try paths and verify that the mailbox path is actually Git-ignored (a repository negation must not
make it visible). No token or browser capability enters the launcher, descriptor, argv, output, mailbox or receipts.
The installed adapter path and descriptor path are separate argv data to constant launcher JavaScript;
quotes, newlines or Unicode in installation/workspace paths cannot become executable JavaScript.

### Workspace-only CLI state

All agent command data stays under ignored private .pdd/try directories: descriptor, queue, mailbox,
last result and quiet usage receipt. Never persist a token there. Only setup and the owner relay may use
home files, gh or network; a sandboxed command uses none of them. Old global descriptors require setup again.
A global --save-last pointer is written at setup, never read or changed by the shim.
The [mailbox](try-mailbox.prompt.md) owns the workspace request/reply exchange and owner relay.

Commands for one session wait for the current command before dispatch or invalidating last-result evidence.
Keep a private process lock through receipt persistence, release it on normal failure/cancellation, and bound
waiting to60seconds. Print a short waiting line on stderr even for agents/pipes. An expired or abandoned wait
returns125 with no dispatch and names its lock path; never steal a potentially active lock. Forward
cancellation through queue and runtime waits. Runtime-confirmed busy handling is owned by the runtime client.

Print its absolute path and distinct examples from the Story's
argv steps. Every shell word in an example is quoted safely. Keep the owner mailbox relay open until Ctrl-C. --shell runs the relay while it launches the
user's bash or zsh (otherwise /bin/sh) with the inherited PATH and terminal, waits, and returns its status.

`runShim(descriptorPath, argv, ports={})` loads the private descriptor and passes argv unchanged. Read stdin only when the input schema declares a stdin property. Otherwise do not open, iterate or consume the stream, even when piped or never closed, so an enclosing shell read loop retains its input. For declared piped stdin, read at most 1 MiB as UTF-8; forward even an empty pipe. Terminal stdin is
omitted unless required, when it is an empty string. --help is passed to the prompt like any argv. Invoke
through the mailbox by default for non-terminal stderr, requiring only workspace access. A terminal stderr
uses the original direct runDoorCall route; PDD_TRY_TRANSPORT=mailbox or direct explicitly selects a route.
Direct mode reauthenticates outside the sandbox with the original global state and identity checks. Require stdout/stderr strings and integer exit_code in 0..255 except 125.
Preserve program stdout byte-for-byte and return its exit code. Preserve program stderr exactly. Save usage privately to usage.json; only with PDD_TRY_USAGE=1 append a separated short Try usage line on stderr; wrapper accounting must never enter stdout. If program stderr lacks a final newline, separate the usage line with one. Store known usage on refused calls too, unknown when unconfirmed; never replay for accounting. Reserve 125 for wrapper failures: stderr starts with
`pdd try:` followed by a plain reason; stdout remains empty. Never print credentials, stacks or internal URLs. For EPERM/EACCES file failures, name the blocked path
and explain that the CLI needs workspace access. For denied network access, keep stdout empty, return125,
and print the runtime client's Codex/Claude network guidance.
Record the last confirmed command/result with the original test identity in private state, independently of
whether the program exited successfully. Unknown execution must not leave an older command eligible for Save.

`saveLast(context)` reads the last confirmed invocation for this repository, verifies the current gh login and
original session identity, and appends the input/result as one exact recorded case in the original test file
through saveDoorCase. This records an observation; it does not approve a prompt or validate that the answer is
correct. Repeated Save for the same action is a no-op. Refuse missing/unknown evidence or a changed Story/test
identity, and keep earlier checks and all unrelated test bytes. Tie the recording to the original step's criterion.
Print the target file and new step name. No model call is needed.

## Dependencies

- [Try launcher](try-launcher.prompt.md): required generation/runtime context for names, collisions and cwd repository selection.
- [Mailbox](try-mailbox.prompt.md): required generation/runtime context for sandbox-safe command exchange and relay.
- [Runtime client](runtime-client.prompt.md): required generation/runtime context for authentication, state, owner
  calls, confirmed results and safe original-test append.
- [Runtime preflight](runtime-preflight.prompt.md): required generation/runtime context for CLI interfaces.
- [Prompting guide](../../docs/prompting-guide.md): required authoring context.

Launcher execution must work inside projects declaring CommonJS or ESM. Use an absolute Node executable and
syntax-neutral dynamic import rather than relying on extensionless-file module detection. The launcher must use the absolute Node executable without resolving a project program as Node.
Refuse reserved dependency names case-insensitively before writing a launcher.

A reused Try retains its uploaded prompt bytes. Before overwriting a launcher or making a command, compare
local entry prompt bytes with the original private descriptor (and with the prompt hashes captured at session
creation). Refuse changed prompts with a --new hint; never relabel old runtime output with a new prompt hash.
An older session without pinned source hashes needs --new before becoming a CLI.
Keep the reported before/after world privately alongside the last result. Like the hosted Try Save, the appended
case records the last command's observed output; it does not rewrite the original scenario's initial_world or
preceding steps. For a nonempty saved world, print a short reminder to review the saved-data setup before replay.

At CLI startup, read authenticated owner model metadata once (GET /v1/try/ID/model, no model calls) and print current session usage on stderr; model calls.cap/remaining are authoritative. If metadata is unavailable, show unknown and keep existing CLI startup behavior. Retain the known cap in the private descriptor so each confirmed call can show session used/remaining. Do not treat usage as a new budget or reset it.

Usage normalization and formatting are owned by [runtime output](runtime-output.prompt.md#try-usage), required generation/runtime context.

## Progress
A command on the Try can take many seconds. When stderr is a terminal and the call takes more than 2 s, the launcher prints `pdd try: running <name> on the Try…` on stderr. With a pipe or an agent it prints nothing extra, so the program's output stays exact.
