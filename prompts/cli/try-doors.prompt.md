# Use a Try session from a terminal or HTTP client

Own src/try-doors.mjs. Provide one generic adapter around the owner's saved Try. Preserve argv strings, program
streams and saved session identity. Do not interpret commands, execute a project binary, or generate project logic.

`openCli(context, test, sessionId, options)` selects the first distinct CLI entry used by the Story's tests; refuse
if there are multiple distinct CLI entries. Both input and result schemas carry the cli convention. A safe program
name comes from the prompt's first H1 (optionally backticked): letters/digits/dot/underscore/hyphen, starting with
a letter, up to 64 characters; pdd, node, gh and git are reserved because putting their shims first on PATH would shadow pdd’s own tools. Record schema, original test and Story criteria privately using
the runtime state store. Create .pdd/try/bin/<program> with mode 0700 and a POSIX shell shebang that execs the absolute Node executable. Never traverse a symlink
or overwrite a file not marked as a PDD Try launcher. Ignore .pdd/try/ via the repository's local Git exclude file
so future source captures contain no adapters or evidence. No token or browser capability enters the launcher.
Keep the evaluated JavaScript constant. Pass the installed module URL and private
descriptor path as separate data arguments, followed by the program's unchanged
argv, with POSIX-safe shell quoting. Paths must never become JavaScript source.

Print its absolute path, one POSIX-safe `export PATH=…:"$PATH"` line, and distinct examples from the Story's
argv steps. Every shell word in an example is quoted safely. Default returns immediately. --shell launches the
user's bash or zsh (otherwise /bin/sh) with the PATH and inherited terminal, waits, and returns its status.

`runShim(descriptorPath, argv, ports={})` loads the private descriptor and passes argv unchanged. Read stdin only when the input schema declares a stdin property. Otherwise do not open, iterate or consume the stream, even when piped or never closed, so an enclosing shell read loop retains its input. For declared piped stdin, read at most 1 MiB as UTF-8; forward even an empty pipe. Terminal stdin is
omitted unless required, when it is an empty string. --help is passed to the prompt like any argv. Authenticate
and invoke through runDoorCall. Require stdout/stderr strings and integer exit_code in 0..255 except 125.
Preserve program stdout byte-for-byte and return its exit code. Preserve program stderr, then append a separated short Try usage line on stderr; wrapper accounting must never enter stdout. If program stderr lacks a final newline, separate the usage line with one. Show known usage on refused calls too, unknown when unconfirmed; never replay for accounting. Reserve 125 for wrapper failures: stderr starts with
`pdd try:` followed by a plain reason; stdout remains empty. Never print credentials, stacks or internal URLs.
Record the last confirmed command/result with the original test identity in private state, independently of
whether the program exited successfully. Unknown execution must not leave an older command eligible for Save.

`saveLast(context)` reads the last confirmed invocation for this repository, verifies the current gh login and
original session identity, and appends the input/result as one exact recorded case in the original test file
through saveDoorCase. This records an observation; it does not approve a prompt or validate that the answer is
correct. Repeated Save for the same action is a no-op. Refuse missing/unknown evidence or a changed Story/test
identity, and keep earlier checks and all unrelated test bytes. Tie the recording to the original step's criterion.
Print the target file and new step name. No model call is needed.

## Dependencies

- [Runtime client](runtime-client.prompt.md): required generation/runtime context for authentication, state, owner
  calls, confirmed results and safe original-test append.
- [Runtime preflight](runtime-preflight.prompt.md): required generation/runtime context for CLI interfaces.
- [Prompting guide](../../docs/prompting-guide.md): required authoring context.

Launcher execution must work inside projects declaring CommonJS or ESM. Use an absolute Node executable and
syntax-neutral dynamic import rather than relying on extensionless-file module detection. The launcher must
not resolve its own program name as Node or gh: capture the absolute PATH entry for the GitHub CLI when opening a Try, preserving its stable symlink rather than its versioned target. Use it for later authentication. If a saved executable is gone, resolve gh from PATH again while skipping PDD launchers; never authenticate through a project launcher. Refuse reserved dependency names case-insensitively before writing a launcher.

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
