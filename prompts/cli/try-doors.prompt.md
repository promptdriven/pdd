# Use a Try session from a terminal or HTTP client

Own src/try-doors.mjs. Provide one generic adapter around the owner's saved Try. Preserve argv strings, program
streams and saved session identity. Do not interpret commands, execute a project binary, or generate project logic.

`openCli(context, test, sessionId, options)` selects the first distinct CLI entry used by the Story's tests; refuse
if there are multiple distinct CLI entries. Both input and result schemas carry the cli convention. A safe program
name comes from the prompt's first H1 (optionally backticked): letters/digits/dot/underscore/hyphen, starting with
a letter, up to 64 characters; pdd, node, gh and git are reserved because putting their shims first on PATH would shadow pdd’s own tools. Record schema, original test and Story criteria privately using
the runtime state store. Create .pdd/try/bin/<program> with mode 0700 and a Node shebang. Never traverse a symlink
or overwrite a file not marked as a PDD Try launcher. Ignore .pdd/try/ via the repository's local Git exclude file
so future source captures contain no adapters or evidence. No token or browser capability enters the launcher.

Print its absolute path, one POSIX-safe `export PATH=…:"$PATH"` line, and distinct examples from the Story's
argv steps. Every shell word in an example is quoted safely. Default returns immediately. --shell launches the
user's bash or zsh (otherwise /bin/sh) with the PATH and inherited terminal, waits, and returns its status.

`runShim(descriptorPath, argv, ports={})` loads the private descriptor and passes argv unchanged. If stdin is
piped, read at most 1 MiB as UTF-8. Forward a nonempty pipe as stdin only if declared by the input schema;
otherwise refuse with a plain explanation. A declared stdin receives even an empty pipe. Terminal stdin is
omitted unless required, when it is an empty string. --help is passed to the prompt like any argv. Authenticate
and invoke through runDoorCall. Require stdout/stderr strings and integer exit_code in 0..255 except 125.
Print streams byte-for-byte and return that exit code. Reserve 125 for wrapper failures: stderr starts with
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
not resolve its own program name as Node or gh: capture the original absolute GitHub CLI path when opening a
Try and use it for later authentication. Refuse reserved dependency names case-insensitively before writing a launcher.

A reused Try retains its uploaded prompt bytes. Before overwriting a launcher or making a command, compare
local entry prompt bytes with the original private descriptor (and with the prompt hashes captured at session
creation). Refuse changed prompts with a --new hint; never relabel old runtime output with a new prompt hash.
An older session without pinned source hashes needs --new before becoming a CLI.
Keep the reported before/after world privately alongside the last result. Like the hosted Try Save, the appended
case records the last command's observed output; it does not rewrite the original scenario's initial_world or
preceding steps. For a nonempty saved world, print a short reminder to review the saved-data setup before replay.
