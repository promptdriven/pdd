---
kind: native-only
reason: Filesystem custody, shared terminal input ownership, and physical child process-group cleanup require native host tests.
---
# Local command host primitives

Own `src/core/live-local-host.mjs`. Export `createLiveLocalHost({ env, redaction, root })`, returning the host ports consumed by the [PDD to Runtime seam](runtime-seam.prompt.md) for owner-local command execution. This Layer-1 `core` module imports only `node:*` built-ins and provides physical OS effects; `@promptdriven/runtime-client` owns manifest compilation, admission, command matching, dispatch authority, and write policy. Never infer read or write authority here.

## Boundary and runtime contract

Creating the host via `createLiveLocalHost({ env = process.env, redaction, root = process.cwd() } = {})` performs zero filesystem, terminal, or child-process effects and returns the port surface below:

| Host port | Signature & observable contract |
|---|---|
| `terminal` | Boolean `true` only when both `process.stdin.isTTY === true` and `process.stdout.isTTY === true`. |
| `readManifest({ path, root })` | Resolve `actualRoot = realpath(root)` and `realpath(resolve(actualRoot, path))`, open with `O_RDONLY \| O_NOFOLLOW \| O_NONBLOCK`, verify regular file and `<= 1 MiB` (`1048576` bytes) via bounded read, unchanged `fstat`, and unchanged `lstat(actualPath)`, decode strict UTF-8, parse strict JSON rejecting duplicate keys at any nesting level (including escaped spellings) and depth `> 128`, deep-freeze the object, record file identity (`actualPath`, `stat`) keyed by `resolve(actualRoot, path)` and update `sourceRoot`, and return the frozen manifest. Supports both expanded `pdd.live-local-manifest.v1` and concise command-map shorthand objects. |
| `manifestInSource({ path, root, files })` | Resolve `actualRoot = realpath(root)` and verify the retained manifest snapshot for `resolve(actualRoot, path)` still matches current `realpath` and unchanged `stat` (`dev`, `ino`, `size`, `mtimeMs`, `ctimeMs`); validate every repository-relative entry in `files` (rejecting non-strings, absolute paths, `..`, `\\`, and NUL bytes) and return `true` if any captured file matches `actualPath` or `(dev, ino)` (covering symlinks and hardlinks), else `false`. |
| `resolveExecutable({ executable })` | Accept a single fixed basename matching `/^[A-Za-z0-9][A-Za-z0-9_.+-]{0,127}$/`; search absolute `env.PATH` entries in order without shell lookup, resolve via `realpath`, verify regular file and `X_OK`, and return its absolute real path. |
| `environment({ names })` | Validate each name against `/^[A-Z][A-Z0-9_]{0,127}$/`; return a null-prototype object containing only available string values for `names` plus local `HOME`, `USERPROFILE`, `XDG_CONFIG_HOME`, `GH_CONFIG_DIR`, and `APPDATA`. Register explicitly named values with `redaction.remember` before use; never serialize them. |
| `execute({ request, resolvedExecutable, signal, environment, root })` | Validate `request`, string `resolvedExecutable`, and an explicit plain/null-prototype `environment` object (with NUL-free string keys/values; never falling back to `process.env`) plus argument counts/sizes, stdin bounds, timeout (`1..120000` ms), and stream caps (`0..65536` bytes) before launch. Spawn `resolvedExecutable` with `request.argv.slice(1)`, literal `request.stdin`, explicit sanitized `environment`, `shell: false`, and `detached: true` inside a verified real `cwd` under `realpath(root)`. Capture up to `1 MiB` per stream, redact each full stream through `redaction.redact` before UTF-8 code-point truncation to admitted caps (stepping back a truncated cut if needed so the truncated text remains a fixed point under `redaction.redact` and never trips journal `safeValue` checks), terminate the entire process group on exit/timeout/abort/overflow before settling, and return `{ stdout, stderr, exit_code, timed_out, stdout_truncated, stderr_truncated }`. |
| `confirm({ binding_id, executable, argv, signal })` | Require actual `terminal` (`stdin.isTTY && stdout.isTTY`) and a single module-level FIFO terminal confirmation queue (`confirmationTail`) shared across all host instances. Drain complete and partial typeahead before rendering a sanitized control-free, bidi-escaped, and line-separator-escaped JSON label (`Allow this local write? ... Type yes to confirm: `). Confirm only on an exact fresh `yes` answer. |
| `journal.read(key)` / `journal.write(key, value)` | Persist SHA-256 lowercase-hex keys under `<PDD_STATE_DIR or HOME/.local/state/pdd>/live-local-journal/<key>.json`, strictly outside `realpath(sourceRoot)`. Reject symlink ancestors (outside OS root `/var`/`/tmp`), non-regular entries, wrong owner, or group/world permissions (`mode & 0o077 !== 0`). Open reads with `O_RDONLY \| O_NOFOLLOW \| O_NONBLOCK`; write atomically via `O_WRONLY \| O_CREAT \| O_EXCL \| O_NOFOLLOW` (`0600`), `fsync` file, `rename`, and `fsync` directory. Validate `<= 1 MiB`, strict JSON, no known secrets in serialized JSON, unchanged string keys/leaves under `redaction.redact`, and no unredacted values under secret-named keys on both read and write. |
| `redact({ text })` | Call `redaction.redact(text)`, verify string output, and return `{ text }`. |
| `randomUUID()` | Return an opaque `node:crypto` UUID. |
| `sleep(ms, signal)` | Abortable timer that cleans up timer and `AbortSignal` listener on settle. |

## Error mapping and failure behavior

- **`readManifest` failures:** Any missing file, FIFO/non-regular target or TOCTOU-swapped symlink/file, size `> 1 MiB`, concurrent stat mutation, invalid UTF-8, malformed JSON, depth `> 128`, or duplicate key rejects with `Error` carrying `code: 'live-local-manifest-invalid'`.
- **Fail-closed host errors:** Unsupported platforms (`win32`), invalid paths/bounds, symlink escapes, missing executables, stream capture `> 1 MiB` overflow (kills process group and drops partial output), non-integer exit codes, redaction errors, changed manifest metadata on `manifestInSource`, or unsafe/secret-containing journal entries reject fail-closed without leaking raw output or credentials.
- **Timeouts and cancellation:** Execution timeouts kill the child process group and resolve `{ ..., exit_code: null, timed_out: true }`. `AbortSignal` cancellation during `execute` or `sleep` kills the process group / clears the timer and rejects with `name: 'AbortError'`.
- **Terminal consent fail-closed & isolation:** Headless streams, piped stdin, blank answers, `no`, Ctrl-C, EOF, read errors, or `AbortSignal` (before queue, while queued, while draining, or while prompting) resolve `{ confirmed: false }` without poisoning subsequent queued calls, without leaking terminal listeners or raw mode, and without granting consent to any other call.

## Real-host verification cases

- `test/live-local-host.test.mjs`: non-mocked filesystem custody tests covering nested/escaped duplicate keys, invalid UTF-8, deep-freeze immutability, symlink and hardlink `manifestInSource` detection, post-read mutation refusal, real `PATH` binary execution without shell evaluation, secret redaction before UTF-8 byte truncation, `cwd` traversal and symlink escape refusal, real child process-group termination on timeout/abort/exit, `> 1 MiB` stream overflow suppression, and private `0600` atomic journal custody.
- `test/live-local-consent.test.mjs` (`test/helpers/live-local-consent-pty.py` + `live-local-consent-child.mjs`): real POSIX PTY tests across 16 scenarios verifying one fresh `yes` answer per call, concurrent queue ordering across shared and separate host instances, complete/partial typeahead draining, decline/blank/SIGINT/EOF/read-error isolation, and real `executeLocalCommand` / `createLocalCommandBridge` scratch writes.
- `test/live-local-cancel.test.mjs` (`test/helpers/live-local-cancel-pty.py` + `live-local-cancel-child.mjs`): real POSIX PTY tests across 9 `AbortSignal` cancellation scenarios (before queue, during drain, while queued, while active, both active+queued, race with `yes`, and bridge service/remote/close aborts) verifying zero leaked listeners, restored terminal mode, and zero physical writes.

## Dependencies

- [Shared secret redaction](secret-redaction.prompt.md): required shared redaction registry (`remember`, `redact`, `known`) supplied by injection.
