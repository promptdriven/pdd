---
kind: native-only
reason: Filesystem custody, terminal identity and physical child cleanup require native host tests.
---
# Local command host primitives

Own `src/live-local-host.mjs`. Export `createLiveLocalHost({env, redaction, root})`, returning the host ports named in the Runtime seam contract. This module provides physical effects; runtime-client owns manifest admission, command matching, dispatch authority and write policy. Do not infer read or write authority here.

## Domain decisions

`readManifest({path,root})` reads the explicit local file, bounded to 1 MiB, and returns parsed JSON. Refuse malformed JSON and duplicate object keys at any nesting level, including escaped spellings. Retain the read file identity and freeze the parsed object and all its descendants before returning, so later mutation cannot alter admitted authority. The client must refuse inclusion in captured source; physical placement under the source root alone does not refuse. The path and file contents stay local unless the client explicitly selects their permitted configuration fields.

`manifestInSource({path,root,files})` returns whether the manifest identity appears among captured repository-relative file paths, including realpath and hardlink aliases. Refuse a manifest whose identity or file metadata changed since readManifest. The client owns rejection before upload; never remove selected context.

`resolveExecutable({executable})` accepts one fixed basename, resolves it through local PATH once to an executable regular file, and returns its absolute real path. No shell lookup or command execution. `environment({names})` returns only named available string values and local HOME, USERPROFILE, XDG_CONFIG_HOME, GH_CONFIG_DIR and APPDATA references. Register named values with the supplied shared redaction registry before use; never serialize them.

`execute({request,resolvedExecutable,signal,environment,root})` starts the retained absolute executable with the request argv after its executable token, literal stdin, and explicit environment. Shell execution is disabled. Resolve the repository and relative cwd to real paths; refuse traversal, absolute cwd and symlink escape. Validate primitive size/time bounds before process launch. Return exactly stdout, stderr, exit_code, timed_out, stdout_truncated and stderr_truncated. On timeout, terminate children and return timed_out true and null exit_code. On abort, terminate children and reject. Terminate the process group even when its leader exits, so background descendants cannot survive a completed call. Wait for cleanup before settling. Unsupported platforms refuse before launch. Keep transient capture bounded to 1 MiB per stream; overflow terminates the group and rejects without partial evidence. Redact each full captured stream using the supplied registry before UTF-8 truncation to admitted caps. Invalid redaction results reject. No raw output appears in diagnostics, journals or terminal output.

`terminal` is true only for the actual process stdin and stdout terminal streams. `confirm({binding_id,executable,argv})` returns `{confirmed:boolean}` from a fresh terminal prompt for each call. Display sanitized, control-free JSON argument representations. Only a fresh exact yes response confirms. Headless streams, automatic flags and piped answers cannot confirm. An interrupted or closed prompt declines.

`journal.read(key)` returns the saved JSON value or null; `journal.write(key,value)` durably replaces it. Keys are SHA-256 lowercase hex. Store under the explicit PDD_STATE_DIR or owner home state directory, outside the real repository root. The readManifest root binds the source boundary before journaling; direct bridge callers supply root when creating the host. Refuse symlink paths, non-owner or group/world-accessible directories/files, and non-regular entries. Writes use private mode, atomic replacement and durable file/directory synchronization. Reject any value whose serialized form changes under shared redaction; the client supplies already sanitized receipts. Never save raw outputs or credential values. Reads validate the same custody and redaction rules.

`redact({text})` returns `{text}` through the shared registry. `randomUUID()` creates an opaque UUID. `sleep(ms,signal)` is abortable and removes timer/listener state when settled. Creating the host ports performs no filesystem or process effects.

## Dependencies

- [Secret redaction](secret-redaction.prompt.md), required shared registry and sanitization semantics supplied by injection.
