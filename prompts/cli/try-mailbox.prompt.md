# Run virtual commands across an agent sandbox with files

Own src/try-mailbox.mjs. Exchange one CLI command through ignored workspace files while an owner process
outside the sandbox authenticates and calls the runtime. The sandbox needs neither network nor home access.
Preserve argv, declared stdin, program streams/status, source identity and one-shot dispatch. Never persist
credentials or owner browser capabilities in the mailbox, descriptor, replies, status or diagnostics.

Export prepareMailbox(root, sessionId), mailboxCall(descriptor, input, ports), and watchMailbox(context, descriptor).
The root is canonical, the session ID is a safe identifier. Mailbox directories are below
<root>/.pdd/try/mailbox/<sessionId>, mode0700; files are regular, single-link, mode0600. Reject path escapes,
symlink components and unsafe file types. Publish complete JSON atomically so neither process reads partial data.

## Request and reply

mailboxCall publishes a fresh UUID request {id, sessionId, input} and waits for that ID's reply. Readiness
requires a recent owner heartbeat (at most5seconds old) for the same session. Missing/stale readiness fails
before publishing with advice to keep pdd try STORY --cli open outside the sandbox. Never fall back to network.
After publishing, cancellation, relay loss or a15minute deadline means unknown: never publish again automatically.
Use short local polling waits, cancellable by signal; no gh, process launch, global state or fetch in this route.
Replies must match the request/session IDs; return the owner result or throw its sanitized refusal with known usage.
Malformed/mismatched replies fail without dispatching again. Leave evidence for recovery; do not erase a request
merely because the waiting shim stopped. A request whose answer already exists is never dispatched again.

## Owner relay

watchMailbox keeps the owner setup identity only in RAM, updates readiness while alive and processes requests
sequentially. Bind every call to the descriptor's original root, origin, session, login, prompt and operation;
request data may supply only input, never authority, path, endpoint, token or launcher. Require argv strings and
optional UTF-8 stdin at most1MiB; bound JSON requests to2MiB. Reject malformed input without a runtime call.
Use an exclusive dispatch claim per request before calling runDoorCall with the owner's in-memory identity/store.
An existing claim without a reply is unknown after restart: do not dispatch it again. A confirmed busy rejection
may wait only under the runtime client's pre-execution rule. Preserve passed and nonzero program results exactly.
Sanitize refused diagnostics and echoed credentials before writing replies; receipt usage is metadata, not program output.
An exclusive live-relay lock prevents two owner processes from dispatching the same mailbox concurrently.
Do not steal locks from a possibly running process. Ctrl-C stops the relay, clears only its own readiness/lock,
and leaves the Try running; in-flight outcomes remain unknown and requests stay recorded. --shell can stop the
relay after the interactive shell exits. A killed owner may leave a lock; name it and require checking its process
before removal. No background daemon or global configuration is required.

## Dependencies

- [Runtime client](runtime-client.prompt.md): required generation/runtime context for owner dispatch, identity,
  busy retry, cancellation, unknown recovery and usage.
- [Try doors](try-doors.prompt.md): navigation to CLI selection, source validation, output and Save policy;
  not required loading context (avoids a dependency cycle).
