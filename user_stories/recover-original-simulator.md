# Recover the original Simulator setup

As a person whose Simulator setup stopped before its outcome was clear, I want to read the original setup without creating a replacement.

## Acceptance criteria

1. If the original setup result or session is unknown, repeating my Simulator command keeps its saved setup ID, returns an uncertainty message, and sends no new setup, stop, reopen or lint request.
2. A missing or expired status result also keeps the saved setup ID and gives a read-only way to inspect that exact request; it does not prove that the original work never ran.
3. If a newly submitted setup ends unknown, its saved setup is retained and a later repeat still reads that same request.
4. Once the original request is confirmed running, I can use its existing setup; a separate setup requires a deliberate replacement choice while the outcome is uncertain.
5. Recovery messages name the original request and its authenticated status endpoint, without claiming that unknown work used no AI calls.

## Native cases

The [client contract](../prompts/cli/runtime/runtime-client.prompt.md#pdd-simulate) owns the recovery decision. [Public client regressions](../test/runtime-try-recovery.test.mjs) exercise retained private state and actual HTTP requests through the existing injected transport. Real provider validation uses a separate disposable setup; it never replays the historical uncertain operation.
