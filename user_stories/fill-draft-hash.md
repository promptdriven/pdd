# Fill a draft hash beside an incomplete fixture

I can fill my new draft prompt's hash even when my repository contains an unrelated incomplete prompt fixture.

## Acceptance criteria

1. With one draft prompt and an unrelated interface object without a status, `pdd check --fill-hash` fills the draft hash, warns that the fixture has no status and was skipped, and exits 0.
2. The skipped fixture keeps exactly the same bytes and contributes nothing to the filled, current, refused or stale counts.
3. An explicitly invalid status, malformed JSON, a non-object interface, multiple interface blocks or a draft without a hash key is refused and makes the command exit 4.
4. An approved prompt whose text changed stays unchanged and makes the command exit 4, even when no test reaches it.
5. Hash filling needs no tests, sign-in, network request or AI call, and applies the same rules in every directory.

## Rules to check

Only absence of the status key earns the skipped-fixture warning; null, an empty string and other explicit invalid statuses must not become warnings. Refusals and stale approved prompts retain exit 4 even alongside a successfully filled draft or a skipped fixture. Never change approval status or skipped/approved file bytes.

The native replay vectors in `test/fixtures/fill-hash/cases.json` describe expected outcomes. Both owning CLI prompts lack an executable Runtime interface and declared filesystem/Git resource ports; runtime scenarios cannot prove this command's native file writes, stdout or exit code. Verify through the public CLI and native preflight export using temporary Git repositories; do not add a check-only operation.
