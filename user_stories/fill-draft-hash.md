# Fill a draft hash beside an incomplete fixture

I can fill my new draft prompt's hash even when my repository contains an unrelated incomplete prompt fixture.

## Acceptance criteria

1. With one draft prompt and an unrelated interface object without status or prose_sha256 keys, `pdd test --fill-hash` fills the draft hash, warns that the fixture has neither key and was skipped with advice to add "status": "draft" and rerun the command if it is a prompt to check, and exits 0.
2. The skipped fixture keeps exactly the same bytes and contributes nothing to the filled, current, refused or stale counts.
3. An explicitly invalid status, malformed JSON, a non-object interface, multiple interface blocks or a draft without a hash key is refused and makes the command exit 4.
4. An approved prompt whose text changed stays unchanged and makes the command exit 4, even when no test reaches it.
5. A prompt with its own prose_sha256 key but no own status key, including a misspelled "Status", stays unchanged, is refused with advice to add "status": "draft" and rerun `pdd test --fill-hash`, and makes the command exit 4.
6. With only skipped fixtures and nothing filled, the command exits 0 with zero filled, current, refused and stale counts. Warnings print before filled paths, refusals and stale hints; the counts print last.
7. Hash filling needs no tests, sign-in, network request or AI call, and applies the same rules in every directory.

## Rules to check

Only absence of both own status and prose_sha256 keys earns the skipped-fixture warning; a present prose_sha256 key requires a refusal when status is absent regardless of the hash value. Inherited keys do not count as own keys; null, an empty string and other explicit invalid statuses must not become warnings. Refusals and stale approved prompts retain exit 4 even alongside a successfully filled draft or a skipped fixture. Never change approval status or skipped/approved file bytes.

The native replay vectors in `test/fixtures/fill-hash/cases.json` describe expected outcomes. Both owning CLI prompts lack an executable Runtime interface and declared filesystem/Git resource ports; runtime scenarios cannot prove this command's native file writes, stdout or exit code. Verify through the public CLI and native preflight export using temporary Git repositories; do not add a check-only operation.
