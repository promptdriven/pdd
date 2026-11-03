# Compact a draft interface before checking it

I can remove unused JSON formatting from my draft interface before its first check, so the interpreter receives fewer source bytes.

## Acceptance criteria

1. `pdd test --fill-hash --compact` fills draft hashes and removes interface JSON formatting whitespace, including in drafts whose hashes are already current; it lists compacted paths and counts and exits 0 when nothing refuses or is stale.
2. Compaction preserves every field, member order, number spelling, escape and string byte; only the usual hash string and whitespace between JSON tokens may change, while prose, fences, wrappers and approval status stay exact.
3. Running compaction again on a compact current draft changes nothing; ordinary `pdd test --fill-hash` retains its hash-only output, result shape and formatting behavior.
4. Approved, statusless, malformed, multiple-block and unsafe-to-fill prompts stay unchanged with the existing current, stale, warning or refusal outcome; refusals or stale approved hashes retain exit 4.
5. For execution, `--compact` without `--fill-hash`, with a Story, or with another mode or option exits 2 before any write, sign-in, network request or AI call. Existing local help requests still show help without execution.
6. The command needs no tests, sign-in, network request or AI call, applies in every directory, and uses the canonical `pdd test` command; the removed `pdd check` name stays rejected.

## Rules to check

Compaction removes only space, tab, CR and LF between tokens inside the root JSON object. It never reserializes JSON, drops metadata, rewrites numbers or string escapes, changes prose-hash meaning or approves a prompt. Safe drafts retain their normal hash classification even when their whitespace changes. Only opt-in results have a separate list of compacted paths. An unsafe file stays unchanged even beside a successful draft.

[Native cases](../test/fixtures/fill-hash/compact-cases.json) fix exact source and result expectations independently of implementation. Replay the public command, native preflight export and direct command handler in temporary Git repositories; retain the existing hash-only vectors and bounded status/hash checks. The existing Runtime interfaces do not bind native hash filling/compaction or its Git/filesystem effects. Runtime check: NOT REPLAYED; native effects require build-step tests. No check-only API or synthetic Runtime pass is requested.
