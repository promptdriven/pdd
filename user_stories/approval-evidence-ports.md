# Native chat approval evidence ports

I can discover matching native sessions and extract post-gate user messages while skipping stale files, subagent rollouts, generated wrappers, and ignored prefixes, and refusing unreadable sessions or unavailable clocks.

```pdd-boundary
prompts/cli/approval-evidence.prompt.md
```

## Acceptance criteria

1. `findNativeSessions` skips files whose `mtimeMs` is older than `stage.startedAt` without reading their contents, excludes subagent rollouts, and returns matching sessions `[{id, startedAt}]`.
2. `findNativeSessions` raises `session_unreadable` when session discovery encounters an unreadable directory or file rather than returning an empty list.
3. `readApprovalEvidence` excludes generated `environment_context` wrappers, `[Request interrupted` lines, and `ignorePrefixes` matches, returning the latest eligible human message after `gateAskedAt` or `{ok: false, code: "user_message_missing"}` when none remain.
4. `readApprovalEvidence` raises `clock_unavailable` without reading session directories when `clock.now` returns a non-positive observation timestamp.
