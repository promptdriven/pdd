# Run an existing simulation by Try ID

As an agent operator without a browser, I want to run, observe and stop an existing simulation by its exact Try ID, so that a pure JSON prompt stays inside its created session and call cap.

## Acceptance criteria

1. Supplying `try_id` "520c7aa5-72f6-4add-b60e-8ed87db656c2" binds only that running simulation with its pinned `source_sha256` and call cap 40 (40 remaining), and refuses a missing, paused, stopped or cap-mismatched Try ID without opening or reopening a session.
2. Running a pure JSON prompt on that bound Try returns the confirmed outcome or declared error "invalid-quantity" with external `run_id` and internal `action_id`, uses 1 call on the first run and marks an exact repeat as `replayed: true` with 0 calls.
3. Observing `run_id` "7b409bce-ede1-40a5-ba87-ae67cbf516b0" on Try "520c7aa5-72f6-4add-b60e-8ed87db656c2" returns its read-only `state`, `session_state` (including "stopped"), external `run_id` and internal `action_id` "605cd2d9e23745f990720a7a5103490c", and marks an "unknown" call as `unknown_outcome: true` without replaying it.
4. `pdd simulate --stop 520c7aa5-72f6-4add-b60e-8ed87db656c2` selects only that saved simulation to stop and refuses an unknown Try ID.

## What must not change

- Calling `pdd mcp` tools without `try_id` keeps the existing Story selection, automatic initial Try setup and idle-paused reopen behavior.
- Existing `pdd simulate --cli`, `pdd simulate --serve` and `pdd simulate --stop [STORY]` Story/test selectors keep their current behavior and exit codes.
- Undeclared call refusals and uncertain (`unknownOutcome: true`) calls remain errors, and uncertain calls continue to block later `try_run` dispatches on the same MCP connection.

## Rules to check

- An explicit `try_id` never opens a new simulation (`POST /v1/try`) and never reopens a paused or stopped simulation (`POST /v1/try/<id>/reopen`), even when the saved ID is missing, `404`, `410` or `409` `session-stopped`. Forbidden: silent session creation, silent reopen or silently switching to a `400`-call cap.
- External `run_id` (`request_id`) and internal `action_id` stay distinct across `try_run` and `try_observe`, and an `"unknown"` observation never triggers `GET /v1/runs/<id>` recovery or a duplicate `POST /v1/try/<id>/call`. Forbidden: substituting `action_id` for `run_id`, replaying an uncertain call or turning an undeclared refusal into a normal outcome.
- `pdd simulate --stop <TRY_ID>` selects at most one saved simulation before authentication or `DELETE /v1/try/<id>`, leaving every other saved simulation untouched. Forbidden: stopping another Story's simulation or removing a saved record without confirmed stop.

## Coverage boundary

```pdd-boundary
prompts/cli/try-session.prompt.md
```

The Runtime test checks the pure binding, call-outcome projection, read-only observation projection and stop-selector decisions on supplied records and runtime replies. Stdio MCP JSON-RPC framing, Git repository discovery, private state files, authenticated HTTP requests and CLI exit codes are covered by the repository's native tests.
