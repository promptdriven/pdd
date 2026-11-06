# Run the Node test suite

I can run the repository's tests from npm inside or outside a workflow chat.

## Acceptance criteria

1. `npm test` selects the top-level `test/*.test.mjs` files by default. `npm test -- <file...>` selects only the supplied files.
2. A test child receives no environment variable whose name starts with `HERDR_` or equals `PDD_AGENT_SESSION`.
3. A test child receives no caller stdin. Each stdout and stderr chunk reaches the matching caller stream as soon as the child writes it.
4. Runs with the same selected test outcomes have the same exit status. The launcher preserves the child's exact numeric status, including a nonzero status.

## Rules to check

The focused-file list replaces the default set; it never runs beside the full suite. Keep every environment entry except the named session markers. Ignore stdin. Forward stdout and stderr chunks as they arrive; do not accumulate and replay them after exit. Do not compare separate runs' output bytes or timing lines: each run keeps its own live streams, and elapsed times can differ. Do not inspect or connect to a live Herdr socket or agent session. The Story does not claim that every descriptor or socket is isolated.

## Native verification boundary

Prompt scenarios can check selection arguments, environment filtering, stdio choices and supplied child exit codes. They cannot prove live stream timing, OS descriptor behavior, socket isolation or native child termination. The cause of the reported hang remains unknown. A passing containment or native check alone does not establish the cause or resolve the historical hang.
