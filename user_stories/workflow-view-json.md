# Review a workflow run as JSON

I can request a machine-readable review of one saved workflow run with `pdd workflow view ISSUE --json`.

## Acceptance criteria

1. With a saved gated run, `pdd workflow view ISSUE --json` prints one JSON object with `version: 1`, the saved issue `{number,title,url}`, `state`, `area`, `gate: {id,area,kind}`, and the saved question text in `message`, then exits 0 without changing the run or contacting Herdr, GitHub, the PDD runtime or the network; `gate.id` equals saved `run.gate.id` or JSON `null` when that field is absent.
2. With a saved completed, cancelled or otherwise ungated run that has no saved question, the command prints `gate: null` and `message: null`, preserving the saved `state` and current area, and exits 0.
3. `links` is exactly `{stories,plan,pull_requests}` of saved Story, plan and pull-request URLs; a saved Try URL is absent from all three arrays, and an absent group is `[]`.
4. Each recorded approval is exactly `{decision,actor:{via},timestamp}` where `via` is the saved `via` value and `timestamp` is the saved finite `at` converted to an ISO-8601 UTC string; a run with no approvals returns `approvals: []` and no approval is inferred.
5. If the run file or a referenced review artifact is missing, unreadable or malformed, the command still exits 0, leaves the affected scalar `null` or array empty, and lists the affected field/path in `unavailable`; it does not crash or fabricate data.

## Rules to check

The JSON form is a read-only projection of saved local state. It does not approve, cancel, open or resume a workflow, refresh external status, or infer identities, timestamps, gate ids or links that are not recorded. Gate ids are nullable saved strings; actor is the saved channel under `actor.via`; timestamps are nullable ISO-8601 UTC strings derived only from finite saved epoch milliseconds.

Verification: `node --test test/workflow-view.test.mjs` covers the existing passive text view; the new JSON contract needs gated and ungated runtime cases before implementation.
