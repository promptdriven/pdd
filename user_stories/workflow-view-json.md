# Review a workflow run as JSON

I can request a machine-readable review of one saved workflow run with `pdd workflow view ISSUE --json`.

## Acceptance criteria

1. The command prints one JSON object with `version: 1`, the saved issue identity, run state and current area, and exits successfully without changing the run or contacting Herdr, GitHub, the PDD runtime or the network.
2. An open gate is represented by `gate` with its saved id, area and kind, and the saved gate or question text is in `message`; a completed, cancelled or otherwise ungated run has `gate: null` and `message: null` when no message is saved.
3. `links` groups the saved Story, plan and pull-request review links, and contains no Try URL.
4. `approvals` lists only approvals recorded in the run, with each decision's actor and timestamp; a run with none returns an empty list.
5. Missing or malformed local review artifacts remain represented as unavailable or empty data and do not make the JSON command crash.

## Rules to check

The JSON form is a read-only projection of saved local state. It does not approve, cancel, open or resume a workflow, refresh external status, or infer identities, timestamps, gate ids or links that are not recorded. The exact representation of a gate id, actor and timestamp remains an open contract decision for the person at the Story gate.

Verification: `node --test test/workflow-view.test.mjs` covers the existing passive text view; the new JSON contract needs gated and ungated runtime cases before implementation.
