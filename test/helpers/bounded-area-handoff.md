# Bounded earlier-area handoff verification

Prerequisites: the repository's supported Node version and Git on PATH. No
installation, credentials, live GitHub/Herdr server or model call is needed.

From the repository root, run:

```sh
node --test test/bounded-area-handoff.vectors.test.mjs
```

The test reads every case ID from the approved
`test/authoring-guidance/bounded-area-handoff-cases.json` manifest. It calls the
real `startRun`, `stepDone`, `approveRun` and `openRun` exports. A temporary Git
repository supplies a project-local custom workflow. Local Git runs normally;
GitHub publication and Herdr process/pane interactions use injected controlled
ports. A native launch must reference the exact saved start-message file before
the test reads that message. No private conversation or operational fixture is
required.

The short/empty-order and no-completion cases remove a completed record from a
controlled fixture ledger after the real step establishes its displayed gate.
This supplies an incomplete legacy-gate input without changing product gate
logic. The terminal confirmation port then uses the existing approval route.
Every other summary is recorded through `stepDone`. The persistence vector also
seeds a historical PR record, then renders a replacement with a real gate,
question and existing approval history. Synthetic confirmations are
test inputs, not human approvals. Metrics delivery is disabled for isolated
fixtures. All other durable fields are retained.

Expected observations: UTF-8 item and whole-line limits; exact equality behavior;
maximal complete-code-point prefixes; ordered aggregate omission with exact
counts; one JSON-quoted original-ledger recovery reference when needed; preserved
full summaries, late failures and report references; native failed-launch recovery
and replacement; unchanged terminal/strict approval refusals; and existing status
and PR projections. Recovery tests check pending questions, open gates, remaining
steps, completed records and approval history. The case IDs identify the approved
acceptance criteria in TAP output. Missing manifest handlers fail explicitly.

The harness removes its temporary repositories, worktrees, state, queue roots and
home directories using the test runner's cleanup hooks. Keep TAP output in the
external run evidence directory, not the repository. An assertion before the
intended launch boundary is a setup failure, not a behavior result.

For the old-code control, use a disposable checkout of the implementation's parent
revision, add these vector/helper files unchanged, and run the same command. The
`item-equality-and-overflow` case must fail the assertion
`whole displayed STEP: SUMMARY item must fit 1024 UTF-8 bytes` on the 1,025-byte
item. A crash or failed fixture setup is not defect detection. A fresh independent
verifier must repeat this control and the corrected run.

This is native local boundary evidence with simulated external services. It does
not establish a hosted interpreter pass, a real agent's evidence-reading choices,
GitHub/Herdr integration, or model token, latency or cost savings. Independently
review the recovery instruction against the complete Story and manifest. Formal
verification and the public full suite remain separate checks.
