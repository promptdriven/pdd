# Verify idle workflow agents

Run from the package checkout with Node.js 22.16.0 or newer:

```sh
node --test test/autopilot-idle-agents.test.mjs test/autopilot-stopped-chats.test.mjs test/workflow-chat-health.test.mjs
node --test test/workflow-change-delivery.test.mjs test/workflow-change-delivery.vectors.test.mjs
```

These tests call `openRun`, `runStatus` and `tickAutopilot` through the package's
public module boundaries. The shared workflow fixture creates isolated Git
repositories and run records. The shared Herdr fake records native launches and
prompt deliveries. The injected clock advances idle time without waiting. The
delivery port also supports controlled unsent failures. No test contacts GitHub,
a model, the interpreter or a live Herdr session.

The idle cases check manual and automatic saved-session resumes for Claude and
Codex, with existing and rebuilt workspaces.
They also restore and attach sessions held at approval gates, open questions and
paused interpreter waits without reserving or sending a continue notice. Controlled
holds during native resume or journal custody prevent notice creation. Holds at final submission
prevent sending and keep the journal request pending.
They check first observation,
10-minute boundaries, three attempts per area, recorded progress, working and
held agents, pending and uncertain delivery, concurrent changes and one stuck
alert. Alert tests use the real alert service with controlled HTTP responses.
They check retry after a failure before service custody, known unsent transport
failure, destination setup after the stop, and a fresh tick process after the
runner saves the stop before alert handoff. Repeated ticks preserve delivered
and unconfirmed alert custody. Status is checked in detail, list, all-repository
and JSON forms. The stopped-chat and delivery tests check the shared recovery
and journal behavior.

Run the same idle test file against a separate checkout of the candidate's parent
revision to check the regression. Keep its expected values unchanged. Missing
continue deliveries, idle nudges and idle status must fail assertions. A setup
error does not prove this regression. Keep the commands and counts outside the
repository, then remove the temporary checkout.

These checks prove native decisions with controlled dependencies. They do not
prove that a live agent acts on a delivered prompt or that a real Herdr server
reports its state correctly. They do not check prompt interpretation or approval.
