# Sort observations and effects

Own sort integration with GitHub and local area/release data. Use injected ports
for GitHub, settings, files, clock and waits. The native adapter reads root pdd.json,
CODEOWNERS (.github first, then root, then docs) and package version. The resulting
area/release fingerprint is a snapshot input. No extra issue or model reads for
classification: use the dependency snapshot and coordinator analysis.sorts.
Prepare supplies sort context in contextJson. Queue issues with no current sort
alongside ordinary dependency subjects, at most 10. Completion requires one sort
per requested issue only when sort context is supplied. Reuse current records.
Validate the entire sort batch and reread current inputs before saving any sort.
Save one immutable sort comment, with named base IDs and human readable evidence.
Untrusted or edited sort comments cannot supply decisions. Record comments are
bookkeeping and do not stale requirements or dependency review.

Routing uses current mode and rereads the issue's assignees and live claim before
each effect. Never close or assign a person-owned or claimed issue. Off writes
nothing. Auto: one evidence comment with a reopen hint, then close. Observe:
pdd:close-proposed and one evidence comment, leave open. Assign another login
with one comment and no start. For another repository write one link note and
no start. Unsure: pdd:needs-owner and one question. Every write is serial, at
least 1000 ms after the preceding write, including record saves. Use immutable
comment bodies to recover retries. A failed or unconfirmed write stops the batch;
never blindly retry it. Confirm comments and issue updates by readback. Labels
are created only when absent. Do not change claims, trust, approvals or merging.

## Dependencies

- [Sort](issue-sort.prompt.md): required validation and routing policy.
- [Areas](autopilot-areas.prompt.md): required local area matching and draft policy.
- [GitHub observations](issue-dependencies-github.prompt.md): required native ports,
  trust and ownership behavior. Sort hooks only add observations and bookkeeping.
