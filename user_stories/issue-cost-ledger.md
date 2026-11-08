As an operator, I want local costs for each issue, so that I can compare the cost and outcome of factory work.

## Acceptance criteria

1. Normal and automatic runs retain measured tokens for each agent account. Repeated status reads do not add the same usage twice.
2. Status shows day and week totals, outcomes, and P50/P90 costs per merged issue. JSON exposes the same measurements without network reads.
3. Questions, recorded answers and person approvals have counts and waiting minutes. Active person time and runner suite time use explicit measured minutes. Unknown data stays visible.
4. A closed PR permits at most one read of Actions durations. Repeated status reads do not fetch durations.
5. Local ledgers retain GitHub call counts after the short GitHub budget ledger is compacted. No message text or secrets enter cost data.

## Rules to check

Cumulative token counts and duplicate Claude message rows must not inflate costs.
Retries of one measurement id must not add minutes twice.
Merged issue percentiles must group attempts by repository and issue.

## Native verification

Run `node --test test/issue-cost-ledger.vectors.test.mjs test/cost-ledger.test.mjs`.
Fixtures are synthetic Codex rollout and Claude transcript rows. The tests use the
repository workflow and Herdr fakes. No live account, timer or agent is needed.
