# See an independent review before the code PR

I can see an independent review of a fix and its proof before the code PR opens, so a green result cannot hide an unfixed defect or weakened tests.

## Acceptance criteria

1. Bug and feature workflows finish the code area with build, verify, formal, then review, before the existing code-PR gate, with no new human gate.
2. Review uses a fresh subagent that did not build or verify the change. It receives only the issue, Story, Defect block, diff, Old-code proof and Tests vs base evidence, without builder notes or chat history, and may inspect source, tests and the real changed path.
3. Review answers all six questions separately: defect and detection gap fixed; every new test fails on old code for the bug's reason; each removed test or changed assertion justified; fake-only coverage checked through one real path; warning-light-only work marked unfinished with the issue open; Story, PR and status claims supported by evidence.
4. The run's review.md starts with "Review: N must-fix" or "Review: no must-fix" and gives concrete findings. Must-fixes return to a fresh build and subsequent verify, formal and fresh review for at most two repair rounds; the code PR then opens with the verdict and any remaining must-fix list at the top.
5. The complete brakes-and-warning-light principle from issue #2595 appears verbatim at the top of bug, feature and small-change skill instructions and in the RUNBOOK; both RUNBOOK copies remain byte-identical.
6. Warning-light-only work says "Not fixed yet: this helps find the cause" at the PR top, uses "Refs #N" and keeps the issue open.
7. For a small-change behavior fix, scope records "Defect:" and "Not caught because:"; verify records "Proof (defect fixed):" and "Proof (gap closed):" and a reason for every removed test or changed assertion.
8. The exact supplied check-x RUNBOOK patch for #2598, #2599 and #2602 is retained in both copies, and the PR names those issues. Adding prove-command guidance to section 17 is deferred to #2594 together with the command; #2595 adds no guidance for an unavailable command.
9. Evidence distinguishes source checks from actual fresh-agent reviews: the required historical reviews detect the known unsafe change and find no must-fix in the control, while limitations and failures remain visible.

## Rules to check

The two repair rounds start after the initial review. Remaining findings cannot become a clean verdict because the rounds are exhausted. Expected values, existing gates and regression obligations remain owned by the person.

Acceptance specification: [manual cases](../test/manual/independent-code-review.md). This Story concerns agent instructions and workflow metadata; it introduces no callable runtime operation. Source assertions check the shipped instructions, and fresh-agent exercises check their use. Neither establishes runtime enforcement of reviewer identity or proves agent judgment.
