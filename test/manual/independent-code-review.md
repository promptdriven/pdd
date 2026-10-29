# MANUAL acceptance: independent code review

Story: [See an independent review before the code PR](../../user_stories/independent-code-review.md). Requirements: [#2595](https://github.com/promptdriven/pdd/issues/2595) and its authorized scope additions. These are acceptance cases, not executable runtime scenarios. All implementation exercises below are **NOT RUN** in PR 1.

The shipped skill instructions remain the canonical prompt source. Install them with workflow metadata and structural tests together in PR 2. Do not add a duplicate review prompt or a made-up review API. Keep this acceptance specification and its expected historical findings out of every reviewer's supplied context.

## MANUAL 1 — workflow and reviewer context (AC1, AC2)

Inspect bug and feature workflow definitions, skill area summaries and docs: the code sequence is build, verify, formal, review, with review last before the existing PR gate. The gate list is unchanged. In an actual run, record separate fresh reviewer identity and supplied paths; the reviewer neither built nor verified this change. The brief addresses the reviewer directly: read only the issue, Story, Defect block, diff, Old-code proof and Tests vs base evidence, PR 1 body and supplied step summaries. Source/test inspection and a real changed-path exercise are permitted. Builder notes, prior conversation and expected replay findings are excluded; the reviewer must not open build.md, verify.md or formal.md in the run folder. Text assertions alone cannot establish reviewer independence.

## MANUAL 2 — six review answers (AC3, AC6)

Read each new review brief and an actual run's review.md. Require one evidence-based line per question:

| Question | Required observation; forbidden result |
|---|---|
| Defect and gap | Identifies whether both are fixed where the defect occurs; a message or guard alone cannot claim the defect fixed. |
| Old-code proof | Each new test fails on old code for the bug's reason; passing old code, a crash or another error is not proof. |
| Test changes | A sound reason for each removed test and changed assertion; matching the builder's output is insufficient. |
| Fakes | Checks whether coverage uses only a fake process, git, HTTP or files and exercises one real changed path; a fake-only pass is insufficient. |
| Unfinished work | Warning-light-only work has the exact PR-top line "Not fixed yet: this helps find the cause", uses "Refs #N" rather than "Closes #N" and leaves the issue open. |
| Claims | Checks the PR 1 body, step summaries and Story against actual evidence; green claims cannot conceal unsupported criteria, skips or failures. PR 2 does not yet exist. |

A must-fix is a problem build can fix in this change. Withhold the pdd-made "Old-code proof:" and "Tests vs base:" lines: the reviewer records their absence as limitations, not must-fixes or passes. Other unavailable evidence remains a limitation or concrete finding. PR rendering and issue-reference behavior depend on flow-runner (#2594); retain the integration check until that work is present.

## MANUAL 3 — verdict and bounded repair (AC4)

Exercise a clean review: the run-folder review.md first line is exactly "Review: no must-fix". Exercise a review with two concrete unresolved findings: the first line is exactly "Review: 2 must-fix" and the findings follow. The PR top receives the actual verdict and unresolved list.

After the initial must-fix review, observe that the chat holds `pdd workflow done review`, gives the findings to a fresh build and leaves PR 2 unopened. Each repair runs build, verify, formal and a fresh review. If the first repair review still finds must-fixes, hold completion again and run the second repair. Call `pdd workflow done review` only after the final review: either no must-fixes remain or two repair rounds are complete. It then opens PR 2 with the actual verdict and remaining list visible. No third repair round or new human gate is introduced. Do not claim this exercise was enforced by new CLI code.

## MANUAL 4 — exact principle and small changes (AC5, AC7)

Compare the following requirement fixture verbatim against the top of skills/pdd-{bug,feature,small-change}/SKILL.md and RUNBOOK.md. Compare RUNBOOK.md with skills/pdd-prompting/RUNBOOK.md byte for byte:

> Fix both: the brakes (the real defect) and the warning light (a test or check that would catch it next time). Brakes first. If the agent cannot find the defect yet, it fixes the warning light first: it adds what makes the defect visible (a failing reproducer test, a precise error, logging), so the cause becomes easy to find, and then it fixes the brakes. A warning-light-only change must say 'Not fixed yet: this helps find the cause' on the PR, and the issue stays open; it never closes the bug.

For a small-change behavior fix, inspect scope/verify instructions and an actual result: "Defect:", "Not caught because:", "Proof (defect fixed):" and "Proof (gap closed):" appear with evidence. Every removed test or changed assertion has a reason. For warning-light-only work, verify writes "Not fixed yet: this helps find the cause" in verify.md for pdd to lift to the PR top. Preserve existing expected-value ownership, approvals and regression checks. Skill/step sizes pass the repository's limits, or a necessary limit increase is explicitly justified in the PR.

## MANUAL 5 — RUNBOOK dependencies (AC8)

In #2595, section 17 does not add `pdd workflow prove` guidance. Flow-runner adds that guidance in #2594 together with the command, so this slice requires no unavailable command.

Apply the supplied check-x-RUNBOOK.patch unchanged to both RUNBOOK copies in PR 2 and check they remain identical. Its expected-value, missing-error and failed-check guidance must survive other edits. Name #2598, #2599 and #2602 in the PR body. Do not edit check-x's feature check.md or small-change change.md, or #1462's existing bug step files. If the patch cannot apply, report the conflict rather than guessing replacement policy.

## MANUAL 6 — actual proof and separation of expectations (AC9)

After implementation, run `node --test test/skills.test.mjs` and `npm test` on the VM; report real pass/fail/skip counts. Source checks cover labels and structure, including six numbered review questions, verdict/proof labels, review last in the code area and the completion hold in both skills. Keep the verbatim principle check across all five files; do not pin other long wording or check-x text. Require the new completion-hold assertion to fail on the pre-fix head. Run each new deterministic source-contract assertion against old source and require assertion failure where applicable. This checks installed instruction/metadata changes; it is not runtime replay or proof of agent judgment. Both PR bodies give their added and removed line counts as +added / -removed.

In scratch clones, supply only MANUAL 1's permitted evidence and the shipped review brief to separate fresh read-only subagents. Do not give them this document, expected findings, builder notes or earlier review reports. They may run tests in the scratch copy without editing source. Independently compare their completed outputs with these requirements:

| Replay | Expected acceptance result |
|---|---|
| #2559 first code version: base a1b09cb9, head 0db39638 | Must identify 19 deleted safety tests, no test with a real symlinked repository, and a test passing for the wrong reason. A later repaired head cannot substitute. |
| #2560 control | Resolve and record exact base/head hashes first; the fresh review reports "Review: no must-fix". |

If a required problem is missed, improve the generic review instructions without adding historical answers and retry at most two rounds; retain all outcomes and explain the changes. Record both replay results in the run's verify.md and DOGFOOD.md outside source. Missing proofs remain unproved. Formal check: Not applicable, because instruction prose, reviewer judgment and plain metadata wiring introduce no solver rule. Runtime check/Try: Not applicable; there is no application operation to invoke.
