# Native validation profile

I can see whether my reviewed native validation profile completed its required coverage on this source.

Issue: https://github.com/promptdriven/pdd/issues/2961

## Acceptance criteria

1. An exit-zero report with a missing required fixture or skipped required test shows incomplete validation and the affected test IDs.
2. Complete required coverage can pass with optional skips; I can still see their reasons and the original evidence source and limits.
3. Missing, partial, stale, incompatible and unknown evidence stay distinct and give no current native proof.
4. I can see selected, started and completed observations, duplicate occurrences and distinct IDs; duplicate passes cannot fill a missing required ID.
5. A compatible prior report shows the actual lost test IDs even when totals match; an incompatible or unknown baseline is marked incomparable.
6. Candidate edits cannot lower the reviewed required inventory without matching review; absent or changed review binding gives no current proof.
7. I can see required gate outcomes and relevant fixture/artifact identities, observed states and verification references; an unexecuted gate, failed test, unknown execution or incompatible artifact cannot pass.
8. Reading saved evidence does no execution or repair; notes, typed origin claims, modeled results and declared counts cannot become native proof.

## Rules to check

No current native proof may follow from missing required execution, prerequisites or review/source identity. Optional skips stay visible. Expected results come from these rules, not observed output.

Runtime cases judge synthetic supplied evidence. They execute no physical filesystem, Git or pane effect. Native capture and integration still need native tests.

## Draft choices for review

The [shared contract](../prompts/cli/workflow-results.prompt.md#native-profile-and-criterion-assessment-draft) proposes a Node event report, requirements in approved trusted-source prompt prose, qualified original external evidence and all mapped required tests passing. Review the producer/format and external intake verification route before implementation. No gate is approved.
