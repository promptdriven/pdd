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

## Draft contract and verification limits

The [shared contract](../prompts/cli/workflow-results.prompt.md#native-profile-and-criterion-assessment-draft)
keeps original external reports through the existing workflow evidence route.
The result owner checks original bytes, run/workspace association, selected
source, reviewed profile, outcomes and fixture/gate references. Checked imported
evidence stays qualified; missing facts stay unknown. An original report does
not need a new PDD or Node producer.

Requirements bind to actual approved prompt bytes through the existing journal
and saved gate snapshot, including newly approved worktree content. Candidate
edits cannot lower protected requirements before a matching later review.

For a native Story, the author links its owning reviewed profile in a
`Native validation` section. `pdd lint STORY` selects that profile within the
workspace boundary and shows each current criterion's evidence or missing
reason. Workflow and PR readers use the same judgment and original source/stage.
A complete profile cannot prove unmapped, empty or unknown Story criteria.

The supplied cases judge only synthetic owner-derived contexts. They do not
test the original-report parser, real admission/approval readers, lint discovery
or display, workflow/PR integration, or native effects. Those routes still need
implementation and native verification. The actual private retained pair is
unavailable and was not read or reproduced. No gate is approved.
