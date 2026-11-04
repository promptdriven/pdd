# Native criterion evidence

I can see which executed native tests support each Story criterion, and what still lacks proof.

Issue: https://github.com/promptdriven/pdd/issues/2954

## Acceptance criteria

1. I can select a Story and see its exact criterion identity, reviewed profile, executed native test IDs and relevant fixture and gate evidence.
2. A criterion with several required mapped tests has support only when all execute and pass; failed, skipped or missing required tests leave it unproved.
3. A missing mapping, changed criterion text or out-of-profile test stays unproved with a reason; a Story has native support only when every current criterion has valid executed support.
4. Stale or incomplete profile evidence cannot prove a criterion; the executed observations remain visible.
5. Original external machine evidence keeps its source and limits and gives qualified support; only PDD-observed execution is labeled PDD-observed.
6. A declaration, lint pass, typed count, replay manifest or modeled physical result alone cannot prove a native criterion.

## Rules to check

Profile completion alone cannot prove a Story. Missing, unknown or empty current Story facts give no whole-Story native support.

No current native proof may follow from missing required execution, prerequisites or review/source identity. Optional skips stay visible. Expected results come from these rules, not observed output.

Runtime cases judge synthetic supplied evidence. They execute no physical filesystem, Git or pane effect. Native capture and integration still need native tests.

## Draft choices for review

The [shared contract](../prompts/cli/workflow-results.prompt.md#native-profile-and-criterion-assessment-draft) proposes a Node event report, requirements in approved trusted-source prompt prose, qualified original external evidence and all mapped required tests passing. Review the producer/format and external intake verification route before implementation. No gate is approved.
