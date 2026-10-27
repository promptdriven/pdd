# Area labels on the shared run status

`src/workflow-area-chats.mjs` owns the immutable small-change area map and
additive labels for the opt-in runner. The default runner has no chat metadata.
It never authorizes a decision, validates stage evidence, writes a status file
or publishes a PR. Preserve these function exports.

`AREA_CHATS` maps small-change to plan (`Chat 1: plan`, scope, approve-plan gate)
and build (`Chat 2: build`, change/verify/open-pr/wait-merge, merge gate).
`areaChatForStage(workflowName, stageId)` returns its immutable descriptor,
or null for an unsupported stage/workflow.

`areaChatStatus({state,base,event,now})` returns null without chat:true. Otherwise
it spreads the complete shared status `base` and adds mode:area-chats, area
{id,label,stages}, chat label, gate, event and updatedAt. A pending unapproved
proposal stays in plan even though the next definition is change. Otherwise
select the current definition, falling back to the last completed area after
completion. Merge is the merge gate; no other stage is a person approval.

Session identity, step times, waitingFor, links, changes and approvalRecord
remain exactly the shared projection's fields. Never borrow a pending session
for another step or substitute a Herdr server name for a native session ID.

## Dependencies

- [Shared status](workflow-run-records.prompt.md): required runtime/authoring
  authority for base status and its atomic writer; area metadata is additive.
- [Runner](workflow-runner.prompt.md): navigation to the producer of
  saved chat mode, definitions, proposal, accepted input and completed stages.
