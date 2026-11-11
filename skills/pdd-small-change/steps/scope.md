# scope

- Read the repo instructions and the code and prompts that the request touches.
- In scope.md, list every issue request and trusted follow-up as a checklist. Save the same items in `small-change-checklist.json` (RUNBOOK §15). Keep pending items visible; exclusions need a reason quoted from the issue, not the plan.
- State the result, the files it touches, the owner that `pdd owner FILE` gives for each (or "no prompt"), why it is small and how to undo it.
- If behavior changes, write the expected output or error now, before the code changes.
- For a behavior fix, write `Defect:` (the real defect and where it occurs) and `Not caught because:` (the detection gap) in scope.md.
- Name the test command. Record any docs-only/formal exemption in the typed formal block (RUNBOOK §15); prose is not gate evidence.
- Ask only about a choice that changes the result. Do not widen the scope.
- Only the person decides gate approval. See RUNBOOK §2.
