# Show the real formal result on a code PR

As a reviewer of a pdd code PR, I want the formal check line to say what pdd read from the formal record and why, so that I can trust that line and repair a missing or bad record.

## Acceptance criteria

1. pdd reads the `formal` block of `replay-evidence.json` on its own, also when the approved prompt area has no scenario vectors or the scenario replay stops early. The scenario replay keeps its own status: NOT REPLAYED or BLOCKED never becomes a pass.
2. The formal status is one of: recorded (with its result: Proved (bounded), Proved (solver), Failed + counterexample, Not run + reason or Not applicable + reason), missing, malformed (FIELD) or stale (source changed). The header line and the Proof table row use the same words. When the status is not recorded, they give the reason and one repair step, for example "write the formal block per docs/replay-evidence.md, then run pdd workflow done formal again". They never say only "not recorded". They never say that the evidence has no formal result when the file holds a block that pdd did not accept.
3. With no scenario vectors, pdd records a Proved result only when the formal block has its own control: `control_outcome: assertion_failure`, `control_command` and a nonzero `control_exit_code`. With scenario vectors, a Proved result needs the semantic mutation control that names failed original assertions.
4. When a Story of the run has `## Rules to check`, the code PR is not ready to merge until the formal status is recorded with Proved or Not applicable. The status line names the formal problem. A Failed result stays publishable with its failure line and is not ready. With scenario vectors, the code replay needs a typed formal block, so the line and the row always give the formal status with its reason and repair step, and a missing, malformed or stale block holds the PR. The row says "not needed (no Rules to check in the Story)" only when pdd read the Stories of the run, none has `## Rules to check` and the prompt area has no scenario vectors; then only a Failed result holds the PR. When pdd finds no Story file of the run, the formal check counts as needed, and the line says why and how to name the Story. One PR never says "not needed" while its code replay is blocked for the formal block.

## Rules to check

Wrong: "Formal check (agent reported): not recorded." with no reason and no repair step; "has no formal result" when the file holds a formal block; a formal result that pdd drops because the area has no scenario vectors; a Proved result with no vectors and no own control; a stale formal record that shows as Proved; a code replay NOT REPLAYED that becomes PASS because of a formal result; "✅ Ready to merge" when a Story has Rules to check and the formal result is missing, malformed, stale or Not run; "not needed" on a PR whose code replay is blocked for a missing or bad formal block.

## Native checks

The checks are in [test/formal-evidence-status.test.mjs](../test/formal-evidence-status.test.mjs) (cases named `FORMAL`) and in [test/workflow-pr-publication.test.mjs](../test/workflow-pr-publication.test.mjs) (cases named `FORMAL-REAL`). They read real `replay-evidence.json` files in temporary Git repositories, render the PR body builders, and publish a code PR through the real workflow command with local Git and a fake `gh` command. No interpreter run and no GitHub rendering is claimed.
