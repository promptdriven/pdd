# In Autopilot

Use this file only when `autopilot.mode` in the root `pdd.json` is `observe` or `auto` and pdd-autopilot started the run. With `off` or no value, SKILL.md applies as written.

Overrides SKILL.md and RUNBOOK §2, §4, §11 and §12:
- Gates (§2): in `auto` (non-strict), pdd auto-approves plan/PR gates (`autopilot-auto`: mode + checks) when checks pass and draft review has `Review: no must-fix` (a contract change asks one question); else follow [$pdd-merge](../../pdd-merge/SKILL.md). A fresh pdd-check checks the PR; its PASS is checker evidence, not approval.
- Optional steps: do not ask. Skip them (§12): pdd-check runs the changed path. Never put a Simulator link in a PR, issue or file.
- Plan gate: put the scope and the checker's verdict line in the PR body.
- Expected values (§4): take each one from an issue quote or from the old behavior. A new test value needs no person when the runtime and the checker (blind, from the Story, with a named rule) agree. Else it is a note on the PR. Never change a test to make it pass.
- A Story or an expected value that seems wrong (§11): ask one question only for a product call that the issue does not settle. Else pick one and say why on the PR.
- Cost (RUNBOOK "AI calls"): write the likely check cost on the issue or PR, and do not wait.
- No verdict from the AI service, busy or not run (§11): ask no person. Follow [$pdd-autopilot interpreter outage](../../pdd-autopilot/steps/handoff.md#interpreter-outage): `pdd workflow park --interpreter`; end the turn.
- Missing route: [record it](../../pdd-autopilot/steps/handoff.md#missing-pdd-route).
- Merge: pdd-merge, not a person. New words that users see go in its merge line; they do not stop the run.

Keep: product calls the issue does not settle, actions that cannot be undone, `--max-calls`, strict mode, and never sending a failed check again.

Fix the failed check's cause before retrying; two failed rounds do not block work. Keep repairing while a useful correction is available, for at most 5 repair rounds in one area (a round is a return to an earlier step that clears later steps; a retry of the same step is not one); pdd refuses a 6th. For a real blocker or at the limit, record cause and next action; take the stuck path: `pdd:stuck`, one comment with the cause, one `stuck` alert. Keep its claim and progress; the coordinator continues other eligible work. Never repeat an external action with an unknown outcome.

Something runs a prompt (a test, a command or another prompt) that has no interface block: draft the block from the prompt text through pdd and save it. A prompt that nothing runs needs none.

Full suites/builds follow the [shared queue rule](../../pdd-autopilot/steps/handoff.md).
