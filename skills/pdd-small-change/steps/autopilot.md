# In Autopilot

Use this file only when `autopilot.mode` in the root `pdd.json` is `observe` or `auto` and pdd-autopilot started the run. With `off` or no value, SKILL.md applies as written.

Overrides SKILL.md and RUNBOOK §2, §4, §11 and §12:
- Gates (§2): read the owner handoff/run notes. Follow the scoped delegation and native approval route in [$pdd-merge](../../pdd-merge/SKILL.md), ahead of generic ask-and-stop rules for covered non-strict gates. A fresh pdd-check checks the PR at its head; its PASS is checker evidence, not approval.
- Optional steps: do not ask. Skip them (§12): pdd-check runs the changed path. Never put a Simulator link in a PR, issue or file.
- Plan gate: put the scope and the checker's verdict line in the PR body.
- Expected values (§4): take each one from an issue quote or from the old behavior. A new test value needs no person when the runtime and the checker (blind, from the Story, with a named rule) agree. Else it is a note on the PR. Never change a test to make it pass.
- A Story or an expected value that seems wrong (§11): ask one question only for a product call that the issue does not settle. Else pick one and say why on the PR.
- Cost (RUNBOOK "AI calls"): write the likely check cost on the issue or PR, and do not wait.
- No verdict from the AI service, busy or not run (§11): ask no person. Follow [$pdd-autopilot interpreter outage](../../pdd-autopilot/steps/handoff.md#interpreter-outage): `pdd workflow park --interpreter`; end the turn.
- Missing route: [record it](../../pdd-autopilot/steps/handoff.md#missing-pdd-route).
- Merge: pdd-merge, not a person. New words that users see go in its merge line; they do not stop the run.

Keep: product calls the issue does not settle, actions that cannot be undone, `--max-calls`, strict mode, and never sending a failed check again.

After repeated failed validation, inspect the actual failure, identify its cause and change the repair before another permitted check. Two failed rounds do not by themselves mean this issue is blocked. Keep repairing while a useful correction is available, with correct expectations and required validation, for at most 5 repair rounds in one area (a round is a return to an earlier step that clears later steps; a retry of the same step is not one); pdd refuses a 6th. Then, or if a real blocker remains, record its cause and next action in the original run and take the stuck path: `pdd:stuck`, one comment with the cause, one `stuck` alert. Keep its claim and progress, and let the coordinator continue independent eligible work. Never repeat an unchanged failed check or an external action with an unknown outcome.

Every behavior prompt needs a declaration: full, partial or native-only with reason. Use `pdd interface draft`. Show coverage; unmapped/conflicting sentences need one grouped person decision with quotes, never delegation.

Full suites/builds follow the [shared queue rule](../../pdd-autopilot/steps/handoff.md).
