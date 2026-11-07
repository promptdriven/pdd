# In Autopilot

Use this file only when `autopilot.mode` in the root `pdd.json` is `observe` or `auto` and pdd-autopilot started the run. With `off` or no value, SKILL.md applies as written.

It changes these rules of SKILL.md and RUNBOOK §2, §4, §11 and §12:
- Gates (§2): read the existing owner handoff/run notes, then follow the scoped standing delegation and native approval route in [$pdd-merge](../../pdd-merge/SKILL.md), including its precedence over generic ask-and-stop instructions for covered ordinary non-strict gates. A fresh pdd-check checks the PR at its head; its PASS is checker evidence, not approval.
- Optional steps: do not ask. Skip them (§12): pdd-check runs the changed path. Never put a Simulator link in a PR, issue or file.
- Plan gate: put the scope and the checker's verdict line in the PR body.
- Expected values (§4): take each one from an issue quote or from the old behavior. A new test value needs no person when the runtime and the checker (blind, from the Story, with a named rule) agree. Else it is a note on the PR. Never change a test to make it pass.
- A Story or an expected value that seems wrong (§11): ask one question only for a product call that the issue does not settle. Else pick one and say why on the PR.
- Cost (RUNBOOK "AI calls"): write the likely check cost on the issue or PR, and do not wait.
- Merge: pdd-merge, not a person. New words that users see go in its merge line; they do not stop the run.

Still in force: product calls the issue does not settle, actions that cannot be undone, `--max-calls`, strict mode, and never sending a failed check again.

After repeated failed validation, inspect the actual failure, identify its cause and change the repair before another permitted check. Two failed rounds do not by themselves mean this issue is blocked. Keep repairing while a useful correction is available, preserving behavior expectations and required validation, for at most 5 repair rounds in one area (a round is a `done` for a step that area already recorded); pdd refuses a 6th. Then, or if a real blocker remains, record its cause and next action in the original run and take the stuck path: `pdd:stuck`, one comment with the cause, one `stuck` alert. Keep its claim and progress, and let the coordinator continue independent eligible work. Never repeat an unchanged failed check or an external action with an unknown outcome.

Something runs a prompt (a test, a command or another prompt) that has no interface block: draft the block from the prompt text through pdd and save it. A prompt that nothing runs needs none.
