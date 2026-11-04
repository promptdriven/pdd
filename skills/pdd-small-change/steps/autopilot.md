# In Autopilot

Use this file only when `autopilot.mode` in the root `pdd.json` is `observe` or `auto` and pdd-autopilot started the run. With `off` or no value, SKILL.md applies as written.

It changes these rules of SKILL.md and RUNBOOK §2 and §4:
- Gates: do not ask the person. A fresh pdd-check checker checks the PR at its head. Its PASS is the approval; pdd-merge records it with `pdd workflow approve N --said -`.
- Optional steps: do not ask. Skip them.
- Plan gate: put the scope in the PR body.
- Expected values: take each one from an issue quote or from the old behavior. A new value needs a rule that a trusted person wrote on the issue; else ask one question on the issue. Never change a test to make it pass.
- Merge: pdd-merge, not a person. New words that users see go in its merge line; they do not stop the run.

Still in force: product calls the issue does not settle, actions that cannot be undone, `--max-calls`, strict mode, and never sending a failed check again.

After a FAIL, do one fix round. After a second FAIL, check the premise: is the issue, the Story or the plan wrong? Write the cause and a new plan in one comment, add the `pdd:stuck` label (`gh issue edit N --add-label pdd:stuck`), and stop work on this issue.

A test runs a prompt that has no interface block: draft the block through pdd, do not skip the test.
