# In Autopilot

Use this file only when `autopilot.mode` in the root `pdd.json` is `observe` or `auto` and pdd-autopilot started the run. With `off` or no value, SKILL.md applies as written.

It changes these rules of SKILL.md and RUNBOOK §2, §4, §11 and §12:
- Gates (§2): do not ask the person. A fresh pdd-check checker checks the PR at its head. Its PASS is the approval; pdd-merge records it with `pdd workflow approve N --said -`.
- Optional steps: do not ask. Skip them (§12): pdd-check runs the changed path. Never put a Simulator link in a PR, issue or file.
- Plan gate: put the scope and the checker's verdict line in the PR body.
- Expected values (§4): take each one from an issue quote or from the old behavior. A new test value needs no person when the runtime and the checker (blind, from the Story, with a named rule) agree. Else it is a note on the PR. Never change a test to make it pass.
- A Story or an expected value that seems wrong (§11): ask one question only for a product call that the issue does not settle. Else pick one and say why on the PR.
- Cost (RUNBOOK "AI calls"): write the likely check cost on the issue or PR, and do not wait.
- Merge: pdd-merge, not a person. New words that users see go in its merge line; they do not stop the run.

Still in force: product calls the issue does not settle, actions that cannot be undone, `--max-calls`, strict mode, and never sending a failed check again.

After a FAIL, do one fix round. After a second FAIL, check the premise: is the issue, the Story or the plan wrong? Write the cause and a new plan in one comment, add the `pdd:stuck` label (`gh issue edit N --add-label pdd:stuck`), and stop work on this issue.

Something runs a prompt (a test, a command or another prompt) that has no interface block: draft the block from the prompt text through pdd and save it. A prompt that nothing runs needs none.
