# In Autopilot

Use this file only when `autopilot.mode` in the root `pdd.json` is `observe` or `auto` and pdd-autopilot started the run. With `off` or no value, SKILL.md applies as written.

Overrides SKILL.md and RUNBOOK §2, §4, §11, §12 and §14:
- Gates (§2): in `auto` (non-strict), pdd auto-approves Story/PR gates (`autopilot-auto`: mode + checks) when checks pass and draft review has `Review: no must-fix` (a contract change asks one question); else follow [$pdd-merge](../../pdd-merge/SKILL.md). A fresh pdd-check checks each PR; its PASS is checker evidence, not approval.
- Optional steps: do not ask. Skip try (§12): pdd-check runs the changed path. Never put a Simulator link in a PR, issue or file.
- Story gate: put the verdict line (§14) and the full Story paths in the PR 1 body.
- Code PR: start it as soon as PR 1 is open, stacked on PR 1; do not wait for PR 1 to merge. In `auto`, do this in every repo. In `observe`, a repo with a release does it too; a new product waits for a person's "code now".
- Expected values (§4): take each one from an issue quote or from the old behavior. A new test value needs no person when the runtime and the checker (blind, from the Story, with a named rule) agree. Else it is a note on the PR. Never change a test to make it pass.
- A Story or an expected value that seems wrong (§11, §14): ask one question only for a product call the issue does not settle; else pick one and say why on the PR.
- Cost (RUNBOOK "AI calls"): write the likely check cost on the issue or PR, and do not wait.
- No AI verdict, busy or not run (§11): ask no person; follow [$pdd-autopilot interpreter outage](../../pdd-autopilot/steps/handoff.md#interpreter-outage): `pdd workflow park --interpreter`; end the turn.
- Missing route: [record it](../../pdd-autopilot/steps/handoff.md#missing-pdd-route).
- Merge: pdd-merge, not a person. New words that users see go in its merge line; they do not stop the run.

Keep: unresolved product calls, irreversible actions, `--max-calls`, strict mode, and never sending a failed check again.

Fix the failed check's cause before retrying; two failed rounds do not block work. Keep repairing while a useful correction is available, for at most 5 repair rounds in one area (a round is a return to an earlier step that clears later steps; a retry of the same step is not one); pdd refuses a 6th. For a real blocker or at the limit, record cause and next action; take the stuck path: `pdd:stuck`, one comment with the cause, one `stuck` alert. Keep its claim and progress; the coordinator continues other eligible work. Never repeat an external action with an unknown outcome.

Executed prompts: draft through pdd. Show coverage; unmapped/conflicting sentences need one grouped person decision with quotes, never delegation. Unused prompts need none. No prompt covers the code: use the verdict "no prompt covers this yet".

Full suites/builds follow the [shared queue rule](../../pdd-autopilot/steps/handoff.md).
