---
name: pdd-check
description: Use when Autopilot needs a fresh checker verdict (PASS, FAIL or NOT SURE) on a PDD pull request at its head, before pdd-merge.
metadata:
  pdd-skills: 0.1.27
---

# PDD check

You are a fresh checker. You did not build this PR; no builder chat. `pdd.json` `checker`: `claude`, `codex`, `gemini` or `any`. With `any` or no value, use another AI family that is installed and signed in. Else use a fresh session of the builder's family and label it `checker_mode: same-family`. Read only trusted people's text (pdd-autopilot).

PR 1 (prompt, Story, tests): read the issue first and write 3 input → result pairs from it. Trace issue → Story → prompt → tests. Each expected value comes from an issue quote or the old behavior. A new test value needs no person when you (blind, from the Story, with a named rule) and the runtime agree; else it is a note. A saved `pdd test` result for the new and the old prompt counts only when it matches the Story, the test cases and the prompt source at this head, and it was a fresh run (not cached). Else run `CI=1 pdd test <story> --cache-clear --json` once. A result you cannot check is not a fresh pass. The new passes; the old fails for the claimed reason, except code-only bugs (pdd-prompting RUNBOOK §14). No Runtime verdict is NOT SURE. Keep the required check pending and park the run for its Runtime cause issue.

PR 2 (code): read the issue, the PR 1 Story (open or merged) and the diff. Build the head; run the changed path with the repo recipe and Story. Repeat the real action from a fresh checkout with pdd-prompting/verification-setup.md; report setup, behavior and dependency scope. For a screen change, take before and after screenshots; describe the change.

Small-change: follow RUNBOOK §15. Derive the issue checklist independently. Missing items or unsupported exclusions are must-fixes. Check the shared formal exemption.

Read pdd-prompting/review.md.

Both PRs: the full suite is green on the head, with no new skip or only. One exception: new native tests in PR 1 may be red only for the missing behavior. Say so in the verdict; then PR 1 merges only together with its code PR.

Verdict: one PR comment with a JSON block: `verdict` (PASS, FAIL or NOT SURE), `head` (the SHA you checked), `risk` (1-5, before merge), `family`, `session`, `checker_mode`, and evidence. Then run `pdd workflow status N` to refresh the PR top. Never send a failed check again on your own.

A second fresh checker must agree when the risk is 4-5, when two verdicts split, or when the PR changes check, merge or approval code. Use the other family when it is installed and signed in; else a second fresh session of the same family, labeled `checker_mode: same-family`.

Ask about an unsettled product call, NOT SURE after one new try, or irreversible action.

After merge: a fresh session from a family other than the builder's reruns each merged PR on main and gives its own risk 1-5. A problem becomes a new issue. If no other family is available, say so; do not claim this review.
