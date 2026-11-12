# See proof before Autopilot merges

As an Autopilot operator, I can see independent evidence for the current PR commit and the work that needs my attention.

## Acceptance criteria

1. A fresh independent reviewer runs checks on the current commit and records the commands and results, plus a real app or Try exercise when applicable or a reason it does not apply. The PR review shows the evidence.
2. Missing, failed, malformed or stale evidence cannot authorize a merge. A new commit, including a base refresh or mechanical conflict fix, requires fresh review and proof; CI and the full suite must also pass on that commit.
3. A repair retains a regression case for each behavioral finding. The reviewer checks the tracked case, its passing result and evidence that it fails on old code or a planted reproduction before passing the repaired commit. For a finding without changed public behavior, the reviewer records why a regression check is not applicable.
4. Status summarizes ready merges, open decisions and blocked work from saved local state without changing it or contacting GitHub.
5. The existing authority, trust and person-approval requirements still apply to every merge.

## Rules to check

A reviewer cannot turn a failed or missing check into a pass. An earlier commit's proof cannot authorize a later commit. A repeated behavioral finding without retained regression evidence cannot pass. Attention lines are bounded and do not claim a live GitHub state.
