---
name: pdd-merge
description: Use when Autopilot has a fresh checker PASS on a PDD pull request and must decide to merge it, write "would merge", or leave it for a person.
metadata:
  pdd-skills: 0.1.26
---

# PDD merge

Read the facts first: `autopilot.mode` in `pdd.json`, the issue author, the checker verdict, the PR head and its checks. If `autopilot.mode` is absent or `off`, a person merges as RUNBOOK §2 says.

An agent needs the person’s explicit merge request. An operator’s explicit auto setup and start, or an applicable standing delegation, supplies it for eligible work; a configuration read alone does not. A fresh independent checker PASS is evidence, never approval. Never fabricate approval words or infer broader authority. Strict approval, trust and repository-required human reviews still apply. `observe`: when all the conditions below are true, write one PR comment "Would merge" with the facts; a person merges. In `auto`, an issue from a person who is not trusted (pdd-autopilot) gets a draft PR, and a trusted person merges it.

A PR with no checker verdict (the checker could not run or gave none): add the `pdd:no-verdict` label, do not merge, and take the next issue.

Apply all [$pdd-autopilot merge conditions](../pdd-autopilot/steps/handoff.md#merge-conditions) before merging.

In an Autopilot run, read the owner notes for the attributed operator action or exact delegation and scope. For an ordinary non-strict gate covered by that authority, after the gate is ready and its prerequisites are met, record the actual attributed operator action or delegation words with `pdd workflow approve N --said -` using the safe stdin form in RUNBOOK §2. This scoped rule overrides manual ask-and-stop guidance; no repeated per-issue approval is needed. A checker PASS is separate evidence, never approval words. If authority is absent or does not cover the gate, wait for actual authorized approval. Strict mode requires the person terminal; never bypass it or edit approval fields. Keep other work moving while approval is pending.

Post one PR comment identifying the person’s actual explicit merge authorization without fabricating a quotation. It gives the verdict, the head and the checker. It lists the new words that users see (command names, help text, error messages) and each screen change, with its screenshot path and one line on what changed, so a person can look at them before a release. These do not stop the merge. A failed comment stops. If PR 1 has a PASS but no runtime verdict, it merges; add the `pdd:no-verdict` label to the PR.

Before merging and after it, require `pdd autopilot check-base RUN PR` exit 0. Report refusals; a post-merge mismatch is an incident.

Check the head again, then run `gh pr merge PR --merge --match-head-commit <sha>`. Never use `--auto`. A changed head stops. Read the merged state back. After PR 1, add the `pdd:code-pending` label to the issue. After the code PR, close each issue that waited on it with "Fixed in #PR" and remove `pdd:code-pending`. Remove the `pdd:working` label.
