---
name: pdd-merge
description: Use when Autopilot has a fresh checker PASS on a PDD pull request and must decide to merge it, write "would merge", or leave it for a person.
metadata:
  pdd-skills: 0.1.20
---

# PDD merge

Read the facts first: `autopilot.mode` in `pdd.json`, the issue author, the checker verdict, the PR head and its checks. If `autopilot.mode` is absent or `off`, a person merges as RUNBOOK §2 says.

RUNBOOK.md:66 says: "An agent may merge only after the person's explicit chat request". Turning Autopilot to `auto` is that request. `observe`: when all the conditions below are true, write one PR comment "Would merge" with the facts; a person merges. In `auto`, an issue from a person who is not trusted (pdd-autopilot) gets a draft PR, and a trusted person merges it.

A PR with no checker verdict (the checker could not run or gave none): add the `pdd:no-verdict` label, do not merge, and take the next issue.

Merge only when all of these are true:
- a fresh checker PASS (pdd-check) is for the current head. A PASS for another head counts only when `git patch-id` of both heads is equal and the full suite is green on the exact current head. A conflict fix or any other change gives a new patch-id and needs a fresh PASS;
- the full suite is green on the exact merge head, for PR 1 and the code PR. Red pair: if PR 1's new native tests are red only for the missing behavior, never merge PR 1 alone. When both PRs have a PASS, set the code PR's base to PR 1's base (`gh pr edit CODE --base BASE`); merge the code PR, which carries PR 1, once the full suite is green on its exact head;
- at least one check ran, and all required checks are green on that head. A missing, pending or failed check: wait, do not merge;
- a second fresh checker agreed when pdd-check asks for one (risk 4-5, a split verdict, or a change to check, merge or approval code);
- no question to a person is open.

In a pdd run, record the PASS. Never edit approval fields:

```sh
pdd workflow approve N --said - <<'PDD_SAID'
Decided by the checker: <verdict>, head <sha>, checker <family/session>
PDD_SAID
```

If pdd refuses it (strict approvals), do not merge; ask the person one question.

Post the merge line as one PR comment that starts `Merge requested by the person: "autopilot.mode: auto"`. It gives the verdict, the head and the checker. It lists the new words that users see (command names, help text, error messages) and each screen change, with its screenshot path and one line on what changed, so a person can look at them before a release. These do not stop the merge. A failed comment stops. If PR 1 has a PASS but no runtime verdict, it merges; add the `pdd:no-verdict` label to the PR.

Check the head again, then run `gh pr merge PR --merge --match-head-commit <sha>`. Never use `--auto`. A changed head stops. Read the merged state back. After PR 1, add the `pdd:code-pending` label to the issue. After the code PR, close each issue that waited on it with "Fixed in #PR" and remove `pdd:code-pending`. Remove the `pdd:working` label.
