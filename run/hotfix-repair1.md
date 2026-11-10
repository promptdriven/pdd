# Intake hotfix repair 1

Issue: #3053. Branch: `pdd/hotfix-intake-codex-1110`.
Start commit: `803a2ac1b`.

## Must-fix 1: Save the snapshot after sort writes

The branch already had the repair from `44f75d25a`. It also had the two exact-count factory assertions. This repair puts the success refresh directly before the final return. It keeps a refresh before each partial-failure or caught-failure return. Each refresh follows the sort saves, group updates, mixed-part updates and routes. Successful sibling writes remain visible when another write fails.

The factory prompt was updated before source and test edits. It requires one completion, one review comment and eligible free work on the completion wake. The intake prompt already requires the correct refresh order. Its approved contract did not need a change.

Tests:

- With the old intake source from `a2011ff9d`, both partial-write controls fail at `INTAKE_PARTIAL_SORT_SNAPSHOT_NOT_REFRESHED`: 0 pass, 2 fail, exit 1.
- With the same old intake source, the tightened mixed factory case fails at `INTAKE_FACTORY_DUPLICATE_INTAKE`: 0 pass, 1 fail, exit 1.
- The candidate intake file passes: 13 pass, 0 fail, exit 0. It covers thrown saves, unconfirmed saves, route failures and assigned subjects.
- Final independent focused and factory counts appear below.

## Must-fix 2: Test both assigned umbrella paths

A separate snapshot-marker case is restored. It adds the marker to issue #100, then calls `w.review(100)`. Completion now reaches the umbrella assertion on old code.

A separate live-index case is added. Issue #100 is absent from the prepared snapshot. Its assigned marker appears only during the issues-page read under group admission. The test checks that this scan runs. It also checks that one umbrella #101 is created and issue #100 gets no writes.

The same cases were run with the three old intake and sort source modules from `48f5466cb`. Both tests fail at the intended assertions: `INTAKE_ASSIGNED_UMBRELLA_RECOVERED` and `INTAKE_ASSIGNED_LIVE_UMBRELLA_RECOVERED`. Counts: 0 pass, 2 fail, exit 1. Neither test fails with `invalid-analysis`. Both pass on the candidate.

## Final checks

The fresh verifier did not write code, tests or prompts.

Focused command:

```sh
node --import ./test/helpers/test-home.mjs --test test/issue-sort-intake.test.mjs test/issue-sort.test.mjs test/issue-sort-groups.test.mjs test/issue-sort-mixed.test.mjs test/issue-sort-native.test.mjs test/issue-sort-repair.test.mjs test/issue-sort-repair2.test.mjs test/issue-sort-publication.test.mjs test/issue-sort.formal.test.mjs test/issue-dependencies-freshness.test.mjs
```

Result: 243 pass, 0 fail, exit 0.

Factory command:

```sh
bash scripts/factory-test.sh
```

Result: 36 pass, 0 fail, 0 skipped, exit 0. The fresh verifier reports PASS on both must-fixes.

The old-source controls used the same tests in this worktree. They changed only the named production modules. Each control restored the candidate bytes in a `finally` block. Raw logs stay outside the repository in `lead/repair1-evidence/`.

## Prompt hashes and limits

Scoped `fillHashes` was run for the three intake Runtime prompts and the factory prompt. The three Runtime prose hashes are current. There are no stale hashes or refusals. Their generated source hashes match their prompts. The factory prompt has no Runtime interface or `prose_sha256` field. Its current SHA-256 was recorded in the generated factory test header: `f0910848bafcfb9efc519e752ac37fe83591991961637b1375a8a18d8b09b781`.

No prompt was approved in this repair. The changed `prompts/test/autopilot-factory.prompt.md` needs person review. It has no Runtime approval block. The three existing intake approvals are unchanged.

Do not infer a live GitHub or model result from these checks. The factory uses real local Git and native CLI commands with service fakes. No prompt-interpreter check, full public suite or process-replay test was run. No GitHub write or push was made.
