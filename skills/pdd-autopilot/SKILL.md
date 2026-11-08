---
name: pdd-autopilot
description: Use when a person asks to start or use Autopilot, or it is on for a repo: pick ready issues, claim them and run each to an outcome.
metadata:
  pdd-skills: 0.1.22
---

# PDD Autopilot

Before you start or use Autopilot, confirm the repo. If this folder is in no Git repo, the person named another repo or it is unclear, ask one plain question with the repos you see and wait; never pick one. Run `pdd autopilot` in that repo's folder.

Read root `pdd.json`: `{"autopilot":{"mode":"off|observe|auto","trust":[...]}}` and `checker`. If `autopilot.mode` is absent or `off`, do nothing; a person leads. `observe`: do all the work; a person merges. `auto`: $pdd-merge merges under its delegation and merge rules. `pdd autopilot start` runs a tick with no AI that starts this skill only when there is work.

Follow [handoff](steps/handoff.md) for the person's chosen automatic work and merge authority, outcomes and retries.

GitHub labels `pdd:working`, `pdd:stuck`, `pdd:no-verdict`, `pdd:code-pending`: add with `gh issue edit N --add-label NAME` (or `gh pr edit`); create a missing one with `gh label create NAME`.

1. Check repo, account, native agent and CLI readiness. On a first visit, use pdd-prompting `verification-setup.md` to find or create and keep the repo’s start-up recipe for install, test and running a changed path; report gaps. Run only documented bounded startup before dependency review and selection. After selection, use the available recipe to build, verify and test the chosen path or Story. Workers follow repo repro/tests.
2. Trust: trusted = the repo owner + write access + people added with `pdd autopilot trust`. Read only trusted people's text: the issue body and comments. On a public repo, do not read an issue from another author until a trusted person comments on it.
3. Ready: open, eligible under [dependency review](steps/dependencies.md); the current GitHub `Assignees` field (human ownership) is known and empty; no live `pdd:working` claim; and not owned elsewhere. Include old and new backlog; a related PR or saved run alone is not ownership and does not stop fresh work. Missing assignment or eligibility data waits. `eligible: false` in a launcher packet is monitoring, never fresh work.
4. Own it: one owner per issue. Give the owner the issue link and a note of at most 30 words with goal, scope and repro; for a Story, use pdd-prompting. Stop with one comment if it is not a bug, has no repro or someone else owns it. For a product call no test settles, ask one question on the issue; that issue waits and the others go on. In `observe`, an owned workflow with an open PR waits for a person's review or merge; its `pdd:working` claim remains. Verify the claim owner before you continue or resume.
5. Run it with pdd-bug, pdd-feature or pdd-small-change. In `auto`, start the code PR as soon as PR 1 is open, in every repo. In `observe`, a repo with a release does the same; a new product waits for a person's "code now". One code PR per prompt file closes every issue that waits on it.
