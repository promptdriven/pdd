# Autonomous Parallel PR Bug-Fix Loop

Reusable runbook for shipping non-trivial bug fixes in `promptdriven/pdd` with
maximum safe parallelism, independent adversarial review, and minimal human
involvement.

The normal path is autonomous from issue intake through a merge-ready PR. A
human supplies the goal and any initial authority constraints, then is contacted
only for an escalation listed in [Human escalation policy](#human-escalation-policy).

## Operating objectives

Optimize for these outcomes, in order:

1. Correctness and preservation of user work.
2. A verifiable goal with explicit acceptance criteria and evidence.
3. Maximum safe parallelism on independent work.
4. Minimal human attention and no routine approval requests.
5. A short review/remediation loop.

Parallelism is bounded by dependencies and file ownership, not by habit. Run
independent work concurrently; keep causally dependent work sequential.

## Required agent tiers

Use these tiers explicitly. Do not rely on a tool's default model:

| Responsibility | Model | Reasoning | Mutation |
| --- | --- | --- | --- |
| Implementation, tests, investigation, integration, and remediation | `gpt-5.6-terra` | `high` | Allowed within assigned ownership |
| Independent adversarial review | `gpt-5.6-sol` | `high` | Read-only |
| Top-level orchestration | Current top-level agent | Highest available | Coordination and integration only |

In Codex agent environments, set `model: "gpt-5.6-terra"` and
`reasoning_effort: "high"` explicitly for implementation workers. A configured
`throughput-implementer-small` profile is also suitable for a genuinely small,
isolated lane when it guarantees Terra-high. Use `throughput-reviewer` when it
guarantees Sol-high. Agent-type names are conveniences; the model and reasoning
settings above are the invariant.

If the environment cannot guarantee the required model and reasoning level,
record that limitation in the PR and use the strongest available equivalent.
Do not silently substitute a weaker reviewer.

## Actors

1. **Orchestrator** — owns the goal, dependency graph, task assignment,
   integration, evidence ledger, CI monitoring, stopping decision, and PR
   lifecycle. It continues without waiting for human prompts.
2. **Terra-high implementers** — own disjoint files or narrowly defined
   responsibilities in isolated worktrees. They investigate, test, implement,
   validate, and return commits plus evidence.
3. **Sol-high reviewers** — one fresh reviewer at a time examines the current
   integrated diff. Reviewers do not edit code or inherit another reviewer's
   conclusions.

The orchestrator must remain available for coordination. Do not consume every
agent slot with workers.

## Autonomy contract

After the human supplies a bug, issue, or verifiable goal, the orchestrator
automatically:

- inspects repository instructions and preserves existing changes;
- resolves reasonable ambiguity from code, tests, history, and issue context;
- creates a concrete acceptance checklist;
- partitions work and launches all independent tasks concurrently;
- integrates worker commits;
- runs the sequential review/fix loop;
- triages findings under the policy below;
- dispatches parallel remediation;
- runs validation and monitors CI;
- posts PR evidence and leaves the PR merge-ready; and
- merges automatically only when repository policy and the user's initial
  authority permit it.

Do not ask a human to choose routine implementation details, approve ordinary
tests, relay agent output, initiate the next round, classify straightforward
findings, rerun CI, or copy commands between actors.

## Isolation and ownership invariants

Use one **integration worktree** for the PR branch and one isolated worktree per
mutating worker. Reviewers inspect the integration worktree read-only.

Prefer external per-user worktrees:

```bash
AGENT_WORKTREE_ROOT="${AGENT_WORKTREE_ROOT:-${XDG_STATE_HOME:-$HOME/.local/state}/agent-worktrees}"
PDD_AGENT_WORKTREE_DIR="$AGENT_WORKTREE_ROOT/promptdriven__pdd/<task-name>"
```

Rules:

- Each mutating worker receives explicit file or module ownership.
- No two concurrent workers may edit the same file.
- Workers must not revert or rewrite changes made by other workers.
- Shared contracts, central registries, generated artifacts, and files needed by
  multiple lanes belong to one designated integration owner.
- If newly discovered work overlaps another lane, the worker stops editing the
  overlap and informs the orchestrator. The orchestrator serializes or reassigns
  that portion; unrelated work continues.
- A worker returns small conventional commits. The orchestrator integrates them
  with `cherry-pick` in dependency order.
- Never use `git reset --hard`, `git checkout --`, `--force`, `--no-verify`, or
  amend as a coordination mechanism.
- Use `--force-with-lease` only when a legitimate rebase requires it and the
  remote state has been rechecked.

Existing or unrelated changes belong to the user. Preserve them.

## Concurrency policy

At every phase, the orchestrator builds a dependency graph and immediately
starts every ready node.

With nine available agent slots, keep one slot for the top-level orchestrator
and allocate the other eight by phase:

- Investigation: zero workers for low uncertainty, one or two for medium
  uncertainty, and up to four for high uncertainty.
- Implementation: up to seven Terra-high workers, normally leaving one slot
  free for newly discovered work or replacement.
- Review: one Sol-high reviewer at a time; unused slots remain available for
  independent reproduction of uncertain findings.
- Remediation: up to seven Terra-high workers when findings have disjoint
  ownership.

Fill all slots only when there are that many ready, independent nodes. Adapt to
available capacity and task shape; agents that would contend for ownership or
wait on the same prerequisite do not add useful parallelism.

Good parallel lanes include:

- reproduction, sibling-bug search, and relevant-history search;
- changes in independent modules;
- tests for independent behaviors;
- documentation and code changes with disjoint ownership;
- independent investigation of uncertain review findings;
- targeted test, lint, packaging, and safe end-to-end checks;
- remediation of findings in disjoint files.

Keep these sequential:

- a failing test before its corresponding fix;
- implementation that depends on an unresolved contract or API decision;
- integration before review of the integrated diff;
- remediation before the next review of that remediation;
- merge after all required checks and evidence gates.

`run_in_background: true` alone is not parallelization. Multiple independent
tasks must actually be dispatched before waiting.

## Autonomous workflow

### 0. Intake and verifiable goal

The orchestrator reads all applicable `AGENTS.md` files, checks the worktree,
collects the issue evidence, and records a lightweight internal task manifest.
Include only the fields needed for this change:

- observed failure or reproduction signal;
- desired externally observable behavior;
- explicit acceptance criteria;
- scope and non-goals;
- authority limits;
- expected end-to-end boundary;
- candidate files and likely ownership conflicts; and
- required CI checks.

Infer reasonable details from the repository. Escalate only when the missing
answer meets the human escalation policy.

### 1. Scale investigation to uncertainty

Do not launch a fixed investigation fleet. The orchestrator first classifies
uncertainty qualitatively:

- **Low uncertainty:** the failure is reproducible, localized, and follows a
  familiar pattern; acceptance criteria and the verification boundary are
  obvious. Launch no separate investigation worker. Let the implementation lane
  confirm the reproduction and proceed.
- **Medium uncertainty:** one or two important facts are unresolved, such as the
  root cause, sibling exposure, repository convention, or end-to-end boundary.
  Launch only the one or two lanes that resolve those unknowns.
- **High uncertainty:** the failure is intermittent, cross-cutting, newly
  introduced without an obvious cause, security/concurrency/persistence
  sensitive, or has unclear acceptance criteria or production boundaries.
  Launch up to four relevant Terra-high read-only lanes concurrently.

Available investigation lanes are a menu, not a checklist:

- **Reproduction** — reproduce the failure and identify the smallest reliable
  regression test.
- **Sibling-bug search** — search for the same anti-pattern, function, error, or
  call shape across the repository.
- **History/convention search** — inspect `git log`, `git blame`, and relevant
  prior fixes for the established implementation and test shape.
- **Boundary analysis** — identify the real CLI, workflow, provider, or
  integration path needed for end-to-end verification.

Suggested history commands:

```bash
git log --all --oneline --grep="<keyword>"
git log -S "<exact buggy snippet>"
git log --all --oneline -- <file>
git show <relevant-sha>
```

After each investigation batch, reassess uncertainty. Expand investigation only
when evidence conflicts or a safe implementation still depends on an unresolved
fact. Stop investigating as soon as the reproduction, acceptance criteria,
ownership, and verification plan are sufficient to implement safely. Never
launch a lane merely to fill an available agent slot.

The orchestrator consolidates any material investigation results and updates the
acceptance criteria. Post a separate investigation summary only when the
investigation changed scope, exposed sibling bugs, or established a non-obvious
convention; otherwise include the reproduction evidence in the final PR summary.
Do not ask a human to relay findings between agents.

### 2. Partition and dispatch

Partition the fix into the largest set of independent ownership lanes. Each
Terra-high implementer prompt must include:

- the full goal and acceptance criteria;
- its exact responsibility and owned files;
- known sibling occurrences and repository conventions;
- dependencies and interfaces it must preserve;
- other active lanes and the instruction not to revert their work;
- required targeted tests, lint, and end-to-end evidence;
- strict TDD and commit requirements; and
- a concise result schema: commits, files, tests, commands, outcomes, and risks.

If the work cannot be split safely, use one implementer rather than create
conflicting lanes. Maximize useful parallelism, not agent count.

### 3. Per-lane TDD implementation

Each implementer independently:

1. Confirms the assigned reproduction.
2. Writes a failing test first.
3. Runs it and captures the red output.
4. Commits the test separately with a `test(...)` conventional prefix.
5. Implements the smallest complete fix.
6. Runs targeted pytest and pylint until clean.
7. Exercises its safe end-to-end boundary when possible.
8. Commits the fix separately with a `fix(...)` prefix.
9. Returns commit SHAs and red-to-green evidence immediately.

Do not push a knowingly failing integration branch. Separate test and fix
commits preserve TDD evidence; integrate the pair together after both exist.

Prefer targeted commands:

```bash
pytest -vv tests/test_<module>.py::test_<behavior>
pylint pdd/<module>.py tests/test_<module>.py
```

Avoid `make lint` during iteration because it may reinstall dependencies. Do not
run broad regression suites unless they are part of the acceptance criteria.

### 4. Deterministic integration

As worker lanes finish, the orchestrator:

1. Inspects each returned commit and evidence.
2. Cherry-picks test/fix pairs into the integration worktree in dependency order.
3. Resolves only integration-owned conflicts. If resolution changes a worker's
   behavior, rerun that lane's tests.
4. Checks that the diff contains only intentional files.
5. Runs the combined targeted tests.
6. Pushes the PR branch and creates or updates a non-draft PR.

Integrate completed independent lanes while slower lanes continue when doing so
cannot invalidate their base. Do not wait unnecessarily for the entire batch.

After integration:

```bash
git status --short
git log origin/main..HEAD --oneline
gh pr diff <PR> --name-only
```

The tree must be clean, all commits must be intentional, and generated or
unrelated files must not appear unexpectedly.

### 5. Sequential review/fix loop

Run at most three sequential review rounds. Launch exactly one fresh Sol-high
reviewer per round, remediate that review before starting the next reviewer, and
stop early when a reviewer returns clean.

A round is consumed when its reviewer returns a verdict. A failed launch or
timed-out reviewer may be replaced without consuming a round.

Each reviewer inspects the whole current diff exhaustively. Give each round a
primary perspective so successive reviews add depth:

1. **Round 1 — correctness:** logic, state transitions, error handling, async
   and concurrency behavior, backward compatibility.
2. **Round 2 — verification:** regression-test strength, missing edge cases,
   acceptance-criteria coverage, and end-to-end fidelity.
3. **Round 3 — security/design:** trust boundaries, data loss, injection,
   permissions, unsafe side effects, and significant design flaws.

The perspective is an emphasis, not a restriction. Every round must report any
material correctness, security, verification, compatibility, or design problem
it finds.

Reviewer rules:

- Model must be `gpt-5.6-sol` with `high` reasoning.
- Review the integrated diff against `origin/main`.
- Remain read-only.
- Find all material findings in one pass.
- Review only the current code and evidence; do not inherit or merely confirm
  the previous reviewer's conclusions.
- Cite exact files and lines.
- Classify findings as P1 or P2 and provide a concrete proposed fix.
- Return a structured verdict to the orchestrator; the orchestrator posts one
  PR comment for that round.

Classification:

- **P1:** blocking correctness, security, silent corruption/data loss, broken
  acceptance criterion, or credible regression.
- **P2:** robustness, maintainability with operational consequence, or a
  reachable edge case that is not release-blocking.

Cosmetic preference without behavioral or maintenance consequence is not a
finding.

### 6. Autonomous triage and parallel remediation

The orchestrator deduplicates findings and applies this policy:

- P1: fix automatically.
- P2 with a reachable failure or inexpensive low-risk fix: fix automatically.
- P2 disproven by code, tests, or documented invariants: reject with evidence.
- P2 representing an unreachable or intentionally unsupported case: accept and
  document the trade-off.
- Uncertain findings: dispatch a short Terra-high reproduction task. Use its
  evidence to decide without involving a human unless an escalation condition
  applies.

Post a single response covering every finding before remediation begins. Then
partition accepted fixes by disjoint ownership and launch Terra-high remediation
workers concurrently. Each worker follows the same test-first discipline.

After integrating and validating remediation, start the next sequential review
round with a fresh Sol-high reviewer. A clean verdict ends the loop early.

If round 3 reports material findings, remediate them autonomously and run all
targeted validation, but do not merge: the resulting code has not received a
clean subsequent review within the three-round cap. Post the remaining evidence
and escalate one decision—authorize a fourth review or require human review.

### 7. Validation fan-out

Once the integrated diff is stable, run independent safe checks concurrently
where the environment permits:

- targeted pytest for all touched behaviors;
- pylint for touched Python modules and tests;
- relevant packaging or installation smoke checks;
- the real affected CLI or integration boundary;
- diff, commit, and worktree cleanliness checks; and
- any repository-required focused suite.

Do not treat unit tests, lint, CI, or review as a substitute for end-to-end
verification. Record the exact command and result in the PR.

If the live path requires real provider credentials, production effects, money,
or a long-running regression harness outside the initial authority, do not run
it. Use the closest safe local substitute and escalate only if that live result
is required to establish the goal.

### 8. CI monitoring and merge

The orchestrator monitors required checks without human polling:

```bash
gh pr checks <PR> --watch
```

For internal PRs, if `auto-heal` is the only failing or missing required check,
post `/heal` at column 1 and monitor the new run. `auto-heal` may push a commit;
fetch it, inspect it, rerun affected validation, and submit it to the same
sequential Sol-high review gate. If all three rounds have already been consumed,
leave merge blocked and escalate rather than silently exceeding the cap.

Diagnose ordinary CI failures automatically and dispatch Terra-high remediation
when they are caused by the PR. Retry an identified flaky infrastructure failure
once when repository policy allows. Do not repeatedly rerun unexplained failures.

When the stopping criteria are satisfied:

- If initial authority permits merging and branch policy allows it, enable
  auto-merge or merge once checks pass.
- Otherwise leave a merge-ready PR with a concise final evidence comment. This
  is the normal single human handoff.

Before merge:

```bash
git status                              # clean
git log origin/<pr-branch>..HEAD        # empty
gh pr checks <PR>                       # all required checks passing
```

Then, only when authorized:

```bash
gh pr merge <PR> --squash --delete-branch
```

Leave agent worktrees available for inspection after merge unless cleanup was
explicitly requested.

## Human escalation policy

Human attention is an exception. Escalate only when at least one condition is
true:

1. Two plausible interpretations would materially change user-visible behavior,
   scope, compatibility, or data semantics, and repository evidence cannot
   resolve the choice.
2. Completion requires credentials, spending money, a production mutation, a
   destructive or irreversible action, or authority not provided at intake.
3. A required check needs an external-state change the agents cannot perform.
4. Reviewer disagreement exposes a product or policy decision rather than a
   technical fact that a reproduction can settle.
5. The proposed fix must overwrite user-owned changes or expand into unrelated
   modules with significant blast radius.
6. Repository policy requires human approval or forbids autonomous merge.
7. The third review round found material issues, so confirming its remediation
   would require exceeding the automatic three-round cap.

When escalating, ask one concise decision question and include:

- the blocked acceptance criterion;
- evidence already collected;
- the smallest set of viable options;
- the recommended option and trade-off; and
- useful work that continued in parallel.

Do not escalate merely because work is difficult, a test failed, an agent timed
out, a reviewer found an issue, or another autonomous round is needed before the
three-round cap is reached.

## Stopping criteria

The loop is complete when all of these are true:

1. Every acceptance criterion has recorded evidence.
2. No P1 finding remains.
3. Every P2 is fixed, disproven with evidence, or documented as an accepted
   trade-off supported by repository behavior or an explicit invariant.
4. The most recent Sol-high reviewer returned clean, and no code changed after
   that verdict.
5. Targeted tests and lint pass.
6. The safe end-to-end boundary passes, or an explicitly required live path is
   documented as the sole escalation.
7. Required CI checks pass.
8. The branch is clean, pushed, and contains only intentional changes.

Stop early on a clean review. Never exceed three review rounds automatically.
If the third review is not clean, complete safe remediation and validation, then
leave the PR blocked under the escalation rule above.

## Dispatch templates

### Terra-high implementation worker

```text
Role: implementation worker
Model: gpt-5.6-terra
Reasoning: high
Isolation: dedicated worktree
Run: background

Goal:
<verifiable goal and acceptance criteria>

Ownership:
<exact files/modules/responsibility>

Parallel context:
<other active lanes and their ownership>
You are not alone in the repository. Do not edit files outside your ownership,
revert others' work, or resolve cross-lane conflicts yourself.

Process:
1. Confirm reproduction.
2. Add and run a failing regression test.
3. Commit test separately with test(...) prefix.
4. Implement the fix.
5. Run targeted pytest and pylint.
6. Run the assigned safe end-to-end check.
7. Commit fix separately with fix(...) prefix.

Return immediately when complete:
- test and fix commit SHAs;
- files changed;
- failing test command and red result;
- green validation commands and results;
- end-to-end evidence;
- overlap, assumptions, or remaining risk.
```

### Sol-high independent reviewer

```text
Role: independent adversarial reviewer
Model: gpt-5.6-sol
Reasoning: high
Mutation: forbidden

Review the complete integrated diff against origin/main from the assigned
perspective, while remaining alert to every material correctness, security,
verification, compatibility, and design issue.

Be exhaustive in one pass. Review the current diff independently rather than
inheriting the prior reviewer's conclusions. For each finding return:
- P1 or P2;
- one-line title;
- exact file and line;
- concrete failure mode;
- evidence or reproduction reasoning;
- smallest safe suggested fix.

Return "MERGE — no findings" when clean. Do not edit files, post partial results,
or wait for another reviewer.
```

### Orchestrator evidence comment

```markdown
## Autonomous PR loop evidence

**Goal:** <externally observable outcome>
**Verdict:** MERGE-READY | ESCALATION REQUIRED

### Acceptance criteria
- [x] <criterion> — <test, command, or evidence>

### Parallel execution
- Terra-high lane: <ownership> — <commits>
- Sol-high sequential rounds: <round, perspective, and verdict>

### Review disposition
- <finding>: FIXED | DISPROVEN | ACCEPTED — <evidence or rationale>

### Validation
- `<command>` — PASS

### Remaining human action
- None; auto-merge enabled.
  <!-- or the single precise escalation/merge approval required -->
```

## Repository-specific guardrails

- `unit-tests` runs on non-draft pull requests for `opened`, `synchronize`, and
  `ready_for_review`.
- `auto-heal` is required. A collaborator-triggered run requires `/heal` at
  column 1. Fork PRs cannot receive heal commits and normally conclude neutral.
- Review every commit produced by `auto-heal`; it is part of the PR diff.
- Run `git status --short` and inspect `git diff` after tests. Reject unintended
  changes to `architecture.json`, `prompts/`, `pdd/`, or `examples/`.
- Prefer focused tests in worker worktrees. Run broad suites only in a designated
  validation lane or CI when the task requires them.
- Never commit credentials, cache databases, generated secrets, or unredacted
  provider logs.
