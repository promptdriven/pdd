# Runbook: Code Space Replays and the Formal Check

> Part of [RUNBOOK.md](../RUNBOOK.md) — see the router table in `../RUNBOOK.md` for other `§N` sections.

## 17. Code space: replay evidence and the formal check

On `agent thread limit reached`, follow the workflow skill's checking fallback. Before checking, close finished subagents if supported, then try a fresh checker first. Only after fresh startup failure may verify/formal reuse an agent that wrote no code, tests or prompts in this run. If no eligible checker can run:

- For review, write `Not checked: review (agent limit)` in the review run file; review always needs a fresh agent, never a reused checker.
- For another unrun check, write `Not checked: <step> (agent limit)` in its run file.

Stop and tell the person to start a new agent session in the run's worktree. No verdict or `workflow done` for unrun checks.
`pdd workflow open 42` focuses or resumes the same session; it does not start a new one or clear the limit.
Only after the check actually runs, replace its `Not checked:` line with the real result in the step's run file and any copy in `verify.md`; never keep both.

Code space is the PDD compiler: your agent writes the code from the approved prompts, and the same tests run on that code.
For CLI entries with a declared implementation, `pdd test --target code` executes
the same Story cases and records the results with the commit. Unsupported steps
are not run and cannot pass. Agents replay other approved prompt-space cases
against the real code using native tests. Checks of prompts on the PDD interpreter
do not establish that the code behaves the same. For agent-supplied replay
evidence, pdd validates structure and identity; it does not independently prove
execution or prompt/code equivalence.

In verify after the last commit, run one `pdd workflow prove <run> --test "<command>" --expect "<distinctive text printed by the failing test on old code>"` command that covers all new or changed tests; text the old-code run does not print gives `wrong-reason`. Its line goes on the PR. Fresh worktrees have no installed dependencies, so include any required installation in the command.

**Test vectors: the approved cases, run on the real code.**
- Use `tests/<story>.json` from prompt space as it is. Never edit it in code space. If an expected value looks
  wrong, return to prompt space for the person's approval and start a run with the approved vectors.
- In `build`, write one replay test in the repo's own test runner (for example `test/<story>.vectors.test.mjs`).
  It reads the JSON file when it runs, and for each step it calls the real public boundary named by `operation`
  (function, command or route). Steps run in order and share state, as on the interpreter.
- Read whole numbers exactly. `JSON.parse` rounds a whole number above 2^53 without a sign; read the file with
  `JSON.parse(text, (key, value, context) => typeof value === 'number' && /^-?(?:0|[1-9][0-9]*)$/.test(context.source) && !Number.isSafeInteger(value) ? BigInt(context.source) : value)`.
  Give a Number parameter `Number(value)` only when `BigInt(Number(value)) === value`; otherwise the case fails.
  Compare an integer result as a BigInt. See [exact whole numbers](https://github.com/promptdriven/pdd/blob/main/docs/replay-evidence.md#exact-whole-numbers).
- Map each check target: `result` → the returned value at the path; `error` → the error code; `world` → the app's
  store after the step, seeded from `initial_world`; `calls` → a spy count. A target you cannot map is
  "Not replayed", with the reason. It is never a pass. Missing checks and unexecuted operations are not replayed.
- In `verify`, run the replay test. Then run it again on a throwaway copy with ONE planted mistake (in a bug run:
  the old code). At least one assertion must fail there. A crash does not count. After a merge from the base, the old
  code is the code at the new merge base: when no assertion fails there, the base already holds the fix.
- Write the table into `verify.md`: case, criterion, input, expected, prompt check, code (got), result.
  Also show that `tests/<story>.json` is unchanged since prompt space.
- In bug and feature, finish the initial build, verify and formal steps with fresh independent review.
  After the initial review, a ✗ case or review must-fix goes back to `build` (at most 2 repair rounds),
  then verify, formal and fresh review. The code-space PR keeps the actual `Review:` verdict and remaining
  must-fix list at the top, plus "✗ N vectors fail" if vectors still fail. No new human gate.
  Keep actual failures; never change expected values to get a pass.

**The formal check (done by an agent that did not write the code).**
- Every code-space PR has a "Formal check" section with one result: **Proved (bounded)**, **Proved (solver)**,
  **Failed + counterexample**, **Not run + reason** or **Not applicable + reason**.
- Use it for a precise rule with a clear forbidden result: money and rounding, limits, who may do what,
  order of states, parsers. It is not applicable for looks, wording or plain wiring.
- Take the rule from the approved Story's `## Rules to check` section. Never take it from the code.
- Default method: a **bounded check**. Loop over EVERY input in a small, stated range, call the real code, and
  compare with an oracle written from the Story. State the bounds in the PR.
- Use a solver (Z3, or CrossHair for Python) only when the range is too big to loop. Replay each counterexample
  and 2 witnesses on the real code.
- Control: the planted mistake must fail the formal check too. If it does not, write "Not run: the check cannot
  see the mistake". A crash is not assertion detection. With no scenario vectors, put the control in the formal
  block: `control_command` and its nonzero `control_exit_code`.
- Commit the replay test and the formal test as normal tests. Do not commit raw logs.

**Structured record for a workflow run.**
New bundled feature/bug code areas opt in with `replay_evidence: "pdd.replay-evidence.v1"`. Saved areas and
custom workflows without that field keep their publication behavior; small-change has no replay policy.
For ordinary runs, after each prompt-space publication or push, pdd refreshes the changed scenario files, their original byte
hashes and step/check identities in `status.json` as `replayBaseline`, including empty or blocked selections.
This continues through the final approval publication before code space. Final approval refuses unpublished
scenario edits; publish approved edits in prompt space first. On entry into code space the published anchor
freezes; a code-space retry cannot replace it. No selected vectors means not replayed. The anchor also holds the approved scenario files on the base branch that link to the changed files (`story_path`, step `entry_path`, `pdd-bindings.json`, or a changed file's `Generated from PATH.prompt.md` header); pdd reads them from the base commit. With `{"replay":{"base_scenarios":"all"}}` in the base `pdd.json`, it holds all of them. Expect to write a replay test for each; pdd does not write or run these tests itself. A run without a prompt area builds this part in code space. The PR line counts files and checks by source, for example `Anchor: 3 changed scenarios (40 checks) + 18 linked approved on base 6b58b76 (1,722 checks).` They give no pass by themselves: replay every anchored check. Adopted runs instead keep their frozen declared scenario inventory, bytes and authority through prompt publication, code entry and every retry; publication never refreshes that adopted anchor.
pdd reads the formal block on its own, also with no selected vectors. The PR shows its status: recorded,
missing, malformed (FIELD) or stale (source changed), with the reason and one repair step. When a Story has
`## Rules to check`, the code PR is not ready to merge until the formal status is recorded with Proved or Not applicable.

Before completing each code-space step, the agent writes `<run-folder>/replay-evidence.json`; update it
with the formal result after that step. Use the versioned contract in the package's `docs/replay-evidence.md`.
It records the run ID, current Git-visible content fingerprint, every original vector hash, per-check outcomes,
public-boundary executions, exact counts, a semantic mutation control and a typed formal result with scope and
reason. Keep this JSON in the run folder, outside the Git-visible source; never commit it or raw logs.
Missing/unmapped checks need honest not-replayed outcomes, and a control that was not run needs a reason.

pdd revalidates immediately before publishing, after committing leftovers, and when updating an open PR.
It independently inventories current changed scenario files against the saved run base with exact
NUL-delimited Git paths, including non-ASCII names. A scenario absent from the frozen anchor makes replay
BLOCKED even when all anchored checks pass; an unavailable inventory cannot establish PASS.
Changed, absent, empty or unreadable original files cannot pass even with a new source fingerprint. Missing,
malformed or stale records produce prominent **BLOCKED** / **NOT REPLAYED** status above prose and prompt
check results. Actual assertion or formal failures remain publishable with a failure line. An existing PR is
marked publication-pending before source is pushed; a failed final description update leaves it pending.
A structurally valid agent-reported replay pass can coexist with an explicit formal **Not run** or
**Not applicable**; neither means a formal proof. Read the counts, scope, reason and trust boundary together.
