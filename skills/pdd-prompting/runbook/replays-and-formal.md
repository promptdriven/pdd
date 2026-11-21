# Runbook: Code Space Replays and the Formal Check

> Deep reference for [RUNBOOK.md](../RUNBOOK.md).

## 17. Code space: replay evidence and the formal check

**Agent limit recovery:** On `agent thread limit reached`, follow the workflow skill's checking fallback: close finished subagents if supported, then try a fresh checker first. Only after fresh startup failure may verify/formal reuse an agent that wrote no code, tests or prompts in this run. If no eligible checker can run:
- For review, write `Not checked: review (agent limit)` in the review run file; review always needs a fresh agent, never a reused checker.
- For another unrun check, write `Not checked: <step> (agent limit)` in its run file.
Stop and tell the person to start a new agent session in the run's worktree (`pdd workflow open 42` focuses or resumes the same session; it does not start a new one or clear the limit). No verdict or `workflow done` for unrun checks. Only after the check actually runs, replace its `Not checked:` line with the real result in the step's run file and any copy in `verify.md`; never keep both.

**Old-code proof & CLI replay:** For CLI entries, `pdd test --target code` executes Story scenarios against native code. In `verify` after the last commit, run `pdd workflow prove <run> --test "<cmd>" --expect "<failing text on old code>"` (include dependency install in fresh worktrees).

**Test vectors (approved cases on real code):**
- Use `tests/<story>.json` from prompt space as-is. Never edit it in code space.
- Write one native replay test (`test/<story>.vectors.test.mjs`) calling the real public boundary for each step in order. Parse whole numbers outside `±(2^53-1)` exactly with `JSON.parse` `context.source` → `BigInt`, compare integer results as `BigInt`, and map `result`, `error`, `world`, and `calls` (unmapped targets are `"Not replayed"` with reason—never a pass).
- In `verify`, run the replay test, then run it against a throwaway copy with ONE planted mistake (or old code in bug runs): at least one assertion must fail; A crash does not count.
- Write the table into `verify.md` (`case, criterion, input, expected, prompt check, code (got), result`) and confirm `tests/<story>.json` is unchanged since prompt space.
- Finish initial build, verify, and formal with fresh independent review; allow at most 2 repair rounds back to `build`, then verify, formal, and fresh review. The code-space PR keeps the actual `Review:` verdict and remaining must-fix list at the top, plus `"✗ N vectors fail"` if vectors still fail. Never edit expected values to force a pass.

**The formal check (done by an agent that did not write the code):**
- Every code-space PR has a "Formal check" section with one result: **Proved (bounded)**, **Proved (solver)**, **Failed + counterexample**, **Not run + reason**, or **Not applicable + reason**.
- Take the rule from touched `.prompt.md` `## Domain decisions` or the Story's `## Rules to check` (never from code).
- Default: **bounded check** looping over EVERY input in a stated range against an oracle from the Story; use a solver (Z3 or CrossHair) when the range is too large, replaying counterexamples and 2 witnesses on real code.
- Control: the planted mistake must fail the formal check too (not a crash); otherwise record `"Not run: the check cannot see the mistake"`. Commit replay/formal tests normally; Do not commit raw logs.

**Structured record (`<run-folder>/replay-evidence.json`):**
Write/update `<run-folder>/replay-evidence.json` per `docs/replay-evidence.md` (run ID, Git-visible content fingerprint, original vector hashes, per-check outcomes, mutation control, typed `formal` result with `scope`/`reason`). Never commit it or raw logs. Prompt-space publication freezes `replayBaseline` on entry into code space (plus linked approved base scenarios); missing, malformed, or stale evidence shows **BLOCKED** / **NOT REPLAYED** on the PR.

**Real-host verification for `kind: native-only` and OS-boundary modules:**
Codegen PRs that modify `kind: native-only` modules or OS/process/TTY/sandbox boundary code require an executable, non-mocked real-host smoke/integration test or `--live-local` / real-binary probe before merge. Mocked unit helpers, argv-prefix assertions, or uninstantiated DI shells fail closed (`needs-real-host-smoke`) and never prove real host behavior. Verify every applicable host boundary class directly on the host:
- **Nested OS sandbox execution:** Run a real child process inside the active host OS sandbox rather than asserting only mocked launch-prefix arguments (catches host kernel denials such as `sandbox_apply: Operation not permitted`, `rc=71`).
- **Real host device/TTY ownership:** Probe `/dev/tty` and actual host kernel UID/permission metadata directly rather than mocking the TTY check helper (catches root-owned kernel aliases such as `st_uid == 0` on non-root hosts).
- **Multi-turn real CLI state side effects:** Execute at least two sequential turns (Turn 1 → Turn 2) of the real CLI binary inside an isolated home directory and verify on-disk state and containment across turns rather than relying on single-turn or stubbed calls.
- **Full-size realistic payload handling:** Exercise un-truncated boundary payloads strictly larger than `4 KiB` (for example `12 KiB` realistic CLI/wire responses) rather than tiny synthetic fixtures that hide fixed preview-truncation defects.
