## Step 9: Implement Changes

**Status:** Changes Applied

### Files Modified
FILES_MODIFIED: pdd/prompts/checkup_review_loop_python.prompt, pdd/prompts/agentic_checkup_python.prompt, README.md

### Summary of Changes

#### `README.md`
- Updated the `checkup` command options documentation to mention the `reviewer_fallback` functionality.
- Updated the `Review-Loop Mode` paragraph to mention that diagnostic details are surfaced in the final report and the configured fixer is promoted dynamically when the primary reviewer encounters a critical failure.

#### `pdd/prompts/checkup_review_loop_python.prompt`
- Updated `ReviewLoopConfig` requirement to include `reviewer_fallback: bool` (default `True`).
- Updated `ReviewResult` and `ReviewLoopState` to capture `status_reason`, `exit_code`, `stderr_tail`, and `error_class` from the reviewer subprocess.
- Added requirement to bubble up these diagnostics to the final report.
- Added requirement for loop semantics to implement promote-on-failure when primary reviewer ends in a `HARD_NOT_CLEAN` state.

#### `pdd/prompts/agentic_checkup_python.prompt`
- Updated `run_agentic_checkup` function signature to include `reviewer_fallback: bool = True`.
- Updated requirement to map `reviewer_fallback` onto `ReviewLoopConfig` when dispatching.

### Worktree Location
Changes are in: `/tmp/pdd_job_R9j1GUPFRPgK4kQfD6Ht_aflmqdbo/.pdd/worktrees/change-issue-922`

### Next Steps
After review, run `pdd sync` on modified prompts to regenerate code.

---
*Proceeding to Step 10: Identify Issues*
