## Step 7: Prompt Classification

**Classification:** Prompt Defect

DEFECT_TYPE: prompt
PROMPT_FIXED: pdd/prompts/sync_orchestration_python.prompt

### Analysis
The code correctly implements the prompt's 5-consecutive-fix loop break logic, but the prompt lacks instructions to track zero-cost no-op iterations. Similarly, the `sync_determine_operation` prompt lacks instructions to validate `run_report` staleness before recommending fix/crash operations. The prompts themselves were missing the requirements necessary to handle these edge cases correctly.

### Evidence
- **Prompt specifies:** "Consecutive fix operations: Break after 5" and makes no mention of checking run_report staleness for crash/fix decisions.
- **Code implements:** Code breaks after 5 consecutive fixes without checking cost, and recommends fix/crash without validating if the run_report hashes match current files.
- **User expects:** The circuit breaker should abort after 2 consecutive $0 cost (no-op) fixes, and the operations recommender should validate run_report staleness before repeatedly recommending fixes.

### Prompt Change Made
**File:** `pdd/prompts/sync_orchestration_python.prompt`

**Before:**
```markdown
- Consecutive fix operations: Break after 5
- Consecutive test operations: Break after `MAX_CONSECUTIVE_TESTS` (3)
- Consecutive crash operations: Break after `MAX_CONSECUTIVE_CRASHES` (3)
```

**After:**
```markdown
- Consecutive fix operations: Break after 5. In addition, track consecutive no-op fix iterations (where actual_cost == 0.0 and model == ""); reset on a real LLM call, and abort after 2 consecutive no-ops with a distinct error message.
- Consecutive test operations: Break after `MAX_CONSECUTIVE_TESTS` (3). Also track consecutive no-ops and abort after 2.
- Consecutive crash operations: Break after `MAX_CONSECUTIVE_CRASHES` (3). Also track consecutive no-ops and abort after 2.
```

**File:** `pdd/prompts/sync_determine_operation_python.prompt`

**Before:**
```markdown
    -   **Unparseable output**: `tests_passed=0`, `tests_failed=0`, `exit_code=0` → accept as `all_synced` (confidence=0.70).
```

**After:**
```markdown
    -   **Unparseable output**: `tests_passed=0`, `tests_failed=0`, `exit_code=0` → accept as `all_synced` (confidence=0.70).
    -   **Staleness**: Must validate `run_report` staleness (hash matching) before recommending `fix` based on `tests_failed > 0` or recommending `crash` based on `exit_code != 0`.
```

### Conclusion
The prompt specification was incorrect. The prompt has been fixed. Proceeding with test generation based on the corrected specification.

---
*Proceeding to Step 8: Test Plan*
