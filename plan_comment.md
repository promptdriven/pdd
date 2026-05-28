## Step 8: Test Plan

### Existing Test Coverage
- **Test files:** `tests/test_sync_orchestration.py`, `tests/test_sync_determine_operation.py`
- **Current coverage:** Existing tests for `sync_orchestration.py` verify loop termination logic on `MAX_CONSECUTIVE_FIXES` (5) but do not track `0.0` cost no-op iterations. Tests for `sync_determine_operation.py` parse `run_report` state but do not enforce file hash staleness validation before acting on `tests_failed` or `exit_code`.
- **Gap:** Missing tracking for no-op zero-cost iterations across `fix`, `test`, and `crash` loops (which currently artificially inflate the consecutive operation counts). Missing staleness validation for `run_report` in `sync_determine_operation.py` (which currently recommends operations based on stale, mismatched files).

### Proposed Tests

#### Test 1: test_issue1200_noop_fix_trips_consecutive_fix_breaker
- **Input:** `fix` operations return `actual_cost == 0.0` and `model == ""`.
- **Expected:** Orchestrator aborts with a distinct error message about consecutive no-ops, NOT the misleading "consecutive fix" message.
- **Actual (before fix):** Exits with misleading "MAX_CONSECUTIVE_FIXES" message.

#### Test 2: test_issue1200_noop_fix_calls_fix_main_4_times_before_breaker
- **Input:** `fix` operations return `actual_cost == 0.0` and `model == ""`.
- **Expected:** `fix_main` is called exactly 2 times (early abort).
- **Actual (before fix):** `fix_main` is called 5 times.

#### Test 3: test_issue1200_noop_fix_loop_zero_cost_and_early_abort
- **Input:** Continuous zero-cost `fix` operations.
- **Expected:** Orchestrator loop aborts early; total tracked cost is exactly $0.

#### Test 4: test_issue1200_noop_fix_log_entries_count_reflects_early_abort
- **Input:** Continuous zero-cost `fix` operations.
- **Expected:** Output channel integrity (Python logging and Rich output) verifies exactly 2 no-op entries are logged, ensuring no silent loop-spinning.

#### Test 5: test_issue1200_stale_state_skip_flags_exhausts_consecutive_fix_breaker
- **Input:** Stale `run_report.json` with `tests_failed > 0` but a recorded file hash that does NOT match current files.
- **Expected:** `sync_determine_operation` validates staleness, ignores the stale report, and does NOT recommend `fix`.

#### Test 6: test_issue1200_single_noop_then_real_fix_succeeds
- **Input:** 1 no-op fix (`actual_cost == 0.0`), followed by 1 real fix (`actual_cost > 0.0`), followed by 1 no-op fix.
- **Expected:** Regression guard passes. The no-op tracker resets on the real fix, allowing the loop to continue normally.

#### Test 7: test_issue1200_real_fix_then_noop_aborts_after_2_noop_iterations
- **Input:** 1 real fix (`actual_cost > 0.0`) followed by 2 no-op fixes (`actual_cost == 0.0`).
- **Expected:** Orchestrator loop aborts exactly after the 2 consecutive no-op iterations.

#### Test 8: test_issue1200_stale_run_report_crash_validation
- **Input:** Stale `run_report.json` with `exit_code != 0` but a recorded file hash that does NOT match current files.
- **Expected:** `sync_determine_operation` validates staleness, ignores the stale report, and does NOT recommend `crash`. (Expansion item).

#### Test 9: test_issue1200_fresh_run_report_fix_and_crash_validation
- **Input:** Fresh `run_report.json` with matching file hash, containing both `tests_failed > 0` and `exit_code != 0`.
- **Expected:** `sync_determine_operation` correctly recommends operations because the report is not stale. (Regression prevention for Expansion items).

#### Test 10: test_issue1200_noop_test_aborts_after_2_iterations
- **Input:** `test` operations return `actual_cost == 0.0` and `model == ""` continuously.
- **Expected:** Orchestrator loop aborts after exactly 2 consecutive no-op `test` iterations. (Expansion item).

#### Test 11: test_issue1200_noop_crash_aborts_after_2_iterations
- **Input:** `crash` operations return `actual_cost == 0.0` and `model == ""` continuously.
- **Expected:** Orchestrator loop aborts after exactly 2 consecutive no-op `crash` iterations. (Expansion item).

### Test Location
- **File:** `tests/test_sync_orchestration.py` (append) and `tests/test_sync_determine_operation.py` (append)
- **Framework:** pytest

### Notes
All tests are behavioral. To avoid structural testing, we will mock the dependencies (`fix_main`, `test_main`, `crash_main`) to simulate actual return values (`actual_cost`, `model`) and assert against observable side effects (logger output, execution flow, early exit exceptions, and exact loop call counts). Similarly, `run_report` parsing tests will assert on the resulting `SyncDecision` returned rather than introspecting internal function signatures.

---
*Proceeding to Step 9: Generate Test*