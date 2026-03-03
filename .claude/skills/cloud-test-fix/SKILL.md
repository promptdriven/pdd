---
name: cloud-test-fix
description: Run pdd cloud tests and iteratively fix failures using TDD
allowed-tools: Bash, Read, Edit, Write, Grep, Glob, Agent
---

# Cloud Test Fix Loop

Run `make cloud-test`, stream failures in real-time, fix them using TDD (write a failing local test first, then fix), and re-run until the full suite is green.

## IMPORTANT: Only committed code is tested

Cloud Batch uses `git archive HEAD` to create the source tarball. Uncommitted changes are NOT tested. The skill must always check for this and warn.

## Step 1: Pre-flight

1. Run `git status` to check for uncommitted changes (staged or unstaged)
2. If there are uncommitted changes, **warn the user**:
   ```
   WARNING: You have uncommitted changes. Cloud tests only test committed code (git archive HEAD).
   Uncommitted files will NOT be tested.
   ```
   Then ask: "Would you like me to commit these changes first?"
3. If the user confirms, commit the changes before proceeding

## Step 2: Launch the cloud test run

Run `make cloud-test` in the background using `Bash` with `run_in_background: true`. Save the task ID.

Print to the user: "Cloud test run launched. Streaming failures as they arrive..."

## Step 3: Stream and fix failures (TDD)

Monitor the background task output periodically using `TaskOutput` with `block: false` to check for new output.

### Failure detection

As output streams in, watch for these patterns:
- `!! FAILURE: Task N (suite / detail) !!` — a task failed, followed by its log output
- The final results report at `test-results/cloud-batch-results.md`

### Task layout (73 tasks total)

| Task Range | Suite | Description |
|-----------|-------|-------------|
| 0-31 | pytest | Unit test chunks (32 shards) |
| 32-53 | regression | Regression test cases (22 cases) |
| 54-63 | sync_regression | Sync regression tests (10 cases) |
| 64-71 | cloud_regression | Cloud regression tests (8 cases) |
| 72 | vitest | Frontend Vitest tests |

### Fixing failures with TDD

For each failure detected:

1. **Extract failure details**: task number, suite, detail, and error output from the streamed `!! FAILURE:` block
2. **Read the full failure log** if available (check `TaskOutput` or `test-results/cloud-batch-results.md` after completion)
3. **TDD — Write a failing local test first**:
   - For pytest failures: read the failing test, understand the assertion, write a minimal local test that reproduces the issue, run `pytest -vv tests/test_file.py::test_name` to confirm it fails
   - For regression failures: read the regression case (`tests/regression.sh CASE_NUM`), understand what it tests, write a pytest test that captures the same failure
   - For vitest failures: read the failing frontend test, reproduce locally with `cd pdd/frontend && npx vitest run`
4. **Fix the code** to make the local test pass
5. **Verify locally** with `pytest -vv` (or `npx vitest run` for frontend)
6. Spawn `general-purpose` Agents to fix independent failures concurrently

### Important guidelines

- Group related failures (same root cause across multiple shards/cases) into a single fix
- For pytest failures: look at both the test file and the implementation under test
- For regression failures: the case number maps to `tests/regression.sh CASE_NUM` (case_N where N = task_index - 32)
- For sync_regression: case number = task_index - 54 + 1
- For cloud_regression: case number = task_index - 64 + 1
- Do NOT try to fix infrastructure/timeout issues — flag them to the user

## Step 4: Re-run until green

After all fixes from the current cycle are applied:

1. Summarize what was fixed: list each failure and the fix applied
2. **Commit the fixes** (since only committed code is tested)
3. Ask the user: "Fixes committed. Ready to re-run cloud tests?"
4. On confirmation, go back to Step 2 and repeat
5. Continue until all tasks pass (or the user stops the loop)

## Key files

- `ci/cloud-batch/submit.sh` — uploads source tarball + submits Cloud Batch job + polls + streams failures
- `ci/cloud-batch/entrypoint.sh` — task dispatcher (pytest chunks, regression, sync_regression, cloud_regression, vitest)
- `ci/cloud-batch/collect-results.sh` — downloads results from GCS, generates `test-results/cloud-batch-results.md`
- `ci/cloud-batch/job-template.json` — Cloud Batch job spec
- `test-results/cloud-batch-results.md` — final results report with per-task table and failure logs

## Output format

When reporting to the user, use this format:

```
## Cloud Test Run #N

### Failures detected (X/73 tasks failed)

| Task | Suite | Detail | Error Summary | Fix Status |
|------|-------|--------|--------------|------------|
| 5 | pytest | chunk_5 | AssertionError in test_foo | Fixed — corrected expected value |
| 38 | regression | case_6 | Exit code 1 in generate | Fixing... |

### Still running
- 45/73 tasks complete
```
