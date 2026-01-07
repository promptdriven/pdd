# PDD Sync Command: Architecture Analysis

## Executive Summary

The `pdd sync` command is a **state machine-based orchestrator** that coordinates 8 operations (auto-deps, generate, example, crash, verify, test, fix, update) to keep code synchronized with prompts. After thorough analysis of ~3000 lines of code across 5 key files, we identified **27 distinct bugs** that cause unpredictable behavior.

**Root Cause**: The system behaves like a finite state machine but states and transitions are **not explicitly defined**. Instead, they're encoded as 615 lines of nested if-else chains in `sync_determine_operation.py`.

---

## 1. Architecture Overview

### 1.1 Core Components

| Component | File | Lines | Purpose |
|-----------|------|-------|---------|
| CLI Entry | `commands/maintenance.py` | 14-101 | Command registration |
| Main Wrapper | `sync_main.py` | 79-345 | Language detection, orchestration |
| **Decision Function** | `sync_determine_operation.py` | 829-1444 | **Core problem: 615 lines of heuristics** |
| Worker Loop | `sync_orchestration.py` | 739-1038 | Executes operations, cycle detection |
| State Tracking | Fingerprint (`.pdd/meta/*.json`) | N/A | 4-file hash tracking |
| Outcome Logging | RunReport (`.pdd/meta/*_run.json`) | N/A | Test results, exit codes |

### 1.2 State Inputs (5 Categories)

```
+-------------------------------------------------------------------+
|                      DECISION INPUTS                              |
+-------------------------------------------------------------------+
| 1. File Hashes (4 files x 2 states = 16 combinations)             |
|    - prompt_hash, code_hash, example_hash, test_hash              |
+-------------------------------------------------------------------+
| 2. File Existence (4 files x 2 states = 16 combinations)          |
|    - prompt, code, example, test: exists/missing                  |
+-------------------------------------------------------------------+
| 3. RunReport (outcome log)                                        |
|    - exists/missing, exit_code, tests_passed/failed               |
|    - coverage, test_hash (staleness detection)                    |
+-------------------------------------------------------------------+
| 4. Fingerprint (last operation state)                             |
|    - command: auto-deps/generate/example/crash/verify/test/fix    |
|    - timestamp: relative to run_report                            |
+-------------------------------------------------------------------+
| 5. Operation History (in-memory during sync session)              |
|    - Arbitrary sequence of operations (for cycle detection)       |
+-------------------------------------------------------------------+

Theoretical State Space: 16 x 16 x 8 x 8 x 4 = 32,768 states
```

### 1.3 Available Operations

| # | Operation | Purpose | Trigger |
|---|-----------|---------|---------|
| 1 | auto-deps | Resolve `<include>`, `<web>`, `<shell>` dependencies | Prompt has dependency markers |
| 2 | generate | Create code from prompt | Prompt changed or code missing |
| 3 | example | Create usage example from code | Code exists, example missing |
| 4 | crash | Fix runtime crashes in example | Example crashes (exit_code != 0) |
| 5 | verify | Verify example runs correctly | After crash fix |
| 6 | test | Generate and run unit tests | Example verified, tests missing |
| 7 | fix | Fix code bugs found by tests | Tests fail |
| 8 | update | Sync code changes back to prompt | Code changed (by user) |

### 1.4 Decision Tree Structure (Priority Order)

```
TIER 1: Runtime Signals (if run_report exists) - Lines 872-1018
+-- fingerprint.command == 'crash' + exit_code != 0 -> CRASH (retry)
+-- fingerprint.command == 'crash' + exit_code == 0 -> VERIFY
+-- tests_failed > 0 -> FIX
+-- exit_code != 0 + example success history -> FIX
+-- exit_code != 0 + no history -> CRASH
+-- coverage < target -> TEST

TIER 2: No Fingerprint (new unit) - Lines 1025-1066
+-- prompt exists + has dependencies -> AUTO-DEPS
+-- prompt exists + no dependencies -> GENERATE
+-- no prompt -> NOTHING

TIER 3: Validate Expected Files - Lines 1068-1081
+-- Files missing that should exist -> _handle_missing_expected_files()

TIER 4: Hash Comparison - Lines 1083-1094
+-- Detect changes: prompt/code/example/test

TIER 5: No Changes - Workflow Progression - Lines 1096-1246
+-- _is_workflow_complete() -> NOTHING
+-- All files exist + no run_report -> CRASH
+-- All files exist + exit_code != 0 -> CRASH
+-- All files exist + verify not done -> VERIFY
+-- All files exist + stale run_report -> TEST
+-- Code exists + example missing -> EXAMPLE
+-- Code + example exist + test missing -> (crash/verify/test sequence)
+-- Code missing -> GENERATE

TIER 6: Single File Changed - Lines 1295-1365
+-- prompt changed -> AUTO-DEPS or GENERATE
+-- code changed -> UPDATE
+-- test changed -> TEST
+-- example changed -> VERIFY

TIER 7: Multiple Files Changed - Lines 1367-1430
+-- prompt in changes -> ANALYZE_CONFLICT (LLM)
+-- code in changes -> VERIFY
+-- example in changes -> VERIFY
+-- test in changes -> TEST

TIER 8: Fallback - Lines 1432-1444
+-- NOTHING (confidence=0.50)
```

---

## 2. Identified Bugs (27 Total)

### 2.1 CRITICAL Bugs (Prevent Core Functionality)

| Bug # | Name | Location | Impact |
|-------|------|----------|--------|
| **11** | Fingerprint Saved When Skipped | `sync_orchestration.py:857,864,871` | Records skipped ops as completed, state machine makes wrong decisions |
| **23** | Verify Check Via Fingerprint Only | `sync_determine_operation.py:732-734` | skip_verify creates false completion record |
| **8** | Silent Exception in Post-Crash | `sync_orchestration.py:1117` | `except: pass` hides verification failures |
| **4** | Hardcoded Cycle Count | `sync_orchestration.py:793-800` | `cycle_count = 2` always triggers immediately |

### 2.2 HIGH Severity Bugs (Cause Incorrect Behavior)

| Bug # | Name | Location | Impact |
|-------|------|----------|--------|
| **5** | Fingerprint Saved Without Validation | `sync_orchestration.py:1086` | Records success before files verified |
| **9** | Conditional Run Report Creation | `sync_orchestration.py:1000-1010` | No run_report when test file not created |
| **10** | Missing Run Report After Fix | `sync_orchestration.py:1120-1130` | No proof fix succeeded |
| **27** | Test Success Heuristic | `sync_orchestration.py:1062` | Success = file exists, not actual result |
| **26** | Inconsistent Return Handling | `sync_orchestration.py:1057-1089` | Different ops return different formats |
| **1** | Lock Window Race | `sync_orchestration.py:755-774` | State can change between lock and check |
| **12** | No Operation Output Validation | `sync_orchestration.py:909-913` | Silent operation failures |

### 2.3 MEDIUM Severity Bugs (Reduce Reliability)

| Bug # | Name | Location | Impact |
|-------|------|----------|--------|
| **2** | Budget Over-spend | `sync_orchestration.py:759-761` | Ops can exceed budget |
| **3** | Weak Auto-deps Cycle Detection | `sync_orchestration.py:781-787` | Alternating cycles not caught |
| **6** | Null Hash Handling | `sync_determine_operation.py:1086-1094` | False change detection |
| **7** | Run Report Deleted After Generate | `sync_orchestration.py:913` | State baseline lost |
| **13** | Crash Detection Uses Wrong Logic | `sync_orchestration.py:950` | Manual run differs from test logic |
| **14** | No Verify Run Report | `sync_orchestration.py:995-999` | Verify completion not tracked |
| **15** | Stale Error Content in Fix | `sync_orchestration.py:1012-1049` | Fixing wrong errors |
| **16** | No Result Validation After Fix | `sync_orchestration.py:1011-1050` | Assumes fix succeeded |
| **17** | Update Doesn't Invalidate Fingerprint | `sync_orchestration.py:1051-1052` | Workflow stops after update |
| **18** | Contradictory State in Test Failures | `sync_determine_operation.py:919-952` | Test file missing despite failures |
| **19** | Success History Heuristic Fragile | `sync_determine_operation.py:956-986` | Wrong crash vs fix decision |
| **20** | Coverage Check With skip_tests | `sync_determine_operation.py:988-1004` | Marks incomplete as complete |
| **21** | Missing File Handler Incomplete | `sync_determine_operation.py:1070-1081` | Optional files not detected |
| **22** | Incomplete Workflow Not Detected | `sync_determine_operation.py:1083-1110` | Missing steps not caught |
| **25** | Example Success History Fragile | `sync_determine_operation.py:1186-1229` | Crash re-run logic fragile |

### 2.4 LOW Severity Bugs (Edge Cases)

| Bug # | Name | Location | Impact |
|-------|------|----------|--------|
| **24** | No Run Report = Incomplete | `sync_determine_operation.py:705` | Intentional but confusing |

---

## 3. Root Cause Analysis

### 3.1 Fundamental Flaw: Implicit State Machine

The system should be a **finite state machine** with:
- Explicit states (NEW, HAS_CODE, HAS_EXAMPLE, VERIFIED, HAS_TESTS, SYNCED)
- Explicit transitions (state + event -> new_state + operation)
- Validation before each transition

Instead, it's:
- 615 lines of if-else chains
- Multiple sources of truth (fingerprint, run_report, file system)
- Reactive cycle detection (detect after failure, not prevent)

### 3.2 Multiple Sources of Truth

| Source | Location | Updated When | Problem |
|--------|----------|--------------|---------|
| Fingerprint | `.pdd/meta/{name}_{lang}.json` | After operation | Updated AFTER success, before validation |
| RunReport | `.pdd/meta/{name}_{lang}_run.json` | After test/crash | Deleted after generate, inconsistent |
| File System | `src/`, `examples/`, `tests/` | By operations | Can be modified externally |

### 3.3 Skip Flags Create Hidden Paths

When `--skip-verify` or `--skip-tests` is used:
1. Fingerprint is saved with `command='verify'` or `command='test'`
2. But the operation never actually ran
3. `_is_workflow_complete()` sees fingerprint and returns True
4. State machine believes workflow is complete when it isn't

---

## 4. Recommended Architecture: Explicit State Machine

### 4.1 State Definition

```python
class SyncState(Enum):
    NEW_PROMPT = "new_prompt"
    DEPS_NEEDED = "deps_needed"
    CODE_MISSING = "code_missing"
    EXAMPLE_MISSING = "example_missing"
    EXAMPLE_CRASHES = "example_crashes"
    VERIFY_PENDING = "verify_pending"
    TESTS_MISSING = "tests_missing"
    TESTS_FAIL = "tests_fail"
    COVERAGE_LOW = "coverage_low"
    SYNCED = "synced"
    CONFLICT = "conflict"
```

### 4.2 Transition Table

```python
TRANSITIONS = {
    SyncState.NEW_PROMPT: {
        'has_deps': (SyncState.DEPS_NEEDED, 'auto-deps'),
        'no_deps': (SyncState.CODE_MISSING, 'generate'),
    },
    SyncState.CODE_MISSING: {
        'generate_success': (SyncState.EXAMPLE_MISSING, 'example'),
    },
    SyncState.EXAMPLE_MISSING: {
        'example_success': (SyncState.VERIFY_PENDING, 'crash'),
    },
    SyncState.VERIFY_PENDING: {
        'verify_success': (SyncState.TESTS_MISSING, 'test'),
        'verify_fail': (SyncState.EXAMPLE_CRASHES, 'crash'),
    },
    # ... etc
}
```

### 4.3 Benefits

1. **Deterministic**: Same inputs always produce same outputs
2. **Testable**: Each transition can be unit tested
3. **Complete**: All valid states explicitly defined
4. **Maintainable**: Easy to add/modify transitions
5. **Debuggable**: Current state always known

---

## 5. Files Reference

| File | Purpose | Key Lines |
|------|---------|-----------|
| `pdd/sync_main.py` | CLI entry, language detection | 79-345 |
| `pdd/sync_orchestration.py` | Worker loop, operation execution | 739-1038 |
| `pdd/sync_determine_operation.py` | Decision logic, state analysis | 829-1444 |
| `pdd/sync_animation.py` | Real-time UI updates | All |
| `pdd/sync_tui.py` | Terminal UI framework | All |

---

## 6. Testing Recommendations

### 6.1 Unit Tests Needed
1. Skip flag handling doesn't create false fingerprints
2. Cycle detection with various patterns
3. Post-crash exception handling
4. Run report creation for all paths
5. Return value normalization

### 6.2 Integration Tests Needed
1. Full sync with skip_verify=True
2. Full sync with crash-verify cycle scenario
3. Full sync with test failures scenario
4. Full sync with budget exhaustion
5. Full sync after external file modification

---

## 7. Conclusion

The sync command has significant architectural debt that causes unpredictable behavior. The 27 identified bugs stem from three root causes:

1. **Implicit state machine**: States and transitions are scattered across 615 lines of if-else chains
2. **Multiple sources of truth**: Fingerprint, run_report, and file system can become inconsistent
3. **Reactive cycle detection**: Cycles are detected after failure, not prevented

The recommended long-term solution is to refactor to an explicit state machine with:
- States defined as Python enum
- Transitions defined as dictionary
- Validation before each transition
- Single source of truth

---

*Generated: 2024-12-20*
