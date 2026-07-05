from pathlib import Path

from pdd.agentic_checkup_orchestrator import (
    _select_step5_python_tests,
    _step5_output_has_strong_pass_evidence,
)


def test_step5_missing_signal_accepts_strong_pass_evidence():
    output = "\n".join(
        [
            "## Step 5/8: Test Execution",
            "**Status:** All tests pass",
            "### Result",
            "- **Exit code:** 0",
            "- **Total:** 491 passed, 9 warnings",
            "- **Failures:** 0",
        ]
    )

    assert _step5_output_has_strong_pass_evidence(output) is True


def test_step5_strong_pass_evidence_accepts_zero_failed_summary():
    output = "- Exit code: 0\n- 5 passed, 0 failed in 3.21s"

    assert _step5_output_has_strong_pass_evidence(output) is True


def test_step5_strong_pass_evidence_accepts_hosted_all_clear_table():
    output = """
## Step 5: Test Execution

**Status:** All Clear - 0 failures

### Results Summary

| Test File | Passed | Failed | Skipped |
|-----------|--------|--------|---------|
| `tests/test_generate_model_catalog.py` | 82 | 0 | 0 |
| `tests/test_llm_invoke.py` | 362 | 0 | 0 |
| **TOTAL** | **1,186** | **0** | **3** |

### Failures

None. **0 failures.**

### Root Cause of Previous Timeout

Splitting into focused batches completes all tests successfully with no failures.
"""

    assert _step5_output_has_strong_pass_evidence(output) is True


def test_step5_all_clear_without_total_row_remains_ambiguous():
    output = "**Status:** All Clear - 0 failures\nRan pytest. 491 passed"

    assert _step5_output_has_strong_pass_evidence(output) is False


def test_step5_missing_signal_rejects_ambiguous_or_failing_output():
    assert _step5_output_has_strong_pass_evidence("Ran pytest. 491 passed") is False
    assert (
        _step5_output_has_strong_pass_evidence(
            "Exit code: 0\nFAILED tests/test_main.py::test_x"
        )
        is False
    )


def test_step5_selects_focused_and_broad_checkup_orchestrator_tests(tmp_path):
    """Focused override test is appended ALONGSIDE the conventional broad test
    — the broad test must NOT be suppressed when the source file is changed.
    """
    focused = tmp_path / "tests" / "test_agentic_checkup_step5_pass_evidence.py"
    broad = tmp_path / "tests" / "test_agentic_checkup_orchestrator.py"
    focused.parent.mkdir()
    focused.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")
    broad.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")

    selected = _select_step5_python_tests(
        tmp_path,
        ["pdd/agentic_checkup_orchestrator.py"],
    )
    # Both the focused regression test and the conventional broad test must run.
    assert "tests/test_agentic_checkup_step5_pass_evidence.py" in selected
    assert "tests/test_agentic_checkup_orchestrator.py" in selected


def test_step5_explicitly_changed_tests_always_run(tmp_path):
    """Explicitly changed test files are never suppressed by an override.
    When both the broad test and the source file are in changed_paths, both
    the broad test and the focused override test must appear in the selection.
    """
    focused = tmp_path / "tests" / "test_agentic_checkup_step5_pass_evidence.py"
    broad = tmp_path / "tests" / "test_agentic_checkup_orchestrator.py"
    focused.parent.mkdir()
    focused.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")
    broad.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")

    selected = _select_step5_python_tests(
        tmp_path,
        [
            "tests/test_agentic_checkup_orchestrator.py",
            "pdd/agentic_checkup_orchestrator.py",
        ],
    )
    assert "tests/test_agentic_checkup_step5_pass_evidence.py" in selected
    assert "tests/test_agentic_checkup_orchestrator.py" in selected


def test_step5_both_test_files_changed_both_run(tmp_path):
    """When both test files are explicitly changed they both run — no deduplication
    via suppression.
    """
    focused = tmp_path / "tests" / "test_agentic_checkup_step5_pass_evidence.py"
    broad = tmp_path / "tests" / "test_agentic_checkup_orchestrator.py"
    focused.parent.mkdir()
    focused.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")
    broad.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")

    selected = _select_step5_python_tests(
        tmp_path,
        [
            "tests/test_agentic_checkup_orchestrator.py",
            "tests/test_agentic_checkup_step5_pass_evidence.py",
        ],
    )
    assert "tests/test_agentic_checkup_orchestrator.py" in selected
    assert "tests/test_agentic_checkup_step5_pass_evidence.py" in selected


def test_step5_changed_focused_file_runs_directly(tmp_path):
    focused = tmp_path / "tests" / "test_agentic_checkup_step5_pass_evidence.py"
    focused.parent.mkdir()
    focused.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")

    assert _select_step5_python_tests(tmp_path, [focused.as_posix()]) == []
    assert _select_step5_python_tests(
        tmp_path,
        [Path("tests/test_agentic_checkup_step5_pass_evidence.py").as_posix()],
    ) == ["tests/test_agentic_checkup_step5_pass_evidence.py"]
