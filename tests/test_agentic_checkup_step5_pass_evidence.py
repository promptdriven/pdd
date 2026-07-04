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


def test_step5_missing_signal_rejects_ambiguous_or_failing_output():
    assert _step5_output_has_strong_pass_evidence("Ran pytest. 491 passed") is False
    assert (
        _step5_output_has_strong_pass_evidence(
            "Exit code: 0\nFAILED tests/test_main.py::test_x"
        )
        is False
    )


def test_step5_selects_focused_checkup_orchestrator_regression(tmp_path):
    focused = tmp_path / "tests" / "test_agentic_checkup_step5_pass_evidence.py"
    broad = tmp_path / "tests" / "test_agentic_checkup_orchestrator.py"
    focused.parent.mkdir()
    focused.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")
    broad.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")

    assert _select_step5_python_tests(
        tmp_path,
        ["pdd/agentic_checkup_orchestrator.py"],
    ) == ["tests/test_agentic_checkup_step5_pass_evidence.py"]


def test_step5_override_suppresses_stale_broad_direct_test(tmp_path):
    focused = tmp_path / "tests" / "test_agentic_checkup_step5_pass_evidence.py"
    broad = tmp_path / "tests" / "test_agentic_checkup_orchestrator.py"
    focused.parent.mkdir()
    focused.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")
    broad.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")

    assert _select_step5_python_tests(
        tmp_path,
        [
            "tests/test_agentic_checkup_orchestrator.py",
            "pdd/agentic_checkup_orchestrator.py",
        ],
    ) == ["tests/test_agentic_checkup_step5_pass_evidence.py"]


def test_step5_focused_test_suppresses_broad_test_without_source_path(tmp_path):
    focused = tmp_path / "tests" / "test_agentic_checkup_step5_pass_evidence.py"
    broad = tmp_path / "tests" / "test_agentic_checkup_orchestrator.py"
    focused.parent.mkdir()
    focused.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")
    broad.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")

    assert _select_step5_python_tests(
        tmp_path,
        [
            "tests/test_agentic_checkup_orchestrator.py",
            "tests/test_agentic_checkup_step5_pass_evidence.py",
        ],
    ) == ["tests/test_agentic_checkup_step5_pass_evidence.py"]


def test_step5_changed_focused_file_runs_directly(tmp_path):
    focused = tmp_path / "tests" / "test_agentic_checkup_step5_pass_evidence.py"
    focused.parent.mkdir()
    focused.write_text("def test_placeholder():\n    assert True\n", encoding="utf-8")

    assert _select_step5_python_tests(tmp_path, [focused.as_posix()]) == []
    assert _select_step5_python_tests(
        tmp_path,
        [Path("tests/test_agentic_checkup_step5_pass_evidence.py").as_posix()],
    ) == ["tests/test_agentic_checkup_step5_pass_evidence.py"]
