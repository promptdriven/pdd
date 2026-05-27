"""Example usage for pdd.pin_example_hack.

This example exercises the public helper shape without spawning external
test runners. It is intentionally small because the implementation delegates
the heavy behavior to subprocess-driven test execution.
"""

from pathlib import Path
from unittest.mock import MagicMock, patch

from pdd.pin_example_hack import _execute_tests_and_create_run_report


def example_execute_tests_with_mocked_runner(tmp_path: Path) -> None:
    """Create a test file and run the helper with subprocess mocked."""
    test_file = tmp_path / "tests" / "test_demo.py"
    test_file.parent.mkdir(parents=True, exist_ok=True)
    test_file.write_text("def test_demo():\n    assert True\n", encoding="utf-8")

    completed = MagicMock()
    completed.returncode = 0
    completed.stdout = "1 passed"
    completed.stderr = ""

    with patch("pdd.pin_example_hack.subprocess.run", return_value=completed), patch(
        "pdd.pin_example_hack.save_run_report"
    ):
        _execute_tests_and_create_run_report(
            test_file=test_file,
            basename="demo",
            language="python",
            target_coverage=0.0,
        )
