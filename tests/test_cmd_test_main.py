"""
Tests for the `cmd_test_main` function, which handles CLI commands for test generation.
"""
from unittest.mock import patch, MagicMock, mock_open
import pytest
from click import Context
from pdd.cmd_test_main import cmd_test_main


@pytest.fixture
def mock_ctx_fixture():
    """
    Create a mock Click context with default settings for verbosity, strength, etc.
    """
    m_ctx = MagicMock(spec=Context)
    m_ctx.obj = {
        "verbose": False,
        "strength": 0.5,
        "temperature": 0.0,
        "force": False,
        "quiet": False
    }
    return m_ctx


@pytest.fixture
def mock_files_fixture():
    """
    Returns default file paths for prompt_file, code_file, etc. for use in tests.
    """
    return {
        "prompt_file": "fake_prompt_file.prompt",
        "code_file": "fake_code_file.py",
        "output": "fake_test_output.py",
        "existing_tests": "fake_existing_tests.py",
        "coverage_report": "fake_coverage_report.xml",
    }


# pylint: disable=redefined-outer-name
@pytest.mark.parametrize("coverage_report, existing_tests, expect_exit", [
    (None, None, False),
    ("fake_coverage_report.xml", None, True),
    ("fake_coverage_report.xml", "fake_existing_tests.py", False),
])
def test_cmd_test_main_coverage_handling(
    mock_ctx_fixture,
    mock_files_fixture,
    coverage_report,
    existing_tests,
    expect_exit
):
    """
    Tests behavior when coverage_report is missing or present
    and the presence/absence of existing_tests.
    """
    # Force coverage_report / existing_tests for test
    mock_files_fixture["coverage_report"] = coverage_report
    mock_files_fixture["existing_tests"] = existing_tests

    # Patch dependencies
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open()):

        # Mock construct_paths to return some test data
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "prompt_contents",
                "code_file": "code_contents",
                "coverage_report": "coverage_contents" if coverage_report else None,
                "existing_tests": "existing_tests_contents" if existing_tests else None
            },
            {"output": mock_files_fixture["output"]},
            "python",
        )

        # Mock generate_test and increase_tests
        mock_generate_test.return_value = ("generated_tests_code", 0.05, "test_model")
        mock_increase_tests.return_value = ("enhanced_tests_code", 0.10, "coverage_model")

        # Run the function
        exit_called = False
        def mock_exit(code):
            nonlocal exit_called
            exit_called = True
            assert code == 1, "Expected exit code 1 for this test case"

        mock_ctx_fixture.exit.side_effect = mock_exit

        cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=coverage_report,
            existing_tests=existing_tests,
            target_coverage=95.0,
            merge=False,
        )

        # Check if we expected click.Context.exit to be invoked
        assert exit_called == expect_exit

        if not expect_exit:
            # If not exiting, we either tested generate_test or increase_tests
            if coverage_report is None:
                # Should have invoked generate_test
                mock_generate_test.assert_called_once()
                mock_increase_tests.assert_not_called()
            else:
                # coverage_report is present, should have invoked increase_tests
                if existing_tests:
                    mock_increase_tests.assert_called_once()
                    mock_generate_test.assert_not_called()


# pylint: disable=unused-argument
def test_cmd_test_main_path_construction_error(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that if construct_paths raises an exception,
    cmd_test_main handles it and calls ctx.exit(1).
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths:
        mock_construct_paths.side_effect = Exception("construct_paths error")

        exit_called = False
        def mock_exit(code):
            nonlocal exit_called
            exit_called = True
            assert code == 1

        mock_ctx_fixture.exit.side_effect = mock_exit

        cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )
        assert exit_called is True


# pylint: disable=unused-argument
def test_cmd_test_main_generate_test_error(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that if generate_test raises an exception,
    cmd_test_main handles it and calls ctx.exit(1).
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_generate_test.side_effect = Exception("generate_test error")

        exit_called = False
        def mock_exit(code):
            nonlocal exit_called
            exit_called = True
            assert code == 1

        mock_ctx_fixture.exit.side_effect = mock_exit

        cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )
        assert exit_called is True


# pylint: disable=unused-argument
def test_cmd_test_main_increase_tests_error(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that if increase_tests raises an exception (when coverage_report is provided),
    cmd_test_main handles it and calls ctx.exit(1).
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "prompt_contents",
                "code_file": "code_contents",
                "coverage_report": "coverage_contents",
                "existing_tests": "existing_tests_contents",
            },
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_increase_tests.side_effect = Exception("increase_tests error")

        exit_called = False
        def mock_exit(code):
            nonlocal exit_called
            exit_called = True
            assert code == 1

        mock_ctx_fixture.exit.side_effect = mock_exit

        cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=mock_files_fixture["coverage_report"],
            existing_tests=mock_files_fixture["existing_tests"],
            target_coverage=95.0,
            merge=False,
        )
        assert exit_called is True


# pylint: disable=redefined-outer-name
def test_cmd_test_main_successful_generate_test_no_coverage(mock_ctx_fixture, mock_files_fixture):
    """
    Tests successful run where no coverage_report is provided
    and generate_test is used.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()) as m_file:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_generate_test.return_value = ("unit_test_code", 0.10, "model_v1")

        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Verify file writing
        m_file.assert_called_once_with(mock_files_fixture["output"], "w", encoding="utf-8")
        handle = m_file()
        handle.write.assert_called_once_with("unit_test_code")

        # Verify the result
        assert result == ("unit_test_code", 0.10, "model_v1")


# pylint: disable=redefined-outer-name
def test_cmd_test_main_successful_increase_test_with_coverage(mock_ctx_fixture, mock_files_fixture):
    """
    Tests a successful run with a coverage report, which should trigger 'increase_tests'.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open()) as m_file:

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "prompt_contents",
                "code_file": "code_contents",
                "coverage_report": "coverage_contents",
                "existing_tests": "existing_tests_contents",
            },
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_increase_tests.return_value = ("more_tests", 0.20, "model_v2")

        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=mock_files_fixture["output"],
            language=None,
            coverage_report=mock_files_fixture["coverage_report"],
            existing_tests=mock_files_fixture["existing_tests"],
            target_coverage=95.0,
            merge=False,
        )

        # Verify file writing and result
        m_file.assert_any_call(mock_files_fixture["output"], "w", encoding="utf-8")
        handle = m_file()
        handle.write.assert_called_once_with("more_tests")
        assert result == ("more_tests", 0.20, "model_v2")


# pylint: disable=redefined-outer-name
def test_cmd_test_main_merge_existing_tests(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that when 'merge' is True, the output file is the 'existing_tests' path.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()) as m_file:

        # Ensure 'existing_tests' is in the output path from construct_paths
        mock_construct_paths.return_value = (
            {},  # resolved_config
            {"prompt_file": "p", "code_file": "c", "existing_tests": "et"},
            {"output": mock_files_fixture["output"]},
            "python"
        )
        mock_generate_test.return_value = ("merged_code", 0.15, "model_v3")

        cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=None,
            language=None,
            coverage_report=None,
            existing_tests=[mock_files_fixture["existing_tests"]],
            target_coverage=None,
            merge=True,
        )

        # The opened file should be the existing_tests path, not the regular output
        m_file.assert_any_call(mock_files_fixture["existing_tests"], "w", encoding="utf-8")
        handle = m_file()
        handle.write.assert_called_once_with("merged_code")


def test_cmd_test_main_output_directory_path_uses_resolved_file(mock_ctx_fixture, mock_files_fixture, tmp_path):
    """
    Intended behavior: when output is a directory path, cmd should write to the
    resolved file from construct_paths, not exit.
    """
    out_dir = tmp_path / "tests_out"
    out_dir.mkdir()

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()) as m_open:

        resolved_file = out_dir / "unit_test_file.py"
        mock_construct_paths.return_value = (
            {},
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": str(resolved_file)},
            "python",
        )
        mock_generate_test.return_value = ("unit_test_code", 0.10, "model_v1")

        # Pass directory path via output; command should use resolved file
        result = cmd_test_main(
            ctx=mock_ctx_fixture,
            prompt_file=mock_files_fixture["prompt_file"],
            code_file=mock_files_fixture["code_file"],
            output=str(out_dir),
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        assert result == ("unit_test_code", 0.10, "model_v1")
        m_open.assert_called_once_with(str(resolved_file), "w", encoding="utf-8")
        handle = m_open()
        handle.write.assert_called_once_with("unit_test_code")
