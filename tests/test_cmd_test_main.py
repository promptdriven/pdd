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
        "existing_tests": ["fake_existing_tests.py"],  # Now a list to support multiple test files
        "coverage_report": "fake_coverage_report.xml",
    }


# pylint: disable=redefined-outer-name
@pytest.mark.parametrize("coverage_report, existing_tests, expect_error", [
    (None, None, False),
    ("fake_coverage_report.xml", None, True),
    ("fake_coverage_report.xml", ["fake_existing_tests.py"], False),  # Now a list
])
def test_cmd_test_main_coverage_handling(
    mock_ctx_fixture,
    mock_files_fixture,
    coverage_report,
    existing_tests,
    expect_error
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

        result = cmd_test_main(
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

        # Check if we expected an error result (tuple with Error in model_name)
        if expect_error:
            assert result[0] == ""
            assert result[1] == 0.0
            assert "Error:" in result[2]
        else:
            # If not an error, we either tested generate_test or increase_tests
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
    cmd_test_main handles it and returns an error result tuple.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths:
        mock_construct_paths.side_effect = Exception("construct_paths error")

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

        # Verify error result tuple is returned
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error:" in result[2]
        assert "construct_paths error" in result[2]


# pylint: disable=unused-argument
def test_cmd_test_main_generate_test_error(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that if generate_test raises an exception,
    cmd_test_main handles it and returns an error result tuple.
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

        # Verify error result tuple is returned
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error:" in result[2]
        assert "generate_test error" in result[2]


# pylint: disable=unused-argument
def test_cmd_test_main_increase_tests_error(mock_ctx_fixture, mock_files_fixture):
    """
    Tests that if increase_tests raises an exception (when coverage_report is provided),
    cmd_test_main handles it and returns an error result tuple.
    """
    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.increase_tests") as mock_increase_tests, \
         patch("builtins.open", mock_open(read_data="existing test content")) as m_file:

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

        # Verify error result tuple is returned
        assert result[0] == ""
        assert result[1] == 0.0
        assert "Error:" in result[2]
        assert "increase_tests error" in result[2]


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
            existing_tests=mock_files_fixture["existing_tests"],  # Already a list
            target_coverage=None,
            merge=True,
        )

        # The opened file should be the first existing_tests path, not the regular output
        m_file.assert_any_call(mock_files_fixture["existing_tests"][0], "w", encoding="utf-8")
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


def test_cmd_test_main_uses_safe_ctx_obj_access():
    """
    Regression: cmd_test_main should not raise KeyError if ctx.obj
    is missing 'strength' or 'temperature' keys.

    Bug: Direct dict access ctx.obj["strength"] raises KeyError,
    but ctx.obj.get("strength", DEFAULT) is safe.
    """
    import inspect

    source = inspect.getsource(cmd_test_main)

    # Should NOT use direct dict access for strength/temperature
    assert 'ctx.obj["strength"]' not in source, \
        "cmd_test_main should use ctx.obj.get('strength', ...) not ctx.obj['strength']"
    assert 'ctx.obj["temperature"]' not in source, \
        "cmd_test_main should use ctx.obj.get('temperature', ...) not ctx.obj['temperature']"


def test_cmd_test_main_uses_pddrc_strength_from_resolved_config():
    """
    REGRESSION TEST: cmd_test_main must use strength from resolved_config (pddrc),
    not just ctx.obj or defaults.

    Bug: strength was resolved BEFORE calling construct_paths, so pddrc values
    from resolved_config were ignored. generate_test received DEFAULT_STRENGTH
    instead of pddrc value.

    BEFORE FIX: generate_test called with strength=0.75 (default)
    AFTER FIX: generate_test called with strength=0.9 (from pddrc via resolved_config)
    """
    mock_ctx = MagicMock(spec=Context)
    mock_ctx.obj = {
        "verbose": False,
        "force": False,
        "quiet": False,
        "time": 0.25,
        # strength/temperature NOT in ctx.obj (simulates CLI not passing --strength)
    }

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()):

        # resolved_config contains pddrc strength value
        mock_construct_paths.return_value = (
            {"strength": 0.9, "temperature": 0.5},  # pddrc values in resolved_config
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": "test_output.py"},
            "python"
        )
        mock_generate_test.return_value = ("unit_test_code", 0.10, "model_v1")

        cmd_test_main(
            ctx=mock_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Verify generate_test was called with pddrc strength (0.9), not default (0.75)
        mock_generate_test.assert_called_once()
        call_kwargs = mock_generate_test.call_args.kwargs
        assert call_kwargs["strength"] == 0.9, \
            f"Expected pddrc strength 0.9, got {call_kwargs['strength']}"
        assert call_kwargs["temperature"] == 0.5, \
            f"Expected pddrc temperature 0.5, got {call_kwargs['temperature']}"


def test_cmd_test_main_cli_strength_overrides_pddrc():
    """
    Verify that explicit CLI --strength overrides pddrc value.

    When user passes --strength 0.3, that should be used even if pddrc has 0.9.
    """
    mock_ctx = MagicMock(spec=Context)
    mock_ctx.obj = {
        "verbose": False,
        "force": False,
        "quiet": False,
        "time": 0.25,
        "strength": 0.3,  # CLI passed --strength 0.3
        "temperature": 0.1,
    }

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()):

        # resolved_config would normally have pddrc value, but CLI should win
        # However, construct_paths merges CLI > pddrc, so resolved_config
        # should already have the CLI value
        mock_construct_paths.return_value = (
            {"strength": 0.3, "temperature": 0.1},  # CLI values propagated
            {"prompt_file": "prompt_contents", "code_file": "code_contents"},
            {"output": "test_output.py"},
            "python"
        )
        mock_generate_test.return_value = ("unit_test_code", 0.10, "model_v1")

        cmd_test_main(
            ctx=mock_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=None,
            target_coverage=None,
            merge=False,
        )

        # Verify CLI strength (0.3) was used
        call_kwargs = mock_generate_test.call_args.kwargs
        assert call_kwargs["strength"] == 0.3, \
            f"Expected CLI strength 0.3, got {call_kwargs['strength']}"


def test_cmd_test_main_multiple_existing_tests_concatenated(tmp_path):
    """
    Test that cmd_test_main correctly concatenates multiple existing test files.

    This tests the new feature where multiple --existing-tests options can be provided
    and their content is concatenated before being passed to the test generation.
    """
    mock_ctx = MagicMock(spec=Context)
    mock_ctx.obj = {
        "verbose": False,
        "force": True,
        "quiet": False,
        "time": 0.25,
        "context": None,
        "confirm_callback": None,
    }

    # Create test files
    test_file_1 = tmp_path / "test_1.py"
    test_file_1.write_text("# test 1 content\ndef test_one(): pass")
    test_file_2 = tmp_path / "test_2.py"
    test_file_2.write_text("# test 2 content\ndef test_two(): pass")

    with patch("pdd.cmd_test_main.construct_paths") as mock_construct_paths, \
         patch("pdd.cmd_test_main.generate_test") as mock_generate_test, \
         patch("builtins.open", mock_open()):

        mock_construct_paths.return_value = (
            {},  # resolved_config
            {
                "prompt_file": "prompt_contents",
                "code_file": "code_contents",
                # existing_tests will be populated by cmd_test_main after construct_paths
            },
            {"output": "test_output.py"},
            "python"
        )
        mock_generate_test.return_value = ("generated_tests", 0.10, "model_v1")

        result = cmd_test_main(
            ctx=mock_ctx,
            prompt_file="test.prompt",
            code_file="test.py",
            output="test_output.py",
            language=None,
            coverage_report=None,
            existing_tests=[str(test_file_1), str(test_file_2)],
            target_coverage=None,
            merge=False,
        )

        # Verify generate_test was called and received concatenated existing tests
        mock_generate_test.assert_called_once()
        call_kwargs = mock_generate_test.call_args.kwargs

        # The existing_tests should contain content from both files
        if "existing_tests" in call_kwargs:
            existing_tests_content = call_kwargs["existing_tests"]
            assert "test 1 content" in existing_tests_content, \
                "Content from test_file_1 should be in existing_tests"
            assert "test 2 content" in existing_tests_content, \
                "Content from test_file_2 should be in existing_tests"
