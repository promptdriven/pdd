"""
E2E Test for Issue #219: Auto-deps inserts duplicate context includes when include already exists in prompt

This test exercises the full CLI path from `pdd auto-deps` to verify that when a prompt
file already contains a bare include, the auto-deps command does NOT insert a duplicate
wrapped version of the same include.

The bug: When running `pdd sync <module>` or `pdd auto-deps`, the auto_include function
receives dependencies from the LLM wrapped in module tags:
    <context.python_preamble><include>context/python_preamble.prompt</include></context.python_preamble>

But if the prompt already has a bare include:
    <include>context/python_preamble.prompt</include>

The wrapped duplicate gets inserted alongside the original, resulting in the same
context being included twice.

This E2E test:
1. Sets up a temp directory with a prompt file containing a bare include
2. Runs the auto-deps command through Click's CliRunner
3. Mocks the LLM to return dependencies that include a wrapped duplicate
4. Verifies that the duplicate is filtered out and NOT present in the final output

The test should FAIL on buggy code (duplicate not filtered) and PASS once the fix is applied.
"""

import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from click.testing import CliRunner


@pytest.fixture(autouse=True)
def set_pdd_path(monkeypatch):
    """Set PDD_PATH to the pdd package directory for all tests in this module.

    This is required because construct_paths uses PDD_PATH to find the language_format.csv
    file for language detection.
    """
    import pdd
    pdd_package_dir = Path(pdd.__file__).parent
    monkeypatch.setenv("PDD_PATH", str(pdd_package_dir))


class TestDuplicateIncludesE2E:
    """
    E2E tests for Issue #219: Verify auto-deps does not insert duplicate includes
    when the prompt already contains a bare include for the same path.
    """

    def test_auto_deps_does_not_insert_duplicate_wrapped_include(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: pdd auto-deps should NOT insert wrapped includes that duplicate
        bare includes already in the input prompt.

        This test runs the full CLI path and verifies that when the input prompt
        already has <include>context/python_preamble.prompt</include>, the
        auto-deps command does NOT insert a duplicate wrapped version like
        <context.python_preamble><include>context/python_preamble.prompt</include></context.python_preamble>

        Expected behavior (after fix):
        - The wrapped duplicate should be filtered out
        - Only non-duplicate includes should be inserted

        Bug behavior (Issue #219):
        - The wrapped duplicate is inserted alongside the bare include
        - The same content gets included twice
        """
        # 1. Create a prompt file with an existing bare include
        prompt_content = """You are an expert Python developer.
<include>context/python_preamble.prompt</include>
Write clean, well-documented Python code that follows best practices.
"""
        (tmp_path / "test_python.prompt").write_text(prompt_content)

        # 2. Create a CSV file for dependencies (normally created by summarize_directory)
        csv_content = """full_path,file_summary,date
context/python_preamble.prompt,Python preamble with coding standards,2023-02-02
context/helper_example.py,Helper utility functions,2023-02-02
"""
        (tmp_path / "dependencies.csv").write_text(csv_content)

        # 3. Create the context files referenced in the CSV
        context_dir = tmp_path / "context"
        context_dir.mkdir()
        (context_dir / "python_preamble.prompt").write_text("# Python coding standards")
        (context_dir / "helper_example.py").write_text("# Helper utilities")

        monkeypatch.chdir(tmp_path)

        # Force local execution
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        # Track what gets passed to insert_includes_LLM
        captured_dependencies = []

        def mock_llm_invoke_for_auto_include(*args, **kwargs):
            """Mock llm_invoke calls in the auto-include flow."""
            prompt = kwargs.get("prompt", args[0] if args else "")
            input_json = kwargs.get("input_json", {})

            # Detect which prompt template is being used
            if "auto_include_LLM" in prompt or "available_includes" in input_json:
                # First LLM call: auto_include_LLM - suggest dependencies
                return {
                    "result": "Include python_preamble and helper_example for context",
                    "cost": 0.001,
                    "model_name": "mock-model",
                }
            elif kwargs.get("output_pydantic"):
                pydantic_class = kwargs["output_pydantic"]
                class_name = pydantic_class.__name__

                if class_name == "AutoIncludeOutput":
                    # Second LLM call: extract_auto_include_LLM - return wrapped includes
                    # This simulates the LLM returning a DUPLICATE of the existing include
                    # wrapped in module tags, plus a non-duplicate include
                    mock_result = MagicMock()
                    mock_result.string_of_includes = (
                        "<context.python_preamble><include>context/python_preamble.prompt"
                        "</include></context.python_preamble>\n"
                        "<utils.helper><include>context/helper_example.py"
                        "</include></utils.helper>"
                    )
                    return {
                        "result": mock_result,
                        "cost": 0.001,
                        "model_name": "mock-model",
                    }
                elif class_name == "InsertIncludesOutput":
                    # Third LLM call: insert_includes_LLM - insert deps into prompt
                    # Capture what dependencies were passed to this step
                    deps = input_json.get("actual_dependencies_to_insert", "")
                    captured_dependencies.append(deps)

                    mock_result = MagicMock()
                    # Return prompt with only the deps that were passed
                    mock_result.output_prompt = f"{prompt_content}\n{deps}"
                    return {
                        "result": mock_result,
                        "cost": 0.001,
                        "model_name": "mock-model",
                    }

            # Default response
            return {
                "result": "Default mock response",
                "cost": 0.001,
                "model_name": "mock-model",
            }

        def mock_summarize_directory(*args, **kwargs):
            """Mock summarize_directory to return our pre-defined CSV."""
            return (csv_content, 0.001, "mock-model")

        # 4. Run the CLI command
        with patch('pdd.auto_include.llm_invoke', side_effect=mock_llm_invoke_for_auto_include):
            with patch('pdd.insert_includes.llm_invoke', side_effect=mock_llm_invoke_for_auto_include):
                with patch('pdd.auto_include.summarize_directory', side_effect=mock_summarize_directory):
                    from pdd import cli

                    runner = CliRunner()
                    result = runner.invoke(cli.cli, [
                        "--local",
                        "--force",
                        "auto-deps",
                        "test_python.prompt",
                        "context/*.py",
                        "--csv", str(tmp_path / "dependencies.csv"),
                        "--output", str(tmp_path / "output.prompt")
                    ], catch_exceptions=False)

        # 5. THE KEY ASSERTIONS

        # Check that dependencies were captured
        assert len(captured_dependencies) > 0, (
            f"No dependencies were captured - auto-deps flow may not have completed. "
            f"CLI output: {result.output}"
        )

        # THE BUG CHECK: The dependencies passed to insert_includes_LLM should NOT
        # contain the python_preamble include, because it already exists bare in the prompt
        deps_passed = captured_dependencies[0]

        # BUG: If python_preamble is in the dependencies, the duplicate wasn't filtered
        assert "context/python_preamble.prompt" not in deps_passed, (
            f"BUG DETECTED (Issue #219): Wrapped duplicate include was NOT filtered out!\n\n"
            f"The input prompt already contains:\n"
            f"  <include>context/python_preamble.prompt</include>\n\n"
            f"But the auto-deps command passed a wrapped duplicate to insert_includes:\n"
            f"  {deps_passed}\n\n"
            f"This causes the same context to be included twice in the final prompt.\n"
            f"Expected: python_preamble should be filtered out since it already exists."
        )

        # The non-duplicate helper include SHOULD be present
        assert "context/helper_example.py" in deps_passed, (
            f"Non-duplicate includes should be preserved.\n"
            f"Expected: context/helper_example.py should be in dependencies.\n"
            f"Got: {deps_passed}"
        )

    def test_auto_deps_preserves_all_includes_when_no_duplicates(
        self, tmp_path, monkeypatch
    ):
        """
        E2E Test: When the input prompt has NO existing includes, all LLM-generated
        includes should be preserved (not filtered out).

        This ensures the fix doesn't over-filter and remove valid non-duplicate includes.
        """
        # 1. Create a prompt file with NO existing includes
        prompt_content = """You are an expert Python developer.
Write clean, well-documented Python code that follows best practices.
"""
        (tmp_path / "test_python.prompt").write_text(prompt_content)

        # 2. Create CSV and context files
        csv_content = """full_path,file_summary,date
context/python_preamble.prompt,Python preamble with coding standards,2023-02-02
context/helper_example.py,Helper utility functions,2023-02-02
"""
        (tmp_path / "dependencies.csv").write_text(csv_content)

        context_dir = tmp_path / "context"
        context_dir.mkdir()
        (context_dir / "python_preamble.prompt").write_text("# Python coding standards")
        (context_dir / "helper_example.py").write_text("# Helper utilities")

        monkeypatch.chdir(tmp_path)
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        captured_dependencies = []

        def mock_llm_invoke_for_auto_include(*args, **kwargs):
            """Mock llm_invoke calls."""
            prompt = kwargs.get("prompt", args[0] if args else "")
            input_json = kwargs.get("input_json", {})

            if "auto_include_LLM" in prompt or "available_includes" in input_json:
                return {
                    "result": "Include both files",
                    "cost": 0.001,
                    "model_name": "mock-model",
                }
            elif kwargs.get("output_pydantic"):
                pydantic_class = kwargs["output_pydantic"]
                class_name = pydantic_class.__name__

                if class_name == "AutoIncludeOutput":
                    mock_result = MagicMock()
                    mock_result.string_of_includes = (
                        "<context.python_preamble><include>context/python_preamble.prompt"
                        "</include></context.python_preamble>\n"
                        "<utils.helper><include>context/helper_example.py"
                        "</include></utils.helper>"
                    )
                    return {
                        "result": mock_result,
                        "cost": 0.001,
                        "model_name": "mock-model",
                    }
                elif class_name == "InsertIncludesOutput":
                    deps = input_json.get("actual_dependencies_to_insert", "")
                    captured_dependencies.append(deps)

                    mock_result = MagicMock()
                    mock_result.output_prompt = f"{prompt_content}\n{deps}"
                    return {
                        "result": mock_result,
                        "cost": 0.001,
                        "model_name": "mock-model",
                    }

            return {
                "result": "Default mock response",
                "cost": 0.001,
                "model_name": "mock-model",
            }

        def mock_summarize_directory(*args, **kwargs):
            return (csv_content, 0.001, "mock-model")

        with patch('pdd.auto_include.llm_invoke', side_effect=mock_llm_invoke_for_auto_include):
            with patch('pdd.insert_includes.llm_invoke', side_effect=mock_llm_invoke_for_auto_include):
                with patch('pdd.auto_include.summarize_directory', side_effect=mock_summarize_directory):
                    from pdd import cli

                    runner = CliRunner()
                    result = runner.invoke(cli.cli, [
                        "--local",
                        "--force",
                        "auto-deps",
                        "test_python.prompt",
                        "context/*.py",
                        "--csv", str(tmp_path / "dependencies.csv"),
                        "--output", str(tmp_path / "output.prompt")
                    ], catch_exceptions=False)

        # Verify dependencies were captured
        assert len(captured_dependencies) > 0, (
            f"No dependencies were captured. CLI output: {result.output}"
        )

        deps_passed = captured_dependencies[0]

        # Both includes should be present since input has no existing includes
        assert "context/python_preamble.prompt" in deps_passed, (
            f"python_preamble should be preserved (no existing include to duplicate).\n"
            f"Got: {deps_passed}"
        )
        assert "context/helper_example.py" in deps_passed, (
            f"helper_example should be preserved.\n"
            f"Got: {deps_passed}"
        )


class TestDuplicateIncludesE2EDirectAutoInclude:
    """
    More targeted E2E test that directly calls auto_include function but exercises
    the full code path without mocking the filtering logic.
    """

    def test_auto_include_filters_wrapped_duplicates_e2e(self, tmp_path, monkeypatch):
        """
        E2E Test: Call auto_include directly and verify wrapped duplicates are filtered.

        This test is less comprehensive than the CLI test but runs faster and is more
        targeted at the specific bug location.
        """
        monkeypatch.setenv("PDD_FORCE_LOCAL", "1")
        monkeypatch.setenv("OPENAI_API_KEY", "fake-openai-key-for-testing")

        # Input prompt with existing bare include
        input_prompt_with_include = """You are an expert Python developer.
<include>context/python_preamble.prompt</include>
Write clean Python code.
"""

        def mock_llm_invoke(*args, **kwargs):
            """Mock llm_invoke to return controlled dependencies."""
            if kwargs.get("output_pydantic"):
                pydantic_class = kwargs["output_pydantic"]
                if pydantic_class.__name__ == "AutoIncludeOutput":
                    mock_result = MagicMock()
                    # Return a wrapped duplicate of the existing include + a non-duplicate
                    mock_result.string_of_includes = (
                        "<context.python_preamble><include>context/python_preamble.prompt"
                        "</include></context.python_preamble>\n"
                        "<utils.helper><include>context/helper_example.py"
                        "</include></utils.helper>"
                    )
                    return {
                        "result": mock_result,
                        "cost": 0.001,
                        "model_name": "mock-model",
                    }

            return {
                "result": "Step 4: Include python_preamble and helper",
                "cost": 0.001,
                "model_name": "mock-model",
            }

        def mock_summarize_directory(*args, **kwargs):
            csv = """full_path,file_summary,date
context/python_preamble.prompt,Python preamble,2023-02-02
context/helper_example.py,Helper utilities,2023-02-02
"""
            return (csv, 0.001, "mock-model")

        with patch('pdd.auto_include.llm_invoke', side_effect=mock_llm_invoke):
            with patch('pdd.auto_include.summarize_directory', side_effect=mock_summarize_directory):
                from pdd.auto_include import auto_include

                dependencies, csv_output, total_cost, model_name = auto_include(
                    input_prompt=input_prompt_with_include,
                    directory_path="context/*.py",
                    csv_file=None,
                    prompt_filename="prompts/test_python.prompt",
                    strength=0.7,
                    temperature=0.0,
                    verbose=False,
                )

        # THE BUG CHECK: python_preamble should be filtered out (it's a duplicate)
        assert "context/python_preamble.prompt" not in dependencies, (
            f"BUG DETECTED (Issue #219): Wrapped duplicate was NOT filtered!\n\n"
            f"Input prompt already has: <include>context/python_preamble.prompt</include>\n"
            f"But auto_include returned: {dependencies}\n\n"
            f"The wrapped version should have been filtered out."
        )

        # helper_example should still be present (not a duplicate)
        assert "context/helper_example.py" in dependencies, (
            f"Non-duplicate includes should be preserved.\n"
            f"Got: {dependencies}"
        )
