"""Unit tests for the auto_include module."""
from unittest.mock import patch, MagicMock
import pytest
from pdd.auto_include import auto_include


@pytest.fixture(name="mock_load_prompt_template")
def mock_load_prompt_template_fixture():
    """Fixture to mock load_prompt_template calls."""
    with patch("pdd.auto_include.load_prompt_template") as mock_load:
        yield mock_load


@pytest.fixture(name="mock_summarize_directory")
def mock_summarize_directory_fixture():
    """Fixture to mock summarize_directory calls."""
    with patch("pdd.auto_include.summarize_directory") as mock_summarize:
        yield mock_summarize


@pytest.fixture(name="mock_llm_invoke")
def mock_llm_invoke_fixture():
    """Fixture to mock llm_invoke calls."""
    with patch("pdd.auto_include.llm_invoke") as mock_llm:
        yield mock_llm


def test_auto_include_valid_call(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """
    Test a successful call to auto_include with valid parameters.
    Ensures we get back a tuple of (dependencies, csv_output, total_cost, model_name).
    """
    # Mock prompt templates
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    # Mock summarize_directory return
    mock_summarize_directory.return_value = (
        "full_path,file_summary,date\n"
        "context/example.py,Example summary,2023-02-02",
        0.25,
        "mock-summary-model",
    )

    # Mock llm_invoke for auto_include_LLM step
    mock_llm_invoke.side_effect = [
        {
            "result": "Mocked auto_include_LLM output",
            "cost": 0.5,
            "model_name": "mock-model-1",
        },
        # Mock llm_invoke for extract_auto_include_LLM step (pydantic)
        {
            "result": MagicMock(string_of_includes="from .context.example import Example"),
            "cost": 0.75,
            "model_name": "mock-model-2",
        },
    ]

    deps, csv_out, total_cost, model_name = auto_include(
        input_prompt="Process image data",
        directory_path="context/*.py",
        csv_file=None,
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    assert "from .context.example import Example" in deps
    assert "full_path,file_summary,date" in csv_out
    # total_cost should be sum of summarize_directory (0.25) +
    # first llm_invoke (0.5) + second llm_invoke (0.75) = 1.5
    assert total_cost == 1.5
    # The last model used is from the second llm_invoke
    assert model_name == "mock-model-2"


def test_auto_include_fail_load_templates(mock_load_prompt_template):
    """
    Test that a failure to load either prompt template raises a ValueError.
    """
    # Return None for one of the templates
    mock_load_prompt_template.side_effect = [None, "extract_auto_include_LLM content"]

    with pytest.raises(ValueError) as excinfo:
        auto_include(
            input_prompt="Valid prompt",
            directory_path="context/*.py",
            csv_file=None,
            strength=0.7,
            temperature=0.0,
            verbose=False,
        )
    assert "Failed to load prompt templates" in str(excinfo.value)


def test_auto_include_csv_parsing_error(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """
    Test that an invalid CSV does not raise but logs an error and sets available_includes = [].
    We verify it proceeds to subsequent steps and handles it gracefully.
    """
    # Mock prompt templates
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    # Mock summarize_directory to return an invalid CSV
    mock_summarize_directory.return_value = (
        "not_a_valid_csv",
        0.25,
        "mock-summary-model",
    )

    # Mock llm_invoke
    mock_llm_invoke.side_effect = [
        {
            "result": "Mocked auto_include_LLM output",
            "cost": 0.5,
            "model_name": "mock-model-1",
        },
        {
            "result": MagicMock(string_of_includes="from .some_import import SomeClass"),
            "cost": 0.75,
            "model_name": "mock-model-2",
        },
    ]

    deps, _, total_cost, model_name = auto_include(
        input_prompt="Valid prompt",
        directory_path="context/*.py",
        csv_file=None,
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    # Dependencies are extracted from the second mock
    assert "from .some_import import SomeClass" in deps
    assert total_cost == 1.5
    assert model_name == "mock-model-2"


def test_auto_include_llm_invoke_error_extract(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """
    Test that if the second llm_invoke (extract_auto_include_LLM) fails,
    dependencies are set to "".
    """
    # Mock templates
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    # Mock summarize_directory
    mock_summarize_directory.return_value = (
        "full_path,file_summary,date\n"
        "context/example.py,Example summary,2023-02-02",
        0.2,
        "mock-summary-model",
    )

    # First llm_invoke works, second fails
    mock_llm_invoke.side_effect = [
        {
            "result": "Mocked auto_include_LLM output",
            "cost": 0.3,
            "model_name": "mock-model-1",
        },
        # Raise exception on second call
        Exception("Test extraction failure"),
    ]

    deps, _, total_cost, model_name = auto_include(
        input_prompt="Valid prompt",
        directory_path="context/*.py",
        csv_file=None,
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    # The second step fails, so dependencies remain ""
    assert deps == ""
    # only the cost of summarize_directory + first llm_invoke
    assert total_cost == 0.5
    # The last successful model name is "mock-model-1"
    assert model_name == "mock-model-1"


def test_auto_include_filters_self_referential_example(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """
    Test that auto_include filters out a module's own example file.

    When processing prompts/agentic_fix_python.prompt, the system should NOT
    include context/agentic_fix_example.py as a dependency - that file is the
    example OUTPUT of the module, not a dependency.
    """
    # Mock prompt templates
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    # Mock summarize_directory - includes the module's own example
    mock_summarize_directory.return_value = (
        "full_path,file_summary,date\n"
        "context/agentic_fix_example.py,Example usage of agentic fix,2023-02-02\n"
        "context/llm_invoke_example.py,Example usage of llm_invoke,2023-02-02",
        0.25,
        "mock-summary-model",
    )

    # Mock LLM returns a self-referential include (the bug we're testing)
    mock_llm_invoke.side_effect = [
        {
            "result": "Include agentic_fix_example.py for context",
            "cost": 0.5,
            "model_name": "mock-model-1",
        },
        {
            "result": MagicMock(
                string_of_includes=(
                    "<pdd.agentic_fix><include>context/agentic_fix_example.py"
                    "</include></pdd.agentic_fix>"
                )
            ),
            "cost": 0.75,
            "model_name": "mock-model-2",
        },
    ]

    deps, _, _, _ = auto_include(
        input_prompt="Write the pdd/agentic_fix.py module...",
        directory_path="context/*.py",
        csv_file=None,
        prompt_filename="prompts/agentic_fix_python.prompt",
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    # The self-referential include should be filtered out
    assert "agentic_fix_example.py" not in deps


def test_auto_include_fixes_malformed_file_brackets(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """
    Test that auto_include fixes malformed [File: ...] patterns to proper <include> format.

    This is a regression test for GitHub issue #238 where the LLM outputs
    [File: path] instead of <include>path</include>.
    """
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    mock_summarize_directory.return_value = (
        "full_path,file_summary,date\n"
        "context/python_preamble.prompt,Python preamble,2023-02-02",
        0.25,
        "mock-summary-model",
    )

    # Mock LLM returning the MALFORMED format (the bug)
    mock_llm_invoke.side_effect = [
        {
            "result": "Step 4: dependencies",
            "cost": 0.5,
            "model_name": "mock-model-1",
        },
        {
            "result": MagicMock(
                string_of_includes=(
                    "<context.python_preamble>\n"
                    "[File: context/python_preamble.prompt]\n"
                    "</context.python_preamble>"
                )
            ),
            "cost": 0.75,
            "model_name": "mock-model-2",
        },
    ]

    deps, _, _, _ = auto_include(
        input_prompt="Write a Python module...",
        directory_path="context/*.py",
        csv_file=None,
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    # The malformed [File: ...] should be fixed to <include>...</include>
    assert "[File:" not in deps
    assert "<include>context/python_preamble.prompt</include>" in deps


def test_auto_include_fixes_multiple_malformed_file_brackets(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """
    Test that auto_include fixes multiple malformed [File: ...] patterns.

    Ensures the regex replacement handles multiple occurrences.
    """
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    mock_summarize_directory.return_value = (
        "full_path,file_summary,date\n"
        "context/python_preamble.prompt,Python preamble,2023-02-02\n"
        "context/database-schema.md,Database schema,2023-02-02",
        0.25,
        "mock-summary-model",
    )

    # Mock LLM returning MULTIPLE malformed patterns
    mock_llm_invoke.side_effect = [
        {
            "result": "Step 4: dependencies",
            "cost": 0.5,
            "model_name": "mock-model-1",
        },
        {
            "result": MagicMock(
                string_of_includes=(
                    "<context.python_preamble>\n"
                    "[File: context/python_preamble.prompt]\n"
                    "</context.python_preamble>\n"
                    "<database_schema>\n"
                    "[File: context/database-schema.md]\n"
                    "</database_schema>"
                )
            ),
            "cost": 0.75,
            "model_name": "mock-model-2",
        },
    ]

    deps, _, _, _ = auto_include(
        input_prompt="Write a Python module...",
        directory_path="context/*.py",
        csv_file=None,
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    # Both malformed patterns should be fixed
    assert "[File:" not in deps
    assert "<include>context/python_preamble.prompt</include>" in deps
    assert "<include>context/database-schema.md</include>" in deps


def test_auto_include_filters_self_referential_example_in_subdirectory(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """
    Test that auto_include filters out a module's own example file when in a subdirectory.

    This is a regression test for the issue where examples in context/backend/ or other
    subdirectories were not being filtered out because the regex pattern only matched
    context/{module}_example.py but not context/backend/{module}_example.py.
    """
    # Mock prompt templates
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    # Mock summarize_directory - includes the module's own example in a subdirectory
    mock_summarize_directory.return_value = (
        "full_path,file_summary,date\n"
        "context/backend/credit_helpers_example.py,Example usage of credit helpers,2023-02-02\n"
        "context/firebase_helpers_example.py,Example usage of firebase helpers,2023-02-02",
        0.25,
        "mock-summary-model",
    )

    # Mock LLM returns a self-referential include with subdirectory path (the bug)
    mock_llm_invoke.side_effect = [
        {
            "result": "Include credit_helpers_example.py for context",
            "cost": 0.5,
            "model_name": "mock-model-1",
        },
        {
            "result": MagicMock(
                string_of_includes=(
                    "<utils.credit_helpers><include>context/backend/credit_helpers_example.py"
                    "</include></utils.credit_helpers>"
                )
            ),
            "cost": 0.75,
            "model_name": "mock-model-2",
        },
    ]

    deps, _, _, _ = auto_include(
        input_prompt="Write the utils/credit_helpers.py module...",
        directory_path="context/*.py",
        csv_file=None,
        prompt_filename="prompts/backend/utils/credit_helpers_python.prompt",
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    # The self-referential include should be filtered out even with subdirectory
    assert "credit_helpers_example.py" not in deps


# ============================================================================
# Circular Dependency Detection Tests
# ============================================================================

def test_extract_example_modules_basic():
    """
    Test that _extract_example_modules correctly extracts module names from example includes.
    """
    from pdd.auto_include import _extract_example_modules

    content = """
    Some text here
    <include>context/agentic_bug_example.py</include>
    <include>context/regular_file.py</include>
    <include>context/bug_main_example.py</include>
    More text
    """
    result = _extract_example_modules(content)

    # Should extract module names from _example.py files
    assert "agentic_bug" in result
    assert "bug_main" in result
    # Should NOT include regular files
    assert "regular_file" not in result
    assert len(result) == 2


def test_extract_example_modules_empty():
    """
    Test that _extract_example_modules returns empty set for no example includes.
    """
    from pdd.auto_include import _extract_example_modules

    content = "No includes here"
    result = _extract_example_modules(content)
    assert result == set()


def test_extract_example_modules_with_subdirectory():
    """
    Test that _extract_example_modules handles subdirectories.
    """
    from pdd.auto_include import _extract_example_modules

    content = "<include>context/backend/credit_helpers_example.py</include>"
    result = _extract_example_modules(content)
    assert "credit_helpers" in result


def test_detect_circular_dependencies_self_reference():
    """
    Test that self-references (module including its own example) are handled.

    Note: Self-references are primarily handled by _filter_self_references,
    not by circular dependency detection. This test verifies the function
    returns empty when no cross-module cycles exist.
    """
    from pdd.auto_include import _detect_circular_dependencies

    current_prompt = "prompts/module_a_python.prompt"
    # Module A tries to include its own example - this is a self-reference,
    # not a cross-module circular dependency
    new_dependencies = "<wrapper><include>context/module_a_example.py</include></wrapper>"

    cycles = _detect_circular_dependencies(current_prompt, new_dependencies)

    # Self-references are handled by _filter_self_references, not here
    # This function only detects cross-module cycles (A -> B -> A)
    # Since there's no cross-module dependency, no cycles detected
    assert cycles == []


def test_detect_circular_dependencies_direct_cycle(tmp_path):
    """
    Test detection of direct circular dependency: A includes B's example, B includes A's example.
    """
    from pdd.auto_include import _detect_circular_dependencies

    # Create temporary prompt files
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()

    # module_b's prompt includes module_a's example (creates cycle when module_a includes module_b's example)
    (prompts_dir / "module_b_python.prompt").write_text(
        "<pdd.module_a><include>context/module_a_example.py</include></pdd.module_a>"
    )

    current_prompt = str(prompts_dir / "module_a_python.prompt")
    # module_a wants to include module_b's example
    new_dependencies = "<wrapper><include>context/module_b_example.py</include></wrapper>"

    cycles = _detect_circular_dependencies(
        current_prompt, new_dependencies, prompts_dir=str(prompts_dir)
    )

    # Should detect the A -> B -> A cycle
    assert len(cycles) >= 1


def test_detect_circular_dependencies_no_cycle(tmp_path):
    """
    Test that valid dependencies without cycles return empty list.
    """
    from pdd.auto_include import _detect_circular_dependencies

    # Create temporary prompt files
    prompts_dir = tmp_path / "prompts"
    prompts_dir.mkdir()

    # module_b has no includes that reference module_a (no cycle possible)
    (prompts_dir / "module_b_python.prompt").write_text(
        "<pdd.other><include>context/other_example.py</include></pdd.other>"
    )

    current_prompt = str(prompts_dir / "module_a_python.prompt")
    new_dependencies = "<wrapper><include>context/module_b_example.py</include></wrapper>"

    cycles = _detect_circular_dependencies(
        current_prompt, new_dependencies, prompts_dir=str(prompts_dir)
    )

    # Should not detect any cycles
    assert cycles == []


def test_filter_circular_dependencies_removes_problematic():
    """
    Test that _filter_circular_dependencies removes example includes that create cycles.
    """
    from pdd.auto_include import _filter_circular_dependencies

    dependencies = (
        "<wrapper1><include>context/module_b_example.py</include></wrapper1>"
        "<wrapper2><include>context/module_c_example.py</include></wrapper2>"
    )
    cycles = [["module_a_python.prompt", "module_b_python.prompt", "module_a_python.prompt"]]

    result = _filter_circular_dependencies(dependencies, cycles)

    # module_b should be filtered out (it's in the cycle)
    assert "module_b_example.py" not in result
    # module_c should remain (it's not in the cycle)
    assert "module_c_example.py" in result


def test_filter_circular_dependencies_empty_cycles():
    """
    Test that _filter_circular_dependencies returns original when no cycles.
    """
    from pdd.auto_include import _filter_circular_dependencies

    dependencies = "<wrapper><include>context/module_b_example.py</include></wrapper>"
    cycles = []

    result = _filter_circular_dependencies(dependencies, cycles)

    # Should return original dependencies unchanged
    assert result == dependencies


def test_auto_include_filters_circular_dependency(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke, tmp_path
):
    """
    Integration test: auto_include filters out circular dependencies.

    Scenario: Processing module_a_python.prompt, LLM suggests including
    module_a_example.py (self-reference through example file).
    """
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    mock_summarize_directory.return_value = (
        "full_path,file_summary,date\n"
        "context/module_a_example.py,Module A example,2023-02-02",
        0.25,
        "mock-summary-model",
    )

    # LLM suggests including the module's own example (self-reference)
    mock_llm_invoke.side_effect = [
        {
            "result": "Include module_a example",
            "cost": 0.5,
            "model_name": "mock-model-1",
        },
        {
            "result": MagicMock(
                string_of_includes=(
                    "<pdd.module_a><include>context/module_a_example.py</include></pdd.module_a>"
                )
            ),
            "cost": 0.75,
            "model_name": "mock-model-2",
        },
    ]

    deps, _, _, _ = auto_include(
        input_prompt="Write module A...",
        directory_path="context/*.py",
        csv_file=None,
        prompt_filename="prompts/module_a_python.prompt",
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    # The self-referential circular dependency should be filtered out
    assert "module_a_example.py" not in deps


# ============================================================================
# Duplicate Include Detection Tests (Issue #219)
# ============================================================================

def test_auto_include_deduplicates_wrapped_includes(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """
    Regression test for GitHub issue #219: auto_include should not return
    wrapped duplicates of includes that already exist bare in the input prompt.

    When the input prompt already contains:
        <include>context/python_preamble.prompt</include>

    And the LLM returns the same include wrapped in module tags:
        <context.python_preamble><include>context/python_preamble.prompt</include></context.python_preamble>

    The wrapped duplicate should be filtered out, because the bare include
    already exists in the input.
    """
    # Mock prompt templates
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    # Mock summarize_directory - includes available context files
    mock_summarize_directory.return_value = (
        "full_path,file_summary,date\n"
        "context/python_preamble.prompt,Python preamble for code generation,2023-02-02\n"
        "context/helper_example.py,Helper utilities,2023-02-02",
        0.25,
        "mock-summary-model",
    )

    # Input prompt already has a bare include for python_preamble
    input_prompt_with_existing_include = """You are an expert Python developer.
<include>context/python_preamble.prompt</include>
Write clean, well-documented Python code."""

    # LLM returns BOTH includes - python_preamble (duplicate) and helper (non-duplicate)
    mock_llm_invoke.side_effect = [
        {
            "result": "Step 4: dependencies for the module",
            "cost": 0.5,
            "model_name": "mock-model-1",
        },
        {
            "result": MagicMock(
                string_of_includes=(
                    "<context.python_preamble><include>context/python_preamble.prompt"
                    "</include></context.python_preamble>\n"
                    "<utils.helper><include>context/helper_example.py"
                    "</include></utils.helper>"
                )
            ),
            "cost": 0.75,
            "model_name": "mock-model-2",
        },
    ]

    deps, _, _, _ = auto_include(
        input_prompt=input_prompt_with_existing_include,
        directory_path="context/*.py",
        csv_file=None,
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    # The wrapped python_preamble should be REMOVED (it duplicates the bare include)
    assert "context/python_preamble.prompt" not in deps, (
        "Wrapped duplicate of bare include should be filtered out. "
        f"Got: {deps}"
    )

    # The non-duplicate helper include should be PRESERVED
    assert "context/helper_example.py" in deps, (
        "Non-duplicate includes should be preserved. "
        f"Got: {deps}"
    )


def test_auto_include_preserves_non_duplicate_includes(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """
    Test that auto_include preserves includes that don't duplicate existing bare includes.

    When the input prompt has NO existing includes, all LLM-generated includes
    should be preserved.
    """
    mock_load_prompt_template.side_effect = lambda name: f"{name} content"

    mock_summarize_directory.return_value = (
        "full_path,file_summary,date\n"
        "context/python_preamble.prompt,Python preamble,2023-02-02\n"
        "context/helper_example.py,Helper utilities,2023-02-02",
        0.25,
        "mock-summary-model",
    )

    # Input prompt with NO existing includes
    input_prompt_no_includes = "Write a Python module to process data."

    mock_llm_invoke.side_effect = [
        {
            "result": "Step 4: dependencies",
            "cost": 0.5,
            "model_name": "mock-model-1",
        },
        {
            "result": MagicMock(
                string_of_includes=(
                    "<context.python_preamble><include>context/python_preamble.prompt"
                    "</include></context.python_preamble>\n"
                    "<utils.helper><include>context/helper_example.py"
                    "</include></utils.helper>"
                )
            ),
            "cost": 0.75,
            "model_name": "mock-model-2",
        },
    ]

    deps, _, _, _ = auto_include(
        input_prompt=input_prompt_no_includes,
        directory_path="context/*.py",
        csv_file=None,
        strength=0.7,
        temperature=0.0,
        verbose=False,
    )

    # Both includes should be preserved since input has no existing includes
    assert "context/python_preamble.prompt" in deps
    assert "context/helper_example.py" in deps