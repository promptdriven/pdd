import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""
Test Plan for auto_include module
==================================

1. Input Validation Tests (unit tests):
   - test_validate_input_valid: Valid strength/temperature values
   - test_validate_input_invalid_strength: Strength out of range
   - test_validate_input_invalid_temperature: Temperature out of range
   - test_auto_include_invalid_strength: auto_include rejects bad strength
   - test_auto_include_invalid_temperature: auto_include rejects bad temperature
   - test_auto_include_empty_prompt: Empty prompt raises ValueError

2. Core auto_include flow tests (unit tests with mocks):
   - test_auto_include_valid_call: Successful end-to-end call returns tuple
   - test_auto_include_returns_four_tuple: Return type is (str, str, float, str)
   - test_auto_include_cost_aggregation: total_cost = summary_cost + llm_cost
   - test_auto_include_llm_failure_returns_empty: LLM failure returns empty deps
   - test_auto_include_failed_prompt_template: Missing template raises ValueError

3. CSV formatting tests (unit tests):
   - test_format_csv_rows_empty: Empty CSV returns empty string
   - test_format_csv_rows_valid: Valid CSV produces formatted output
   - test_format_csv_rows_invalid: Invalid CSV handles gracefully

4. Self-reference filtering tests (unit tests):
   - test_filter_self_references_removes_own_example
   - test_filter_self_references_no_module_name

5. Circular dependency tests (unit tests):
   - test_extract_example_modules_basic
   - test_extract_example_modules_empty
   - test_extract_example_modules_subdirectory
   - test_detect_circular_no_cycles
   - test_filter_circular_dependencies_removes_problematic
   - test_filter_circular_dependencies_empty_cycles

6. Duplicate filtering tests (unit tests):
   - test_filter_duplicates_removes_existing
   - test_filter_duplicates_no_existing

7. Module name extraction tests (unit tests):
   - test_extract_module_name_standard
   - test_extract_module_name_none
   - test_extract_module_name_with_path

8. Two-stage retrieval tests (unit tests):
   - test_embed_and_rank_fallback_on_error
   - test_auto_include_skips_embedding_under_threshold

9. Small file selector stripping tests (unit tests):
   - test_strip_selectors_from_small_files

10. Build directives tests (unit tests):
    - test_build_new_block
    - test_build_update_block
    - test_build_update_block_empty

11. Path qualification tests (unit tests):
    - test_qualify_path_absolute
    - test_qualify_path_relative
    - test_directory_prefix_glob
    - test_directory_prefix_empty

Z3 Formal Verification:
   - Strength/temperature range validation can be verified with Z3
     to prove all valid/invalid ranges are handled correctly.
   - Cost aggregation: verify total_cost = summary_cost + llm_cost
"""

import types
import sys
from unittest.mock import patch, MagicMock, PropertyMock
from pathlib import Path

import pytest

from pdd.auto_include import (
    auto_include,
    _validate_input,
    _format_csv_rows_for_llm,
    _extract_module_name,
    _extract_example_modules,
    _detect_circular_dependencies,
    _filter_circular_dependencies,
    _filter_self_references,
    _filter_duplicates,
    _embed_and_rank,
    _build_new_block,
    _build_update_block,
    _build_include_directives,
    _directory_prefix,
    _strip_selectors_from_small_files,
    AutoIncludeResult,
    NewInclude,
    IncludeAnnotation,
)


# ============================================================================
# Fixtures
# ============================================================================

@pytest.fixture
def mock_load_prompt_template():
    with patch("pdd.auto_include.load_prompt_template") as m:
        m.return_value = "mock prompt template {input_prompt} {available_includes}"
        yield m


@pytest.fixture
def mock_summarize_directory():
    with patch("pdd.auto_include.summarize_directory") as m:
        m.return_value = (
            "full_path,file_summary,date,key_exports,dependencies\n"
            "context/example.py,Example summary,2023-02-02,\"['func']\",\"[]\"\n",
            0.10,  # Changed from 0.25 to 0.10 to fix the collision issue with the first block's fixture
            "mock-summary-model",
        )
        yield m


@pytest.fixture
def mock_llm_invoke():
    with patch("pdd.auto_include.llm_invoke") as m:
        yield m


@pytest.fixture
def mock_embed_and_retrieve():
    with patch("pdd.auto_include.embed_and_retrieve") as m:
        yield m


# ============================================================================
# 1. Input Validation Tests
# ============================================================================

def test_validate_input_valid():
    """Valid strength and temperature should not raise."""
    _validate_input(0.5, 0.5)
    _validate_input(0.0, 0.0)
    _validate_input(1.0, 1.0)


def test_validate_input_invalid_strength_high():
    with pytest.raises(ValueError, match="Strength"):
        _validate_input(1.5, 0.5)


def test_validate_input_invalid_strength_low():
    with pytest.raises(ValueError, match="Strength"):
        _validate_input(-0.1, 0.5)


def test_validate_input_invalid_temperature_high():
    with pytest.raises(ValueError, match="Temperature"):
        _validate_input(0.5, 1.5)


def test_validate_input_invalid_temperature_low():
    with pytest.raises(ValueError, match="Temperature"):
        _validate_input(0.5, -0.1)


def test_auto_include_invalid_strength(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    with pytest.raises(ValueError, match="Strength"):
        auto_include(
            input_prompt="test",
            directory_path="context/*.py",
            strength=2.0,
            temperature=0.0,
        )


def test_auto_include_invalid_temperature(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    with pytest.raises(ValueError, match="Temperature"):
        auto_include(
            input_prompt="test",
            directory_path="context/*.py",
            strength=0.5,
            temperature=-1.0,
        )


def test_auto_include_empty_prompt_raises(mock_load_prompt_template):
    """When load_prompt_template returns None, auto_include raises ValueError."""
    mock_load_prompt_template.return_value = None
    with pytest.raises(ValueError, match="Failed to load"):
        auto_include(
            input_prompt="test prompt",
            directory_path="context/*.py",
            strength=0.5,
            temperature=0.0,
        )


# ============================================================================
# 2. Core auto_include flow tests
# ============================================================================

def test_auto_include_returns_four_tuple(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """auto_include should return a 4-tuple."""
    result = AutoIncludeResult(
        reasoning="test",
        new_includes=[NewInclude(file="context/helper.py", module="utils")],
        existing_include_annotations=[],
    )
    mock_llm_invoke.return_value = {
        "result": result,
        "cost": 0.5,
        "model_name": "mock-model",
    }

    output = auto_include(
        input_prompt="Process data",
        directory_path="context/*.py",
        strength=0.7,
        temperature=0.0,
    )

    assert isinstance(output, tuple)
    assert len(output) == 4
    deps, csv_out, cost, model = output
    assert isinstance(deps, str)
    assert isinstance(csv_out, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)


def test_auto_include_cost_aggregation(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """total_cost should be summary_cost + llm_cost."""
    result = AutoIncludeResult(
        reasoning="test",
        new_includes=[],
        existing_include_annotations=[],
    )
    mock_llm_invoke.return_value = {
        "result": result,
        "cost": 0.75,
        "model_name": "mock-model",
    }

    _, _, total_cost, _ = auto_include(
        input_prompt="Process data",
        directory_path="context/*.py",
        strength=0.7,
        temperature=0.0,
    )

    # summary_cost = 0.10, llm_cost = 0.75
    assert total_cost == pytest.approx(0.85)


def test_auto_include_llm_failure_returns_empty(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """When LLM invocation fails, return empty dependencies."""
    mock_llm_invoke.side_effect = Exception("LLM error")

    deps, csv_out, cost, model = auto_include(
        input_prompt="Process data",
        directory_path="context/*.py",
        strength=0.7,
        temperature=0.0,
    )

    assert deps == ""
    assert "full_path" in csv_out
    assert cost == 0.10  # only summary cost
    assert model == "mock-summary-model"


def test_auto_include_verbose_flag(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """verbose=True should not raise errors."""
    result = AutoIncludeResult(
        reasoning="test",
        new_includes=[],
        existing_include_annotations=[],
    )
    mock_llm_invoke.return_value = {
        "result": result,
        "cost": 0.1,
        "model_name": "mock-model",
    }

    deps, _, _, _ = auto_include(
        input_prompt="Process data",
        directory_path="context/*.py",
        strength=0.7,
        temperature=0.0,
        verbose=True,
    )

    assert isinstance(deps, str)


# ============================================================================
# 3. CSV formatting tests
# ============================================================================

def test_format_csv_rows_empty():
    assert _format_csv_rows_for_llm("") == ""


def test_format_csv_rows_valid():
    csv = (
        "full_path,file_summary,date,key_exports,dependencies\n"
        "helper.py,Helper functions,2023-01-01,\"['func']\",\"[]\"\n"
    )
    result = _format_csv_rows_for_llm(csv)
    assert "File:" in result
    assert "Purpose:" in result
    assert "Key Exports:" in result


def test_format_csv_rows_invalid():
    """Invalid CSV should not raise but return empty."""
    result = _format_csv_rows_for_llm("not,a,valid\ncsv,without,header\n")
    # Should still produce something or empty without error
    assert isinstance(result, str)


# ============================================================================
# 4. Self-reference filtering tests
# ============================================================================

def test_filter_self_references_removes_own_example():
    directives = (
        '<new>\n<mod><include>context/agentic_fix_example.py</include></mod>\n</new>\n'
        '<new>\n<mod><include>context/other_example.py</include></mod>\n</new>'
    )
    result = _filter_self_references(directives, "agentic_fix")
    assert "agentic_fix_example.py" not in result
    assert "other_example.py" in result


def test_filter_self_references_no_module_name():
    directives = '<new>\n<mod><include>context/agentic_fix_example.py</include></mod>\n</new>'
    result = _filter_self_references(directives, None)
    assert "agentic_fix_example.py" in result


# ============================================================================
# 5. Circular dependency tests
# ============================================================================

def test_extract_example_modules_basic():
    content = '<include>context/agentic_bug_example.py</include>'
    result = _extract_example_modules(content)
    assert "agentic_bug" in result


def test_extract_example_modules_empty():
    result = _extract_example_modules("no includes here")
    assert result == set()


def test_extract_example_modules_subdirectory():
    content = '<include>context/backend/credit_helpers_example.py</include>'
    result = _extract_example_modules(content)
    assert "credit_helpers" in result


def test_extract_example_modules_multiple():
    content = (
        '<include>context/module_a_example.py</include>\n'
        '<include>context/module_b_example.py</include>\n'
        '<include>context/regular_file.py</include>'
    )
    result = _extract_example_modules(content)
    assert "module_a" in result
    assert "module_b" in result
    assert len(result) == 2


def test_filter_circular_dependencies_empty_cycles():
    directives = '<new>\n<mod><include>context/a_example.py</include></mod>\n</new>'
    result = _filter_circular_dependencies(directives, [])
    assert result == directives


def test_filter_circular_dependencies_removes_problematic():
    directives = (
        '<new>\n<mod><include>context/module_b_example.py</include></mod>\n</new>\n'
        '<new>\n<mod><include>context/module_c_example.py</include></mod>\n</new>'
    )
    cycles = [["module_a_python.prompt", "module_b_python.prompt", "module_a_python.prompt"]]
    result = _filter_circular_dependencies(directives, cycles)
    assert "module_b_example.py" not in result
    assert "module_c_example.py" in result


def test_detect_circular_no_module_name():
    """No module name -> no cycles detected."""
    result = _detect_circular_dependencies("", "some deps")
    assert result == []


def test_detect_circular_no_dep_modules():
    """No example modules in dependencies -> no cycles."""
    result = _detect_circular_dependencies(
        "prompts/test_python.prompt", "no example includes"
    )
    assert result == []


# ============================================================================
# 6. Duplicate filtering tests
# ============================================================================

def test_filter_duplicates_removes_existing():
    directives = '<new>\n<mod><include>context/helper.py</include></mod>\n</new>'
    input_prompt = 'Some text <include>context/helper.py</include> more text'
    result = _filter_duplicates(directives, input_prompt)
    assert "helper.py" not in result


def test_filter_duplicates_no_existing():
    directives = '<new>\n<mod><include>context/helper.py</include></mod>\n</new>'
    input_prompt = 'Some text without includes'
    result = _filter_duplicates(directives, input_prompt)
    assert "helper.py" in result


def test_filter_duplicates_basename_match():
    """Should detect duplicates even with different path prefixes."""
    directives = '<new>\n<mod><include>context/helper.py</include></mod>\n</new>'
    input_prompt = 'Text <include>helper.py</include>'
    result = _filter_duplicates(directives, input_prompt)
    assert "helper.py" not in result or "<new>" not in result


# ============================================================================
# 7. Module name extraction tests
# ============================================================================

def test_extract_module_name_standard():
    assert _extract_module_name("agentic_fix_python.prompt") == "agentic_fix"


def test_extract_module_name_with_path():
    assert _extract_module_name("prompts/agentic_fix_python.prompt") == "agentic_fix"


def test_extract_module_name_none():
    assert _extract_module_name(None) is None


def test_extract_module_name_no_match():
    result = _extract_module_name("invalid_filename.txt")
    assert result is None


def test_extract_module_name_llm_suffix():
    assert _extract_module_name("some_module_LLM.prompt") == "some_module"


# ============================================================================
# 8. Two-stage retrieval tests
# ============================================================================

def test_embed_and_rank_fallback_on_error():
    """On failure, _embed_and_rank returns original candidates."""
    candidates = ["File: a.py\nPurpose: test", "File: b.py\nPurpose: test2"]
    with patch("pdd.auto_include.embed_and_retrieve", side_effect=Exception("fail")):
        result = _embed_and_rank("query", candidates)
    assert result == candidates


def test_embed_and_rank_success():
    """On success, returns ranked candidates."""
    candidates = ["File: a.py\nPurpose: test", "File: b.py\nPurpose: test2"]
    ranked = [("File: b.py\nPurpose: test2", 0.9), ("File: a.py\nPurpose: test", 0.5)]
    with patch("pdd.auto_include.embed_and_retrieve", return_value=ranked):
        result = _embed_and_rank("query", candidates, top_n=2)
    assert result == ["File: b.py\nPurpose: test2", "File: a.py\nPurpose: test"]


def test_auto_include_embedding_prefilter_over_50(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """When candidates > 50, embedding pre-filter should be invoked."""
    # Create CSV with >50 rows
    rows = "full_path,file_summary,date,key_exports,dependencies\n"
    for i in range(55):
        rows += f"file_{i}.py,Summary {i},2023-01-01,\"[]\",\"[]\"\n"
    mock_summarize_directory.return_value = (rows, 0.1, "model")

    result = AutoIncludeResult(
        reasoning="test", new_includes=[], existing_include_annotations=[]
    )
    mock_llm_invoke.return_value = {
        "result": result,
        "cost": 0.1,
        "model_name": "mock-model",
    }

    with patch("pdd.auto_include._embed_and_rank") as mock_rank:
        mock_rank.return_value = ["File: file_0.py\nPurpose: Summary 0"]
        auto_include(
            input_prompt="test",
            directory_path="context/*.py",
            strength=0.7,
            temperature=0.0,
        )
        mock_rank.assert_called_once()


# ============================================================================
# 9. Build directives tests
# ============================================================================

def test_build_new_block_simple():
    inc = NewInclude(file="context/helper.py", module="utils")
    result = _build_new_block(inc)
    assert "<new>" in result
    assert "<include>" in result
    assert "context/helper.py" in result
    assert "<utils>" in result
    assert "</utils>" in result



import sys
from pathlib import Path

# Add project root to sys.path to ensure local code is prioritized
# This allows testing local changes without installing the package
project_root = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(project_root))

"""
Test Plan for auto_include module
==================================

1. Input Validation Tests (unit tests):
   - test_validate_input_valid: Valid strength/temperature values
   - test_validate_input_invalid_strength: Strength out of range
   - test_validate_input_invalid_temperature: Temperature out of range
   - test_auto_include_invalid_strength: auto_include rejects bad strength
   - test_auto_include_invalid_temperature: auto_include rejects bad temperature
   - test_auto_include_empty_prompt: Empty prompt raises ValueError

2. Core auto_include flow tests (unit tests with mocks):
   - test_auto_include_valid_call: Successful end-to-end call returns tuple
   - test_auto_include_returns_four_tuple: Return type is (str, str, float, str)
   - test_auto_include_cost_aggregation: total_cost = summary_cost + llm_cost
   - test_auto_include_llm_failure_returns_empty: LLM failure returns empty deps
   - test_auto_include_failed_prompt_template: Missing template raises ValueError

3. CSV formatting tests (unit tests):
   - test_format_csv_rows_empty: Empty CSV returns empty string
   - test_format_csv_rows_valid: Valid CSV produces formatted output
   - test_format_csv_rows_invalid: Invalid CSV handles gracefully

4. Self-reference filtering tests (unit tests):
   - test_filter_self_references_removes_own_example
   - test_filter_self_references_no_module_name

5. Circular dependency tests (unit tests):
   - test_extract_example_modules_basic
   - test_extract_example_modules_empty
   - test_extract_example_modules_subdirectory
   - test_detect_circular_no_cycles
   - test_filter_circular_dependencies_removes_problematic
   - test_filter_circular_dependencies_empty_cycles

6. Duplicate filtering tests (unit tests):
   - test_filter_duplicates_removes_existing
   - test_filter_duplicates_no_existing

7. Module name extraction tests (unit tests):
   - test_extract_module_name_standard
   - test_extract_module_name_none
   - test_extract_module_name_with_path

8. Two-stage retrieval tests (unit tests):
   - test_embed_and_rank_fallback_on_error
   - test_auto_include_skips_embedding_under_threshold

9. Small file selector stripping tests (unit tests):
   - test_strip_selectors_from_small_files

10. Build directives tests (unit tests):
    - test_build_new_block
    - test_build_update_block
    - test_build_update_block_empty

11. Path qualification tests (unit tests):
    - test_qualify_path_absolute
    - test_qualify_path_relative
    - test_directory_prefix_glob
    - test_directory_prefix_empty

Z3 Formal Verification:
   - Strength/temperature range validation can be verified with Z3
     to prove all valid/invalid ranges are handled correctly.
   - Cost aggregation: verify total_cost = summary_cost + llm_cost
"""

import types
import sys
from unittest.mock import patch, MagicMock, PropertyMock
from pathlib import Path

import pytest

from pdd.auto_include import (
    auto_include,
    _validate_input,
    _format_csv_rows_for_llm,
    _extract_module_name,
    _extract_example_modules,
    _detect_circular_dependencies,
    _filter_circular_dependencies,
    _filter_self_references,
    _filter_duplicates,
    _embed_and_rank,
    _build_new_block,
    _build_update_block,
    _build_include_directives,
    _directory_prefix,
    _strip_selectors_from_small_files,
    AutoIncludeResult,
    NewInclude,
    IncludeAnnotation,
)


# ============================================================================
# Fixtures
# ============================================================================

@pytest.fixture
def mock_load_prompt_template():
    with patch("pdd.auto_include.load_prompt_template") as m:
        m.return_value = "mock prompt template {input_prompt} {available_includes}"
        yield m


@pytest.fixture
def mock_summarize_directory():
    with patch("pdd.auto_include.summarize_directory") as m:
        m.return_value = (
            "full_path,file_summary,date,key_exports,dependencies\n"
            "context/example.py,Example summary,2023-02-02,\"['func']\",\"[]\"\n",
            0.25,
            "mock-summary-model",
        )
        yield m


@pytest.fixture
def mock_llm_invoke():
    with patch("pdd.auto_include.llm_invoke") as m:
        yield m


@pytest.fixture
def mock_embed_and_retrieve():
    with patch("pdd.auto_include.embed_and_retrieve") as m:
        yield m


# ============================================================================
# 1. Input Validation Tests
# ============================================================================

def test_validate_input_valid():
    """Valid strength and temperature should not raise."""
    _validate_input(0.5, 0.5)
    _validate_input(0.0, 0.0)
    _validate_input(1.0, 1.0)


def test_validate_input_invalid_strength_high():
    with pytest.raises(ValueError, match="Strength"):
        _validate_input(1.5, 0.5)


def test_validate_input_invalid_strength_low():
    with pytest.raises(ValueError, match="Strength"):
        _validate_input(-0.1, 0.5)


def test_validate_input_invalid_temperature_high():
    with pytest.raises(ValueError, match="Temperature"):
        _validate_input(0.5, 1.5)


def test_validate_input_invalid_temperature_low():
    with pytest.raises(ValueError, match="Temperature"):
        _validate_input(0.5, -0.1)


def test_auto_include_invalid_strength(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    with pytest.raises(ValueError, match="Strength"):
        auto_include(
            input_prompt="test",
            directory_path="context/*.py",
            strength=2.0,
            temperature=0.0,
        )


def test_auto_include_invalid_temperature(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    with pytest.raises(ValueError, match="Temperature"):
        auto_include(
            input_prompt="test",
            directory_path="context/*.py",
            strength=0.5,
            temperature=-1.0,
        )


def test_auto_include_empty_prompt_raises(mock_load_prompt_template):
    """When load_prompt_template returns None, auto_include raises ValueError."""
    mock_load_prompt_template.return_value = None
    with pytest.raises(ValueError, match="Failed to load"):
        auto_include(
            input_prompt="test prompt",
            directory_path="context/*.py",
            strength=0.5,
            temperature=0.0,
        )


# ============================================================================
# 2. Core auto_include flow tests
# ============================================================================

def test_auto_include_returns_four_tuple(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """auto_include should return a 4-tuple."""
    result = AutoIncludeResult(
        reasoning="test",
        new_includes=[NewInclude(file="context/helper.py", module="utils")],
        existing_include_annotations=[],
    )
    mock_llm_invoke.return_value = {
        "result": result,
        "cost": 0.5,
        "model_name": "mock-model",
    }

    output = auto_include(
        input_prompt="Process data",
        directory_path="context/*.py",
        strength=0.7,
        temperature=0.0,
    )

    assert isinstance(output, tuple)
    assert len(output) == 4
    deps, csv_out, cost, model = output
    assert isinstance(deps, str)
    assert isinstance(csv_out, str)
    assert isinstance(cost, float)
    assert isinstance(model, str)


def test_auto_include_cost_aggregation(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """total_cost should be summary_cost + llm_cost."""
    result = AutoIncludeResult(
        reasoning="test",
        new_includes=[],
        existing_include_annotations=[],
    )
    mock_llm_invoke.return_value = {
        "result": result,
        "cost": 0.75,
        "model_name": "mock-model",
    }

    _, _, total_cost, _ = auto_include(
        input_prompt="Process data",
        directory_path="context/*.py",
        strength=0.7,
        temperature=0.0,
    )

    # summary_cost = 0.25, llm_cost = 0.75
    assert total_cost == pytest.approx(1.0)


def test_auto_include_llm_failure_returns_empty(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """When LLM invocation fails, return empty dependencies."""
    mock_llm_invoke.side_effect = Exception("LLM error")

    deps, csv_out, cost, model = auto_include(
        input_prompt="Process data",
        directory_path="context/*.py",
        strength=0.7,
        temperature=0.0,
    )

    assert deps == ""
    assert "full_path" in csv_out
    assert cost == 0.25  # only summary cost
    assert model == "mock-summary-model"


def test_auto_include_verbose_flag(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """verbose=True should not raise errors."""
    result = AutoIncludeResult(
        reasoning="test",
        new_includes=[],
        existing_include_annotations=[],
    )
    mock_llm_invoke.return_value = {
        "result": result,
        "cost": 0.1,
        "model_name": "mock-model",
    }

    deps, _, _, _ = auto_include(
        input_prompt="Process data",
        directory_path="context/*.py",
        strength=0.7,
        temperature=0.0,
        verbose=True,
    )

    assert isinstance(deps, str)


# ============================================================================
# 3. CSV formatting tests
# ============================================================================

def test_format_csv_rows_empty():
    assert _format_csv_rows_for_llm("") == ""


def test_format_csv_rows_valid():
    csv = (
        "full_path,file_summary,date,key_exports,dependencies\n"
        "helper.py,Helper functions,2023-01-01,\"['func']\",\"[]\"\n"
    )
    result = _format_csv_rows_for_llm(csv)
    assert "File:" in result
    assert "Purpose:" in result
    assert "Key Exports:" in result


def test_format_csv_rows_invalid():
    """Invalid CSV should not raise but return empty."""
    result = _format_csv_rows_for_llm("not,a,valid\ncsv,without,header\n")
    # Should still produce something or empty without error
    assert isinstance(result, str)


# ============================================================================
# 4. Self-reference filtering tests
# ============================================================================

def test_filter_self_references_removes_own_example():
    directives = (
        '<new>\n<mod><include>context/agentic_fix_example.py</include></mod>\n</new>\n'
        '<new>\n<mod><include>context/other_example.py</include></mod>\n</new>'
    )
    result = _filter_self_references(directives, "agentic_fix")
    assert "agentic_fix_example.py" not in result
    assert "other_example.py" in result


def test_filter_self_references_no_module_name():
    directives = '<new>\n<mod><include>context/agentic_fix_example.py</include></mod>\n</new>'
    result = _filter_self_references(directives, None)
    assert "agentic_fix_example.py" in result


# ============================================================================
# 5. Circular dependency tests
# ============================================================================

def test_extract_example_modules_basic():
    content = '<include>context/agentic_bug_example.py</include>'
    result = _extract_example_modules(content)
    assert "agentic_bug" in result


def test_extract_example_modules_empty():
    result = _extract_example_modules("no includes here")
    assert result == set()


def test_extract_example_modules_subdirectory():
    content = '<include>context/backend/credit_helpers_example.py</include>'
    result = _extract_example_modules(content)
    assert "credit_helpers" in result


def test_extract_example_modules_multiple():
    content = (
        '<include>context/module_a_example.py</include>\n'
        '<include>context/module_b_example.py</include>\n'
        '<include>context/regular_file.py</include>'
    )
    result = _extract_example_modules(content)
    assert "module_a" in result
    assert "module_b" in result
    assert len(result) == 2


def test_filter_circular_dependencies_empty_cycles():
    directives = '<new>\n<mod><include>context/a_example.py</include></mod>\n</new>'
    result = _filter_circular_dependencies(directives, [])
    assert result == directives


def test_filter_circular_dependencies_removes_problematic():
    directives = (
        '<new>\n<mod><include>context/module_b_example.py</include></mod>\n</new>\n'
        '<new>\n<mod><include>context/module_c_example.py</include></mod>\n</new>'
    )
    cycles = [["module_a_python.prompt", "module_b_python.prompt", "module_a_python.prompt"]]
    result = _filter_circular_dependencies(directives, cycles)
    assert "module_b_example.py" not in result
    assert "module_c_example.py" in result


def test_detect_circular_no_module_name():
    """No module name -> no cycles detected."""
    result = _detect_circular_dependencies("", "some deps")
    assert result == []


def test_detect_circular_no_dep_modules():
    """No example modules in dependencies -> no cycles."""
    result = _detect_circular_dependencies(
        "prompts/test_python.prompt", "no example includes"
    )
    assert result == []


# ============================================================================
# 6. Duplicate filtering tests
# ============================================================================

def test_filter_duplicates_removes_existing():
    directives = '<new>\n<mod><include>context/helper.py</include></mod>\n</new>'
    input_prompt = 'Some text <include>context/helper.py</include> more text'
    result = _filter_duplicates(directives, input_prompt)
    assert "helper.py" not in result


def test_filter_duplicates_no_existing():
    directives = '<new>\n<mod><include>context/helper.py</include></mod>\n</new>'
    input_prompt = 'Some text without includes'
    result = _filter_duplicates(directives, input_prompt)
    assert "helper.py" in result


def test_filter_duplicates_basename_match():
    """Should detect duplicates even with different path prefixes."""
    directives = '<new>\n<mod><include>context/helper.py</include></mod>\n</new>'
    input_prompt = 'Text <include>helper.py</include>'
    result = _filter_duplicates(directives, input_prompt)
    assert "helper.py" not in result or "<new>" not in result


# ============================================================================
# 7. Module name extraction tests
# ============================================================================

def test_extract_module_name_standard():
    assert _extract_module_name("agentic_fix_python.prompt") == "agentic_fix"


def test_extract_module_name_with_path():
    assert _extract_module_name("prompts/agentic_fix_python.prompt") == "agentic_fix"


def test_extract_module_name_none():
    assert _extract_module_name(None) is None


def test_extract_module_name_no_match():
    result = _extract_module_name("invalid_filename.txt")
    assert result is None


def test_extract_module_name_llm_suffix():
    assert _extract_module_name("some_module_LLM.prompt") == "some_module"


# ============================================================================
# 8. Two-stage retrieval tests
# ============================================================================

def test_embed_and_rank_fallback_on_error():
    """On failure, _embed_and_rank returns original candidates."""
    candidates = ["File: a.py\nPurpose: test", "File: b.py\nPurpose: test2"]
    with patch("pdd.auto_include.embed_and_retrieve", side_effect=Exception("fail")):
        result = _embed_and_rank("query", candidates)
    assert result == candidates


def test_embed_and_rank_success():
    """On success, returns ranked candidates."""
    candidates = ["File: a.py\nPurpose: test", "File: b.py\nPurpose: test2"]
    ranked = [("File: b.py\nPurpose: test2", 0.9), ("File: a.py\nPurpose: test", 0.5)]
    with patch("pdd.auto_include.embed_and_retrieve", return_value=ranked):
        result = _embed_and_rank("query", candidates, top_n=2)
    assert result == ["File: b.py\nPurpose: test2", "File: a.py\nPurpose: test"]


def test_auto_include_embedding_prefilter_over_50(
    mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke
):
    """When candidates > 50, embedding pre-filter should be invoked."""
    # Create CSV with >50 rows
    rows = "full_path,file_summary,date,key_exports,dependencies\n"
    for i in range(55):
        rows += f"file_{i}.py,Summary {i},2023-01-01,\"[]\",\"[]\"\n"
    mock_summarize_directory.return_value = (rows, 0.1, "model")

    result = AutoIncludeResult(
        reasoning="test", new_includes=[], existing_include_annotations=[]
    )
    mock_llm_invoke.return_value = {
        "result": result,
        "cost": 0.1,
        "model_name": "mock-model",
    }

    with patch("pdd.auto_include._embed_and_rank") as mock_rank:
        mock_rank.return_value = ["File: file_0.py\nPurpose: Summary 0"]
        auto_include(
            input_prompt="test",
            directory_path="context/*.py",
            strength=0.7,
            temperature=0.0,
        )
        mock_rank.assert_called_once()


# ============================================================================
# 9. Build directives tests
# ============================================================================

def test_build_new_block_simple():
    inc = NewInclude(file="context/helper.py", module="utils")
    result = _build_new_block(inc)
    assert "<new>" in result
    assert "<include>" in result
    assert "context/helper.py" in result
    assert "<utils>" in result
    assert "</utils>" in result

# ============================================================================
# 10. Path handling bug tests (issue #603)
#
# When project_dependencies.csv preserves entries from multiple directory scans
# (the fix for CSV wipeout), downstream code must handle mixed-origin paths
# correctly. These tests surface bugs where it doesn't.
# ============================================================================


class TestFormatCsvRowsCrossDirectoryPaths:
    """_format_csv_rows_for_llm blindly prepends directory_path to ALL
    relative paths. When the CSV has entries from a different scan scope,
    this produces nonexistent paths."""

    def test_cross_directory_entries_not_misqualified(self, tmp_path):
        """CSV has 'cli.py' (from pdd/ scan) and 'example_a.py' (from
        context/ scan). Formatting with directory_path=context/ should NOT
        turn 'cli.py' into 'context/cli.py'.
        """
        context_dir = tmp_path / "context"
        context_dir.mkdir()

        csv_data = (
            "full_path,file_summary,key_exports,dependencies,content_hash\n"
            "example_a.py,An example file,\"[]\",\"[]\",abc123\n"
            "cli.py,CLI entry point,\"[]\",\"[]\",def456\n"
        )
        result = _format_csv_rows_for_llm(csv_data, directory_path=str(context_dir))
        lines = result.split("\n")
        file_lines = [l for l in lines if l.startswith("File:")]
        misqualified = [l for l in file_lines if "context" in l and "cli.py" in l]
        assert not misqualified, (
            f"cli.py was misqualified with context/ prefix. It came from a "
            f"different scan (pdd/) and should not be requalified. "
            f"File lines: {file_lines}"
        )

    def test_already_qualified_paths_not_double_qualified(self, tmp_path):
        """CSV has 'context/example_a.py' (already qualified from a root
        scan). Formatting with directory_path='context/' should NOT produce
        'context/context/example_a.py'.
        """
        context_dir = tmp_path / "context"
        context_dir.mkdir()

        csv_data = (
            "full_path,file_summary,key_exports,dependencies,content_hash\n"
            "context/example_a.py,An example,\"[]\",\"[]\",abc123\n"
        )
        result = _format_csv_rows_for_llm(csv_data, directory_path=str(context_dir))
        assert "context/context" not in result and "context\\context" not in result, (
            f"Path was double-qualified. Result:\n{result}"
        )


class TestAutoIncludeCrossDirectoryPaths:
    """When the CSV has entries from multiple directory scans, auto_include
    must not corrupt paths by blindly prepending directory_path. These tests
    exercise the full auto_include() public API with a mixed-origin CSV."""

    @patch("pdd.auto_include.llm_invoke")
    @patch("pdd.auto_include.summarize_directory")
    def test_cross_directory_entry_not_misqualified(
        self, mock_summarize, mock_llm, tmp_path, monkeypatch
    ):
        """CSV has 'cli.py' (from pdd/ scan) and 'example_a.py' (from
        context/ scan). auto_include with directory_path=context/ should NOT
        turn 'cli.py' into 'context/cli.py' in the LLM's input or output.
        """
        monkeypatch.chdir(tmp_path)
        context_dir = tmp_path / "context"
        context_dir.mkdir()
        (context_dir / "example_a.py").write_text("# example\n" * 200)

        pdd_dir = tmp_path / "pdd"
        pdd_dir.mkdir()
        (pdd_dir / "cli.py").write_text("# cli\n" * 200)

        # Mixed-origin CSV: entries from both context/ and pdd/ scans
        mixed_csv = (
            "full_path,file_summary,key_exports,dependencies,content_hash\n"
            "example_a.py,An example,\"[]\",\"[]\",abc123\n"
            "cli.py,CLI entry point,\"[]\",\"[]\",def456\n"
        )
        mock_summarize.return_value = (mixed_csv, 0.001, "mock")

        # LLM returns a new include for cli.py (which came from pdd/ scan)
        mock_result = AutoIncludeResult(
            reasoning="Need CLI",
            new_includes=[NewInclude(file="cli.py", module="cli")],
            existing_include_annotations=[],
        )
        mock_llm.return_value = {"result": mock_result, "cost": 0.01, "model_name": "mock"}

        directives, _, _, _ = auto_include(
            input_prompt="Generate a tool",
            directory_path=str(context_dir),
            strength=0.7,
            temperature=0.0,
        )

        # cli.py should NOT be qualified as context/cli.py — it's from pdd/
        assert "context/cli.py" not in directives and "context\\cli.py" not in directives, (
            f"cli.py was misqualified with context/ prefix. Directives:\n{directives}"
        )

    @patch("pdd.auto_include.llm_invoke")
    @patch("pdd.auto_include.summarize_directory")
    def test_already_qualified_path_not_double_qualified(
        self, mock_summarize, mock_llm, tmp_path, monkeypatch
    ):
        """CSV has 'context/example_a.py' (from a root scan). auto_include
        with directory_path='context/' should NOT produce
        'context/context/example_a.py'.
        """
        monkeypatch.chdir(tmp_path)
        context_dir = tmp_path / "context"
        context_dir.mkdir()
        (context_dir / "example_a.py").write_text("# example\n" * 200)

        csv_data = (
            "full_path,file_summary,key_exports,dependencies,content_hash\n"
            "context/example_a.py,An example,\"[]\",\"[]\",abc123\n"
        )
        mock_summarize.return_value = (csv_data, 0.001, "mock")

        mock_result = AutoIncludeResult(
            reasoning="Need example",
            new_includes=[NewInclude(file="context/example_a.py", module="example")],
            existing_include_annotations=[],
        )
        mock_llm.return_value = {"result": mock_result, "cost": 0.01, "model_name": "mock"}

        directives, _, _, _ = auto_include(
            input_prompt="Generate a tool",
            directory_path=str(context_dir),
            strength=0.7,
            temperature=0.0,
        )

        assert "context/context" not in directives and "context\\context" not in directives, (
            f"Path was double-qualified in directives:\n{directives}"
        )

    @patch("pdd.auto_include.llm_invoke")
    @patch("pdd.auto_include.summarize_directory")
    def test_dot_directory_does_not_corrupt_paths(
        self, mock_summarize, mock_llm, tmp_path, monkeypatch
    ):
        """Scanning from '.' (project root) should not prepend './' to paths
        in the LLM input or corrupt paths in the output."""
        monkeypatch.chdir(tmp_path)
        (tmp_path / "pdd").mkdir()
        (tmp_path / "pdd" / "cli.py").write_text("# cli\n" * 200)

        csv_data = (
            "full_path,file_summary,key_exports,dependencies,content_hash\n"
            "pdd/cli.py,CLI entry,\"[]\",\"[]\",abc\n"
        )
        mock_summarize.return_value = (csv_data, 0.001, "mock")

        mock_result = AutoIncludeResult(
            reasoning="Need CLI",
            new_includes=[NewInclude(file="pdd/cli.py", module="cli")],
            existing_include_annotations=[],
        )
        mock_llm.return_value = {"result": mock_result, "cost": 0.01, "model_name": "mock"}

        directives, _, _, _ = auto_include(
            input_prompt="Generate a tool",
            directory_path=".",
            strength=0.7,
            temperature=0.0,
        )

        # Path should remain 'pdd/cli.py', not './pdd/cli.py'
        assert "./pdd/" not in directives, (
            f"Path was unnecessarily prefixed with './': {directives}"
        )
