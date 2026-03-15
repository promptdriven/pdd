"""Unit tests for the auto_include module.

Tests are organized around the prompt requirements:
  1. Load auto_include_LLM prompt template
  2. Run summarize_directory and format CSV rows for LLM
  3. Invoke LLM with Pydantic AutoIncludeResult
  4. Build include_directives with <new> and <update> tags
  5. Filter duplicates, self-references, circular dependencies
  6. Strip selectors from small files (<100 lines)
  7. Validate inputs; on LLM failure return empty directives
  8. Return (include_directives, csv_output, total_cost, model_name)
"""
import os
import textwrap
from unittest.mock import patch, MagicMock

import pytest

from pdd.auto_include import (
    auto_include,
    AutoIncludeResult,
    NewInclude,
    IncludeAnnotation,
    _build_include_directives,
    _build_new_block,
    _build_update_block,
    _extract_module_name,
    _extract_example_modules,
    _filter_duplicates,
    _filter_self_references,
    _filter_circular_dependencies,
    _detect_circular_dependencies,
    _format_csv_rows_for_llm,
    _strip_selectors_from_small_files,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

CSV_OUTPUT = (
    "full_path,file_summary,key_exports,dependencies,content_hash\n"
    'context/example.py,"Example utilities","[""foo"", ""bar""]","[""os""]",abc123'
)


@pytest.fixture(name="mock_load_prompt_template")
def mock_load_prompt_template_fixture():
    with patch("pdd.auto_include.load_prompt_template") as mock_load:
        mock_load.return_value = "auto_include_LLM prompt content"
        yield mock_load


@pytest.fixture(name="mock_summarize_directory")
def mock_summarize_directory_fixture():
    with patch("pdd.auto_include.summarize_directory") as mock_summarize:
        mock_summarize.return_value = (CSV_OUTPUT, 0.10, "mock-summary-model")
        yield mock_summarize


@pytest.fixture(name="mock_llm_invoke")
def mock_llm_invoke_fixture():
    with patch("pdd.auto_include.llm_invoke") as mock_llm:
        yield mock_llm


def _make_llm_response(result: AutoIncludeResult, cost: float = 0.50, model: str = "mock-model"):
    """Helper to build a mock llm_invoke response dict."""
    return {"result": result, "cost": cost, "model_name": model}


# ---------------------------------------------------------------------------
# Req 1 — Load prompt template
# ---------------------------------------------------------------------------

class TestLoadPromptTemplate:
    def test_loads_auto_include_LLM(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        """Should call load_prompt_template('auto_include_LLM')."""
        mock_llm_invoke.return_value = _make_llm_response(AutoIncludeResult(reasoning="", new_includes=[], existing_include_annotations=[]))
        auto_include("prompt", "dir/*.py")
        mock_load_prompt_template.assert_called_once_with("auto_include_LLM")

    def test_raises_when_template_not_found(self):
        """Req 7: raise ValueError if prompt template cannot be loaded."""
        with patch("pdd.auto_include.load_prompt_template", return_value=None):
            with pytest.raises(ValueError, match="Failed to load prompt template"):
                auto_include("prompt", "dir/*.py")


# ---------------------------------------------------------------------------
# Req 2 — Summarize directory and format CSV rows
# ---------------------------------------------------------------------------

class TestFormatCsvRows:
    def test_format_csv_rows_structure(self):
        """CSV rows should be formatted as File/Purpose/Key Exports/Dependencies."""
        csv = (
            "full_path,file_summary,key_exports,dependencies,content_hash\n"
            'context/api.py,"API helpers","[""get"", ""post""]","[""requests""]",hash1'
        )
        result = _format_csv_rows_for_llm(csv)
        assert "File: context/api.py" in result
        assert "Purpose: API helpers" in result
        assert "Key Exports:" in result
        assert "Dependencies:" in result

    def test_format_csv_rows_empty(self):
        assert _format_csv_rows_for_llm("") == ""

    def test_format_csv_rows_bad_csv(self):
        """Should return empty string on unparseable CSV."""
        assert _format_csv_rows_for_llm("not,csv\ndata") == "" or isinstance(_format_csv_rows_for_llm("not,csv\ndata"), str)


# ---------------------------------------------------------------------------
# Req 3 — Single LLM call with Pydantic structured output
# ---------------------------------------------------------------------------

class TestLLMInvocation:
    def test_single_llm_call_with_pydantic(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        """Should invoke llm_invoke exactly once with output_pydantic=AutoIncludeResult."""
        result_obj = AutoIncludeResult(
            reasoning="chose api.py",
            new_includes=[NewInclude(file="context/api.py", module="core.api")],
            existing_include_annotations=[],
        )
        mock_llm_invoke.return_value = _make_llm_response(result_obj)

        auto_include("some prompt", "context/*.py")

        assert mock_llm_invoke.call_count == 1
        call_kwargs = mock_llm_invoke.call_args
        assert call_kwargs.kwargs.get("output_pydantic") is AutoIncludeResult or \
               (len(call_kwargs.args) > 0 or call_kwargs[1].get("output_pydantic") is AutoIncludeResult)

    def test_passes_available_includes_to_llm(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        """Should pass formatted available_includes as input_json to llm_invoke."""
        result_obj = AutoIncludeResult(reasoning="", new_includes=[], existing_include_annotations=[])
        mock_llm_invoke.return_value = _make_llm_response(result_obj)

        auto_include("my prompt text", "context/*.py")

        call_kwargs = mock_llm_invoke.call_args
        input_json = call_kwargs.kwargs.get("input_json") or call_kwargs[1].get("input_json")
        assert "input_prompt" in input_json
        assert input_json["input_prompt"] == "my prompt text"
        assert "available_includes" in input_json


# ---------------------------------------------------------------------------
# Req 4 — Build include_directives with <new> and <update> tags
# ---------------------------------------------------------------------------

class TestBuildIncludeDirectives:
    def test_new_block_plain(self):
        inc = NewInclude(file="core/api.py", module="core.api")
        block = _build_new_block(inc)
        assert "<new>" in block
        assert "</new>" in block
        assert "<core.api>" in block
        assert "<include>core/api.py</include>" in block

    def test_new_block_with_select(self):
        inc = NewInclude(file="core/api.py", module="core.api", select="class:Handler")
        block = _build_new_block(inc)
        assert 'select="class:Handler"' in block
        assert "<include" in block

    def test_new_block_with_query(self):
        inc = NewInclude(file="spec.md", module="spec", query="List auth requirements")
        block = _build_new_block(inc)
        assert 'query="List auth requirements"' in block

    def test_update_block_with_select(self):
        ann = IncludeAnnotation(file="auth.py", select="def:require_admin")
        block = _build_update_block(ann)
        assert "<update>" in block
        assert 'select="def:require_admin"' in block

    def test_update_block_skips_no_attributes(self):
        """Skip <update> entries with neither select nor query."""
        ann = IncludeAnnotation(file="auth.py")
        block = _build_update_block(ann)
        assert block == ""

    def test_full_directive_output(self):
        result = AutoIncludeResult(
            reasoning="test",
            new_includes=[
                NewInclude(file="core/api.py", module="core.api", select="class:Handler"),
                NewInclude(file="utils/validators.py", module="utils.validators"),
            ],
            existing_include_annotations=[
                IncludeAnnotation(file="auth_helpers.py", select="def:require_admin,def:get_current_user"),
                IncludeAnnotation(file="plain.py"),  # should be skipped
            ],
        )
        directives = _build_include_directives(result)
        assert directives.count("<new>") == 2
        assert directives.count("<update>") == 1  # plain.py skipped
        assert "plain.py" not in directives


# ---------------------------------------------------------------------------
# Req 5 — Filter duplicates, self-references, circular deps
# ---------------------------------------------------------------------------

class TestFiltering:
    def test_filter_duplicates(self):
        """Remove <new> blocks whose file is already in the prompt."""
        input_prompt = "<include>context/python_preamble.prompt</include>"
        directives = (
            "<new>\n<preamble><include>context/python_preamble.prompt</include></preamble>\n</new>\n"
            "<new>\n<helper><include>context/helper.py</include></helper>\n</new>"
        )
        result = _filter_duplicates(directives, input_prompt)
        assert "python_preamble.prompt" not in result
        assert "helper.py" in result

    def test_filter_self_references(self):
        """Remove <new> blocks referencing the module's own example file."""
        directives = (
            "<new>\n<mod><include>context/agentic_fix_example.py</include></mod>\n</new>\n"
            "<new>\n<other><include>context/other_example.py</include></other>\n</new>"
        )
        result = _filter_self_references(directives, "agentic_fix")
        assert "agentic_fix_example.py" not in result
        assert "other_example.py" in result

    def test_filter_self_references_subdirectory(self):
        directives = "<new>\n<mod><include>context/backend/credit_helpers_example.py</include></mod>\n</new>"
        result = _filter_self_references(directives, "credit_helpers")
        assert "credit_helpers_example.py" not in result

    def test_filter_self_references_no_module(self):
        directives = "<new>\n<mod><include>context/example.py</include></mod>\n</new>"
        assert _filter_self_references(directives, None) == directives

    def test_detect_circular_direct_cycle(self, tmp_path):
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        # module_b's prompt includes module_a's example
        (prompts_dir / "module_b_python.prompt").write_text(
            "<include>context/module_a_example.py</include>"
        )
        current = str(prompts_dir / "module_a_python.prompt")
        new_deps = "<new>\n<mod><include>context/module_b_example.py</include></mod>\n</new>"
        cycles = _detect_circular_dependencies(current, new_deps, prompts_dir=str(prompts_dir))
        assert len(cycles) >= 1

    def test_detect_circular_no_cycle(self, tmp_path):
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        (prompts_dir / "module_b_python.prompt").write_text(
            "<include>context/other_example.py</include>"
        )
        current = str(prompts_dir / "module_a_python.prompt")
        new_deps = "<new>\n<mod><include>context/module_b_example.py</include></mod>\n</new>"
        cycles = _detect_circular_dependencies(current, new_deps, prompts_dir=str(prompts_dir))
        assert cycles == []

    def test_filter_circular_removes_problematic(self):
        directives = (
            "<new>\n<mod_b><include>context/module_b_example.py</include></mod_b>\n</new>\n"
            "<new>\n<mod_c><include>context/module_c_example.py</include></mod_c>\n</new>"
        )
        cycles = [["module_a_python.prompt", "module_b_python.prompt", "module_a_python.prompt"]]
        result = _filter_circular_dependencies(directives, cycles)
        assert "module_b_example.py" not in result
        assert "module_c_example.py" in result

    def test_filter_circular_empty_cycles(self):
        directives = "<new>\n<mod><include>context/module_b_example.py</include></mod>\n</new>"
        assert _filter_circular_dependencies(directives, []) == directives


class TestExtractModuleName:
    def test_python_suffix(self):
        assert _extract_module_name("prompts/agentic_fix_python.prompt") == "agentic_fix"

    def test_llm_suffix(self):
        assert _extract_module_name("prompts/some_module_LLM.prompt") == "some_module"

    def test_none(self):
        assert _extract_module_name(None) is None

    def test_no_match(self):
        assert _extract_module_name("invalid") is None


class TestExtractExampleModules:
    def test_basic(self):
        content = "<include>context/agentic_bug_example.py</include>"
        result = _extract_example_modules(content)
        assert "agentic_bug" in result

    def test_subdirectory(self):
        content = "<include>context/backend/credit_helpers_example.py</include>"
        result = _extract_example_modules(content)
        assert "credit_helpers" in result

    def test_empty(self):
        assert _extract_example_modules("no includes here") == set()

    def test_non_example_files_excluded(self):
        content = "<include>context/regular_file.py</include>"
        result = _extract_example_modules(content)
        assert len(result) == 0


# ---------------------------------------------------------------------------
# Req 6 — Strip selectors from small files
# ---------------------------------------------------------------------------

class TestStripSelectorsSmallFiles:
    def test_new_block_small_file_strips_selector(self, tmp_path):
        """For <new> blocks with small files, remove select/query but keep include."""
        small_file = tmp_path / "small.py"
        small_file.write_text("x = 1\n")  # 1 line < 100

        directives = f'<new>\n<mod><include select="class:Foo">{small_file}</include></mod>\n</new>'
        with patch("pdd.auto_include._get_file_line_count", return_value=1):
            result = _strip_selectors_from_small_files(directives)
        assert 'select=' not in result
        assert "<include>" in result
        assert str(small_file) in result

    def test_update_block_small_file_removed(self):
        """For <update> blocks with small files, remove the entire block."""
        directives = '<update>\n<include select="def:foo">small.py</include>\n</update>'
        with patch("pdd.auto_include._get_file_line_count", return_value=10):
            result = _strip_selectors_from_small_files(directives)
        assert result == ""

    def test_large_file_keeps_selector(self):
        """Files >= 100 lines should keep their selectors."""
        directives = '<new>\n<mod><include select="class:Foo">large.py</include></mod>\n</new>'
        with patch("pdd.auto_include._get_file_line_count", return_value=200):
            result = _strip_selectors_from_small_files(directives)
        assert 'select="class:Foo"' in result

    def test_relative_path_resolved_via_directory_path(self, tmp_path):
        """Relative paths should be resolved against directory_path for line counting."""
        large_file = tmp_path / "utils.py"
        large_file.write_text("\n".join(f"line {i}" for i in range(150)))  # 150 lines

        # Without directory_path, relative "utils.py" can't be found → treated as 0 lines → stripped
        directives = '<update>\n<include select="def:foo">utils.py</include>\n</update>'
        result = _strip_selectors_from_small_files(directives)
        assert result == ""  # stripped because file not found

        # With directory_path, "utils.py" resolves to tmp_path/utils.py → 150 lines → kept
        result = _strip_selectors_from_small_files(directives, directory_path=str(tmp_path))
        assert 'select="def:foo"' in result
        assert "utils.py" in result

    def test_new_block_relative_path_resolved_via_directory_path(self, tmp_path):
        """<new> blocks with relative paths should also resolve via directory_path."""
        small_file = tmp_path / "tiny.py"
        small_file.write_text("x = 1\n")  # 1 line

        large_file = tmp_path / "big.py"
        large_file.write_text("\n".join(f"line {i}" for i in range(150)))

        # Small file: selector stripped but include kept
        directives = '<new>\n<mod><include select="class:X">tiny.py</include></mod>\n</new>'
        result = _strip_selectors_from_small_files(directives, directory_path=str(tmp_path))
        assert 'select=' not in result
        assert "<include>" in result

        # Large file: selector preserved
        directives = '<new>\n<mod><include select="class:X">big.py</include></mod>\n</new>'
        result = _strip_selectors_from_small_files(directives, directory_path=str(tmp_path))
        assert 'select="class:X"' in result


# ---------------------------------------------------------------------------
# Req 7 — Validate inputs; on LLM failure return empty directives
# ---------------------------------------------------------------------------

class TestValidation:
    def test_strength_out_of_range(self):
        with pytest.raises(ValueError, match="Strength"):
            auto_include("prompt", "dir/*.py", strength=1.5)

    def test_temperature_out_of_range(self):
        with pytest.raises(ValueError, match="Temperature"):
            auto_include("prompt", "dir/*.py", temperature=-0.1)

    def test_strength_zero_and_one_are_valid(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        result_obj = AutoIncludeResult(reasoning="", new_includes=[], existing_include_annotations=[])
        mock_llm_invoke.return_value = _make_llm_response(result_obj)
        # Should not raise
        auto_include("prompt", "dir/*.py", strength=0.0, temperature=0.0)
        auto_include("prompt", "dir/*.py", strength=1.0, temperature=1.0)

    def test_llm_failure_returns_empty(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        """On LLM failure, return empty include_directives (not raise)."""
        mock_llm_invoke.side_effect = RuntimeError("LLM service unavailable")

        directives, csv_out, cost, model = auto_include("prompt", "dir/*.py")

        assert directives == ""
        assert csv_out == CSV_OUTPUT
        assert cost == 0.10  # only summarize cost
        assert model == "mock-summary-model"


# ---------------------------------------------------------------------------
# Req 8 — Return tuple integration tests
# ---------------------------------------------------------------------------

class TestIntegration:
    def test_basic_successful_call(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        """Full happy-path: returns (include_directives, csv_output, total_cost, model_name)."""
        result_obj = AutoIncludeResult(
            reasoning="chose api.py",
            new_includes=[NewInclude(file="context/api.py", module="core.api", select="class:Handler")],
            existing_include_annotations=[
                IncludeAnnotation(file="auth.py", select="def:login"),
            ],
        )
        mock_llm_invoke.return_value = _make_llm_response(result_obj, cost=0.50, model="gpt-4o")

        with patch("pdd.auto_include._get_file_line_count", return_value=200):
            directives, csv_out, total_cost, model_name = auto_include(
                input_prompt="Write a module...",
                directory_path="context/*.py",
            )

        assert "<new>" in directives
        assert "core.api" in directives
        assert 'select="class:Handler"' in directives
        assert "<update>" in directives
        assert 'select="def:login"' in directives
        assert csv_out == CSV_OUTPUT
        assert total_cost == pytest.approx(0.60)  # 0.10 + 0.50
        assert model_name == "gpt-4o"

    def test_verbose_does_not_crash(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        result_obj = AutoIncludeResult(reasoning="", new_includes=[], existing_include_annotations=[])
        mock_llm_invoke.return_value = _make_llm_response(result_obj)
        # Should not raise
        auto_include("prompt", "dir/*.py", verbose=True)

    def test_progress_callback_forwarded(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        """progress_callback should be passed through to summarize_directory."""
        result_obj = AutoIncludeResult(reasoning="", new_includes=[], existing_include_annotations=[])
        mock_llm_invoke.return_value = _make_llm_response(result_obj)

        cb = MagicMock()
        auto_include("prompt", "dir/*.py", progress_callback=cb)

        _, kwargs = mock_summarize_directory.call_args
        assert kwargs.get("progress_callback") is cb

    def test_filters_self_reference_integration(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        """Self-referential example files should be removed end-to-end."""
        result_obj = AutoIncludeResult(
            reasoning="",
            new_includes=[
                NewInclude(file="context/agentic_fix_example.py", module="pdd.agentic_fix"),
                NewInclude(file="context/llm_invoke_example.py", module="pdd.llm_invoke"),
            ],
            existing_include_annotations=[],
        )
        mock_llm_invoke.return_value = _make_llm_response(result_obj)

        with patch("pdd.auto_include._get_file_line_count", return_value=200):
            directives, _, _, _ = auto_include(
                input_prompt="Write agentic_fix...",
                directory_path="context/*.py",
                prompt_filename="prompts/agentic_fix_python.prompt",
            )

        assert "agentic_fix_example.py" not in directives
        assert "llm_invoke_example.py" in directives

    def test_filters_duplicates_integration(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        """Includes already present in input_prompt should be removed."""
        result_obj = AutoIncludeResult(
            reasoning="",
            new_includes=[
                NewInclude(file="context/python_preamble.prompt", module="preamble"),
                NewInclude(file="context/helper.py", module="helper"),
            ],
            existing_include_annotations=[],
        )
        mock_llm_invoke.return_value = _make_llm_response(result_obj)

        with patch("pdd.auto_include._get_file_line_count", return_value=200):
            directives, _, _, _ = auto_include(
                input_prompt="<include>context/python_preamble.prompt</include>\nWrite code...",
                directory_path="context/*.py",
            )

        assert "python_preamble.prompt" not in directives
        assert "helper.py" in directives

    def test_circular_dependency_filtered_and_warned(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke, tmp_path):
        """Circular dependencies should be removed and warned about."""
        prompts_dir = tmp_path / "prompts"
        prompts_dir.mkdir()
        # module_b includes module_a's example => cycle
        (prompts_dir / "module_b_python.prompt").write_text(
            "<include>context/module_a_example.py</include>"
        )

        result_obj = AutoIncludeResult(
            reasoning="",
            new_includes=[
                NewInclude(file="context/module_b_example.py", module="pdd.module_b"),
            ],
            existing_include_annotations=[],
        )
        mock_llm_invoke.return_value = _make_llm_response(result_obj)

        with patch("pdd.auto_include._get_file_line_count", return_value=200):
            directives, _, _, _ = auto_include(
                input_prompt="Write module_a...",
                directory_path="context/*.py",
                prompt_filename=str(prompts_dir / "module_a_python.prompt"),
            )

        assert "module_b_example.py" not in directives

    def test_csv_file_passed_to_summarize(self, mock_load_prompt_template, mock_summarize_directory, mock_llm_invoke):
        """csv_file parameter should be forwarded to summarize_directory."""
        result_obj = AutoIncludeResult(reasoning="", new_includes=[], existing_include_annotations=[])
        mock_llm_invoke.return_value = _make_llm_response(result_obj)

        auto_include("prompt", "dir/*.py", csv_file="existing,csv\ndata,here")

        _, kwargs = mock_summarize_directory.call_args
        assert kwargs.get("csv_file") == "existing,csv\ndata,here"
