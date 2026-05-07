import logging
import os
import textwrap
from pathlib import Path

from pdd.sync_determine_operation import get_pdd_file_paths
from pdd.validate_prompt_includes import validate_prompt_includes


def test_generate_prompt_template_does_not_instruct_fabricated_example_paths():
    template_path = Path(__file__).resolve().parent.parent / "pdd" / "templates" / "generic" / "generate_prompt.prompt"
    content = template_path.read_text(encoding="utf-8")

    assert "Do NOT fabricate file paths or assume files exist." in content
    assert (
        "If examples are not provided, use the pattern "
        "${EXAMPLE_OUTPUT_PATH}/[dependency_name]_example.${DEP_EXAMPLE_EXT}."
    ) not in content


def test_validate_prompt_includes_resolves_project_root_relative_paths(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "context" / "python_preamble.prompt").write_text("preamble", encoding="utf-8")
    (tmp_path / "prompts" / "backend").mkdir(parents=True)

    content = "<include>context/python_preamble.prompt</include>"

    validated, invalid = validate_prompt_includes(
        content,
        base_dir=tmp_path / "prompts" / "backend",
        remove_invalid=False,
    )

    assert invalid == []
    assert validated == content


def test_validate_prompt_includes_resolves_relative_includes_when_cwd_differs_from_base_dir(
    tmp_path,
):
    """Regression (Issue #225): resolution must use base_dir, not only process cwd."""
    project = tmp_path / "project"
    (project / "context").mkdir(parents=True)
    (project / "context" / "python_preamble.prompt").write_text("preamble", encoding="utf-8")
    (project / "prompts" / "backend").mkdir(parents=True)
    other_cwd = tmp_path / "other_cwd"
    other_cwd.mkdir()

    old = os.getcwd()
    try:
        os.chdir(other_cwd)
        validated, invalid = validate_prompt_includes(
            "<include>context/python_preamble.prompt</include>",
            base_dir=project / "prompts" / "backend",
            remove_invalid=False,
        )
    finally:
        os.chdir(old)

    assert invalid == []
    assert validated == "<include>context/python_preamble.prompt</include>"


def test_validate_prompt_includes_removes_optional_shared_context_blocks_when_files_are_absent(
    tmp_path,
    monkeypatch,
):
    monkeypatch.chdir(tmp_path)
    content = textwrap.dedent(
        """\
        <prompt>
        <context_data_dictionary>
        <include>prompts/_context/data_dictionary.yaml</include>
        </context_data_dictionary>
        Requirements
        1. Keep this content.
        </prompt>
        """
    )

    validated, invalid = validate_prompt_includes(
        content,
        base_dir=tmp_path / "prompts",
        remove_invalid=False,
    )

    assert invalid == []
    assert "<context_data_dictionary>" not in validated
    assert "prompts/_context/data_dictionary.yaml" not in validated
    assert "Requirements" in validated


def test_validate_prompt_includes_validates_attributed_missing_include(tmp_path, monkeypatch):
    """Attributed include tags must get the same missing-file cleanup as bare tags."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "prompts").mkdir()

    content = '<include select="def:missing_symbol">context/missing.py</include>'

    validated, invalid = validate_prompt_includes(
        content,
        base_dir=tmp_path / "prompts",
        remove_invalid=False,
    )

    assert invalid == ["context/missing.py"]
    assert validated == "<!-- Missing: context/missing.py -->"


def test_validate_prompt_includes_validates_self_closing_path_include(tmp_path, monkeypatch):
    """Self-closing include tags with path= are real include tags and need validation."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "prompts").mkdir()

    content = '<dependency><include path="context/missing.py" /></dependency>'

    validated, invalid = validate_prompt_includes(
        content,
        base_dir=tmp_path / "prompts",
        remove_invalid=False,
    )

    assert invalid == ["context/missing.py"]
    assert "<!-- Missing: context/missing.py -->" in validated
    assert "path=\"context/missing.py\"" not in validated


def test_validate_prompt_includes_preserves_case_insensitive_module_prompt_include(
    tmp_path,
    monkeypatch,
):
    """Linux-safe regression: module prompt includes follow architecture/sync casing semantics."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "parent_Python.prompt").write_text("%\n", encoding="utf-8")
    content = "<include>parent_python.prompt</include>"
    original_exists = Path.exists

    def case_sensitive_exists(path: Path) -> bool:
        if path.name == "parent_python.prompt":
            return False
        return original_exists(path)

    monkeypatch.setattr(Path, "exists", case_sensitive_exists)

    validated, invalid = validate_prompt_includes(
        content,
        base_dir=tmp_path / "prompts",
        remove_invalid=False,
    )

    assert invalid == []
    assert validated == content


def test_validate_prompt_includes_ignores_inline_code_include_examples(tmp_path, monkeypatch):
    """Literal include syntax in inline code is documentation, not a real directive."""
    monkeypatch.chdir(tmp_path)
    content = (
        'Use `<include select="def:foo">path/to/file.py</include>` for deterministic '
        'selection and `<include query="summarize auth">path/to/file.py</include>` '
        "for semantic extraction."
    )

    validated, invalid = validate_prompt_includes(
        content,
        base_dir=tmp_path,
        remove_invalid=False,
    )

    assert invalid == []
    assert validated == content


def test_validate_prompt_includes_ignores_fenced_code_include_examples(tmp_path, monkeypatch):
    """Literal include syntax in fenced code is documentation, not a real directive."""
    monkeypatch.chdir(tmp_path)
    content = textwrap.dedent(
        """\
        ```prompt
        <include select="def:foo">path/to/file.py</include>
        <include query="summarize auth">path/to/other.py</include>
        ```
        """
    )

    validated, invalid = validate_prompt_includes(
        content,
        base_dir=tmp_path,
        remove_invalid=False,
    )

    assert invalid == []
    assert validated == content


def test_validate_prompt_includes_rejects_invalid_selected_symbols(tmp_path, monkeypatch):
    """Regression for issue #798: selected includes must not silently fall back."""
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "prompts").mkdir()
    (tmp_path / "context" / "llm_invoke_example.py").write_text(
        "def run_llm_invoke_examples():\n    pass\n",
        encoding="utf-8",
    )

    content = (
        "<pdd.llm_invoke>"
        '<include select="class:TokenMatch,def:detect_control_token,'
        'def:classify_step_output,def:substitute_template_variables">'
        "context/llm_invoke_example.py"
        "</include>"
        "</pdd.llm_invoke>"
    )

    validated, invalid = validate_prompt_includes(
        content,
        base_dir=tmp_path / "prompts",
        remove_invalid=False,
    )

    assert len(invalid) == 1
    assert invalid[0].startswith("context/llm_invoke_example.py")
    assert "TokenMatch" in invalid[0]
    assert "Invalid selector" in validated
    assert "class:TokenMatch" not in validated


def test_validate_prompt_includes_allows_valid_selected_symbols(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    (tmp_path / "context").mkdir()
    (tmp_path / "prompts").mkdir()
    (tmp_path / "context" / "agentic_common.py").write_text(
        "class TokenMatch:\n    pass\n\n"
        "def detect_control_token():\n    pass\n",
        encoding="utf-8",
    )

    content = (
        '<include select="class:TokenMatch,def:detect_control_token">'
        "context/agentic_common.py"
        "</include>"
    )

    validated, invalid = validate_prompt_includes(
        content,
        base_dir=tmp_path / "prompts",
        remove_invalid=False,
    )

    assert invalid == []
    assert validated == content


def test_get_pdd_file_paths_uses_architecture_filepath_for_flattened_prompt_names(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    (tmp_path / ".pddrc").write_text(
        textwrap.dedent(
            """\
            version: "1.0"
            contexts:
              default:
                defaults:
                  generate_output_path: "src/"
                  test_output_path: "tests/"
                  example_output_path: "examples/"
            """
        ),
        encoding="utf-8",
    )
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "models_findings_python.prompt").write_text("prompt", encoding="utf-8")
    (tmp_path / "architecture.json").write_text(
        (
            '[{"filename":"models_findings_python.prompt","filepath":"src/backend/models/findings.py",'
            '"priority":1,"dependencies":[],"description":"x"}]'
        ),
        encoding="utf-8",
    )

    paths = get_pdd_file_paths("models_findings", "python", prompts_dir="prompts")

    assert paths["code"] == tmp_path / "src" / "backend" / "models" / "findings.py"
    assert paths["example"] == tmp_path / "examples" / "findings_example.py"
    assert paths["test"] == tmp_path / "tests" / "test_findings.py"


def test_get_pdd_file_paths_preserves_nested_prompt_path_when_architecture_filename_has_subdirs(
    tmp_path,
    monkeypatch,
):
    monkeypatch.chdir(tmp_path)
    (tmp_path / ".pddrc").write_text(
        textwrap.dedent(
            """\
            version: "1.0"
            contexts:
              default:
                defaults:
                  generate_output_path: "src/"
                  test_output_path: "tests/"
                  example_output_path: "examples/"
            """
        ),
        encoding="utf-8",
    )
    prompt_path = tmp_path / "prompts" / "src" / "models" / "user_python.prompt"
    prompt_path.parent.mkdir(parents=True)
    prompt_path.write_text("prompt", encoding="utf-8")
    (tmp_path / "architecture.json").write_text(
        (
            '[{"filename":"src/models/user_python.prompt","filepath":"src/models/user.py",'
            '"priority":1,"dependencies":[],"description":"x"}]'
        ),
        encoding="utf-8",
    )

    paths = get_pdd_file_paths("src/models/user", "python", prompts_dir="prompts")

    assert paths["prompt"] == prompt_path
    assert paths["code"] == tmp_path / "src" / "models" / "user.py"


def test_get_pdd_file_paths_prefers_existing_basename_artifacts_with_architecture_filepath(
    tmp_path: Path,
    monkeypatch,
    caplog,
) -> None:
    caplog.set_level(logging.INFO)
    monkeypatch.chdir(tmp_path)
    (tmp_path / ".pddrc").write_text(
        textwrap.dedent(
            """\
            version: "1.0"
            contexts:
              default:
                defaults:
                  generate_output_path: "lib/"
                  test_output_path: "tests/"
                  example_output_path: "examples/"
            """
        ),
        encoding="utf-8",
    )
    (tmp_path / "prompts").mkdir()
    (tmp_path / "prompts" / "lib_sse_python.prompt").write_text("prompt", encoding="utf-8")
    (tmp_path / "architecture.json").write_text(
        (
            '[{"filename":"lib_sse_python.prompt","filepath":"lib/sse.py",'
            '"priority":1,"dependencies":[],"description":"x"}]'
        ),
        encoding="utf-8",
    )
    (tmp_path / "examples").mkdir()
    (tmp_path / "tests").mkdir()
    existing_example = tmp_path / "examples" / "lib_sse_example.py"
    existing_test = tmp_path / "tests" / "test_lib_sse.py"
    existing_example.write_text("# example", encoding="utf-8")
    existing_test.write_text("def test_it():\n    assert True\n", encoding="utf-8")

    paths = get_pdd_file_paths("lib_sse", "python", prompts_dir="prompts")

    assert paths["code"] == tmp_path / "lib" / "sse.py"
    assert paths["example"] == existing_example
    assert paths["test"] == existing_test
    assert existing_test in paths["test_files"]
    assert "Preferring basename-derived artifacts for lib_sse over architecture stem sse" in caplog.text
