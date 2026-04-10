from pathlib import Path
import textwrap

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
