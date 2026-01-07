"""
Minimal contract smoke test for sync prompt/context/output resolution.
"""
from pathlib import Path

import pytest

from pdd.sync_determine_operation import get_pdd_file_paths
from pdd.sync_main import _find_prompt_in_contexts


@pytest.fixture()
def contract_smoke_project(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    repo_root = Path(__file__).resolve().parents[1]
    monkeypatch.setenv("PDD_PATH", str(repo_root))

    pddrc_path = tmp_path / ".pddrc"
    pddrc_path.write_text(
        """version: "1.0"
contexts:
  frontend-components:
    paths:
      - "frontend/components/**"
    defaults:
      default_language: "typescriptreact"
      outputs:
        prompt:
          path: "prompts/frontend/components/{category}/{name}_{language}.prompt"
        code:
          path: "frontend/src/components/{category}/{name}/{name}.tsx"
        example:
          path: "context/frontend/{name}_example.tsx"
""",
        encoding="utf-8",
    )

    prompt_path = (
        tmp_path
        / "prompts"
        / "frontend"
        / "components"
        / "marketplace"
        / "AssetCard_typescriptreact.prompt"
    )
    prompt_path.parent.mkdir(parents=True, exist_ok=True)
    prompt_path.write_text("Generate AssetCard component", encoding="utf-8")

    monkeypatch.chdir(tmp_path)
    return tmp_path


def test_contract_smoke_template_pipeline(contract_smoke_project: Path) -> None:
    result = _find_prompt_in_contexts("frontend/components/marketplace/AssetCard")
    assert result is not None

    context_name, prompt_path, language = result
    assert context_name == "frontend-components"
    assert language == "typescriptreact"

    paths = get_pdd_file_paths(
        basename="frontend/components/marketplace/AssetCard",
        language=language,
        prompts_dir="prompts",
        context_override=context_name,
    )

    expected_prompt = (
        contract_smoke_project
        / "prompts"
        / "frontend"
        / "components"
        / "marketplace"
        / "AssetCard_typescriptreact.prompt"
    )
    expected_code = (
        contract_smoke_project
        / "frontend"
        / "src"
        / "components"
        / "marketplace"
        / "AssetCard"
        / "AssetCard.tsx"
    )
    expected_example = contract_smoke_project / "context" / "frontend" / "AssetCard_example.tsx"

    assert paths["prompt"].resolve() == expected_prompt.resolve()
    assert paths["code"].resolve() == expected_code.resolve()
    assert paths["example"].resolve() == expected_example.resolve()


@pytest.fixture()
def subdirectory_project(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> Path:
    """Create a project with .pddrc at root and a subdirectory with its own prompt."""
    repo_root = Path(__file__).resolve().parents[1]
    monkeypatch.setenv("PDD_PATH", str(repo_root))

    # Create .pddrc at project root (similar to real pdd repo)
    pddrc_path = tmp_path / ".pddrc"
    pddrc_path.write_text(
        """version: "1.0"
contexts:
  examples:
    paths: ["examples/**"]
    defaults:
      generate_output_path: "src/"
      test_output_path: "tests/"
      example_output_path: "examples/"
""",
        encoding="utf-8",
    )

    # Create subdirectory with its own prompt (like examples/hello/)
    subdir = tmp_path / "examples" / "hello"
    subdir.mkdir(parents=True, exist_ok=True)
    (subdir / "hello_python.prompt").write_text("Create hello function")
    (subdir / "src").mkdir()
    (subdir / "tests").mkdir()
    (subdir / "examples").mkdir()

    # Change to subdirectory (simulating `cd examples/hello && pdd sync hello`)
    monkeypatch.chdir(subdir)
    return subdir


def test_subdirectory_paths_resolve_relative_to_cwd(subdirectory_project: Path) -> None:
    """When running from a subdirectory, paths should be CWD-relative."""
    # Use absolute path for prompts_dir to mirror how sync_main passes it at runtime
    # (sync_main calls _normalize_prompts_root which often returns absolute paths)
    paths = get_pdd_file_paths("hello", "python", prompts_dir=str(subdirectory_project))

    # Critical: code path should NOT point to project root's src/
    project_root = subdirectory_project.parent.parent
    assert not str(paths["code"].resolve()).startswith(str(project_root / "src"))
