import json
import ast
from pathlib import Path

from pdd.compressed_sync_context import (
    DEFAULT_BUDGET,
    build_compressed_sync_context,
    compressed_context_is_active,
    metadata,
    render_for_prompt,
)
from pdd.sync_determine_operation import get_pdd_file_paths


def test_compressed_sync_context_metadata_is_deterministic_and_redacted(tmp_path: Path) -> None:
    prompt = tmp_path / "prompts" / "pay_python.prompt"
    code = tmp_path / "pdd" / "pay.py"
    test = tmp_path / "tests" / "test_pay.py"
    prompt.parent.mkdir()
    code.parent.mkdir()
    test.parent.mkdir()
    prompt.write_text(
        "<contract_rules>\nR1 - Secret safety\nMUST NOT leak tokens.\n</contract_rules>\n",
        encoding="utf-8",
    )
    code.write_text("API_KEY=abc123\n", encoding="utf-8")
    test.write_text("def test_pay(): assert True\n", encoding="utf-8")

    first = build_compressed_sync_context("generate", prompt, code_path=code, test_paths=[test])
    second = build_compressed_sync_context("generate", prompt, code_path=code, test_paths=[test])

    assert first.used is True
    assert first.compressed_sha256 == second.compressed_sha256
    assert "abc123" not in first.content
    assert "[REDACTED]" in first.content
    safe = metadata(first)
    assert "content" not in safe


def test_compressed_sync_context_soft_omits_missing_optional_sources(tmp_path: Path) -> None:
    prompt = tmp_path / "prompt.prompt"
    prompt.write_text("Create a module.\n", encoding="utf-8")

    package = build_compressed_sync_context(
        "fix",
        prompt,
        example_path=tmp_path / "missing_example.py",
        test_paths=[tmp_path / "missing_test.py"],
    )

    assert package.used is True
    assert package.missing_sources
    assert "missing_example.py" in "\n".join(package.missing_sources)


def test_render_for_prompt_escapes_content_and_omits_raw_metadata(tmp_path: Path) -> None:
    prompt = tmp_path / "prompt.prompt"
    prompt.write_text("<contract_rules>R1 < unsafe & raw</contract_rules>\n", encoding="utf-8")

    package = build_compressed_sync_context("verify", prompt)
    rendered = render_for_prompt(package)

    assert '<compressed_sync_context phase="verify">' in rendered
    assert "&lt;contract_rules&gt;" in rendered
    metadata_text = rendered.split("<metadata>", 1)[1].split("</metadata>", 1)[0]
    assert "content" not in json.loads(metadata_text)


def test_compressed_sync_context_respects_global_budget_with_many_sources(
    tmp_path: Path,
) -> None:
    """Rendered package must stay within budget even with many test sources."""
    prompt = tmp_path / "prompts" / "mod_python.prompt"
    code = tmp_path / "pdd" / "mod.py"
    prompt.parent.mkdir(parents=True)
    code.parent.mkdir()
    prompt.write_text("<contract_rules>R1</contract_rules>\n", encoding="utf-8")
    code.write_text("x = 1\n", encoding="utf-8")

    test_paths = []
    for idx in range(40):
        test_file = tmp_path / "tests" / f"test_mod_{idx}.py"
        test_file.parent.mkdir(parents=True, exist_ok=True)
        test_file.write_text(f"def test_case_{idx}():\n    assert {idx} == {idx}\n", encoding="utf-8")
        test_paths.append(test_file)

    package = build_compressed_sync_context(
        "generate",
        prompt,
        code_path=code,
        test_paths=test_paths,
        budget=DEFAULT_BUDGET,
    )

    assert package.char_count <= DEFAULT_BUDGET
    assert package.source_count == 42
    rendered = render_for_prompt(package)
    assert len(rendered) <= DEFAULT_BUDGET


def test_render_for_prompt_respects_total_budget_with_many_sources(tmp_path: Path) -> None:
    """LLM-facing rendered XML must stay within the configured budget."""
    prompt = tmp_path / "prompt.prompt"
    prompt.write_text("<contract_rules>R1</contract_rules>\n", encoding="utf-8")
    test_paths = []
    for idx in range(40):
        test_file = tmp_path / f"test_{idx}.py"
        test_file.write_text(f"def test_{idx}(): assert {idx} == {idx}\n", encoding="utf-8")
        test_paths.append(test_file)

    package = build_compressed_sync_context(
        "generate",
        prompt,
        test_paths=test_paths,
        budget=DEFAULT_BUDGET,
    )
    rendered = render_for_prompt(package)

    assert rendered
    assert len(rendered) <= DEFAULT_BUDGET


def test_compressed_context_is_active_requires_used_flag() -> None:
    assert compressed_context_is_active({"used": True, "content": "x"}) is True
    assert compressed_context_is_active({"used": False, "content": "x"}) is False
    assert compressed_context_is_active(None) is False


def test_compressed_sync_context_dev_unit_resolves_package_import_path() -> None:
    paths = get_pdd_file_paths("compressed_sync_context", "python", prompts_dir="prompts")

    assert paths["prompt"].as_posix().endswith(
        "prompts/compressed_sync_context_python.prompt"
    )
    assert paths["code"].as_posix().endswith("pdd/compressed_sync_context.py")
    assert paths["test"].as_posix().endswith("tests/test_compressed_sync_context.py")

    test_source = paths["test"].read_text(encoding="utf-8")
    imports = [
        node.module
        for node in ast.walk(ast.parse(test_source))
        if isinstance(node, ast.ImportFrom)
    ]
    assert "pdd.compressed_sync_context" in imports
    assert "compressed_sync_context" not in imports


def test_redact_catches_github_pat() -> None:
    """Regression: _redact must redact GitHub PATs that the old 6-pattern list missed."""
    from pdd.compressed_sync_context import _redact

    pat = "ghp_ABCDEFGHIJKLMNOPQRSTUVWXYZabcdef1234"
    result = _redact(f"Authorization: token {pat}")
    assert "ghp_" not in result, (
        "_redact did not redact the GitHub PAT — compressed context can leak credentials"
    )


def test_redact_catches_aws_access_key() -> None:
    """Regression: _redact must redact AWS access keys that the old 6-pattern list missed."""
    from pdd.compressed_sync_context import _redact

    result = _redact("key=AKIAIOSFODNN7EXAMPLE something else")
    assert "AKIAIOSFODNN7EXAMPLE" not in result, (
        "_redact did not redact the AWS access key"
    )
