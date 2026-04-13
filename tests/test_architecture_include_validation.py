"""Tests for architecture.json vs prompt <include> cross-validation."""
from __future__ import annotations

import json
from pathlib import Path
from unittest.mock import patch

import pytest
from click.testing import CliRunner

from pdd import cli
from pdd.architecture_include_validation import (
    collect_architecture_include_validation_warnings,
    cross_validate_architecture_with_prompt_includes,
)


def _write_pair(
    root: Path,
    filename: str,
    body: str,
    *,
    subdir: str = "",
) -> None:
    rel = Path(filename)
    base = root / "prompts"
    if subdir:
        base = base / subdir
    base.mkdir(parents=True, exist_ok=True)
    (base / rel.name).write_text(body, encoding="utf-8")


def test_no_mismatch_when_arch_matches_includes(tmp_path: Path) -> None:
    """Aligned architecture dependencies and module <include>s produce no warnings."""
    root = tmp_path / "proj"
    root.mkdir()
    prompts = root / "prompts"
    prompts.mkdir()

    _write_pair(
        root,
        "child_Python.prompt",
        "% Reason\n<include>parent_python.prompt</include>\n",
    )
    _write_pair(root, "parent_Python.prompt", "% Reason\n")

    arch = [
        {"filename": "child_Python.prompt", "dependencies": ["parent_Python.prompt"]},
        {"filename": "parent_Python.prompt", "dependencies": []},
    ]
    (root / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == []


def test_ignores_example_py_includes_for_arch_edges(tmp_path: Path) -> None:
    """Example *.py includes do not count as module edges (no false extra-include warnings)."""
    root = tmp_path / "proj"
    root.mkdir()
    prompts = root / "prompts"
    prompts.mkdir()

    _write_pair(
        root,
        "api_Python.prompt",
        "%\n<include>context/models_example.py</include>\n",
    )
    _write_pair(root, "models_Python.prompt", "% Models\n")

    arch = [
        {"filename": "api_Python.prompt", "dependencies": []},
        {"filename": "models_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == []


def test_warns_when_arch_dep_not_included(tmp_path: Path) -> None:
    """Architecture lists a dependency the prompt does not <include> as a module."""
    root = tmp_path / "proj"
    root.mkdir()
    prompts = root / "prompts"
    prompts.mkdir()

    _write_pair(
        root,
        "api_Python.prompt",
        "% Only doc context\n<include>context/readme.md</include>\n",
    )
    _write_pair(root, "models_Python.prompt", "% Models\n")

    arch = [
        {"filename": "api_Python.prompt", "dependencies": ["models_Python.prompt"]},
        {"filename": "models_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert len(warnings) == 1
    assert "api_Python.prompt" in warnings[0]
    assert "models" in warnings[0].lower() or "models_Python.prompt" in warnings[0]
    assert "include" in warnings[0].lower()


def test_warns_when_include_module_missing_from_arch_deps(tmp_path: Path) -> None:
    """Prompt <include>s another module prompt but architecture dependencies omit it."""
    root = tmp_path / "proj"
    root.mkdir()
    prompts = root / "prompts"
    prompts.mkdir()

    _write_pair(
        root,
        "frontend_Python.prompt",
        "% UI\n<include>shared_python.prompt</include>\n",
    )
    _write_pair(root, "shared_Python.prompt", "% Shared\n")

    arch = [
        {"filename": "frontend_Python.prompt", "dependencies": []},
        {"filename": "shared_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert len(warnings) == 1
    assert "frontend_Python.prompt" in warnings[0]
    assert "shared" in warnings[0].lower()
    assert "architecture" in warnings[0].lower() or "dependencies" in warnings[0].lower()


def test_ignores_non_module_includes(tmp_path: Path) -> None:
    """Context paths and non-module includes do not trigger missing-arch-dep warnings."""
    root = tmp_path / "proj"
    root.mkdir()
    (root / "prompts").mkdir()
    (root / "context").mkdir()
    (root / "context" / "preamble.prompt").write_text("x", encoding="utf-8")

    _write_pair(
        root,
        "solo_Python.prompt",
        "%\n<include>context/preamble.prompt</include>\n",
    )

    arch = [{"filename": "solo_Python.prompt", "dependencies": []}]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == []


def test_skips_entry_when_prompt_file_missing(tmp_path: Path) -> None:
    """Missing prompt on disk yields a single skip warning, not a crash."""
    arch = [
        {"filename": "ghost_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, tmp_path)
    assert len(warnings) == 1
    assert "ghost" in warnings[0].lower()
    assert "not found" in warnings[0].lower() or "missing" in warnings[0].lower()


def test_both_mismatches_report_two_warnings(tmp_path: Path) -> None:
    """Extra arch dep and extra include each produce a warning."""
    root = tmp_path / "proj"
    root.mkdir()
    (root / "prompts").mkdir()

    _write_pair(
        root,
        "a_Python.prompt",
        "%\n<include>c_python.prompt</include>\n",
    )
    _write_pair(root, "b_Python.prompt", "%\n")
    _write_pair(root, "c_Python.prompt", "%\n")

    arch = [
        {"filename": "a_Python.prompt", "dependencies": ["b_Python.prompt"]},
        {"filename": "b_Python.prompt", "dependencies": []},
        {"filename": "c_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert len(warnings) == 2
    kinds = " ".join(warnings).lower()
    assert "b_python" in kinds or "b" in kinds
    assert "c_python" in kinds or "c" in kinds


def test_collect_resolves_prompts_relative_to_arch_parent(tmp_path: Path) -> None:
    """Each architecture.json is validated using its parent as the prompt root."""
    (tmp_path / ".git").mkdir()
    svc = tmp_path / "svc"
    prompts = svc / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "child_Python.prompt").write_text(
        "%\n<include>parent_python.prompt</include>\n", encoding="utf-8"
    )
    (prompts / "parent_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "child_Python.prompt", "dependencies": ["parent_Python.prompt"]},
        {"filename": "parent_Python.prompt", "dependencies": []},
    ]
    (svc / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    warnings = collect_architecture_include_validation_warnings(tmp_path)
    assert warnings == []


def test_collect_skips_examples_tree_when_configured(tmp_path: Path) -> None:
    """Bundled sample trees are skipped unless strict validation is requested."""
    (tmp_path / ".git").mkdir()
    ex = tmp_path / "examples" / "demo"
    prompts = ex / "prompts"
    prompts.mkdir(parents=True)
    (prompts / "a_Python.prompt").write_text(
        "%\n<include>b_python.prompt</include>\n", encoding="utf-8"
    )
    (prompts / "b_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "a_Python.prompt", "dependencies": []}]
    (ex / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    assert collect_architecture_include_validation_warnings(
        tmp_path, skip_bundled_sample_arch=True
    ) == []
    strict = collect_architecture_include_validation_warnings(
        tmp_path, skip_bundled_sample_arch=False
    )
    assert len(strict) == 1


def test_pdd_dependency_tag_satisfies_arch_dep(tmp_path: Path) -> None:
    """<pdd-dependency> alone must satisfy an arch.json dep — no <include> of the .prompt needed.

    Per docs/prompting_guide.md, <pdd-dependency> is the authoritative architectural
    declaration; <include> is purely for LLM context ("does NOT affect architecture").
    The forward check must honor <pdd-dependency> as proof of a declared dep so that
    prompts using the tag aren't flagged as drift.
    """
    root = tmp_path / "proj"
    (root / "prompts").mkdir(parents=True)

    _write_pair(
        root,
        "orchestrator_Python.prompt",
        "<pdd-dependency>helper_python.prompt</pdd-dependency>\n"
        "<include>context/helper_example.py</include>\n"
        "% Body\n",
    )
    _write_pair(root, "helper_Python.prompt", "% Helper\n")

    arch = [
        {
            "filename": "orchestrator_Python.prompt",
            "dependencies": ["helper_Python.prompt"],
        },
        {"filename": "helper_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == [], f"Expected no warnings; got: {warnings}"


def test_pdd_dependency_and_include_mixed(tmp_path: Path) -> None:
    """A prompt may satisfy different arch deps via <pdd-dependency> and <include>."""
    root = tmp_path / "proj"
    (root / "prompts").mkdir(parents=True)

    _write_pair(
        root,
        "orchestrator_Python.prompt",
        "<pdd-dependency>helper_python.prompt</pdd-dependency>\n"
        "% Body\n"
        "<include>other_python.prompt</include>\n",
    )
    _write_pair(root, "helper_Python.prompt", "% Helper\n")
    _write_pair(root, "other_Python.prompt", "% Other\n")

    arch = [
        {
            "filename": "orchestrator_Python.prompt",
            "dependencies": ["helper_Python.prompt", "other_Python.prompt"],
        },
        {"filename": "helper_Python.prompt", "dependencies": []},
        {"filename": "other_Python.prompt", "dependencies": []},
    ]

    warnings = cross_validate_architecture_with_prompt_includes(arch, root)
    assert warnings == [], f"Expected no warnings; got: {warnings}"


@patch("pdd.core.cli.auto_update")
def test_validate_arch_includes_cli_ok(mock_auto_update, tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    runner = CliRunner()
    result = runner.invoke(
        cli.cli,
        ["checkup", "--validate-arch-includes", "--project-root", str(tmp_path)],
    )
    assert result.exit_code == 0
    assert "No architecture" in result.output or "mismatches" in result.output


@patch("pdd.core.cli.auto_update")
def test_validate_arch_includes_cli_fails_on_mismatch(mock_auto_update, tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "a_Python.prompt").write_text(
        "%\n<include>b_python.prompt</include>\n", encoding="utf-8"
    )
    (prompts / "b_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "a_Python.prompt", "dependencies": []}]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    runner = CliRunner()
    result = runner.invoke(
        cli.cli,
        ["checkup", "--validate-arch-includes", "--project-root", str(tmp_path)],
    )
    assert result.exit_code == 1
    assert "mismatch" in result.output.lower()
