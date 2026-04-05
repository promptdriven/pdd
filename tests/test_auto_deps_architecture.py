"""Tests for auto-deps → architecture.json dependency updates."""
from __future__ import annotations

import json
from pathlib import Path

from pdd.auto_deps_architecture import (
    extract_include_paths_from_prompt_text,
    merge_auto_deps_includes_into_architecture,
)


def test_extract_include_paths_supports_attributes() -> None:
    text = '<include path="x">foo/bar.prompt</include>\n<include>plain.prompt</include>'
    paths = extract_include_paths_from_prompt_text(text)
    assert "foo/bar.prompt" in paths
    assert "plain.prompt" in paths


def test_merge_adds_architecture_dependency_for_new_module_include(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "child_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "parent_Python.prompt").write_text("%\n", encoding="utf-8")

    arch = [
        {"filename": "child_Python.prompt", "dependencies": []},
        {"filename": "parent_Python.prompt", "dependencies": []},
    ]
    arch_path = tmp_path / "architecture.json"
    arch_path.write_text(json.dumps(arch), encoding="utf-8")

    old = "%\n"
    new = "%\n<include>parent_python.prompt</include>\n"

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "child_Python.prompt",
        old,
        new,
    )
    assert report["updated"] is True
    assert report["added_dependencies"] == ["parent_Python.prompt"]

    data = json.loads(arch_path.read_text(encoding="utf-8"))
    child = next(e for e in data if e["filename"] == "child_Python.prompt")
    assert child["dependencies"] == ["parent_Python.prompt"]


def test_merge_noop_when_prompt_not_in_architecture(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    p = prompts / "solo_Python.prompt"
    p.write_text("%\n", encoding="utf-8")
    (tmp_path / "architecture.json").write_text("[]", encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        p,
        "%\n",
        '%\n<include>other_python.prompt</include>\n',
    )
    assert report["updated"] is False
    assert report["added_dependencies"] == []


def test_merge_ignores_non_module_includes(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "api_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "api_Python.prompt", "dependencies": []}]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "api_Python.prompt",
        "%\n",
        '%\n<include>context/preamble.prompt</include>\n',
    )
    assert report["updated"] is False


def test_merge_idempotent_when_dependency_already_listed(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "a_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "b_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "a_Python.prompt", "dependencies": ["b_Python.prompt"]},
        {"filename": "b_Python.prompt", "dependencies": []},
    ]
    ap = tmp_path / "architecture.json"
    ap.write_text(json.dumps(arch), encoding="utf-8")

    old = "%\n"
    new = "%\n<include>b_python.prompt</include>\n"
    report = merge_auto_deps_includes_into_architecture(
        tmp_path, prompts / "a_Python.prompt", old, new
    )
    assert report["updated"] is False
    assert report["added_dependencies"] == []


def test_merge_skips_self_referential_module_include(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "mod_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "mod_Python.prompt", "dependencies": []}]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    old = "%\n"
    new = "%\n<include>mod_python.prompt</include>\n"
    report = merge_auto_deps_includes_into_architecture(
        tmp_path, prompts / "mod_Python.prompt", old, new
    )
    assert report["updated"] is False


def test_merge_dry_run_does_not_write(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "child_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "parent_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "child_Python.prompt", "dependencies": []},
        {"filename": "parent_Python.prompt", "dependencies": []},
    ]
    ap = tmp_path / "architecture.json"
    original = json.dumps(arch)
    ap.write_text(original, encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "child_Python.prompt",
        "%\n",
        '%\n<include>parent_python.prompt</include>\n',
        dry_run=True,
    )
    assert report["updated"] is True
    assert ap.read_text(encoding="utf-8") == original
    assert json.loads(ap.read_text(encoding="utf-8"))[0]["dependencies"] == []


def test_merge_resolves_nested_package_architecture(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    svc = tmp_path / "svc"
    pr = svc / "prompts"
    pr.mkdir(parents=True)
    (pr / "a_Python.prompt").write_text("%\n", encoding="utf-8")
    (pr / "b_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "a_Python.prompt", "dependencies": []},
        {"filename": "b_Python.prompt", "dependencies": []},
    ]
    (svc / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        pr / "a_Python.prompt",
        "%\n",
        '%\n<include>b_python.prompt</include>\n',
    )
    assert report["updated"] is True
    data = json.loads((svc / "architecture.json").read_text(encoding="utf-8"))
    a = next(e for e in data if e["filename"] == "a_Python.prompt")
    assert a["dependencies"] == ["b_Python.prompt"]


def test_merge_maps_example_path_include_to_module_arch_entry(tmp_path: Path) -> None:
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    ctx = tmp_path / "context"
    ctx.mkdir()
    (ctx / "models_example.py").write_text("# x", encoding="utf-8")
    (prompts / "api_Python.prompt").write_text("%\n", encoding="utf-8")
    (prompts / "models_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [
        {"filename": "api_Python.prompt", "dependencies": []},
        {"filename": "models_Python.prompt", "dependencies": []},
    ]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "api_Python.prompt",
        "%\n",
        '%\n<include>context/models_example.py</include>\n',
    )
    assert report["updated"] is True
    assert report["added_dependencies"] == ["models_Python.prompt"]
    data = json.loads((tmp_path / "architecture.json").read_text(encoding="utf-8"))
    api = next(e for e in data if e["filename"] == "api_Python.prompt")
    assert api["dependencies"] == ["models_Python.prompt"]


def test_merge_does_not_add_dep_without_architecture_entry_for_peer(tmp_path: Path) -> None:
    """Unknown modules (no row in architecture) are not appended as orphan filenames."""
    (tmp_path / ".git").mkdir()
    prompts = tmp_path / "prompts"
    prompts.mkdir()
    (prompts / "only_Python.prompt").write_text("%\n", encoding="utf-8")
    arch = [{"filename": "only_Python.prompt", "dependencies": []}]
    (tmp_path / "architecture.json").write_text(json.dumps(arch), encoding="utf-8")

    report = merge_auto_deps_includes_into_architecture(
        tmp_path,
        prompts / "only_Python.prompt",
        "%\n",
        '%\n<include>ghost_python.prompt</include>\n',
    )
    assert report["updated"] is False
