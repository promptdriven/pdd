"""Tests for architecture vs include-graph sync order consistency warnings."""
from __future__ import annotations

from pathlib import Path

from pdd.sync_graph_order_consistency import warnings_for_arch_vs_include_sync_order


def _write_python_prompts(root: Path, specs: dict[str, str]) -> None:
    p = root / "prompts"
    p.mkdir(parents=True)
    for name, body in specs.items():
        (p / f"{name}_python.prompt").write_text(body, encoding="utf-8")


def test_no_divergence_warnings_when_edges_align(tmp_path: Path) -> None:
    _write_python_prompts(
        tmp_path,
        {
            "child": "%\n<include>parent_python.prompt</include>\n",
            "parent": "%\n",
        },
    )
    w = warnings_for_arch_vs_include_sync_order(
        dep_graph_from_architecture={"child": ["parent"], "parent": []},
        modules_to_sync=["child", "parent"],
        project_root=tmp_path,
    )
    assert not any("differs" in x for x in w)
    assert not any("Only in architecture graph" in x for x in w)
    assert not any("Only in <include>" in x for x in w)


def test_warns_when_architecture_has_extra_edge(tmp_path: Path) -> None:
    _write_python_prompts(
        tmp_path,
        {
            "api": "%\n",
            "models": "%\n",
        },
    )
    w = warnings_for_arch_vs_include_sync_order(
        dep_graph_from_architecture={"api": ["models"], "models": []},
        modules_to_sync=["api", "models"],
        project_root=tmp_path,
    )
    assert any("differs" in x for x in w)
    assert any("Only in architecture graph" in x for x in w)


def test_warns_when_include_graph_has_extra_edge(tmp_path: Path) -> None:
    _write_python_prompts(
        tmp_path,
        {
            "frontend": "%\n<include>shared_python.prompt</include>\n",
            "shared": "%\n",
        },
    )
    w = warnings_for_arch_vs_include_sync_order(
        dep_graph_from_architecture={"frontend": [], "shared": []},
        modules_to_sync=["frontend", "shared"],
        project_root=tmp_path,
    )
    assert any("differs" in x for x in w)
    assert any("Only in <include>" in x for x in w)


def test_skips_when_prompts_dir_missing(tmp_path: Path) -> None:
    w = warnings_for_arch_vs_include_sync_order(
        dep_graph_from_architecture={"a": [], "b": []},
        modules_to_sync=["a", "b"],
        project_root=tmp_path,
    )
    assert any("prompts directory not found" in x for x in w)


def test_notice_when_some_modules_not_alignable_with_prompt_scan(tmp_path: Path) -> None:
    _write_python_prompts(tmp_path, {"solo": "%\n"})
    w = warnings_for_arch_vs_include_sync_order(
        dep_graph_from_architecture={"solo": []},
        modules_to_sync=["solo", "phantom_not_on_disk"],
        project_root=tmp_path,
    )
    assert any("could not be aligned" in x for x in w)


def test_uses_custom_prompts_dir(tmp_path: Path) -> None:
    custom = tmp_path / "my_prompts"
    custom.mkdir()
    (custom / "x_python.prompt").write_text("%\n<include>y_python.prompt</include>\n", encoding="utf-8")
    (custom / "y_python.prompt").write_text("%\n", encoding="utf-8")
    w = warnings_for_arch_vs_include_sync_order(
        dep_graph_from_architecture={"x": [], "y": []},
        modules_to_sync=["x", "y"],
        project_root=tmp_path,
        prompts_dir=custom,
    )
    assert any("Only in <include>" in x for x in w)
