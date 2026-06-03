"""Wiring tests for --compress through CLI, auto-deps, and sync (#876)."""
from __future__ import annotations

from unittest.mock import MagicMock, patch

import click

from pdd.auto_include import (
    AutoIncludeResult,
    NewInclude,
    _apply_compress_to_include_tags,
    _build_include_directives,
)
from pdd.auto_deps_main import auto_deps_main


def test_build_include_directives_adds_compressed_mode_for_python() -> None:
    """auto_include emits mode=compressed for Python paths when compress=True."""
    result = AutoIncludeResult(
        reasoning="test",
        new_includes=[
            NewInclude(file="context/fewshot.py", module="context", select=None, query=None),
        ],
        existing_include_annotations=[],
    )
    directives = _build_include_directives(result, compress=True)
    assert 'mode="compressed"' in directives
    assert "context/fewshot.py" in directives


def test_apply_compress_to_include_tags_skips_non_python() -> None:
    """Compression mode is only applied to Python include paths."""
    raw = "<include>docs/guide.md</include>\n<include>app.py</include>"
    out = _apply_compress_to_include_tags(raw, compress=True)
    assert 'mode="compressed">docs/guide.md' not in out
    assert 'mode="compressed">app.py' in out


@patch("pdd.auto_deps_main.construct_paths")
@patch("pdd.auto_deps_main.insert_includes")
def test_auto_deps_main_forwards_compress(
    mock_insert_includes: MagicMock,
    mock_construct_paths: MagicMock,
    tmp_path,
) -> None:
    """auto_deps_main passes compress through to insert_includes."""
    output_path = tmp_path / "out.prompt"
    csv_path = tmp_path / "deps.csv"
    mock_construct_paths.return_value = (
        {},
        {"prompt_file": "% test"},
        {"output": str(output_path), "csv": str(csv_path)},
        {},
    )
    mock_insert_includes.return_value = ("% test", "", 0.0, "test-model")

    ctx = click.Context(click.Command("auto-deps"))
    ctx.obj = {
        "force": False,
        "quiet": True,
        "strength": 0.5,
        "temperature": 0.0,
        "time": 0.25,
    }

    auto_deps_main(
        ctx=ctx,
        prompt_file="demo_python.prompt",
        directory_path="examples",
        auto_deps_csv_path=None,
        output=None,
        compress=True,
    )

    assert mock_insert_includes.call_args.kwargs["compress"] is True
