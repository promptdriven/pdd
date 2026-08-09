"""Wiring tests for --compress through CLI, auto-deps, and sync (#876)."""
from __future__ import annotations

from unittest.mock import MagicMock, patch

import click
import pytest

from pdd.auto_include import (
    AutoIncludeResult,
    NewInclude,
    _apply_compress_to_include_tags,
    _build_include_directives,
    _strip_selectors_from_small_files,
    auto_include,
)
from pdd.auto_deps_main import auto_deps_main
from pdd.insert_includes import insert_includes


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


def test_strip_selectors_from_small_files_preserves_compressed_mode(
    tmp_path, monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Small-file selector stripping must not drop mode=\"compressed\" (#876)."""
    monkeypatch.chdir(tmp_path)
    tiny = tmp_path / "fewshot.py"
    tiny.write_text("def mold():\n    return True\n", encoding="utf-8")
    directives = (
        "<new>\n<context>"
        '<include mode="compressed" select="def:mold">fewshot.py</include>'
        "</context>\n</new>"
    )
    stripped = _strip_selectors_from_small_files(
        directives,
        directory_path=str(tmp_path),
    )
    assert 'mode="compressed">fewshot.py' in stripped
    assert "select=" not in stripped


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


@patch("pdd.insert_includes.llm_invoke")
@patch("pdd.insert_includes.auto_include")
@patch("pdd.insert_includes.preprocess", return_value="processed")
@patch("pdd.insert_includes.load_prompt_template", return_value="template")
def test_insert_includes_forwards_compress_to_auto_include(
    mock_lpt: MagicMock,
    mock_pp: MagicMock,
    mock_auto_include: MagicMock,
    mock_llm: MagicMock,
    tmp_path,
) -> None:
    """insert_includes passes compress through to auto_include (#876 review)."""
    csv_path = tmp_path / "deps.csv"
    mock_auto_include.return_value = ("", "csv_out", 0.0, "model")

    insert_includes(
        input_prompt="my prompt",
        directory_path="context/",
        csv_filename=str(csv_path),
        compress=True,
    )

    assert mock_auto_include.call_args.kwargs["compress"] is True


@patch("pdd.auto_include.llm_invoke")
@patch("pdd.auto_include.summarize_directory")
def test_auto_include_compress_true_emits_compressed_python_tags(
    mock_summarize: MagicMock,
    mock_llm: MagicMock,
    tmp_path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Real auto_include(compress=True) tags discovered Python includes (#876)."""
    monkeypatch.chdir(tmp_path)
    context_dir = tmp_path / "context"
    context_dir.mkdir()
    (context_dir / "fewshot.py").write_text(
        '"""Few-shot example."""\n\ndef mold():\n    return True\n',
        encoding="utf-8",
    )

    mock_summarize.return_value = (
        "full_path,file_summary,key_exports,dependencies,content_hash\n"
        "fewshot.py,Example,\"[]\",\"[]\",abc\n",
        0.001,
        "mock-model",
    )
    mock_llm.return_value = {
        "result": AutoIncludeResult(
            reasoning="Need few-shot mold",
            new_includes=[
                NewInclude(
                    file="fewshot.py",
                    module="context",
                    select=None,
                    query=None,
                ),
            ],
            existing_include_annotations=[],
        ),
        "cost": 0.01,
        "model_name": "mock-model",
    }

    directives, _, cost, model = auto_include(
        input_prompt="Generate a module using few-shot context",
        directory_path=str(context_dir),
        strength=0.7,
        temperature=0.0,
        compress=True,
    )

    assert 'mode="compressed">fewshot.py' in directives
    assert cost == pytest.approx(0.011)
    assert model == "mock-model"
