"""Regression tests for context-compression env wiring (issue #877)."""

from __future__ import annotations

import os
from pathlib import Path
from unittest.mock import patch

import pytest
import yaml

from pdd.compression_reporting import (
    CompressionFallbackError,
    clear_compression_fallback_events,
    format_compression_summary_lines,
    record_compression_fallback,
)
from pdd.config_resolution import apply_compression_env
from pdd.construct_paths import construct_paths
from pdd.preprocess import preprocess
from pdd.pytest_output import _count_skipped_by_compression, _test_context_compression_active


def test_apply_compression_env_exports_pddrc_defaults(monkeypatch: pytest.MonkeyPatch) -> None:
    """`.pddrc` compression defaults must reach os.environ for preprocess."""
    monkeypatch.delenv("PDD_CONTEXT_COMPRESSION", raising=False)
    monkeypatch.delenv("PDD_COMPRESS_EXAMPLES", raising=False)
    monkeypatch.delenv("PDD_COMPRESSION_FALLBACK", raising=False)

    apply_compression_env(
        {
            "context_compression": "examples",
            "compress_examples": True,
            "compression_fallback": "error",
        }
    )

    assert os.environ["PDD_CONTEXT_COMPRESSION"] == "examples"
    assert os.environ["PDD_COMPRESS_EXAMPLES"] == "1"
    assert os.environ["PDD_COMPRESSION_FALLBACK"] == "error"


def test_construct_paths_applies_pddrc_compression_to_env(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """construct_paths must export .pddrc compression keys without polluting output_locations."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PDD_CONTEXT_COMPRESSION", raising=False)
    monkeypatch.delenv("PDD_COMPRESS_EXAMPLES", raising=False)

    pddrc = tmp_path / ".pddrc"
    pddrc.write_text(
        yaml.safe_dump(
            {
                "version": 1,
                "contexts": {
                    "default": {
                        "defaults": {
                            "context_compression": "examples",
                            "compress_examples": True,
                        }
                    }
                },
            }
        )
    )

    prompt_file = tmp_path / "demo_python.prompt"
    prompt_file.write_text("prompt body")

    mock_output = {"output": str(tmp_path / "out.py")}

    with patch("pdd.construct_paths.generate_output_paths", return_value=mock_output) as mock_gen:
        construct_paths(
            {"prompt_file": str(prompt_file)},
            force=True,
            quiet=True,
            command="generate",
            command_options={},
        )

    mock_gen.assert_called_once()
    assert "context_compression" not in mock_gen.call_args.kwargs["output_locations"]
    assert os.environ.get("PDD_CONTEXT_COMPRESSION") == "examples"
    assert os.environ.get("PDD_COMPRESS_EXAMPLES") == "1"


def test_preprocess_auto_interface_mode_for_examples_dir(tmp_path: Path, monkeypatch: pytest.MonkeyPatch) -> None:
    """PDD_CONTEXT_COMPRESSION=examples shrinks example includes to signatures."""
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "examples")

    examples_dir = tmp_path / "examples"
    examples_dir.mkdir()
    example_py = examples_dir / "widget_example.py"
    example_py.write_text(
        "def run_widget():\n"
        "    return 42\n"
    )

    prompt = f"<include>examples/{example_py.name}</include>"
    result = preprocess(prompt, recursive=False, double_curly_brackets=False, examples_dir="examples")

    assert "def run_widget" in result
    assert "return 42" not in result
    assert "..." in result


def test_apply_compression_env_off_unsets_context_compression(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "examples")
    apply_compression_env({"context_compression": "off"})
    assert "PDD_CONTEXT_COMPRESSION" not in os.environ


def test_preprocess_test_interface_keeps_only_failing_test(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "test")
    monkeypatch.setenv("PDD_FAILING_TESTS", "tests/test_sample.py::test_fails")

    (tmp_path / "tests").mkdir()
    (tmp_path / "tests" / "test_sample.py").write_text(
        "import pytest\n\n"
        "@pytest.fixture\n"
        "def widget():\n"
        "    return 1\n\n"
        "def test_passes():\n"
        "    assert True\n\n"
        "def test_fails(widget):\n"
        "    assert widget == 2\n"
    )

    result = preprocess(
        "<include>tests/test_sample.py</include>",
        recursive=False,
        double_curly_brackets=False,
        tests_dir="tests",
    )
    assert "def test_fails" in result
    assert "def test_passes" not in result


def test_preprocess_contracts_mode_strips_non_rules(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "contracts")
    (tmp_path / "rules.prompt").write_text(
        "Narrative intro.\nR1 - Always validate input.\n- MUST reject invalid tokens.\n"
    )
    result = preprocess("<include>rules.prompt</include>", recursive=False, double_curly_brackets=False)
    assert "R1 - Always validate input." in result
    assert "Narrative intro" not in result


def test_preprocess_compression_fallback_error_raises(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.chdir(tmp_path)
    monkeypatch.setenv("PDD_QUIET", "1")
    monkeypatch.setenv("PDD_COMPRESSION_FALLBACK", "error")
    (tmp_path / "module.py").write_text("def foo():\n    return 1\n")
    with patch("pdd.content_selector.ContentSelector") as mock_cs:
        mock_cs.return_value.select.side_effect = ValueError("function 'missing' not found")
        with pytest.raises(CompressionFallbackError, match="missing"):
            preprocess('<include select="def:missing">module.py</include>', recursive=False, double_curly_brackets=False)


def test_compression_summary_reports_active_modes_and_fallback(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("PDD_CONTEXT_COMPRESSION", "examples")
    clear_compression_fallback_events()
    record_compression_fallback("fallback event")
    assert any("context-compression=examples" in ln for ln in format_compression_summary_lines())


def test_pytest_output_skipped_by_compression_from_deselected(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setenv("PDD_COMPRESS_TEST_CONTEXT", "1")
    assert _test_context_compression_active()
    assert _count_skipped_by_compression("===== 1 passed, 3 deselected in 0.12s =====") == 3
