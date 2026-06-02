"""Regression tests for context-compression env wiring (issue #877)."""

from __future__ import annotations

import os
from pathlib import Path
from unittest.mock import patch

import pytest
import yaml

from pdd.config_resolution import apply_compression_env
from pdd.construct_paths import construct_paths
from pdd.preprocess import preprocess


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
