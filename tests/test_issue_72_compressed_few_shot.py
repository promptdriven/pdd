"""Human-verifiable regression tests for issue #72 compressed few-shot context."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest

from pdd.content_selector import ContentSelector, _COMPRESSED_MAX_CHARS
from pdd.evidence_manifest import write_evidence_manifest
from pdd.preprocess import preprocess


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# SCENARIO A: MAIN BUG FIX — compressed mode shrinks few-shot while keeping logic
def test_compressed_mode_strips_docstrings_keeps_callable_bodies() -> None:
    """AST compression must preserve executable mold (function bodies)."""
    source = '''
"""Module doc."""

def helper(value: int) -> int:
    """Add one."""
    return value + 1
'''
    out = ContentSelector.select(source, [], file_path="example.py", mode="compressed")
    assert '"""Module doc."""' not in out
    assert '"""Add one."""' not in out
    assert "return value + 1" in out
    assert "def helper(value: int) -> int:" in out


# SCENARIO B: EDGE CASE — sibling test patch target stays in compressed module
def test_compressed_module_keeps_patch_target_from_sibling_test(tmp_path: Path) -> None:
    """Patch targets referenced in sibling tests must survive compression."""
    module = tmp_path / "worker.py"
    test_file = tmp_path / "test_worker.py"
    module.write_text(
        '"""Worker module."""\n\n'
        "def fetch_data():\n"
        '    """Fetch."""\n'
        "    return 42\n\n"
        "def unused():\n"
        "    return 0\n",
        encoding="utf-8",
    )
    test_file.write_text(
        "from unittest.mock import patch\n\n"
        "@patch('worker.fetch_data', return_value=1)\n"
        "def test_fetch(mock_fetch):\n"
        "    assert mock_fetch() == 1\n",
        encoding="utf-8",
    )
    compressed = ContentSelector.select(
        module.read_text(encoding="utf-8"),
        [],
        file_path=str(module),
        mode="compressed",
    )
    assert "def fetch_data" in compressed
    assert "return 42" in compressed
    assert '"""Worker module."""' not in compressed


# SCENARIO B: EDGE CASE — 30k token cap falls back to interface mode
def test_preprocess_compressed_fallback_to_interface_when_over_cap(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Oversized compressed includes must fall back to interface signatures."""
    huge = tmp_path / "huge.py"
    body = "".join(
        f'def fn_{i}(x: int) -> int:\n    """doc"""\n    return x + {i}\n'
        for i in range(4000)
    )
    huge.write_text(f'"""big"""\n{body}', encoding="utf-8")
    rel = huge.name
    prompt = f'<include mode="compressed">{rel}</include>'
    monkeypatch.chdir(tmp_path)
    expanded = preprocess(prompt, recursive=False, double_curly_brackets=False)
    assert "..." in expanded
    assert len(expanded) < len(huge.read_text(encoding="utf-8"))


# SCENARIO C: INTEGRATION — evidence manifest records deterministic compression hashes
def test_evidence_manifest_records_compressed_include_metadata(tmp_path: Path) -> None:
    """Compressed includes must record source and post-compression hashes."""
    example = tmp_path / "context" / "fewshot.py"
    prompt = tmp_path / "prompts" / "demo_python.prompt"
    example.parent.mkdir(parents=True)
    prompt.parent.mkdir()
    example.write_text(
        '"""Few-shot example."""\n\n'
        "def mold():\n"
        '    """Behavior."""\n'
        "    return True\n",
        encoding="utf-8",
    )
    prompt.write_text(
        f'<include mode="compressed">context/fewshot.py</include>\n',
        encoding="utf-8",
    )
    manifest_path = write_evidence_manifest(
        command="pdd generate",
        prompt_file=prompt,
        project_root=tmp_path,
    )
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    include = manifest["context"]["includes"][0]
    source_text = example.read_text(encoding="utf-8")
    compressed = ContentSelector.select(
        source_text, [], file_path=str(example), mode="compressed"
    )
    assert include["sha256"] == _sha256(source_text)
    assert include["source_sha256"] == include["sha256"]
    assert include["compressed_sha256"] == _sha256(compressed)
    assert include["estimated_tokens"] == -(-len(compressed) // 4)


# SCENARIO C: INTEGRATION — compress=True defaults includes to compressed mode
def test_preprocess_compress_flag_defaults_to_compressed_mode(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """CLI/pipeline compress=True must apply compressed includes without explicit mode."""
    module = tmp_path / "sample.py"
    module.write_text(
        '"""Doc."""\n\ndef run():\n    return 1\n',
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)
    expanded = preprocess(
        f"<include>{module.name}</include>",
        recursive=False,
        double_curly_brackets=False,
        compress=True,
    )
    assert '"""Doc."""' not in expanded
    assert "return 1" in expanded
