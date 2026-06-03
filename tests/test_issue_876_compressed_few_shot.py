"""Human-verifiable regression tests for promptdriven/pdd issue #876.

Marketplace few-shot compression: deterministic, contract-preserving, with
fallback when over token budget. Run:

    pytest -vv tests/test_issue_876_compressed_few_shot.py
"""
from __future__ import annotations

import hashlib
import json
import textwrap
from pathlib import Path

import pytest

from pdd.content_selector import (
    ContentSelector,
    _COMPRESSED_MAX_CHARS,
    augment_interface_with_patch_targets,
    discover_sibling_patch_targets,
)
from pdd.evidence_manifest import write_evidence_manifest
from pdd.preprocess import preprocess


def _sha256(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# SCENARIO A: MAIN — compressed few-shot keeps behavioral mold
def test_compressed_mode_strips_docstrings_keeps_callable_bodies() -> None:
    """Compression keeps executable logic for few-shot grounding (#876)."""
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


def test_externally_called_helper_definition_preserved() -> None:
    """Contract-bearing helpers referenced in-module must survive compression."""
    source = """
def helper():
    return 1

def main():
    return helper()
"""
    out = ContentSelector.select(source, [], file_path="app.py", mode="compressed")
    assert "def helper" in out
    assert "return 1" in out
    assert "helper()" in out


def test_compression_output_is_deterministic() -> None:
    """Same source must produce identical compressed bytes (#876)."""
    source = '"""x"""\n\ndef f():\n    return 1\n'
    a = ContentSelector.select(source, [], file_path="m.py", mode="compressed")
    b = ContentSelector.select(source, [], file_path="m.py", mode="compressed")
    assert a == b
    assert _sha256(a) == _sha256(b)


# SCENARIO B: EDGE — patch targets + fallback chain
def test_compressed_module_keeps_patch_target_from_sibling_test(tmp_path: Path) -> None:
    """Sibling test patch targets must remain in compressed module source."""
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
    assert discover_sibling_patch_targets(module) == {"fetch_data"}
    compressed = ContentSelector.select(
        module.read_text(encoding="utf-8"),
        [],
        file_path=str(module),
        mode="compressed",
    )
    assert "def fetch_data" in compressed
    assert "return 42" in compressed


def test_interface_fallback_restores_patch_target_body(tmp_path: Path) -> None:
    """After compressed→interface fallback, patched symbols keep full bodies."""
    module = tmp_path / "worker.py"
    test_file = tmp_path / "test_worker.py"
    filler = "".join(
        f"def fn_{i}(x: int) -> int:\n    return x + {i}\n" for i in range(3500)
    )
    module.write_text(
        "def fetch_data():\n    return 42\n\n" + filler,
        encoding="utf-8",
    )
    test_file.write_text(
        "@patch('worker.fetch_data', return_value=1)\n"
        "def test_fetch():\n    pass\n",
        encoding="utf-8",
    )
    raw = module.read_text(encoding="utf-8")
    iface = ContentSelector.select(raw, [], file_path=str(module), mode="interface")
    assert "return 42" not in iface
    restored = augment_interface_with_patch_targets(
        iface, raw, discover_sibling_patch_targets(module)
    )
    assert "return 42" in restored


def test_preprocess_compressed_fallback_to_interface_when_over_cap(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """Oversized compressed includes use interface then truncated full (#876)."""
    huge = tmp_path / "huge.py"
    body = "".join(
        f'def fn_{i}(x: int) -> int:\n    """doc"""\n    return x + {i}\n'
        for i in range(4000)
    )
    huge.write_text(f'"""big"""\n{body}', encoding="utf-8")
    raw_len = len(huge.read_text(encoding="utf-8"))
    monkeypatch.chdir(tmp_path)
    expanded = preprocess(
        f'<include mode="compressed">{huge.name}</include>',
        recursive=False,
        double_curly_brackets=False,
    )
    assert len(expanded) <= _COMPRESSED_MAX_CHARS
    assert len(expanded) < raw_len


# SCENARIO C: INTEGRATION — manifest hashes + compress flag
def test_evidence_manifest_records_compressed_include_metadata(tmp_path: Path) -> None:
    """Deterministic source/compressed hashes and token estimate in manifest."""
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
        '<include mode="compressed">context/fewshot.py</include>\n',
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


def test_preprocess_compress_flag_defaults_to_compressed_mode(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """compress=True applies compressed includes without explicit mode attribute."""
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


def test_contract_selector_compressed_strips_slice_banners_and_docstrings() -> None:
    """contract: slices must honor mode=compressed (#876 review)."""
    source = textwrap.dedent(
        '''
        """Module doc."""

        def _helper():
            """Hidden helper."""
            return 1

        def run():
            """Public entry."""
            return _helper()
        '''
    )
    out = ContentSelector.select(source, ["contract:run"], file_path="mod.py", mode="compressed")
    assert "# --- API Contract Slice ---" not in out
    assert '"""Module doc."""' not in out
    assert '"""Hidden helper."""' not in out
    assert '"""Public entry."""' not in out
    assert "def run():" in out
    assert "return _helper()" in out


def test_pytest_selector_compressed_strips_docstrings(tmp_path: Path) -> None:
    """pytest: slices must honor mode=compressed (#876 review)."""
    test_file = tmp_path / "test_sample.py"
    test_file.write_text(
        textwrap.dedent(
            '''
            """Test module."""

            def test_one():
                """One."""
                assert 1 == 1

            def test_two():
                assert 2 == 2
            '''
        ),
        encoding="utf-8",
    )
    out = ContentSelector.select(
        test_file.read_text(encoding="utf-8"),
        ["pytest:test_one"],
        file_path=str(test_file),
        mode="compressed",
    )
    assert '"""Test module."""' not in out
    assert '"""One."""' not in out
    assert "def test_one():" in out
    assert "test_two" not in out


def test_preprocess_include_many_compress_strips_python_docstrings(
    monkeypatch: pytest.MonkeyPatch, tmp_path: Path
) -> None:
    """<include-many> with compress=True applies Python compression (#876 review)."""
    module = tmp_path / "sample.py"
    module.write_text(
        '"""Module doc."""\n\ndef run():\n    return 1\n',
        encoding="utf-8",
    )
    monkeypatch.chdir(tmp_path)
    expanded = preprocess(
        f"<include-many>{module.name}</include-many>",
        recursive=False,
        double_curly_brackets=False,
        compress=True,
    )
    assert '"""Module doc."""' not in expanded
    assert "return 1" in expanded
