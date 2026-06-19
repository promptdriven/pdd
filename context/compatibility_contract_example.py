"""
Example: compatibility_contract — extract public API surface from a Python file.

This module demonstrates how to use `extract_compatibility_contract` and
`CompatibilityContract.to_prompt_block` from `pdd.compatibility_contract`.

Scenarios covered:
  1. File with __all__ declaration (authoritative symbol list)
  2. File without __all__ (all non-underscore-prefixed top-level names)
  3. Missing file (returns empty contract)
  4. File with syntax error (returns empty contract)
  5. max_symbols cap (truncation)
  6. test_files patch target extraction
"""

import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

import tempfile
from pathlib import Path

from pdd.compatibility_contract import (
    CompatibilityContract,
    extract_compatibility_contract,
)

# ---------------------------------------------------------------------------
# Helper to write a temporary .py file and return its Path
# ---------------------------------------------------------------------------

def make_py_file(content: str, tmpdir: Path, name: str = "sample.py") -> Path:
    p = tmpdir / name
    p.write_text(content)
    return p


# ---------------------------------------------------------------------------
# Scenario 1: file with __all__
# ---------------------------------------------------------------------------

WITH_ALL_SOURCE = '''\
from __future__ import annotations

__all__ = ["PublicClass", "public_func"]

class PublicClass:
    def public_method(self) -> None:
        pass
    def _private_method(self) -> None:
        pass

class _PrivateClass:
    pass

def public_func(x: int) -> str:
    """Convert int to string."""
    return str(x)

def _helper(y: int) -> int:
    return y + 1

CONSTANT = 42
'''

# ---------------------------------------------------------------------------
# Scenario 2: file without __all__
# ---------------------------------------------------------------------------

WITHOUT_ALL_SOURCE = '''\
from __future__ import annotations

import os

class Processor:
    """Processes items."""
    def __init__(self, name: str) -> None:
        self.name = name

    def run(self, items: list) -> list:
        return items

    def _internal(self) -> None:
        pass

async def fetch_data(url: str) -> bytes:
    return b""

def _private_helper() -> None:
    pass

TIMEOUT = 30
_INTERNAL_FLAG = False
'''

# ---------------------------------------------------------------------------
# Scenario 3: test file with patch targets
# ---------------------------------------------------------------------------

TEST_SOURCE_WITH_PATCHES = '''\
from unittest.mock import patch

def test_something():
    with patch("mymodule._fetch_resource") as mock_fetch:
        mock_fetch.return_value = b"data"
        assert True

@patch("mymodule._send_request")
def test_other(mock_send):
    mock_send.return_value = 200
    assert True
'''


def run_examples() -> None:
    with tempfile.TemporaryDirectory() as tmpdir_str:
        tmpdir = Path(tmpdir_str)

        # ------------------------------------------------------------------
        # 1. File with __all__
        # ------------------------------------------------------------------
        print("=" * 60)
        print("Scenario 1: File with __all__")
        print("=" * 60)

        py_file = make_py_file(WITH_ALL_SOURCE, tmpdir, "with_all.py")
        contract = extract_compatibility_contract(py_file)

        print(f"public_symbols: {contract.public_symbols}")
        print(f"callable_signatures keys: {list(contract.callable_signatures.keys())}")
        print(f"patch_targets (no test_files): {contract.patch_targets}")
        print(f"truncated: {contract.truncated}")
        print(f"source_hash length: {len(contract.source_hash)}")
        print()
        print("--- to_prompt_block() output ---")
        print(contract.to_prompt_block())
        print()

        # Assertions
        assert "PublicClass" in contract.public_symbols
        assert "public_func" in contract.public_symbols
        assert "_helper" not in contract.public_symbols  # __all__ is authoritative
        assert "CONSTANT" not in contract.public_symbols  # not in __all__
        assert "PublicClass.public_method" in contract.callable_signatures
        assert "PublicClass._private_method" not in contract.callable_signatures
        assert contract.source_hash != ""
        assert not contract.truncated

        # ------------------------------------------------------------------
        # 2. File without __all__
        # ------------------------------------------------------------------
        print("=" * 60)
        print("Scenario 2: File without __all__")
        print("=" * 60)

        py_file2 = make_py_file(WITHOUT_ALL_SOURCE, tmpdir, "without_all.py")
        contract2 = extract_compatibility_contract(py_file2)

        print(f"public_symbols: {contract2.public_symbols}")
        print(f"callable_signatures keys: {list(contract2.callable_signatures.keys())}")
        print(f"patch_targets (no test_files fallback): {contract2.patch_targets}")
        print()

        assert "Processor" in contract2.public_symbols
        assert "fetch_data" in contract2.public_symbols
        assert "TIMEOUT" in contract2.public_symbols
        # import re-exports are included per spec
        assert "os" in contract2.public_symbols
        assert "_INTERNAL_FLAG" not in contract2.public_symbols
        assert "_private_helper" not in contract2.public_symbols
        assert "Processor" in contract2.callable_signatures
        assert "Processor.__init__" in contract2.callable_signatures
        assert "Processor.run" in contract2.callable_signatures
        assert "fetch_data" in contract2.callable_signatures
        # Patch targets (fallback): module-level underscore-prefixed non-dunder functions
        assert "_private_helper" in contract2.patch_targets

        # ------------------------------------------------------------------
        # 3. test_files patch target extraction
        # ------------------------------------------------------------------
        print("=" * 60)
        print("Scenario 3: Patch target extraction from test files")
        print("=" * 60)

        test_file = make_py_file(TEST_SOURCE_WITH_PATCHES, tmpdir, "test_mod.py")
        contract3 = extract_compatibility_contract(py_file2, test_files=[test_file])

        print(f"patch_targets (from test_files): {contract3.patch_targets}")
        print()

        assert any("_fetch_resource" in t for t in contract3.patch_targets)
        assert any("_send_request" in t for t in contract3.patch_targets)

        # ------------------------------------------------------------------
        # 4. Missing file
        # ------------------------------------------------------------------
        print("=" * 60)
        print("Scenario 4: Missing file")
        print("=" * 60)

        missing_contract = extract_compatibility_contract(tmpdir / "does_not_exist.py")
        print(f"public_symbols: {missing_contract.public_symbols}")
        print(f"callable_signatures: {missing_contract.callable_signatures}")
        print(f"truncated: {missing_contract.truncated}")
        print()

        assert missing_contract.public_symbols == []
        assert missing_contract.callable_signatures == {}
        assert missing_contract.patch_targets == []
        assert missing_contract.source_hash == ""
        assert not missing_contract.truncated

        # ------------------------------------------------------------------
        # 5. Syntax error file
        # ------------------------------------------------------------------
        print("=" * 60)
        print("Scenario 5: Syntax error file")
        print("=" * 60)

        bad_py = make_py_file("def broken(\n", tmpdir, "bad.py")
        bad_contract = extract_compatibility_contract(bad_py)
        print(f"public_symbols: {bad_contract.public_symbols}")
        print(f"callable_signatures: {bad_contract.callable_signatures}")
        print()

        assert bad_contract.public_symbols == []
        assert bad_contract.callable_signatures == {}
        assert bad_contract.patch_targets == []

        # ------------------------------------------------------------------
        # 6. max_symbols cap (truncation)
        # ------------------------------------------------------------------
        print("=" * 60)
        print("Scenario 6: max_symbols cap (truncation)")
        print("=" * 60)

        # Generate a file with many public symbols
        many_funcs = "\n".join(
            f"def func_{i}(x: int) -> int:\n    return x + {i}" for i in range(10)
        )
        many_source = f"from __future__ import annotations\n\n{many_funcs}\n"
        many_file = make_py_file(many_source, tmpdir, "many.py")

        # Cap at 3
        capped = extract_compatibility_contract(many_file, max_symbols=3)
        print(f"public_symbols (capped to 3): {capped.public_symbols}")
        print(f"truncated: {capped.truncated}")
        print(f"truncated_counts: {capped.truncated_counts}")
        print()
        print("--- to_prompt_block() with truncation ---")
        print(capped.to_prompt_block())
        print()

        # `from __future__ import annotations` adds 'annotations' as an import re-export,
        # so there are 11 public symbols (10 funcs + 'annotations'), and 10 callable_signatures.
        assert capped.truncated
        assert len(capped.public_symbols) == 3
        assert "public_symbols" in capped.truncated_counts
        # 11 total public symbols (10 funcs + 'annotations') - 3 capped = 8 omitted
        assert capped.truncated_counts["public_symbols"] == 11 - 3
        assert "callable_signatures" in capped.truncated_counts
        # 10 callable signatures - 3 capped = 7 omitted
        assert capped.truncated_counts["callable_signatures"] == 10 - 3
        assert "(truncated:" in capped.to_prompt_block()

    print("=" * 60)
    print("All scenarios passed successfully.")
    print("=" * 60)


if __name__ == "__main__":
    run_examples()
