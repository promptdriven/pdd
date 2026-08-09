from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path

# Ensure the parent directory is in the path so we can import pdd
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.test_context_packer import TestContextPacker


def run_example() -> None:
    """Demonstrate ranked test packing under a token budget."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        module = root / "calculator.py"
        module.write_text(
            "def add(a, b):\n    return a + b\n\n\ndef subtract(a, b):\n    return a - b\n",
            encoding="utf-8",
        )

        tests_dir = root / "tests"
        tests_dir.mkdir()
        # A test that exercises the module directly (high relevance).
        (tests_dir / "test_add.py").write_text(
            "from calculator import add\n\n\ndef test_add():\n    assert add(1, 2) == 3\n",
            encoding="utf-8",
        )
        # An unrelated test (low relevance).
        (tests_dir / "test_unrelated.py").write_text(
            "def test_unrelated():\n    assert 'hello'.upper() == 'HELLO'\n",
            encoding="utf-8",
        )

        packer = TestContextPacker(test_root=str(tests_dir))

        print("=== Ranked packing (no failing tests) ===")
        result = packer.pack(module_path=str(module), budget_tokens=2000)
        print(f"Token count: {result.token_count}")
        for entry in result.manifest.selected:
            print(f"  selected: {Path(entry.file).name} score={entry.score} reason={entry.reason}")
        for entry in result.manifest.omitted:
            print(f"  omitted: {Path(entry.file).name} reason={entry.reason}")

        print("\n=== Failing-test priority lane ===")
        failing = [f"{tests_dir / 'test_add.py'}::test_add"]
        result = packer.pack(module_path=str(module), failing_tests=failing, budget_tokens=2000)
        print(f"Priority count: {result.manifest.failing_test_priority_count}")
        print(f"First selected reason: {result.manifest.selected[0].reason}")

        print("\n=== Zero budget disables test context ===")
        result = packer.pack(module_path=str(module), budget_tokens=0)
        print(f"Selected: {len(result.manifest.selected)} (expected 0)")


if __name__ == "__main__":
    run_example()
    print("\nSTEP_COMPLETE:example_generate")
