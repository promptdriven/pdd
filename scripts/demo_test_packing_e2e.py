#!/usr/bin/env python
"""Visible end-to-end demo of ranked test packing (issue #793 / PR #1524).

Run it and *watch* the feature pick and drop tests under a token budget:

    PYTHONPATH=. python scripts/demo_test_packing_e2e.py

It builds a throwaway mini-project (a `calculator` module + several tests) in a
temp dir, then drives two layers on it:

  1. TestContextPacker.pack(...) directly  -- the raw ranking/packing + manifest.
  2. build_compressed_sync_context(...)     -- the integration the real sync/fix
     flows use, comparing context_compression="test" (the PR) vs None (before it).

No network, no LLM calls, no auth -- everything here is deterministic.
"""

from __future__ import annotations

import os
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))

from pdd.compressed_sync_context import build_compressed_sync_context
from pdd.test_context_packer import TestContextPacker


def _write(path: Path, text: str) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def _rule(title: str) -> None:
    print("\n" + "=" * 72)
    print(title)
    print("=" * 72)


def _print_manifest(m) -> None:
    """Pretty-print a TestPackingManifest (dataclass or dict)."""
    get = (lambda k: getattr(m, k)) if not isinstance(m, dict) else (lambda k: m[k])
    selected = get("selected")
    omitted = get("omitted")
    sget = (lambda e, k: e[k]) if selected and isinstance(selected[0], dict) else (lambda e, k: getattr(e, k))
    oget = (lambda e, k: e[k]) if omitted and isinstance(omitted[0], dict) else (lambda e, k: getattr(e, k))

    print(f"  budget={get('budget_tokens')} tokens   used={get('used_tokens')} tokens   "
          f"failing-priority={get('failing_test_priority_count')}")
    print("  SELECTED (in packed order):")
    if not selected:
        print("    (none)")
    for e in selected:
        print(f"    + {Path(sget(e, 'file')).name:<22} score={sget(e, 'score'):<8} "
              f"tokens={sget(e, 'token_count'):<5} {sget(e, 'reason')}")
    print("  OMITTED:")
    if not omitted:
        print("    (none)")
    for e in omitted:
        print(f"    - {Path(oget(e, 'file')).name:<22} {oget(e, 'reason')}")


def build_project(root: Path):
    prompt = _write(root / "calculator_python.prompt",
                    "Write a calculator exposing add(a, b) and subtract(a, b).\n")
    module = _write(root / "calculator.py",
                    "def add(a, b):\n    return a + b\n\n\ndef subtract(a, b):\n    return a - b\n")
    tests = root / "tests"
    tests.mkdir()
    files = {
        "test_add.py": "from calculator import add\n\n\ndef test_add():\n    assert add(1, 2) == 3\n",
        "test_subtract.py": "from calculator import subtract\n\n\ndef test_subtract():\n    assert subtract(5, 2) == 3\n",
        "test_unrelated.py": "def test_upper():\n    assert 'x'.upper() == 'X'\n",
        # near-duplicate of test_add (identical import set) -> should be deduped
        "test_add_dup.py": "from calculator import add\n\n\ndef test_add_again():\n    assert add(2, 2) == 4\n",
    }
    paths = [str(_write(tests / name, body)) for name, body in files.items()]
    return prompt, module, tests, paths


def main() -> None:
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        prompt, module, tests_dir, test_paths = build_project(root)

        _rule("LAYER 1  -  TestContextPacker.pack() directly (ranking + manifest)")
        os.environ["PDD_TEST_TOKEN_BUDGET"] = "2000"
        packer = TestContextPacker(test_root=str(tests_dir))
        result = packer.pack(module_path=str(module), budget_tokens=2000)
        _print_manifest(result.manifest)

        _rule("LAYER 1  -  failing-test priority lane (PDD_FAILING_TESTS)")
        failing = _write(tests_dir / "test_regression.py",
                         "from calculator import add\n\n\ndef test_bug():\n    assert add(2, 2) == 5\n")
        os.environ["PDD_FAILING_TESTS"] = f"{failing}::test_bug"
        result = packer.pack(module_path=str(module), budget_tokens=2000)
        _print_manifest(result.manifest)
        print("  -> test_regression.py is forced first (priority lane), regardless of score.")
        del os.environ["PDD_FAILING_TESTS"]

        _rule("LAYER 1  -  tiny budget squeezes out low-relevance tests")
        result = packer.pack(module_path=str(module), budget_tokens=40)
        _print_manifest(result.manifest)

        _rule('LAYER 2  -  build_compressed_sync_context(context_compression="test")  [PR #1524]')
        pkg_on = build_compressed_sync_context(
            "generate", str(prompt), code_path=str(module),
            test_paths=test_paths, context_compression="test",
        )
        print(f"  test_packing_manifest present: {pkg_on.test_packing_manifest is not None}")
        print(f"  assembled context: {pkg_on.token_estimate} est. tokens, {pkg_on.source_count} sources")
        if pkg_on.test_packing_manifest:
            _print_manifest(pkg_on.test_packing_manifest)

        _rule("LAYER 2  -  context_compression=None  [pre-#793 verbatim behavior]")
        pkg_off = build_compressed_sync_context(
            "generate", str(prompt), code_path=str(module),
            test_paths=test_paths, context_compression=None,
        )
        print(f"  test_packing_manifest present: {pkg_off.test_packing_manifest is not None}  (expected False)")
        print(f"  assembled context: {pkg_off.token_estimate} est. tokens, {pkg_off.source_count} sources")
        print("  -> all tests included verbatim, no ranking, no manifest, no budget on tests.")

        _rule("SUMMARY")
        print(f"  feature ON : {pkg_on.token_estimate:>5} est. tokens, manifest emitted")
        print(f"  feature OFF: {pkg_off.token_estimate:>5} est. tokens, no manifest")
        print("  The PR ranks + caps test context and explains every decision in the manifest.")


if __name__ == "__main__":
    main()
