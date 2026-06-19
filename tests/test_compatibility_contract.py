"""
Test plan for pdd.compatibility_contract
=========================================

Requirements from spec:
  R1: CompatibilityContract is a pydantic v2 model with fields:
       public_symbols, callable_signatures, patch_targets, source_hash,
       truncated, truncated_counts
  R2: extract_compatibility_contract returns empty contract (empty
       collections, truncated=False) when file is missing or raises SyntaxError
  R3: __all__-authoritative public symbol logic:
       - When __all__ is a static list/tuple of string literals, only names
         in __all__ are considered public
       - Otherwise include all non-underscore-prefixed top-level names
         (functions, classes, constants, import re-exports)
       - Skip dunder names unless listed in __all__
  R4: callable_signatures maps qualified name to ast.unparse()-based signature
       with kind tags: [function], [async_function], [class], [method]
       - Nested class methods use dotted qualified names
       - __init__ is included as a public method
  R5: patch_targets - when test_files provided: scan for patch() strings
       with module-relative underscore-prefixed non-dunder names;
       when test_files omitted: fall back to module-level underscore
       non-dunder functions in py_file
  R6: max_symbols cap applied independently per category (public_symbols,
       callable_signatures keys, patch_targets) after stable alphabetical
       sort; set truncated=True and truncated_counts[cat] = original - max
  R7: to_prompt_block() produces:
       - "% Compatibility Surface" header
       - "% public_symbols: ..." (comma-separated)
       - "% callable_signatures:" with one entry per line (2-space indent)
       - "% patch_targets: ..." (comma-separated)
       - For capped categories: append "# (truncated: N symbols omitted)"

Additional test coverage:
  - source_hash is SHA-256 hex digest of file bytes
  - stable alphabetical sort of all categories
  - patch_targets from multiple test files (union)
  - patch_targets: dunder patterns (e.g. __init__) are excluded
  - empty test_files list (no patch targets from test scan)
  - callable_signatures only for public names (not underscore-prefixed classes/fns)
  - import re-export names included in non-__all__ mode
  - regression: each bug fixed in steps 2-3
"""

import hashlib
import textwrap
from pathlib import Path

import pytest

from pdd.compatibility_contract import (
    CompatibilityContract,
    extract_compatibility_contract,
)


# ---------------------------------------------------------------------------
# R1: CompatibilityContract model
# ---------------------------------------------------------------------------


class TestCompatibilityContractModel:
    def test_default_fields(self):
        c = CompatibilityContract()
        assert c.public_symbols == []
        assert c.callable_signatures == {}
        assert c.patch_targets == []
        assert c.source_hash == ""
        assert c.truncated is False
        assert c.truncated_counts == {}

    def test_field_types(self):
        c = CompatibilityContract(
            public_symbols=["A", "B"],
            callable_signatures={"A": "[class] class A: ..."},
            patch_targets=["_helper"],
            source_hash="abc123",
            truncated=True,
            truncated_counts={"public_symbols": 5},
        )
        assert isinstance(c.public_symbols, list)
        assert isinstance(c.callable_signatures, dict)
        assert isinstance(c.patch_targets, list)
        assert isinstance(c.source_hash, str)
        assert isinstance(c.truncated, bool)
        assert isinstance(c.truncated_counts, dict)

    def test_is_pydantic_model(self):
        from pydantic import BaseModel
        assert issubclass(CompatibilityContract, BaseModel)


# ---------------------------------------------------------------------------
# R7: to_prompt_block()
# ---------------------------------------------------------------------------


class TestToPromptBlock:
    def test_section_header(self):
        c = CompatibilityContract()
        block = c.to_prompt_block()
        assert block.startswith("% Compatibility Surface")

    def test_public_symbols_line(self):
        c = CompatibilityContract(public_symbols=["Alpha", "Beta"])
        block = c.to_prompt_block()
        assert "% public_symbols: Alpha, Beta" in block

    def test_public_symbols_empty(self):
        c = CompatibilityContract()
        block = c.to_prompt_block()
        assert "% public_symbols: " in block

    def test_callable_signatures_line_format(self):
        c = CompatibilityContract(
            callable_signatures={"foo": "[function] def foo() -> None: ..."}
        )
        block = c.to_prompt_block()
        assert "% callable_signatures:" in block
        assert "  [function] def foo() -> None: ..." in block

    def test_callable_signatures_sorted(self):
        c = CompatibilityContract(
            callable_signatures={
                "zoo": "[function] def zoo(): ...",
                "aaa": "[function] def aaa(): ...",
            }
        )
        block = c.to_prompt_block()
        idx_aaa = block.index("aaa")
        idx_zoo = block.index("zoo")
        assert idx_aaa < idx_zoo

    def test_patch_targets_line(self):
        c = CompatibilityContract(patch_targets=["_a", "_b"])
        block = c.to_prompt_block()
        assert "% patch_targets: _a, _b" in block

    def test_no_truncation_annotation(self):
        c = CompatibilityContract(public_symbols=["A"])
        block = c.to_prompt_block()
        assert "truncated" not in block

    def test_truncation_public_symbols(self):
        c = CompatibilityContract(
            public_symbols=["A"],
            truncated=True,
            truncated_counts={"public_symbols": 5},
        )
        block = c.to_prompt_block()
        assert "# (truncated: 5 symbols omitted)" in block

    def test_truncation_callable_signatures(self):
        c = CompatibilityContract(
            callable_signatures={"foo": "[function] def foo(): ..."},
            truncated=True,
            truncated_counts={"callable_signatures": 3},
        )
        block = c.to_prompt_block()
        assert "% callable_signatures: # (truncated: 3 symbols omitted)" in block

    def test_truncation_patch_targets(self):
        c = CompatibilityContract(
            patch_targets=["_a"],
            truncated=True,
            truncated_counts={"patch_targets": 10},
        )
        block = c.to_prompt_block()
        assert "# (truncated: 10 symbols omitted)" in block

    def test_block_structure_order(self):
        c = CompatibilityContract(
            public_symbols=["Foo"],
            callable_signatures={"Foo": "[class] class Foo: ..."},
            patch_targets=["_bar"],
        )
        block = c.to_prompt_block()
        lines = block.split("\n")
        assert lines[0] == "% Compatibility Surface"
        pub_idx = next(i for i, l in enumerate(lines) if "public_symbols" in l)
        sig_idx = next(i for i, l in enumerate(lines) if "callable_signatures" in l)
        patch_idx = next(i for i, l in enumerate(lines) if "patch_targets" in l)
        assert pub_idx < sig_idx < patch_idx


# ---------------------------------------------------------------------------
# R2: Missing / syntax error file
# ---------------------------------------------------------------------------


class TestMissingAndBadFile:
    def test_missing_file_returns_empty_contract(self, tmp_path):
        contract = extract_compatibility_contract(tmp_path / "nonexistent.py")
        assert contract.public_symbols == []
        assert contract.callable_signatures == {}
        assert contract.patch_targets == []
        assert contract.source_hash == ""
        assert contract.truncated is False
        assert contract.truncated_counts == {}

    def test_syntax_error_file_returns_empty_collections(self, tmp_path):
        bad = tmp_path / "bad.py"
        bad.write_text("def broken(\n")
        contract = extract_compatibility_contract(bad)
        assert contract.public_symbols == []
        assert contract.callable_signatures == {}
        assert contract.patch_targets == []
        assert contract.truncated is False


# ---------------------------------------------------------------------------
# R3: __all__-authoritative public symbol logic
# ---------------------------------------------------------------------------


class TestPublicSymbols:
    def test_all_authoritative_includes_only_listed(self, tmp_path):
        src = textwrap.dedent("""
            __all__ = ["Pub", "pub_func"]
            class Pub:
                pass
            class _Priv:
                pass
            def pub_func():
                pass
            def _helper():
                pass
            CONSTANT = 1
        """)
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert set(c.public_symbols) == {"Pub", "pub_func"}
        assert "CONSTANT" not in c.public_symbols
        assert "_helper" not in c.public_symbols

    def test_all_as_tuple(self, tmp_path):
        src = "from __future__ import annotations\n__all__ = ('Alpha', 'Beta')\ndef Alpha(): pass\ndef Beta(): pass\ndef Gamma(): pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert set(c.public_symbols) == {"Alpha", "Beta"}

    def test_no_all_includes_public_names(self, tmp_path):
        src = textwrap.dedent("""
            def public_fn():
                pass
            def _private_fn():
                pass
            class PublicClass:
                pass
            CONSTANT = 42
            _PRIV = 0
        """)
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "public_fn" in c.public_symbols
        assert "PublicClass" in c.public_symbols
        assert "CONSTANT" in c.public_symbols
        assert "_private_fn" not in c.public_symbols
        assert "_PRIV" not in c.public_symbols

    def test_no_all_skips_dunders(self, tmp_path):
        src = "def __version__(): pass\ndef public_fn(): pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "__version__" not in c.public_symbols
        assert "public_fn" in c.public_symbols

    def test_all_can_include_dunder(self, tmp_path):
        src = "__all__ = ['__version__', 'public_fn']\n__version__ = '1.0'\ndef public_fn(): pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "__version__" in c.public_symbols
        assert "public_fn" in c.public_symbols

    def test_import_reexports_included_without_all(self, tmp_path):
        src = "import os\nfrom pathlib import Path\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "os" in c.public_symbols
        assert "Path" in c.public_symbols

    def test_annotated_assignment_included(self, tmp_path):
        src = "TIMEOUT: int = 30\n_priv: str = 'x'\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "TIMEOUT" in c.public_symbols
        assert "_priv" not in c.public_symbols

    def test_public_symbols_sorted(self, tmp_path):
        src = "def zebra(): pass\ndef alpha(): pass\ndef middle(): pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert c.public_symbols == sorted(c.public_symbols)


# ---------------------------------------------------------------------------
# R4: callable_signatures
# ---------------------------------------------------------------------------


class TestCallableSignatures:
    def test_function_kind_tag(self, tmp_path):
        src = "def my_func(x: int, y: str = 'a') -> bool:\n    pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "my_func" in c.callable_signatures
        assert c.callable_signatures["my_func"].startswith("[function]")

    def test_async_function_kind_tag(self, tmp_path):
        src = "async def my_async(url: str) -> bytes:\n    return b''\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "my_async" in c.callable_signatures
        assert c.callable_signatures["my_async"].startswith("[async_function]")

    def test_class_kind_tag(self, tmp_path):
        src = "class MyClass:\n    pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "MyClass" in c.callable_signatures
        assert c.callable_signatures["MyClass"].startswith("[class]")

    def test_method_kind_tag(self, tmp_path):
        src = "class MyClass:\n    def my_method(self) -> None:\n        pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "MyClass.my_method" in c.callable_signatures
        assert c.callable_signatures["MyClass.my_method"].startswith("[method]")

    def test_init_included_as_method(self, tmp_path):
        src = "class MyClass:\n    def __init__(self, x: int) -> None:\n        self.x = x\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "MyClass.__init__" in c.callable_signatures
        assert c.callable_signatures["MyClass.__init__"].startswith("[method]")

    def test_private_method_excluded(self, tmp_path):
        src = "class MyClass:\n    def _secret(self):\n        pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "MyClass._secret" not in c.callable_signatures

    def test_nested_class_dotted_name(self, tmp_path):
        src = textwrap.dedent("""
            class Outer:
                class Inner:
                    def inner_method(self) -> None:
                        pass
        """)
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "Outer.Inner" in c.callable_signatures
        assert "Outer.Inner.inner_method" in c.callable_signatures

    def test_private_class_excluded(self, tmp_path):
        src = "class _Hidden:\n    pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "_Hidden" not in c.callable_signatures

    def test_private_function_excluded(self, tmp_path):
        src = "def _private(): pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert "_private" not in c.callable_signatures

    def test_signature_contains_ast_unparse(self, tmp_path):
        src = "def greet(name: str, count: int = 1) -> str:\n    return name * count\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        sig = c.callable_signatures["greet"]
        assert "name: str" in sig
        # ast.unparse() does not add spaces around default value '='
        assert "count: int=1" in sig
        assert "-> str" in sig


# ---------------------------------------------------------------------------
# R5: patch_targets
# ---------------------------------------------------------------------------


class TestPatchTargets:
    def test_fallback_module_level_underscore_functions(self, tmp_path):
        src = textwrap.dedent("""
            def public_fn():
                pass
            def _helper():
                pass
            def _fetcher():
                pass
            def __dunder__():
                pass
        """)
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f, test_files=None)
        assert "_helper" in c.patch_targets
        assert "_fetcher" in c.patch_targets
        assert "public_fn" not in c.patch_targets
        assert "__dunder__" not in c.patch_targets

    def test_test_files_patch_extraction(self, tmp_path):
        src = "def public_fn(): pass\n"
        py_file = tmp_path / "m.py"
        py_file.write_text(src)
        test_src = textwrap.dedent("""
            from unittest.mock import patch
            def test_a():
                with patch("mymod._private_a") as m:
                    pass
            @patch("mymod._private_b")
            def test_b(m):
                pass
        """)
        test_file = tmp_path / "test_m.py"
        test_file.write_text(test_src)
        c = extract_compatibility_contract(py_file, test_files=[test_file])
        assert "mymod._private_a" in c.patch_targets
        assert "mymod._private_b" in c.patch_targets

    def test_test_files_excludes_dunder_patch_targets(self, tmp_path):
        src = "def public_fn(): pass\n"
        py_file = tmp_path / "m.py"
        py_file.write_text(src)
        test_src = 'with patch("mymod.__init__") as m:\n    pass\n'
        test_file = tmp_path / "test_m.py"
        test_file.write_text(test_src)
        c = extract_compatibility_contract(py_file, test_files=[test_file])
        assert "mymod.__init__" not in c.patch_targets

    def test_test_files_empty_list(self, tmp_path):
        src = "def _helper(): pass\n"
        py_file = tmp_path / "m.py"
        py_file.write_text(src)
        c = extract_compatibility_contract(py_file, test_files=[])
        # Empty list means scan test_files (none), not fallback
        assert c.patch_targets == []

    def test_multiple_test_files_union(self, tmp_path):
        src = "def public_fn(): pass\n"
        py_file = tmp_path / "m.py"
        py_file.write_text(src)
        test_a = tmp_path / "test_a.py"
        test_b = tmp_path / "test_b.py"
        test_a.write_text('with patch("m._alpha") as x: pass\n')
        test_b.write_text('with patch("m._beta") as x: pass\n')
        c = extract_compatibility_contract(py_file, test_files=[test_a, test_b])
        assert "m._alpha" in c.patch_targets
        assert "m._beta" in c.patch_targets

    def test_patch_targets_sorted(self, tmp_path):
        src = "def _zzz(): pass\ndef _aaa(): pass\n"
        py_file = tmp_path / "m.py"
        py_file.write_text(src)
        c = extract_compatibility_contract(py_file)
        assert c.patch_targets == sorted(c.patch_targets)

    def test_fallback_async_underscore_functions(self, tmp_path):
        src = "async def _async_helper(): pass\n"
        py_file = tmp_path / "m.py"
        py_file.write_text(src)
        c = extract_compatibility_contract(py_file, test_files=None)
        assert "_async_helper" in c.patch_targets


# ---------------------------------------------------------------------------
# R6: max_symbols cap and truncation
# ---------------------------------------------------------------------------


class TestMaxSymbolsCap:
    def _make_many_funcs_file(self, tmp_path: Path, count: int) -> Path:
        lines = [f"def func_{i}(): pass" for i in range(count)]
        f = tmp_path / "many.py"
        f.write_text("\n".join(lines) + "\n")
        return f

    def test_no_truncation_within_limit(self, tmp_path):
        f = self._make_many_funcs_file(tmp_path, 3)
        c = extract_compatibility_contract(f, max_symbols=10)
        assert not c.truncated
        assert c.truncated_counts == {}

    def test_public_symbols_capped(self, tmp_path):
        f = self._make_many_funcs_file(tmp_path, 10)
        c = extract_compatibility_contract(f, max_symbols=3)
        assert len(c.public_symbols) == 3

    def test_callable_signatures_capped(self, tmp_path):
        f = self._make_many_funcs_file(tmp_path, 10)
        c = extract_compatibility_contract(f, max_symbols=3)
        assert len(c.callable_signatures) == 3

    def test_truncated_flag_set(self, tmp_path):
        f = self._make_many_funcs_file(tmp_path, 10)
        c = extract_compatibility_contract(f, max_symbols=3)
        assert c.truncated is True

    def test_truncated_counts_public_symbols(self, tmp_path):
        f = self._make_many_funcs_file(tmp_path, 10)
        c = extract_compatibility_contract(f, max_symbols=3)
        assert "public_symbols" in c.truncated_counts
        assert c.truncated_counts["public_symbols"] == 10 - 3

    def test_truncated_counts_callable_signatures(self, tmp_path):
        f = self._make_many_funcs_file(tmp_path, 10)
        c = extract_compatibility_contract(f, max_symbols=3)
        assert "callable_signatures" in c.truncated_counts
        assert c.truncated_counts["callable_signatures"] == 10 - 3

    def test_patch_targets_capped(self, tmp_path):
        lines = [f"def _helper_{i}(): pass" for i in range(10)]
        f = tmp_path / "m.py"
        f.write_text("\n".join(lines) + "\n")
        c = extract_compatibility_contract(f, max_symbols=3)
        assert len(c.patch_targets) == 3
        assert c.truncated_counts["patch_targets"] == 10 - 3

    def test_cap_applied_independently_per_category(self, tmp_path):
        # 5 public functions (will hit callable_signatures cap but not if max=10)
        # Check that only exceeded categories appear in truncated_counts
        lines = [f"def func_{i}(): pass" for i in range(5)]
        f = tmp_path / "m.py"
        f.write_text("\n".join(lines) + "\n")
        c = extract_compatibility_contract(f, max_symbols=5)
        # Exactly 5 functions, cap is 5 → not truncated
        assert not c.truncated
        assert c.truncated_counts == {}

    def test_alphabetical_sort_applied_before_cap(self, tmp_path):
        # Letters a-z (26 > 5 cap), alphabetical sort means first 5 are a-e
        lines = [f"def func_{chr(ord('a')+i)}(): pass" for i in range(26)]
        f = tmp_path / "m.py"
        f.write_text("\n".join(lines) + "\n")
        c = extract_compatibility_contract(f, max_symbols=5)
        # After sort, first 5 should be func_a ... func_e
        assert c.public_symbols[0] == "func_a"
        assert c.callable_signatures and list(c.callable_signatures.keys())[0] == "func_a"


# ---------------------------------------------------------------------------
# Source hash
# ---------------------------------------------------------------------------


class TestSourceHash:
    def test_source_hash_is_sha256(self, tmp_path):
        src = "def foo(): pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        expected = hashlib.sha256(src.encode()).hexdigest()
        c = extract_compatibility_contract(f)
        assert c.source_hash == expected

    def test_source_hash_length(self, tmp_path):
        src = "x = 1\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        assert len(c.source_hash) == 64

    def test_source_hash_empty_for_missing_file(self, tmp_path):
        c = extract_compatibility_contract(tmp_path / "nope.py")
        assert c.source_hash == ""


# ---------------------------------------------------------------------------
# Integration smoke tests
# ---------------------------------------------------------------------------


class TestIntegration:
    def test_full_contract_from_realistic_module(self, tmp_path):
        src = textwrap.dedent("""
            from __future__ import annotations
            from typing import Optional

            __all__ = ["MyClass", "process"]

            class MyClass:
                def __init__(self, name: str) -> None:
                    self.name = name

                def greet(self) -> str:
                    return f"Hello, {self.name}"

                def _private(self) -> None:
                    pass

            async def process(items: list, *, timeout: int = 30) -> dict:
                return {}

            def _internal_helper(x: int) -> int:
                return x * 2
        """)
        f = tmp_path / "realistic.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)

        assert set(c.public_symbols) == {"MyClass", "process"}
        assert "MyClass" in c.callable_signatures
        assert "MyClass.__init__" in c.callable_signatures
        assert "MyClass.greet" in c.callable_signatures
        assert "MyClass._private" not in c.callable_signatures
        assert "process" in c.callable_signatures
        assert c.callable_signatures["process"].startswith("[async_function]")
        assert "_internal_helper" in c.patch_targets  # fallback mode

    def test_prompt_block_from_realistic_module(self, tmp_path):
        src = "class Foo:\n    def bar(self) -> None:\n        pass\n"
        f = tmp_path / "m.py"
        f.write_text(src)
        c = extract_compatibility_contract(f)
        block = c.to_prompt_block()
        assert "% Compatibility Surface" in block
        assert "% public_symbols:" in block
        assert "% callable_signatures:" in block
        assert "% patch_targets:" in block

    def test_return_type_is_compatibility_contract(self, tmp_path):
        f = tmp_path / "m.py"
        f.write_text("x = 1\n")
        result = extract_compatibility_contract(f)
        assert isinstance(result, CompatibilityContract)

    def test_missing_file_returns_compatibility_contract(self, tmp_path):
        result = extract_compatibility_contract(tmp_path / "missing.py")
        assert isinstance(result, CompatibilityContract)
