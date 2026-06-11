"""Issue #1558: one semantic callable-contract model across ALL sync gates.

These are gate-level acceptance tests (not just helper unit tests). They drive
both default-comparison sites end to end:

* the public-surface regression gate
  (:func:`pdd.code_generator_main._verify_public_surface_regression`), and
* the ``<pdd-interface>`` / architecture-conformance gate
  (:func:`pdd.code_generator_main._verify_pdd_interface_signatures`, reached via
  :func:`_verify_architecture_conformance`).

The defining scenario: a backward-compatible literal<->same-module-constant
default refactor (``max_chars=25000`` <-> ``_LIMIT = 25000`` then
``max_chars=_LIMIT``) is identical for every caller, so NEITHER gate may report
it as drift. Provably-different and unresolvable defaults must still fail closed,
and missing functions / removed public fields must still fail.
"""

import json

import pytest

from pdd.code_generator_main import (
    ArchitectureConformanceError,
    PublicSurfaceRegressionError,
    _verify_architecture_conformance,
    _verify_pdd_interface_signatures,
    _verify_public_surface_regression,
)

PROMPT = "demo_Python.prompt"
OUT = "pdd/demo.py"


def _iface_prompt(signature: str, name: str = "f") -> str:
    """A minimal prompt carrying a single ``<pdd-interface>`` function decl."""
    spec = {
        "type": "module",
        "module": {"functions": [{"name": name, "signature": signature}]},
    }
    return f"<pdd-interface>{json.dumps(spec)}</pdd-interface>\n% engineer\n"


# ---------------------------------------------------------------------------
# Public-surface regression gate (existing-code -> generated-code).
# Old defaults resolve in the OLD module namespace, new in the NEW one.
# ---------------------------------------------------------------------------
class TestPublicSurfaceSemanticDefaults:
    def test_existing_literal_to_generated_module_constant_passes(self):
        """AC: existing literal default -> generated same-module immutable
        constant default passes public-surface regression."""
        before = "def f(max_chars=25000):\n    return max_chars\n"
        after = (
            "_LIMIT = 25000\n"
            "def f(max_chars=_LIMIT):\n    return max_chars\n"
        )
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", "Refactor default into a constant."
        )

    def test_existing_module_constant_to_generated_literal_passes(self):
        """AC: existing same-module immutable constant default -> generated
        equivalent literal default passes public-surface regression."""
        before = (
            "_LIMIT = 25000\n"
            "def f(max_chars=_LIMIT):\n    return max_chars\n"
        )
        after = "def f(max_chars=25000):\n    return max_chars\n"
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", "Inline the constant."
        )

    def test_constant_to_different_constant_value_still_fails(self):
        """AC: existing constant value and generated DIFFERENT constant value
        still fail. Each side resolves in its OWN module, so 25000 != 5000."""
        before = (
            "_LIMIT = 25000\n"
            "def f(max_chars=_LIMIT):\n    return max_chars\n"
        )
        after = (
            "_LIMIT = 5000\n"
            "def f(max_chars=_LIMIT):\n    return max_chars\n"
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", "Change the limit."
            )
        assert "f" in exc.value.changed_signatures

    def test_literal_to_different_constant_value_still_fails(self):
        before = "def f(max_chars=25000):\n    return max_chars\n"
        after = (
            "_LIMIT = 5000\n"
            "def f(max_chars=_LIMIT):\n    return max_chars\n"
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", "Change the limit."
            )
        assert "f" in exc.value.changed_signatures

    def test_dynamic_default_change_fails_closed(self):
        """AC: calls / dynamic expressions fail closed (UNKNOWN) -> reported."""
        before = "def f(x=helper()):\n    return x\n"
        after = "def f(x=other()):\n    return x\n"
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", "Swap helper."
            )
        assert "f" in exc.value.changed_signatures

    def test_unchanged_dynamic_default_passes(self):
        """The control for the asymmetric cases below: when the default is
        unresolvable in BOTH module versions and its source text is unchanged,
        the expression itself did not change, so it is not a regression."""
        before = "def f(x=helper()):\n    return x\n"
        after = "def f(x=helper()):\n    return x\n"
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", "No default change."
        )

    def test_existing_dynamic_default_to_generated_literal_fails_closed(self):
        """A default whose constant the EXISTING module computes dynamically but
        the GENERATED module pins to a literal is a possible behavior change even
        though the signature text (``_LIMIT``) is identical: exactly one side
        resolves, so the gate must fail closed rather than trust the matching
        text. This matches the gate's own contract that dynamic defaults fail
        closed."""
        before = "_LIMIT = load_limit()\ndef f(max_chars=_LIMIT):\n    return max_chars\n"
        after = "_LIMIT = 5000\ndef f(max_chars=_LIMIT):\n    return max_chars\n"
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", "Pin the limit."
            )
        assert "f" in exc.value.changed_signatures

    def test_existing_imported_default_to_generated_literal_fails_closed(self):
        """Same asymmetry as above with an imported name on the existing side:
        the import is unresolvable, the generated literal resolves, identical
        ``_LIMIT`` text -> fail closed."""
        before = "from cfg import _LIMIT\ndef f(max_chars=_LIMIT):\n    return max_chars\n"
        after = "_LIMIT = 5000\ndef f(max_chars=_LIMIT):\n    return max_chars\n"
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", "Inline the import."
            )
        assert "f" in exc.value.changed_signatures

    def test_existing_literal_default_to_generated_imported_fails_closed(self):
        """The reverse direction: the existing literal resolves but the generated
        module makes the same name an import (unresolvable). Still asymmetric,
        still fail closed."""
        before = "_LIMIT = 5000\ndef f(max_chars=_LIMIT):\n    return max_chars\n"
        after = "from cfg import _LIMIT\ndef f(max_chars=_LIMIT):\n    return max_chars\n"
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", "Import the limit."
            )
        assert "f" in exc.value.changed_signatures

    def test_mutable_module_constant_default_fails_closed(self):
        """A mutable-container module constant can be mutated in place after
        binding, so it stays UNKNOWN: a literal<->mutable-constant default
        change must fail closed rather than be waved through."""
        before = "def f(items=[1, 2]):\n    return items\n"
        after = (
            "_ITEMS = [1, 2]\n"
            "def f(items=_ITEMS):\n    return items\n"
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", "Hoist list default."
            )
        assert "f" in exc.value.changed_signatures

    def test_removed_public_dataclass_field_still_fails(self):
        """AC: removed public fields like ``AgenticTaskResult.usage`` still
        fail. The semantic-default change must not weaken field-removal
        detection (a dropped required constructor field)."""
        before = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class AgenticTaskResult:\n"
            "    name: str\n"
            "    usage: int\n"
        )
        after = (
            "from dataclasses import dataclass\n"
            "@dataclass\n"
            "class AgenticTaskResult:\n"
            "    name: str\n"
        )
        with pytest.raises(PublicSurfaceRegressionError):
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", "Drop usage field."
            )

    def test_literal_to_constant_passes_despite_function_local_shadow(self):
        """The literal -> same-module-constant refactor must still be recognized
        when an unrelated function reuses the constant's name as a local: the
        parameter default reads the module global ``_LIMIT`` (25000), not the
        function-local one, so the contract is unchanged and the gate must not
        flag it."""
        before = "def f(max_chars=25000):\n    return max_chars\n"
        after = (
            "_LIMIT = 25000\n"
            "def f(max_chars=_LIMIT):\n    return max_chars\n"
            "def g():\n    _LIMIT = 1\n    return _LIMIT\n"
        )
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", "Hoist default into a constant."
        )

    def test_literal_to_constant_passes_despite_function_local_walrus(self):
        """A function-local walrus reusing the constant's name binds a local, not
        the module global, so the literal->constant refactor must still pass (it
        previously failed closed on the over-broad whole-tree walrus scan)."""
        before = "def f(max_chars=25000):\n    return max_chars\n"
        after = (
            "_LIMIT = 25000\n"
            "def f(max_chars=_LIMIT):\n    return max_chars\n"
            "def g():\n    return (_LIMIT := 1)\n"
        )
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", "Hoist default; unrelated walrus."
        )


# ---------------------------------------------------------------------------
# <pdd-interface> / architecture-conformance gate (prompt -> generated-code).
# Both sides resolve in the GENERATED module namespace.
# ---------------------------------------------------------------------------
class TestInterfaceSemanticDefaults:
    def test_prompt_literal_to_generated_module_constant_passes(self):
        """AC: prompt literal default -> generated same-module immutable
        constant default passes <pdd-interface> conformance."""
        prompt = _iface_prompt("(max_chars: int = 25000)")
        code = (
            "_LIMIT = 25000\n"
            "def f(max_chars: int = _LIMIT):\n    return max_chars\n"
        )
        _verify_pdd_interface_signatures(code, prompt, PROMPT, OUT, {})

    def test_prompt_literal_to_generated_constant_passes_architecture_gate(
        self, tmp_path
    ):
        """AC: same scenario through the architecture-conformance wrapper, with
        a real architecture.json so the symbol-existence check runs first."""
        arch = [
            {
                "filename": PROMPT,
                "filepath": "pdd/demo.py",
                "interface": {
                    "type": "module",
                    "module": {"functions": [{"name": "f", "signature": "def f(...)"}]},
                },
            }
        ]
        arch_path = tmp_path / "architecture.json"
        arch_path.write_text(json.dumps(arch))
        prompt = _iface_prompt("(max_chars: int = 25000)")
        code = (
            "_LIMIT = 25000\n"
            "def f(max_chars: int = _LIMIT):\n    return max_chars\n"
        )
        _verify_architecture_conformance(
            generated_code=code,
            prompt_name=PROMPT,
            arch_path=str(arch_path),
            language="python",
            verbose=False,
            output_path=OUT,
            prompt_content=prompt,
        )

    def test_prompt_constant_with_different_value_still_drifts(self):
        """AC: a same-module constant resolving to a DIFFERENT value still
        raises drift."""
        prompt = _iface_prompt("(max_chars: int = 25000)")
        code = (
            "_LIMIT = 5000\n"
            "def f(max_chars: int = _LIMIT):\n    return max_chars\n"
        )
        with pytest.raises(ArchitectureConformanceError) as exc:
            _verify_pdd_interface_signatures(code, prompt, PROMPT, OUT, {})
        assert "f.max_chars" in exc.value.missing_symbols

    def test_dynamic_default_fails_closed(self):
        """AC: a dynamic/unresolvable generated default stays UNKNOWN and still
        raises rather than being silently accepted."""
        prompt = _iface_prompt("(max_chars: int = 25000)")
        code = "def f(max_chars: int = compute()):\n    return max_chars\n"
        with pytest.raises(ArchitectureConformanceError) as exc:
            _verify_pdd_interface_signatures(code, prompt, PROMPT, OUT, {})
        assert "f.max_chars" in exc.value.missing_symbols

    def test_dropped_default_still_fails(self):
        """AC: dropped defaults still fail (callers omitting the kwarg break)."""
        prompt = _iface_prompt("(max_chars: int = 25000)")
        code = "def f(max_chars: int):\n    return max_chars\n"
        with pytest.raises(ArchitectureConformanceError) as exc:
            _verify_pdd_interface_signatures(code, prompt, PROMPT, OUT, {})
        assert "f.max_chars" in exc.value.missing_symbols

    def test_missing_declared_function_still_fails(self):
        """AC: missing declared functions like ``extract_step_report`` still
        fail. The semantic-default change must not weaken symbol existence."""
        prompt = _iface_prompt("(report: dict)", name="extract_step_report")
        code = "def unrelated():\n    return None\n"
        with pytest.raises(ArchitectureConformanceError) as exc:
            _verify_pdd_interface_signatures(code, prompt, PROMPT, OUT, {})
        assert "extract_step_report" in exc.value.missing_symbols

    def test_mutable_module_constant_default_fails_closed(self):
        """AC: a mutable-container same-module constant can be mutated in place
        after binding, so it stays UNKNOWN and the gate fails closed rather than
        treating it as equivalent to the declared literal."""
        prompt = _iface_prompt("(items: list = [])")
        code = (
            "_ITEMS = []\n"
            "def f(items: list = _ITEMS):\n    return items\n"
        )
        with pytest.raises(ArchitectureConformanceError) as exc:
            _verify_pdd_interface_signatures(code, prompt, PROMPT, OUT, {})
        assert "f.items" in exc.value.missing_symbols

    def test_imported_name_default_fails_closed(self):
        """AC: a default whose generated source is an imported name cannot be
        resolved statically, so it stays UNKNOWN and fails closed."""
        prompt = _iface_prompt("(max_chars: int = 25000)")
        code = (
            "from config import LIMIT\n"
            "def f(max_chars: int = LIMIT):\n    return max_chars\n"
        )
        with pytest.raises(ArchitectureConformanceError) as exc:
            _verify_pdd_interface_signatures(code, prompt, PROMPT, OUT, {})
        assert "f.max_chars" in exc.value.missing_symbols

    def test_function_local_shadow_does_not_defeat_constant_resolution(self):
        """A function-local variable reusing the constant's name must not push
        the generated default to UNKNOWN: the declared literal and the module
        constant ``_LIMIT`` (25000) still match, so conformance passes."""
        prompt = _iface_prompt("(max_chars: int = 25000)")
        code = (
            "_LIMIT = 25000\n"
            "def f(max_chars: int = _LIMIT):\n    return max_chars\n"
            "def g():\n    _LIMIT = 1\n    return _LIMIT\n"
        )
        _verify_pdd_interface_signatures(code, prompt, PROMPT, OUT, {})
