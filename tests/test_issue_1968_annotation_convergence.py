"""Issue #1968: the sync surface-contract repair must converge on annotation-level
drift (``object`` vs ``Any``, a broadened parameter union).

Before this fix the public-surface gate correctly flagged an annotation-level
regression on a declared ``<pdd-interface>`` signature, but the repair loop did
not converge: the retry regenerated the identical drift and failed again. Two
complementary fixes are exercised here.

* Requirement 1 (LLM directive) — the repair directive built for a
  ``signature_changed`` / ``source: pdd-interface`` violation must inject the
  DECLARED signature as a VERBATIM hard constraint ("emit exactly this
  signature ...", plus an explicit anti-substitution rule), not merely describe
  the violation. Both builders are covered: the typed
  :class:`PublicSurfaceRegressionError.repair_directive` (in-process path) and
  ``agentic_sync_runner._parse_public_surface_failure`` (subprocess/cloud path).

* Requirement 2 (deterministic pass) —
  :func:`pdd.code_generator_main._reconcile_declared_annotation_drift` rewrites
  an emitted signature back to the declared text when the ONLY drift from the
  declaration is annotation spelling on a declared symbol, so the gate passes on
  the reconciled code WITHOUT another generation attempt. Non-annotation
  (structural) violations are left untouched so the gate still fires.
"""

import json

import pytest

from pdd.code_generator_main import (
    PublicSurfaceRegressionError,
    _reconcile_declared_annotation_drift,
    _verify_public_surface_regression,
)

PROMPT = "secrets_client_Python.prompt"
OUT = "src/clients/secrets_client.py"


def _iface_prompt(functions, body="% engineer\n"):
    """Build a minimal prompt carrying a ``<pdd-interface>`` module decl."""
    decls = []
    for name, signature in functions:
        entry = {"name": name}
        if signature is not None:
            entry["signature"] = signature
        decls.append(entry)
    spec = {"type": "module", "module": {"functions": decls}}
    return f"<pdd-interface>{json.dumps(spec)}</pdd-interface>\n{body}"


class TestRepairDirectiveVerbatim:
    """Requirement 1: the declared signature rides along as a hard constraint."""

    def test_property_directive_injects_verbatim_constraint(self):
        exc = PublicSurfaceRegressionError(
            prompt_name=PROMPT,
            output_path=OUT,
            removed_symbols=[],
            changed_signatures=["list_secrets"],
            pre_surface_size=5,
            post_surface_size=5,
            signature_details=[
                (
                    "list_secrets",
                    "[function] (name: str) -> list[dict[str, object]]",
                    "[function] (name: str) -> list[dict[str, Any]]",
                    "pdd-interface",
                )
            ],
        )
        directive = exc.repair_directive
        # Existing behavior: the declared signature is named as the stable target.
        assert (
            "Restore `list_secrets` to its declared signature "
            "`[function] (name: str) -> list[dict[str, object]]`" in directive
        )
        # NEW: a verbatim hard constraint, not just a description of the violation.
        assert "VERBATIM" in directive
        assert "Emit exactly `[function] (name: str) -> list[dict[str, object]]`" in directive
        # NEW: explicit anti-substitution rule so the retry stops emitting `Any`.
        assert "do not substitute" in directive.lower()
        assert "never emit `Any` where the declaration says `object`" in directive
        # A declared-param fix must not be advised via a BREAKING-CHANGE marker.
        assert "change signature" not in directive

    def test_subprocess_directive_injects_verbatim_constraint(self):
        from pdd.agentic_sync_runner import _parse_public_surface_failure

        detail = "signature_detail: " + json.dumps(
            {
                "symbol": "list_secrets",
                "expected": "[function] (name: str) -> list[dict[str, object]]",
                "actual": "[function] (name: str) -> list[dict[str, Any]]",
                "source": "pdd-interface",
            }
        )
        stderr = (
            "Public surface regression for secrets_client_Python.prompt:\n"
            "removed: <none>\n"
            "signature_changed: list_secrets\n"
            "output: src/clients/secrets_client.py\n"
            "pre_surface_size: 5\n"
            "post_surface_size: 5\n" + detail + "\n"
        )
        parsed = _parse_public_surface_failure("", stderr)
        assert parsed is not None
        directive, _signature = parsed
        # Existing per-symbol line preserved (the cloud parser and tests key on it).
        assert (
            "Restore `list_secrets` to its declared signature "
            "`[function] (name: str) -> list[dict[str, object]]`" in directive
        )
        # NEW verbatim hard-constraint framing on the subprocess path too.
        assert "VERBATIM" in directive
        assert "Emit exactly `[function] (name: str) -> list[dict[str, object]]`" in directive
        assert "do not substitute" in directive.lower()


class TestDeterministicReconcile:
    """Requirement 2: annotation-only drift is rewritten to the declared text."""

    def test_object_vs_any_return_annotation_converges(self):
        existing = (
            "def list_secrets(name: str) -> list[dict[str, object]]:\n"
            "    return []\n"
        )
        generated = (
            "from typing import Any\n"
            "def list_secrets(name: str) -> list[dict[str, Any]]:\n"
            "    return []\n"
        )
        prompt = _iface_prompt(
            [("list_secrets", "(name: str) -> list[dict[str, object]]")]
        )
        # Baseline: the gate flags the annotation drift.
        with pytest.raises(PublicSurfaceRegressionError):
            _verify_public_surface_regression(
                existing, generated, PROMPT, OUT, "python", prompt
            )
        # Reconcile rewrites the emitted annotation back to the declared spelling.
        reconciled = _reconcile_declared_annotation_drift(
            existing, generated, PROMPT, OUT, "python", prompt
        )
        assert reconciled is not None
        assert "list[dict[str, object]]" in reconciled
        assert "list[dict[str, Any]]" not in reconciled
        # Deterministic convergence: the gate now passes on the reconciled code.
        _verify_public_surface_regression(
            existing, reconciled, PROMPT, OUT, "python", prompt
        )

    def test_broadened_param_union_converges(self):
        existing = (
            "def load(req: dict[str, object] | None = None) -> None:\n"
            "    return None\n"
        )
        generated = (
            "from typing import Any\n"
            "def load(req: dict[str, Any] | list | None = None) -> None:\n"
            "    return None\n"
        )
        prompt = _iface_prompt(
            [("load", "(req: dict[str, object] | None = None) -> None")]
        )
        with pytest.raises(PublicSurfaceRegressionError):
            _verify_public_surface_regression(
                existing, generated, PROMPT, OUT, "python", prompt
            )
        reconciled = _reconcile_declared_annotation_drift(
            existing, generated, PROMPT, OUT, "python", prompt
        )
        assert reconciled is not None
        def_line = next(
            line for line in reconciled.splitlines() if line.startswith("def load")
        )
        assert "dict[str, object] | None" in def_line
        assert "Any" not in def_line
        assert "list" not in def_line
        _verify_public_surface_regression(
            existing, reconciled, PROMPT, OUT, "python", prompt
        )

    def test_structural_added_param_is_not_auto_fixed(self):
        # An added required param is a real regression, not annotation spelling —
        # the reconciler must leave it for the gate/repair loop.
        existing = "def f(a):\n    return a\n"
        generated = "def f(a, b):\n    return a\n"
        prompt = _iface_prompt([("f", "(a)")])
        reconciled = _reconcile_declared_annotation_drift(
            existing, generated, PROMPT, OUT, "python", prompt
        )
        assert reconciled is None
        with pytest.raises(PublicSurfaceRegressionError):
            _verify_public_surface_regression(
                existing, generated, PROMPT, OUT, "python", prompt
            )

    def test_removed_symbol_is_not_touched(self):
        existing = "def f(a):\n    return a\ndef g(a):\n    return a\n"
        generated = "def f(a):\n    return a\n"
        prompt = _iface_prompt([("f", "(a)"), ("g", "(a)")])
        reconciled = _reconcile_declared_annotation_drift(
            existing, generated, PROMPT, OUT, "python", prompt
        )
        assert reconciled is None

    def test_compatible_annotation_alias_is_left_alone(self):
        # `Dict[str, int]` and `dict[str, int]` are compatible — the gate never
        # flags them, so the reconciler must not churn the emitted code.
        existing = "def h(x: dict[str, int]) -> None:\n    return None\n"
        generated = (
            "from typing import Dict\n"
            "def h(x: Dict[str, int]) -> None:\n    return None\n"
        )
        prompt = _iface_prompt([("h", "(x: dict[str, int]) -> None")])
        reconciled = _reconcile_declared_annotation_drift(
            existing, generated, PROMPT, OUT, "python", prompt
        )
        assert reconciled is None

    def test_method_annotation_drift_converges(self):
        existing = (
            "class C:\n"
            "    def m(self, name: str) -> dict[str, object]:\n"
            "        return {}\n"
        )
        generated = (
            "from typing import Any\n"
            "class C:\n"
            "    def m(self, name: str) -> dict[str, Any]:\n"
            "        return {}\n"
        )
        prompt = _iface_prompt([("C.m", "(self, name: str) -> dict[str, object]")])
        reconciled = _reconcile_declared_annotation_drift(
            existing, generated, PROMPT, OUT, "python", prompt
        )
        assert reconciled is not None
        assert "dict[str, object]" in reconciled
        assert "dict[str, Any]" not in reconciled
        _verify_public_surface_regression(
            existing, reconciled, PROMPT, OUT, "python", prompt
        )

    def test_no_declaration_is_a_noop(self):
        existing = "def f(a: int) -> object:\n    return a\n"
        generated = "def f(a: int) -> object:\n    return a\n"
        reconciled = _reconcile_declared_annotation_drift(
            existing, generated, PROMPT, OUT, "python", "Just prose, no interface."
        )
        assert reconciled is None
