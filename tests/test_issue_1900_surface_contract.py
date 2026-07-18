"""Issue #1900: the prompt-declared ``<pdd-interface>`` is the surface contract.

The public-surface regression gate
(:func:`pdd.code_generator_main._verify_public_surface_regression`) used to
compare the OLD generated code against the NEW generated code for EVERY public
symbol. That dead-ends the ``pdd change -> pdd sync`` loop whenever a legitimate
change adds a symbol AND regeneration also drifts an unrelated *declared* public
function's signature (live case pdd_cloud#2971: ``list_secret_metadata``): the
gate hard-fails with a repair directive whose target is "compatible with the
very code being regenerated", i.e. no stable target.

The fix makes the gate declaration-aware, per-symbol:

* DECLARED symbols (named in the prompt's ``<pdd-interface>``) are validated
  against the prompt declaration — a stable target — not against the old code.
* UNDECLARED symbols keep today's old-code baseline (+ ``BREAKING-CHANGE``
  opt-out), so backward-compat protection for helpers/re-exports is unchanged.

These are gate-level acceptance tests: they call
``_verify_public_surface_regression(before, after, prompt_name, out, "python",
prompt_content)`` directly and assert on ``PublicSurfaceRegressionError``'s
``.removed_symbols`` / ``.changed_signatures`` / ``str(exc)`` / repair directive,
plus one test that the ``signature_detail:`` lines propagate through
``pdd.agentic_sync_runner``'s subprocess parser.
"""

import json
from pathlib import Path

import pytest

from pdd.code_generator_main import (
    PromptInterfaceContractError,
    PublicSurfaceRegressionError,
    _verify_declared_interface_exact,
    _verify_public_surface_regression,
)

PROMPT = "demo_Python.prompt"
OUT = "pdd/demo.py"


def _iface_prompt(functions, body="% engineer\n"):
    """Build a minimal prompt carrying a ``<pdd-interface>`` module decl.

    ``functions`` is an iterable of ``(name, signature)`` pairs. A ``signature``
    of ``None`` is emitted as a description-only declaration (no ``signature``
    key) so the presence-only path can be exercised.
    """
    decls = []
    for name, signature in functions:
        entry = {"name": name}
        if signature is not None:
            entry["signature"] = signature
        decls.append(entry)
    spec = {"type": "module", "module": {"functions": decls}}
    return f"<pdd-interface>{json.dumps(spec)}</pdd-interface>\n{body}"


def _detail_line(symbol, expected, actual, source="pdd-interface"):
    """Build a ``signature_detail:`` line in the JSON wire format (round-8 #2)."""
    return "signature_detail: " + json.dumps(
        {"symbol": symbol, "expected": expected, "actual": actual, "source": source}
    )


class TestIssue1900SurfaceContract:
    def test_full_tracked_module_contract_corpus_manifest(self):
        """Audit every direct Python prompt/code contract, not selected examples."""
        prompts = Path("pdd/prompts")
        candidates = []
        contracts = []
        prose_only = []
        for prompt_path in sorted(prompts.glob("*_python.prompt")):
            code_path = Path("pdd") / f"{prompt_path.name.removesuffix('_python.prompt')}.py"
            text = prompt_path.read_text(encoding="utf-8")
            if not code_path.exists() or "<pdd-interface" not in text:
                continue
            candidates.append(prompt_path.name)
            if "\n<pdd-interface" not in text:
                prose_only.append(prompt_path.name)
                continue
            contracts.append((prompt_path, code_path, text))
        assert len(candidates) == 110
        assert prose_only == ["architecture_include_validation_python.prompt"]
        assert len(contracts) == 109
        for prompt_path, code_path, text in contracts:
            _verify_declared_interface_exact(
                code_path.read_text(encoding="utf-8"), text, prompt_path.name,
                str(code_path), "python",
            )

    def test_returns_can_supply_missing_signature_annotation_but_conflicts_fail(self):
        """``returns`` is authoritative when a legacy signature omits ``->``."""
        prompt = _iface_prompt([("f", "(x: int)")]).replace(
            '"signature": "(x: int)"', '"signature": "(x: int)", "returns": "str"'
        )
        _verify_public_surface_regression(
            "def f(x: int) -> str:\n    return str(x)\n",
            "def f(x: int) -> str:\n    return str(x)\n", PROMPT, OUT, "python", prompt,
        )
        conflicting = _iface_prompt([("f", "(x: int) -> str")]).replace(
            '"signature": "(x: int) -> str"',
            '"signature": "(x: int) -> str", "returns": "int"',
        )
        with pytest.raises(PromptInterfaceContractError, match="conflicts"):
            _verify_public_surface_regression(
                "def f(x: int) -> str:\n    return str(x)\n",
                "def f(x: int) -> str:\n    return str(x)\n", PROMPT, OUT, "python", conflicting,
            )

    def test_prose_marker_is_not_a_contract_but_unterminated_tag_fails_closed(self):
        """Literal documentation is distinct from a malformed metadata block."""
        prose = "% Explain the <pdd-interface> contract in this prose.\n"
        _verify_public_surface_regression("def f():\n    pass\n", "def f():\n    pass\n", PROMPT, OUT, "python", prose)
        malformed = "<pdd-interface>\n{\"type\": \"module\"}\n"
        with pytest.raises(PromptInterfaceContractError, match="unterminated"):
            _verify_public_surface_regression("def f():\n    pass\n", "def f():\n    pass\n", PROMPT, OUT, "python", malformed)

    def test_unknown_interface_root_field_fails_closed(self):
        """The contract root has the same closed-schema treatment as members."""
        prompt = '<pdd-interface>{"type":"module","mystery":true,"module":{"functions":[{"name":"f","signature":"()"}]}}</pdd-interface>'
        with pytest.raises(PromptInterfaceContractError, match="interface root has unsupported"):
            _verify_public_surface_regression("def f():\n    pass\n", "def f():\n    pass\n", PROMPT, OUT, "python", prompt)

    def test_large_callable_body_uses_compact_actionable_signature_evidence(self):
        """A mismatch record remains below structured transport bounds."""
        prompt = _iface_prompt([("f", "(value: int) -> str")])
        before = "def f(value: int) -> str:\n    return str(value)\n"
        after = "def f(value: int) -> int:\n" + "    payload = 'x' * 80\n" * 600 + "    return value\n"
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(before, after, PROMPT, OUT, "python", prompt)
        detail = next(detail for detail in exc.value.signature_details if detail[0] == "f")
        assert "f(value: int) -> int" in detail[2]
        assert len(detail[2].encode("utf-8")) < 1024

    @pytest.mark.parametrize(
        ("prompt_name", "code_path"),
        [
            ("resolved_sync_unit_python.prompt", "pdd/resolved_sync_unit.py"),
            ("checkup_prompt_main_python.prompt", "pdd/checkup_prompt_main.py"),
            ("git_porcelain_python.prompt", "pdd/git_porcelain.py"),
            ("cli_status_python.prompt", "pdd/cli_status.py"),
        ],
    )
    def test_real_synchronized_prompt_code_pairs_pass_exact_gate(self, prompt_name, code_path):
        """Known synchronized repository units cover receiver/export boundaries."""
        _verify_declared_interface_exact(
            Path(code_path).read_text(encoding="utf-8"),
            (Path("prompts") / prompt_name).read_text(encoding="utf-8"),
            prompt_name,
            code_path,
            "python",
        )

    def test_logger_assignment_is_not_an_implicit_export(self):
        """Ordinary module state is not an undeclared public callable export."""
        prompt = _iface_prompt([("f", "()")])
        code = "logger = object()\ndef f():\n    return 1\n"
        _verify_public_surface_regression(code, code, PROMPT, OUT, "python", prompt)

    def test_documented_class_constant_and_method_fields_are_enforced(self):
        """Kinds, bindings, values and conflicting/unknown shapes fail closed."""
        spec = {
            "type": "module",
            "module": {
                "constants": [{"name": "VERSION", "type": "str", "value": "v1"}],
                "classes": [{"name": "Record", "kind": "dataclass", "methods": [
                    {"name": "build", "signature": "(self, x)", "binding": "instance"},
                ]}],
                "functions": [{"name": "f", "signature": "() -> str", "returns": "str"}],
            },
        }
        prompt = f"<pdd-interface>{json.dumps(spec)}</pdd-interface>\n% engineer\n"
        bad = (
            "VERSION = 'v2'\n"
            "class Record:\n"
            "    @staticmethod\n"
            "    def build(self, x):\n"
            "        return x\n"
            "def f() -> str:\n"
            "    return 'ok'\n"
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(bad, bad, PROMPT, OUT, "python", prompt)
        assert {"VERSION", "Record"}.issubset(exc.value.changed_signatures)

        conflicting = _iface_prompt([("f", "() -> str")]).replace(
            '"signature": "() -> str"',
            '"signature": "() -> str", "returns": "int"',
        )
        unknown = _iface_prompt([("f", "()")]).replace(
            '"signature": "()"', '"signature": "()", "mystery": true'
        )
        for invalid in (conflicting, unknown):
            with pytest.raises(PromptInterfaceContractError):
                _verify_public_surface_regression(
                    "def f():\n    return 1\n", "def f():\n    return 1\n",
                    PROMPT, OUT, "python", invalid,
                )

    def test_documented_enum_alias_and_model_fields_are_enforced(self):
        """Repository schema variants are exact contracts, not ignored metadata."""
        spec = {
            "type": "module",
            "module": {
                "enums": [{"name": "Mode", "values": ["READY"]}],
                "typeAliases": [{"name": "ModeName", "definition": "Literal['ready']"}],
                "models": [{"name": "Report", "fields": [{"name": "mode", "type": "str"}]}],
            },
        }
        prompt = f"<pdd-interface>{json.dumps(spec)}</pdd-interface>\n% engineer\n"
        valid = (
            "from enum import Enum\nfrom typing import Literal\n"
            "class Mode(Enum):\n    READY = 'ready'\n"
            "ModeName = Literal['ready']\n"
            "class Report:\n    mode: str\n"
        )
        _verify_public_surface_regression(valid, valid, PROMPT, OUT, "python", prompt)
        invalid = valid.replace("READY = 'ready'", "WAITING = 'waiting'")
        with pytest.raises(PublicSurfaceRegressionError):
            _verify_public_surface_regression(invalid, invalid, PROMPT, OUT, "python", prompt)

    def test_exact_contract_rejects_optional_annotation(self):
        """A new optional parameter still violates the declared signature."""
        prompt = _iface_prompt([("f", "(x: int) -> str")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                "def f(x: int) -> str:\n    return str(x)\n",
                "def f(x, y=None):\n    return str(x)\ndef g():\n    return 1\n",
                PROMPT, OUT, "python", prompt,
            )
        assert "f" in exc.value.changed_signatures

    def test_delta_rejects_new_undeclared_callable_and_explicit_all_constant(self):
        """Legacy exports may remain, but new exports and ``__all__`` entries may not."""
        prompt = _iface_prompt([("f", "() -> int")])
        before = "def f() -> int:\n    return 1\ndef legacy():\n    return 2\n"
        after = before + "def extra():\n    return 3\n__all__ = ['f', 'EXTRA']\nEXTRA = 1\n"
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(before, after, PROMPT, OUT, "python", prompt)
        assert {"extra", "EXTRA"}.issubset(exc.value.changed_signatures)

    def test_exact_contract_handles_decorated_multiline_and_nested_methods(self):
        """AST comparison handles formatting while preserving exact contracts."""
        spec = {
            "type": "module",
            "module": {
                "classes": [{
                    "name": "Outer",
                    "methods": [{"name": "run", "signature": "(self, /, item: int = 1, *, verbose: bool = False) -> str"}],
                }],
            },
        }
        prompt = f"<pdd-interface>{json.dumps(spec)}</pdd-interface>\n% engineer\n"
        code = (
            "class Outer:\n"
            "    @staticmethod\n"
            "    def ignored():\n"
            "        return None\n"
            "    def run(\n"
            "        self, /, item: int = 1, *, verbose: bool = False\n"
            "    ) -> str:\n"
            "        return str(item)\n"
        )
        _verify_public_surface_regression(code, code, PROMPT, OUT, "python", prompt)

    def test_malformed_duplicate_and_partial_declarations_fail_closed(self):
        """Marker presence never silently demotes malformed data to legacy."""
        malformed = "<pdd-interface>{not json}</pdd-interface>\n% engineer\n"
        duplicate = _iface_prompt([("f", "()"), ("f", "()")])
        partial = _iface_prompt([("f", "not a signature")])
        for prompt in (malformed, duplicate, partial):
            with pytest.raises(PromptInterfaceContractError):
                _verify_public_surface_regression(
                    "def f():\n    return 1\n", "def f():\n    return 1\n",
                    PROMPT, OUT, "python", prompt,
                )

    def test_2971_shape_flags_declared_drift_not_added_symbol(self):
        """The pdd_cloud#2971 shape: a legit change ADDS
        ``get_secret_with_enabled_fallback`` while regeneration DRIFTS the
        unrelated declared ``list_secret_metadata`` (adds a required param).

        The declared drift must be flagged against the DECLARED signature (a
        stable target); the correctly-added declared symbol must NOT be flagged;
        a stable declared symbol must NOT be flagged."""
        before = (
            "def list_secret_metadata(project_id, prefix=''):\n"
            "    return []\n"
            "def get_secret(project_id, name):\n"
            "    return name\n"
        )
        after = (
            "def list_secret_metadata(project_id, prefix='', *, region):\n"
            "    return []\n"
            "def get_secret(project_id, name):\n"
            "    return name\n"
            "def get_secret_with_enabled_fallback(project_id, name):\n"
            "    return name\n"
        )
        prompt = _iface_prompt(
            [
                ("list_secret_metadata", "(project_id, prefix='')"),
                ("get_secret", "(project_id, name)"),
                ("get_secret_with_enabled_fallback", "(project_id, name)"),
            ]
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "list_secret_metadata" in exc.value.changed_signatures
        assert "get_secret_with_enabled_fallback" not in exc.value.changed_signatures
        assert "get_secret" not in exc.value.changed_signatures
        assert "get_secret_with_enabled_fallback" not in exc.value.removed_symbols
        # The directive/message must name the DECLARED expected signature, the
        # stable target the old code-vs-code comparison never had.
        message = str(exc.value) + "\n" + exc.value.repair_directive
        assert "(project_id, prefix='')" in message

    def test_declaration_authorizes_incompatible_change(self):
        """A declaration is a permit: dropping a required param that the
        declaration also drops must pass, even though old-vs-new alone would
        flag the removed required ``b``."""
        before = "def f(a, b):\n    return a\n"
        after = "def f(a):\n    return a\n"
        prompt = _iface_prompt([("f", "(a)")])
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", prompt
        )

    def test_additive_only_declared_symbol_passes(self):
        """A newly declared symbol added in ``after`` matching its declared
        signature, with no other drift, must pass with no error."""
        before = "def f(a):\n    return a\n"
        after = (
            "def f(a):\n    return a\n"
            "def g(a, b):\n    return b\n"
        )
        prompt = _iface_prompt([("f", "(a)"), ("g", "(a, b)")])
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", prompt
        )

    def test_no_declaration_falls_back_to_old_code(self):
        """The same drift as the #2971 case but with NO ``<pdd-interface>`` must
        still raise against the old code (the fallback baseline is preserved)."""
        before = (
            "def list_secret_metadata(project_id, prefix=''):\n"
            "    return []\n"
        )
        after = (
            "def list_secret_metadata(project_id, prefix='', *, region):\n"
            "    return []\n"
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", "Just prose, no interface."
            )
        assert "list_secret_metadata" in exc.value.changed_signatures

    def test_declared_symbol_missing_from_generated_is_removed(self):
        """A declared symbol absent from generated code is a violation, listed in
        ``removed_symbols`` — regardless of whether it was in ``before`` (the
        declaration is authoritative for presence)."""
        before = "def f(a):\n    return a\n"
        after = "def f(a):\n    return a\n"
        # ``g`` is declared but never generated (never in before or after).
        prompt = _iface_prompt([("f", "(a)"), ("g", "(a)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "g" in exc.value.removed_symbols

    def test_declaration_authoritative_over_breaking_change(self):
        """A ``BREAKING-CHANGE: remove`` marker does NOT excuse a symbol that is
        still declared in ``<pdd-interface>``: the declaration wins."""
        before = "def f(a):\n    return a\ndef g(a):\n    return a\n"
        after = "def f(a):\n    return a\n"
        prompt = _iface_prompt(
            [("f", "(a)"), ("g", "(a)")],
            body="% engineer\nBREAKING-CHANGE: remove g\n",
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "g" in exc.value.removed_symbols

    def test_undeclared_symbol_still_protected(self):
        """Per-symbol hybrid: an UNDECLARED public helper dropped by
        regeneration must still raise (old-code protection intact), even though
        another symbol IS declared."""
        before = (
            "def f(a):\n    return a\n"
            "def helper():\n    return 1\n"
        )
        after = "def f(a):\n    return a\n"
        prompt = _iface_prompt([("f", "(a)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "helper" in exc.value.removed_symbols

    def test_output_carries_full_expected_and_actual_signatures(self):
        """Criterion 4: the error output carries the FULL declared-expected AND
        the actual generated signature text (no truncation)."""
        before = "def f(a, b='x'):\n    return a\n"
        after = "def f(a, b='x', *, c):\n    return a\n"
        prompt = _iface_prompt([("f", "(a, b='x')")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        text = str(exc.value) + "\n" + exc.value.repair_directive
        assert "(a, b='x')" in text  # declared expected
        assert "*, c" in text  # actual generated drift

    def test_presence_only_declared_signature_requires_the_symbol(self):
        """Repository presence-only declarations are valid but not optional."""
        prompt = _iface_prompt([("f", None)])
        _verify_public_surface_regression(
            "def f(a):\n    return a\n", "def f(a):\n    return a\n",
            PROMPT, OUT, "python", prompt,
        )
        with pytest.raises(PublicSurfaceRegressionError):
            _verify_public_surface_regression(
                "def f(a):\n    return a\n", "def other(a):\n    return a\n",
                PROMPT, OUT, "python", prompt,
            )

    def test_default_resolution_uses_generated_namespace(self):
        """Issue #1558: for the declared-vs-generated comparison BOTH sides
        resolve in the GENERATED module namespace. A declared default written as
        a bare constant name that the generated module binds must resolve to its
        literal and NOT be flagged (it would fail closed if the declared side
        were resolved against the OLD/empty namespace)."""
        before = "def f(max_chars=999):\n    return max_chars\n"
        after = (
            "_LIMIT = 25000\n"
            "def f(max_chars=_LIMIT):\n    return max_chars\n"
        )
        prompt = _iface_prompt([("f", "(max_chars=_LIMIT)")])
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", prompt
        )

    def test_cli_and_command_names_are_not_surface_symbols(self):
        """Codex finding 1: ``type: cli`` / ``type: command`` interfaces declare
        COMMAND strings (``sync-architecture``, ``pdd extracts prune`` — hyphens
        and spaces, not valid Python identifiers), NOT module symbols. They must
        never drive ``removed:`` diffs; only ``type: module`` declares Python
        symbols the surface gate can own. CLI/command signature conformance stays
        with the conformance gate."""
        before = "def run():\n    return 1\n"
        after = "def run():\n    return 1\n"
        cli_spec = {
            "type": "cli",
            "cli": {"commands": [{"name": "sync-architecture", "signature": "(--flag)"}]},
        }
        cli_prompt = (
            f"<pdd-interface>{json.dumps(cli_spec)}</pdd-interface>\n% engineer\n"
        )
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", cli_prompt
        )
        command_spec = {
            "type": "command",
            "command": {"name": "pdd extracts prune", "signature": "(target)"},
        }
        command_prompt = (
            f"<pdd-interface>{json.dumps(command_spec)}</pdd-interface>\n% engineer\n"
        )
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", command_prompt
        )

    def test_dotted_init_requires_exact_constructor_signature(self):
        """Codex finding 2: a constructor's ABI is keyed on the CLASS symbol
        (``Foo``), never ``Foo.__init__``. A real ``type: module`` prompt may
        declare ``Foo.__init__``; its presence must be satisfied by the class
        symbol and its signature left to the conformance gate — so valid code
        must NOT raise. The class going missing is still a violation."""
        prompt = _iface_prompt([("Foo.__init__", "(self, value)")])
        before = (
            "class Foo:\n"
            "    def __init__(self, value):\n"
            "        self.value = value\n"
        )
        # An optional constructor parameter changes the declared contract too.
        after = (
            "class Foo:\n"
            "    def __init__(self, value, extra=None):\n"
            "        self.value = value\n"
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "Foo.__init__" in exc.value.changed_signatures
        # The class itself absent -> still a violation naming the class.
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before,
                "def other():\n    return 1\n",
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "Foo.__init__" in exc.value.removed_symbols

    def test_declared_async_or_kind_drift_uses_old_code_baseline(self):
        """Codex round-2 finding 1a: the ``<pdd-interface>`` cannot express
        ``async`` or a function/class binding kind, so those un-declarable
        structural facets are anchored to the PRIOR generation for a declared
        symbol. An ``async``->sync (and sync->``async``) drift on a declared
        function must therefore still raise, even though the declaration's
        parameter list is unchanged."""
        prompt = _iface_prompt([("f", "(x)")])
        # async -> sync.
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                "async def f(x):\n    return x\n",
                "def f(x):\n    return x\n",
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "f" in exc.value.changed_signatures
        # sync -> async.
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                "def f(x):\n    return x\n",
                "async def f(x):\n    return x\n",
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "f" in exc.value.changed_signatures

    def test_declared_async_regenerated_async_requires_exact_shape(self):
        """The declaration expresses async-ness and every default exactly."""
        prompt = _iface_prompt([("f", "async def f(x)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                "async def f(x):\n    return x\n",
                "async def f(x, y=None):\n    return x\n",
                PROMPT, OUT, "python", prompt,
            )
        assert "f" in exc.value.changed_signatures

    def test_breaking_change_opts_out_declared_kind_change(self):
        """A rare INTENDED async/kind change on a declared symbol still has an
        escape hatch: ``BREAKING-CHANGE: change signature f`` opts the declared
        symbol out of the declared-signature check (mirroring the undeclared
        path), because the declaration cannot express the change."""
        prompt = _iface_prompt(
            [("f", "(x)")],
            body="% engineer\nBREAKING-CHANGE: change signature f\n",
        )
        _verify_public_surface_regression(
            "async def f(x):\n    return x\n",
            "def f(x):\n    return x\n",
            PROMPT,
            OUT,
            "python",
            prompt,
        )

    def test_declared_dotted_method_receiver_stripped(self):
        """Codex round-5: declared dotted methods are first-class declared-contract
        citizens, validated against the DECLARED signature with the leading
        ``self``/``cls`` receiver stripped to match the snapshot. So an UNCHANGED
        method (declared with ``(self, x)`` OR ``def method(self, x)``) must NOT
        raise (receiver-strip correctness), while a method whose params drift
        incompatibly from the declaration MUST raise."""
        code = (
            "class Foo:\n"
            "    def method(self, x):\n"
            "        return x\n"
        )
        for sig in ("(self, x)", "def method(self, x)"):
            prompt = _iface_prompt([("Foo.method", sig)])
            _verify_public_surface_regression(
                code, code, PROMPT, OUT, "python", prompt
            )
        # Incompatible drift from the declared method signature -> raises.
        prompt = _iface_prompt([("Foo.method", "(self, x)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                code,
                "class Foo:\n    def method(self, x, y):\n        return x\n",
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "Foo.method" in exc.value.changed_signatures

    def test_declared_dotted_method_dropped_still_raises(self):
        """Presence of a declared dotted method is still enforced: dropping
        ``Foo.method`` from the generated code raises it as removed."""
        before = (
            "class Foo:\n"
            "    def method(self, x):\n"
            "        return x\n"
        )
        after = "class Foo:\n    pass\n"
        prompt = _iface_prompt([("Foo.method", "(self, x)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "Foo.method" in exc.value.removed_symbols

    def test_breaking_change_does_not_bypass_declared_params(self):
        """Codex FM2: ``BREAKING-CHANGE: change signature`` relaxes ONLY the
        un-declarable binding-kind/async, NOT the declared param/return contract.
        An added-required param that violates the declared signature must STILL be
        flagged even with the opt-out (the declaration is the source of truth for
        params)."""
        prompt = _iface_prompt(
            [("f", "(a)")],
            body="% engineer\nBREAKING-CHANGE: change signature f\n",
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                "def f(a):\n    return a\n",
                "def f(a, b):\n    return a\n",
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "f" in exc.value.changed_signatures

    def test_presence_only_declared_method_added_required_param_raises(self):
        """Codex F1: a presence-only DECLARED dotted method must still fall back
        to the OLD-CODE baseline for its signature (not be skipped from every
        check). Adding a required parameter to ``Foo.method`` breaks callers and
        must raise."""
        prompt = _iface_prompt([("Foo.method", "(self, x)")])
        before = "class Foo:\n    def method(self, x):\n        return x\n"
        after = "class Foo:\n    def method(self, x, required):\n        return x\n"
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "Foo.method" in exc.value.changed_signatures

    def test_presence_only_declared_method_binding_kind_flip_raises(self):
        """Codex F2: a ``@staticmethod`` -> instance binding-kind flip on a
        declared method must be caught via the old-code baseline (receiver-
        stripped snapshot entries on both sides, so no self false positive)."""
        prompt = _iface_prompt([("Factory.build", "(path)")])
        before = (
            "class Factory:\n"
            "    @staticmethod\n"
            "    def build(path):\n"
            "        return path\n"
        )
        after = (
            "class Factory:\n"
            "    def build(self, path):\n"
            "        return path\n"
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "Factory.build" in exc.value.changed_signatures

    def test_invalid_callable_declaration_fails_closed(self):
        """A non-callable function signature cannot silently become legacy."""
        prompt = _iface_prompt([("Service", "class Service")])
        before = (
            "class Service:\n"
            "    def __init__(self, config):\n"
            "        self.config = config\n"
        )
        after = (
            "class Service:\n"
            "    def __init__(self, config, region):\n"
            "        self.config = config\n"
        )
        with pytest.raises(PromptInterfaceContractError, match="signature must be"):
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )

    def test_breaking_change_on_declared_method_relaxes_only_kind(self):
        """Codex round-5: now that declared methods are validated against the
        declaration, ``BREAKING-CHANGE: change signature <method>`` must relax ONLY
        the un-declarable binding-kind/async — a binding-kind flip opted out passes,
        but an added-required PARAM that violates the declaration STILL raises
        (consistent with FM2; the declaration is authoritative for params)."""
        # (a) binding-kind flip remains a contract breach; directives cannot
        # weaken an authoritative declaration.
        flip_prompt = _iface_prompt(
            [("Factory.build", "(path)")],
            body="% engineer\nBREAKING-CHANGE: change signature Factory.build\n",
        )
        with pytest.raises(PublicSurfaceRegressionError):
            _verify_public_surface_regression(
                "class Factory:\n    @staticmethod\n    def build(path):\n        return path\n",
                "class Factory:\n    def build(self, path):\n        return path\n",
                PROMPT, OUT, "python", flip_prompt,
            )
        # (b) added-required param still raises despite the opt-out.
        param_prompt = _iface_prompt(
            [("Foo.method", "(self, x)")],
            body="% engineer\nBREAKING-CHANGE: change signature Foo.method\n",
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                "class Foo:\n    def method(self, x):\n        return x\n",
                "class Foo:\n    def method(self, x, required):\n        return x\n",
                PROMPT,
                OUT,
                "python",
                param_prompt,
            )
        assert "Foo.method" in exc.value.changed_signatures

    def test_new_declared_method_added_required_param_raises(self):
        """Codex round-5: a NEWLY-added declared method (no old-code baseline) is
        still validated against its DECLARED signature, so generating it with an
        extra required parameter beyond the declaration raises."""
        before = "def existing():\n    return 1\n"
        after = (
            "def existing():\n    return 1\n"
            "class Foo:\n    def method(self, x, required):\n        return x\n"
        )
        prompt = _iface_prompt([("Foo.method", "(self, x)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "Foo.method" in exc.value.changed_signatures

    def test_new_declared_constructor_added_required_param_raises(self):
        """Codex round-5: a NEWLY-added declared constructor (``Class.__init__``,
        keyed on the class ``[class]`` entry) is validated against its DECLARED
        signature — an extra required ctor param beyond the declaration raises."""
        before = "def existing():\n    return 1\n"
        after = (
            "def existing():\n    return 1\n"
            "class Service:\n"
            "    def __init__(self, config, region):\n"
            "        self.config = config\n"
        )
        prompt = _iface_prompt([("Service.__init__", "(self, config)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "Service.__init__" in exc.value.changed_signatures

    def test_declared_method_change_authorized_by_declaration(self):
        """Codex round-5 F3: the declaration is the permit for METHOD changes too.
        A declared method whose signature was edited (dropping a param) and whose
        regeneration follows the new declaration must PASS — the declared name is
        excluded from the old-code baseline, so the dropped param is not flagged."""
        before = "class Foo:\n    def method(self, a, b):\n        return a\n"
        after = "class Foo:\n    def method(self, a):\n        return a\n"
        prompt = _iface_prompt([("Foo.method", "(self, a)")])
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", prompt
        )

    def test_declared_underscore_symbol_unchanged_no_false_positive(self):
        """Codex round-7 finding 1: a prompt may declare ``_``-prefixed helpers in
        its ``<pdd-interface>`` (real: ``_extract_step_report``). The declaration is
        authoritative (like ``__all__``), so a declared underscore symbol that
        EXISTS must NOT be reported as removed on unchanged code, even though the
        public-surface snapshot normally filters underscore names out."""
        code = (
            "def _extract_step_report(x):\n    return x\n"
            "def pub():\n    return 1\n"
        )
        prompt = _iface_prompt([
            ("_extract_step_report", "(x)"), ("pub", "()"),
        ])
        _verify_public_surface_regression(
            code, code, PROMPT, OUT, "python", prompt
        )

    def test_declared_underscore_symbol_removed_raises(self):
        """A genuinely removed declared underscore symbol is still a violation."""
        before = (
            "def _helper(x):\n    return x\n"
            "def pub():\n    return 1\n"
        )
        after = "def pub():\n    return 1\n"
        prompt = _iface_prompt([("_helper", "(x)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "_helper" in exc.value.removed_symbols

    def test_declared_underscore_symbol_signature_drift_raises(self):
        """A declared underscore symbol's signature is now validated too: an
        added required param beyond the declaration raises."""
        before = "def _helper(x):\n    return x\n"
        after = "def _helper(x, y):\n    return x\n"
        prompt = _iface_prompt([("_helper", "(x)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "_helper" in exc.value.changed_signatures

    def test_declared_callable_regenerated_as_assignment_raises(self):
        """Codex round-7 finding 2: a declared callable regenerated as a
        non-callable (``def f()`` -> ``f = 1``) is a break. The declared path can't
        decide (the actual isn't a callable contract), so the symbol falls back to
        the old-code baseline, which catches the ``[function]`` -> ``[assignment]``
        kind flip."""
        before = "def f():\n    return 1\n"
        after = "f = 1\n"
        prompt = _iface_prompt([("f", "()")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "f" in exc.value.changed_signatures

    def test_declared_callable_regenerated_as_import_raises(self):
        """Same as above but the callable becomes a re-exported import
        (``[function]`` -> ``[import]``)."""
        before = "def f():\n    return 1\n"
        after = "from pkg import f as f\n"
        prompt = _iface_prompt([("f", "()")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "f" in exc.value.removed_symbols

    def test_callable_assignment_is_not_a_declared_function(self):
        """A callable assignment cannot satisfy a declared def contract."""
        code = "f = lambda: x\n"
        prompt = _iface_prompt([("f", "()")])
        with pytest.raises(PublicSurfaceRegressionError):
            _verify_public_surface_regression(code, code, PROMPT, OUT, "python", prompt)

    def test_callable_to_noncallable_raises_even_with_breaking_change(self):
        """Codex round-8 finding 1: ``BREAKING-CHANGE: change signature`` authorizes
        a PARAMETER change, not de-callable-ing a declared callable (that would be
        ``BREAKING-CHANGE: remove``). A declared callable regenerated as a
        non-callable must raise even under the opt-out (which would otherwise make
        the old-code fallback skip the symbol)."""
        prompt = _iface_prompt(
            [("f", "()")],
            body="% engineer\nBREAKING-CHANGE: change signature f\n",
        )
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                "def f():\n    return 1\n",
                "f = 1\n",
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "f" in exc.value.changed_signatures

    def test_breaking_change_does_not_accept_callable_assignment(self):
        """Compatibility markers cannot weaken the exact callable requirement."""
        code = "f = lambda: x\n"
        prompt = _iface_prompt(
            [("f", "()")],
            body="% engineer\nBREAKING-CHANGE: change signature f\n",
        )
        with pytest.raises(PublicSurfaceRegressionError):
            _verify_public_surface_regression(code, code, PROMPT, OUT, "python", prompt)

    def test_declared_underscore_class_ctor_drift_raises(self):
        """Codex round-8 finding 3: a declared UNDERSCORE class constructor is a
        first-class declared contract. Its ``[class]`` constructor-ABI entry must be
        captured (via the patch-target path) so an added required ctor param
        raises."""
        before = (
            "class _Service:\n"
            "    def __init__(self, config):\n"
            "        self.config = config\n"
        )
        after = (
            "class _Service:\n"
            "    def __init__(self, config, region):\n"
            "        self.config = config\n"
        )
        prompt = _iface_prompt([("_Service.__init__", "(self, config)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "_Service.__init__" in exc.value.changed_signatures

    def test_declared_underscore_class_ctor_unchanged_passes(self):
        """A declared underscore class constructor that is unchanged must NOT
        raise (receiver-stripped ctor ABI matches on both sides)."""
        code = (
            "class _Service:\n"
            "    def __init__(self, config):\n"
            "        self.config = config\n"
        )
        prompt = _iface_prompt([("_Service.__init__", "(self, config)")])
        _verify_public_surface_regression(
            code, code, PROMPT, OUT, "python", prompt
        )

    def test_declared_underscore_method_drift_raises(self):
        """A declared underscore method's signature is validated too: an added
        required param beyond the declaration raises."""
        before = "class _Cls:\n    def _m(self, x):\n        return x\n"
        after = "class _Cls:\n    def _m(self, x, y):\n        return x\n"
        prompt = _iface_prompt([("_Cls._m", "(self, x)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "_Cls._m" in exc.value.changed_signatures

    @staticmethod
    def _nested_ctor_module(outer, inner, extra=""):
        return (
            f"class {outer}:\n"
            f"    class {inner}:\n"
            f"        def __init__(self, config{extra}):\n"
            f"            self.config = config\n"
        )

    def test_declared_nested_ctor_underscore_outer_drift_raises(self):
        """Codex round-9 case A: a declared NESTED constructor whose class path has
        an underscore OUTER class (``_Outer.Inner.__init__``) must raise a signature
        drift (``changed`` + a ``pdd-interface`` detail) on an added ctor param,
        exactly like the public control — not pass silently."""
        prompt = _iface_prompt([("_Outer.Inner.__init__", "(self, config)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                self._nested_ctor_module("_Outer", "Inner"),
                self._nested_ctor_module("_Outer", "Inner", ", region"),
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "_Outer.Inner.__init__" in exc.value.changed_signatures

    def test_declared_nested_ctor_underscore_inner_drift_raises(self):
        """Codex round-9 case B: underscore INNER class (``Outer._Inner.__init__``)
        drift must raise as a ``changed`` signature with a detail — NOT be
        mischaracterized as a bare ``removed`` of the nested class."""
        prompt = _iface_prompt([("Outer._Inner.__init__", "(self, config)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                self._nested_ctor_module("Outer", "_Inner"),
                self._nested_ctor_module("Outer", "_Inner", ", region"),
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "Outer._Inner.__init__" in exc.value.changed_signatures
        assert "Outer._Inner" not in exc.value.removed_symbols

    def test_declared_nested_ctor_underscore_unchanged_passes(self):
        """An unchanged declared nested constructor (underscore outer OR inner)
        must NOT raise (captured and validated, no phantom removal)."""
        for outer, inner in [("_Outer", "Inner"), ("Outer", "_Inner")]:
            code = self._nested_ctor_module(outer, inner)
            prompt = _iface_prompt([(f"{outer}.{inner}.__init__", "(self, config)")])
            _verify_public_surface_regression(
                code, code, PROMPT, OUT, "python", prompt
            )

    def test_declared_nested_ctor_public_control_raises(self):
        """Codex round-9 control C (must stay working): an all-public declared
        nested constructor drift raises ``changed=['Outer.Inner.__init__']``."""
        prompt = _iface_prompt([("Outer.Inner.__init__", "(self, config)")])
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                self._nested_ctor_module("Outer", "Inner"),
                self._nested_ctor_module("Outer", "Inner", ", region"),
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "Outer.Inner.__init__" in exc.value.changed_signatures


class TestIssue1900AgenticPropagation:
    def test_signature_detail_lines_reach_agentic_directive(self):
        """The subprocess/agentic path rebuilds the repair directive from stdout,
        so the new ``signature_detail:`` lines must be parsed and carried into
        the rebuilt directive (criterion 4 on the agentic path)."""
        from pdd.agentic_sync_runner import _parse_public_surface_failure

        stderr = (
            "Public surface regression for demo_Python.prompt:\n"
            "removed: <none>\n"
            "signature_changed: list_secret_metadata\n"
            "output: pdd/demo.py\n"
            "pre_surface_size: 2\n"
            "post_surface_size: 3\n"
            + _detail_line(
                "list_secret_metadata",
                "[function] (project_id, prefix='')",
                "[function] (project_id, prefix='', *, region)",
            )
            + "\n"
        )
        parsed = _parse_public_surface_failure("", stderr)
        assert parsed is not None
        directive, signature = parsed
        # The declared expected signature (the stable target) must ride along in
        # the rebuilt directive.
        assert "(project_id, prefix='')" in directive
        assert "list_secret_metadata" in directive
        # Existing signature tuple contract is unchanged (removed + changed).
        assert signature == ("signature_changed:list_secret_metadata",)

    def test_signature_detail_union_types_survive_parsing(self):
        """A ``signature_detail:`` line whose expected AND actual entries contain
        PEP-604 ` | ` union types must round-trip through the JSON parser with the
        FULL signatures intact."""
        from pdd.agentic_sync_runner import _parse_public_surface_failure

        expected_sig = "[function] (x: int | str) -> bool | None"
        actual_sig = "[function] (x: int | str, y: int) -> bool | None"
        stderr = (
            "Public surface regression for demo_Python.prompt:\n"
            "removed: <none>\n"
            "signature_changed: f\n"
            "output: pdd/demo.py\n"
            "pre_surface_size: 1\n"
            "post_surface_size: 1\n"
            + _detail_line("f", expected_sig, actual_sig) + "\n"
        )
        parsed = _parse_public_surface_failure("", stderr)
        assert parsed is not None
        directive, _signature = parsed
        assert expected_sig in directive
        assert actual_sig in directive

    def test_malformed_signature_detail_line_is_skipped_not_crash(self):
        """A malformed ``signature_detail:`` line (invalid JSON) must be SKIPPED,
        never raise. A well-formed JSON line in the same payload must still
        parse."""
        from pdd.agentic_sync_runner import _parse_public_surface_failure

        stderr = (
            "Public surface regression for demo_Python.prompt:\n"
            "removed: <none>\n"
            "signature_changed: good, bad\n"
            "output: pdd/demo.py\n"
            "pre_surface_size: 2\n"
            "post_surface_size: 2\n"
            # Well-formed JSON.
            + _detail_line("good", "[function] (a)", "[function] (a, b)") + "\n"
            # Malformed: not valid JSON -> must be skipped, not crash.
            + "signature_detail: bad | this is not json\n"
        )
        parsed = _parse_public_surface_failure("", stderr)
        assert parsed is not None
        directive, _signature = parsed
        # The well-formed detail survives with its declared target line.
        assert "Restore `good` to its declared signature `[function] (a)`" in directive
        # The malformed line contributed no declared-target line.
        assert "Restore `bad`" not in directive

    def test_signature_detail_delimiter_substring_in_signature_parses(self):
        """Codex round-8 finding 2: JSON encoding makes a signature/default that
        contains the ` | actual: ` AND ` | source: ` delimiter substrings survive
        intact — the recurring right-split corruption is gone."""
        from pdd.agentic_sync_runner import _parse_public_surface_failure

        expected_sig = "[function] (mode=' | source: X | actual: Y')"
        actual_sig = "[function] (mode='ok')"
        stderr = (
            "Public surface regression for demo_Python.prompt:\n"
            "removed: <none>\n"
            "signature_changed: f\n"
            "output: pdd/demo.py\n"
            "pre_surface_size: 1\n"
            "post_surface_size: 1\n"
            + _detail_line("f", expected_sig, actual_sig) + "\n"
        )
        parsed = _parse_public_surface_failure("", stderr)
        assert parsed is not None
        directive, _signature = parsed
        assert expected_sig in directive
        assert actual_sig in directive

    def test_declared_violation_advice_points_at_declaration(self):
        """Codex round-7 finding 3: since ``BREAKING-CHANGE: change signature`` no
        longer bypasses a declared PARAM contract, the repair advice for a declared
        violation (across the typed error, the agentic hard-failure block, and the
        rebuilt directive) must point at editing the ``<pdd-interface>`` declaration
        and must NOT tell the user to add a ``change signature`` marker (which would
        loop back into the dead-end #1900 removes)."""
        from unittest.mock import patch
        from pdd.code_generator_main import PublicSurfaceRegressionError
        from pdd.agentic_sync_runner import (
            build_public_surface_hard_failure_from_error,
            _parse_public_surface_failure,
        )

        exc = PublicSurfaceRegressionError(
            prompt_name="demo_Python.prompt",
            output_path="pdd/demo.py",
            removed_symbols=[],
            changed_signatures=["f"],
            pre_surface_size=1,
            post_surface_size=1,
            signature_details=[
                ("f", "[function] (a)", "[function] (a, b)", "pdd-interface")
            ],
        )
        # Typed error's repair directive.
        directive = exc.repair_directive
        assert "<pdd-interface>" in directive
        assert "change signature" not in directive

        # Agentic hard-failure block built from the typed error.
        with patch(
            "pdd.agentic_sync_runner._env_fingerprint", return_value="--- env ---"
        ):
            block = build_public_surface_hard_failure_from_error(exc, "demo")
        assert "<pdd-interface>" in block
        assert "change signature" not in block

        # Agentic rebuilt directive parsed from the failure stdout.
        rebuilt = _parse_public_surface_failure("", str(exc) + "\n")
        assert rebuilt is not None
        rebuilt_directive, _sig = rebuilt
        assert "<pdd-interface>" in rebuilt_directive
        assert "change signature" not in rebuilt_directive
