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

import pytest

from pdd.code_generator_main import (
    PublicSurfaceRegressionError,
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


class TestIssue1900SurfaceContract:
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

    def test_presence_only_declared_signature_falls_back_to_old_code(self):
        """A declared signature that is not a parseable paren-list (here: omitted)
        is presence-only for the DECLARED check, but it FALLS BACK to the old-code
        baseline (its exact pre-PR protection) rather than being skipped from every
        check. So a backward-compatible change passes, an incompatible change
        raises, and its ABSENCE is a violation."""
        prompt = _iface_prompt([("f", None)])
        # Present with a backward-compatible change (added optional) -> no raise.
        _verify_public_surface_regression(
            "def f(a):\n    return a\n",
            "def f(a, b=None):\n    return a\n",
            PROMPT,
            OUT,
            "python",
            prompt,
        )
        # Present with an incompatible change (added required) -> the old-code
        # baseline still catches it (no longer silently unchecked).
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
        # Absent from generated code -> violation.
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                "def f(a):\n    return a\n",
                "def other():\n    return 1\n",
                PROMPT,
                OUT,
                "python",
                prompt,
            )
        assert "f" in exc.value.removed_symbols

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

    def test_dotted_init_presence_satisfied_by_class_symbol(self):
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
        # Constructor signature drift (added optional param) is owned by the
        # conformance gate; the surface gate must not raise here.
        after = (
            "class Foo:\n"
            "    def __init__(self, value, extra=None):\n"
            "        self.value = value\n"
        )
        _verify_public_surface_regression(
            before, after, PROMPT, OUT, "python", prompt
        )
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
        assert "Foo" in exc.value.removed_symbols

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

    def test_declared_async_regenerated_async_passes(self):
        """The anchor must not create a false positive: a declared async function
        regenerated async — even with an added OPTIONAL parameter — is
        backward-compatible and must NOT raise."""
        prompt = _iface_prompt([("f", "(x)")])
        _verify_public_surface_regression(
            "async def f(x):\n    return x\n",
            "async def f(x, y=None):\n    return x\n",
            PROMPT,
            OUT,
            "python",
            prompt,
        )

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

    def test_presence_only_declared_class_ctor_drift_raises(self):
        """Codex F3: a declared class whose signature is a non-paren string
        (``class Service``) is presence-only for the declared check (its
        ``_declared_signature_to_entry`` is None) and must still fall back to the
        old-code baseline, catching an added required ``__init__`` parameter."""
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
        with pytest.raises(PublicSurfaceRegressionError) as exc:
            _verify_public_surface_regression(
                before, after, PROMPT, OUT, "python", prompt
            )
        assert "Service" in exc.value.changed_signatures

    def test_breaking_change_on_declared_method_relaxes_only_kind(self):
        """Codex round-5: now that declared methods are validated against the
        declaration, ``BREAKING-CHANGE: change signature <method>`` must relax ONLY
        the un-declarable binding-kind/async — a binding-kind flip opted out passes,
        but an added-required PARAM that violates the declaration STILL raises
        (consistent with FM2; the declaration is authoritative for params)."""
        # (a) binding-kind flip (staticmethod -> instance) opted out -> passes.
        flip_prompt = _iface_prompt(
            [("Factory.build", "(path)")],
            body="% engineer\nBREAKING-CHANGE: change signature Factory.build\n",
        )
        _verify_public_surface_regression(
            "class Factory:\n    @staticmethod\n    def build(path):\n        return path\n",
            "class Factory:\n    def build(self, path):\n        return path\n",
            PROMPT,
            OUT,
            "python",
            flip_prompt,
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
            "signature_detail: list_secret_metadata | expected: "
            "[function] (project_id, prefix='') | actual: "
            "[function] (project_id, prefix='', *, region) | source: pdd-interface\n"
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
        """Codex finding 3: a ``signature_detail:`` line whose expected AND actual
        entries contain PEP-604 ` | ` union types must round-trip through the
        parser with the FULL signatures intact (no truncation at the ` | ` inside
        the signature). Right-anchored field splitting keeps the trailing
        ``| actual:`` / ``| source:`` field delimiters unambiguous."""
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
            f"signature_detail: f | expected: {expected_sig} | "
            f"actual: {actual_sig} | source: pdd-interface\n"
        )
        parsed = _parse_public_surface_failure("", stderr)
        assert parsed is not None
        directive, _signature = parsed
        assert expected_sig in directive
        assert actual_sig in directive

    def test_malformed_signature_detail_line_is_skipped_not_crash(self):
        """Codex round-2 finding 3: a malformed ``signature_detail:`` line (fields
        out of order) must be SKIPPED, never raise. A well-formed line in the same
        payload must still parse."""
        from pdd.agentic_sync_runner import _parse_public_surface_failure

        stderr = (
            "Public surface regression for demo_Python.prompt:\n"
            "removed: <none>\n"
            "signature_changed: good, bad\n"
            "output: pdd/demo.py\n"
            "pre_surface_size: 2\n"
            "post_surface_size: 2\n"
            # Well-formed.
            "signature_detail: good | expected: [function] (a) | "
            "actual: [function] (a, b) | source: pdd-interface\n"
            # Malformed: fields out of order -> must be skipped, not crash.
            "signature_detail: bad | source: pdd-interface | "
            "actual: [function] (a) | expected: [function] (b)\n"
        )
        parsed = _parse_public_surface_failure("", stderr)
        assert parsed is not None
        directive, _signature = parsed
        # The well-formed detail survives with its declared target line.
        assert "Restore `good` to its declared signature `[function] (a)`" in directive
        # The malformed line contributed no declared-target line.
        assert "Restore `bad`" not in directive

    def test_signature_detail_delimiter_substring_in_signature_parses(self):
        """Codex FM3: a VALID ``signature_detail:`` line whose expected default
        contains the ` | source: ` and ` | actual: ` delimiter substrings must
        still parse — the right-anchored rsplit resolves the real trailing
        delimiters — and must NOT be dropped (which would lose the stable declared
        target and fall back to the generic directive)."""
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
            f"signature_detail: f | expected: {expected_sig} | "
            f"actual: {actual_sig} | source: pdd-interface\n"
        )
        parsed = _parse_public_surface_failure("", stderr)
        assert parsed is not None
        directive, _signature = parsed
        assert expected_sig in directive
        assert actual_sig in directive
