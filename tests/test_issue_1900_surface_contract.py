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

    def test_presence_only_declared_signature(self):
        """A declared signature that is not a parseable paren-list (here:
        omitted) is presence-only: the symbol must exist but its signature is
        NOT checked, so an arbitrary signature change passes; its ABSENCE is
        still a violation."""
        prompt = _iface_prompt([("f", None)])
        # Present with a wildly different signature -> no signature false-positive.
        _verify_public_surface_regression(
            "def f(a):\n    return a\n",
            "def f(a, b, c, d):\n    return a\n",
            PROMPT,
            OUT,
            "python",
            prompt,
        )
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
