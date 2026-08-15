# pylint: disable=missing-module-docstring,missing-function-docstring
"""Deterministic ## Entry Point derivation for story contracts (#2391)."""

from pathlib import Path

from pdd.user_story_tests import (
    _insert_entry_point,
    _oracle_bullets_are_safe_expressions,
    derive_contract_entry_point,
)


_INTERFACE_ONE = """<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "checkout_total", "signature": "()", "returns": "dict"}
    ]
  }
}
</pdd-interface>

% Implement the checkout total.
"""

_INTERFACE_TWO = """<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "checkout_total", "signature": "()", "returns": "dict"},
      {"name": "checkout_refund", "signature": "(a)", "returns": "dict"}
    ]
  }
}
</pdd-interface>

% Implement checkout.
"""

_INTERFACE_REQUIRED_ARGS = """<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "checkout_total", "signature": "(a, b)", "returns": "dict"}
    ]
  }
}
</pdd-interface>

% Implement the checkout total.
"""

_INTERFACE_NO_SIGNATURE = """<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "checkout_total", "returns": "dict"}
    ]
  }
}
</pdd-interface>

% Implement the checkout total.
"""

_INTERFACE_DEFAULTED_ARGS = """<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "checkout_total", "signature": "(a=1, b=2)", "returns": "dict"}
    ]
  }
}
</pdd-interface>

% Implement the checkout total.
"""


def _prompts_root(tmp_path: Path, body: str, name: str = "checkout_python.prompt") -> Path:
    prompts = tmp_path / "prompts"
    prompts.mkdir(parents=True, exist_ok=True)
    prompt = prompts / name
    prompt.parent.mkdir(parents=True, exist_ok=True)
    prompt.write_text(body, encoding="utf-8")
    (tmp_path / "pdd").mkdir(parents=True, exist_ok=True)
    return prompts


def test_derives_entry_point_from_a_single_declared_callable(tmp_path):
    prompts = _prompts_root(tmp_path, _INTERFACE_ONE)
    code = tmp_path / "src" / "checkout.py"
    code.parent.mkdir()
    code.write_text("def checkout_total(): return {}\n", encoding="utf-8")

    block = derive_contract_entry_point([prompts / "checkout_python.prompt"], prompts)

    assert block is not None
    assert "## Entry Point" in block
    assert "- module: checkout" in block
    assert "- callable: checkout_total" in block
    assert "- args: []" in block
    assert "- kwargs: {}" in block


def test_derives_entry_point_when_all_params_have_defaults(tmp_path):
    prompts = _prompts_root(tmp_path, _INTERFACE_DEFAULTED_ARGS)
    code = tmp_path / "src" / "checkout.py"
    code.parent.mkdir()
    code.write_text("def checkout_total(a=1, b=2): return {}\n", encoding="utf-8")

    block = derive_contract_entry_point([prompts / "checkout_python.prompt"], prompts)

    assert block is not None
    assert "- callable: checkout_total" in block


def test_omits_entry_point_when_the_callable_requires_arguments(tmp_path):
    """A guessed ``args: []`` for a required-arg callable is worse than none:
    it produces a generated test that TypeErrors before reaching the Oracle."""
    prompts = _prompts_root(tmp_path, _INTERFACE_REQUIRED_ARGS)
    code = tmp_path / "src" / "checkout.py"
    code.parent.mkdir()
    code.write_text("def checkout_total(a, b): return {}\n", encoding="utf-8")

    assert (
        derive_contract_entry_point([prompts / "checkout_python.prompt"], prompts)
        is None
    )


def test_omits_entry_point_when_the_declared_callable_has_no_signature(tmp_path):
    prompts = _prompts_root(tmp_path, _INTERFACE_NO_SIGNATURE)
    code = tmp_path / "src" / "checkout.py"
    code.parent.mkdir()
    code.write_text("def checkout_total(): return {}\n", encoding="utf-8")

    assert (
        derive_contract_entry_point([prompts / "checkout_python.prompt"], prompts)
        is None
    )


def test_omits_entry_point_when_the_prompt_declares_several_callables(tmp_path):
    """A guessed callable would produce a confidently wrong behavioural test."""
    prompts = _prompts_root(tmp_path, _INTERFACE_TWO)

    assert (
        derive_contract_entry_point(
            [prompts / "checkout_python.prompt"], prompts
        )
        is None
    )


def test_omits_entry_point_when_several_prompts_are_linked(tmp_path):
    prompts = _prompts_root(tmp_path, _INTERFACE_ONE)
    (prompts / "other_python.prompt").write_text(_INTERFACE_ONE, encoding="utf-8")

    assert (
        derive_contract_entry_point(
            [prompts / "checkout_python.prompt", prompts / "other_python.prompt"],
            prompts,
        )
        is None
    )


def test_omits_entry_point_when_the_prompt_declares_no_interface(tmp_path):
    prompts = _prompts_root(tmp_path, "% Just a prompt with no interface block.\n")

    assert (
        derive_contract_entry_point(
            [prompts / "checkout_python.prompt"], prompts
        )
        is None
    )


def test_omits_entry_point_without_a_prompts_root(tmp_path):
    assert derive_contract_entry_point([tmp_path / "x_python.prompt"], None) is None


def test_omits_entry_point_for_an_empty_link_list(tmp_path):
    prompts = _prompts_root(tmp_path, _INTERFACE_ONE)

    assert derive_contract_entry_point([], prompts, tmp_path) is None


def test_omits_entry_point_when_the_mapped_source_module_is_missing(tmp_path):
    prompts = _prompts_root(tmp_path, _INTERFACE_ONE)

    assert (
        derive_contract_entry_point([prompts / "checkout_python.prompt"], prompts)
        is None
    )


def test_derives_module_relative_to_pdd_src_dir(tmp_path, monkeypatch):
    prompts = _prompts_root(
        tmp_path, _INTERFACE_ONE, "payments/checkout_python.prompt"
    )
    code = tmp_path / "custom_src" / "payments" / "checkout.py"
    code.parent.mkdir(parents=True)
    code.write_text("def checkout_total(): return {}\n", encoding="utf-8")
    monkeypatch.setenv("PDD_SRC_DIR", str(tmp_path / "custom_src"))

    block = derive_contract_entry_point(
        [prompts / "payments/checkout_python.prompt"], prompts
    )

    assert block is not None
    assert "- module: payments.checkout" in block


# ---------------------------------------------------------------------------
# insertion
# ---------------------------------------------------------------------------

_BODY = (
    "## Covers\n\n- R1: total\n\n"
    "## Context\n\nSome context.\n\n"
    "## Oracle\n\n- result is a dict\n\n"
    "## Notes\n\n- n/a\n"
)
_BLOCK = "## Entry Point\n\n- module: pdd.checkout\n- callable: checkout_total\n"


def test_entry_point_is_inserted_directly_before_the_oracle():
    merged = _insert_entry_point(_BODY, _BLOCK)

    assert merged.index("## Entry Point") > merged.index("## Context")
    assert merged.index("## Entry Point") < merged.index("## Oracle")
    # Nothing else is disturbed.
    assert "## Covers" in merged and "## Notes" in merged
    assert "- result is a dict" in merged


def test_insertion_is_a_no_op_when_the_contract_already_declares_one():
    already = _BODY.replace("## Oracle", "## Entry Point\n\n- module: x\n\n## Oracle")

    assert _insert_entry_point(already, _BLOCK) == already


def test_entry_point_is_appended_when_the_contract_has_no_oracle():
    body = "## Covers\n\n- R1: total\n"

    merged = _insert_entry_point(body, _BLOCK)

    assert merged.startswith("## Covers")
    assert merged.rstrip().endswith(_BLOCK.rstrip())


# ---------------------------------------------------------------------------
# Oracle safety gate: an Entry Point must not be inserted into a contract
# whose Oracle/Negative Cases bullets aren't safe assertion expressions --
# routing on heading presence would otherwise turn a working (if weak)
# traceability-path generation into a hard error, or worse, splice unsafe
# text into generated pytest source (see story_test_generator.py).
# ---------------------------------------------------------------------------


def test_oracle_gate_accepts_safe_expression_bullets():
    body = "## Oracle\n\n- result['total'] == 42\n- isinstance(result, dict)\n"

    assert _oracle_bullets_are_safe_expressions(body) is True


def test_oracle_gate_rejects_prose_bullets():
    body = "## Oracle\n\n- selected workflow: agentic bug vs manual bug repair\n"

    assert _oracle_bullets_are_safe_expressions(body) is False


def test_oracle_gate_rejects_unsafe_call_expressions():
    body = "## Oracle\n\n- __import__('os').system('echo hi') or True\n"

    assert _oracle_bullets_are_safe_expressions(body) is False


def test_oracle_gate_rejects_when_no_oracle_or_negative_cases_present():
    body = "## Covers\n\n- R1: total\n"

    assert _oracle_bullets_are_safe_expressions(body) is False
