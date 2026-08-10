# pylint: disable=missing-module-docstring,missing-function-docstring
"""Deterministic ## Entry Point derivation for story contracts (#2391)."""

from pathlib import Path

from pdd.user_story_tests import (
    _insert_entry_point,
    derive_contract_entry_point,
)


_INTERFACE_ONE = """<pdd-interface>
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

_INTERFACE_TWO = """<pdd-interface>
{
  "type": "module",
  "module": {
    "functions": [
      {"name": "checkout_total", "signature": "(a, b)", "returns": "dict"},
      {"name": "checkout_refund", "signature": "(a)", "returns": "dict"}
    ]
  }
}
</pdd-interface>

% Implement checkout.
"""


def _prompts_root(tmp_path: Path, body: str, name: str = "checkout_python.prompt") -> Path:
    prompts = tmp_path / "prompts"
    prompts.mkdir(parents=True, exist_ok=True)
    (prompts / name).write_text(body, encoding="utf-8")
    (tmp_path / "pdd").mkdir(parents=True, exist_ok=True)
    return prompts


def test_derives_entry_point_from_a_single_declared_callable(tmp_path):
    prompts = _prompts_root(tmp_path, _INTERFACE_ONE)

    block = derive_contract_entry_point(
        [prompts / "checkout_python.prompt"], prompts, tmp_path
    )

    assert block is not None
    assert "## Entry Point" in block
    assert "- callable: checkout_total" in block
    assert "- args: []" in block
    assert "- kwargs: {}" in block


def test_omits_entry_point_when_the_prompt_declares_several_callables(tmp_path):
    """A guessed callable would produce a confidently wrong behavioural test."""
    prompts = _prompts_root(tmp_path, _INTERFACE_TWO)

    assert (
        derive_contract_entry_point(
            [prompts / "checkout_python.prompt"], prompts, tmp_path
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
            tmp_path,
        )
        is None
    )


def test_omits_entry_point_when_the_prompt_declares_no_interface(tmp_path):
    prompts = _prompts_root(tmp_path, "% Just a prompt with no interface block.\n")

    assert (
        derive_contract_entry_point(
            [prompts / "checkout_python.prompt"], prompts, tmp_path
        )
        is None
    )


def test_omits_entry_point_without_a_prompts_root(tmp_path):
    assert derive_contract_entry_point([tmp_path / "x_python.prompt"], None) is None


def test_omits_entry_point_for_an_empty_link_list(tmp_path):
    prompts = _prompts_root(tmp_path, _INTERFACE_ONE)

    assert derive_contract_entry_point([], prompts, tmp_path) is None


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
