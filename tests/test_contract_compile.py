"""Unit tests for deterministic contract IR compilation."""
from __future__ import annotations

from pathlib import Path

from pdd.contract_compile import compile_directory, compile_prompt

FIXTURES = Path(__file__).parent / "fixtures" / "contract_compile"


def test_compile_prompt_extracts_rule_ids_and_conditions():
    result = compile_prompt(FIXTURES / "refund_payment_python.prompt")

    assert result.error_count == 0
    assert [rule.id for rule in result.rules] == ["R1", "R2", "R3"]
    assert result.rules[0].condition == "a refund request has amount_cents equal to 0"


def test_compile_prompt_extracts_http_and_negative_write_obligations():
    result = compile_prompt(FIXTURES / "refund_payment_python.prompt")
    rule = next(rule for rule in result.rules if rule.id == "R2")

    assert any(
        obligation.type == "return"
        and obligation.value["http_status"] == 409
        for obligation in rule.obligations
    )
    assert any(
        obligation.type == "write"
        and obligation.modal == "MUST NOT"
        and obligation.value["target"] == "a new refund record"
        for obligation in rule.obligations
    )


def test_compile_prompt_extracts_call_and_emit_obligations():
    result = compile_prompt(FIXTURES / "refund_payment_python.prompt")
    rule1 = next(rule for rule in result.rules if rule.id == "R1")
    rule3 = next(rule for rule in result.rules if rule.id == "R3")

    assert any(
        obligation.type == "call"
        and obligation.modal == "MUST NOT"
        and obligation.value["target"] == "provider_client"
        for obligation in rule1.obligations
    )
    assert any(
        obligation.type == "emit"
        and obligation.value["target"] == "refund.accepted"
        for obligation in rule3.obligations
    )


def test_compile_prompt_reports_missing_condition_and_obligation():
    result = compile_prompt(FIXTURES / "uncompilable_python.prompt")
    codes = {error.code for error in result.compile_errors}

    assert "MISSING_CONDITION" in codes
    assert "NO_OBSERVABLE_OBLIGATION" in codes


def test_compile_prompt_legacy_without_contracts_is_clean():
    result = compile_prompt(FIXTURES / "legacy_no_contracts_python.prompt")

    assert result.has_contract_rules is False
    assert result.rule_count == 0
    assert result.error_count == 0


def test_compile_directory_returns_all_prompt_files():
    results = compile_directory(FIXTURES)
    names = {result.path.name for result in results}

    assert "refund_payment_python.prompt" in names
    assert "uncompilable_python.prompt" in names
    assert "legacy_no_contracts_python.prompt" in names


def test_compile_prompt_extracts_generic_return_obligation(tmp_path):
    prompt = tmp_path / "generic_return_python.prompt"
    prompt.write_text(
        "<contract_rules>\n"
        "R1 - Return payload\n"
        "When the request is accepted,\n"
        "the service MUST return a JSON object containing upload_id.\n"
        "</contract_rules>\n",
        encoding="utf-8",
    )

    result = compile_prompt(prompt)
    obligations = result.rules[0].obligations

    assert result.error_count == 0
    assert any(
        obligation.type == "return"
        and obligation.value["target"] == "a JSON object containing upload_id"
        for obligation in obligations
    )


def test_compile_prompt_extracts_raise_obligation(tmp_path):
    prompt = tmp_path / "raise_python.prompt"
    prompt.write_text(
        "<contract_rules>\n"
        "R1 - Raise validation error\n"
        "When the amount is negative,\n"
        "the function MUST raise ValueError.\n"
        "</contract_rules>\n",
        encoding="utf-8",
    )

    result = compile_prompt(prompt)

    assert result.error_count == 0
    assert any(
        obligation.type == "raise"
        and obligation.value["target"] == "ValueError"
        for obligation in result.rules[0].obligations
    )


def test_compile_prompt_reports_unstable_rule_id(tmp_path):
    prompt = tmp_path / "sequential_python.prompt"
    prompt.write_text(
        "<contract_rules>\n"
        "1. When a request is missing a token, the service MUST return HTTP 401.\n"
        "</contract_rules>\n",
        encoding="utf-8",
    )

    result = compile_prompt(prompt)

    assert result.rule_count == 0
    assert result.error_count == 1
    assert result.compile_errors[0].code == "UNSTABLE_RULE_ID"


def test_compiled_ir_as_dict_is_json_safe():
    result = compile_prompt(FIXTURES / "refund_payment_python.prompt")
    payload = result.as_dict()

    assert payload["version"] == "pdd.contract_ir.v1"
    assert payload["rules"][0]["obligations"][0]["value"]["http_status"] == 400
    assert payload["compile_errors"] == []
