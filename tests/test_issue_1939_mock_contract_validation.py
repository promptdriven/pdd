"""Regression coverage for generated mock-vs-real-contract validation (#1939)."""

from __future__ import annotations

import io
from pathlib import Path

from rich.console import Console

from pdd.agentic_e2e_fix_orchestrator import (
    _find_mock_contract_test_files,
    _post_step9_resume_action,
    _resolve_step9_loop_token,
)


def _console() -> Console:
    return Console(file=io.StringIO(), force_terminal=False)


def _write(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def test_mock_audit_routing_uses_mock_apis_not_field_name_heuristics(
    tmp_path: Path,
) -> None:
    """Route on actual mocking APIs, never on suspicious-looking field names."""
    plain_test = tmp_path / "tests" / "test_plain_contract.py"
    mocked_test = tmp_path / "tests" / "test_mocked_contract.py"
    pytest_mock_test = tmp_path / "tests" / "test_pytest_mock_contract.py"
    _write(
        plain_test,
        "def test_payload():\n"
        "    payload = {'userId': 'uid-1'}\n"
        "    assert payload['userId'] == 'uid-1'\n",
    )
    _write(
        mocked_test,
        "from unittest.mock import patch\n\n"
        "def test_reader():\n"
        "    with patch('service.read_user') as reader:\n"
        "        reader.return_value = {'uid': 'uid-1'}\n"
        "        assert reader()['uid'] == 'uid-1'\n",
    )
    _write(
        pytest_mock_test,
        "def test_reader(mocker):\n"
        "    reader = mocker.patch('service.read_user')\n"
        "    reader.return_value = {'uid': 'uid-1'}\n"
        "    assert reader()['uid'] == 'uid-1'\n",
    )

    result = _find_mock_contract_test_files(
        [
            "tests/test_plain_contract.py",
            "tests/test_mocked_contract.py",
            "tests/test_pytest_mock_contract.py",
        ],
        tmp_path,
    )

    assert result == [
        "tests/test_mocked_contract.py",
        "tests/test_pytest_mock_contract.py",
    ]


def test_4235_impossible_query_mock_cannot_be_certified_by_green_tests(
    tmp_path: Path,
) -> None:
    """The live #4235 shape is routed to audit and mismatch overrides green."""
    _write(
        tmp_path / "context" / "database-schema.md",
        "user_waitlist is keyed by the user UID document id; documents do not "
        "contain a userId field.\n",
    )
    _write(
        tmp_path / "service.py",
        "def list_waitlist(query_collection, uids):\n"
        "    return query_collection('user_waitlist', "
        "filters=[('userId', 'in', uids)])\n",
    )
    test_path = tmp_path / "tests" / "test_service.py"
    _write(
        test_path,
        "from unittest.mock import MagicMock\n"
        "from service import list_waitlist\n\n"
        "def test_batch_lookup():\n"
        "    query_collection = MagicMock(return_value=[{'userId': 'uid-1'}])\n"
        "    assert list_waitlist(query_collection, ['uid-1'])\n",
    )

    audit_files = _find_mock_contract_test_files(
        ["tests/test_service.py"], tmp_path
    )
    output = """All generated tests pass.
The schema and sibling document readers prove that user_waitlist uses UID
document ids and has no userId query field.
**Mock contract audit:** MOCK_CONTRACT_MISMATCH
**Status:** ALL_TESTS_PASS
"""

    assert audit_files == ["tests/test_service.py"]
    assert (
        _resolve_step9_loop_token(
            output,
            _console(),
            mock_contract_audit_required=bool(audit_files),
        )
        == "CONTINUE_CYCLE"
    )


def test_real_contract_mock_keeps_the_existing_pass_path() -> None:
    """A verified test double preserves the normal independently-tested pass path."""
    output = """The mock matches the declared UserRecord type and both production readers.
**Mock contract audit:** MOCK_CONTRACTS_VERIFIED
**Status:** ALL_TESTS_PASS
"""

    assert (
        _resolve_step9_loop_token(
            output,
            _console(),
            mock_contract_audit_required=True,
        )
        == "LOCAL_TESTS_PASS"
    )


def test_required_audit_missing_exact_verification_line_fails_closed() -> None:
    """A prose mention cannot impersonate the exact audit result line."""
    output = """All tests pass. I considered MOCK_CONTRACTS_VERIFIED in prose.
**Status:** ALL_TESTS_PASS
"""

    assert (
        _resolve_step9_loop_token(
            output,
            _console(),
            mock_contract_audit_required=True,
        )
        == "CONTINUE_CYCLE"
    )


def test_tests_without_mocks_do_not_require_a_new_marker() -> None:
    """Tests without doubles retain the pre-#1939 Step 9 behavior."""
    assert (
        _resolve_step9_loop_token(
            "**Status:** ALL_TESTS_PASS",
            _console(),
            mock_contract_audit_required=False,
        )
        == "LOCAL_TESTS_PASS"
    )


def test_cached_step9_pass_reapplies_mock_contract_gate_on_resume() -> None:
    """Resume must not trust a pre-gate cached success token."""
    unverified = _post_step9_resume_action(
        "**Status:** ALL_TESTS_PASS",
        current_cycle=1,
        max_cycles=3,
        console=_console(),
        mock_contract_audit_required=True,
    )
    verified = _post_step9_resume_action(
        "**Mock contract audit:** MOCK_CONTRACTS_VERIFIED\n"
        "**Status:** ALL_TESTS_PASS",
        current_cycle=1,
        max_cycles=3,
        console=_console(),
        mock_contract_audit_required=True,
    )

    assert unverified == "ADVANCE_CYCLE"
    assert verified == "SUCCESS_FALL_THROUGH"


def test_step9_prompt_requires_real_contract_evidence_and_exact_markers() -> None:
    """The audit prompt anchors decisions in real contracts and exact markers."""
    prompt = (
        Path(__file__).resolve().parents[1]
        / "pdd"
        / "prompts"
        / "agentic_e2e_fix_step9_verify_all_LLM.prompt"
    ).read_text(encoding="utf-8")

    for expected in (
        "{mock_contract_audit_required}",
        "{mock_contract_test_files}",
        "schema documentation",
        "declared interfaces/types",
        "production readers and writers",
        "sibling production call sites",
        "query fields/operators",
        "MOCK_CONTRACT_MISMATCH",
        "MOCK_CONTRACTS_VERIFIED",
        "Do not treat the generated test",
    ):
        assert expected in prompt
