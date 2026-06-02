"""Tests for capability contracts and ``pdd checkup policy check``."""
from __future__ import annotations

import json
from pathlib import Path

from click.testing import CliRunner

from pdd import cli
from pdd.contract_ir import extract_capabilities, parse_prompt_contracts
from pdd.policy_check import run_policy_check

FIXTURE_DIR = Path(__file__).resolve().parent / "fixtures" / "policy_check"
_CLI_ENV = {"PDD_AUTO_UPDATE": "false"}


def _cli_json_payload(output: str) -> list:
    """Extract the JSON array from mixed CLI output (debug snapshots, etc.)."""
    start = output.index("[")
    end = output.rindex("]") + 1
    return json.loads(output[start:end])


def test_extract_capabilities_parses_modals() -> None:
    """Capability bullets retain modal metadata for policy enforcement."""
    prompt = FIXTURE_DIR / "forbidden_network_python.prompt"
    ir = parse_prompt_contracts(prompt)
    capabilities = extract_capabilities(ir.sections["capabilities"])
    assert any(c.is_must_not and "network" in c.text.lower() for c in capabilities)
    assert any(not c.is_must_not for c in capabilities)


def test_allowed_code_passes_with_matching_prompt() -> None:
    """Allowed imports and env reads pass when capabilities permit them."""
    prompt = FIXTURE_DIR / "allowed_refund_python.prompt"
    target = FIXTURE_DIR / "allowed_refund.py"
    result = run_policy_check(target, prompt)
    assert result.passed
    assert result.issues == []


def test_forbidden_network_import_fails() -> None:
    """Network libraries are flagged when capabilities forbid them."""
    prompt = FIXTURE_DIR / "forbidden_network_python.prompt"
    target = FIXTURE_DIR / "forbidden_network.py"
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "network" for i in result.issues)


def test_sensitive_logging_fails() -> None:
    """Logging sensitive variable names is reported as leakage."""
    prompt = FIXTURE_DIR / "sensitive_log_python.prompt"
    target = FIXTURE_DIR / "sensitive_log.py"
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "leakage" for i in result.issues)


def test_legacy_prompt_without_capabilities_does_not_fail() -> None:
    """Modules without capability sections stay permissive unless strict."""
    legacy_prompt = (
        Path(__file__).resolve().parent / "fixtures" / "test_generation" / "refund_policy_python.prompt"
    )
    target = FIXTURE_DIR / "forbidden_network.py"
    result = run_policy_check(target, legacy_prompt, strict=False)
    assert result.passed


def test_strict_mode_flags_side_effects_without_capabilities() -> None:
    """Strict mode enforces checks even when the prompt omits capabilities."""
    legacy_prompt = (
        Path(__file__).resolve().parent / "fixtures" / "test_generation" / "refund_policy_python.prompt"
    )
    target = FIXTURE_DIR / "forbidden_network.py"
    result = run_policy_check(target, legacy_prompt, strict=True)
    assert not result.passed


def test_invalid_python_fails_gracefully(tmp_path: Path) -> None:
    """Syntax errors surface as system issues instead of raising."""
    broken = tmp_path / "broken.py"
    broken.write_text("def oops(\n", encoding="utf-8")
    result = run_policy_check(broken)
    assert not result.passed
    assert any(i.category == "system" for i in result.issues)


def test_endpoint_capability_allows_network_keywords() -> None:
    """Issue #828 example bullets using 'endpoint' allow network libraries."""
    prompt = FIXTURE_DIR / "allowed_refund_python.prompt"
    text = (FIXTURE_DIR / "allowed_refund.py").read_text(encoding="utf-8")
    text += "\nimport requests\n"
    target = FIXTURE_DIR / "_tmp_endpoint.py"
    target.write_text(text, encoding="utf-8")
    try:
        result = run_policy_check(target, prompt)
        assert result.passed
    finally:
        target.unlink(missing_ok=True)


def test_forbidden_email_import() -> None:
    prompt = FIXTURE_DIR / "forbidden_email_python.prompt"
    target = FIXTURE_DIR / "forbidden_email.py"
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "email" for i in result.issues)


def test_file_write_open_mode_detected() -> None:
    prompt = FIXTURE_DIR / "file_write_python.prompt"
    target = FIXTURE_DIR / "file_write.py"
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "file" for i in result.issues)


def test_read_only_open_allowed() -> None:
    prompt = FIXTURE_DIR / "file_write_python.prompt"
    target = FIXTURE_DIR / "read_only_open.py"
    result = run_policy_check(target, prompt)
    assert result.passed


def test_inline_waiver_suppresses_issue(tmp_path: Path) -> None:
    prompt = FIXTURE_DIR / "file_write_python.prompt"
    target = tmp_path / "waived.py"
    target.write_text(
        "def persist(data: str) -> None:\n"
        "    # pdd-policy-ignore: test fixture allows write\n"
        "    with open('out.txt', 'w', encoding='utf-8') as handle:\n"
        "        handle.write(data)\n",
        encoding="utf-8",
    )
    result = run_policy_check(target, prompt)
    assert result.passed


def test_percent_format_logging_detected(tmp_path: Path) -> None:
    prompt = FIXTURE_DIR / "sensitive_log_python.prompt"
    target = tmp_path / "percent_log.py"
    target.write_text(
        "import logging\n"
        "logger = logging.getLogger(__name__)\n"
        "def audit(secret: str) -> None:\n"
        "    logger.info('value %s', secret)\n",
        encoding="utf-8",
    )
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "leakage" for i in result.issues)


def test_domain_write_capability_does_not_allow_filesystem_open(tmp_path: Path) -> None:
    """Issue #828 style: domain 'write records' must not permit open(..., 'w')."""
    prompt = tmp_path / "domain_write.prompt"
    prompt.write_text(
        "<capabilities>\n"
        "- MAY write refund records.\n"
        "- MUST NOT send emails.\n"
        "</capabilities>\n",
        encoding="utf-8",
    )
    target = tmp_path / "refund.py"
    target.write_text(
        "def refund() -> None:\n"
        "    open('/tmp/pdd_policy_probe', 'w').write('x')\n",
        encoding="utf-8",
    )
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "file" for i in result.issues)


def test_pathlib_write_text_requires_filesystem_capability(tmp_path: Path) -> None:
    prompt = tmp_path / "no_file.prompt"
    prompt.write_text(
        "<capabilities>\n- MAY read configuration.\n</capabilities>\n",
        encoding="utf-8",
    )
    target = tmp_path / "path_write.py"
    target.write_text(
        "from pathlib import Path\n\n"
        "def save() -> None:\n"
        "    Path('/tmp/pdd_policy_path_probe').write_text('x')\n",
        encoding="utf-8",
    )
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "file" and "write_text" in i.message for i in result.issues)


def test_pathlib_write_bytes_and_open_write_mode(tmp_path: Path) -> None:
    prompt = tmp_path / "no_file.prompt"
    prompt.write_text("<capabilities>\n- MAY call provider API.\n</capabilities>\n", encoding="utf-8")
    target = tmp_path / "path_ops.py"
    target.write_text(
        "from pathlib import Path\n\n"
        "def save() -> None:\n"
        "    Path('/tmp/a').write_bytes(b'x')\n"
        "    Path('/tmp/b').open('w').write('y')\n",
        encoding="utf-8",
    )
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert sum(1 for i in result.issues if i.category == "file") >= 2


def test_import_os_environ_subscript_blocked(tmp_path: Path) -> None:
    prompt = tmp_path / "no_env.prompt"
    prompt.write_text("<capabilities>\n- MAY read records.\n</capabilities>\n", encoding="utf-8")
    target = tmp_path / "env_read.py"
    target.write_text(
        "from os import environ\n\n"
        "def token() -> str:\n"
        "    return environ['SECRET_TOKEN']\n",
        encoding="utf-8",
    )
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "env" for i in result.issues)


def test_import_os_as_alias_environ_blocked(tmp_path: Path) -> None:
    prompt = tmp_path / "no_env.prompt"
    prompt.write_text("<capabilities>\n- MAY read records.\n</capabilities>\n", encoding="utf-8")
    target = tmp_path / "env_alias.py"
    target.write_text(
        "import os as o\n\n"
        "def token() -> str:\n"
        "    return o.environ['SECRET_TOKEN']\n",
        encoding="utf-8",
    )
    result = run_policy_check(target, prompt)
    assert not result.passed
    assert any(i.category == "env" and "environ" in i.message for i in result.issues)


def test_explicit_filesystem_capability_allows_pathlib_write(tmp_path: Path) -> None:
    prompt = tmp_path / "file_ok.prompt"
    prompt.write_text(
        "<capabilities>\n- MAY write audit files to disk.\n</capabilities>\n",
        encoding="utf-8",
    )
    target = tmp_path / "allowed_path.py"
    target.write_text(
        "from pathlib import Path\n\n"
        "def audit(line: str) -> None:\n"
        "    Path('/tmp/audit.log').write_text(line)\n",
        encoding="utf-8",
    )
    result = run_policy_check(target, prompt)
    assert result.passed


def test_policy_check_cli_json_output() -> None:
    """CLI ``--json`` returns structured findings for CI integration."""
    target = FIXTURE_DIR / "forbidden_network.py"
    prompt = FIXTURE_DIR / "forbidden_network_python.prompt"
    result = CliRunner().invoke(
        cli.cli,
        ["checkup", "policy", "check", str(target), "--prompt", str(prompt), "--json"],
        env=_CLI_ENV,
    )
    assert result.exit_code != 0, result.output
    payload = _cli_json_payload(result.output)
    assert payload[0]["passed"] is False
    assert payload[0]["capabilities"]
    assert payload[0]["issues"]
