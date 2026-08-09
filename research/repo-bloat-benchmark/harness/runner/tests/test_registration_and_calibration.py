"""Tests for env registration (blocker 2) and first-run calibration (blocker 4)."""

import hashlib
import json
import stat
import sys
import textwrap
from pathlib import Path

import pytest

from harness.runner.env_freeze import FreezeViolation
from harness.runner.first_run_calibration import calibrate
from harness.runner.register_env import load_arm_config, register

ARM_PATH = Path(__file__).resolve().parents[1] / "pilot_arm_codex.json"


def _write_fake_cli(tmp_path, version: str) -> str:
    script = tmp_path / "fake-cli"
    script.write_text(
        textwrap.dedent(
            f"""\
            #!{sys.executable}
            print("{version}")
            """
        )
    )
    script.chmod(script.stat().st_mode | stat.S_IEXEC)
    return str(script)


def _arm_file(tmp_path, cli_path, version="codex-cli 9.9.9-test") -> Path:
    arm = json.loads(ARM_PATH.read_text())
    arm.pop("_comment", None)
    arm["pinned_cli_version"] = version
    arm["cli_version_command"] = [cli_path, "--version"]
    path = tmp_path / "arm.json"
    path.write_text(json.dumps(arm))
    return path


def test_register_emits_stable_fingerprint_matching_freeze_config(tmp_path):
    cli = _write_fake_cli(tmp_path, "codex-cli 9.9.9-test")
    arm_path = _arm_file(tmp_path, cli)
    record = register(arm_path)
    assert record["cli_version_verified"] == "codex-cli 9.9.9-test"
    assert record["valid_for_runs"] is True
    assert record["binary_check_skipped"] is False
    expected = load_arm_config(arm_path).fingerprint()
    assert record["registered_env_fingerprint"] == expected
    assert register(arm_path)["registered_env_fingerprint"] == expected


def test_skip_binary_check_record_is_not_valid_for_runs(tmp_path):
    cli = _write_fake_cli(tmp_path, "codex-cli 9.9.9-test")
    arm_path = _arm_file(tmp_path, cli)
    record = register(arm_path, check_binary=False)
    assert record["valid_for_runs"] is False
    assert record["binary_check_skipped"] is True
    # The authoritative key is absent — no consumer can mistake this for real.
    assert "registered_env_fingerprint" not in record
    assert "unverified_fingerprint" in record


def test_register_aborts_on_version_mismatch(tmp_path):
    cli = _write_fake_cli(tmp_path, "codex-cli 0.0.1-other")
    arm_path = _arm_file(tmp_path, cli, version="codex-cli 9.9.9-test")
    with pytest.raises(FreezeViolation, match="pin is"):
        register(arm_path)


def test_committed_arm_config_loads_and_matches_pin_doc():
    config = load_arm_config(ARM_PATH)
    assert config.pinned_cli_version == "codex-cli 0.142.4"
    assert config.model_id == "gpt-5.1-codex-max"
    assert config.reasoning_effort == "medium"
    assert config.context_window_tokens == 272_000
    assert config.api_key_env_var == "OPENAI_API_KEY"
    assert not config.web_search_enabled
    rendered = config.render_config("http://x")
    assert 'wire_api = "responses"' in rendered
    assert "model_context_window = 272000" in rendered


# -- first-run calibration ----------------------------------------------------

_ARM = {"model_id": "gpt-5.1-codex-max", "pinned_cli_version": "codex-cli 0.142.4"}
_FINGERPRINT = "f" * 64


def _build_run_dir(tmp_path, *, model="gpt-5.1-codex-max", tamper_payload=False,
                   fingerprint=_FINGERPRINT, agent_error=False, returncode=0,
                   timed_out=False) -> Path:
    run_dir = tmp_path / "run"
    (run_dir / "payloads").mkdir(parents=True)
    request = json.dumps({"model": model, "input": []}).encode()
    (run_dir / "payloads" / "00001.request.json").write_bytes(request)
    completed = {
        "type": "response.completed",
        "response": {"id": "r1", "status": "completed", "output": [],
                     "usage": {"input_tokens": 10, "output_tokens": 2,
                               "total_tokens": 12}},
    }
    (run_dir / "payloads" / "00001.response.body").write_bytes(
        f"event: response.completed\ndata: {json.dumps(completed)}\n\n".encode()
    )
    sha = hashlib.sha256(b"tampered" if tamper_payload else request).hexdigest()
    snapshot = {
        "ordinal": 1, "endpoint": "/v1/responses", "request_sha256": sha,
        "payload_path": "payloads/00001.request.json",
        "response_path": "payloads/00001.response.body",
        "model": model, "input_tokens": 10, "streamed": True,
    }
    (run_dir / "context_snapshots.jsonl").write_text(json.dumps(snapshot) + "\n")
    (run_dir / "run_record.json").write_text(json.dumps({
        "cli_version": "codex-cli 0.142.4",
        "env_fingerprint_sha256": fingerprint,
        "token_metrics_supported": True,
        "development_only": False,
        "agent_error": agent_error,
    }))
    (run_dir / "agent_process.json").write_text(json.dumps({
        "returncode": returncode,
        "timed_out": timed_out,
    }))
    return run_dir


def test_calibration_go_on_conforming_run(tmp_path):
    verdict = calibrate(_build_run_dir(tmp_path), _ARM, _FINGERPRINT)
    assert verdict["checks"] == {k: True for k in verdict["checks"]}
    assert verdict["go"] is True


def test_calibration_no_go_on_model_mismatch(tmp_path):
    run_dir = _build_run_dir(tmp_path, model="some-other-model")
    verdict = calibrate(run_dir, _ARM, _FINGERPRINT)
    assert verdict["checks"]["model_matches_pin"] is False
    assert verdict["go"] is False


def test_calibration_no_go_on_payload_tamper(tmp_path):
    verdict = calibrate(_build_run_dir(tmp_path, tamper_payload=True), _ARM, _FINGERPRINT)
    assert verdict["checks"]["payload_sha256_integrity"] is False
    assert verdict["go"] is False


def test_calibration_no_go_without_registration(tmp_path):
    verdict = calibrate(_build_run_dir(tmp_path), _ARM, None)
    assert verdict["checks"]["env_fingerprint_registered"] is False
    assert verdict["go"] is False


def test_calibration_no_go_on_empty_run_dir(tmp_path):
    empty = tmp_path / "empty"
    empty.mkdir()
    verdict = calibrate(empty, _ARM, _FINGERPRINT)
    assert verdict["go"] is False
    assert verdict["checks"]["snapshots_present"] is False


def test_calibration_no_go_when_a_snapshot_response_is_missing(tmp_path):
    run_dir = _build_run_dir(tmp_path)
    # Delete the response body but leave the snapshot metadata (which still
    # carries input_tokens) — this must NO-GO, not be silently skipped.
    (run_dir / "payloads" / "00001.response.body").unlink()
    verdict = calibrate(run_dir, _ARM, _FINGERPRINT)
    assert verdict["checks"]["response_parsed_for_every_request"] is False
    assert verdict["go"] is False


def test_calibration_no_go_when_run_record_marks_agent_error(tmp_path):
    verdict = calibrate(
        _build_run_dir(tmp_path, agent_error=True, returncode=3), _ARM, _FINGERPRINT
    )
    assert verdict["checks"]["agent_error_false"] is False
    assert verdict["checks"]["agent_process_exit_zero"] is False
    assert verdict["go"] is False
