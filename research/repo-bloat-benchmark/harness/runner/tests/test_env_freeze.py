"""Tests for the §8.1.1 run-environment freeze.

Unit tests pin each freeze guarantee; the end-to-end test runs a real
subprocess agent (arm="command") under a frozen environment and asserts the
guarantees held *inside* the agent process.
"""

import json
from pathlib import Path

import pytest

from harness.distractors.generator import GenerationConfig, generate_manifest
from harness.distractors.manifest import ManifestWriter, write_lockfile
from harness.runner.env_freeze import (
    FreezeConfig,
    FreezeViolation,
    FrozenEnvironment,
    capture_cli_version,
    egress_guard_env,
)
from harness.runner.mock_agent import MockModelServer
from harness.runner.runner import ExperimentRunner, RunConfig

FAKE_VERSION = "codex-cli 0.0-test"
VERSION_COMMAND = ["python3", "-c", f"print('{FAKE_VERSION}')"]


def _freeze_config(**overrides):
    defaults = dict(
        pinned_cli_version=FAKE_VERSION,
        cli_version_command=list(VERSION_COMMAND),
        model_id="mock-model",
        reasoning_effort="medium",
        api_key_env_var="FAKE_API_KEY",
    )
    defaults.update(overrides)
    return FreezeConfig(**defaults)


# -- config rendering + fingerprint -----------------------------------------


def test_render_config_pins_model_provider_and_history():
    rendered = _freeze_config().render_config("http://127.0.0.1:9999")
    assert 'model = "mock-model"' in rendered
    assert 'model_reasoning_effort = "medium"' in rendered
    assert 'base_url = "http://127.0.0.1:9999/v1"' in rendered
    assert 'persistence = "none"' in rendered
    assert "web_search = false" in rendered
    assert "mcp_servers" not in rendered  # none unless the arm defines them


def test_render_config_enumerates_frozen_mcp_set():
    rendered = _freeze_config(mcp_servers=("alpha",)).render_config("http://x")
    assert "[mcp_servers.alpha]" in rendered


def test_fingerprint_deterministic_and_port_independent(tmp_path):
    config = _freeze_config()
    env_a = FrozenEnvironment(config, tmp_path / "a", "http://127.0.0.1:1111").build()
    env_b = FrozenEnvironment(config, tmp_path / "b", "http://127.0.0.1:2222").build()
    assert env_a.fingerprint() == env_b.fingerprint() == config.fingerprint()


def test_fingerprint_changes_with_frozen_fields():
    base = _freeze_config().fingerprint()
    assert _freeze_config(model_id="other-model").fingerprint() != base
    assert _freeze_config(reasoning_effort="high").fingerprint() != base
    assert _freeze_config(web_search_enabled=True).fingerprint() != base
    assert _freeze_config(mcp_servers=("alpha",)).fingerprint() != base


def test_verify_fingerprint_mismatch_aborts(tmp_path):
    env = FrozenEnvironment(
        _freeze_config(), tmp_path, "http://127.0.0.1:1"
    ).build()
    with pytest.raises(FreezeViolation, match="fingerprint mismatch"):
        env.verify_fingerprint("0" * 64)


# -- version pinning ---------------------------------------------------------


def test_capture_cli_version():
    assert capture_cli_version(VERSION_COMMAND) == FAKE_VERSION


def test_version_mismatch_aborts(tmp_path):
    config = _freeze_config(pinned_cli_version="codex-cli 9.9-other")
    with pytest.raises(FreezeViolation, match="version mismatch"):
        FrozenEnvironment(config, tmp_path, "http://127.0.0.1:1").build()


def test_version_command_failure_aborts():
    with pytest.raises(FreezeViolation, match="cannot capture|failed"):
        capture_cli_version(["python3", "-c", "raise SystemExit(3)"])


# -- fresh home + ephemerality ------------------------------------------------


def test_home_is_fresh_and_reuse_aborts(tmp_path):
    config = _freeze_config()
    env = FrozenEnvironment(config, tmp_path, "http://127.0.0.1:1").build()
    assert sorted(p.name for p in env.home_dir.iterdir()) == ["config.toml"]
    with pytest.raises(FreezeViolation, match="already exists"):
        FrozenEnvironment(config, tmp_path, "http://127.0.0.1:1").build()


def test_collect_and_destroy_archives_then_deletes(tmp_path):
    env = FrozenEnvironment(
        _freeze_config(), tmp_path, "http://127.0.0.1:1"
    ).build()
    sessions = env.home_dir / "sessions"
    sessions.mkdir()
    (sessions / "rollout.jsonl").write_text('{"type": "session_meta"}\n')
    archived = env.collect_and_destroy()
    assert archived == ["sessions/rollout.jsonl"]
    assert not env.home_dir.exists()  # nothing can leak into a later run
    assert (tmp_path / "codex_home_artifacts" / "sessions" / "rollout.jsonl").is_file()


# -- sanitized environment + egress guard -------------------------------------


def test_environment_is_allowlist_only(tmp_path, monkeypatch):
    monkeypatch.setenv("SUPER_SECRET_TOKEN", "leak-me")
    monkeypatch.setenv("FAKE_API_KEY", "sk-test")
    env = FrozenEnvironment(
        _freeze_config(), tmp_path, "http://127.0.0.1:4321"
    ).build()
    variables = env.environment()
    assert "SUPER_SECRET_TOKEN" not in variables  # dropped: not allowlisted
    assert variables["FAKE_API_KEY"] == "sk-test"  # the one permitted secret
    assert variables["CODEX_HOME"] == str(env.home_dir)
    assert variables["OPENAI_BASE_URL"] == "http://127.0.0.1:4321/v1"
    assert "PATH" in variables


def test_egress_guard_blackholes_everything_but_loopback():
    guard = egress_guard_env("http://127.0.0.1:5555")
    assert guard["HTTPS_PROXY"].endswith(":9")
    assert guard["HTTP_PROXY"].endswith(":9")
    assert "127.0.0.1" in guard["NO_PROXY"]
    assert "localhost" in guard["NO_PROXY"]
    assert guard["https_proxy"] == guard["HTTPS_PROXY"]  # lower-case honored too


def test_environment_before_build_aborts(tmp_path):
    env = FrozenEnvironment(_freeze_config(), tmp_path, "http://127.0.0.1:1")
    with pytest.raises(FreezeViolation, match="before build"):
        env.environment()


# -- end-to-end: command arm under a frozen environment ------------------------

SCENARIO_DIR = Path(__file__).resolve().parents[3] / "scenarios" / "example-pagination"

# The scripted "agent": asserts the freeze guarantees from inside the agent
# process, leaves a session artifact, and makes one model request through the
# proxy. It never edits, so the run ends as a localization_miss.
AGENT_SCRIPT = r"""
import json, os, sys, urllib.request, urllib.error
from pathlib import Path

home = Path(os.environ["CODEX_HOME"])
assert [p.name for p in home.iterdir()] == ["config.toml"], "home not fresh"
assert "SUPER_SECRET_TOKEN" not in os.environ, "env not sanitized"
assert os.environ["HTTPS_PROXY"].endswith(":9"), "egress guard missing"

sessions = home / "sessions"
sessions.mkdir()
sessions.joinpath("rollout.jsonl").write_text(
    json.dumps({"type": "event_msg", "payload": {"type": "token_count",
                "usage": {"input_tokens": 10, "output_tokens": 1}}}) + "\n")

base = os.environ["OPENAI_BASE_URL"]
body = json.dumps({"model": "mock-model", "messages": [
    {"role": "user", "content": "INTENT: done"}]}).encode()
req = urllib.request.Request(base + "/chat/completions", data=body,
    headers={"Content-Type": "application/json"}, method="POST")
urllib.request.urlopen(req, timeout=10).read()
"""


@pytest.fixture()
def frozen_run(tmp_path, monkeypatch):
    monkeypatch.setenv("SUPER_SECRET_TOKEN", "leak-me")
    monkeypatch.setenv("FAKE_API_KEY", "sk-test")
    scenario = json.loads((SCENARIO_DIR / "scenario.json").read_text())
    generation = GenerationConfig(
        scenario_id=scenario["scenario_id"],
        core_root=SCENARIO_DIR / "core",
        pool_root=SCENARIO_DIR / "pool",
        target_file=scenario["target_files"][0],
        template_file_tokens=150,
    )
    writer = ManifestWriter(tmp_path / "distractors")
    manifest_path = writer.write(generate_manifest(generation, 1))
    write_lockfile([manifest_path], tmp_path / "distractors" / "manifests.lock")

    upstream = MockModelServer()
    upstream_url = upstream.start()
    freeze = _freeze_config()
    config = RunConfig(
        scenario_dir=SCENARIO_DIR,
        distractors_dir=tmp_path / "distractors",
        reports_dir=tmp_path / "reports",
        work_root=tmp_path / "work",
        arm="command",
        agent_command=["python3", "-c", AGENT_SCRIPT],
        upstream_base_url=upstream_url,
        freeze=freeze,
        registered_env_fingerprint=freeze.fingerprint(),
        timeout_seconds=60,
    )
    yield ExperimentRunner(config), freeze, tmp_path
    upstream.stop()


def test_command_arm_runs_frozen(frozen_run):
    runner, freeze, tmp_path = frozen_run
    result = runner.run_trial(1, 0)
    record = result.record

    # The in-agent assertions passed (the request reached the proxy).
    assert record["iterations_total"] == 1
    assert record["input_tokens_per_run"] > 0
    # Freeze facts are in the record.
    assert record["env_fingerprint_sha256"] == freeze.fingerprint()
    assert record["cli_version"] == FAKE_VERSION
    # Ephemerality: the home is gone, its artifacts archived.
    assert not (result.report_dir / "codex_home").exists()
    archived = json.loads(
        (result.report_dir / "codex_home_manifest.json").read_text()
    )
    assert "sessions/rollout.jsonl" in archived["archived"]
    # The agent never read or edited the target.
    assert not record["hidden_pass"]
    assert record["failure_class"] == "localization_miss"


def test_registered_fingerprint_mismatch_aborts_before_agent(frozen_run):
    runner, freeze, tmp_path = frozen_run
    runner.config.registered_env_fingerprint = "0" * 64
    with pytest.raises(FreezeViolation, match="fingerprint mismatch"):
        runner.run_trial(1, 0)
