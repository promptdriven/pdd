"""Zero-billing integration check for the isolated command-arm path."""

from __future__ import annotations

import json
from pathlib import Path

from harness.distractors.generator import GenerationConfig, generate_manifest
from harness.distractors.manifest import ManifestWriter, write_lockfile
from harness.runner.env_freeze import FreezeConfig
from harness.runner.mock_agent import MockModelServer
from harness.runner.runner import ExperimentRunner, RunConfig

BENCH_ROOT = Path(__file__).resolve().parents[3]
SCENARIO_DIR = BENCH_ROOT / "scenarios" / "example-pagination"
REPORTS_ROOT = Path("/bench/reports/container-integration")
REQUEST_ROOT = Path("/bench/agent-requests")

AGENT_SCRIPT = r"""
import json, os, socket, sys, urllib.request
from pathlib import Path
from urllib.parse import urlparse

sys.path.insert(0, "/bench")
from harness.runner.container import egress_check

home = Path(os.environ["CODEX_HOME"])
assert home.joinpath("config.toml").is_file(), "frozen CODEX_HOME missing"
assert os.environ["HOME"] == os.environ["CODEX_HOME"], "HOME not redirected"
base = os.environ["OPENAI_BASE_URL"]
parsed = urlparse(base)
assert parsed.hostname == "runner", f"unexpected proxy host: {parsed.hostname}"
agent_checks = egress_check.agent_checks(proxy_url=base)
(home / "agent_egress_check.json").write_text(
    json.dumps({"role": "agent", "checks": agent_checks}, indent=2) + "\n",
    encoding="utf-8",
)
assert all(agent_checks.values()), agent_checks
try:
    socket.create_connection(("gateway", 8888), timeout=1)
    raise AssertionError("gateway should be unreachable from agent")
except OSError:
    pass
(home / "sessions").mkdir(exist_ok=True)
(home / "sessions" / "integration.jsonl").write_text("{}\n", encoding="utf-8")
body = json.dumps({"model": "mock-model", "messages": [{"role": "user", "content": "ping"}]}).encode()
request = urllib.request.Request(
    base + "/chat/completions",
    data=body,
    headers={"Content-Type": "application/json"},
    method="POST",
)
urllib.request.urlopen(request, timeout=10).read()
"""


def _prepare_distractors() -> Path:
    scenario = json.loads((SCENARIO_DIR / "scenario.json").read_text(encoding="utf-8"))
    generation = GenerationConfig(
        scenario_id=scenario["scenario_id"],
        core_root=SCENARIO_DIR / "core",
        pool_root=SCENARIO_DIR / "pool",
        target_file=scenario["target_files"][0],
        template_file_tokens=150,
    )
    distractors_dir = REPORTS_ROOT / "distractors"
    writer = ManifestWriter(distractors_dir)
    manifest_path = writer.write(generate_manifest(generation, 1))
    write_lockfile([manifest_path], distractors_dir / "manifests.lock")
    return distractors_dir


def main(argv: list[str] | None = None) -> int:
    REPORTS_ROOT.mkdir(parents=True, exist_ok=True)
    REQUEST_ROOT.mkdir(parents=True, exist_ok=True)
    distractors_dir = _prepare_distractors()
    upstream = MockModelServer()
    upstream_url = upstream.start()
    try:
        freeze = FreezeConfig(
            pinned_cli_version="codex-cli integration-check",
            cli_version_command=["python3", "-c", "print('codex-cli integration-check')"],
            model_id="mock-model",
        )
        config = RunConfig(
            scenario_dir=SCENARIO_DIR,
            distractors_dir=distractors_dir,
            reports_dir=REPORTS_ROOT / "reports",
            work_root=REPORTS_ROOT / "work",
            arm="command",
            agent_command=["python3", "-c", AGENT_SCRIPT],
            upstream_base_url=upstream_url,
            freeze=freeze,
            registered_env_fingerprint=freeze.fingerprint(),
            proxy_host="0.0.0.0",
            proxy_advertised_host="runner",
            agent_launcher="container_worker",
            agent_request_dir=REQUEST_ROOT,
            timeout_seconds=60,
        )
        result = ExperimentRunner(config).run_trial(1, 0)
    finally:
        upstream.stop()

    process = json.loads(
        (result.report_dir / "agent_process.json").read_text(encoding="utf-8")
    )
    agent_egress_path = (
        result.report_dir / "codex_home_artifacts" / "agent_egress_check.json"
    )
    agent_egress = json.loads(agent_egress_path.read_text(encoding="utf-8"))
    ok = (
        process["launcher"] == "container_worker"
        and process["returncode"] == 0
        and all(agent_egress["checks"].values())
        and result.record["iterations_total"] == 1
        and (
            result.report_dir
            / "codex_home_artifacts"
            / "sessions"
            / "integration.jsonl"
        ).is_file()
    )
    print(
        json.dumps(
            {
                "run_id": result.record["run_id"],
                "agent_egress": agent_egress,
                "ok": ok,
            },
            indent=2,
        )
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
