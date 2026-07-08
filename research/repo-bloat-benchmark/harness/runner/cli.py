"""Run a whole experiment from a JSON config.

Example (from ``research/repo-bloat-benchmark/``)::

    python3 -m harness.runner.cli --config experiment.json

with ``experiment.json``::

    {
      "scenario_dir": "scenarios/example-pagination",
      "distractors_dir": "distractors/example-pagination",
      "reports_dir": "reports/example-pagination",
      "work_root": "/tmp/repo-bloat-work",
      "arm": "mock",
      "mock_behavior": "oracle",
      "sizes": [1, 2, 5],
      "trials": 3
    }

For a real agent arm set ``"arm": "command"`` plus ``"agent_command":
["codex", "exec", "--cd", "{workdir}", "..."]``, ``"upstream_base_url"``,
``"freeze"`` (a ``FreezeConfig`` JSON object), and
``"registered_env_fingerprint"``; the runner injects ``OPENAI_BASE_URL``
pointing at the recording proxy.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .env_freeze import FreezeConfig
from .report import generate_report, load_run_records
from .runner import ExperimentRunner, RunConfig


def load_experiment_config(path: Path) -> tuple[RunConfig, list[int], int]:
    """Load JSON config and coerce nested dataclass fields."""
    import os

    config_data = json.loads(path.read_text(encoding="utf-8"))
    sizes = config_data.pop("sizes", [1])
    trials = config_data.pop("trials", 1)
    if isinstance(config_data.get("freeze"), dict):
        config_data["freeze"] = FreezeConfig(**config_data["freeze"])
    # Container hard tier sets RB_PROXY_HOST=0.0.0.0 so the isolated agent can
    # reach the recording proxy; an explicit config value still wins.
    if "proxy_host" not in config_data and os.environ.get("RB_PROXY_HOST"):
        config_data["proxy_host"] = os.environ["RB_PROXY_HOST"]
    if (
        "proxy_advertised_host" not in config_data
        and os.environ.get("RB_PROXY_ADVERTISED_HOST")
    ):
        config_data["proxy_advertised_host"] = os.environ["RB_PROXY_ADVERTISED_HOST"]
    if "agent_launcher" not in config_data and os.environ.get("RB_AGENT_LAUNCHER"):
        config_data["agent_launcher"] = os.environ["RB_AGENT_LAUNCHER"]
    if "agent_request_dir" not in config_data and os.environ.get("RB_AGENT_REQUEST_DIR"):
        config_data["agent_request_dir"] = os.environ["RB_AGENT_REQUEST_DIR"]
    return RunConfig(**config_data), sizes, trials


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, type=Path)
    args = parser.parse_args(argv)

    run_config, sizes, trials = load_experiment_config(args.config)
    runner = ExperimentRunner(run_config)

    for size in sizes:
        for result in runner.run_cell(size, trials):
            record = result.record
            print(
                f"{record['run_id']}: hidden={'PASS' if record['hidden_pass'] else 'fail'} "
                f"tokens={record['input_tokens_per_run']} "
                f"shape={record['growth_shape']} "
                f"failure={record['failure_class']}"
            )

    records_path = run_config.reports_dir / "run_records.jsonl"
    report = generate_report(load_run_records(records_path))
    report_path = run_config.reports_dir / "report.md"
    report_path.write_text(report, encoding="utf-8")
    print(f"report: {report_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
