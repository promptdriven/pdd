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
["codex", "exec", "--cd", "{workdir}", "..."]`` and ``"upstream_base_url"``;
the runner injects ``OPENAI_BASE_URL`` pointing at the recording proxy.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .report import generate_report, load_run_records
from .runner import ExperimentRunner, RunConfig


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, type=Path)
    args = parser.parse_args(argv)

    config_data = json.loads(args.config.read_text(encoding="utf-8"))
    sizes = config_data.pop("sizes", [1])
    trials = config_data.pop("trials", 1)
    run_config = RunConfig(**config_data)
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
