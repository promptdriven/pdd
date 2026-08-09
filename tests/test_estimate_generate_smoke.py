"""Subprocess-level smoke test for generate-only estimate mode.

This exercises the real CLI entrypoint (`python -m pdd --estimate-json generate`)
end to end in a separate process, rather than via Click's in-process test runner,
to prove the externally observable contract reviewers care about:

* stdout is a single, valid JSON object (no log lines or banner text leak into it,
  so downstream automation can `json.loads` it directly);
* the provider is never called (`provider_call_made` is False);
* no command output file is written (estimate mode is side-effect free);
* no `--output-cost` CSV row is appended.

It also locks in the decision on import-time logging: estimate mode keeps stdout
JSON-only, so any incidental import-time info logs must not contaminate stdout.
"""

import json
import os
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]


def _run_estimate(cwd: Path, args, extra_env=None):
    env = os.environ.copy()
    # Make `python -m pdd` importable when running from a source checkout while
    # still working against an installed package in CI.
    env["PYTHONPATH"] = os.pathsep.join(
        [str(REPO_ROOT), env.get("PYTHONPATH", "")]
    ).rstrip(os.pathsep)
    if extra_env:
        env.update(extra_env)
    return subprocess.run(
        [sys.executable, "-m", "pdd", *args],
        cwd=str(cwd),
        env=env,
        capture_output=True,
        text=True,
    )


def test_estimate_json_generate_subprocess_is_side_effect_free(tmp_path):
    prompt = tmp_path / "example_python.prompt"
    prompt.write_text(
        "Write a Python function add(a, b) that returns a + b.\n",
        encoding="utf-8",
    )
    cost_csv = tmp_path / "cost.csv"

    result = _run_estimate(
        tmp_path,
        [
            "--output-cost",
            str(cost_csv),
            "--estimate-json",
            "generate",
            str(prompt),
        ],
    )

    assert result.returncode == 0, (
        f"non-zero exit; stdout={result.stdout!r} stderr={result.stderr!r}"
    )

    # stdout must be exactly one JSON object, with nothing else mixed in.
    payload = json.loads(result.stdout)
    assert payload["estimate"] is True
    assert payload["input_tokens"] > 0
    records = payload["records"]
    assert records, "estimate payload carried no per-call records"
    assert all(rec.get("provider_call_made") is False for rec in records)

    # No provider was called and no command output / cost artifacts were written.
    assert not cost_csv.exists(), "estimate mode must not append cost CSV rows"
    produced = {p.name for p in tmp_path.iterdir()} - {prompt.name}
    py_outputs = [name for name in produced if name.endswith(".py")]
    assert not py_outputs, f"estimate mode wrote command output files: {py_outputs}"

    # stdout stays JSON-only: no traceback leaked through the process boundary.
    assert "Traceback" not in result.stderr
