"""Credential-free execution of checker-owned packaged lifecycle scenarios."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

from .certificate import LifecycleResult
from .isolation import SECRET_ENV_MARKERS
from .scenario_contract import REQUIRED_SCENARIOS


def _isolated_lifecycle_environment(home: Path) -> dict[str, str]:
    """Build a credential-free environment with no source import overrides."""
    environment = {
        key: value
        for key, value in os.environ.items()
        if not any(marker in key.upper() for marker in SECRET_ENV_MARKERS)
        and key not in {"PYTHONPATH", "PYTHONHOME", "PDD_PATH"}
    }
    environment["HOME"] = str(home)
    environment["XDG_CONFIG_HOME"] = str(home / ".config")
    environment["XDG_CACHE_HOME"] = str(home / ".cache")
    environment["PYTHONNOUSERSITE"] = "1"
    return environment


def _failed_result(*, timeout: bool = False) -> LifecycleResult:
    return LifecycleResult(
        len(REQUIRED_SCENARIOS),
        0,
        0,
        int(timeout),
        1,
        1,
        tuple(sorted(REQUIRED_SCENARIOS)),
        "",
    )


def _normalized_results(payload: Any) -> dict[str, dict[str, Any]]:
    if not isinstance(payload, dict) or payload.get("schema_version") != 1:
        raise ValueError("released lifecycle result schema is invalid")
    rows = payload.get("results")
    if not isinstance(rows, list):
        raise ValueError("released lifecycle results are absent")
    results: dict[str, dict[str, Any]] = {}
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("released lifecycle result is malformed")
        scenario_id = row.get("scenario_id")
        status = row.get("status")
        if (
            not isinstance(scenario_id, str)
            or scenario_id in results
            or status not in {"PASS", "FAIL", "MISSING"}
        ):
            raise ValueError("released lifecycle result identity is invalid")
        for metric in (
            "required_tests_skipped_or_xfailed",
            "collection_errors",
            "timeouts",
            "post_repair_second_run_writes",
            "post_merge_tree_changes",
        ):
            value = row.get(metric)
            if not isinstance(value, int) or isinstance(value, bool) or value < 0:
                raise ValueError("released lifecycle metric is invalid")
        results[scenario_id] = row
    if set(results) != set(REQUIRED_SCENARIOS):
        raise ValueError("released lifecycle scenario set is incomplete")
    return results


def _install_candidate_wheel(temporary: Path, home: Path, wheel: Path) -> Path | None:
    """Install the exact candidate wheel in a separate isolated environment."""
    environment = temporary / "candidate-venv"
    isolated = _isolated_lifecycle_environment(home)
    created = subprocess.run(
        [sys.executable, "-m", "venv", str(environment)],
        capture_output=True,
        text=True,
        check=False,
        env=isolated,
    )
    candidate_python = environment / (
        "Scripts/python.exe" if os.name == "nt" else "bin/python"
    )
    if created.returncode != 0:
        return None
    installed = subprocess.run(
        [
            str(candidate_python),
            "-m",
            "pip",
            "install",
            "--only-binary=:all:",
            "--disable-pip-version-check",
            "--force-reinstall",
            str(wheel.resolve()),
        ],
        capture_output=True,
        text=True,
        check=False,
        env=isolated,
    )
    return candidate_python if installed.returncode == 0 else None


def run_lifecycle_matrix(
    root: Path,
    *,
    candidate_wheel: Path | None = None,
    cloud_root: Path | None = None,
    cloud_base_ref: str | None = None,
    cloud_head_ref: str | None = None,
    timeout_seconds: int = 1200,
) -> LifecycleResult:
    # pylint: disable=too-many-arguments
    """Run only the scenario harness installed with the released checker."""
    del root  # Candidate repository tests are never lifecycle evidence.
    if (
        candidate_wheel is None
        or not Path(candidate_wheel).is_file()
        or cloud_root is None
        or cloud_base_ref is None
        or cloud_head_ref is None
    ):
        return _failed_result()
    with tempfile.TemporaryDirectory(prefix="pdd-released-lifecycle-") as directory:
        temporary = Path(directory)
        output = temporary / "result.json"
        (temporary / "home").mkdir(mode=0o700)
        candidate_python = _install_candidate_wheel(
            temporary, temporary / "home", Path(candidate_wheel)
        )
        if candidate_python is None:
            return _failed_result()
        command = [
            sys.executable,
            "-I",
            "-m",
            "pdd.sync_core.scenario_harness",
            "--output",
            str(output),
            "--cloud-root",
            str(Path(cloud_root).resolve()),
            "--cloud-base-ref",
            cloud_base_ref,
            "--cloud-head-ref",
            cloud_head_ref,
            "--candidate-python",
            str(candidate_python),
        ]
        try:
            completed = subprocess.run(
                command,
                capture_output=True,
                text=True,
                check=False,
                timeout=timeout_seconds,
                env=_isolated_lifecycle_environment(temporary / "home"),
            )
        except subprocess.TimeoutExpired:
            return _failed_result(timeout=True)
        try:
            results = _normalized_results(json.loads(output.read_text(encoding="utf-8")))
        except (OSError, ValueError, json.JSONDecodeError):
            return _failed_result()
        missing = tuple(
            sorted(
                scenario_id
                for scenario_id, row in results.items()
                if row["status"] == "MISSING"
            )
        )
        failures = sum(row["status"] != "PASS" for row in results.values())
        if completed.returncode != 0 and failures == 0:
            failures = 1
        return LifecycleResult(
            failures,
            sum(
                int(row["required_tests_skipped_or_xfailed"])
                for row in results.values()
            ),
            sum(int(row["collection_errors"]) for row in results.values()),
            sum(int(row["timeouts"]) for row in results.values()),
            sum(
                int(row["post_repair_second_run_writes"])
                for row in results.values()
            ),
            sum(int(row["post_merge_tree_changes"]) for row in results.values()),
            missing,
            hashlib.sha256(Path(candidate_wheel).read_bytes()).hexdigest(),
        )
