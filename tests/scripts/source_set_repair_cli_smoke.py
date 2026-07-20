#!/usr/bin/env python3
"""Runnable prompt-target source-set repair smoke transcript for PR #1426.

Exercises the local ``pdd checkup <prompt> --prompt-repair best-effort`` path
with zero lint issues and failing contract/coverage findings.  The initial
checkup uses the real CLI; ``change()`` is mocked so the transcript is
deterministic and does not require LLM credentials.
"""
from __future__ import annotations

import json
import os
import shutil
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parents[2]
_REPO_ROOT_STR = str(REPO_ROOT)
# Always prefer this checkout over any installed ``pdd`` on sys.path.
while _REPO_ROOT_STR in sys.path:
    sys.path.remove(_REPO_ROOT_STR)
sys.path.insert(0, _REPO_ROOT_STR)

from click.testing import CliRunner

FIXTURE = REPO_ROOT / "tests" / "fixtures" / "prompt_lint" / "clean.prompt"


def _run_cli_checkup(prompt: Path, *, repair: bool) -> dict:
    from pdd.commands.checkup import checkup

    args = [str(prompt), "--json"]
    if repair:
        args.extend(["--prompt-repair", "best-effort"])
    result = CliRunner().invoke(
        checkup,
        args,
        obj={"quiet": True, "verbose": False},
        catch_exceptions=False,
    )
    if result.exit_code not in {0, 1}:
        raise RuntimeError(
            f"unexpected exit {result.exit_code}\noutput={result.output}"
        )
    payload = json.loads(result.output)
    return payload


def _summarize_report(payload: dict) -> dict:
    report = payload["reports"][0]
    findings = report.get("findings", [])
    by_check: dict[str, list[str]] = {}
    for finding in findings:
        by_check.setdefault(finding.get("source_check", "?"), []).append(
            finding.get("code", "?")
        )
    lint_check = next(
        (check for check in report.get("checks", []) if check.get("name") == "lint"),
        {},
    )
    return {
        "status": report.get("status"),
        "deterministic_exit_code": payload.get("deterministic_exit_code"),
        "lint_check_status": lint_check.get("status"),
        "finding_counts": {key: len(codes) for key, codes in by_check.items()},
        "contract_codes": by_check.get("contract", [])[:4],
        "coverage_codes": by_check.get("coverage", [])[:4],
    }


def _repaired_text(original: str) -> str:
    return (
        original.replace(
            "1. The function returns an integer exit code of 0 on success, 1 on failure.",
            "1. The function MUST return an integer exit code of 0 on success, 1 on failure.",
        )
        .replace(
            "2. If the input file does not exist, raises FileNotFoundError.",
            "2. If the input file does not exist, the function MUST raise FileNotFoundError.",
        )
        .replace(
            "3. Writes output to the path specified by the --output flag.",
            "3. The function MUST write output to the path specified by the --output flag.",
        )
        .replace(
            "4. Logs the request ID to stdout before processing begins.",
            "4. The function MUST log the request ID to stdout before processing begins.",
        )
    )


def main() -> int:
    from pdd.commands.checkup import checkup

    with tempfile.TemporaryDirectory(prefix="pdd-source-set-smoke-") as tmp:
        prompt = Path(tmp) / "contract_smoke_python.prompt"
        original = FIXTURE.read_text(encoding="utf-8")
        shutil.copy2(FIXTURE, prompt)

        print("=== Source-set repair CLI smoke (PR #1426) ===")
        print(f"fixture: {FIXTURE}")
        print(f"prompt:  {prompt}")
        print()

        print("1) Initial checkup (real CLI, repair off)")
        print(
            "   ",
            " ".join(
                [
                    "python -m pdd.cli checkup",
                    str(prompt),
                    "--json",
                ]
            ),
        )
        initial = _summarize_report(_run_cli_checkup(prompt, repair=False))
        print("   result:", json.dumps(initial, indent=2))
        print()

        before_bytes = prompt.read_bytes()
        repaired = _repaired_text(original)

        print("2) Repair run (CLI path, change() mocked)")
        print(
            "   ",
            " ".join(
                [
                    "python -m pdd.cli checkup",
                    str(prompt),
                    "--prompt-repair",
                    "best-effort",
                ]
            ),
        )
        with patch("pdd.prompt_repair.change", return_value=(repaired, 0.02, "smoke-model")) as mock_change:
            cli_result = CliRunner().invoke(
                checkup,
                [str(prompt), "--prompt-repair", "best-effort"],
                obj={"quiet": True, "verbose": False},
            )
        assert mock_change.called, "change() was not invoked"
        input_code = mock_change.call_args.kwargs.get("input_code", "")
        print("   cli exit_code:", cli_result.exit_code)
        print("   change() called:", mock_change.call_count)
        print('   input_code contains "source_set_report":', "source_set_report" in input_code)
        after_bytes = prompt.read_bytes()
        print("   prompt file changed:", before_bytes != after_bytes)
        print()

        print("3) Final recheck (real CLI, repair off)")
        print(
            "   ",
            " ".join(
                [
                    "python -m pdd.cli checkup",
                    str(prompt),
                    "--json",
                ]
            ),
        )
        final = _summarize_report(_run_cli_checkup(prompt, repair=False))
        print("   result:", json.dumps(final, indent=2))
        print()

        contract_before = initial["finding_counts"].get("contract", 0)
        contract_after = final["finding_counts"].get("contract", 0)
        print("contract findings:", f"{contract_before} -> {contract_after}")
        if initial["lint_check_status"] != "pass":
            print("FAIL: expected zero lint issues in fixture")
            return 1
        if contract_before == 0:
            print("FAIL: expected initial contract findings")
            return 1
        if not (before_bytes != after_bytes):
            print("FAIL: prompt file was not rewritten")
            return 1
        if contract_after >= contract_before:
            print("FAIL: contract findings did not decrease after repair")
            return 1
        print("PASS")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
