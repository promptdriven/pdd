"""First-real-run calibration — GO/NO-GO before any pilot cell (blocker 4).

The routing probe (`codex_probe.py`) verified everything a *scripted*
upstream can verify. Exactly one thing still needs a real provider: that the
account serves the pinned model and streams the same Responses-API event
shapes the probe's fixtures emit. The procedure (the **only** intentionally
billed step before the pilot, ~one request):

1. run ONE trial of `pdd-find-section` at 1x with the registered frozen
   environment (`arm: "command"`, the committed `pilot_arm_codex.json`
   values, `registered_env_fingerprint` from `register_env`);
2. point this tool at that trial's report directory::

       python3 -m harness.runner.first_run_calibration \
           --run-dir reports/<run_id> \
           --arm harness/runner/pilot_arm_codex.json \
           --registration registered_env.json

3. **GO** (exit 0) ⇒ start the pilot. **NO-GO** ⇒ every failed check names
   what diverged; fix (or re-register deliberately) before burning tokens.

This tool itself performs **no network I/O and no billing** — it only reads
artifacts the runner already archived.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path

from harness.context_snapshots.proxy import _analyze_response_body


def _load_snapshots(run_dir: Path) -> list[dict]:
    path = run_dir / "context_snapshots.jsonl"
    if not path.is_file():
        return []
    return [json.loads(line) for line in path.read_text().splitlines() if line.strip()]


def calibrate(run_dir: Path, arm: dict, registered_fingerprint: str | None) -> dict:
    """Return the GO/NO-GO verdict for one archived real run."""
    snapshots = sorted(_load_snapshots(run_dir), key=lambda s: s["ordinal"])
    record_path = run_dir / "run_record.json"
    record = json.loads(record_path.read_text()) if record_path.is_file() else {}
    process_path = run_dir / "agent_process.json"
    process = json.loads(process_path.read_text()) if process_path.is_file() else {}

    responses_analyses = []
    payload_sha_ok = True
    every_snapshot_has_response = bool(snapshots)
    for snap in snapshots:
        payload = run_dir / snap["payload_path"]
        if not payload.is_file() or (
            hashlib.sha256(payload.read_bytes()).hexdigest() != snap["request_sha256"]
        ):
            payload_sha_ok = False
        response = run_dir / snap["response_path"]
        if response.is_file():
            responses_analyses.append(
                _analyze_response_body(response.read_bytes(), "text/event-stream")
            )
        else:
            every_snapshot_has_response = False

    models_seen = {snap.get("model") for snap in snapshots}
    checks = {
        "snapshots_present": bool(snapshots),
        "all_requests_responses_api": bool(snapshots)
        and all(s["endpoint"].endswith("/responses") for s in snapshots),
        "payload_sha256_integrity": payload_sha_ok and bool(snapshots),
        "model_matches_pin": models_seen == {arm["model_id"]},
        "usage_on_every_request": bool(snapshots)
        and all(s.get("input_tokens") is not None for s in snapshots),
        # Every request must have an on-disk response that parses to usage —
        # a snapshot whose response body is missing can no longer be skipped.
        "response_parsed_for_every_request": every_snapshot_has_response
        and len(responses_analyses) == len(snapshots)
        and all(a["input_tokens"] is not None for a in responses_analyses),
        "cli_version_matches_pin": record.get("cli_version")
        == arm["pinned_cli_version"],
        "env_fingerprint_registered": (
            registered_fingerprint is not None
            and record.get("env_fingerprint_sha256") == registered_fingerprint
        ),
        "token_metrics_supported": record.get("token_metrics_supported") is True,
        "not_development_only": record.get("development_only") is False,
        "agent_error_false": record.get("agent_error") is False,
        "agent_process_exit_zero": (
            process.get("timed_out") is False and process.get("returncode") == 0
        ),
    }
    return {
        "run_dir": str(run_dir),
        "requests": len(snapshots),
        "models_seen": sorted(str(m) for m in models_seen),
        "checks": checks,
        "go": all(checks.values()),
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-dir", required=True, type=Path)
    parser.add_argument("--arm", required=True, type=Path,
                        help="committed arm config (pilot_arm_codex.json)")
    parser.add_argument("--registration", type=Path, default=None,
                        help="register_env output (registered_env.json)")
    parser.add_argument("--json", type=Path, default=None)
    args = parser.parse_args(argv)

    arm = json.loads(args.arm.read_text(encoding="utf-8"))
    arm.pop("_comment", None)
    registered = None
    if args.registration:
        reg = json.loads(args.registration.read_text())
        # Only a binary-verified registration (register_env with the pinned
        # CLI installed) is accepted; a development-only record carries no
        # `registered_env_fingerprint` key and yields NO-GO.
        if reg.get("valid_for_runs") is True:
            registered = reg.get("registered_env_fingerprint")
    verdict = calibrate(args.run_dir, arm, registered)
    if args.json:
        args.json.write_text(json.dumps(verdict, indent=2) + "\n", encoding="utf-8")
    for name, passed in verdict["checks"].items():
        print(f"  {'PASS' if passed else 'FAIL'}  {name}")
    print("GO — start the pilot" if verdict["go"]
          else "NO-GO — resolve the failed checks before any pilot cell")
    return 0 if verdict["go"] else 1


if __name__ == "__main__":
    sys.exit(main())
