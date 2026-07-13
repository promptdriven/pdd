#!/usr/bin/env python3
"""Reproducible zero-provider orchestration comparison for pdd issue #2026."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import socket
import subprocess
import sys
import time
from pathlib import Path


ISSUE_URL = "https://github.com/e2e-org/greeter-proj/issues/7"
MANIFEST = ["textutil", "greeter"]
SCHEDULE = ["regular", "agentic", "agentic", "regular", "regular", "agentic"]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def run(cmd: list[str], *, cwd: Path, env: dict[str, str]) -> dict[str, object]:
    started = time.monotonic_ns()
    result = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=420)
    elapsed = (time.monotonic_ns() - started) / 1_000_000_000
    return {
        "command": cmd,
        "returncode": result.returncode,
        "elapsed_seconds": round(elapsed, 6),
        "stdout": result.stdout,
        "stderr": result.stderr,
    }


def git(project: Path, env: dict[str, str], *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=project, env=env, check=True,
        capture_output=True, text=True, timeout=60,
    )
    return result.stdout.strip()


def load_harness_module(checkout: Path):
    test_file = checkout / "tests" / "test_agentic_sync_mocked_e2e.py"
    spec = importlib.util.spec_from_file_location("fixture7_harness", test_file)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"cannot load {test_file}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module, test_file


def make_harness(module, root: Path):
    root.mkdir(parents=True)
    harness = module.harness.__wrapped__(root)
    fixed_env = {
        **harness.git_env,
        "GIT_AUTHOR_DATE": "2000-01-01T00:00:00Z",
        "GIT_COMMITTER_DATE": "2000-01-01T00:00:00Z",
    }
    subprocess.run(
        ["git", "commit", "--amend", "--no-edit", "--date=2000-01-01T00:00:00Z"],
        cwd=harness.project, env=fixed_env, check=True,
        capture_output=True, text=True, timeout=60,
    )
    subprocess.run(
        ["git", "branch", "-f", "main", "HEAD"],
        cwd=harness.project, env=fixed_env, check=True,
        capture_output=True, text=True, timeout=60,
    )
    return harness


def read_optional(path: Path) -> str:
    return path.read_text() if path.exists() else ""


def generated_files(project: Path) -> list[dict[str, str]]:
    root = project / ".pdd"
    if not root.exists():
        return []
    return [
        {"path": str(path.relative_to(project)), "sha256": sha256(path)}
        for path in sorted(root.rglob("*"))
        if path.is_file()
    ]


def snapshot(harness, test_file: Path) -> dict[str, object]:
    project = harness.project
    files = [
        project / ".pddrc",
        project / "architecture.json",
        project / "prompts" / "textutil_python.prompt",
        project / "prompts" / "greeter_python.prompt",
    ]
    return {
        "fixture_harness_sha256": sha256(test_file),
        "files": {str(path.relative_to(project)): sha256(path) for path in files},
        "commit": git(project, harness.git_env, "rev-parse", "HEAD"),
        "tree": git(project, harness.git_env, "rev-parse", "HEAD^{tree}"),
        "status": git(project, harness.git_env, "status", "--porcelain=v1"),
        "generated_files": generated_files(project),
    }


def isolation_probe() -> dict[str, object]:
    attempts = []
    for label, address in (
        ("external_tcp", ("1.1.1.1", 443)),
        ("loopback_tcp", ("127.0.0.1", 9)),
    ):
        sock = socket.socket()
        sock.settimeout(2)
        try:
            sock.connect(address)
        except OSError as exc:
            attempts.append({"name": label, "blocked": True, "error": repr(exc)})
        else:
            attempts.append({"name": label, "blocked": False, "error": None})
        finally:
            sock.close()
    return {"attempts": attempts, "all_blocked": all(item["blocked"] for item in attempts)}


def planning_run(checkout: Path, module, test_file: Path, output: Path) -> dict[str, object]:
    harness = make_harness(module, output / "sandbox")
    prompt = harness.project / "prompts" / "greeter_python.prompt"
    prompt.write_text(prompt.read_text() + "# friendlier greeting\n")
    commit_env = {
        **harness.git_env,
        "GIT_AUTHOR_DATE": "2000-01-02T00:00:00Z",
        "GIT_COMMITTER_DATE": "2000-01-02T00:00:00Z",
    }
    subprocess.run(
        ["git", "commit", "-qam", "tweak greeter prompt"],
        cwd=harness.project, env=commit_env, check=True, timeout=60,
    )
    before = snapshot(harness, test_file)
    result = run(
        [sys.executable, "-m", "pdd", "--force", "--local", "sync", ISSUE_URL,
         "--no-steer", "--dry-run", "--no-github-state"],
        cwd=harness.project, env=harness.env,
    )
    logs = {
        name: read_optional(harness.log_dir / name)
        for name in ("pdd_calls.log", "claude_calls.log", "gh_calls.log", "gh_writes.log", "TRIPWIRE.log")
    }
    after = snapshot(harness, test_file)
    diff = git(harness.project, harness.git_env, "diff", "--binary", "HEAD")
    record = {
        "checkout": str(checkout),
        "checkout_commit": subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=checkout, check=True,
            capture_output=True, text=True,
        ).stdout.strip(),
        "before": before,
        "result": result,
        "after": after,
        "worktree_diff": diff,
        "logs": logs,
    }
    (output / "result.json").write_text(json.dumps(record, indent=2, sort_keys=True))
    return record


def execution_arm(checkout: Path, module, test_file: Path, output: Path, mode: str) -> dict[str, object]:
    harness = make_harness(module, output / "sandbox")
    before = snapshot(harness, test_file)
    commands = []
    for basename in MANIFEST:
        cmd = [sys.executable, "-m", "pdd", "--force", "--local", "sync", basename, "--dry-run"]
        if mode == "agentic":
            cmd.append("--agentic")
        cmd.append("--no-steer")
        commands.append(run(cmd, cwd=harness.project, env=harness.env))
    after = snapshot(harness, test_file)
    diff = git(harness.project, harness.git_env, "diff", "--binary", "HEAD")
    logs = {
        name: read_optional(harness.log_dir / name)
        for name in ("pdd_calls.log", "claude_calls.log", "gh_calls.log", "gh_writes.log", "TRIPWIRE.log")
    }
    record = {
        "mode": mode,
        "manifest": MANIFEST,
        "checkout": str(checkout),
        "before": before,
        "commands": commands,
        "after": after,
        "worktree_diff": diff,
        "logs": logs,
    }
    (output / "result.json").write_text(json.dumps(record, indent=2, sort_keys=True))
    return record


def validate(records: list[dict[str, object]], planning: dict[str, object], probe: dict[str, object]) -> None:
    if not probe["all_blocked"]:
        raise AssertionError("OS network sandbox probe unexpectedly succeeded")
    expected_tree = records[0]["before"]["tree"]
    expected_files = records[0]["before"]["files"]
    for record in records:
        assert record["before"]["status"] == ""
        assert record["before"]["tree"] == expected_tree
        assert record["before"]["files"] == expected_files
        assert record["after"]["tree"] == expected_tree
        assert record["after"]["files"] == expected_files
        assert record["after"]["status"] == "?? .pdd/"
        assert len(record["after"]["generated_files"]) == len(MANIFEST)
        assert all(
            item["path"].startswith(".pdd/core_dumps/pdd-core-")
            and item["path"].endswith(".json")
            for item in record["after"]["generated_files"]
        )
        assert record["worktree_diff"] == ""
        assert all(command["returncode"] == 0 for command in record["commands"])
        assert record["logs"]["claude_calls.log"] == ""
        assert record["logs"]["gh_writes.log"] == ""
        assert record["logs"]["TRIPWIRE.log"] == ""
    assert planning["result"]["returncode"] == 0
    assert "greeter" in planning["result"]["stdout"]
    assert "textutil" in planning["result"]["stdout"]
    assert "adding them to the sync scope" in planning["result"]["stdout"]
    assert planning["logs"]["claude_calls.log"] == ""
    assert planning["logs"]["gh_writes.log"] == ""
    assert planning["logs"]["TRIPWIRE.log"] == ""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--checkout", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--planning-only", action="store_true")
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    module, test_file = load_harness_module(checkout)
    probe = isolation_probe()
    planning_dir = output / "planning-agentic-issue"
    planning_dir.mkdir()
    planning = planning_run(checkout, module, test_file, planning_dir)
    records = []
    if not args.planning_only:
        for index, mode in enumerate(SCHEDULE, start=1):
            arm_dir = output / f"execution-{index:02d}-{mode}"
            arm_dir.mkdir()
            records.append(execution_arm(checkout, module, test_file, arm_dir, mode))
        validate(records, planning, probe)
    else:
        assert probe["all_blocked"]
        assert planning["result"]["returncode"] == 0
        assert planning["logs"]["claude_calls.log"] == ""
        assert planning["logs"]["gh_writes.log"] == ""
        assert planning["logs"]["TRIPWIRE.log"] == ""
    summary = {
        "schema": 1,
        "issue": 2026,
        "fixture_issue": ISSUE_URL,
        "candidate_commit": planning["checkout_commit"],
        "network_isolation": probe,
        "planning_result": str((planning_dir / "result.json").relative_to(output)),
        "execution_schedule": [] if args.planning_only else SCHEDULE,
        "manifest": MANIFEST,
        "execution_results": [
            str((output / f"execution-{index:02d}-{mode}" / "result.json").relative_to(output))
            for index, mode in enumerate(SCHEDULE, start=1)
        ] if not args.planning_only else [],
        "validation": "passed",
    }
    (output / "summary.json").write_text(json.dumps(summary, indent=2, sort_keys=True))
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
