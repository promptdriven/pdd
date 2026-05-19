"""Tests for ``pdd.checkup_gates`` deterministic gate discovery + execution.

The gate module exists so ``pdd checkup --pr --review-loop`` cannot ship a
clean LLM verdict on top of a worktree that fails a fast, deterministic
local check (e.g. ``prettier --check``). The tests below pin every gate
the v1 discovery set is supposed to emit, and pin the runner-side
contract (timeout handling, output truncation, secret scrubbing,
artifact persistence).
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Dict, List
from unittest.mock import patch


def _make_pkg_json(scripts: Dict[str, str]) -> str:
    return json.dumps({"name": "fake", "version": "0.0.0", "scripts": scripts})


def _git_init(worktree: Path) -> None:
    """Initialize a minimal git repo so ``git diff --check`` has something to scan."""
    subprocess.run(["git", "init", "-q"], cwd=worktree, check=True)
    subprocess.run(
        ["git", "-c", "user.name=t", "-c", "user.email=t@x", "commit",
         "--allow-empty", "-m", "init", "-q"],
        cwd=worktree,
        check=True,
    )


class TestDiscoverGates:
    """``discover_gates`` inspects repo config and emits an allowlisted gate set."""

    def test_emits_git_diff_check_always(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "git-diff-check" in names

    def test_finds_prettier_check_from_package_json(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:format:check" in names
        gate = next(g for g in gates if g.name == "npm:format:check")
        assert gate.cmd[0] in {"npm", "yarn", "pnpm", "bun"}
        assert "format:check" in gate.cmd

    def test_skips_non_check_scripts(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format": "prettier --write ."}),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:format" not in names

    def test_skips_install_or_deploy_scripts(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json(
                {
                    "preinstall": "npm install foo",
                    "deploy": "firebase deploy",
                    "start": "node server.js",
                    "build": "tsc -p .",
                    "publish": "npm publish",
                    "push": "git push",
                }
            ),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        for forbidden in (
            "npm:preinstall",
            "npm:deploy",
            "npm:start",
            "npm:build",
            "npm:publish",
            "npm:push",
        ):
            assert forbidden not in names

    def test_skips_eslint_without_no_fix_flag(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"lint:check": "eslint --fix ."}),
            encoding="utf-8",
        )
        gates = discover_gates(tmp_path, changed_files=())
        names = [g.name for g in gates]
        assert "npm:lint:check" not in names

    def test_emits_py_compile_for_changed_python_files(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = [g.name for g in gates]
        assert "py-compile:a.py" in names
        gate = next(g for g in gates if g.name == "py-compile:a.py")
        assert gate.cmd[:3] == [sys.executable, "-m", "py_compile"]
        assert gate.cmd[-1].endswith("a.py")

    def test_skips_py_compile_when_no_python_files_changed(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        gates = discover_gates(tmp_path, changed_files=("readme.md",))
        names = [g.name for g in gates]
        assert not any(n.startswith("py-compile:") for n in names)

    def test_skips_ruff_when_no_pyproject_config(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = [g.name for g in gates]
        assert "ruff" not in names

    def test_emits_ruff_when_configured_and_binary_present(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        with patch("pdd.checkup_gates.shutil.which", return_value="/usr/bin/ruff"):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = [g.name for g in gates]
        assert "ruff" in names

    def test_skips_ruff_when_configured_but_binary_missing(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        (tmp_path / "pyproject.toml").write_text(
            "[tool.ruff]\nline-length = 100\n", encoding="utf-8"
        )
        with patch("pdd.checkup_gates.shutil.which", return_value=None):
            gates = discover_gates(tmp_path, changed_files=("a.py",))
        names = [g.name for g in gates]
        assert "ruff" not in names

    def test_user_extra_allow_is_honored(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        gates = discover_gates(
            tmp_path, changed_files=(), extra_allow=("git-diff-check",)
        )
        names = [g.name for g in gates]
        assert "git-diff-check" in names

    def test_gates_use_list_form_no_shell(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import discover_gates

        _git_init(tmp_path)
        (tmp_path / "package.json").write_text(
            _make_pkg_json({"format:check": "prettier --check ."}),
            encoding="utf-8",
        )
        (tmp_path / "a.py").write_text("x = 1\n", encoding="utf-8")
        gates = discover_gates(tmp_path, changed_files=("a.py",))
        for gate in gates:
            assert isinstance(gate.cmd, list)
            for token in gate.cmd:
                assert isinstance(token, str)


class TestRunGates:
    """``run_gates`` executes each discovered gate and persists artifacts."""

    def test_records_exit_code_and_persists_artifact(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        gates = [
            Gate(
                name="echo-ok",
                cmd=[sys.executable, "-c", "import sys; sys.exit(0)"],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert len(results) == 1
        assert results[0].exit_code == 0
        manifest = artifacts_dir / "round-1-review-gates.json"
        assert manifest.exists()
        payload = json.loads(manifest.read_text(encoding="utf-8"))
        assert payload[0]["exit_code"] == 0
        assert payload[0]["gate"]["name"] == "echo-ok"
        per_gate = artifacts_dir / "round-1-review-gate-echo-ok.txt"
        assert per_gate.exists()

    def test_failure_exit_code_recorded(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        gates = [
            Gate(
                name="echo-fail",
                cmd=[sys.executable, "-c", "import sys; sys.exit(7)"],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert results[0].exit_code == 7

    def test_truncates_oversize_output(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # Emit ~200KB of stdout; the runner truncates to ~10KB.
        script = (
            "import sys; sys.stdout.write('A' * 200000); sys.exit(1)"
        )
        gates = [
            Gate(
                name="bigout",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        # ~10KB cap, generously bound to allow a small marker like "[truncated]".
        assert len(results[0].stdout_excerpt) <= 12000
        assert results[0].stdout_excerpt  # not empty

    def test_handles_timeout(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # Long sleep with a 0.1s timeout: runner must record exit_code=None
        # plus a non-empty error rather than block the loop.
        script = "import time; time.sleep(60)"
        gates = [
            Gate(
                name="hang",
                cmd=[sys.executable, "-c", script],
                source="<test>",
                timeout=0.1,
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert results[0].exit_code is None
        lowered = results[0].error.lower()
        assert "timeout" in lowered or "timed out" in lowered

    def test_handles_missing_binary(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        gates = [
            Gate(
                name="ghost",
                cmd=["this-binary-does-not-exist-xyz-1092"],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert results[0].exit_code is None
        assert results[0].error  # non-empty

    def test_scrubs_secrets_in_excerpts(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # Use ``Authorization: Bearer …`` which the existing scrubber regex
        # recognises, so the runner must consult the loop's scrubber before
        # persisting the excerpt.
        script = (
            "import sys; "
            "sys.stderr.write('error: Authorization: Bearer sk-abcdefghijklmnopqr\\n'); "
            "sys.exit(1)"
        )
        gates = [
            Gate(
                name="leakage",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert "[REDACTED]" in results[0].stderr_excerpt
        assert "sk-abcdefghijklmnopqr" not in results[0].stderr_excerpt
        assert "sk-abcdefghijklmnopqr" not in results[0].stdout_excerpt

    def test_runs_with_ci_env_and_no_color(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # The runner must inject CI=1, NO_COLOR=1, FORCE_COLOR=0 so deterministic
        # gates emit non-interactive output. Probe via a dump-env gate.
        script = (
            "import os, sys; "
            "sys.stdout.write("
            "f\"CI={os.environ.get('CI')}|"
            "NO_COLOR={os.environ.get('NO_COLOR')}|"
            "FORCE_COLOR={os.environ.get('FORCE_COLOR')}\""
            "); sys.exit(0)"
        )
        gates = [
            Gate(
                name="env-probe",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert "CI=1" in results[0].stdout_excerpt
        assert "NO_COLOR=1" in results[0].stdout_excerpt
        assert "FORCE_COLOR=0" in results[0].stdout_excerpt

    def test_strips_pdd_env_so_gate_does_not_inherit_loop_state(
        self, tmp_path: Path, monkeypatch: Any
    ) -> None:
        from pdd.checkup_gates import Gate, run_gates

        # Set a PDD_* env that must NOT leak into the gate process.
        monkeypatch.setenv("PDD_FAKE_SECRET", "must-not-appear")
        script = (
            "import os, sys; "
            "sys.stdout.write(os.environ.get('PDD_FAKE_SECRET', '<unset>')); "
            "sys.exit(0)"
        )
        gates = [
            Gate(
                name="pdd-env-probe",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        assert results[0].stdout_excerpt.strip() == "<unset>"

    def test_uses_worktree_as_cwd(self, tmp_path: Path) -> None:
        from pdd.checkup_gates import Gate, run_gates

        script = "import os, sys; sys.stdout.write(os.getcwd()); sys.exit(0)"
        gates = [
            Gate(
                name="cwd-probe",
                cmd=[sys.executable, "-c", script],
                source="<test>",
            )
        ]
        artifacts_dir = tmp_path / "artifacts"
        results = run_gates(
            tmp_path, gates, artifacts_dir=artifacts_dir, round_number=1, mode="review"
        )
        # tmp_path may be a symlink on macOS; resolve both sides for comparison.
        emitted = Path(results[0].stdout_excerpt.strip()).resolve()
        assert emitted == tmp_path.resolve()


class TestGateResultsToFindings:
    """``gate_results_to_findings`` converts failing gates to ``ReviewFinding``."""

    def test_failed_gate_becomes_blocker_finding(self) -> None:
        from pdd.checkup_gates import Gate, GateResult, gate_results_to_findings

        gate = Gate(
            name="prettier-check",
            cmd=["prettier", "--check", "."],
            source="package.json:scripts.format:check",
            required_fix_hint="Run prettier --write . locally and commit.",
        )
        result = GateResult(
            gate=gate,
            exit_code=1,
            stdout_excerpt="Code style issues found in 2 files.",
            stderr_excerpt="",
            duration_seconds=0.5,
            started_at_iso="2025-01-01T00:00:00Z",
        )
        findings = gate_results_to_findings([result], round_number=2)
        assert len(findings) == 1
        finding = findings[0]
        assert finding.severity == "blocker"
        assert finding.reviewer == "gate:prettier-check"
        assert finding.area == "deterministic-gate"
        assert (
            "prettier --check" in finding.required_fix.lower()
            or "prettier --write" in finding.required_fix.lower()
        )
        evidence_lower = finding.evidence.lower()
        assert "exit code 1" in evidence_lower or "exit_code=1" in evidence_lower
        assert finding.location == "package.json:scripts.format:check"
        assert finding.round_number == 2
        assert finding.status == "open"

    def test_passed_gates_skipped(self) -> None:
        from pdd.checkup_gates import Gate, GateResult, gate_results_to_findings

        gate = Gate(name="ok", cmd=["true"], source="<test>")
        passing = GateResult(
            gate=gate,
            exit_code=0,
            stdout_excerpt="",
            stderr_excerpt="",
            duration_seconds=0.01,
            started_at_iso="2025-01-01T00:00:00Z",
        )
        findings = gate_results_to_findings([passing], round_number=1)
        assert findings == []

    def test_runner_side_error_becomes_finding(self) -> None:
        from pdd.checkup_gates import Gate, GateResult, gate_results_to_findings

        gate = Gate(name="hang", cmd=["sleep", "10"], source="<test>")
        result = GateResult(
            gate=gate,
            exit_code=None,
            stdout_excerpt="",
            stderr_excerpt="",
            duration_seconds=0.1,
            started_at_iso="2025-01-01T00:00:00Z",
            error="timed out after 0.1s",
        )
        findings = gate_results_to_findings([result], round_number=1)
        assert len(findings) == 1
        assert findings[0].severity == "blocker"
        evidence_lower = findings[0].evidence.lower()
        assert "timed out" in evidence_lower or "timeout" in evidence_lower

    def test_dedup_key_is_stable_across_rounds(self) -> None:
        from pdd.checkup_gates import Gate, GateResult, gate_results_to_findings

        gate = Gate(
            name="prettier-check",
            cmd=["prettier", "--check", "."],
            source="package.json:scripts.format:check",
        )
        r1 = gate_results_to_findings(
            [
                GateResult(
                    gate=gate,
                    exit_code=1,
                    stdout_excerpt="A",
                    stderr_excerpt="",
                    duration_seconds=0.5,
                    started_at_iso="2025-01-01T00:00:00Z",
                )
            ],
            round_number=1,
        )
        r2 = gate_results_to_findings(
            [
                GateResult(
                    gate=gate,
                    exit_code=1,
                    stdout_excerpt="B",
                    stderr_excerpt="",
                    duration_seconds=0.5,
                    started_at_iso="2025-01-01T00:00:01Z",
                )
            ],
            round_number=2,
        )
        assert r1[0].key == r2[0].key
