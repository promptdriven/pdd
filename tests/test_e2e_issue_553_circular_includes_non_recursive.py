"""
E2E Test for Issue #553: Circular <include> tags cause infinite loop in non-recursive preprocess.

This test exercises the full CLI path: `pdd preprocess` (default, non-recursive) with
real circular prompt files on disk. No mocking of the preprocessor. This verifies the
user-facing behavior: running `pdd preprocess` on circular includes must produce an
error exit code within a reasonable time, not hang forever.

Issue #521 (fixed by PR #528) added cycle detection for --recursive mode.
Issue #553 reports that the default (non-recursive) path was not covered by that fix.
"""

import os
import subprocess
import sys
import pytest
from pathlib import Path


# Timeout in seconds for subprocess — buggy code loops forever, so this must be finite.
# 10 seconds is generous; the fixed code should exit in < 1 second.
CLI_TIMEOUT = 10


def _get_project_root() -> Path:
    """Get the project root directory."""
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pyproject.toml").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")


def _run_pdd_preprocess(prompt_file: str, cwd: str, extra_args: list = None):
    """Run `pdd --force preprocess <prompt_file>` via subprocess with timeout.

    Returns (returncode, stdout, stderr) or raises subprocess.TimeoutExpired
    if the process hangs (indicating the infinite loop bug).
    """
    cmd = [sys.executable, "-m", "pdd.cli", "--force", "preprocess", prompt_file]
    if extra_args:
        cmd.extend(extra_args)
    env = os.environ.copy()
    env["PYTHONPATH"] = str(_get_project_root())
    return subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        cwd=cwd,
        env=env,
        timeout=CLI_TIMEOUT,
    )


class TestIssue553CircularIncludesNonRecursiveE2E:
    """E2E: `pdd preprocess` (non-recursive) on circular includes must error, not loop forever."""

    def test_mutual_circular_includes_default_mode(self, tmp_path):
        """Reproduce the exact bug: A includes B, B includes A, default (non-recursive) mode.

        Bug behavior: process hangs forever, spamming "Processing XML include" messages.
        Expected: non-zero exit code with "Circular include detected" in output, within seconds.
        """
        a_file = tmp_path / "a_python.prompt"
        b_file = tmp_path / "b_python.prompt"

        a_file.write_text("Hello\n<include>b_python.prompt</include>\n")
        b_file.write_text("World\n<include>a_python.prompt</include>\n")

        try:
            result = _run_pdd_preprocess(str(a_file), cwd=str(tmp_path))
        except subprocess.TimeoutExpired:
            pytest.fail(
                f"pdd preprocess hung for {CLI_TIMEOUT}s — infinite loop detected (bug #553). "
                f"Non-recursive circular include cycle detection is missing."
            )

        # Process completed within timeout. Verify it errored out properly.
        assert result.returncode != 0, (
            f"pdd preprocess should have exited with non-zero code for circular includes, "
            f"got exit code {result.returncode}.\n"
            f"stdout: {result.stdout[:500]}\nstderr: {result.stderr[:500]}"
        )

        combined_output = result.stdout + result.stderr
        assert "circular include" in combined_output.lower(), (
            f"Expected 'Circular include detected' in output, got:\n"
            f"stdout: {result.stdout[:500]}\nstderr: {result.stderr[:500]}"
        )

    def test_self_referencing_include_default_mode(self, tmp_path):
        """A file that includes itself must not loop forever in non-recursive mode."""
        self_file = tmp_path / "self_ref_python.prompt"
        self_file.write_text("Content\n<include>self_ref_python.prompt</include>\n")

        try:
            result = _run_pdd_preprocess(str(self_file), cwd=str(tmp_path))
        except subprocess.TimeoutExpired:
            pytest.fail(
                f"pdd preprocess hung for {CLI_TIMEOUT}s — self-referencing infinite loop (bug #553)."
            )

        assert result.returncode != 0, (
            f"Self-referencing include should error, got exit code {result.returncode}."
        )

    def test_three_file_cycle_default_mode(self, tmp_path):
        """A→B→C→A cycle via CLI must not loop forever in non-recursive mode."""
        (tmp_path / "a_python.prompt").write_text("AAA\n<include>b_python.prompt</include>\n")
        (tmp_path / "b_python.prompt").write_text("BBB\n<include>c_python.prompt</include>\n")
        (tmp_path / "c_python.prompt").write_text("CCC\n<include>a_python.prompt</include>\n")

        try:
            result = _run_pdd_preprocess(
                str(tmp_path / "a_python.prompt"), cwd=str(tmp_path)
            )
        except subprocess.TimeoutExpired:
            pytest.fail(
                f"pdd preprocess hung for {CLI_TIMEOUT}s — 3-file cycle infinite loop (bug #553)."
            )

        assert result.returncode != 0, (
            f"Three-file cycle should error, got exit code {result.returncode}."
        )

    def test_backtick_circular_includes_default_mode(self, tmp_path):
        """Backtick-style circular includes must also be detected in non-recursive mode."""
        x_file = tmp_path / "x_python.prompt"
        y_file = tmp_path / "y_python.prompt"

        x_file.write_text("Foo\n```<y_python.prompt>```\n")
        y_file.write_text("Bar\n```<x_python.prompt>```\n")

        try:
            result = _run_pdd_preprocess(str(x_file), cwd=str(tmp_path))
        except subprocess.TimeoutExpired:
            pytest.fail(
                f"pdd preprocess hung for {CLI_TIMEOUT}s — backtick circular include loop (bug #553)."
            )

        assert result.returncode != 0, (
            f"Backtick circular include should error, got exit code {result.returncode}."
        )

    def test_non_circular_includes_still_work(self, tmp_path):
        """Non-circular chain (A→B→C) must still preprocess successfully in default mode."""
        (tmp_path / "top_python.prompt").write_text("Top\n<include>mid.txt</include>\n")
        (tmp_path / "mid.txt").write_text("Mid\n<include>leaf.txt</include>\n")
        (tmp_path / "leaf.txt").write_text("Leaf\n")

        output_file = tmp_path / "output.txt"

        try:
            result = _run_pdd_preprocess(
                str(tmp_path / "top_python.prompt"),
                cwd=str(tmp_path),
                extra_args=["--output", str(output_file)],
            )
        except subprocess.TimeoutExpired:
            pytest.fail("Non-circular preprocess should not hang.")

        assert result.returncode == 0, (
            f"Non-circular include should succeed, got exit code {result.returncode}.\n"
            f"stderr: {result.stderr[:500]}"
        )

        assert output_file.exists(), (
            f"Expected output file {output_file} to be created by --output flag.\n"
            f"stdout: {result.stdout[:500]}"
        )
        content = output_file.read_text()
        assert "Top" in content
        assert "Mid" in content
        assert "Leaf" in content

    def test_recursive_mode_still_detects_cycle(self, tmp_path):
        """Sanity check: --recursive mode still catches circular includes (regression guard)."""
        a_file = tmp_path / "a_python.prompt"
        b_file = tmp_path / "b_python.prompt"

        a_file.write_text("Hello\n<include>b_python.prompt</include>\n")
        b_file.write_text("World\n<include>a_python.prompt</include>\n")

        try:
            result = _run_pdd_preprocess(
                str(a_file), cwd=str(tmp_path), extra_args=["--recursive"]
            )
        except subprocess.TimeoutExpired:
            pytest.fail("--recursive mode should not hang on circular includes.")

        assert result.returncode != 0, (
            f"--recursive mode should error on circular includes, got exit code {result.returncode}."
        )
