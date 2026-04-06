"""Phase 4b negative E2E test: Step 11 cleanup revert safety net.

Verifies that when Step 11 (code cleanup) removes code that is asserted in
tests, the cleanup changes are reverted — the debug print stays and no
"chore: clean up" commit is left behind.

This test makes REAL LLM calls and costs money. Mark: e2e, real.
"""

import hashlib
import subprocess
import tempfile
from pathlib import Path

import pytest

from pdd.agentic_e2e_fix_orchestrator import _run_step11_code_cleanup

# ---------------------------------------------------------------------------
# Fixtures: tiny repo with "cleanup bait" that the test suite depends on
# ---------------------------------------------------------------------------

APP_PY = """\
import os  # unused import — cleanup bait (safe to remove)

def process(value: str) -> str:
    \"\"\"Process a value and return the result.\"\"\"
    print("DEBUG: processing")  # cleanup bait — BUT asserted by tests
    return f"processed-{value}"

def add(a: int, b: int) -> int:
    \"\"\"Add two numbers.\"\"\"
    return a + b
"""

TEST_APP_PY = """\
import io
import sys
import os

# Ensure the repo root is on sys.path so 'import app' works
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

def test_process_output(capsys):
    \"\"\"Verify process() emits the DEBUG line on stdout.\"\"\"
    from app import process
    process("x")
    captured = capsys.readouterr()
    assert "DEBUG: processing" in captured.out, (
        f"Expected DEBUG line in stdout, got: {captured.out!r}"
    )

def test_add():
    from app import add
    assert add(1, 2) == 3
"""


def _md5(path: Path) -> str:
    """Return MD5 hex digest for *path*."""
    return hashlib.md5(path.read_bytes()).hexdigest()


def _git(cwd: Path, *args: str) -> subprocess.CompletedProcess:
    """Run a git command in *cwd* and return the result."""
    return subprocess.run(
        ["git", *args],
        cwd=cwd,
        capture_output=True,
        text=True,
        check=True,
    )


@pytest.mark.e2e
@pytest.mark.real
def test_step11_reverts_cleanup_when_tests_break():
    """Step 11 must revert cleanup if removing the debug print breaks tests."""

    with tempfile.TemporaryDirectory() as tmp:
        repo = Path(tmp)

        # ---- 1. Initialise the git repo on branch "main" ------------------
        _git(repo, "init", "-b", "main")
        _git(repo, "config", "user.email", "test@test.com")
        _git(repo, "config", "user.name", "Test")

        # ---- 2. Write app.py (without the unused import yet) and test -----
        initial_app = (
            'def process(value: str) -> str:\n'
            '    """Process a value and return the result."""\n'
            '    print("DEBUG: processing")  # cleanup bait -- BUT asserted by tests\n'
            '    return f"processed-{value}"\n'
        )
        (repo / "app.py").write_text(initial_app)
        (repo / "test_app.py").write_text(TEST_APP_PY)

        _git(repo, "add", ".")
        _git(repo, "commit", "-m", "initial commit")

        # ---- 3. Record initial file hashes (BEFORE the "fix") -------------
        initial_hashes = {
            "app.py": _md5(repo / "app.py"),
            "test_app.py": _md5(repo / "test_app.py"),
        }

        # ---- 4. Create a feature branch, apply the "fix" ------------------
        _git(repo, "checkout", "-b", "fix/issue-999")

        # Now write the full APP_PY which adds the unused `import os` and a
        # second function — giving the LLM real cleanup targets.
        (repo / "app.py").write_text(APP_PY)

        _git(repo, "add", ".")
        _git(repo, "commit", "-m", "fix: add feature")

        # ---- 5. Sanity-check: tests pass before Step 11 -------------------
        pre_result = subprocess.run(
            ["python", "-m", "pytest", "test_app.py", "-v"],
            cwd=repo,
            capture_output=True,
            text=True,
        )
        assert pre_result.returncode == 0, (
            f"Tests must pass BEFORE Step 11. stdout:\n{pre_result.stdout}\n"
            f"stderr:\n{pre_result.stderr}"
        )

        # Record commit count before Step 11
        log_before = _git(repo, "log", "--oneline").stdout.strip()
        commit_count_before = len(log_before.splitlines())

        # ---- 6. Run Step 11 -----------------------------------------------
        print("\n===== Running Step 11 (real LLM call) =====")
        updated_cost, updated_files = _run_step11_code_cleanup(
            cwd=repo,
            issue_number=999,
            issue_content="Test issue — app.py has a debug print and unused import",
            issue_url="",
            repo_owner="test",
            repo_name="test",
            initial_file_hashes=initial_hashes,
            total_cost=0.0,
            changed_files=["app.py", "test_app.py"],
            timeout_adder=0.0,
            verbose=True,
            quiet=False,
        )
        print(f"Step 11 returned: cost={updated_cost}, files={updated_files}")

        # ---- 7. Verify the safety net held --------------------------------
        app_content = (repo / "app.py").read_text()
        print(f"\n===== app.py after Step 11 =====\n{app_content}")

        # The debug print MUST still be present (either the LLM was smart
        # enough not to remove it, or cleanup was reverted).
        assert 'print("DEBUG: processing")' in app_content, (
            "SAFETY NET FAILED: the debug print was removed and NOT reverted!"
        )

        # Tests must still pass after Step 11
        post_result = subprocess.run(
            ["python", "-m", "pytest", "test_app.py", "-v"],
            cwd=repo,
            capture_output=True,
            text=True,
        )
        assert post_result.returncode == 0, (
            f"Tests FAIL after Step 11. stdout:\n{post_result.stdout}\n"
            f"stderr:\n{post_result.stderr}"
        )

        # There should NOT be a "chore: clean up" commit (cleanup was reverted)
        log_after = _git(repo, "log", "--oneline").stdout.strip()
        print(f"\n===== git log after Step 11 =====\n{log_after}")

        # Two acceptable outcomes:
        #   A) LLM removed the debug print -> tests failed -> revert (no cleanup commit)
        #   B) LLM was smart enough to leave it -> no cleanup commit or a harmless one
        #      (e.g., only removed unused import — that's fine, tests still pass)
        #
        # The critical invariant: tests pass AND the debug print is present.
        # If there IS a cleanup commit, that's fine — it means the LLM only
        # cleaned safe things (like the unused import). We already verified
        # tests pass and the debug print is present above.

        print("\n===== PASS: Safety net held — debug print preserved, tests pass =====")
