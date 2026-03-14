import os
import subprocess
import sys
from pathlib import Path

def get_project_root() -> Path:
    current = Path(__file__).parent
    while current != current.parent:
        if (current / "pdd").is_dir() and (current / "pyproject.toml").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find project root with pdd/ directory")

def run_pdd_agentic_failure(command: str) -> subprocess.CompletedProcess:
    project_root = get_project_root()
    env = os.environ.copy()
    env["PYTHONPATH"] = str(project_root)
    
    # We use a completely invalid GitHub URL so the issue fetch fails immediately,
    # avoiding real LLM API calls, but still triggering the "failure -> non-zero exit code" path.
    invalid_url = "https://github.com/promptdriven/pdd/issues/99999999"
    
    return subprocess.run(
        [sys.executable, "-m", "pdd.cli", command, invalid_url],
        capture_output=True,
        text=True,
        cwd=str(project_root),
        env=env,
    )

def test_pdd_bug_exit_code_on_failure():
    result = run_pdd_agentic_failure("bug")
    # Should exit with code 1 due to failure, not 0
    assert result.returncode == 1, f"Expected exit code 1, got {result.returncode}. Output: {result.stdout} {result.stderr}"

def test_pdd_test_exit_code_on_failure():
    result = run_pdd_agentic_failure("test")
    assert result.returncode == 1, f"Expected exit code 1, got {result.returncode}. Output: {result.stdout} {result.stderr}"

def test_pdd_fix_exit_code_on_failure():
    result = run_pdd_agentic_failure("fix")
    assert result.returncode == 1, f"Expected exit code 1, got {result.returncode}. Output: {result.stdout} {result.stderr}"
