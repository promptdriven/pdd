import py_compile
import pytest
from pathlib import Path

def test_all_examples_syntax():
    """Ensure all Python files under the examples/ directory compile without SyntaxErrors."""
    repo_root = Path(__file__).resolve().parents[1]
    examples_dir = repo_root / "examples"
    assert examples_dir.exists(), f"Examples directory not found at {examples_dir}"
    
    python_files = list(examples_dir.rglob("*.py"))
    assert len(python_files) > 0, "No Python files found under examples/"
    
    failed_files = []
    for py_file in python_files:
        try:
            py_compile.compile(str(py_file), doraise=True)
        except py_compile.PyCompileError as e:
            failed_files.append((py_file, str(e)))
            
    if failed_files:
        failure_msg = "\n".join([f"- {path}: {err}" for path, err in failed_files])
        pytest.fail(f"SyntaxError(s) detected in examples:\n{failure_msg}")
