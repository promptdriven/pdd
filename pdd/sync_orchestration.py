# pdd/sync_orchestration.py
"""
Orchestrates the complete PDD sync workflow by coordinating operations and
animations in parallel, serving as the core engine for the `pdd sync` command.
"""

import threading
import time
import json
import datetime
import subprocess
import re
import os
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable
from dataclasses import asdict, dataclass, field
import tempfile
import sys

import click
import logging

# --- Constants ---
MAX_CONSECUTIVE_TESTS = 3  # Allow up to 3 consecutive test attempts
MAX_TEST_EXTEND_ATTEMPTS = 2  # Allow up to 2 attempts to extend tests for coverage
MAX_CONSECUTIVE_CRASHES = 3  # Allow up to 3 consecutive crash attempts (Bug #157 fix)

# --- Real PDD Component Imports ---
from .sync_tui import SyncApp
from .sync_determine_operation import (
    sync_determine_operation,
    get_pdd_file_paths,
    RunReport,
    SyncDecision,
    PDD_DIR,
    META_DIR,
    SyncLock,
    read_run_report,
    calculate_sha256,
    calculate_current_hashes,
    _safe_basename,
)
from .auto_deps_main import auto_deps_main
from .code_generator_main import code_generator_main
from .context_generator_main import context_generator_main
from .crash_main import crash_main
from .fix_verification_main import fix_verification_main
from .cmd_test_main import cmd_test_main
from .fix_main import fix_main
from .update_main import update_main
from .python_env_detector import detect_host_python_executable
from .get_run_command import get_run_command_for_file
from .pytest_output import extract_failing_files_from_output
from . import DEFAULT_STRENGTH


# --- Helper Functions ---
# Note: _safe_basename is imported from sync_determine_operation


# --- Atomic State Update (Issue #159 Fix) ---

@dataclass
class PendingStateUpdate:
    """Holds pending state updates for atomic commit."""
    run_report: Optional[Dict[str, Any]] = None
    fingerprint: Optional[Dict[str, Any]] = None
    run_report_path: Optional[Path] = None
    fingerprint_path: Optional[Path] = None


class AtomicStateUpdate:
    """
    Context manager for atomic state updates.

    Ensures run_report and fingerprint are both written or neither is written.
    This fixes Issue #159 where non-atomic writes caused state desynchronization.

    Usage:
        with AtomicStateUpdate(basename, language) as state:
            state.set_run_report(report_dict, report_path)
            state.set_fingerprint(fingerprint_dict, fp_path)
        # On successful exit, both files are written atomically
        # On exception, neither file is written (rollback)
    """

    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self.pending = PendingStateUpdate()
        self._temp_files: List[str] = []

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            self._commit()
        else:
            self._rollback()
        return False  # Don't suppress exceptions

    def set_run_report(self, report: Dict[str, Any], path: Path):
        """Buffer a run report for atomic write."""
        self.pending.run_report = report
        self.pending.run_report_path = path

    def set_fingerprint(self, fingerprint: Dict[str, Any], path: Path):
        """Buffer a fingerprint for atomic write."""
        self.pending.fingerprint = fingerprint
        self.pending.fingerprint_path = path

    def _atomic_write(self, data: Dict[str, Any], target_path: Path) -> None:
        """Write data to file atomically using temp file + rename pattern."""
        target_path.parent.mkdir(parents=True, exist_ok=True)

        # Write to temp file in same directory (required for atomic rename)
        fd, temp_path = tempfile.mkstemp(
            dir=target_path.parent,
            prefix=f".{target_path.stem}_",
            suffix=".tmp"
        )
        self._temp_files.append(temp_path)

        try:
            with os.fdopen(fd, 'w') as f:
                json.dump(data, f, indent=2, default=str)

            # Atomic rename - guaranteed atomic on POSIX systems
            os.replace(temp_path, target_path)
            self._temp_files.remove(temp_path)  # Successfully moved, stop tracking
        except Exception:
            # Leave temp file for rollback to clean up
            raise

    def _commit(self):
        """Commit all pending state updates atomically."""
        # Write fingerprint first (checkpoint), then run_report
        if self.pending.fingerprint and self.pending.fingerprint_path:
            self._atomic_write(self.pending.fingerprint, self.pending.fingerprint_path)
        if self.pending.run_report and self.pending.run_report_path:
            self._atomic_write(self.pending.run_report, self.pending.run_report_path)

    def _rollback(self):
        """Clean up any temp files without committing changes."""
        for temp_path in self._temp_files:
            try:
                if os.path.exists(temp_path):
                    os.unlink(temp_path)
            except OSError:
                pass  # Best effort cleanup
        self._temp_files.clear()


# --- Mock Helper Functions ---

def load_sync_log(basename: str, language: str) -> List[Dict[str, Any]]:
    """Load sync log entries for a basename and language."""
    log_file = META_DIR / f"{_safe_basename(basename)}_{language}_sync.log"
    if not log_file.exists():
        return []
    try:
        with open(log_file, 'r') as f:
            return [json.loads(line) for line in f if line.strip()]
    except Exception:
        return []

def create_sync_log_entry(decision, budget_remaining: float) -> Dict[str, Any]:
    """Create initial log entry from decision with all fields (actual results set to None initially)."""
    return {
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "operation": decision.operation,
        "reason": decision.reason,
        "decision_type": decision.details.get("decision_type", "heuristic") if decision.details else "heuristic",
        "confidence": decision.confidence,
        "estimated_cost": decision.estimated_cost,
        "actual_cost": None,
        "success": None,
        "model": None,
        "duration": None,
        "error": None,
        "details": {
            **(decision.details if decision.details else {}),
            "budget_remaining": budget_remaining
        }
    }

def update_sync_log_entry(entry: Dict[str, Any], result: Dict[str, Any], duration: float) -> Dict[str, Any]:
    """Update log entry with execution results (actual_cost, success, model, duration, error)."""
    entry.update({
        "actual_cost": result.get("cost", 0.0),
        "success": result.get("success", False),
        "model": result.get("model", "unknown"),
        "duration": duration,
        "error": result.get("error") if not result.get("success") else None
    })
    return entry

def append_sync_log(basename: str, language: str, entry: Dict[str, Any]):
    """Append completed log entry to the sync log file."""
    log_file = META_DIR / f"{_safe_basename(basename)}_{language}_sync.log"
    META_DIR.mkdir(parents=True, exist_ok=True)
    with open(log_file, 'a') as f:
        f.write(json.dumps(entry) + '\n')

def log_sync_event(basename: str, language: str, event: str, details: Dict[str, Any] = None):
    """Log a special sync event (lock_acquired, budget_warning, etc.)."""
    entry = {
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "event": event,
        "details": details or {}
    }
    append_sync_log(basename, language, entry)

def save_run_report(report: Dict[str, Any], basename: str, language: str,
                    atomic_state: Optional['AtomicStateUpdate'] = None):
    """Save a run report to the metadata directory.

    Args:
        report: The run report dictionary to save.
        basename: The module basename.
        language: The programming language.
        atomic_state: Optional AtomicStateUpdate for atomic writes (Issue #159 fix).
    """
    report_file = META_DIR / f"{_safe_basename(basename)}_{language}_run.json"
    if atomic_state:
        # Buffer for atomic write
        atomic_state.set_run_report(report, report_file)
    else:
        # Legacy direct write
        META_DIR.mkdir(parents=True, exist_ok=True)
        with open(report_file, 'w') as f:
            json.dump(report, f, indent=2, default=str)

def _save_operation_fingerprint(basename: str, language: str, operation: str,
                               paths: Dict[str, Path], cost: float, model: str,
                               atomic_state: Optional['AtomicStateUpdate'] = None):
    """Save fingerprint state after successful operation.

    Args:
        basename: The module basename.
        language: The programming language.
        operation: The operation that was performed.
        paths: Dictionary of PDD file paths.
        cost: The cost of the operation.
        model: The model used.
        atomic_state: Optional AtomicStateUpdate for atomic writes (Issue #159 fix).
    """
    from datetime import datetime, timezone
    from .sync_determine_operation import calculate_current_hashes, Fingerprint
    from . import __version__

    current_hashes = calculate_current_hashes(paths)
    fingerprint = Fingerprint(
        pdd_version=__version__,
        timestamp=datetime.now(timezone.utc).isoformat(),
        command=operation,
        prompt_hash=current_hashes.get('prompt_hash'),
        code_hash=current_hashes.get('code_hash'),
        example_hash=current_hashes.get('example_hash'),
        test_hash=current_hashes.get('test_hash'),
        test_files=current_hashes.get('test_files'),  # Bug #156
    )

    fingerprint_file = META_DIR / f"{_safe_basename(basename)}_{language}.json"
    if atomic_state:
        # Buffer for atomic write
        atomic_state.set_fingerprint(asdict(fingerprint), fingerprint_file)
    else:
        # Legacy direct write
        META_DIR.mkdir(parents=True, exist_ok=True)
        with open(fingerprint_file, 'w') as f:
            json.dump(asdict(fingerprint), f, indent=2, default=str)

def _python_cov_target_for_code_file(code_file: Path) -> str:
    """Return a `pytest-cov` `--cov` target for a Python code file.

    - If the file is inside a Python package (directories with `__init__.py`),
      returns a dotted module path (e.g., `pdd.sync_orchestration`).
    - Otherwise falls back to the filename stem (e.g., `admin_get_users`).
    """
    if code_file.suffix != ".py":
        return code_file.stem

    package_dir: Optional[Path] = None
    current = code_file.parent
    while (current / "__init__.py").exists():
        package_dir = current
        parent = current.parent
        if parent == current:
            break
        current = parent

    if package_dir:
        relative_module = code_file.relative_to(package_dir.parent).with_suffix("")
        return str(relative_module).replace(os.sep, ".")

    return code_file.stem


def _python_cov_target_for_test_and_code(test_file: Path, code_file: Path, fallback: str) -> str:
    """Choose the best `--cov` target based on how tests import the code.

    In some repos, tests add a directory to `sys.path` and import modules by their
    filename stem (e.g., `from admin_get_users import ...`) even when the code
    also lives under a package (e.g., `backend.functions.admin_get_users`).

    Heuristic:
    - Prefer the code file stem when the test file imports it directly.
    - Otherwise, prefer the dotted module path derived from the package layout.
    - Fall back to the provided fallback (usually the basename).
    """

    def _imports_module(source: str, module: str) -> bool:
        escaped = re.escape(module)
        return bool(
            re.search(rf"^\s*import\s+{escaped}\b", source, re.MULTILINE)
            or re.search(rf"^\s*from\s+{escaped}\b", source, re.MULTILINE)
        )

    stem = code_file.stem
    dotted = _python_cov_target_for_code_file(code_file)

    try:
        test_source = test_file.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        test_source = ""

    if stem and _imports_module(test_source, stem):
        return stem

    if dotted and dotted != stem:
        if _imports_module(test_source, dotted):
            return dotted

        if "." in dotted:
            parent = dotted.rsplit(".", 1)[0]
            # e.g. `from backend.functions import admin_get_users`
            if re.search(
                rf"^\s*from\s+{re.escape(parent)}\s+import\s+.*\b{re.escape(stem)}\b",
                test_source,
                re.MULTILINE,
            ):
                return dotted
            # e.g. `import backend.functions.admin_get_users`
            if re.search(
                rf"^\s*import\s+{re.escape(parent)}\.{re.escape(stem)}\b",
                test_source,
                re.MULTILINE,
            ):
                return dotted

        return dotted

    return stem or fallback


def _parse_test_output(output: str, language: str) -> tuple[int, int, float]:
    """
    Parse test output to extract passed/failed/coverage.

    Args:
        output: Combined stdout/stderr from test runner
        language: Language name (e.g., 'python', 'typescript', 'go')

    Returns:
        (tests_passed, tests_failed, coverage)
    """
    tests_passed = 0
    tests_failed = 0
    coverage = 0.0

    lang = language.lower()

    # Python (pytest)
    if lang == 'python':
        if 'passed' in output:
            passed_match = re.search(r'(\d+) passed', output)
            if passed_match:
                tests_passed = int(passed_match.group(1))
        if 'failed' in output:
            failed_match = re.search(r'(\d+) failed', output)
            if failed_match:
                tests_failed = int(failed_match.group(1))
        if 'error' in output:
            error_match = re.search(r'(\d+) error', output)
            if error_match:
                tests_failed += int(error_match.group(1))
        coverage_match = re.search(r'TOTAL.*?(\d+)%', output)
        if not coverage_match:
            coverage_match = re.search(r'(\d+)%\s*$', output, re.MULTILINE)
        if not coverage_match:
            coverage_match = re.search(r'(\d+(?:\.\d+)?)%', output)
        if coverage_match:
            coverage = float(coverage_match.group(1))

    # Jest/Vitest (JavaScript/TypeScript)
    elif lang in ('javascript', 'typescript', 'typescriptreact'):
        # "Tests: X passed, Y failed" or "Tests: X passed, Y failed, Z total"
        match = re.search(r'Tests:\s*(\d+)\s+passed', output)
        if match:
            tests_passed = int(match.group(1))
        match = re.search(r'Tests:.*?(\d+)\s+failed', output)
        if match:
            tests_failed = int(match.group(1))

        # Alternative Mocha-style: "X passing, Y failing"
        if tests_passed == 0:
            pass_match = re.search(r'(\d+)\s+pass(?:ing)?', output, re.I)
            if pass_match:
                tests_passed = int(pass_match.group(1))
        if tests_failed == 0:
            fail_match = re.search(r'(\d+)\s+fail(?:ing)?', output, re.I)
            if fail_match:
                tests_failed = int(fail_match.group(1))

        # Coverage: "All files | XX.XX |"
        cov_match = re.search(r'All files[^|]*\|\s*(\d+\.?\d*)', output)
        if cov_match:
            coverage = float(cov_match.group(1))

    # Go
    elif lang == 'go':
        # Count PASS and FAIL occurrences for individual tests
        tests_passed = len(re.findall(r'--- PASS:', output))
        tests_failed = len(re.findall(r'--- FAIL:', output))

        # Fallback: check for overall PASS/FAIL
        if tests_passed == 0 and 'PASS' in output and 'FAIL' not in output:
            tests_passed = 1
        if tests_failed == 0 and 'FAIL' in output:
            tests_failed = 1

        # coverage: XX.X% of statements
        cov_match = re.search(r'coverage:\s*(\d+\.?\d*)%', output)
        if cov_match:
            coverage = float(cov_match.group(1))

    # Rust (cargo test)
    elif lang == 'rust':
        # "test result: ok. X passed; Y failed;"
        match = re.search(r'(\d+)\s+passed', output)
        if match:
            tests_passed = int(match.group(1))
        match = re.search(r'(\d+)\s+failed', output)
        if match:
            tests_failed = int(match.group(1))

    # Fallback: try generic patterns
    else:
        pass_match = re.search(r'(\d+)\s+(?:tests?\s+)?pass(?:ed)?', output, re.I)
        fail_match = re.search(r'(\d+)\s+(?:tests?\s+)?fail(?:ed)?', output, re.I)
        if pass_match:
            tests_passed = int(pass_match.group(1))
        if fail_match:
            tests_failed = int(fail_match.group(1))

    return tests_passed, tests_failed, coverage


def _detect_example_errors(output: str) -> tuple[bool, str]:
    """
    Detect if example output contains error indicators.

    Only detects true crashes/errors:
    - Python tracebacks (catches ALL unhandled exceptions)
    - ERROR level log messages

    Intentionally does NOT detect:
    - HTTP status codes (examples may test error responses)
    - Individual exception type names (causes false positives, redundant with traceback)

    Returns:
        (has_errors, error_summary)
    """
    error_patterns = [
        (r'Traceback \(most recent call last\):', 'Python traceback'),
        (r' - ERROR - ', 'Error log message'),  # Python logging format
    ]

    errors_found = []
    for pattern, description in error_patterns:
        if re.search(pattern, output, re.MULTILINE):
            errors_found.append(description)

    if errors_found:
        return True, '; '.join(errors_found)
    return False, ''


def _try_auto_fix_import_error(
    error_output: str,
    code_file: Path,
    example_file: Path,
) -> tuple[bool, str]:
    """
    Try to automatically fix common import errors before calling expensive agentic fix.

    Returns:
        (fixed, message): Whether a fix was attempted and what was done.
    """
    import re

    # Check for ModuleNotFoundError or ImportError
    module_not_found = re.search(r"ModuleNotFoundError: No module named ['\"]([^'\"]+)['\"]", error_output)
    import_error = re.search(r"ImportError: cannot import name ['\"]([^'\"]+)['\"]", error_output)

    if not module_not_found and not import_error:
        return False, "No import error detected"

    if module_not_found:
        missing_module = module_not_found.group(1)
        # Split by . to get the top-level package
        top_level_package = missing_module.split('.')[0]

        # Check if this is the module we're trying to import (local module)
        code_module_name = code_file.stem  # e.g., "data_validator" from "data_validator.py"

        if top_level_package == code_module_name:
            # It's trying to import our own generated code - fix the example's sys.path
            # Read the example and fix the path manipulation
            try:
                example_content = example_file.read_text(encoding='utf-8')
                code_dir = str(code_file.parent.resolve())

                # Look for existing sys.path manipulation
                if 'sys.path' in example_content:
                    # Try to fix the existing path manipulation
                    # Common pattern: module_path = os.path.abspath(os.path.join(...))
                    # Replace with correct path
                    fixed_content = re.sub(
                        r"module_path\s*=\s*os\.path\.abspath\([^)]+\)",
                        f"module_path = '{code_dir}'",
                        example_content
                    )
                    if fixed_content != example_content:
                        example_file.write_text(fixed_content, encoding='utf-8')
                        return True, f"Fixed sys.path to point to {code_dir}"

                # If no existing sys.path, add one at the start after imports
                lines = example_content.split('\n')
                insert_pos = 0
                for i, line in enumerate(lines):
                    if line.startswith('import ') or line.startswith('from '):
                        if 'sys' in line or 'os' in line:
                            insert_pos = i + 1
                            continue
                    if line.strip() and not line.startswith('#') and not line.startswith('import') and not line.startswith('from'):
                        insert_pos = i
                        break

                path_fix = f"\n# Auto-added by pdd to fix import\nimport sys\nsys.path.insert(0, '{code_dir}')\n"
                lines.insert(insert_pos, path_fix)
                example_file.write_text('\n'.join(lines), encoding='utf-8')
                return True, f"Added sys.path.insert(0, '{code_dir}') to example"

            except Exception as e:
                return False, f"Failed to fix import path: {e}"

        else:
            # It's an external package - try pip install
            try:
                result = subprocess.run(
                    [sys.executable, '-m', 'pip', 'install', top_level_package],
                    capture_output=True,
                    text=True,
                    timeout=120
                )
                if result.returncode == 0:
                    return True, f"Installed missing package: {top_level_package}"
                else:
                    return False, f"Failed to install {top_level_package}: {result.stderr}"
            except Exception as e:
                return False, f"Failed to run pip install: {e}"

    return False, "Import error detected but no auto-fix available"


def _run_example_with_error_detection(
    cmd_parts: list[str],
    env: dict,
    cwd: str,
    timeout: int = 60
) -> tuple[int, str, str]:
    """
    Run example file, detecting errors from output.

    For server-style examples that block, this runs until timeout
    then analyzes output for errors. No errors = success.

    Returns:
        (returncode, stdout, stderr)
        - returncode: 0 if no errors detected, positive if errors found or process failed
    """
    import threading

    proc = subprocess.Popen(
        cmd_parts,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        stdin=subprocess.DEVNULL,
        env=env,
        cwd=cwd,
        start_new_session=True,
    )

    stdout_chunks = []
    stderr_chunks = []

    def read_pipe(pipe, chunks):
        try:
            for line in iter(pipe.readline, b''):
                chunks.append(line)
        except Exception:
            pass

    t_out = threading.Thread(target=read_pipe, args=(proc.stdout, stdout_chunks), daemon=True)
    t_err = threading.Thread(target=read_pipe, args=(proc.stderr, stderr_chunks), daemon=True)
    t_out.start()
    t_err.start()

    # Wait for process or timeout
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.terminate()
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            proc.kill()
            proc.wait()

    t_out.join(timeout=2)
    t_err.join(timeout=2)

    stdout = b''.join(stdout_chunks).decode('utf-8', errors='replace')
    stderr = b''.join(stderr_chunks).decode('utf-8', errors='replace')
    combined = stdout + '\n' + stderr

    # Check for errors in output
    has_errors, error_summary = _detect_example_errors(combined)

    # Determine result:
    # - Errors in output → failure
    # - Positive exit code (process failed normally, e.g., sys.exit(1)) → failure
    # - Negative exit code (killed by signal, e.g., -9 for SIGKILL) → check output
    # - Zero exit code → success
    #
    # IMPORTANT: When we kill the process after timeout, returncode is negative
    # (the signal number). This is NOT a failure if output has no errors.
    if has_errors:
        return 1, stdout, stderr  # Errors detected in output
    elif proc.returncode is not None and proc.returncode > 0:
        return proc.returncode, stdout, stderr  # Process exited with error
    else:
        # Success cases:
        # - returncode == 0 (clean exit)
        # - returncode < 0 (killed by signal, but no errors in output)
        # - returncode is None (shouldn't happen after wait, but safe fallback)
        return 0, stdout, stderr


def _execute_tests_and_create_run_report(
    test_file: Path,
    basename: str,
    language: str,
    target_coverage: float = 90.0,
    *,
    code_file: Optional[Path] = None,
    atomic_state: Optional['AtomicStateUpdate'] = None,
    test_files: Optional[List[Path]] = None,  # Bug #156: Support multiple test files
) -> RunReport:
    """Execute tests and create a RunReport with actual results.

    Now supports multiple languages by using get_test_command_for_file()
    to determine the appropriate test runner.

    Args:
        test_file: Primary test file (for backward compat)
        test_files: Optional list of all test files to run (Bug #156)
    """
    from .get_test_command import get_test_command_for_file

    timestamp = datetime.datetime.now(datetime.timezone.utc).isoformat()

    # Bug #156: Use test_files if provided, otherwise just the single test_file
    all_test_files = test_files if test_files else [test_file]

    # Calculate test file hash for staleness detection (primary file for backward compat)
    test_hash = calculate_sha256(test_file) if test_file.exists() else None

    # Bug #156: Calculate hashes for ALL test files
    test_file_hashes = {
        f.name: calculate_sha256(f)
        for f in all_test_files
        if f.exists()
    } if all_test_files else None

    # Use clean env without TUI-specific vars
    clean_env = os.environ.copy()
    for var in ['FORCE_COLOR', 'COLUMNS']:
        clean_env.pop(var, None)

    try:
        lang_lower = language.lower()

        # Python: use existing pytest logic with coverage
        if lang_lower == "python":
            module_name = test_file.name.replace('test_', '').replace('.py', '')
            python_executable = detect_host_python_executable()

            cov_target = None
            if code_file is not None:
                cov_target = _python_cov_target_for_test_and_code(test_file, code_file, basename or module_name)
            else:
                cov_target = basename or module_name

            if not cov_target:
                cov_target = basename or module_name

            # Bug #156: Run pytest on ALL test files
            pytest_args = [
                python_executable, '-m', 'pytest',
            ] + [str(f) for f in all_test_files] + [
                '-v',
                '--tb=short',
                f'--cov={cov_target}',
                '--cov-report=term-missing'
            ]
            result = subprocess.run(
                pytest_args,
                capture_output=True, text=True, timeout=300, stdin=subprocess.DEVNULL, env=clean_env, start_new_session=True
            )

            exit_code = result.returncode
            stdout = result.stdout + (result.stderr or '')
            tests_passed, tests_failed, coverage = _parse_test_output(stdout, language)

        else:
            # Non-Python: use language-appropriate test command
            test_cmd = get_test_command_for_file(str(test_file), language)

            if test_cmd is None:
                # No test command available - return report indicating this
                report = RunReport(
                    timestamp=timestamp,
                    exit_code=127,  # Command not found
                    tests_passed=0,
                    tests_failed=0,
                    coverage=0.0,
                    test_hash=test_hash,
                    test_files=test_file_hashes,  # Bug #156
                )
                save_run_report(asdict(report), basename, language, atomic_state)
                return report

            # Run the test command
            result = subprocess.run(
                test_cmd,
                shell=True,
                capture_output=True,
                text=True,
                timeout=300,
                env=clean_env,
                cwd=str(test_file.parent),
                stdin=subprocess.DEVNULL,
                start_new_session=True
            )

            exit_code = result.returncode
            stdout = (result.stdout or '') + '\n' + (result.stderr or '')

            # Parse results based on language
            tests_passed, tests_failed, coverage = _parse_test_output(stdout, language)

        report = RunReport(
            timestamp=timestamp,
            exit_code=exit_code,
            tests_passed=tests_passed,
            tests_failed=tests_failed,
            coverage=coverage,
            test_hash=test_hash,
            test_files=test_file_hashes,  # Bug #156
        )

    except (subprocess.TimeoutExpired, subprocess.CalledProcessError, Exception) as e:
        report = RunReport(
            timestamp=timestamp,
            exit_code=1,
            tests_passed=0,
            tests_failed=1,
            coverage=0.0,
            test_hash=test_hash,
            test_files=test_file_hashes,  # Bug #156
        )

    save_run_report(asdict(report), basename, language, atomic_state)
    return report

def _create_mock_context(**kwargs) -> click.Context:
    """Creates a mock Click context object to pass parameters to command functions."""
    ctx = click.Context(click.Command('sync'))
    ctx.obj = kwargs
    return ctx


def _display_sync_log(basename: str, language: str, verbose: bool = False) -> Dict[str, Any]:
    """Displays the sync log for a given basename and language."""
    log_file = META_DIR / f"{_safe_basename(basename)}_{language}_sync.log"
    if not log_file.exists():
        print(f"No sync log found for '{basename}' in language '{language}'.")
        return {'success': False, 'errors': ['Log file not found.'], 'log_entries': []}

    log_entries = load_sync_log(basename, language)
    print(f"--- Sync Log for {basename} ({language}) ---")

    if not log_entries:
        print("Log is empty.")
        return {'success': True, 'log_entries': []}

    for entry in log_entries:
        timestamp = entry.get('timestamp', 'N/A')
        
        if 'event' in entry:
            event = entry.get('event', 'N/A')
            print(f"[{timestamp[:19]}] EVENT: {event}")
            if verbose and 'details' in entry:
                details_str = json.dumps(entry['details'], indent=2)
                print(f"  Details: {details_str}")
            continue
        
        operation = entry.get('operation', 'N/A')
        reason = entry.get('reason', 'N/A')
        success = entry.get('success')
        actual_cost = entry.get('actual_cost')
        estimated_cost = entry.get('estimated_cost', 0.0)
        duration = entry.get('duration')
        
        if verbose:
            print(f"[{timestamp[:19]}] {operation:<12} | {reason}")
            decision_type = entry.get('decision_type', 'N/A')
            confidence = entry.get('confidence', 'N/A')
            model = entry.get('model', 'N/A')
            budget_remaining = entry.get('details', {}).get('budget_remaining', 'N/A')
            
            print(f"  Decision Type: {decision_type} | Confidence: {confidence}")
            if actual_cost is not None:
                print(f"  Cost: ${actual_cost:.2f} (estimated: ${estimated_cost:.2f}) | Model: {model}")
                if duration is not None:
                    print(f"  Duration: {duration:.1f}s | Budget Remaining: ${budget_remaining}")
            else:
                print(f"  Estimated Cost: ${estimated_cost:.2f}")
            
            if 'details' in entry and entry['details']:
                details_copy = entry['details'].copy()
                details_copy.pop('budget_remaining', None)
                if details_copy:
                    details_str = json.dumps(details_copy, indent=2)
                    print(f"  Details: {details_str}")
        else:
            status_icon = "✓" if success else "✗" if success is False else "?"
            
            cost_info = ""
            if actual_cost is not None:
                cost_info = f" | {status_icon} ${actual_cost:.2f} (est: ${estimated_cost:.2f})"
            else:
                cost_info = f" | Est: ${estimated_cost:.2f}"
            
            duration_info = ""
            if duration is not None:
                duration_info = f" | {duration:.1f}s"
            
            error_info = ""
            if entry.get('error'):
                error_info = f" | Error: {entry['error']}"
            
            print(f"[{timestamp[:19]}] {operation:<12} | {reason}{cost_info}{duration_info}{error_info}")

    print("--- End of Log ---")
    return {'success': True, 'log_entries': log_entries}


def sync_orchestration(
    basename: str,
    target_coverage: float = 90.0,
    language: str = "python",
    prompts_dir: str = "prompts",
    code_dir: str = "src",
    examples_dir: str = "examples",
    tests_dir: str = "tests",
    max_attempts: int = 3,
    budget: float = 10.0,
    skip_verify: bool = False,
    skip_tests: bool = False,
    dry_run: bool = False,
    force: bool = False,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time_param: float = 0.25,
    verbose: bool = False,
    quiet: bool = False,
    output_cost: Optional[str] = None,
    review_examples: bool = False,
    local: bool = False,
    context_config: Optional[Dict[str, str]] = None,
    context_override: Optional[str] = None,
    confirm_callback: Optional[Callable[[str, str], bool]] = None,
) -> Dict[str, Any]:
    """
    Orchestrates the complete PDD sync workflow with parallel animation.
    """
    # Handle None values from CLI (Issue #194) - defense in depth
    if target_coverage is None:
        target_coverage = 90.0
    if budget is None:
        budget = 10.0
    if max_attempts is None:
        max_attempts = 3

    # Import get_extension at function scope
    from .sync_determine_operation import get_extension
    
    if dry_run:
        return _display_sync_log(basename, language, verbose)

    # --- Initialize State and Paths ---
    try:
        pdd_files = get_pdd_file_paths(basename, language, prompts_dir, context_override=context_override)
    except FileNotFoundError as e:
        if "test_config.py" in str(e) or "tests/test_" in str(e):
            pdd_files = {
                'prompt': Path(prompts_dir) / f"{basename}_{language}.prompt",
                'code': Path(f"src/{basename}.{get_extension(language)}"),
                'example': Path(f"context/{basename}_example.{get_extension(language)}"),
                'test': Path(f"tests/test_{basename}.{get_extension(language)}")
            }
            if not quiet:
                print(f"Note: Test file missing, continuing with sync workflow to generate it")
        else:
            print(f"Error constructing paths: {e}")
            return {
                "success": False,
                "error": f"Failed to construct paths: {str(e)}",
                "operations_completed": [],
                "errors": [f"Path construction failed: {str(e)}"]
            }
    except Exception as e:
        print(f"Error constructing paths: {e}")
        return {
            "success": False,
            "error": f"Failed to construct paths: {str(e)}",
            "operations_completed": [],
            "errors": [f"Path construction failed: {str(e)}"]
        }
    
    # Shared state for animation (passed to App)
    current_function_name_ref = ["initializing"]
    stop_event = threading.Event()
    current_cost_ref = [0.0]
    prompt_path_ref = [str(pdd_files.get('prompt', 'N/A'))]
    code_path_ref = [str(pdd_files.get('code', 'N/A'))]
    example_path_ref = [str(pdd_files.get('example', 'N/A'))]
    tests_path_ref = [str(pdd_files.get('test', 'N/A'))]
    prompt_box_color_ref = ["blue"]
    code_box_color_ref = ["blue"]
    example_box_color_ref = ["blue"]
    tests_box_color_ref = ["blue"]

    # Mutable container for the app reference (set after app creation)
    # This allows the worker to access app.request_confirmation()
    app_ref: List[Optional['SyncApp']] = [None]

    # Progress callback ref for TUI ProgressBar updates during auto-deps
    progress_callback_ref: List[Optional[Callable[[int, int], None]]] = [None]

    # Track if user has already confirmed overwrite (to avoid asking multiple times)
    user_confirmed_overwrite: List[bool] = [False]

    def get_confirm_callback() -> Optional[Callable[[str, str], bool]]:
        """Get the confirmation callback from the app if available.

        Once user confirms, we remember it so subsequent operations don't ask again.
        """
        if user_confirmed_overwrite[0]:
            # User already confirmed, return a callback that always returns True
            return lambda msg, title: True

        if app_ref[0] is not None:
            def confirming_callback(msg: str, title: str) -> bool:
                result = app_ref[0].request_confirmation(msg, title)
                if result:
                    user_confirmed_overwrite[0] = True
                return result
            return confirming_callback
        return confirm_callback  # Fall back to provided callback

    def sync_worker_logic():
        """
        The main loop of sync logic, run in a worker thread by Textual App.
        """
        operations_completed: List[str] = []
        skipped_operations: List[str] = []
        errors: List[str] = []
        start_time = time.time()
        last_model_name: str = ""
        operation_history: List[str] = []
        MAX_CYCLE_REPEATS = 2
        
        # Helper function to print inside worker (goes to RichLog via redirection)
        # print() will work if sys.stdout is redirected.
        
        try:
            with SyncLock(basename, language):
                log_sync_event(basename, language, "lock_acquired", {"pid": os.getpid()})
                
                while True:
                    budget_remaining = budget - current_cost_ref[0]
                    if current_cost_ref[0] >= budget:
                        errors.append(f"Budget of ${budget:.2f} exceeded.")
                        log_sync_event(basename, language, "budget_exceeded", {
                            "total_cost": current_cost_ref[0], 
                            "budget": budget
                        })
                        break

                    if budget_remaining < budget * 0.2 and budget_remaining > 0:
                        log_sync_event(basename, language, "budget_warning", {
                            "remaining": budget_remaining,
                            "percentage": (budget_remaining / budget) * 100
                        })

                    decision = sync_determine_operation(basename, language, target_coverage, budget_remaining, False, prompts_dir, skip_tests, skip_verify, context_override)
                    operation = decision.operation
                    
                    log_entry = create_sync_log_entry(decision, budget_remaining)
                    operation_history.append(operation)
                    
                    # Cycle detection logic
                    if len(operation_history) >= 3:
                        recent_auto_deps = [op for op in operation_history[-3:] if op == 'auto-deps']
                        if len(recent_auto_deps) >= 2:
                            errors.append("Detected auto-deps infinite loop. Force advancing to generate operation.")
                            log_sync_event(basename, language, "cycle_detected", {"cycle_type": "auto-deps-infinite"})
                            operation = 'generate'
                            decision.operation = 'generate' # Update decision too

                    # Bug #4 fix: Detect crash-verify cycle pattern
                    # The pattern [crash, verify, crash, verify] or [verify, crash, verify, crash]
                    # represents 2 iterations of the alternating cycle, so break immediately
                    if len(operation_history) >= 4:
                        recent_ops = operation_history[-4:]
                        if (recent_ops == ['crash', 'verify', 'crash', 'verify'] or
                            recent_ops == ['verify', 'crash', 'verify', 'crash']):
                            # Pattern detected - this represents MAX_CYCLE_REPEATS iterations
                            errors.append(f"Detected crash-verify cycle repeated {MAX_CYCLE_REPEATS} times. Breaking cycle.")
                            log_sync_event(basename, language, "cycle_detected", {"cycle_type": "crash-verify", "count": MAX_CYCLE_REPEATS})
                            break

                    # Bug #4 fix: Detect test-fix cycle pattern
                    # The pattern [test, fix, test, fix] or [fix, test, fix, test]
                    # represents 2 iterations of the alternating cycle, so break immediately
                    if len(operation_history) >= 4:
                        recent_ops = operation_history[-4:]
                        if (recent_ops == ['test', 'fix', 'test', 'fix'] or
                            recent_ops == ['fix', 'test', 'fix', 'test']):
                            # Pattern detected - this represents MAX_CYCLE_REPEATS iterations
                            errors.append(f"Detected test-fix cycle repeated {MAX_CYCLE_REPEATS} times. Breaking cycle.")
                            log_sync_event(basename, language, "cycle_detected", {"cycle_type": "test-fix", "count": MAX_CYCLE_REPEATS})
                            break
                                
                    if operation == 'fix':
                        consecutive_fixes = 0
                        for i in range(len(operation_history) - 1, -1, -1):
                            if operation_history[i] == 'fix':
                                consecutive_fixes += 1
                            else:
                                break
                        if consecutive_fixes >= 5:
                            errors.append(f"Detected {consecutive_fixes} consecutive fix operations. Breaking infinite fix loop.")
                            break

                    if operation == 'test':
                        consecutive_tests = 0
                        for i in range(len(operation_history) - 1, -1, -1):
                            if operation_history[i] == 'test':
                                consecutive_tests += 1
                            else:
                                break
                        if consecutive_tests >= MAX_CONSECUTIVE_TESTS:
                            errors.append(f"Detected {consecutive_tests} consecutive test operations. Breaking infinite test loop.")
                            break

                    # Bug #157 fix: Prevent infinite crash retry loops
                    if operation == 'crash':
                        consecutive_crashes = 0
                        for i in range(len(operation_history) - 1, -1, -1):
                            if operation_history[i] == 'crash':
                                consecutive_crashes += 1
                            else:
                                break
                        if consecutive_crashes >= MAX_CONSECUTIVE_CRASHES:
                            errors.append(f"Detected {consecutive_crashes} consecutive crash operations. Breaking infinite crash loop.")
                            break

                    if operation == 'test_extend':
                        # Count test_extend attempts to prevent infinite loop
                        extend_attempts = sum(1 for op in operation_history if op == 'test_extend')
                        if extend_attempts >= MAX_TEST_EXTEND_ATTEMPTS:
                            # Accept current coverage after max attempts
                            log_sync_event(basename, language, "test_extend_limit", {
                                "attempts": extend_attempts,
                                "max_attempts": MAX_TEST_EXTEND_ATTEMPTS,
                                "reason": "Accepting current coverage after max extend attempts"
                            })
                            success = True
                            break

                    if operation in ['all_synced', 'nothing', 'fail_and_request_manual_merge', 'error', 'analyze_conflict']:
                        current_function_name_ref[0] = "synced" if operation in ['all_synced', 'nothing'] else "conflict"
                        success = operation in ['all_synced', 'nothing']
                        error_msg = None
                        if operation == 'fail_and_request_manual_merge':
                            errors.append(f"Manual merge required: {decision.reason}")
                            error_msg = decision.reason
                        elif operation == 'error':
                            errors.append(f"Error determining operation: {decision.reason}")
                            error_msg = decision.reason
                        elif operation == 'analyze_conflict':
                            errors.append(f"Conflict detected: {decision.reason}")
                            error_msg = decision.reason
                        
                        update_sync_log_entry(log_entry, {'success': success, 'cost': 0.0, 'model': 'none', 'error': error_msg}, 0.0)
                        append_sync_log(basename, language, log_entry)
                        break
                    
                    # Handle skips - save fingerprint with 'skip:' prefix to distinguish from actual execution
                    # Bug #11 fix: Use 'skip:' prefix so _is_workflow_complete() knows the op was skipped
                    if operation == 'verify' and (skip_verify or skip_tests):
                        skipped_operations.append('verify')
                        update_sync_log_entry(log_entry, {'success': True, 'cost': 0.0, 'model': 'skipped', 'error': None}, 0.0)
                        append_sync_log(basename, language, log_entry)
                        # Save fingerprint with 'skip:' prefix to indicate operation was skipped, not executed
                        _save_operation_fingerprint(basename, language, 'skip:verify', pdd_files, 0.0, 'skipped')
                        continue
                    if operation == 'test' and skip_tests:
                        skipped_operations.append('test')
                        update_sync_log_entry(log_entry, {'success': True, 'cost': 0.0, 'model': 'skipped', 'error': None}, 0.0)
                        append_sync_log(basename, language, log_entry)
                        # Save fingerprint with 'skip:' prefix to indicate operation was skipped, not executed
                        _save_operation_fingerprint(basename, language, 'skip:test', pdd_files, 0.0, 'skipped')
                        continue
                    if operation == 'crash' and (skip_tests or skip_verify):
                        skipped_operations.append('crash')
                        update_sync_log_entry(log_entry, {'success': True, 'cost': 0.0, 'model': 'skipped', 'error': None}, 0.0)
                        append_sync_log(basename, language, log_entry)
                        # Save fingerprint with 'skip:' prefix to indicate operation was skipped, not executed
                        _save_operation_fingerprint(basename, language, 'skip:crash', pdd_files, 0.0, 'skipped')
                        # FIX: Create a synthetic run_report to prevent infinite loop when crash is skipped
                        # Without this, sync_determine_operation keeps returning 'crash' because no run_report exists
                        current_hashes = calculate_current_hashes(pdd_files)
                        synthetic_report = RunReport(
                            timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                            exit_code=0,  # Assume success since we're skipping validation
                            tests_passed=0,
                            tests_failed=0,
                            coverage=0.0,
                            test_hash=current_hashes.get('test_hash')
                        )
                        save_run_report(asdict(synthetic_report), basename, language)
                        continue

                    current_function_name_ref[0] = operation
                    ctx = _create_mock_context(
                        force=force, strength=strength, temperature=temperature, time=time_param,
                        verbose=verbose, quiet=quiet, output_cost=output_cost,
                        review_examples=review_examples, local=local, budget=budget - current_cost_ref[0],
                        max_attempts=max_attempts, target_coverage=target_coverage,
                        confirm_callback=get_confirm_callback(),
                        context=context_override
                    )
                    
                    result = {}
                    success = False
                    op_start_time = time.time()

                    # Issue #159 fix: Use atomic state for consistent run_report + fingerprint writes
                    with AtomicStateUpdate(basename, language) as atomic_state:

                        # --- Execute Operation ---
                        try:
                            if operation == 'auto-deps':
                                temp_output = str(pdd_files['prompt']).replace('.prompt', '_with_deps.prompt')
                                original_content = pdd_files['prompt'].read_text(encoding='utf-8')
                                result = auto_deps_main(
                                    ctx,
                                    prompt_file=str(pdd_files['prompt']),
                                    directory_path=examples_dir,
                                    auto_deps_csv_path="project_dependencies.csv",
                                    output=temp_output,
                                    force_scan=False,
                                    progress_callback=progress_callback_ref[0]
                                )
                                if Path(temp_output).exists():
                                    import shutil
                                    new_content = Path(temp_output).read_text(encoding='utf-8')
                                    if new_content != original_content:
                                        shutil.move(temp_output, str(pdd_files['prompt']))
                                    else:
                                        Path(temp_output).unlink()
                                        result = (new_content, 0.0, 'no-changes')
                            elif operation == 'generate':
                                # Ensure code directory exists before generating
                                pdd_files['code'].parent.mkdir(parents=True, exist_ok=True)
                                # Use absolute paths to avoid path_resolution_mode mismatch between sync (cwd) and generate (config_base)
                                result = code_generator_main(ctx, prompt_file=str(pdd_files['prompt'].resolve()), output=str(pdd_files['code'].resolve()), original_prompt_file_path=None, force_incremental_flag=False)
                                # Clear stale run_report so crash/verify is required for newly generated code
                                run_report_file = META_DIR / f"{_safe_basename(basename)}_{language}_run.json"
                                run_report_file.unlink(missing_ok=True)
                            elif operation == 'example':
                                # Ensure example directory exists before generating
                                pdd_files['example'].parent.mkdir(parents=True, exist_ok=True)
                                # Use absolute paths to avoid path_resolution_mode mismatch between sync (cwd) and example (config_base)
                                result = context_generator_main(ctx, prompt_file=str(pdd_files['prompt'].resolve()), code_file=str(pdd_files['code'].resolve()), output=str(pdd_files['example'].resolve()))
                            elif operation == 'crash':
                                required_files = [pdd_files['code'], pdd_files['example']]
                                missing_files = [f for f in required_files if not f.exists()]
                                if missing_files:
                                    skipped_operations.append('crash')
                                    continue
                            
                                # Crash handling logic (simplified copy from original)
                                current_run_report = read_run_report(basename, language)
                                crash_log_content = ""
                            
                                # Check for crash condition (either run report says so, or we check manually)
                                has_crash = False
                                if current_run_report and current_run_report.exit_code != 0:
                                    has_crash = True
                                    crash_log_content = f"Test execution failed exit code: {current_run_report.exit_code}\n"
                                else:
                                    # Manual check - run the example to see if it crashes
                                    env = os.environ.copy()
                                    src_dir = Path.cwd() / 'src'
                                    env['PYTHONPATH'] = f"{src_dir}:{env.get('PYTHONPATH', '')}"
                                    # Remove TUI-specific env vars that might contaminate subprocess
                                    for var in ['FORCE_COLOR', 'COLUMNS']:
                                        env.pop(var, None)
                                    # Get language-appropriate run command from language_format.csv
                                    example_path = str(pdd_files['example'])
                                    run_cmd = get_run_command_for_file(example_path)
                                    if run_cmd:
                                        # Use the language-specific interpreter (e.g., node for .js)
                                        cmd_parts = run_cmd.split()
                                    else:
                                        # Fallback to Python if no run command found
                                        cmd_parts = ['python', example_path]
                                    # Use error-detection runner that handles server-style examples
                                    returncode, stdout, stderr = _run_example_with_error_detection(
                                        cmd_parts,
                                        env=env,
                                        cwd=str(pdd_files['example'].parent),
                                        timeout=60
                                    )

                                    class ExampleResult:
                                        def __init__(self, rc, out, err):
                                            self.returncode = rc
                                            self.stdout = out
                                            self.stderr = err

                                    ex_res = ExampleResult(returncode, stdout, stderr)
                                    if ex_res.returncode != 0:
                                        has_crash = True
                                        crash_log_content = f"Example failed exit code: {ex_res.returncode}\nSTDOUT:\n{ex_res.stdout}\nSTDERR:\n{ex_res.stderr}\n"
                                        if "SyntaxError" in ex_res.stderr:
                                             crash_log_content = "SYNTAX ERROR DETECTED:\n" + crash_log_content
                                    else:
                                        # No crash - save run report with exit_code=0 so sync_determine_operation
                                        # knows the example was tested and passed (prevents infinite loop)
                                        # Include test_hash for staleness detection
                                        test_hash = calculate_sha256(pdd_files['test']) if pdd_files['test'].exists() else None
                                        report = RunReport(
                                            datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                            exit_code=0,
                                            tests_passed=1,
                                            tests_failed=0,
                                            coverage=0.0,
                                            test_hash=test_hash
                                        )
                                        save_run_report(asdict(report), basename, language)
                                        skipped_operations.append('crash')
                                        continue
                                    
                                if has_crash:
                                    # Try auto-fix for common import errors before expensive agentic call
                                    auto_fixed, auto_fix_msg = _try_auto_fix_import_error(
                                        crash_log_content,
                                        pdd_files['code'],
                                        pdd_files['example']
                                    )
                                    if auto_fixed:
                                        log_sync_event(basename, language, "auto_fix_attempted", {"message": auto_fix_msg})
                                        # Retry running the example after auto-fix
                                        retry_returncode, retry_stdout, retry_stderr = _run_example_with_error_detection(
                                            cmd_parts,
                                            env=env,
                                            cwd=str(pdd_files['example'].parent),
                                            timeout=60
                                        )
                                        if retry_returncode == 0:
                                            # Auto-fix worked! Save run report and continue
                                            log_sync_event(basename, language, "auto_fix_success", {"message": auto_fix_msg})
                                            test_hash = calculate_sha256(pdd_files['test']) if pdd_files['test'].exists() else None
                                            report = RunReport(
                                                datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                                exit_code=0,
                                                tests_passed=1,
                                                tests_failed=0,
                                                coverage=0.0,
                                                test_hash=test_hash
                                            )
                                            save_run_report(asdict(report), basename, language)
                                            result = (True, 0.0, 'auto-fix')
                                            success = True
                                            actual_cost = 0.0
                                            model_name = 'auto-fix'
                                            # Update crash_log_content for logging
                                            crash_log_content = f"Auto-fixed: {auto_fix_msg}"
                                            continue  # Skip crash_main, move to next operation
                                        else:
                                            # Auto-fix didn't fully work, update error log and proceed
                                            crash_log_content = f"Auto-fix attempted ({auto_fix_msg}) but still failing:\nRETRY STDOUT:\n{retry_stdout}\nRETRY STDERR:\n{retry_stderr}\n"

                                    Path("crash.log").write_text(crash_log_content)
                                    try:
                                        # For non-Python languages, set max_attempts=0 to skip iterative loop
                                        # and go directly to agentic fallback
                                        effective_max_attempts = 0 if language.lower() != 'python' else max_attempts
                                        result = crash_main(ctx, prompt_file=str(pdd_files['prompt']), code_file=str(pdd_files['code']), program_file=str(pdd_files['example']), error_file="crash.log", output=str(pdd_files['code']), output_program=str(pdd_files['example']), loop=True, max_attempts=effective_max_attempts, budget=budget - current_cost_ref[0], strength=strength, temperature=temperature)
                                    except Exception as e:
                                        print(f"Crash fix failed: {e}")
                                        skipped_operations.append('crash')
                                        continue

                            elif operation == 'verify':
                                if not pdd_files['example'].exists():
                                    skipped_operations.append('verify')
                                    continue
                                # For non-Python languages, set max_attempts=0 to skip iterative loop
                                # and go directly to agentic fallback
                                effective_max_attempts = 0 if language.lower() != 'python' else max_attempts
                                result = fix_verification_main(ctx, prompt_file=str(pdd_files['prompt']), code_file=str(pdd_files['code']), program_file=str(pdd_files['example']), output_results=f"{basename}_verify_results.log", output_code=str(pdd_files['code']), output_program=str(pdd_files['example']), loop=True, verification_program=str(pdd_files['example']), max_attempts=effective_max_attempts, budget=budget - current_cost_ref[0], strength=strength, temperature=temperature)
                            elif operation == 'test':
                                pdd_files['test'].parent.mkdir(parents=True, exist_ok=True)
                                # Use merge=True when test file exists to preserve fixes and append new tests
                                # instead of regenerating from scratch (which would overwrite fixes)
                                test_file_exists = pdd_files['test'].exists()
                                result = cmd_test_main(ctx, prompt_file=str(pdd_files['prompt']), code_file=str(pdd_files['code']), output=str(pdd_files['test']), language=language, coverage_report=None, existing_tests=[str(pdd_files['test'])] if test_file_exists else None, target_coverage=target_coverage, merge=test_file_exists, strength=strength, temperature=temperature)
                                if pdd_files['test'].exists():
                                    _execute_tests_and_create_run_report(
                                        pdd_files['test'],
                                        basename,
                                        language,
                                        target_coverage,
                                        code_file=pdd_files.get("code"),
                                        atomic_state=atomic_state,
                                        test_files=pdd_files.get('test_files'),  # Bug #156
                                    )
                            elif operation == 'test_extend':
                                # Extend existing tests to improve coverage
                                # Uses existing_tests and merge=True to add more test cases
                                pdd_files['test'].parent.mkdir(parents=True, exist_ok=True)
                                if pdd_files['test'].exists():
                                    existing_test_path = str(pdd_files['test'])
                                    result = cmd_test_main(
                                        ctx,
                                        prompt_file=str(pdd_files['prompt']),
                                        code_file=str(pdd_files['code']),
                                        output=str(pdd_files['test']),
                                        language=language,
                                        coverage_report=None,
                                        existing_tests=[existing_test_path],
                                        target_coverage=target_coverage,
                                        merge=True,
                                        strength=strength,
                                        temperature=temperature
                                    )
                                    _execute_tests_and_create_run_report(
                                        pdd_files['test'],
                                        basename,
                                        language,
                                        target_coverage,
                                        code_file=pdd_files.get("code"),
                                        atomic_state=atomic_state,
                                        test_files=pdd_files.get('test_files'),  # Bug #156
                                    )
                                else:
                                    # No existing test file, fall back to regular test generation
                                    result = cmd_test_main(ctx, prompt_file=str(pdd_files['prompt']), code_file=str(pdd_files['code']), output=str(pdd_files['test']), language=language, coverage_report=None, existing_tests=None, target_coverage=target_coverage, merge=False, strength=strength, temperature=temperature)
                                    if pdd_files['test'].exists():
                                        _execute_tests_and_create_run_report(
                                            pdd_files['test'],
                                            basename,
                                            language,
                                            target_coverage,
                                            code_file=pdd_files.get("code"),
                                            atomic_state=atomic_state,
                                            test_files=pdd_files.get('test_files'),  # Bug #156
                                        )
                            elif operation == 'fix':
                                error_file_path = Path("fix_errors.log")
                                # Capture errors using language-appropriate test command
                                try:
                                    from .get_test_command import get_test_command_for_file
                                    test_cmd = get_test_command_for_file(str(pdd_files['test']), language)

                                    # Use clean env without TUI-specific vars
                                    clean_env = os.environ.copy()
                                    for var in ['FORCE_COLOR', 'COLUMNS']:
                                        clean_env.pop(var, None)

                                    if test_cmd:
                                        # Run language-appropriate test command
                                        if language.lower() == 'python':
                                            # Use pytest directly for Python
                                            python_executable = detect_host_python_executable()
                                            # Bug #156: Run pytest on ALL matching test files
                                            test_files = pdd_files.get('test_files', [pdd_files['test']])
                                            pytest_args = [python_executable, '-m', 'pytest'] + [str(f) for f in test_files] + ['-v', '--tb=short']
                                            test_result = subprocess.run(
                                                pytest_args,
                                                capture_output=True, text=True, timeout=300,
                                                stdin=subprocess.DEVNULL, env=clean_env, start_new_session=True,
                                                cwd=str(pdd_files['test'].parent)
                                            )
                                        else:
                                            # Use shell command for non-Python
                                            test_result = subprocess.run(
                                                test_cmd,
                                                shell=True,
                                                capture_output=True, text=True, timeout=300,
                                                stdin=subprocess.DEVNULL, env=clean_env,
                                                cwd=str(pdd_files['test'].parent),
                                                start_new_session=True
                                            )
                                        error_content = f"Test output:\n{test_result.stdout}\n{test_result.stderr}"
                                    else:
                                        # No test command available - trigger agentic fallback with context
                                        error_content = f"No test command available for {language}. Please run tests manually and provide error output."
                                except Exception as e:
                                    error_content = f"Test execution error: {e}"
                                error_file_path.write_text(error_content)

                                # Bug #156 fix: Parse pytest output to find actual failing files
                                # and pass the correct file to fix_main
                                failing_files = extract_failing_files_from_output(error_content)
                                unit_test_file_for_fix = str(pdd_files['test'])  # Default to tracked file

                                if failing_files:
                                    # Try to resolve the failing file paths
                                    test_dir = pdd_files['test'].parent
                                    tracked_file_name = pdd_files['test'].name

                                    # Check if the tracked file is among the failures
                                    tracked_in_failures = any(
                                        Path(ff).name == tracked_file_name for ff in failing_files
                                    )

                                    if not tracked_in_failures:
                                        # Failures are in a different file - use the first failing file
                                        for ff in failing_files:
                                            # Try to resolve the path relative to test directory
                                            ff_path = Path(ff)
                                            if ff_path.is_absolute() and ff_path.exists():
                                                unit_test_file_for_fix = str(ff_path)
                                                break
                                            else:
                                                # Try to find it in the test directory
                                                candidate = test_dir / ff_path.name
                                                if candidate.exists():
                                                    unit_test_file_for_fix = str(candidate)
                                                    break
                                                # Also try the path as-is relative to cwd
                                                if ff_path.exists():
                                                    unit_test_file_for_fix = str(ff_path.resolve())
                                                    break

                                # For non-Python languages, set max_attempts=0 to skip iterative loop
                                # and go directly to agentic fallback
                                effective_max_attempts = 0 if language.lower() != 'python' else max_attempts
                                result = fix_main(ctx, prompt_file=str(pdd_files['prompt']), code_file=str(pdd_files['code']), unit_test_file=unit_test_file_for_fix, error_file=str(error_file_path), output_test=str(pdd_files['test']), output_code=str(pdd_files['code']), output_results=f"{basename}_fix_results.log", loop=True, verification_program=str(pdd_files['example']), max_attempts=effective_max_attempts, budget=budget - current_cost_ref[0], auto_submit=True, strength=strength, temperature=temperature)
                            elif operation == 'update':
                                result = update_main(ctx, input_prompt_file=str(pdd_files['prompt']), modified_code_file=str(pdd_files['code']), input_code_file=None, output=str(pdd_files['prompt']), use_git=True, strength=strength, temperature=temperature)
                            else:
                                errors.append(f"Unknown operation {operation}")
                                result = {'success': False}

                            # Result parsing
                            if isinstance(result, dict):
                                success = result.get('success', False)
                                current_cost_ref[0] += result.get('cost', 0.0)
                            elif isinstance(result, tuple) and len(result) >= 3:
                                if operation == 'test': success = pdd_files['test'].exists()
                                else: success = bool(result[0])
                                cost = result[-2] if len(result) >= 2 and isinstance(result[-2], (int, float)) else 0.0
                                current_cost_ref[0] += cost
                            else:
                                success = result is not None

                        except Exception as e:
                            errors.append(f"Exception during '{operation}': {e}")
                            success = False
                    
                        # Log update
                        duration = time.time() - op_start_time
                        actual_cost = 0.0
                        model_name = "unknown"
                        if success:
                            if isinstance(result, dict):
                                 actual_cost = result.get('cost', 0.0)
                                 model_name = result.get('model', 'unknown')
                            elif isinstance(result, tuple) and len(result) >= 3:
                                 actual_cost = result[-2] if len(result) >= 2 else 0.0
                                 model_name = result[-1] if len(result) >= 1 else 'unknown'
                            last_model_name = str(model_name)
                            operations_completed.append(operation)
                            _save_operation_fingerprint(basename, language, operation, pdd_files, actual_cost, str(model_name), atomic_state=atomic_state)

                        update_sync_log_entry(log_entry, {'success': success, 'cost': actual_cost, 'model': model_name, 'error': errors[-1] if errors and not success else None}, duration)
                        append_sync_log(basename, language, log_entry)

                        # Post-operation checks (simplified)
                        if success and operation == 'crash':
                            # Re-run example to verify crash fix worked
                            try:
                                 # Use clean env without TUI-specific vars
                                 clean_env = os.environ.copy()
                                 for var in ['FORCE_COLOR', 'COLUMNS']:
                                     clean_env.pop(var, None)
                                 # Get language-appropriate run command
                                 example_path = str(pdd_files['example'])
                                 run_cmd = get_run_command_for_file(example_path)
                                 if run_cmd:
                                     cmd_parts = run_cmd.split()
                                 else:
                                     cmd_parts = ['python', example_path]
                                 # Use error-detection runner that handles server-style examples
                                 returncode, stdout, stderr = _run_example_with_error_detection(
                                     cmd_parts,
                                     env=clean_env,
                                     cwd=str(pdd_files['example'].parent),
                                     timeout=60
                                 )
                                 # Include test_hash for staleness detection
                                 test_hash = calculate_sha256(pdd_files['test']) if pdd_files['test'].exists() else None
                                 report = RunReport(datetime.datetime.now(datetime.timezone.utc).isoformat(), returncode, 1 if returncode==0 else 0, 0 if returncode==0 else 1, 100.0 if returncode==0 else 0.0, test_hash=test_hash)
                                 save_run_report(asdict(report), basename, language)
                            except Exception as e:
                                 # Bug #8 fix: Don't silently swallow exceptions - log them and mark as error
                                 error_msg = f"Post-crash verification failed: {e}"
                                 errors.append(error_msg)
                                 log_sync_event(basename, language, "post_crash_verification_failed", {"error": str(e)})
                    
                        if success and operation == 'fix':
                            # Re-run tests to update run_report after successful fix
                            # This prevents infinite loop by updating the state machine
                            if pdd_files['test'].exists():
                                _execute_tests_and_create_run_report(
                                    pdd_files['test'],
                                    basename,
                                    language,
                                    target_coverage,
                                    code_file=pdd_files.get("code"),
                                    atomic_state=atomic_state,
                                    test_files=pdd_files.get('test_files'),  # Bug #156
                                )
                    
                        if not success:
                            errors.append(f"Operation '{operation}' failed.")
                            break

        except BaseException as e:
            errors.append(f"An unexpected error occurred in the orchestrator: {type(e).__name__}: {e}")
            # Log the full traceback for debugging
            import traceback
            traceback.print_exc()
        finally:
            try:
                log_sync_event(basename, language, "lock_released", {"pid": os.getpid(), "total_cost": current_cost_ref[0]})
            except: pass
            
        # Return result dict
        return {
            'success': not errors,
            'operations_completed': operations_completed,
            'skipped_operations': skipped_operations,
            'total_cost': current_cost_ref[0],
            'total_time': time.time() - start_time,
            'final_state': {p: {'exists': f.exists(), 'path': str(f)} for p, f in pdd_files.items() if p != 'test_files'},
            'errors': errors,
            'error': "; ".join(errors) if errors else None,  # Add this line
            'model_name': last_model_name,
        }

    # Detect headless mode (no TTY, CI environment, or quiet mode)
    headless = quiet or not sys.stdout.isatty() or os.environ.get('CI')

    if headless:
        # Set PDD_FORCE to also skip API key prompts in headless mode
        os.environ['PDD_FORCE'] = '1'
        # Run worker logic directly without TUI in headless mode
        if not quiet:
            print(f"Running sync in headless mode (CI/non-TTY environment)...")
        result = sync_worker_logic()
        # No TUI app, so no worker_exception to check
        worker_exception = None
    else:
        # Instantiate and run Textual App
        app = SyncApp(
            basename=basename,
            budget=budget,
            worker_func=sync_worker_logic,
            function_name_ref=current_function_name_ref,
            cost_ref=current_cost_ref,
            prompt_path_ref=prompt_path_ref,
            code_path_ref=code_path_ref,
            example_path_ref=example_path_ref,
            tests_path_ref=tests_path_ref,
            prompt_color_ref=prompt_box_color_ref,
            code_color_ref=code_box_color_ref,
            example_color_ref=example_box_color_ref,
            tests_color_ref=tests_box_color_ref,
            stop_event=stop_event,
            progress_callback_ref=progress_callback_ref
        )

        # Store app reference so worker can access request_confirmation
        app_ref[0] = app

        result = app.run()

        # Show exit animation if not quiet
        from .sync_tui import show_exit_animation
        show_exit_animation()

        worker_exception = app.worker_exception

    # Check for worker exception that might have caused a crash (TUI mode only)
    if not headless and worker_exception:
        print(f"\n[Error] Worker thread crashed with exception: {worker_exception}", file=sys.stderr)

        if hasattr(app, 'captured_logs') and app.captured_logs:
             print("\n[Captured Logs (last 20 lines)]", file=sys.stderr)
             for line in app.captured_logs[-20:]: # Print last 20 lines
                 print(f"  {line}", file=sys.stderr)

        import traceback
        # Use trace module to print the stored exception's traceback if available
        if hasattr(worker_exception, '__traceback__'):
            traceback.print_exception(type(worker_exception), worker_exception, worker_exception.__traceback__, file=sys.stderr)

    if result is None:
        return {
            "success": False,
            "total_cost": current_cost_ref[0],
            "model_name": "",
            "error": "Sync process interrupted or returned no result.",
            "operations_completed": [],
            "errors": ["App exited without result"]
        }
    
    return result

if __name__ == '__main__':
    # Example usage
    Path("./prompts").mkdir(exist_ok=True)
    Path("./src").mkdir(exist_ok=True)
    Path("./examples").mkdir(exist_ok=True)
    Path("./tests").mkdir(exist_ok=True)
    Path("./prompts/my_calculator_python.prompt").write_text("Create a calculator.")
    PDD_DIR.mkdir(exist_ok=True)
    META_DIR.mkdir(exist_ok=True)
    result = sync_orchestration(basename="my_calculator", language="python", quiet=True)
    print(json.dumps(result, indent=2))
