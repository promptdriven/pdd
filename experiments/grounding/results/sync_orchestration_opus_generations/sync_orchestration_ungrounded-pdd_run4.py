"""
PDD Sync Orchestration Module

Orchestrates the complete PDD sync workflow by coordinating operations
and animations in parallel. Works with sync_main (CLI/path resolution),
sync_tui (Textual TUI), and sync_determine_operation (decision engine).
"""

import threading
import time
import json
import datetime
import subprocess
import re
import os
import sys
import logging
import tempfile
from pathlib import Path
from typing import Dict, Any, Optional, List, Callable
from dataclasses import asdict, dataclass, field

import click

from .sync_tui import maybe_steer_operation, DEFAULT_STEER_TIMEOUT_S
from .sync_tui import SyncApp
from .operation_log import (
    load_operation_log,
    create_log_entry,
    update_log_entry,
    append_log_entry,
    log_event,
    save_fingerprint,
    save_run_report,
    clear_run_report,
)
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
from .pytest_output import extract_failing_files_from_output, _find_project_root
from . import DEFAULT_STRENGTH

logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------
MAX_CONSECUTIVE_TESTS = 3
MAX_TEST_EXTEND_ATTEMPTS = 2
MAX_CONSECUTIVE_CRASHES = 3


# ---------------------------------------------------------------------------
# AtomicStateUpdate context manager
# ---------------------------------------------------------------------------
class AtomicStateUpdate:
    """Batches fingerprint and run-report writes so both land or neither does.

    Uses temp-file + atomic-rename internally for crash safety.
    """

    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self._pending_fingerprint_kwargs: Optional[Dict[str, Any]] = None
        self._pending_run_report: Optional[Dict[str, Any]] = None

    def __enter__(self) -> "AtomicStateUpdate":
        return self

    def queue_fingerprint(self, **kwargs: Any) -> None:
        self._pending_fingerprint_kwargs = kwargs

    def queue_run_report(self, report_data: Dict[str, Any]) -> None:
        self._pending_run_report = report_data

    def flush(self) -> None:
        meta = Path(META_DIR)
        meta.mkdir(parents=True, exist_ok=True)
        safe_bn = _safe_basename(self.basename)
        lang_lower = self.language.lower()

        try:
            if self._pending_run_report is not None:
                target = meta / f"{safe_bn}_{lang_lower}_run.json"
                fd, tmp = tempfile.mkstemp(
                    dir=str(meta), suffix=".tmp", prefix="run_"
                )
                try:
                    with os.fdopen(fd, "w", encoding="utf-8") as fh:
                        json.dump(self._pending_run_report, fh)
                    os.replace(tmp, str(target))
                except BaseException:
                    if os.path.exists(tmp):
                        os.unlink(tmp)
                    raise
                self._pending_run_report = None

            if self._pending_fingerprint_kwargs is not None:
                save_fingerprint(**self._pending_fingerprint_kwargs)
                self._pending_fingerprint_kwargs = None
        except Exception:
            import traceback as _tb

            logger.error("AtomicStateUpdate.flush failed:\n%s", _tb.format_exc())
            raise

    def __exit__(self, exc_type, exc_val, exc_tb):  # type: ignore[override]
        if exc_type is None:
            self.flush()
        return False


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Return *True* when the agentic code-path should be taken.

    This is the case for every non-Python language **and** for Python when
    ``agentic_mode`` has been explicitly requested.
    """
    return language.lower() != "python" or agentic_mode


def _is_headless(quiet: bool) -> bool:
    if quiet:
        return True
    if os.environ.get("CI"):
        return True
    try:
        if not sys.stdin.isatty():
            return True
    except Exception:
        return True
    return False


def _get_confirm_callback_headless(
    user_confirmed_overwrite: List[bool],
) -> Callable[[str, str], bool]:
    """Return a ``confirm_callback`` for headless / non-TUI runs."""

    def _cb(_filename: str, _message: str) -> bool:
        if user_confirmed_overwrite[0]:
            return True
        result = click.confirm(_message, default=True)
        if result:
            user_confirmed_overwrite[0] = True
        return result

    return _cb


def _get_confirm_callback_tui(
    app_ref: List[Any],
    user_confirmed_overwrite: List[bool],
) -> Callable[[str, str], bool]:
    """Return a ``confirm_callback`` that uses the TUI dialog."""

    def _cb(_filename: str, message: str) -> bool:
        if user_confirmed_overwrite[0]:
            return True
        if app_ref[0] is not None:
            result = app_ref[0].request_confirmation(message)
        else:
            result = True
        if result:
            user_confirmed_overwrite[0] = True
        return result

    return _cb


def _create_mock_context(
    *,
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time_param: float = 0.25,
    force: bool = False,
    quiet: bool = False,
    verbose: bool = False,
    local: bool = False,
    output_cost: Optional[str] = None,
    review_examples: bool = False,
    confirm_callback: Optional[Callable] = None,
    context_override: Optional[str] = None,
) -> click.Context:
    ctx = click.Context(click.Command("sync"))
    ctx.obj = {
        "strength": strength,
        "temperature": temperature,
        "time": time_param,
        "force": force,
        "quiet": quiet,
        "verbose": verbose,
        "context": context_override,
        "confirm_callback": confirm_callback,
    }
    ctx.params = {
        "local": local,
        "force": force,
        "quiet": quiet,
        "output_cost": output_cost,
        "review_examples": review_examples,
    }
    return ctx


# ---------------------------------------------------------------------------
# Display sync log (dry-run)
# ---------------------------------------------------------------------------

def _display_sync_log(basename: str, language: str, verbose: bool) -> List[Dict[str, Any]]:
    """Load and pretty-print the sync log; return raw entries."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync log entries for {basename}_{language.lower()}.")
        return entries

    for entry in entries:
        ts = entry.get("timestamp", "?")
        op = entry.get("operation", "?")
        reason = entry.get("reason", "")
        success = entry.get("success")
        cost = entry.get("actual_cost", entry.get("estimated_cost", 0))

        status = ""
        if success is True:
            status = click.style(" ✓", fg="green")
        elif success is False:
            status = click.style(" ✗", fg="red")

        line = f"  [{ts}] {op}{status}"
        if cost:
            line += f"  ${cost:.4f}"
        click.echo(line)

        if verbose:
            for key in ("decision_type", "confidence", "invocation_mode", "error"):
                val = entry.get(key)
                if val is not None:
                    click.echo(f"           {key}: {val}")
            if reason:
                click.echo(f"           reason: {reason}")

    return entries


# ---------------------------------------------------------------------------
# Test output parsing
# ---------------------------------------------------------------------------

def _parse_test_output(
    output: str, language: str
) -> tuple:
    """Parse test runner output → (tests_passed, tests_failed, coverage).

    Supports pytest, Jest/Vitest/Mocha, ``go test``, and ``cargo test``.
    """
    passed = 0
    failed = 0
    coverage: Optional[float] = None
    lang = language.lower()

    if lang == "python":
        m = re.search(r"(\d+) passed", output)
        if m:
            passed = int(m.group(1))
        m = re.search(r"(\d+) failed", output)
        if m:
            failed = int(m.group(1))
        m = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if m:
            coverage = float(m.group(1))
    elif lang in ("javascript", "typescript"):
        m = re.search(r"Tests:\s*(?:(\d+) failed,?\s*)?(?:(\d+) passed)", output)
        if m:
            failed = int(m.group(1) or 0)
            passed = int(m.group(2) or 0)
        else:
            m_pass = re.search(r"(\d+) passing", output)
            m_fail = re.search(r"(\d+) failing", output)
            if m_pass:
                passed = int(m_pass.group(1))
            if m_fail:
                failed = int(m_fail.group(1))
        m = re.search(r"All files\s*\|\s*[\d.]+\s*\|\s*[\d.]+\s*\|\s*[\d.]+\s*\|\s*([\d.]+)", output)
        if m:
            coverage = float(m.group(1))
    elif lang == "go":
        passed = len(re.findall(r"--- PASS:", output))
        failed = len(re.findall(r"--- FAIL:", output))
        m = re.search(r"coverage:\s*([\d.]+)%", output)
        if m:
            coverage = float(m.group(1))
    elif lang in ("rust",):
        m = re.search(r"test result:.*?(\d+) passed.*?(\d+) failed", output)
        if m:
            passed = int(m.group(1))
            failed = int(m.group(2))

    return passed, failed, coverage


# ---------------------------------------------------------------------------
# Python coverage helpers
# ---------------------------------------------------------------------------

def _python_cov_target_for_code_file(code_file: Optional[str]) -> Optional[str]:
    """Convert code file path to a dotted module path for ``--cov``."""
    if code_file is None:
        return None
    p = Path(code_file)
    parts = list(p.with_suffix("").parts)
    if parts and parts[0] == "src":
        parts = parts[1:]
    return ".".join(parts) if parts else None


def _python_cov_target_for_test_and_code(
    test_file: str,
    code_file: Optional[str],
    fallback: Optional[str],
) -> Optional[str]:
    """Analyze test imports to pick the best ``--cov`` target."""
    target = _python_cov_target_for_code_file(code_file)
    if target:
        return target

    try:
        content = Path(test_file).read_text(encoding="utf-8", errors="ignore")
        for m in re.finditer(
            r"(?:from|import)\s+([\w.]+)", content
        ):
            mod = m.group(1)
            if mod.startswith("test") or mod.startswith("_"):
                continue
            return mod.split(".")[0]
    except Exception:
        pass

    return fallback


# ---------------------------------------------------------------------------
# Test execution
# ---------------------------------------------------------------------------

def _execute_tests_and_create_run_report(
    test_file: str,
    basename: str,
    language: str,
    target_coverage: float,
    *,
    code_file: Optional[str] = None,
    atomic_state: Optional[AtomicStateUpdate] = None,
    test_files: Optional[List[str]] = None,
) -> RunReport:
    """Run tests, parse results, persist a ``RunReport``, and return it."""
    from .get_test_command import get_test_command_for_file

    lang_lower = language.lower()
    env = _subprocess_env()
    all_test_files: List[str] = list(test_files) if test_files else [test_file]

    if lang_lower == "python":
        python_exe = detect_host_python_executable()
        project_root = _find_project_root(test_file)

        cov_target = _python_cov_target_for_test_and_code(
            test_file, code_file, _safe_basename(basename)
        )

        cmd: List[str] = [python_exe, "-m", "pytest", "-x", "--tb=short", "-q"]
        if cov_target:
            cmd += [f"--cov={cov_target}", "--cov-report=term-missing"]
        if project_root:
            cmd += ["--rootdir", str(project_root), "-c", "/dev/null"]
            pypath_parts = [str(project_root)]
            src_dir = Path(project_root) / "src"
            if src_dir.is_dir():
                pypath_parts.append(str(src_dir))
            existing = env.get("PYTHONPATH", "")
            env["PYTHONPATH"] = os.pathsep.join(pypath_parts + ([existing] if existing else []))

        cmd += all_test_files
    else:
        test_cmd = get_test_command_for_file(test_file, language=language)
        if test_cmd is None:
            test_cmd = f"echo 'No test runner found for {language}'"
        cmd = test_cmd if isinstance(test_cmd, list) else test_cmd.split()

    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=300,
            env=env,
            start_new_session=True,
            stdin=subprocess.DEVNULL,
        )
        combined = (proc.stdout or "") + "\n" + (proc.stderr or "")
        exit_code = proc.returncode
    except subprocess.TimeoutExpired:
        combined = "Test execution timed out after 300s"
        exit_code = 1
    except Exception as exc:
        combined = str(exc)
        exit_code = 1

    passed, failed, coverage = _parse_test_output(combined, language)
    if coverage is None:
        coverage = 0.0

    test_hash: Optional[str] = None
    test_file_hashes: Optional[Dict[str, str]] = None
    if all_test_files:
        test_file_hashes = {}
        for tf in all_test_files:
            if Path(tf).exists():
                test_file_hashes[tf] = calculate_sha256(Path(tf))
        if test_file_hashes:
            test_hash = list(test_file_hashes.values())[0]

    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=exit_code,
        tests_passed=passed,
        tests_failed=failed,
        coverage=coverage,
        test_hash=test_hash,
    )
    if test_file_hashes and len(test_file_hashes) > 1:
        report.test_file_hashes = test_file_hashes  # type: ignore[attr-defined]

    report_dict = report.__dict__

    if atomic_state is not None:
        atomic_state.queue_run_report(report_dict)
    else:
        save_run_report(basename, language, report_dict)

    return report


# ---------------------------------------------------------------------------
# Example error detection & execution
# ---------------------------------------------------------------------------

def _detect_example_errors(output: str) -> Optional[str]:
    """Return a description of detected errors, or *None* if output looks clean."""
    if re.search(r"Traceback \(most recent call last\)", output):
        return "Python traceback detected"
    if re.search(r"\bERROR\b", output):
        return "ERROR log message detected"
    if re.search(r"SyntaxError:|NameError:|ImportError:|ModuleNotFoundError:", output):
        return "Python exception detected"
    return None


def _run_example_with_error_detection(
    example_file: str,
    code_file: str,
    language: str,
    timeout: int = 30,
) -> tuple:
    """Run *example_file*, return ``(success, stdout, stderr, exit_code)``."""
    lang_lower = language.lower()
    env = _subprocess_env()

    if lang_lower == "python":
        python_exe = detect_host_python_executable()
        cmd = [python_exe, example_file]
        project_root = _find_project_root(example_file) or _find_project_root(code_file)
        if project_root:
            pypath_parts = [str(project_root)]
            src_dir = Path(project_root) / "src"
            if src_dir.is_dir():
                pypath_parts.append(str(src_dir))
            existing = env.get("PYTHONPATH", "")
            env["PYTHONPATH"] = os.pathsep.join(pypath_parts + ([existing] if existing else []))
    else:
        run_cmd = get_run_command_for_file(example_file)
        if run_cmd is None:
            return False, "", f"No run command for {language}", 1
        cmd = run_cmd if isinstance(run_cmd, list) else run_cmd.split()

    try:
        proc = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
            start_new_session=True,
            stdin=subprocess.DEVNULL,
        )
        stdout = proc.stdout or ""
        stderr = proc.stderr or ""
        combined = stdout + "\n" + stderr
        error_desc = _detect_example_errors(combined)
        success = proc.returncode == 0 and error_desc is None
        return success, stdout, stderr, proc.returncode
    except subprocess.TimeoutExpired:
        # Server-style: might be expected
        return True, "", "Process timed out (may be server-style)", 0
    except Exception as exc:
        return False, "", str(exc), 1


def _try_auto_fix_import_error(
    stderr: str,
    code_file: str,
    example_file: str,
) -> bool:
    """Attempt auto-fix for common ImportError before expensive agentic calls.

    Returns *True* if an automatic fix was applied.
    """
    m = re.search(r"ModuleNotFoundError: No module named '(\w+)'", stderr)
    if not m:
        return False

    module_name = m.group(1)
    code_path = Path(code_file)
    if code_path.stem == module_name:
        # Add code directory to sys.path in example
        example_path = Path(example_file)
        if example_path.exists():
            content = example_path.read_text(encoding="utf-8")
            fix_line = f"import sys; sys.path.insert(0, {str(code_path.parent)!r})\n"
            if fix_line not in content:
                example_path.write_text(fix_line + content, encoding="utf-8")
                return True
    return False


def _create_synthetic_run_report_for_agentic_success(
    test_file: str,
    basename: str,
    language: str,
    *,
    atomic_state: Optional[AtomicStateUpdate] = None,
) -> RunReport:
    """Create a synthetic *passing* ``RunReport`` after agentic test success."""
    test_path = Path(test_file)
    if test_path.exists():
        test_hash = calculate_sha256(test_path)
    else:
        test_hash = "agentic_test_success"

    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=0,
        tests_passed=1,
        tests_failed=0,
        coverage=0.0,
        test_hash=test_hash,
    )
    report_dict = report.__dict__

    if atomic_state is not None:
        atomic_state.queue_run_report(report_dict)
    else:
        save_run_report(basename, language, report_dict)

    return report


# ---------------------------------------------------------------------------
# Subprocess environment helper
# ---------------------------------------------------------------------------

def _subprocess_env() -> Dict[str, str]:
    """Return a copy of ``os.environ`` with TUI variables stripped."""
    env = os.environ.copy()
    for key in ("FORCE_COLOR", "COLUMNS"):
        env.pop(key, None)
    return env


# ---------------------------------------------------------------------------
# Resolve PDD paths with error tolerance
# ---------------------------------------------------------------------------

def _resolve_pdd_paths(
    basename: str,
    language: str,
    prompts_dir: str,
    code_dir: str,
    examples_dir: str,
    tests_dir: str,
) -> Dict[str, Any]:
    """Call ``get_pdd_file_paths`` with graceful fallback for missing tests."""
    from .sync_determine_operation import get_pdd_file_paths  # already at module level

    try:
        return get_pdd_file_paths(
            basename, language, prompts_dir, code_dir, examples_dir, tests_dir
        )
    except FileNotFoundError as exc:
        msg = str(exc).lower()
        if "test" in msg:
            # Construct default paths manually
            from . import get_extension as _ge

            ext = _ge(language)
            # Case-insensitive prompt lookup
            prompt_file: Optional[Path] = None
            prompts_path = Path(prompts_dir)
            target_name = f"{basename}_{language}.prompt".lower()
            if prompts_path.is_dir():
                for candidate in prompts_path.iterdir():
                    if candidate.name.lower() == target_name:
                        prompt_file = candidate
                        break
            if prompt_file is None:
                prompt_file = prompts_path / f"{basename}_{language}.prompt"

            return {
                "prompt": prompt_file,
                "code": Path(code_dir) / f"{basename}.{ext}",
                "example": Path(examples_dir) / f"{basename}_example.{ext}",
                "test": Path(tests_dir) / f"test_{basename}.{ext}",
            }
        raise


# ---------------------------------------------------------------------------
# Extract cost / model from heterogeneous command results
# ---------------------------------------------------------------------------

def _extract_cost_model(
    result: Any, operation: Optional[str] = None
) -> tuple:
    """Return ``(cost, model)`` from a command result in any supported format."""
    if isinstance(result, dict):
        return result.get("cost", 0.0), result.get("model", "unknown")
    if operation in ("test", "test_extend"):
        # 4-tuple: (content, cost, model, agentic_success)
        return result[1], result[2]
    # 3-tuple or 6-tuple: cost is second-to-last, model is last
    return result[-2], result[-1]


# ---------------------------------------------------------------------------
# Cycle detection
# ---------------------------------------------------------------------------

MAX_CYCLE_REPEATS = 2  # used inside sync_worker_logic as well


def _check_cycles(
    history: List[str],
    current_op: str,
) -> tuple:
    """Return ``(action, reason)`` where *action* is one of:

    - ``"continue"`` – proceed normally
    - ``"advance_generate"`` – override current operation to ``generate``
    - ``"break"`` – stop the workflow loop
    """
    # Auto-deps: 2+ in last 3 → force advance to generate
    if current_op == "auto_deps" and len(history) >= 2:
        last_3 = history[-3:]
        if last_3.count("auto_deps") >= 2:
            return "advance_generate", "auto-deps cycle detected; advancing to generate"

    # Crash-verify alternation (4-op pattern, 2 cycles)
    if len(history) >= 4:
        last4 = history[-4:]
        if last4 == ["crash", "verify", "crash", "verify"] or last4 == [
            "verify",
            "crash",
            "verify",
            "crash",
        ]:
            return "break", "crash-verify cycle detected after 2 cycles"

    # Test-fix alternation
    if len(history) >= 4:
        last4 = history[-4:]
        if last4 == ["test", "fix", "test", "fix"] or last4 == [
            "fix",
            "test",
            "fix",
            "test",
        ]:
            return "break", "test-fix cycle detected after 2 cycles"

    # Consecutive fix
    consec = 0
    for op in reversed(history):
        if op == "fix":
            consec += 1
        else:
            break
    if current_op == "fix" and consec >= 5:
        return "break", "too many consecutive fix operations (5)"

    # Consecutive test
    consec = 0
    for op in reversed(history):
        if op in ("test", "test_extend"):
            consec += 1
        else:
            break
    if current_op in ("test", "test_extend") and consec >= MAX_CONSECUTIVE_TESTS:
        return "break", f"too many consecutive test operations ({MAX_CONSECUTIVE_TESTS})"

    # Consecutive crash
    consec = 0
    for op in reversed(history):
        if op == "crash":
            consec += 1
        else:
            break
    if current_op == "crash" and consec >= MAX_CONSECUTIVE_CRASHES:
        return "break", f"too many consecutive crash operations ({MAX_CONSECUTIVE_CRASHES})"

    # Test-extend attempts
    if current_op == "test_extend":
        ext_count = sum(1 for o in history if o == "test_extend")
        if ext_count >= MAX_TEST_EXTEND_ATTEMPTS:
            return (
                "break",
                "accepting current coverage after max test_extend attempts",
            )

    return "continue", ""


# ---------------------------------------------------------------------------
# Build final-state dict
# ---------------------------------------------------------------------------

def _build_final_state(pdd_files: Dict[str, Any]) -> Dict[str, Any]:
    state: Dict[str, Any] = {}
    for key in ("prompt", "code", "example", "test"):
        p = pdd_files.get(key)
        if p is not None:
            pp = Path(p)
            state[key] = {"exists": pp.exists(), "path": str(pp)}
        else:
            state[key] = {"exists": False, "path": None}
    return state


# ---------------------------------------------------------------------------
# Main entry point
# ---------------------------------------------------------------------------

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
    no_steer: bool = False,
    steer_timeout: float = DEFAULT_STEER_TIMEOUT_S,
    agentic_mode: bool = False,
) -> Dict[str, Any]:
    """Orchestrate the full PDD sync workflow.

    Returns a dictionary containing ``success``, ``operations_completed``,
    ``skipped_operations``, ``total_cost``, ``total_time``, ``final_state``,
    ``errors``, ``error``, ``model_name``, and (for dry-runs) ``log_entries``.
    """
    # Defence-in-depth: replace None with defaults (CLI may pass None)
    if target_coverage is None:
        target_coverage = 90.0
    if budget is None:
        budget = 10.0
    if max_attempts is None:
        max_attempts = 3

    # Function-scope import
    from . import get_extension  # noqa: E402 – intentional late import

    start_time = time.time()

    # ------------------------------------------------------------------
    # Dry-run: show log and exit
    # ------------------------------------------------------------------
    if dry_run:
        entries = _display_sync_log(basename, language, verbose)
        decision = sync_determine_operation(
            basename, language, target_coverage, log_mode=True
        )
        click.echo(
            f"\nRecommended operation: {decision.operation}  "
            f"(confidence={decision.confidence:.2f}, "
            f"decision_type={decision.decision_type})"
        )
        if decision.reason:
            click.echo(f"  Reason: {decision.reason}")
        return {
            "success": True,
            "operations_completed": [],
            "skipped_operations": [],
            "total_cost": 0.0,
            "total_time": time.time() - start_time,
            "final_state": {},
            "errors": [],
            "error": None,
            "model_name": "",
            "log_entries": entries,
        }

    # ------------------------------------------------------------------
    # Resolve file paths
    # ------------------------------------------------------------------
    try:
        pdd_files = _resolve_pdd_paths(
            basename, language, prompts_dir, code_dir, examples_dir, tests_dir
        )
    except Exception as exc:
        return {
            "success": False,
            "operations_completed": [],
            "skipped_operations": [],
            "total_cost": 0.0,
            "total_time": time.time() - start_time,
            "final_state": {},
            "errors": [f"Path resolution failed: {exc}"],
            "error": str(exc),
            "model_name": "",
        }

    ext = get_extension(language)
    headless = _is_headless(quiet)

    # ------------------------------------------------------------------
    # Shared mutable references for TUI coordination
    # ------------------------------------------------------------------
    function_name_ref: List[str] = ["initializing"]
    cost_ref: List[float] = [0.0]
    prompt_color_ref: List[str] = ["blue"]
    code_color_ref: List[str] = ["blue"]
    example_color_ref: List[str] = ["blue"]
    test_color_ref: List[str] = ["blue"]
    prompt_path_ref: List[str] = [str(pdd_files.get("prompt", ""))]
    code_path_ref: List[str] = [str(pdd_files.get("code", ""))]
    example_path_ref: List[str] = [str(pdd_files.get("example", ""))]
    test_path_ref: List[str] = [str(pdd_files.get("test", ""))]
    stop_event = threading.Event()
    app_ref: List[Any] = [None]
    user_confirmed_overwrite: List[bool] = [force]
    progress_callback_ref: List[Optional[Callable]] = [None]

    # Result container (populated by the worker)
    result_box: List[Optional[Dict[str, Any]]] = [None]

    # ------------------------------------------------------------------
    # Worker function
    # ------------------------------------------------------------------
    def sync_worker_logic() -> Dict[str, Any]:  # noqa: C901 – inherently complex
        """Core workflow loop – runs in a worker thread or directly (headless)."""
        operations_completed: List[str] = []
        skipped_operations: List[str] = []
        errors: List[str] = []
        total_cost = 0.0
        model_name = ""
        operation_history: List[str] = []

        # Select appropriate confirm callback
        if confirm_callback is not None:
            cb = confirm_callback
        elif headless:
            cb = _get_confirm_callback_headless(user_confirmed_overwrite)
        else:
            cb = _get_confirm_callback_tui(app_ref, user_confirmed_overwrite)

        ctx_kwargs = dict(
            strength=strength,
            temperature=temperature,
            time_param=time_param,
            force=force or user_confirmed_overwrite[0],
            quiet=quiet,
            verbose=verbose,
            local=local,
            output_cost=output_cost,
            review_examples=review_examples,
            confirm_callback=cb,
            context_override=context_override,
        )

        def _make_ctx() -> click.Context:
            return _create_mock_context(**{**ctx_kwargs, "force": True})

        lock: Optional[SyncLock] = None
        try:
            # Acquire lock
            lock = SyncLock(basename, language)
            lock.__enter__()
            log_event(basename, language, "lock_acquired", {}, invocation_mode="sync")

            while not stop_event.is_set():
                # Budget check
                if total_cost >= budget:
                    log_event(
                        basename,
                        language,
                        "budget_exhausted",
                        {"total_cost": total_cost, "budget": budget},
                    )
                    errors.append(f"Budget exhausted: ${total_cost:.2f} >= ${budget:.2f}")
                    break

                if budget > 0 and total_cost / budget >= 0.80:
                    log_event(
                        basename,
                        language,
                        "budget_warning",
                        {"remaining": budget - total_cost},
                    )

                # ----- Determine next operation -----
                decision: SyncDecision = sync_determine_operation(
                    basename, language, target_coverage
                )
                operation = decision.operation
                reason = decision.reason

                # ----- Terminal states -----
                if operation in ("all_synced", "nothing"):
                    function_name_ref[0] = "done"
                    entry = create_log_entry(
                        operation=operation,
                        reason=reason,
                        invocation_mode="sync",
                        estimated_cost=0,
                        confidence=decision.confidence,
                        decision_type=decision.decision_type,
                    )
                    entry = update_log_entry(entry, True, 0, model_name, 0, None)
                    append_log_entry(basename, language, entry)
                    break
                if operation in ("fail_and_request_manual_merge", "error"):
                    errors.append(f"Terminal state: {operation} – {reason}")
                    entry = create_log_entry(
                        operation=operation,
                        reason=reason,
                        invocation_mode="sync",
                        estimated_cost=0,
                        confidence=decision.confidence,
                        decision_type=decision.decision_type,
                    )
                    entry = update_log_entry(entry, False, 0, model_name, 0, reason)
                    append_log_entry(basename, language, entry)
                    break

                # ----- Cycle detection -----
                action, cycle_reason = _check_cycles(operation_history, operation)
                if action == "break":
                    log_event(basename, language, "cycle_break", {"reason": cycle_reason})
                    errors.append(cycle_reason)
                    break
                if action == "advance_generate":
                    log_event(
                        basename,
                        language,
                        "cycle_advance",
                        {"from": operation, "to": "generate", "reason": cycle_reason},
                    )
                    operation = "generate"
                    decision = SyncDecision(
                        operation="generate",
                        reason=cycle_reason,
                        confidence=decision.confidence,
                        decision_type="cycle_override",
                        estimated_cost=decision.estimated_cost,
                    )

                # ----- Skip cascading -----
                _should_skip = False
                if operation == "verify" and (skip_verify or skip_tests):
                    _should_skip = True
                elif operation == "crash" and skip_tests:
                    _should_skip = True
                elif operation in ("test", "test_extend", "fix") and skip_tests:
                    _should_skip = True

                if _should_skip:
                    skipped_operations.append(operation)
                    entry = create_log_entry(
                        operation=f"skip:{operation}",
                        reason=f"Skipped by user flag",
                        invocation_mode="sync",
                        estimated_cost=0,
                        confidence=1.0,
                        decision_type="skip",
                    )
                    entry = update_log_entry(entry, True, 0, "", 0, None)
                    append_log_entry(basename, language, entry)

                    paths_dict = {
                        k: pdd_files[k]
                        for k in ("prompt", "code", "example", "test")
                        if k in pdd_files and pdd_files[k] is not None
                    }
                    save_fingerprint(
                        basename=basename,
                        language=language,
                        operation=f"skip:{operation}",
                        paths=paths_dict,
                        cost=0,
                        model="",
                    )
                    # For crash skip: synthetic run_report
                    if operation == "crash":
                        _create_synthetic_run_report_for_agentic_success(
                            str(pdd_files.get("test", "")),
                            basename,
                            language,
                        )
                    operation_history.append(operation)
                    continue

                # ----- Interactive steering -----
                if not no_steer and not headless:
                    steered_op, should_abort = maybe_steer_operation(
                        operation,
                        reason,
                        app_ref,
                        quiet,
                        skip_tests,
                        skip_verify,
                        timeout_s=steer_timeout,
                    )
                    if should_abort:
                        errors.append("Sync aborted by user via steering")
                        log_event(
                            basename,
                            language,
                            "steering_abort",
                            {"operation": operation},
                        )
                        break
                    if steered_op != operation:
                        log_event(
                            basename,
                            language,
                            "steering_override",
                            {"from": operation, "to": steered_op},
                        )
                        operation = steered_op
                        decision = SyncDecision(
                            operation=steered_op,
                            reason=f"Steered from {decision.operation}: {reason}",
                            confidence=decision.confidence,
                            decision_type="steering_override",
                            estimated_cost=decision.estimated_cost,
                        )

                # ----- Create log entry -----
                log_entry = create_log_entry(
                    operation=operation,
                    reason=reason,
                    invocation_mode="sync",
                    estimated_cost=decision.estimated_cost,
                    confidence=decision.confidence,
                    decision_type=decision.decision_type,
                )

                # ----- Update TUI -----
                function_name_ref[0] = operation
                op_start = time.time()
                op_cost = 0.0
                op_model = ""
                op_success = False

                try:
                    # ======================================================
                    # auto-deps
                    # ======================================================
                    if operation == "auto_deps":
                        import shutil as _shutil  # function-scope per spec

                        prompt_color_ref[0] = "yellow"
                        ctx = _make_ctx()
                        deps_dir = str(pdd_files.get("auto_deps_dir", examples_dir))
                        deps_csv = str(
                            pdd_files.get("deps_csv", "project_dependencies.csv")
                        )
                        result = auto_deps_main(
                            ctx=ctx,
                            prompt_file=str(pdd_files["prompt"]),
                            directory_path=deps_dir,
                            auto_deps_csv_path=deps_csv,
                            output=str(pdd_files["prompt"]),
                            force_scan=False,
                        )
                        op_cost, op_model = _extract_cost_model(result)
                        prompt_color_ref[0] = "green"
                        op_success = True

                    # ======================================================
                    # generate
                    # ======================================================
                    elif operation == "generate":
                        code_color_ref[0] = "yellow"
                        ctx = _make_ctx()
                        result = code_generator_main(
                            ctx=ctx,
                            prompt_file=str(pdd_files["prompt"]),
                            output=str(pdd_files["code"]),
                            original_prompt_file_path=None,
                            force_incremental_flag=False,
                        )
                        # 4-tuple: (code, incremental, cost, model)
                        op_cost = result[2]
                        op_model = result[3]
                        code_color_ref[0] = "green"
                        op_success = True
                        # Delete stale run_report
                        clear_run_report(basename, language)

                    # ======================================================
                    # example
                    # ======================================================
                    elif operation == "example":
                        example_color_ref[0] = "yellow"
                        ctx = _make_ctx()
                        result = context_generator_main(
                            ctx=ctx,
                            prompt_file=str(pdd_files["prompt"]),
                            code_file=str(pdd_files["code"]),
                            output=str(pdd_files["example"]),
                        )
                        op_cost, op_model = _extract_cost_model(result)
                        example_color_ref[0] = "green"
                        op_success = True

                    # ======================================================
                    # crash
                    # ======================================================
                    elif operation == "crash":
                        code_color_ref[0] = "yellow"
                        example_color_ref[0] = "yellow"
                        ctx = _make_ctx()
                        use_agentic = _use_agentic_path(language, agentic_mode)
                        attempts_val = 0 if use_agentic else max_attempts

                        example_path = str(pdd_files.get("example", ""))
                        code_path = str(pdd_files["code"])

                        # Detect crash
                        has_crash = False
                        crash_log = ""
                        if not use_agentic:
                            ex_ok, ex_out, ex_err, ex_rc = _run_example_with_error_detection(
                                example_path, code_path, language
                            )
                            if not ex_ok:
                                has_crash = True
                                crash_log = ex_out + "\n" + ex_err
                                # Try auto-fix first
                                if _try_auto_fix_import_error(ex_err, code_path, example_path):
                                    ex_ok2, _, _, _ = _run_example_with_error_detection(
                                        example_path, code_path, language
                                    )
                                    if ex_ok2:
                                        has_crash = False
                        else:
                            has_crash = True
                            crash_log = "Non-Python language: delegating crash detection to agentic handler"

                        if has_crash:
                            # Write crash log to temp file
                            with tempfile.NamedTemporaryFile(
                                mode="w",
                                suffix=".log",
                                delete=False,
                                prefix="crash_",
                            ) as f:
                                f.write(crash_log)
                                crash_log_path = f.name
                            try:
                                result = crash_main(
                                    ctx=ctx,
                                    prompt_file=str(pdd_files["prompt"]),
                                    code_file=code_path,
                                    program_file=example_path,
                                    error_file=crash_log_path,
                                    output=code_path,
                                    output_program=example_path,
                                    loop=True,
                                    strength=strength,
                                    temperature=temperature,
                                    budget=min(budget - total_cost, budget * 0.3),
                                    max_attempts=attempts_val,
                                )
                                # 6-tuple: (success, code, program, attempts, cost, model)
                                crash_success = result[0]
                                op_cost = result[4]
                                op_model = result[5]
                                op_success = crash_success
                            finally:
                                if os.path.exists(crash_log_path):
                                    os.unlink(crash_log_path)

                            # Post-crash validation
                            if op_success:
                                with AtomicStateUpdate(basename, language) as at_state:
                                    if language.lower() == "python" and not agentic_mode:
                                        ex_ok, ex_out, ex_err, ex_rc = _run_example_with_error_detection(
                                            example_path, code_path, language
                                        )
                                        report = RunReport(
                                            timestamp=datetime.datetime.now().isoformat(),
                                            exit_code=0 if ex_ok else ex_rc,
                                            tests_passed=1 if ex_ok else 0,
                                            tests_failed=0 if ex_ok else 1,
                                            coverage=0.0,
                                        )
                                        at_state.queue_run_report(report.__dict__)
                                    else:
                                        # Trust agentic result
                                        report = RunReport(
                                            timestamp=datetime.datetime.now().isoformat(),
                                            exit_code=0,
                                            tests_passed=1,
                                            tests_failed=0,
                                            coverage=0.0,
                                        )
                                        at_state.queue_run_report(report.__dict__)
                        else:
                            op_success = True

                        code_color_ref[0] = "green" if op_success else "red"
                        example_color_ref[0] = "green" if op_success else "red"

                    # ======================================================
                    # verify
                    # ======================================================
                    elif operation == "verify":
                        code_color_ref[0] = "yellow"
                        ctx = _make_ctx()
                        use_agentic = _use_agentic_path(language, agentic_mode)
                        attempts_val = 0 if use_agentic else max_attempts
                        result = fix_verification_main(
                            ctx=ctx,
                            prompt_file=str(pdd_files["prompt"]),
                            code_file=str(pdd_files["code"]),
                            program_file=str(pdd_files.get("example", "")),
                            output_results=None,
                            output_code=str(pdd_files["code"]),
                            output_program=str(pdd_files.get("example", "")),
                            loop=True,
                            verification_program=None,
                            max_attempts=attempts_val,
                            budget=min(budget - total_cost, budget * 0.3),
                            agentic_fallback=True,
                        )
                        verify_success = result[0]
                        op_cost = result[4]
                        op_model = result[5]
                        op_success = verify_success
                        code_color_ref[0] = "green" if op_success else "red"

                    # ======================================================
                    # test
                    # ======================================================
                    elif operation == "test":
                        test_color_ref[0] = "yellow"
                        ctx = _make_ctx()
                        test_path = str(pdd_files.get("test", ""))
                        result = cmd_test_main(
                            ctx=ctx,
                            prompt_file=str(pdd_files["prompt"]),
                            code_file=str(pdd_files["code"]),
                            output=test_path,
                            language=language,
                            coverage_report=None,
                            existing_tests=None,
                            target_coverage=target_coverage,
                            merge=False,
                            strength=strength,
                            temperature=temperature,
                        )
                        # 4-tuple: (content, cost, model, agentic_success)
                        op_cost = result[1]
                        op_model = result[2]
                        agentic_success = result[3]

                        if agentic_success is not None:
                            op_success = agentic_success
                        else:
                            op_success = Path(test_path).exists()

                        if op_success:
                            with AtomicStateUpdate(basename, language) as at_state:
                                if agentic_success is True:
                                    _create_synthetic_run_report_for_agentic_success(
                                        test_path, basename, language, atomic_state=at_state
                                    )
                                else:
                                    test_files_list = pdd_files.get("test_files")
                                    _execute_tests_and_create_run_report(
                                        test_path,
                                        basename,
                                        language,
                                        target_coverage,
                                        code_file=str(pdd_files["code"]),
                                        atomic_state=at_state,
                                        test_files=test_files_list,
                                    )

                        test_color_ref[0] = "green" if op_success else "red"

                    # ======================================================
                    # test_extend
                    # ======================================================
                    elif operation == "test_extend":
                        lang_lower = language.lower()
                        # Non-Python: skip test_extend entirely
                        if lang_lower != "python" and not (
                            lang_lower == "typescript"
                        ):
                            skipped_operations.append("test_extend")
                            operation_history.append(operation)
                            log_entry = update_log_entry(
                                log_entry, True, 0, "", 0, "Skipped for non-Python/TS"
                            )
                            append_log_entry(basename, language, log_entry)
                            continue

                        test_color_ref[0] = "yellow"
                        ctx = _make_ctx()
                        test_path = str(pdd_files.get("test", ""))
                        existing = [test_path] if Path(test_path).exists() else None

                        rr = read_run_report(basename, language)
                        cov_report = None

                        result = cmd_test_main(
                            ctx=ctx,
                            prompt_file=str(pdd_files["prompt"]),
                            code_file=str(pdd_files["code"]),
                            output=test_path,
                            language=language,
                            coverage_report=cov_report,
                            existing_tests=existing,
                            target_coverage=target_coverage,
                            merge=True,
                            strength=strength,
                            temperature=temperature,
                        )
                        op_cost = result[1]
                        op_model = result[2]
                        agentic_success = result[3]

                        op_success = True
                        with AtomicStateUpdate(basename, language) as at_state:
                            if (
                                agentic_success is True
                                and lang_lower not in ("python", "typescript")
                            ):
                                _create_synthetic_run_report_for_agentic_success(
                                    test_path, basename, language, atomic_state=at_state
                                )
                            else:
                                test_files_list = pdd_files.get("test_files")
                                _execute_tests_and_create_run_report(
                                    test_path,
                                    basename,
                                    language,
                                    target_coverage,
                                    code_file=str(pdd_files["code"]),
                                    atomic_state=at_state,
                                    test_files=test_files_list,
                                )

                        test_color_ref[0] = "green"

                    # ======================================================
                    # fix
                    # ======================================================
                    elif operation == "fix":
                        from .get_test_command import get_test_command_for_file

                        test_color_ref[0] = "yellow"
                        code_color_ref[0] = "yellow"
                        ctx = _make_ctx()
                        use_agentic = _use_agentic_path(language, agentic_mode)
                        attempts_val = 0 if use_agentic else max_attempts

                        test_path = str(pdd_files.get("test", ""))
                        code_path = str(pdd_files["code"])
                        test_files_list = pdd_files.get("test_files")

                        # Determine which test file is failing
                        failing_test = test_path
                        rr = read_run_report(basename, language)
                        if rr and hasattr(rr, "exit_code") and rr.exit_code != 0:
                            # Run tests and extract failing file
                            all_tests = test_files_list or [test_path]
                            env = _subprocess_env()
                            if language.lower() == "python":
                                python_exe = detect_host_python_executable()
                                proj_root = _find_project_root(test_path)
                                cmd = [python_exe, "-m", "pytest", "-x", "--tb=short"] + all_tests
                                if proj_root:
                                    cmd += ["--rootdir", str(proj_root), "-c", "/dev/null"]
                                    pyp = [str(proj_root)]
                                    sd = Path(proj_root) / "src"
                                    if sd.is_dir():
                                        pyp.append(str(sd))
                                    existing_pp = env.get("PYTHONPATH", "")
                                    env["PYTHONPATH"] = os.pathsep.join(
                                        pyp + ([existing_pp] if existing_pp else [])
                                    )
                                try:
                                    proc = subprocess.run(
                                        cmd,
                                        capture_output=True,
                                        text=True,
                                        timeout=120,
                                        env=env,
                                        start_new_session=True,
                                        stdin=subprocess.DEVNULL,
                                    )
                                    combined_out = (proc.stdout or "") + "\n" + (proc.stderr or "")
                                    failing_files = extract_failing_files_from_output(combined_out)
                                    if failing_files:
                                        failing_test = failing_files[0]
                                except Exception:
                                    pass

                        # Write error info
                        with tempfile.NamedTemporaryFile(
                            mode="w", suffix=".log", delete=False, prefix="fix_err_"
                        ) as ef:
                            ef.write("Test failures detected by sync workflow")
                            error_file_path = ef.name

                        try:
                            result = fix_main(
                                ctx=ctx,
                                prompt_file=str(pdd_files["prompt"]),
                                code_file=code_path,
                                unit_test_file=failing_test,
                                error_file=error_file_path,
                                output_test=failing_test,
                                output_code=code_path,
                                output_results=None,
                                loop=True,
                                verification_program=str(pdd_files.get("example", "")),
                                max_attempts=attempts_val,
                                budget=min(budget - total_cost, budget * 0.3),
                                auto_submit=False,
                                agentic_fallback=True,
                                strength=strength,
                                temperature=temperature,
                                test_files=test_files_list,
                            )
                            fix_success = result[0]
                            op_cost = result[4]
                            op_model = result[5]
                            op_success = fix_success
                        finally:
                            if os.path.exists(error_file_path):
                                os.unlink(error_file_path)

                        # Post-fix: re-run tests
                        if op_success:
                            with AtomicStateUpdate(basename, language) as at_state:
                                if language.lower() == "python" and not agentic_mode:
                                    _execute_tests_and_create_run_report(
                                        test_path,
                                        basename,
                                        language,
                                        target_coverage,
                                        code_file=code_path,
                                        atomic_state=at_state,
                                        test_files=test_files_list,
                                    )
                                else:
                                    report = RunReport(
                                        timestamp=datetime.datetime.now().isoformat(),
                                        exit_code=0,
                                        tests_passed=1,
                                        tests_failed=0,
                                        coverage=0.0,
                                    )
                                    at_state.queue_run_report(report.__dict__)

                        code_color_ref[0] = "green" if op_success else "red"
                        test_color_ref[0] = "green" if op_success else "red"

                    # ======================================================
                    # update
                    # ======================================================
                    elif operation == "update":
                        prompt_color_ref[0] = "yellow"
                        ctx = _make_ctx()
                        result = update_main(
                            ctx=ctx,
                            input_prompt_file=str(pdd_files["prompt"]),
                            modified_code_file=str(pdd_files["code"]),
                            input_code_file=None,
                            output=str(pdd_files["prompt"]),
                            use_git=True,
                            simple=False,
                        )
                        op_cost, op_model = _extract_cost_model(result)
                        prompt_color_ref[0] = "green"
                        op_success = True

                    else:
                        errors.append(f"Unknown operation: {operation}")
                        log_entry = update_log_entry(
                            log_entry, False, 0, "", 0, f"Unknown: {operation}"
                        )
                        append_log_entry(basename, language, log_entry)
                        operation_history.append(operation)
                        continue

                except Exception as exc:
                    import traceback as _tb

                    err_msg = f"{operation} failed: {exc}"
                    logger.error("%s\n%s", err_msg, _tb.format_exc())
                    errors.append(err_msg)
                    op_success = False

                    # Update TUI colours to red
                    if operation in ("generate", "crash", "fix", "verify"):
                        code_color_ref[0] = "red"
                    if operation in ("example", "crash"):
                        example_color_ref[0] = "red"
                    if operation in ("test", "test_extend", "fix"):
                        test_color_ref[0] = "red"
                    if operation in ("auto_deps", "update"):
                        prompt_color_ref[0] = "red"

                # ----- Finalise this iteration -----
                duration = time.time() - op_start
                total_cost += op_cost
                cost_ref[0] = total_cost
                if op_model:
                    model_name = op_model

                log_entry = update_log_entry(
                    log_entry,
                    op_success,
                    op_cost,
                    op_model,
                    duration,
                    None if op_success else (errors[-1] if errors else None),
                )
                append_log_entry(basename, language, log_entry)

                if op_success:
                    operations_completed.append(operation)
                    # Save fingerprint
                    paths_dict = {
                        k: pdd_files[k]
                        for k in ("prompt", "code", "example", "test")
                        if k in pdd_files and pdd_files[k] is not None
                    }
                    try:
                        save_fingerprint(
                            basename=basename,
                            language=language,
                            operation=operation,
                            paths=paths_dict,
                            cost=op_cost,
                            model=op_model,
                        )
                    except Exception:
                        pass

                operation_history.append(operation)

        except Exception as exc:
            import traceback as _tb

            errors.append(f"Workflow error: {exc}")
            logger.error("Workflow error:\n%s", _tb.format_exc())
        finally:
            if lock is not None:
                try:
                    lock.__exit__(None, None, None)
                    log_event(
                        basename, language, "lock_released", {}, invocation_mode="sync"
                    )
                except Exception:
                    pass

        elapsed = time.time() - start_time
        result_dict: Dict[str, Any] = {
            "success": len(errors) == 0,
            "operations_completed": operations_completed,
            "skipped_operations": skipped_operations,
            "total_cost": total_cost,
            "total_time": elapsed,
            "final_state": _build_final_state(pdd_files),
            "errors": errors,
            "error": "; ".join(errors) if errors else None,
            "model_name": model_name,
        }
        result_box[0] = result_dict
        return result_dict

    # ------------------------------------------------------------------
    # Run: headless vs TUI
    # ------------------------------------------------------------------
    if headless:
        prev_force = os.environ.get("PDD_FORCE")
        os.environ["PDD_FORCE"] = "1"
        try:
            return sync_worker_logic()
        finally:
            if prev_force is None:
                os.environ.pop("PDD_FORCE", None)
            else:
                os.environ["PDD_FORCE"] = prev_force

    # --- TUI path ---
    def _tui_worker(
        fn_ref, c_ref, p_col, co_col, ex_col, t_col,
        p_path, co_path, ex_path, t_path,
        s_event, a_ref, prog_cb_ref,
    ):
        """Adapter that plugs shared refs then runs the worker."""
        nonlocal function_name_ref, cost_ref
        nonlocal prompt_color_ref, code_color_ref, example_color_ref, test_color_ref
        nonlocal prompt_path_ref, code_path_ref, example_path_ref, test_path_ref
        nonlocal stop_event, app_ref, progress_callback_ref
        function_name_ref = fn_ref
        cost_ref = c_ref
        prompt_color_ref = p_col
        code_color_ref = co_col
        example_color_ref = ex_col
        test_color_ref = t_col
        prompt_path_ref = p_path
        code_path_ref = co_path
        example_path_ref = ex_path
        test_path_ref = t_path
        stop_event = s_event
        app_ref = a_ref
        progress_callback_ref = prog_cb_ref
        sync_worker_logic()

    app = SyncApp(
        worker_func=_tui_worker,
        basename=basename,
        language=language,
    )

    run_result = app.run()

    # Check for worker exceptions
    if hasattr(app, "worker_exception") and app.worker_exception is not None:
        import traceback as _tb

        print(
            f"Sync worker crashed: {app.worker_exception}",
            file=sys.stderr,
        )
        if hasattr(app, "worker_traceback"):
            print(app.worker_traceback, file=sys.stderr)

    if run_result is None and result_box[0] is None:
        return {
            "success": False,
            "operations_completed": [],
            "skipped_operations": [],
            "total_cost": 0.0,
            "total_time": time.time() - start_time,
            "final_state": _build_final_state(pdd_files),
            "errors": ["Sync was interrupted"],
            "error": "Sync was interrupted",
            "model_name": "",
        }

    # Show exit animation
    if not quiet:
        try:
            from .sync_tui import show_exit_animation

            show_exit_animation(
                result_box[0] if result_box[0] else {},
                basename,
                language,
            )
        except Exception:
            pass

    if result_box[0] is not None:
        return result_box[0]

    return {
        "success": False,
        "operations_completed": [],
        "skipped_operations": [],
        "total_cost": 0.0,
        "total_time": time.time() - start_time,
        "final_state": _build_final_state(pdd_files),
        "errors": ["No result produced"],
        "error": "No result produced",
        "model_name": "",
    }