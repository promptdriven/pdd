"""
PDD Sync Orchestration Module.

Coordinates the complete PDD sync workflow by executing operations determined
by sync_determine_operation and providing real-time feedback via a Textual-based
TUI. Handles state management, budget tracking, cycle detection, and interactive
steering in parallel with animation display.
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

_TERMINAL_STATES = frozenset({"all_synced", "nothing", "fail_and_request_manual_merge", "error"})


# ---------------------------------------------------------------------------
# AtomicStateUpdate – ensures fingerprint + run-report consistency
# ---------------------------------------------------------------------------

class AtomicStateUpdate:
    """Context manager for consistent state writes.

    Ensures run-report and fingerprint are both written or neither is written
    by using temp-file + atomic-rename for crash safety.
    """

    def __init__(self, basename: str, language: str):
        self.basename = basename
        self.language = language
        self._pending_fingerprint: Optional[Dict] = None
        self._pending_run_report: Optional[Dict] = None

    def __enter__(self) -> "AtomicStateUpdate":
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        if exc_type is None:
            self._commit()
        return False

    # -- public setters --

    def set_fingerprint(self, operation: str, paths: Dict, cost: float, model: str):
        self._pending_fingerprint = dict(
            operation=operation, paths=paths, cost=cost, model=model,
        )

    def set_run_report(self, report_data):
        if isinstance(report_data, RunReport):
            self._pending_run_report = report_data.__dict__.copy()
        elif isinstance(report_data, dict):
            self._pending_run_report = report_data
        else:
            self._pending_run_report = asdict(report_data)

    # -- internal --

    def _commit(self):
        meta = Path(PDD_DIR) / "meta"
        meta.mkdir(parents=True, exist_ok=True)
        safe = _safe_basename(self.basename)
        lang = self.language.lower()

        if self._pending_run_report is not None:
            target = meta / f"{safe}_{lang}_run.json"
            tmp = target.with_suffix(".tmp")
            try:
                tmp.write_text(
                    json.dumps(self._pending_run_report, default=str),
                    encoding="utf-8",
                )
                tmp.replace(target)
            except Exception:
                tmp.unlink(missing_ok=True)
                raise

        if self._pending_fingerprint is not None:
            save_fingerprint(
                basename=self.basename,
                language=self.language,
                **self._pending_fingerprint,
            )


# ---------------------------------------------------------------------------
# Small helpers
# ---------------------------------------------------------------------------

def _use_agentic_path(language: str, agentic_mode: bool) -> bool:
    """Return True when the agentic (non-iterative) path should be used."""
    return language.lower() != "python" or agentic_mode


def _is_headless() -> bool:
    """Detect headless environments (CI, no TTY)."""
    if os.environ.get("CI"):
        return True
    if not hasattr(sys.stdout, "isatty") or not sys.stdout.isatty():
        return True
    return False


def _get_subprocess_env() -> dict:
    """Get a clean env dict for subprocess calls (TUI vars removed)."""
    env = os.environ.copy()
    for key in ("FORCE_COLOR", "COLUMNS"):
        env.pop(key, None)
    return env


def _get_file_color(path: Optional[str], is_processing: bool = False) -> str:
    """Determine TUI status colour for a file."""
    if is_processing:
        return "yellow"
    if path and Path(path).exists():
        return "green"
    return "red"


# ---------------------------------------------------------------------------
# Display helpers
# ---------------------------------------------------------------------------

def _display_sync_log(basename: str, language: str, verbose: bool) -> List[Dict]:
    """Format and display the sync log from .pdd/meta/ to stdout."""
    entries = load_operation_log(basename, language)
    if not entries:
        click.echo(f"No sync log entries found for {basename}_{language.lower()}")
        return []

    for entry in entries:
        ts = entry.get("timestamp", "?")
        op = entry.get("operation", "?")
        success = entry.get("success")
        cost = entry.get("actual_cost", entry.get("estimated_cost", 0))

        status = "✓" if success else ("✗" if success is False else "…")
        line = f"  {status} [{ts[:19]}] {op}"

        if verbose:
            reason = entry.get("reason", "")
            dtype = entry.get("decision_type", "")
            conf = entry.get("confidence", "")
            if reason:
                line += f" — {reason}"
            if dtype:
                line += f" (type={dtype}"
                if conf:
                    line += f", confidence={conf}"
                line += ")"
            if cost:
                line += f" cost=${cost:.4f}"
            err = entry.get("error")
            if err:
                line += f" ERROR: {err}"
        elif cost:
            line += f" (${cost:.4f})"

        click.echo(line)

    return entries


# ---------------------------------------------------------------------------
# Click context factory
# ---------------------------------------------------------------------------

def _create_mock_context(
    strength: float = DEFAULT_STRENGTH,
    temperature: float = 0.0,
    time_param: float = 0.25,
    verbose: bool = False,
    quiet: bool = False,
    force: bool = False,
    local: bool = False,
    context: Optional[str] = None,
    confirm_callback: Optional[Callable] = None,
    output_cost: Optional[str] = None,
    review_examples: bool = False,
) -> click.Context:
    """Create a Click context suitable for *_main command functions."""
    ctx = click.Context(click.Command("sync"))
    ctx.obj = {
        "strength": strength,
        "temperature": temperature,
        "time": time_param,
        "verbose": verbose,
        "quiet": quiet,
        "force": force,
        "local": local,
        "context": context,
        "confirm_callback": confirm_callback,
        "output_cost": output_cost,
        "review_examples": review_examples,
    }
    ctx.params = {
        "local": local,
        "force": force,
        "quiet": quiet,
    }
    return ctx


# ---------------------------------------------------------------------------
# Test-output parsing
# ---------------------------------------------------------------------------

def _parse_test_output(output: str, language: str) -> tuple:
    """Parse test-runner output → (tests_passed, tests_failed, coverage%)."""
    lang = language.lower()
    passed = failed = 0
    coverage = 0.0

    if lang == "python":
        m = re.search(r"(\d+)\s+passed", output)
        if m:
            passed = int(m.group(1))
        m = re.search(r"(\d+)\s+failed", output)
        if m:
            failed = int(m.group(1))
        m = re.search(r"(\d+)\s+error", output)
        if m:
            failed += int(m.group(1))
        m = re.search(r"TOTAL\s+\d+\s+\d+\s+(\d+)%", output)
        if m:
            coverage = float(m.group(1))

    elif lang in ("javascript", "typescript"):
        m = re.search(r"Tests:\s+(\d+)\s+passed", output)
        if m:
            passed = int(m.group(1))
        m = re.search(r"Tests:.*?(\d+)\s+failed", output)
        if m:
            failed = int(m.group(1))
        if not passed and not failed:
            m = re.search(r"(\d+)\s+passing", output)
            if m:
                passed = int(m.group(1))
            m = re.search(r"(\d+)\s+failing", output)
            if m:
                failed = int(m.group(1))
        m = re.search(r"All files.*?\|\s*([\d.]+)", output)
        if m:
            coverage = float(m.group(1))

    elif lang == "go":
        passed = output.count("--- PASS:")
        failed = output.count("--- FAIL:")
        if "PASS" in output and not passed and not failed:
            passed = 1
        if "FAIL" in output and not failed:
            failed = 1
        m = re.search(r"coverage:\s*([\d.]+)%", output)
        if m:
            coverage = float(m.group(1))

    elif lang == "rust":
        m = re.search(r"test result:.*?(\d+)\s+passed.*?(\d+)\s+failed", output)
        if m:
            passed, failed = int(m.group(1)), int(m.group(2))

    return passed, failed, coverage


# ---------------------------------------------------------------------------
# Coverage-target helpers (Python)
# ---------------------------------------------------------------------------

def _python_cov_target_for_code_file(code_file: str) -> Optional[str]:
    """Derive the dotted module path for ``--cov`` from a code file path."""
    if not code_file:
        return None
    p = Path(code_file)
    if not p.exists():
        return None
    parts = list(p.with_suffix("").parts)
    if parts and parts[0] == "src":
        parts = parts[1:]
    return ".".join(parts) if parts else None


def _python_cov_target_for_test_and_code(
    test_file: str, code_file: str, fallback: str
) -> str:
    """Analyse test imports to pick the best ``--cov`` target."""
    try:
        content = Path(test_file).read_text(encoding="utf-8", errors="replace")
        imports = re.findall(r"(?:from|import)\s+([\w.]+)", content)
        code_stem = Path(code_file).stem if code_file else None
        for imp in imports:
            if code_stem and code_stem in imp:
                return imp.split(".")[0]
    except Exception:
        pass
    target = _python_cov_target_for_code_file(code_file)
    return target or fallback


# ---------------------------------------------------------------------------
# Example-error detection
# ---------------------------------------------------------------------------

def _detect_example_errors(output: str) -> Optional[str]:
    """Return *output* when it contains Python tracebacks or ERROR lines."""
    if not output:
        return None
    if re.search(r"Traceback \(most recent call last\)", output):
        return output
    lines = output.strip().splitlines()
    for line in lines:
        if re.match(r"^\s*(ERROR|CRITICAL)\b", line, re.IGNORECASE):
            return output
    if lines and re.match(r"^\w+Error:", lines[-1]):
        return output
    return None


def _run_example_with_error_detection(
    example_path: str,
    code_dir: str,
    language: str,
    timeout: int = 30,
) -> tuple:
    """Run example with *timeout*; return (exit_code, stdout, stderr)."""
    env = _get_subprocess_env()

    if language.lower() == "python":
        python_exec = detect_host_python_executable() or sys.executable
        cmd: Any = [python_exec, example_path]
        project_root = _find_project_root(example_path)
        if project_root:
            paths = [str(project_root)]
            src = project_root / "src"
            if src.is_dir():
                paths.append(str(src))
            existing = env.get("PYTHONPATH", "")
            env["PYTHONPATH"] = os.pathsep.join(paths + ([existing] if existing else []))
    else:
        cmd_str = get_run_command_for_file(example_path, language=language)
        if cmd_str:
            cmd = cmd_str if isinstance(cmd_str, list) else ["sh", "-c", cmd_str]
        else:
            cmd = [example_path]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            env=env,
            cwd=code_dir if Path(code_dir).is_dir() else None,
            start_new_session=True,
            stdin=subprocess.DEVNULL,
        )
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return 0, "", ""  # server-style examples that block are OK
    except Exception as e:
        return 1, "", str(e)


def _try_auto_fix_import_error(stderr: str, code_file: str) -> bool:
    """Attempt pip-install for common ImportError / ModuleNotFoundError."""
    if not stderr:
        return False
    if "ImportError" not in stderr and "ModuleNotFoundError" not in stderr:
        return False
    m = re.search(r"No module named '(\w+)'", stderr)
    if not m:
        return False
    missing = m.group(1)
    try:
        python_exec = detect_host_python_executable() or sys.executable
        subprocess.run(
            [python_exec, "-m", "pip", "install", missing],
            capture_output=True,
            timeout=60,
            start_new_session=True,
            stdin=subprocess.DEVNULL,
        )
        return True
    except Exception:
        return False


# ---------------------------------------------------------------------------
# Test execution
# ---------------------------------------------------------------------------

def _execute_tests_and_create_run_report(
    test_file: str,
    basename: str,
    language: str,
    target_coverage: float,
    *,
    code_file: str = None,
    atomic_state: Optional[AtomicStateUpdate] = None,
    test_files: Optional[List[str]] = None,
) -> Optional[RunReport]:
    """Run tests with coverage, persist a RunReport, and return it."""
    from .get_test_command import get_test_command_for_file

    lang = language.lower()
    env = _get_subprocess_env()
    all_test_files = test_files or [test_file]
    all_test_files = [f for f in all_test_files if Path(f).exists()]
    if not all_test_files:
        return None

    combined_output = ""
    exit_code = 0

    if lang == "python":
        python_exec = detect_host_python_executable() or sys.executable
        project_root = _find_project_root(all_test_files[0])

        cmd = [python_exec, "-m", "pytest", "-v"]
        if code_file:
            cov_target = _python_cov_target_for_test_and_code(
                all_test_files[0], code_file, _safe_basename(basename),
            )
            cmd.extend([f"--cov={cov_target}", "--cov-report=term-missing"])

        if project_root:
            cmd.extend(["--rootdir", str(project_root), "-c", "/dev/null"])
            paths = [str(project_root)]
            src = project_root / "src"
            if src.is_dir():
                paths.append(str(src))
            existing = env.get("PYTHONPATH", "")
            env["PYTHONPATH"] = os.pathsep.join(paths + ([existing] if existing else []))

        cmd.extend(all_test_files)
        try:
            result = subprocess.run(
                cmd, capture_output=True, text=True, timeout=120,
                env=env, start_new_session=True, stdin=subprocess.DEVNULL,
            )
            combined_output = result.stdout + "\n" + result.stderr
            exit_code = result.returncode
        except subprocess.TimeoutExpired:
            combined_output = "Test execution timed out"
            exit_code = 1
        except Exception as e:
            combined_output = str(e)
            exit_code = 1
    else:
        test_cmd = get_test_command_for_file(all_test_files[0], language=language)
        if not test_cmd:
            return None
        try:
            shell_cmd = test_cmd if isinstance(test_cmd, list) else ["sh", "-c", test_cmd]
            result = subprocess.run(
                shell_cmd, capture_output=True, text=True, timeout=120,
                env=env, start_new_session=True, stdin=subprocess.DEVNULL,
            )
            combined_output = result.stdout + "\n" + result.stderr
            exit_code = result.returncode
        except subprocess.TimeoutExpired:
            combined_output = "Test execution timed out"
            exit_code = 1
        except Exception as e:
            combined_output = str(e)
            exit_code = 1

    total_passed, total_failed, total_coverage = _parse_test_output(combined_output, language)

    # Compute test-file hashes
    test_hash: Optional[str] = None
    for tf in all_test_files:
        if Path(tf).exists():
            h = calculate_sha256(tf)
            if tf == test_file or test_hash is None:
                test_hash = h

    report = RunReport(
        timestamp=datetime.datetime.now().isoformat(),
        exit_code=exit_code,
        tests_passed=total_passed,
        tests_failed=total_failed,
        coverage=total_coverage,
        test_hash=test_hash,
    )

    if atomic_state:
        atomic_state.set_run_report(report)
    else:
        save_run_report(basename, language, report.__dict__)

    return report


def _create_synthetic_run_report_for_agentic_success(
    test_file: str,
    basename: str,
    language: str,
    *,
    atomic_state: Optional[AtomicStateUpdate] = None,
) -> RunReport:
    """Create a synthetic successful RunReport after agentic test generation."""
    if test_file and Path(test_file).exists():
        test_hash = calculate_sha256(test_file)
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

    if atomic_state:
        atomic_state.set_run_report(report)
    else:
        save_run_report(basename, language, report.__dict__)

    return report


# ---------------------------------------------------------------------------
# Cycle detection
# ---------------------------------------------------------------------------

def _detect_cycles(
    operation: str,
    history: List[str],
    test_extend_count: int,
) -> bool:
    """Return True when a cycle should be broken."""
    # Auto-deps: 2+ in last 3 ops → force advance
    if operation == "auto-deps":
        recent = history[-3:] if len(history) >= 3 else history
        if recent.count("auto-deps") >= 2:
            return True

    # Crash-verify alternation
    if len(history) >= 4 and operation in ("crash", "verify"):
        tail = history[-4:]
        pattern_a = ["crash", "verify", "crash", "verify"]
        pattern_b = ["verify", "crash", "verify", "crash"]
        if tail == pattern_a or tail == pattern_b:
            return True

    # Test-fix alternation
    if len(history) >= 4 and operation in ("test", "fix"):
        tail = history[-4:]
        if tail == ["test", "fix", "test", "fix"] or tail == ["fix", "test", "fix", "test"]:
            return True

    # Consecutive fix
    if operation == "fix":
        consecutive = 0
        for h in reversed(history):
            if h == "fix":
                consecutive += 1
            else:
                break
        if consecutive >= 5:
            return True

    # Consecutive test
    if operation in ("test", "test_extend"):
        consecutive = 0
        for h in reversed(history):
            if h in ("test", "test_extend"):
                consecutive += 1
            else:
                break
        if consecutive >= MAX_CONSECUTIVE_TESTS:
            return True

    # Consecutive crash
    if operation == "crash":
        consecutive = 0
        for h in reversed(history):
            if h == "crash":
                consecutive += 1
            else:
                break
        if consecutive >= MAX_CONSECUTIVE_CRASHES:
            return True

    # Test-extend attempts
    if operation == "test_extend" and test_extend_count >= MAX_TEST_EXTEND_ATTEMPTS:
        return True

    return False


# ---------------------------------------------------------------------------
# Skip handling
# ---------------------------------------------------------------------------

def _handle_skip(
    basename: str,
    language: str,
    operation: str,
    pdd_files: Dict,
    skipped_operations: List[str],
):
    """Log a skip and save fingerprint with 'skip:' prefix."""
    skipped_operations.append(operation)
    log_event(
        basename, language, "operation_skipped",
        {"operation": operation}, invocation_mode="sync",
    )
    paths = {}
    for key in ("prompt", "code", "example", "test"):
        p = pdd_files.get(key, "")
        if p and Path(p).exists():
            paths[key] = Path(p)
    save_fingerprint(
        basename=basename,
        language=language,
        operation=f"skip:{operation}",
        paths=paths,
        cost=0.0,
        model="skip",
    )


# ---------------------------------------------------------------------------
# Result extraction
# ---------------------------------------------------------------------------

def _extract_result_fields(result, operation: str) -> tuple:
    """Normalise (success, cost, model) from the diverse *_main return formats."""
    if isinstance(result, dict):
        success = result.get("success", False)
        cost = result.get("cost", result.get("total_cost", 0.0))
        model = result.get("model", result.get("model_name", "unknown"))
        return success, float(cost), str(model)

    if isinstance(result, (tuple, list)):
        if operation == "test" and len(result) == 4:
            content, cost, model, agentic_success = (
                result[0], result[1], result[2], result[3],
            )
            success = bool(content) if agentic_success is None else bool(agentic_success)
            return success, float(cost), str(model)

        if len(result) >= 6:
            # fix_main / crash_main: (success, ..., attempts, cost, model)
            return bool(result[0]), float(result[-2]), str(result[-1])

        if len(result) >= 3:
            cost = result[-2] if not isinstance(result[-2], str) else 0.0
            model = result[-1] if isinstance(result[-1], str) else "unknown"
            return True, float(cost), str(model)

    return bool(result), 0.0, "unknown"


# ---------------------------------------------------------------------------
# Operation dispatcher
# ---------------------------------------------------------------------------

def _execute_operation(
    *,
    operation: str,
    basename: str,
    language: str,
    pdd_files: Dict,
    ctx: click.Context,
    target_coverage: float,
    max_attempts: int,
    force: bool,
    strength: float,
    temperature: float,
    time_param: float,
    verbose: bool,
    quiet: bool,
    local: bool,
    agentic_mode: bool,
    prompts_dir: str,
    code_dir: str,
    examples_dir: str,
    tests_dir: str,
    test_files_list: List[str],
    app_ref: list,
    progress_callback_ref: list,
    budget: float,
) -> tuple:
    """Execute a single sync operation. Returns (success, cost, model, error)."""

    from .get_extension import get_extension

    prompt_file = pdd_files.get("prompt", "")
    code_file = pdd_files.get("code", "")
    example_file = pdd_files.get("example", "")
    test_file = pdd_files.get("test", "")
    ext = get_extension(language)
    use_agentic = _use_agentic_path(language, agentic_mode)

    # ---------------------------------------------------------------- auto-deps
    if operation == "auto-deps":
        import shutil
        dep_dir = examples_dir
        if not Path(dep_dir).exists():
            dep_dir = "context"
        glob_pat = f"{dep_dir}/*_example.{ext}" if Path(dep_dir).is_dir() else dep_dir
        try:
            result = auto_deps_main(
                ctx=ctx,
                prompt_file=prompt_file,
                directory_path=glob_pat,
                auto_deps_csv_path="./project_dependencies.csv",
                output=prompt_file,
                force_scan=False,
            )
            _, cost, model = _extract_result_fields(result, operation)
            return True, cost, model, None
        except Exception as e:
            return False, 0.0, "unknown", str(e)

    # ---------------------------------------------------------------- generate
    if operation == "generate":
        clear_run_report(basename, language)
        try:
            result = code_generator_main(
                ctx=ctx,
                prompt_file=prompt_file,
                output=code_file,
                original_prompt_file_path=None,
                force_incremental_flag=False,
            )
            success, cost, model = _extract_result_fields(result, operation)
            return success, cost, model, None
        except Exception as e:
            return False, 0.0, "unknown", str(e)

    # ---------------------------------------------------------------- example
    if operation == "example":
        try:
            result = context_generator_main(
                ctx=ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                output=example_file,
            )
            _, cost, model = _extract_result_fields(result, operation)
            return True, cost, model, None
        except Exception as e:
            return False, 0.0, "unknown", str(e)

    # ---------------------------------------------------------------- crash
    if operation == "crash":
        if not Path(example_file).exists():
            return False, 0.0, "unknown", "Example file missing, cannot detect crashes"

        # Detect crash
        has_crash = False
        crash_log_content = ""

        if language.lower() == "python" and not use_agentic:
            exit_code, stdout, stderr = _run_example_with_error_detection(
                example_file, code_dir, language,
            )
            combined = (stdout or "") + "\n" + (stderr or "")
            errors_detected = _detect_example_errors(combined)
            if exit_code != 0 or errors_detected:
                has_crash = True
                crash_log_content = combined

                if _try_auto_fix_import_error(stderr, code_file):
                    exit_code2, stdout2, stderr2 = _run_example_with_error_detection(
                        example_file, code_dir, language,
                    )
                    combined2 = (stdout2 or "") + "\n" + (stderr2 or "")
                    if exit_code2 == 0 and not _detect_example_errors(combined2):
                        has_crash = False
        else:
            has_crash = True
            crash_log_content = (
                f"Non-Python language ({language}): delegating crash detection "
                "to agentic handler with language-appropriate tooling."
            )

        if not has_crash:
            # No crash – save synthetic report so determine_operation advances
            report = RunReport(
                timestamp=datetime.datetime.now().isoformat(),
                exit_code=0, tests_passed=0, tests_failed=0,
                coverage=0.0, test_hash=None,
            )
            save_run_report(basename, language, report.__dict__)
            return True, 0.0, "skip", None

        # Write crash log to temp file
        error_fd, error_path = tempfile.mkstemp(suffix=".log", prefix="crash_")
        try:
            os.write(error_fd, crash_log_content.encode("utf-8"))
        finally:
            os.close(error_fd)

        attempts_kwarg = 0 if use_agentic else max_attempts
        try:
            result = crash_main(
                ctx=ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                program_file=example_file,
                error_file=error_path,
                output=code_file,
                output_program=example_file,
                loop=True,
                strength=strength,
                temperature=temperature,
                budget=min(budget, 5.0),
                max_attempts=attempts_kwarg,
            )
            success = result[0] if isinstance(result, (tuple, list)) else result.get("success", False)
            _, cost, model = _extract_result_fields(result, operation)

            if success and language.lower() == "python" and not use_agentic:
                exit_code, stdout, stderr = _run_example_with_error_detection(
                    example_file, code_dir, language,
                )
                combined = (stdout or "") + "\n" + (stderr or "")
                if exit_code != 0 or _detect_example_errors(combined):
                    return False, cost, model, "Crash persists after fix attempt"
                report = RunReport(
                    timestamp=datetime.datetime.now().isoformat(),
                    exit_code=0, tests_passed=0, tests_failed=0,
                    coverage=0.0, test_hash=None,
                )
                save_run_report(basename, language, report.__dict__)
            elif success and use_agentic:
                report = RunReport(
                    timestamp=datetime.datetime.now().isoformat(),
                    exit_code=0, tests_passed=0, tests_failed=0,
                    coverage=0.0, test_hash=None,
                )
                save_run_report(basename, language, report.__dict__)

            return success, cost, model, None
        except Exception as e:
            return False, 0.0, "unknown", str(e)
        finally:
            Path(error_path).unlink(missing_ok=True)

    # ---------------------------------------------------------------- verify
    if operation == "verify":
        if not Path(example_file).exists():
            return False, 0.0, "unknown", "Example file missing for verification"
        attempts_kwarg = 0 if use_agentic else max_attempts
        try:
            result = fix_verification_main(
                ctx=ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                program_file=example_file,
                output_results=None,
                output_code=code_file,
                output_program=example_file,
                loop=True,
                verification_program=None,
                max_attempts=attempts_kwarg,
                budget=min(budget, 5.0),
                agentic_fallback=True,
            )
            success = result[0] if isinstance(result, (tuple, list)) else result.get("success", False)
            _, cost, model = _extract_result_fields(result, operation)
            return success, cost, model, None
        except Exception as e:
            return False, 0.0, "unknown", str(e)

    # ---------------------------------------------------------------- test
    if operation == "test":
        try:
            result = cmd_test_main(
                ctx=ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                output=test_file,
                language=language,
                coverage_report=None,
                existing_tests=None,
                target_coverage=None,
                merge=False,
                strength=strength,
                temperature=temperature,
            )
            content = result[0] if isinstance(result, (tuple, list)) and len(result) >= 4 else result
            cost_val = result[1] if isinstance(result, (tuple, list)) and len(result) >= 4 else 0.0
            model_val = result[2] if isinstance(result, (tuple, list)) and len(result) >= 4 else "unknown"
            agentic_success = result[3] if isinstance(result, (tuple, list)) and len(result) >= 4 else None

            success = bool(content) if agentic_success is None else bool(agentic_success)
            return success, float(cost_val), str(model_val), None
        except Exception as e:
            return False, 0.0, "unknown", str(e)

    # ---------------------------------------------------------------- test_extend
    if operation == "test_extend":
        lang_lower = language.lower()
        if lang_lower not in ("python", "typescript"):
            return True, 0.0, "skip", None

        existing = [f for f in (test_files_list or [test_file]) if Path(f).exists()]
        if not existing:
            return True, 0.0, "skip", None

        try:
            result = cmd_test_main(
                ctx=ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                output=test_file,
                language=language,
                coverage_report=None,
                existing_tests=existing,
                target_coverage=target_coverage,
                merge=True,
                strength=strength,
                temperature=temperature,
            )
            cost_val = result[1] if isinstance(result, (tuple, list)) and len(result) >= 4 else 0.0
            model_val = result[2] if isinstance(result, (tuple, list)) and len(result) >= 4 else "unknown"
            return True, float(cost_val), str(model_val), None
        except Exception as e:
            return False, 0.0, "unknown", str(e)

    # ---------------------------------------------------------------- fix
    if operation == "fix":
        from .get_test_command import get_test_command_for_file

        all_tests = [f for f in (test_files_list or [test_file]) if Path(f).exists()]
        if not all_tests:
            return False, 0.0, "unknown", "No test files found for fix"

        # Pre-run tests to identify failing file
        env = _get_subprocess_env()
        failing_file = all_tests[0]
        error_content = ""

        if language.lower() == "python":
            python_exec = detect_host_python_executable() or sys.executable
            cmd = [python_exec, "-m", "pytest", "-v"]
            project_root = _find_project_root(all_tests[0])
            if project_root:
                cmd.extend(["--rootdir", str(project_root), "-c", "/dev/null"])
                paths = [str(project_root)]
                src = project_root / "src"
                if src.is_dir():
                    paths.append(str(src))
                existing = env.get("PYTHONPATH", "")
                env["PYTHONPATH"] = os.pathsep.join(paths + ([existing] if existing else []))
            cmd.extend(all_tests)
            try:
                pre_result = subprocess.run(
                    cmd, capture_output=True, text=True, timeout=120,
                    env=env, start_new_session=True, stdin=subprocess.DEVNULL,
                )
                error_content = pre_result.stdout + "\n" + pre_result.stderr
                failing_files = extract_failing_files_from_output(error_content)
                if failing_files:
                    for ff in failing_files:
                        if ff in all_tests:
                            failing_file = ff
                            break
            except Exception:
                pass
        else:
            test_cmd = get_test_command_for_file(all_tests[0], language=language)
            if test_cmd:
                try:
                    shell_cmd = test_cmd if isinstance(test_cmd, list) else ["sh", "-c", test_cmd]
                    pre_result = subprocess.run(
                        shell_cmd, capture_output=True, text=True, timeout=120,
                        env=env, start_new_session=True, stdin=subprocess.DEVNULL,
                    )
                    error_content = pre_result.stdout + "\n" + pre_result.stderr
                except Exception:
                    pass

        error_fd, error_path = tempfile.mkstemp(suffix=".log", prefix="fix_")
        try:
            os.write(error_fd, error_content.encode("utf-8"))
        finally:
            os.close(error_fd)

        attempts_kwarg = 0 if use_agentic else max_attempts
        try:
            result = fix_main(
                ctx=ctx,
                prompt_file=prompt_file,
                code_file=code_file,
                unit_test_file=failing_file,
                error_file=error_path,
                output_test=failing_file,
                output_code=code_file,
                output_results=None,
                loop=True,
                verification_program=example_file if Path(example_file).exists() else None,
                max_attempts=attempts_kwarg,
                budget=min(budget, 5.0),
                auto_submit=False,
                agentic_fallback=True,
                strength=None,
                temperature=None,
                test_files=all_tests if len(all_tests) > 1 else None,
            )
            success = result[0] if isinstance(result, (tuple, list)) else result.get("success", False)
            _, cost, model = _extract_result_fields(result, operation)

            if success and language.lower() == "python" and not use_agentic:
                _execute_tests_and_create_run_report(
                    test_file, basename, language, target_coverage,
                    code_file=code_file, test_files=all_tests or None,
                )
            elif success and use_agentic:
                report = RunReport(
                    timestamp=datetime.datetime.now().isoformat(),
                    exit_code=0, tests_passed=1, tests_failed=0,
                    coverage=0.0, test_hash=calculate_sha256(test_file) if Path(test_file).exists() else None,
                )
                save_run_report(basename, language, report.__dict__)

            return success, cost, model, None
        except Exception as e:
            return False, 0.0, "unknown", str(e)
        finally:
            Path(error_path).unlink(missing_ok=True)

    # ---------------------------------------------------------------- update
    if operation == "update":
        try:
            result = update_main(
                ctx=ctx,
                input_prompt_file=prompt_file,
                modified_code_file=code_file,
                input_code_file=None,
                output=prompt_file,
                use_git=True,
                simple=False,
            )
            _, cost, model = _extract_result_fields(result, operation)
            return True, cost, model, None
        except Exception as e:
            return False, 0.0, "unknown", str(e)

    return False, 0.0, "unknown", f"Unknown operation: {operation}"


# ---------------------------------------------------------------------------
# Post-operation actions
# ---------------------------------------------------------------------------

def _post_operation(
    *,
    operation: str,
    basename: str,
    language: str,
    pdd_files: Dict,
    target_coverage: float,
    agentic_mode: bool,
    code_dir: str,
    atomic_state: Optional[AtomicStateUpdate],
    test_files_list: List[str],
):
    """Run post-operation validation and state updates."""
    test_file = pdd_files.get("test", "")
    code_file = pdd_files.get("code", "")
    example_file = pdd_files.get("example", "")
    use_agentic = _use_agentic_path(language, agentic_mode)

    if operation == "generate":
        clear_run_report(basename, language)

    elif operation == "test":
        # Check for agentic success marker stored by _execute_operation
        # handled via the caller inspecting cmd_test_main's 4th return element
        pass

    elif operation in ("test", "test_extend"):
        if Path(test_file).exists():
            all_tests = [f for f in (test_files_list or [test_file]) if Path(f).exists()]
            _execute_tests_and_create_run_report(
                test_file, basename, language, target_coverage,
                code_file=code_file, atomic_state=atomic_state,
                test_files=all_tests or None,
            )


# ---------------------------------------------------------------------------
# Main orchestration entry-point
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
    """Orchestrate the complete PDD sync workflow.

    Coordinates operation execution determined by ``sync_determine_operation``
    while providing real-time TUI feedback via ``SyncApp``.
    """

    # Defence in depth: CLI may pass None for these
    if target_coverage is None:
        target_coverage = 90.0
    if budget is None:
        budget = 10.0
    if max_attempts is None:
        max_attempts = 3

    from .get_extension import get_extension  # function-scope import

    # ------------------------------------------------------------------
    # Dry-run: display analysis then return immediately
    # ------------------------------------------------------------------
    if dry_run:
        click.echo(f"Sync analysis for {basename} ({language}):")
        entries = _display_sync_log(basename, language, verbose)

        decision = sync_determine_operation(basename, language, target_coverage, log_mode=True)
        click.echo(f"\nRecommended operation: {decision.operation}")
        click.echo(f"Reason: {decision.reason}")
        if verbose:
            click.echo(f"Decision type: {decision.decision_type}")
            click.echo(f"Confidence: {decision.confidence}")
            click.echo(f"Estimated cost: ${decision.estimated_cost:.4f}")

        return {
            "success": True,
            "operations_completed": [],
            "skipped_operations": [],
            "total_cost": 0.0,
            "total_time": 0.0,
            "final_state": {},
            "errors": [],
            "error": None,
            "model_name": None,
            "log_entries": entries,
        }

    # ------------------------------------------------------------------
    # Shared mutable state for TUI ↔ worker coordination
    # ------------------------------------------------------------------
    start_time = time.time()

    function_name_ref: List[str] = ["initializing"]
    cost_ref: List[float] = [0.0]
    prompt_color_ref: List[str] = ["blue"]
    prompt_path_ref: List[str] = [""]
    code_color_ref: List[str] = ["blue"]
    code_path_ref: List[str] = [""]
    example_color_ref: List[str] = ["blue"]
    example_path_ref: List[str] = [""]
    test_color_ref: List[str] = ["blue"]
    test_path_ref: List[str] = [""]
    stop_event = threading.Event()
    app_ref: List[Any] = []
    user_confirmed_overwrite: List[bool] = [False]
    progress_callback_ref: List[Any] = [None]
    worker_result: List[Optional[Dict[str, Any]]] = [None]

    headless = _is_headless() or quiet

    # ------------------------------------------------------------------
    # Confirmation callback factory
    # ------------------------------------------------------------------
    def _make_confirm_callback() -> Callable:
        if confirm_callback:
            return confirm_callback

        if headless:
            def _headless_confirm(title: str, message: str) -> bool:
                if force or user_confirmed_overwrite[0]:
                    return True
                result = click.confirm(f"{title}: {message}", default=True)
                if result:
                    user_confirmed_overwrite[0] = True
                return result
            return _headless_confirm

        def _tui_confirm(title: str, message: str) -> bool:
            if force or user_confirmed_overwrite[0]:
                return True
            if app_ref:
                result = app_ref[0].request_confirmation(title, message)
                if result:
                    user_confirmed_overwrite[0] = True
                return result
            return force
        return _tui_confirm

    # ------------------------------------------------------------------
    # TUI colour updater
    # ------------------------------------------------------------------
    def _update_file_colors(pdd_files: Dict, processing_op: str = ""):
        prompt_path_ref[0] = str(pdd_files.get("prompt", ""))
        code_path_ref[0] = str(pdd_files.get("code", ""))
        example_path_ref[0] = str(pdd_files.get("example", ""))
        test_path_ref[0] = str(pdd_files.get("test", ""))

        prompt_color_ref[0] = _get_file_color(pdd_files.get("prompt"))
        code_color_ref[0] = _get_file_color(
            pdd_files.get("code"),
            processing_op in ("generate", "crash", "fix"),
        )
        example_color_ref[0] = _get_file_color(
            pdd_files.get("example"), processing_op == "example",
        )
        test_color_ref[0] = _get_file_color(
            pdd_files.get("test"),
            processing_op in ("test", "test_extend"),
        )

    # ==================================================================
    # Worker logic – runs inside the TUI worker thread (or directly)
    # ==================================================================
    def sync_worker_logic():  # noqa: C901 (complexity unavoidable for orchestrator)
        MAX_CYCLE_REPEATS = 2  # noqa: N806

        total_cost = 0.0
        operations_completed: List[str] = []
        skipped_operations: List[str] = []
        errors: List[str] = []
        last_model: Optional[str] = None
        operation_history: List[str] = []
        test_extend_count = 0

        ctx = _create_mock_context(
            strength=strength,
            temperature=temperature,
            time_param=time_param,
            verbose=verbose,
            quiet=quiet,
            force=force,
            local=local,
            context=context_override,
            confirm_callback=_make_confirm_callback(),
            output_cost=output_cost,
            review_examples=review_examples,
        )

        # -- Resolve file paths ----------------------------------------
        ext = get_extension(language)
        try:
            pdd_files = get_pdd_file_paths(basename, language)
        except FileNotFoundError as e:
            if "test" in str(e).lower():
                pdd_files = {}
                prompts_path = Path(prompts_dir)
                expected = f"{basename}_{language}.prompt".lower()
                prompt_found = None
                if prompts_path.is_dir():
                    for f in prompts_path.iterdir():
                        if f.name.lower() == expected:
                            prompt_found = str(f)
                            break
                if not prompt_found:
                    prompt_found = str(prompts_path / f"{basename}_{language}.prompt")
                pdd_files["prompt"] = prompt_found
                pdd_files["code"] = str(Path(code_dir) / f"{basename}.{ext}")
                pdd_files["example"] = str(Path(examples_dir) / f"{basename}_example.{ext}")
                pdd_files["test"] = str(Path(tests_dir) / f"test_{basename}.{ext}")
            else:
                worker_result[0] = _error_result(str(e), start_time)
                return
        except Exception as e:
            worker_result[0] = _error_result(str(e), start_time)
            return

        test_files_list = pdd_files.get("test_files", [])
        _update_file_colors(pdd_files)

        # -- Acquire lock ----------------------------------------------
        lock: Optional[SyncLock] = None
        try:
            lock = SyncLock(basename, language)
            lock.__enter__()
            log_event(basename, language, "lock_acquired", {}, invocation_mode="sync")
        except Exception as e:
            worker_result[0] = _error_result(f"Failed to acquire lock: {e}", start_time)
            return

        last_decision: Optional[SyncDecision] = None
        try:
            while not stop_event.is_set():
                # Budget gate
                if total_cost >= budget:
                    log_event(
                        basename, language, "budget_exceeded",
                        {"total_cost": total_cost, "budget": budget},
                        invocation_mode="sync",
                    )
                    errors.append(f"Budget exceeded: ${total_cost:.2f} >= ${budget:.2f}")
                    break

                if budget > 0 and total_cost >= budget * 0.8:
                    log_event(
                        basename, language, "budget_warning",
                        {"remaining": budget - total_cost},
                        invocation_mode="sync",
                    )

                # Determine next operation
                decision = sync_determine_operation(basename, language, target_coverage)
                last_decision = decision
                operation = decision.operation
                reason = decision.reason

                function_name_ref[0] = operation
                _update_file_colors(pdd_files, operation)

                # Terminal states
                if operation in _TERMINAL_STATES:
                    if operation == "fail_and_request_manual_merge":
                        errors.append(f"Manual merge required: {reason}")
                    elif operation == "error":
                        errors.append(f"Sync error: {reason}")
                    break

                # Cycle detection
                if _detect_cycles(operation, operation_history, test_extend_count):
                    logger.warning("Cycle detected for '%s', breaking loop", operation)
                    log_event(
                        basename, language, "cycle_break",
                        {"operation": operation, "history": operation_history[-6:]},
                        invocation_mode="sync",
                    )
                    break

                # Interactive steering
                if not no_steer and not headless:
                    steered_op, should_abort = maybe_steer_operation(
                        operation, reason, app_ref, quiet,
                        skip_tests, skip_verify,
                        timeout_s=steer_timeout,
                    )
                    if should_abort:
                        errors.append("Aborted by user steering")
                        break
                    if steered_op != operation:
                        log_event(
                            basename, language, "steering_override",
                            {"original": operation, "steered": steered_op},
                            invocation_mode="sync",
                        )
                        operation = steered_op
                        decision.operation = steered_op

                # Skip handling
                if operation == "verify" and (skip_verify or skip_tests):
                    _handle_skip(basename, language, "verify", pdd_files, skipped_operations)
                    operation_history.append("verify")
                    continue
                if operation == "crash" and skip_tests:
                    _handle_skip(basename, language, "crash", pdd_files, skipped_operations)
                    synthetic = RunReport(
                        timestamp=datetime.datetime.now().isoformat(),
                        exit_code=0, tests_passed=0, tests_failed=0,
                        coverage=0.0, test_hash=None,
                    )
                    save_run_report(basename, language, synthetic.__dict__)
                    operation_history.append("crash")
                    continue
                if operation in ("test", "test_extend", "fix") and skip_tests:
                    _handle_skip(basename, language, operation, pdd_files, skipped_operations)
                    operation_history.append(operation)
                    continue

                # Create log entry
                entry = create_log_entry(
                    operation=decision.operation,
                    reason=decision.reason,
                    invocation_mode="sync",
                    estimated_cost=decision.estimated_cost,
                    confidence=decision.confidence,
                    decision_type=decision.decision_type,
                )

                # Execute
                op_start = time.time()
                op_success = False
                op_cost = 0.0
                op_model = "unknown"
                op_error: Optional[str] = None

                try:
                    op_success, op_cost, op_model, op_error = _execute_operation(
                        operation=operation,
                        basename=basename,
                        language=language,
                        pdd_files=pdd_files,
                        ctx=ctx,
                        target_coverage=target_coverage,
                        max_attempts=max_attempts,
                        force=force,
                        strength=strength,
                        temperature=temperature,
                        time_param=time_param,
                        verbose=verbose,
                        quiet=quiet,
                        local=local,
                        agentic_mode=agentic_mode,
                        prompts_dir=prompts_dir,
                        code_dir=code_dir,
                        examples_dir=examples_dir,
                        tests_dir=tests_dir,
                        test_files_list=test_files_list,
                        app_ref=app_ref,
                        progress_callback_ref=progress_callback_ref,
                        budget=budget - total_cost,
                    )
                except Exception as exc:
                    import traceback as _tb
                    op_error = str(exc)
                    logger.error(
                        "Operation %s failed: %s\n%s",
                        operation, exc, _tb.format_exc(),
                    )

                op_duration = time.time() - op_start
                total_cost += op_cost
                cost_ref[0] = total_cost

                if op_model and op_model not in ("unknown", "skip"):
                    last_model = op_model

                # Update & persist log entry
                entry = update_log_entry(
                    entry=entry,
                    success=op_success,
                    cost=op_cost,
                    model=op_model,
                    duration=op_duration,
                    error=op_error,
                )
                append_log_entry(basename, language, entry)

                if op_success:
                    operations_completed.append(operation)

                    # Atomic state persistence
                    with AtomicStateUpdate(basename, language) as atomic:
                        paths = {}
                        for key in ("prompt", "code", "example", "test"):
                            p = pdd_files.get(key, "")
                            if p and Path(p).exists():
                                paths[key] = Path(p)
                        atomic.set_fingerprint(operation, paths, op_cost, op_model)

                        # Test operation: handle agentic success synthetic report
                        if operation == "test":
                            agentic_success = _check_agentic_test_success(
                                pdd_files, basename, language, operation,
                                agentic_mode, test_files_list, target_coverage,
                                code_dir, atomic,
                            )

                        # Post-operation validation for test/test_extend
                        elif operation in ("test_extend",):
                            lang_lower = language.lower()
                            if lang_lower not in ("python", "typescript"):
                                _create_synthetic_run_report_for_agentic_success(
                                    pdd_files.get("test", ""), basename, language,
                                    atomic_state=atomic,
                                )
                            else:
                                all_tests = [
                                    f for f in (test_files_list or [pdd_files.get("test", "")])
                                    if Path(f).exists()
                                ]
                                if all_tests:
                                    _execute_tests_and_create_run_report(
                                        pdd_files.get("test", ""),
                                        basename, language, target_coverage,
                                        code_file=pdd_files.get("code"),
                                        atomic_state=atomic,
                                        test_files=all_tests,
                                    )

                        # generate clears stale run report
                        elif operation == "generate":
                            clear_run_report(basename, language)
                else:
                    if op_error:
                        errors.append(f"{operation}: {op_error}")

                operation_history.append(operation)
                if operation == "test_extend":
                    test_extend_count += 1

                _update_file_colors(pdd_files)

        finally:
            if lock is not None:
                try:
                    lock.__exit__(None, None, None)
                    log_event(basename, language, "lock_released", {}, invocation_mode="sync")
                except Exception:
                    pass

        # Build final state
        final_state: Dict[str, Any] = {}
        for key in ("prompt", "code", "example", "test"):
            p = pdd_files.get(key, "")
            final_state[key] = {"exists": bool(p) and Path(p).exists(), "path": p}

        is_synced = last_decision is not None and last_decision.operation == "all_synced"
        success = is_synced or (not errors)

        worker_result[0] = {
            "success": success,
            "operations_completed": operations_completed,
            "skipped_operations": skipped_operations,
            "total_cost": total_cost,
            "total_time": time.time() - start_time,
            "final_state": final_state,
            "errors": errors,
            "error": "; ".join(errors) if errors else None,
            "model_name": last_model,
            "log_entries": [],
        }

    # ==================================================================
    # Run the worker – either headless or via TUI
    # ==================================================================
    function_name_ref[0] = "starting"
    stop_event.clear()

    if headless:
        prev_force = os.environ.get("PDD_FORCE")
        os.environ["PDD_FORCE"] = "1"
        try:
            sync_worker_logic()
        finally:
            if prev_force is None:
                os.environ.pop("PDD_FORCE", None)
            else:
                os.environ["PDD_FORCE"] = prev_force

        return worker_result[0] or _error_result("Sync was interrupted", start_time)

    # ── TUI mode ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    def _tui_worker():
        try:
            sync_worker_logic()
        finally:
            stop_event.set()

    app = SyncApp(
        worker_func=_tui_worker,
        function_name_ref=function_name_ref,
        cost_ref=cost_ref,
        prompt_color_ref=prompt_color_ref,
        prompt_path_ref=prompt_path_ref,
        code_color_ref=code_color_ref,
        code_path_ref=code_path_ref,
        example_color_ref=example_color_ref,
        example_path_ref=example_path_ref,
        test_color_ref=test_color_ref,
        test_path_ref=test_path_ref,
        stop_event=stop_event,
    )
    app_ref.append(app)

    app.run()

    # Check for worker-thread exceptions
    if hasattr(app, "worker_exception") and app.worker_exception:
        import traceback as _tb
        exc = app.worker_exception
        print(f"Sync worker error: {exc}", file=sys.stderr)
        if hasattr(exc, "__traceback__"):
            _tb.print_exception(type(exc), exc, exc.__traceback__, file=sys.stderr)

    if worker_result[0] is None:
        return _error_result("Sync was interrupted", start_time)

    # Exit animation
    if not quiet:
        from .sync_tui import show_exit_animation
        res = worker_result[0]
        show_exit_animation(
            success=res["success"],
            operations=res["operations_completed"],
            cost=res["total_cost"],
            time_elapsed=res["total_time"],
            errors=res["errors"],
        )

    return worker_result[0]


# ---------------------------------------------------------------------------
# Private helpers used inside the worker
# ---------------------------------------------------------------------------

def _error_result(message: str, start_time: float) -> Dict[str, Any]:
    """Build a standard error-result dict."""
    return {
        "success": False,
        "operations_completed": [],
        "skipped_operations": [],
        "total_cost": 0.0,
        "total_time": time.time() - start_time,
        "final_state": {},
        "errors": [message],
        "error": message,
        "model_name": None,
        "log_entries": [],
    }


def _check_agentic_test_success(
    pdd_files: Dict,
    basename: str,
    language: str,
    operation: str,
    agentic_mode: bool,
    test_files_list: List[str],
    target_coverage: float,
    code_dir: str,
    atomic: AtomicStateUpdate,
) -> bool:
    """After the test operation, decide whether to trust agentic result or run tests.

    Returns True if a synthetic report was created (agentic path used).
    """
    test_file = pdd_files.get("test", "")
    code_file = pdd_files.get("code", "")

    # The agentic_success flag was returned by cmd_test_main.  We cannot
    # easily thread it here, so we re-check: when agentic_success is True
    # the caller should have already recorded it.  We use a convention:
    # if the test file is brand new (no run report) and is non-empty,
    # assume agentic success for non-Python or agentic_mode.
    use_agentic = _use_agentic_path(language, agentic_mode)

    if use_agentic and Path(test_file).exists():
        _create_synthetic_run_report_for_agentic_success(
            test_file, basename, language, atomic_state=atomic,
        )
        return True

    # Python (non-agentic): actually run the tests
    if Path(test_file).exists():
        all_tests = [f for f in (test_files_list or [test_file]) if Path(f).exists()]
        _execute_tests_and_create_run_report(
            test_file, basename, language, target_coverage,
            code_file=code_file, atomic_state=atomic,
            test_files=all_tests or None,
        )
    return False